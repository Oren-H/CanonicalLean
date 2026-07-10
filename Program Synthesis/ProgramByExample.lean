module

public meta import Canonical.Basic
public meta import Canonical.Util
public meta import Canonical.Monomorphize.Basic
public meta import Canonical.ToCanonical.Util
public meta import Canonical.ToCanonical.Reduction
public meta import Canonical.ToCanonical.Translate
public meta import Canonical.ToCanonical.Main
public meta import Canonical.Main
public meta import Canonical.FromCanonical
public meta import Canonical.Symbols

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.PBE

public meta section

/-! # Programming by example

Problem construction for synthesis from input–output examples: `toProblem`
turns a function type and `f a₁ … aₙ = b` example equations into a single
Canonical inhabitation problem, the examples becoming equational constraints
on the declaration under synthesis — following the shape of the problem
constructed by hand in the Rust repo's `lean/Test.lean`. Driven by the
`synthesize` tactic (`Synthesize.lean`), which replaced the `#synthesize`
command. See `ProgramByExample.md` for the design. -/

mutual
  /-- Rename occurrences of head symbol `old` to `new` in a translated term. -/
  partial def renameExpr (old new : String) (e : Canonical.Expr) : Canonical.Expr :=
    { e with
      params := e.params.map (renameDecl old new)
      lets := e.lets.map (renameDecl old new)
      spine := renameSpine old new e.spine }

  partial def renameSpine (old new : String) (s : Spine) : Spine :=
    { s with
      head := if s.head == old then new else s.head
      args := s.args.map (renameExpr old new) }

  partial def renameDecl (old new : String) (d : Canonical.Decl) : Canonical.Decl :=
    { d with
      type := d.type.map (renameExpr old new)
      equations := d.equations.map (renameRule old new) }

  partial def renameRule (old new : String) (r : Rule) : Rule :=
    { r with lhs := renameSpine old new r.lhs, rhs := renameSpine old new r.rhs }
end

/-- Translate the signature `type` and the `examples` into a single inhabitation
    problem in one `ToCanonicalM` run, so that every symbol appearing in the type
    or in the examples is defined exactly once. Mirrors `toCanonical_`, except that
    the local variable `f` standing for the function is excluded from the premises
    and the examples become `equations` of the returned goal declaration. -/
def toProblem_ (fname : String) (f : Lean.Expr) (type : Lean.Expr)
    (examples : Array Lean.Expr) (premises : Array Name) : ToCanonicalM Canonical.Decl := do
  -- Local context (section variables). `f` is the declaration being synthesized,
  -- so it must not be available as a premise.
  let lets : Array Canonical.Decl ← withReader (fun ctx => { ctx with polarity := .premise }) do
    (← getLCtx).foldlM (fun lets decl => do
      if !decl.isAuxDecl && decl.toExpr != f then
        let (name, declType) ← toHead decl.toExpr
        if let some value := decl.value? then
          let rule := defRule name.toString (← toTerm value declType (← typeArity declType).params.toList)
          pure (lets.push { name := name.toString, equations := #[rule], type := none })
        else
          pure (lets.push { name := name.toString, type := ← toBind decl.fvarId })
      else pure lets
    ) #[]

  -- Goal type
  let typ ← toTyp type

  -- Constant symbol premises
  withReader (fun ctx => { ctx with polarity := .premise }) do
    for premise in premises do
      let _ ← definePremise premise

  -- Examples become equational constraints on the goal declaration. `toHead`
  -- names the local variable `f.<uniq>`; rename that head to the declaration
  -- name on both sides, so recursive occurrences of `f` also line up.
  let fvarHead ← toNameString f
  let equations ← withReader (fun ctx => { ctx with polarity := .premise }) do
    examples.mapM fun ex => do
      let some rule ← toRule #[] ex
        | throwError "example is not an equation:{indentExpr ex}"
      pure (renameRule fvarHead fname rule)

  -- Simp lemmas
  if (← read).config.simp then
    let _ ← addSimpLemmas

  if (← get).definitions.contains fname then
    throwError "the name `{fname}` collides with a symbol occurring in the problem; \
      choose a different function name"

  let lets := lets ++ (← get).definitions.toList.toArray.map fun ⟨name, defn⟩ =>
    { name, equations := defn.rules, type := defn.type.toOption }

  let _ ← finalizeMonos

  return { name := fname, type := some { typ with lets := lets ++ typ.lets }, equations }

/-- Run `toProblem_` with the same context/state initialization as `toCanonical`. -/
def toProblem (fname : String) (f : Lean.Expr) (type : Lean.Expr) (examples : Array Lean.Expr)
    (premises : Array Name) (config : Config) : MetaM Canonical.Decl := do
  let lctx ← getLCtx
  (((toProblem_ fname f type examples premises).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size), config, structures := #[``Pi]
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds, constNames := .ofList [``OfNat.ofNat] }

/-- Check that `candidate` satisfies the example `ex` (an equation in the local
    variable `f`) up to definitional equality. -/
def satisfiesExample (f candidate ex : Lean.Expr) : MetaM Bool := do
  let ex := ex.replaceFVar f candidate
  let some (_, lhs, rhs) := ex.eq? | return true
  withoutArityUnfold do isDefEq lhs rhs

end

end Canonical.PBE
