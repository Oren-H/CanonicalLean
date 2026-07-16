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

/-- Bound up to which ground `Nat` values reach the solver as unary constructor
    spines it can compute with. A value above it stays an opaque rule-less
    symbol, making any example containing it unsatisfiable by computation —
    `synthesize` drops such examples with a warning. -/
def MAX_CTOR_NAT := 64

/-- A ground `Nat` value as a constructor spine, the encoding the hand-built
    problems in the Rust repo's `lean/Test.lean` use for example values. -/
def natCtorSpine : Nat → Spine
  | 0 => { head := (``Nat.zero).toString }
  | n + 1 => { head := (``Nat.succ).toString, args := #[{ spine := natCtorSpine n }] }

/-- The value of a head symbol naming an opaque `Nat` literal (`toHead` names
    `.lit (.natVal n)` as `n`), if within the constructor-spine bound. -/
def numeralHead? (h : String) : Option Nat :=
  h.toNat?.filter (fun n => n ≤ MAX_CTOR_NAT)

mutual
  /-- All head symbols occurring in a translated term. -/
  partial def exprHeads (e : Canonical.Expr) : Array String :=
    e.params.flatMap declHeads ++ e.lets.flatMap declHeads ++ spineHeads e.spine

  partial def spineHeads (s : Spine) : Array String :=
    s.args.foldl (fun acc a => acc ++ exprHeads a) #[s.head]

  partial def declHeads (d : Canonical.Decl) : Array String :=
    (d.type.map exprHeads).getD #[] ++ d.equations.flatMap ruleHeads

  partial def ruleHeads (r : Rule) : Array String :=
    spineHeads r.lhs ++ spineHeads r.rhs
end

mutual
  /-- Replace opaque `Nat`-literal symbols by constructor spines. The `whnf`
      in `toTerm` collapses the examples' `succ` chains into literals and
      `elimSpecial` re-expands only values ≤ 5, so without this pass any
      example value above 5 reaches the solver as a symbol it cannot compute
      with — the equation is then satisfiable only by terms that return the
      symbol verbatim, which is how overfit candidates arise. -/
  partial def expandNumeralsExpr (e : Canonical.Expr) : Canonical.Expr :=
    { e with
      params := e.params.map expandNumeralsDecl
      lets := e.lets.map expandNumeralsDecl
      spine := expandNumeralsSpine e.spine }

  partial def expandNumeralsSpine (s : Spine) : Spine :=
    if s.args.isEmpty then
      match numeralHead? s.head with
      | some n => { natCtorSpine n with premiseRules := s.premiseRules }
      | none => s
    else { s with args := s.args.map expandNumeralsExpr }

  partial def expandNumeralsDecl (d : Canonical.Decl) : Canonical.Decl :=
    { d with
      type := d.type.map expandNumeralsExpr
      equations := d.equations.map expandNumeralsRule }

  partial def expandNumeralsRule (r : Rule) : Rule :=
    { r with lhs := expandNumeralsSpine r.lhs, rhs := expandNumeralsSpine r.rhs }
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

  -- `Nat` values above 5 come back from `toRule` as opaque rule-less symbols;
  -- re-expand them into constructor spines (see `expandNumeralsExpr`). The
  -- constructors are defined explicitly because the equations may be the only
  -- place they occur.
  let numerals := (equations.flatMap ruleHeads).filter (fun h => (numeralHead? h).isSome)
  let equations ← if numerals.isEmpty then pure equations else do
    withReader (fun ctx => { ctx with polarity := .premise }) do
      let _ ← defineConst ``Nat.zero
      let _ ← defineConst ``Nat.succ
    pure (equations.map expandNumeralsRule)

  -- Simp lemmas
  if (← read).config.simp then
    let _ ← addSimpLemmas

  if (← get).definitions.contains fname then
    throwError "the name `{fname}` collides with a symbol occurring in the problem; \
      choose a different function name"

  let lets := lets ++ (← get).definitions.toList.toArray.map fun ⟨name, defn⟩ =>
    { name, equations := defn.rules, type := defn.type.toOption }

  let _ ← finalizeMonos

  let decl : Canonical.Decl :=
    { name := fname, type := some { typ with lets := lets ++ typ.lets }, equations }
  if numerals.isEmpty then return decl
  -- Translating the literals also `define`d them, so they linger as rule-less
  -- premises the search could return verbatim; drop the ones the expanded
  -- problem no longer references.
  let referenced := declHeads decl
  return { decl with type := decl.type.map fun t =>
    { t with lets := t.lets.filter fun d =>
        !numerals.contains d.name || referenced.contains d.name } }

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
