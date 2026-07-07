# Programming by Predicate

## Task

Make Canonical usable as a programming-by-predicate tool. The user provides:

1. a function name and type signature, e.g. `f : Nat → Nat → Nat`;
2. a set of universally quantified predicates, e.g. `∀ n : Nat, f n 0 = n` or
   `∀ n m : Nat, f n m = f m n`.

Instead of asking the user for input–output examples (as `#synthesize` does, see
`ProgramByExample.md`), the command *generates* them: Canonical's `count` option
turns the search procedure into an enumerator, which produces example inhabitants
of the quantified variables' types. Instantiating a predicate with these examples
yields concrete example equations, which are attached to the search as equational
constraints on the declaration being synthesized — from that point on, the
pipeline is exactly that of `#synthesize`.

## Interface

```lean
#synthesize_pred pred : Nat → Nat
  | pred 0 = 0
  | ∀ n : Nat, pred (n + 1) = n
```

On success, the command logs the instantiated example equations and reports
`Try this: def pred : Nat → Nat := fun a => …`; clicking the suggestion replaces
the `#synthesize_pred` command with the definition.

Because the equations only *sample* the predicates, the command then attempts to
**prove** each predicate about the synthesized function (with the same timeout
per predicate). Every proof found is appended to the suggestion as a `theorem`:

```lean
def pred : Nat → Nat := fun a ↦ Nat.rec (motive := fun t ↦ Nat) a (fun n n_ih ↦ n) a
theorem pred_spec_1 : pred 0 = 0 := Eq.refl Nat.zero
theorem pred_spec_2 : ∀ n : Nat, pred (n + 1) = n := fun n ↦ Eq.refl n
```

(`f_spec` if there is a single predicate, `f_spec_<i>` numbered in clause order
otherwise). Each predicate that could not be proved produces a warning: the
definition is then only guaranteed to satisfy the instantiated equations, not
the predicate itself — either because the search timed out, or because the
function genuinely does not satisfy it.

Each clause is a (possibly) universally quantified equation whose left-hand side
is an application of the function under synthesis; both sides may mention the
function. A clause without binders is an ordinary input–output example, so
`#synthesize_pred` subsumes `#synthesize`. Optional arguments:

- **Timeout** (seconds, default 5): `#synthesize_pred 30 f : …`
- **Examples per predicate** (default 3): `#synthesize_pred (examples := 5) f : …`
- **Premises** — extra constants made available to the search:
  `#synthesize_pred 10 [Nat.add] double : Nat → Nat | ∀ n : Nat, double n = n + n`

Each candidate returned by the solver is re-checked against the instantiated
equations by definitional equality after reconstruction; a failure produces a
warning.

## How it works

Implementation: `ProgramByPredicate.lean` (command `#synthesize_pred`, namespace
`Canonical.PBP`). Pipeline, all inside `runTermElabM`:

1. **Elaborate the signature** `T`, introduce the function as a local variable
   (`withLocalDeclD f T`), and elaborate each clause against expected type
   `Prop`. Validation: after stripping the leading `∀` binders, the body must be
   an `Eq` whose left-hand side is an application of `f`; binder types must be
   closed (no dependent quantification, no local variables).
2. **Enumerate example inputs** for the binder types (`enumerate`): a fresh
   metavariable of the binder type is solved by the ordinary Canonical tactic
   pipeline (`getPremises → preprocess → toCanonical → runCanonical →
   postprocess`) with `count := k`, yielding `k` distinct inhabitants — e.g.
   `Nat.zero`, `Nat.succ Nat.zero`, … for `Nat` (the `k` terms found first in
   search order, not necessarily the `k` smallest). Results are sorted
   deterministically and memoized per `(type, count)` for the duration of the
   command, so two binders of the same type see the same terms. For several
   binders, per-type enumerations are combined into a cartesian product
   (`gatherTerms` / `enumerateInputs`), growing the per-type counts until at
   least `k` assignments exist. The enumeration runs in an empty local context,
   so neither `f` nor section variables can occur in example inputs.
3. **Instantiate** each predicate body with every enumerated assignment
   (`Expr.instantiateRev`), then evaluate the ground parts (`reduceGround`): a
   subterm not mentioning `f` that is a whole side of the equation or a direct
   argument of `f` is reduced to normal form, and resulting `Nat` literals are
   converted to `Nat.succ`/`Nat.zero` constructor form (up to `MAX_CTOR_NAT`).
   This turns `pred (1 + 1) = 1` into `pred 2 = 1` and evaluates ground
   right-hand sides such as `2 + 2`.
4. **Filter** the instantiated equations (`dedupExamples`): syntactically
   trivial equations (`a = a`, e.g. commutativity instantiated on the diagonal)
   and duplicates up to symmetry are dropped — from `∀ n m, f n m = f m n` both
   `f 0 1 = f 1 0` and its mirror image are generated, and keeping both would
   orient a rewrite loop. The surviving equations are logged.
5. **Search**: the equations are handed to `Canonical.PBE.toProblem` — the same
   backend as `#synthesize` — which translates the signature and the equations
   in a single `ToCanonicalM` run and attaches them as `equations` of the goal
   `Decl`; then `runCanonical`, `fromCanonical`, and verification against the
   instantiated equations.
6. **Prove the predicates** about the found candidate (`prove`). The candidate
   is let-bound under the function's name in place of the opaque local `f`
   (`withLetDecl`), so its defining equation reaches the solver as a reduction
   rule and found proofs delaborate referring to the function *by name*; the
   proposition — the predicate restated about the let binding — is handed to
   the ordinary Canonical tactic pipeline (`getPremises → preprocess →
   toCanonical → runCanonical → postprocess`) with the user-supplied premises
   and timeout. A found proof is delaborated and re-elaborated against the
   statement (`elaboratesAgainst`) — reconstructed proofs may embed `simp only`
   attributions that only make sense as syntax, and delaboration need not
   round-trip — and, if it survives, becomes a `theorem f_spec…` in the
   suggestion; once the suggestion is applied, the name resolves to the
   suggested `def`, which is definitionally equal to the let binding the proof
   was checked against. Predicates whose proof search fails, times out, or does
   not re-elaborate produce a warning instead.
7. **Suggest** via `TryThis`: the `def` alone if nothing was proved, otherwise
   the `def` followed by the proved `theorem`s as a single multi-command
   suggestion.

## Design decisions

- **Enumerated inputs are constructor spines**, produced by `fromCanonical`, so
  instantiated equations do not depend on `elimSpecial`'s small-numeral limit
  (which only converts literals ≤ 5). Ground reduction re-introduces literals
  (e.g. `2 + 2` reduces to the literal `4`), which `natLitToCtor` converts back
  to constructor form up to `MAX_CTOR_NAT = 64`.
- **Ground subterms under other heads are left alone.** In a right-hand side
  like `f 1 + 2` (recursive predicates), the arguments of `+` are not reduced;
  this is exactly the shape `#synthesize` already supports, handled by
  monomorphization and the translation's reduction rules.
- **`examples := k` counts instantiations, not surviving equations.** A
  predicate such as commutativity loses its diagonal and mirror-image
  instantiations to the trivial/duplicate filter, so it contributes fewer
  equations than `k`.

## Limitations / future work

- **Verification is best-effort.** A predicate that resists proof within the
  timeout only yields a warning — it does not distinguish "the proof search
  timed out" from "the function does not satisfy the predicate". From
  `∀ n m, f n m = f m n` alone with few examples, the solver may return a
  function that is not commutative (the `comm` smoke test does exactly this,
  and its warning is expected); increase `(examples := n)` to constrain the
  search further. Conversely, a true predicate may need a proof (e.g. by
  induction) that Canonical does not find within the timeout — increase the
  timeout or prove it manually.
- **Proof attempts cost time.** Each predicate gets its own proof search with
  the command's timeout, so the worst case adds `timeout × #predicates` per
  candidate on top of the synthesis search.
- **No dependent quantification.** Binder types must be closed types; `∀ (n :
  Nat) (h : n ≤ 2), …` is rejected. (A closed `Prop` binder is accepted — its
  "examples" are proofs found by Canonical — but this is untested territory.)
- Numerals above `MAX_CTOR_NAT` in instantiated equations stay opaque literals
  the search cannot compute with, as in `#synthesize`.
- `count`, `debug`, and the refinement UI are not exposed; only timeout,
  examples count, and premises are.

## Running

```bash
lake build ProgramByPredicate   # builds the command and elaborates the Examples file
```

`ProgramByPredicate/Examples.lean` contains end-to-end smoke tests; elaborating
it runs real searches, and any "no function found" outcome fails the build.
