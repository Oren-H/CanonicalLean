# Programming by Predicate

## Task

Make Canonical usable as a programming-by-predicate tool. The user provides:

1. a `def` with a name and type signature, e.g. `def f : Nat → Nat → Nat`;
2. a set of universally quantified predicates, e.g. `∀ n : Nat, f n 0 = n` or
   `∀ n m : Nat, f n m = f m n`.

Instead of asking the user for input–output examples (see
`ProgramByExample.md`), the tactic *generates* them: Canonical's `count` option
turns the search procedure into an enumerator, which produces example inhabitants
of the quantified variables' types. Instantiating a predicate with these examples
yields concrete example equations, which are attached to the search as equational
constraints on the declaration being synthesized — from that point on, the
pipeline is exactly that of plain input–output examples.

## Interface

The user-facing interface is the `synthesize` tactic (`Synthesize.lean`, which
replaced the `#synthesize_pred` and `#synthesize` commands), used in the body
of the very definition being written:

```lean
def pred : Nat → Nat := by
  synthesize
  | pred 0 = 0
  | ∀ n : Nat, pred (n + 1) = n
```

In the clauses, `pred` refers to the definition's own name — the auxiliary
local constant Lean introduces while elaborating the `def`. On success, the
tactic logs the instantiated example equations, admits the goal (like
`canonical`), and reports `Try this: exact fun a => …`; clicking the
suggestion replaces the tactic, clauses included, with the synthesized term.

Because the equations only *sample* the predicates, the tactic then attempts
to **prove** each predicate about the synthesized function (with the same
timeout per predicate), let-bound under the definition's name (see step 6).
The proofs found are logged as ready-to-paste `theorem`s:

```lean
the synthesized function provably satisfies 2/2 clause(s); paste after the definition:

theorem pred_spec_1 : pred 0 = 0 := Eq.refl Nat.zero

theorem pred_spec_2 : ∀ n : Nat, pred (n + 1) = n := fun n ↦ Eq.refl n
```

(`f_spec` if there is a single predicate, `f_spec_<i>` numbered in clause order
otherwise). Each predicate that could not be proved produces a warning: the
definition is then only guaranteed to satisfy the instantiated equations, not
the predicate itself — either because the search timed out, or because the
function genuinely does not satisfy it.

When proofs are found, the suggested term is displayed raw — the pasted
definition must unfold to the very term the proofs were checked against.
Otherwise recursor applications in the suggestion are rendered as pattern
matching by `R2M.delabR2M` (see `RecursorToMatch.md`), as are the proofs
themselves by `delabProof`.

Each clause is a (possibly) universally quantified equation whose left-hand side
is an application of the function under synthesis; both sides may mention the
function. A clause without binders is an ordinary input–output example, so the
predicate pipeline subsumes the example pipeline. Optional arguments:

- **Timeout** (seconds, default 5): `synthesize 30`
- **Examples per predicate** (default 3): `synthesize (examples := 5)`
- **Premises** — extra constants made available to the search:
  `synthesize 10 [Nat.add]`

Each candidate returned by the solver is re-checked against the instantiated
equations by definitional equality after reconstruction; a failure produces a
warning.

## How it works

Implementation: this file, `ProgramByPredicate.lean` (namespace
`Canonical.PBP`), provides the enumeration, instantiation, and verification
machinery; the tactic driving it is in `Synthesize.lean`. Pipeline:

1. **The signature is the tactic goal**, and the function is the auxiliary
   local constant Lean introduces for the definition being elaborated; each
   clause elaborates against expected type `Prop` with the definition's name
   referring to that local (the `_recApp` metadata the elaborator attaches to
   its applications is stripped). Validation: after stripping the leading `∀`
   binders, the body must be an `Eq` whose left-hand side is an application of
   `f`; binder types must be closed (no dependent quantification, no local
   variables); `f`'s type must be the goal itself — binders to the left of the
   `def`'s colon are rejected.
2. **Enumerate example inputs** for the binder types (`enumerate`): a fresh
   metavariable of the binder type is solved by the ordinary Canonical tactic
   pipeline (`getPremises → preprocess → toCanonical → runCanonical →
   postprocess`) with `count := k`, yielding `k` distinct inhabitants — e.g.
   `Nat.zero`, `Nat.succ Nat.zero`, … for `Nat` (the `k` terms found first in
   search order, not necessarily the `k` smallest). Results are sorted
   deterministically and memoized per `(type, count)` for the duration of the
   tactic, so two binders of the same type see the same terms. For several
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
5. **Search**: the equations are handed to `Canonical.PBE.toProblem` — the
   example backend of `ProgramByExample.md` — which translates the signature
   and the equations in a single `ToCanonicalM` run and attaches them as
   `equations` of the goal `Decl`; then `runCanonical`, `fromCanonical`, and
   verification against the instantiated equations.
6. **Prove the predicates** — about the candidate let-bound under the
   function's name (`provePredicatesLetBound`, `withLetDecl`): the definition
   itself does not exist yet while the tactic elaborates its body, so the
   binding's defining equation reaches the solver as a single reduction rule
   to the raw term, and each predicate is restated about the binding.
   Definitionally true predicates are proved directly with `Eq.refl`
   (`rflProof?`), without invoking the solver — this also rescues specs like
   `comm 1 1 = 2` whose solver reconstruction routes through propositional
   rewrites (e.g. `Nat.succ.injEq`) that do not re-elaborate as tactics.
   Otherwise the proposition is handed to the ordinary Canonical tactic
   pipeline (`prove`: `getPremises → preprocess → toCanonical → runCanonical
   → postprocess`) with the user-supplied premises and timeout. A found proof
   is delaborated and re-elaborated against the statement
   (`elaboratesAgainst`) — reconstructed proofs may embed `simp only`
   attributions that only make sense as syntax, and delaboration need not
   round-trip — and, if it survives, becomes a logged `theorem f_spec…`;
   proofs refer to the function by name, which, once pasted after the
   applied suggestion, resolves to the definition — whose value is the very
   term they were checked against. Predicates whose proof search fails,
   times out, or does not re-elaborate produce a warning either way.
7. **Suggest** `exact …` via `TryThis` and admit the goal. When theorems were
   found the suggested term is displayed raw, so that the pasted definition
   unfolds to the term the proofs elaborate against — a `match`/`let rec`
   rendering compiles through `brecOn` and auxiliary matchers, against which
   proofs that inline the raw recursors in their motives need not typecheck.
   With nothing to stay consistent with, recursor applications are rendered
   as pattern matching (`R2M.delabR2M`, gated by `R2M.roundTrips`).

## Design decisions

- **Enumerated inputs are constructor spines**, produced by `fromCanonical`, so
  instantiated equations do not depend on `elimSpecial`'s small-numeral limit
  (which only converts literals ≤ 5). Ground reduction re-introduces literals
  (e.g. `2 + 2` reduces to the literal `4`), which `natLitToCtor` converts back
  to constructor form up to `MAX_CTOR_NAT = 64`.
- **Ground subterms under other heads are left alone.** In a right-hand side
  like `f 1 + 2` (recursive predicates), the arguments of `+` are not reduced;
  this is exactly the shape the example pipeline already supports, handled by
  monomorphization and the translation's reduction rules.
- **`examples := k` counts instantiations, not surviving equations.** A
  predicate such as commutativity loses its diagonal and mirror-image
  instantiations to the trivial/duplicate filter, so it contributes fewer
  equations than `k`.
- **Suggestion and proofs stay consistent.** The proofs are checked against
  the let-bound raw candidate, so whenever proofs are logged the suggestion is
  that raw term; the prettier `match`/`let rec` rendering is reserved for
  candidates without accompanying theorems.

## Limitations / future work

- **Verification is best-effort.** A predicate that resists proof within the
  timeout only yields a warning — it does not distinguish "the proof search
  timed out" from "the function does not satisfy the predicate". From
  `∀ n m, f n m = f m n` alone with few examples, the solver may return a
  function that is not commutative (a warning on the `add` smoke test is
  expected for this reason); increase `(examples := n)` to constrain the
  search further. Conversely, a true predicate may need a proof (e.g. by
  induction) that Canonical does not find within the timeout — increase the
  timeout or prove it manually.
- **Proofs run against the raw candidate.** The former `#synthesize_pred`
  command elaborated the suggested match-form `def` in a sandboxed copy of
  the command state and proved the predicates against its equation lemmas —
  rules the solver is markedly better at proving with than a delta rule to a
  recursor term. Command elaboration is not available from within a tactic,
  so the tactic proves against the let-bound raw term; recovering match-form
  proving (e.g. by handing the solver the candidate's ι-reduction equations
  directly) is future work.
- **Proof attempts cost time.** Each predicate gets its own proof search with
  the tactic's timeout, so the worst case adds `timeout × #predicates` per
  candidate on top of the synthesis search.
- **No dependent quantification.** Binder types must be closed types; `∀ (n :
  Nat) (h : n ≤ 2), …` is rejected. (A closed `Prop` binder is accepted — its
  "examples" are proofs found by Canonical — but this is untested territory.)
- Numerals above `MAX_CTOR_NAT` in instantiated equations stay opaque literals
  the search cannot compute with, as for plain input–output examples.
- `count`, `debug`, and the refinement UI are not exposed; only timeout,
  examples count, and premises are.

## Running

```bash
lake build Synthesize   # builds the tactic and elaborates the Examples file
```

`Synthesize/Examples.lean` contains end-to-end smoke tests; elaborating it
runs real searches, and any "no function found" outcome fails the build.
