# Programming by Example

## Task

Make Canonical usable as a programming-by-example (PBE) tool. The user provides:

1. a `def` with a name and type signature, e.g. `def f : Nat → Nat → Nat`;
2. a set of input–output examples, e.g. `f 0 0 = 0`, `f 0 1 = 1`, `f 1 1 = 2`.

The examples are attached to the Canonical search as *equational constraints* on the
declaration being synthesized, so the solver only returns terms that satisfy every
example. Canonical then searches for an inhabitant of the signature and suggests it
to the user.

This replaces the manual workflow in `Canonical/lean/Test.lean` (in the Rust repo),
where the goal type is translated with `toCanonical`, the example spines
(`Nat.zero`, `Nat.succ (Nat.zero)`, …) are constructed by hand, and the resulting
`Decl` is fed to `runCanonical`. Here the whole pipeline is driven from ordinary
Lean syntax.

## Interface

The user-facing interface is the `synthesize` tactic (`Synthesize.lean`, which
replaced the `#synthesize` command and subsumes both this file's example
pipeline and `ProgramByPredicate.md`'s quantified clauses), used in the body of
the very definition being written:

```lean
def f : Nat → Nat → Nat := by
  synthesize
  | f 0 0 = 0
  | f 0 1 = 1
  | f 1 1 = 2
```

In the clauses, `f` refers to the definition's own name — the auxiliary local
constant Lean introduces while elaborating the `def`. On success, the tactic
admits the goal (like `canonical`) and reports `Try this: exact fun a b => …`;
clicking the suggestion replaces the tactic, clauses included, with the
synthesized term.

Optional arguments, mirroring the `canonical` tactic:

- **Timeout** (seconds, default 5): `synthesize 30`
- **Premises** — extra constants made available to the search, useful when the
  target is best expressed in terms of existing functions:
  `synthesize 10 [Nat.add]`

Each candidate returned by the solver is re-checked against the examples by
definitional equality (`isDefEq`) after reconstruction; a candidate that fails an
example produces a warning, so a silent translation or solver regression cannot
masquerade as success.

## How it works

Implementation: this file, `ProgramByExample.lean` (namespace `Canonical.PBE`),
provides the problem construction; the tactic driving it is in
`Synthesize.lean`. Pipeline:

1. **The signature is the tactic goal** — the declared type of the `def`.
2. **The function is the definition's auxiliary local**: Lean introduces a
   local constant for `f` while elaborating `def f : T := by …` (so the body
   can be recursive), and the clauses elaborate against expected type `Prop`
   with `f` referring to it (the `_recApp` metadata the elaborator attaches to
   its applications is stripped). Validation: each example must be an `Eq`
   whose left-hand side is an application of `f`, and `f`'s type must be the
   goal itself — binders to the left of the `def`'s colon are rejected.
3. **Translate in a single `ToCanonicalM` run** (`toProblem`/`toProblem_`, modeled
   on `toCanonical`/`toCanonical_` from `Canonical/ToCanonical/Main.lean`):
   - the signature is translated with `toTyp`;
   - user premises are added with `definePremise`;
   - each example is translated with `toRule` — the same function that turns
     definitional equations and simp lemmas into reduction `Rule`s — producing a
     `Rule` whose `lhs` is a spine of the example's arguments and whose `rhs` is
     the translated output value;
   - relevant simp lemmas are added (`addSimpLemmas`), and all collected symbol
     definitions become the `lets` of the goal type.

   A single monad run matters: symbols that appear only in the examples (e.g.
   constructors of an argument type) must land in the same definition table as the
   symbols of the signature.
4. **Assemble the problem `Decl`**: `{ name := "f", type := some T', equations := rules }`.
   The equations on the goal declaration are exactly the equational-constraint
   mechanism exercised by the Rust repo's `lean/Test.lean` — the `program-synthesis`
   branch of the FFI reads the full `Decl`, equations included.
5. **Search** with `runCanonical` (cancellable, honors the timeout).
6. **Reconstruct** each returned term with `fromCanonical`, verify it against the
   examples, admit the goal, and present `exact …` via `TryThis`, with recursor
   applications rendered as pattern matching — inline `match` or `let rec` —
   via `R2M.delabR2M`; see `RecursorToMatch.md`.

## Design decisions

- **`f` is excluded from the problem's premises.** The local variable `f` exists
  only so the examples elaborate; the translation skips it when folding the local
  context (otherwise the solver could "solve" the problem with `f := f`) — the
  fold already skips auxiliary declarations, which is what the definition's local
  is. Instead, occurrences of `f` are identified with the declaration under
  synthesis: `toHead` names the local variable `f.<uniq>`, and a post-pass
  renames that head to the declaration name everywhere in the translated rules.
  Because renaming applies to both sides, examples may mention `f` recursively on
  the right-hand side (e.g. `f 2 = f 1 + 2`).
- **`destruct := false`.** The tactic's destruct preprocessing rewrites a *goal
  metavariable* and is undone by a `reconstruct` closure; there is no goal
  metavariable here. With destruct disabled, `onTypeConst` defines structure
  constructors directly, so signatures involving `Prod` etc. still translate.
  `monomorphize` and `simp` keep their defaults (`true`) — monomorphization in
  particular is what resolves `OfNat` numerals in examples down to `Nat.succ`/
  `Nat.zero` constructor spines.
- **Name freshness is enforced**: if the chosen function name collides with a
  symbol that occurs in the problem, the command errors out rather than producing
  an ambiguous constraint set.

## Limitations / future work

- **Small numerals only.** `elimSpecial` converts natural-number literals ≤ 5 into
  constructor form; larger literals stay opaque literals the search cannot compute
  with. Keep example values small (or provide premises that handle numerals).
- **Monomorphic signatures.** No auto-bound implicits / universe polymorphism in
  the signature.
- `count`, `debug`, and the refinement UI are not exposed; only timeout and
  premises are. Extending the tactic with `canonical`'s `optConfig` is
  straightforward if needed.
- Quality of results with recursive examples depends entirely on the solver's
  handling of speculative recursor placement (program-synthesis mode).

## Running

```bash
lake build Synthesize   # builds the tactic and elaborates the Examples file
```

`Synthesize/Examples.lean` contains end-to-end smoke tests; elaborating it
runs real searches, and any "no function found" outcome fails the build.
