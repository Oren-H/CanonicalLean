# Programming by Example

## Task

Make Canonical usable as a programming-by-example (PBE) tool. The user provides:

1. a function name and type signature, e.g. `f : Nat → Nat → Nat`;
2. a set of input–output examples, e.g. `f 0 0 = 0`, `f 0 1 = 1`, `f 1 1 = 2`.

The examples are attached to the Canonical search as *equational constraints* on the
declaration being synthesized, so the solver only returns terms that satisfy every
example. Canonical then searches for an inhabitant of the signature and suggests it
to the user as a complete Lean definition.

This replaces the manual workflow in `Canonical/lean/Test.lean` (in the Rust repo),
where the goal type is translated with `toCanonical`, the example spines
(`Nat.zero`, `Nat.succ (Nat.zero)`, …) are constructed by hand, and the resulting
`Decl` is fed to `runCanonical`. Here the whole pipeline is driven from ordinary
Lean syntax.

## Interface

```lean
#synthesize f : Nat → Nat → Nat
  | f 0 0 = 0
  | f 0 1 = 1
  | f 1 1 = 2
```

On success, the command reports `Try this: def f : Nat → Nat → Nat := fun a b => …`;
clicking the suggestion replaces the `#synthesize` command with the definition.

Optional arguments, mirroring the `canonical` tactic:

- **Timeout** (seconds, default 5): `#synthesize 30 f : … `
- **Premises** — extra constants made available to the search, useful when the
  target is best expressed in terms of existing functions:
  `#synthesize 10 [Nat.add] double : Nat → Nat | double 1 = 2 | double 2 = 4`

Each candidate returned by the solver is re-checked against the examples by
definitional equality (`isDefEq`) after reconstruction; a candidate that fails an
example produces a warning, so a silent translation or solver regression cannot
masquerade as success.

## How it works

Implementation: `ProgramByExample.lean` (command `#synthesize`, namespace
`Canonical.PBE`). Pipeline, all inside `runTermElabM`:

1. **Elaborate the signature** `T` with `Term.elabType`.
2. **Introduce the function as a local variable** (`withLocalDeclD f T`), then
   elaborate each example clause against expected type `Prop`. Validation: each
   example must be an `Eq` whose left-hand side is an application of `f`.
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
   examples, and present `def f : T := …` via `TryThis`. Recursor applications in
   the suggestion are rendered as pattern matching — definition-level equations,
   inline `match`, or `let rec` — by `R2M.mkDefCommand`; see `RecursorToMatch.md`.

## Design decisions

- **`f` is excluded from the problem's premises.** The local variable `f` exists
  only so the examples elaborate; the translation skips it when folding the local
  context (otherwise the solver could "solve" the problem with `f := f`). Instead,
  occurrences of `f` are identified with the declaration under synthesis: `toHead`
  names the local variable `f.<uniq>`, and a post-pass renames that head to the
  declaration name everywhere in the translated rules. Because renaming applies to
  both sides, examples may mention `f` recursively on the right-hand side
  (e.g. `f 2 = f 1 + 2`).
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
  premises are. Extending the command with the tactic's `optConfig` is
  straightforward if needed.
- Quality of results with recursive examples depends entirely on the solver's
  handling of speculative recursor placement (program-synthesis mode).

## Running

```bash
lake build ProgramByExample   # builds the command and elaborates the Examples file
```

`ProgramByExample/Examples.lean` contains end-to-end smoke tests; elaborating it
runs real searches, and any "no function found" outcome fails the build.
