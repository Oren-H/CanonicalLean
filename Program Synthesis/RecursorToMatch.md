# Recursor → match

## Task

Canonical returns β-normal η-long terms whose head symbols are often recursors, so
the Program Synthesis commands used to suggest definitions like

```lean
def add : Nat → Nat → Nat := fun a b => Nat.rec (motive := fun _ => Nat) a (fun n ih => ih.succ) b
```

Render those recursor applications as pattern matching instead, the way a person
would write the function:

```lean
def add : Nat → Nat → Nat
  | a, Nat.zero => a
  | a, Nat.succ n => (add a n).succ
```

The conversion applies only to `#synthesize` and `#synthesize_pred`; the
`canonical` tactic's suggestions are unchanged. In `#synthesize_pred` the
converted definition is more than display: it is elaborated in a sandboxed
command state and the predicate proofs are attempted *about it*, so the solver
works with its match-form equation lemmas (see `ProgramByPredicate.md`,
step 6).

## Interface

Implementation: `RecursorToMatch.lean` (namespace `Canonical.R2M`). Three renderings,
chosen by the shape of the recursor application:

1. **Definition-level equations** — a *recursive* elimination (some minor premise
   uses its inductive hypothesis) sitting at the top of the synthesized body,
   eliminating one of the definition's own argument binders. Inductive hypotheses
   become recursive calls of the definition's name (example above).
2. **Inline `match`** — a *non-recursive* elimination (all inductive hypotheses
   unused; a case analysis), anywhere in the term. `False.rec`/`Empty.rec` render
   as `nomatch`. Arguments applied beyond the major premise are β-pushed into the
   branches.
3. **`let rec go`** — a recursive elimination nested where equations cannot reach
   (under another application, or eliminating something other than an argument
   binder):

   ```lean
   def double : Nat → Nat := fun n =>
     (let rec go : Nat → Nat := fun x =>
         match x with
         | Nat.zero => Nat.zero
         | Nat.succ k => (go k).succ.succ;
       go n).succ
   ```

   `go` recurses structurally on its argument, so the pasted definition elaborates.

Entry points:

- `delabR2M : Expr → MetaM Term` — delaborate with the conversion enabled
  (renderings 2 and 3); used by `#synthesize_pred` for theorem proofs.
- `mkDefCommand fnameId sig f t type : TermElabM (TSyntax `command)` — build the
  whole `def` suggestion, preferring rendering 1; used by both commands for the
  synthesized function. `f` is the local variable standing for the function under
  synthesis (its user name is the definition's name printed in recursive calls).

## How it works

Renderings 2 and 3 are a pretty-printing concern only, implemented as a single
`@[delab app]` delaborator gated behind the (unregistered, programmatic) option
`canonical.recToMatch`, which only the Program Synthesis display code sets. The
gate keeps the `canonical` tactic and every other consumer of the delaborator
untouched, and the delaborator's `failure` falls through to the builtin
application delaborator, so *one* ineligible recursor degrades to the raw
display locally while the rest of the term still converts. Because branch
right-hand sides are delaborated by re-entering `delab`, nested recursors
convert recursively.

- `analyzeRecApp?` decomposes a fully-applied `.rec` application (params, motive,
  minors, major, residual arguments) and reads the field/hypothesis structure of
  each minor premise off the recursor's *type*, where the motive is a bound
  variable — each hypothesis binder must be literally `motive fld`, which also
  identifies the field it recurses on.
- Minor premises are entered with `withFreshBinders`, which insists on syntactic
  λ-binders (η-long terms always have them) and freshens names against the local
  context, so printed output cannot capture outer variables.
- Inductive-hypothesis substitution is *head replacement*: since terms are η-long,
  an IH occurrence is always fully applied, so replacing the IH variable with a
  partial application (`go fld`, or `f x₁ … fld …` for equations) needs no
  β-reduction and picks up residual arguments by plain application.

Rendering 1 (`mkEquationDef?`) additionally requires: the major premise is one of
the body's λ-binders, any residual arguments are exactly the trailing binders in
order, and the parameters and motive do not depend on the binders. Each equation
is then literally the ι-reduction of the recursor at one constructor. Within an
equation, occurrences of the major binder become the constructor value and
occurrences of the trailing binders become that equation's own pattern variables;
pattern variables unused on the right-hand side print as `_`. Constructor
patterns are delaborated with `pp.fieldNotation` off (`k.succ` is not a pattern).

## Fallbacks

The feature must never make a suggestion worse than today's raw display:

| Trigger | Behavior |
| --- | --- |
| not a `.rec` head; under-applied; multiple motives; indexed inductive (incl. `Eq.rec`, `Acc.rec`); mutual/nested inductive; reflexive inductive (`∀ a, motive (fld a)` hypotheses); non-λ minor (e.g. `.mdata`-wrapped attribution); any exception | delaborator fails over per node → raw recursor display for that node |
| equation preconditions unmet | `:=`-style body with renderings 2/3 |
| `:=`-style body fails the round-trip | today's output, byte for byte |
| converted theorem proof fails `elaboratesAgainst` | retry with the plain delaboration |

The round-trip check (`roundTrips`) re-elaborates the converted body against the
signature and compares with the original using the *kernel*'s definitional
equality — `Meta.isDefEq` deliberately keeps matcher applications stuck on
non-constructor discriminants, so it cannot see through `match`. The original is
`Meta.check`ed first to pin the universe metavariables that Canonical's
reconstruction leaves behind (universe levels are not translated). Bodies
containing `let rec` cannot be re-elaborated outside a definition and are
accepted as-is; they are correct by construction and covered by the paste tests.

## Limitations / future work

- Indexed inductive families (`Eq.rec`, `Acc.rec`, vectors, …), mutual and nested
  inductives, and reflexive inductives fall back to the raw display.
- Equation-style rendering requires the residual arguments in trailing order; a
  permuted shape falls back to `let rec` inside a `:=`-style body.
- Constructor patterns print qualified (`Nat.zero`, `Nat.succ k`) rather than as
  numeric literals (`0`, `k + 1`); a literal-aware pattern printer would read
  better still.
- `Nat.rec`-free suggestions (e.g. `fun a ↦ a + a`) pass through unchanged.

## Running

```bash
lake build RecursorToMatch   # unit tests (#guard_msgs), paste tests, and an e2e search
```

`RecursorToMatch/Examples.lean` pins exact converter output on handcrafted
recursor terms with `#guard_msgs`, re-elaborates representative suggested texts
(`def add2 …`, spec-theorem pairs) with `rfl` checks, and runs one real
`#synthesize` end to end. The solver's found term varies run to run, so the e2e
message is deliberately not pinned.
