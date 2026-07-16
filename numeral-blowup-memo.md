# Numerals in `synthesize` specs blow up the search — findings and a proposed fix

*Oren — for discussion; all measurements from the `program-synthesis` branches of Canonical/CanonicalLean, July 2026.*

## Summary

Example equations containing Nat values above a small, problem-dependent threshold (6 for pred, ~16–20 for addition) make the solver blow past any timeout, trip its `guard_overflow()` panic (surfacing to the Lean user as `error: Stack overflow.`), or get OOM-killed silently at ~3 GB. Using the `steps`/`attempted_resolutions`/`branching` counters that come back over the FFI, I can show the cause is a superexponential explosion in **search effort**, not in per-constraint checking cost: throughput stays flat at ~120–270k steps/s across succeeding and failing runs, and — the decisive experiment — the failing problem stays unsolved even when the exact solution is handed to the search as a premise.

## Minimal repro pair

The frontend sends numerals ≤ 64 as unary `succ` spines (`natLitToCtor`/`MAX_CTOR_NAT` in ProgramByPredicate.lean). These two problems are identical except the last value:

```
def pv : Nat → Nat := by                 def pv : Nat → Nat := by
  synthesize                               synthesize
  | pv 0 = 0                               | pv 0 = 0
  | pv 1 = 0                               | pv 1 = 0
  | pv 2 = 1                               | pv 2 = 1
  | pv 5 = 4      -- 21 steps, 10ms        | pv 6 = 5      -- 10.9M steps, not found in 60s
```

## Measurements

Solver effort (FFI call only, measured with a probe tactic that logs `CanonicalResult` stats):

| problem | largest value | outcome | steps | attempted | branching | time |
|---|---|---|---|---|---|---|
| identity, `g 60 = 60` | 60 | found | 2 | 14 | — | 12ms |
| single example `sg 6 = 5` / `sg 7 = 6` | 7 | found | 13 / 4 | ≤ 97 | — | 12ms |
| pred, 4 examples | 3 / 4 / 5 | found | 24 / 13 / 21 | ≤ 204 | ~4 | ~11ms |
| pred, 4 examples | **6** | **not found** | 10.9M | 88.7M | 3.02 | 60s timeout |
| pred, 4 examples **+ `Nat.pred` premise** | 5 | found | 76 | 678 | 4.5 | 13ms |
| pred + `Nat.pred` premise | **6** / 24 | **not found** | 8.0M / 7.2M | 74M / 73M | 4.7 | 30s timeout |
| addition, 6 examples (`f 3 9 = 12`) | 12 | found | 556k | 6.0M | 4.59 | 2.2s |
| addition, same shape ×2 (`f 6 18 = 24`) | 24 | not found | 2.3M | 27.3M | 3.02 | 20s timeout |

End-to-end (`synthesize 60`, wall clock): addition with max value ≤ 16 solves in ~3s; 18 reproducibly panics `Stack overflow.`; 20 is SIGKILLed with no output (exit 137, ~3 GB max RSS in one premise configuration); 24–60 burn the full timeout on 6 cores. Values > 64 stay opaque literals (`f (succ²⁴ zero) 72 = 96`), so those examples are unsatisfiable by computation and the search silently runs to timeout.

## What the numbers rule out and in

1. **Not per-step cost.** Throughput is flat (~120–270k steps/s) between succeeding and failing runs; doubling the numerals makes each step at most ~2× slower while the outcome goes from 2s to never.
2. **Not term size per se.** Building or matching a `succ⁶⁰` spine is trivial (identity: 2 steps; single big example: ~15 steps — a constant function satisfies it).
3. **Not the depth of the needle in the search order.** With `Nat.pred` as a premise, `fun n => Nat.pred n` is a first-level, two-node candidate, and verifying it against `pred (succ⁶ zero) = succ⁵ zero` is one rule application — yet the search does 8M steps in 30s without returning it.
4. **The trigger is a mix.** Blow-up requires discriminating small examples (`p 0 = 0, p 1 = 0, p 2 = 1`, forcing case analysis) *together with* one value ≥ the threshold. Then the equations stop pruning: the failing runs sit at branching ≈ 3.02 with roughly a third to a half of attempted resolutions succeeding — the DFS is productively wandering in the space of partial terms that stay one-step-consistent with the deep spine equation, of which there are combinatorially many in its depth.

## Where this lives in the code

Goal `equations` become `Equation` constraints installed on the root metavariable (`Prover::new`, canonical-core prover.rs:72–81; `IRDecl::to_problem`, canonical-compat ir.rs:101–109), suspended on stuck metas and re-tested generate-and-test in `Meta::test_assignment` (core.rs:116). The user-visible `Stack overflow.` is `guard_overflow()` (core.rs:22) escaping through the FFI's `catch_unwind`; the OOM kill produces no output at all.

## Proposed fix

**Primary — constraint-directed assignment for rigid ground equations.** When a metavariable carries rigid `Equation` constraints whose other side reduces to a ground constructor spine, derive the admissible assignment(s) for it directly from the constraints — propagating eagerly through `succ` layers — instead of enumerating the full `iter_unify` context and filtering via `test_assignment`. Ground example equations should *determine* assignments where they can, not merely veto them; today each layer of a `succ⁶`-spine equation is a fresh choice point interleaved with every other open meta in DFS order, which is exactly the combinatorial space the counters show the search wandering in.

**Alternative A — compact literal spines.** Represent constructor chains as lazy compact literals (peel `succ` on demand). This caps term size at O(1) in the numeral, removes the depth-linear recursion in `whnf`/`pattern_match` that trips `guard_overflow`, and would compose with a frontend that stops expanding numerals unarily. It doesn't by itself fix the search-effort explosion if the wandering is over candidate structure rather than spine depth, so I'd treat it as complementary.

**Alternative B — diagnosability and graceful failure.** Expose `prove`'s verbose/entropy stats through the FFI, bound memory, and turn `guard_overflow`/OOM into a clean "resource limit" result. These failure modes currently reach Lean users as an opaque elaboration error or a silently dead process, which made this investigation harder than it needed to be.

Separately, on the frontend side (my repo): numerals > `MAX_CTOR_NAT = 64` stay opaque literal symbols with no rules, so any example containing one is quietly unsatisfiable — I'll add a warning/rejection there regardless of what we do here.

I can send the minimal pair as replayable `debug.json` dumps for the CLI entrypoint if useful.
