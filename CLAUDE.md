# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

The Lean 4 frontend for [Canonical](https://github.com/chasenorman/Canonical), an exhaustive term-synthesis engine for dependent type theory. The `canonical` tactic proves theorems, synthesizes programs, and constructs objects. The actual search engine is written in Rust and shipped as a prebuilt shared library (`canonical_lean`); this repo contains only the Lean side: the tactic, the translation to/from Canonical's term representation, and preprocessing passes.

This working copy is a fork: `origin` is Oren-H/CanonicalLean, `upstream` is chasenorman/CanonicalLean.

## Commands

- `lake build` — build. On first build, Lake fetches the prebuilt Rust shared library from the GitHub release (`preferReleaseBuild` + the `canonical` Dynlib target in `lakefile.lean`). If `.lake/build/lib/libcanonical_lean.*` already exists, it is reused — so to test against a locally built Rust library, drop it in that directory.
- `lake test` — runs the test driver, which just builds `Test.lean` (`example : Nat := by canonical`). There is no separate test framework; correctness is checked by elaborating Lean files that use the tactic.
- Toolchain is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.30.0`); elan handles it automatically.
- Releases are manual: the `Upload` GitHub workflow takes a release tag and a Rust-side tag, downloads the matching shared library from chasenorman/Canonical releases, builds, and runs `lake upload`.

## Architecture

The `canonical` tactic (Canonical/Tactic.lean) is a pipeline:

1. **Premise collection** (`getPremises`, Canonical/Main.lean) — merges user-supplied premises (`canonical [foo, bar]`) with optional premise-selector suggestions; splits out structure names for destruct.
2. **Preprocessing** — `Destruct.destructCanonical` (Canonical/Destruct/) unpacks structure types (Prod, And, Sigma, Subtype, ...) in the goal; Monomorphize (Canonical/Monomorphize/) resolves typeclass instances into monomorphic symbols. Both return a `reconstruct` function to undo the transformation on the resulting term. Both are also exposed as standalone tactics (`destruct`, `monomorphize`).
3. **Translation to Canonical** (`toCanonical`, Canonical/ToCanonical/) — converts the goal, local context, and premises into Canonical's representation: β-normal η-long λ-terms (`Canonical.Expr` / `Spine` / `Decl` / `Rule`, defined in Canonical/Basic.lean). Definitional equations and applicable simp lemmas become reduction `Rule`s. Lean Π-types that can't be translated directly are wrapped in the `Pi` structure from Canonical/Symbols.lean.
4. **Search via FFI** — `canonical : Decl → UInt64 → USize → IO CanonicalResult` is an `@[extern]` opaque implemented in the Rust library. `runCanonical` runs it on a dedicated task and polls for interruption so the tactic is cancellable (via the `cancel` extern).
5. **Translation back** (`fromCanonical`, Canonical/FromCanonical.lean) — rebuilds a Lean `Expr` from the result. Rule attributions recorded in `premiseRules`/`goalRules` become `simp only` / `simpa only` wrappers, embedded in the term via `.mdata` and rendered by the `delab mdata.canonical` delaborator in Symbols.lean. `<synthInstance>` heads are re-resolved with `trySynthInstance`.
6. **Presentation** — `Try this: exact ...` suggestions via `TryThis`, or an error naming the knob to turn (timeout, premises).

Tactic options come from `Config` in Canonical/Basic.lean (`count`, `pi`, `debug`, `refine`, `simp`, `monomorphize`, `destruct`, `suggestions`), e.g. `canonical 30 (count := 10) [premise]`. `(debug := true)` dumps the inhabitation problem to `debug.json` instead of searching.

**Refinement UI**: `canonical (refine := true)` starts a server in the Rust library (`refine` extern) and displays an infoview widget (Canonical/Refine.lean + refine.js) that iframes `localhost:3000`; the `Canonical.getRefinementStr` RPC method turns the current partial term into a `refine ...` tactic edit.

## Constraints

- **FFI ABI**: the mutual structures in Canonical/Basic.lean (`Decl`, `Spine`, `Expr`, `Rule`) and `CanonicalResult` in Canonical/Main.lean are read field-by-field by the Rust library. Changing their fields or field order breaks the FFI and must be coordinated with a matching change in chasenorman/Canonical.
- **Module system**: every file uses Lean's module system (`module` header, `public import`, `public meta import`, `public section`). Keep imports minimal and only `public` what downstream files need — the history deliberately minimizes imports. Tactic-defining files use `meta` sections/imports.
- Because the search engine is a separate binary, most behavior changes here are about translation fidelity: what gets sent (ToCanonical, preprocessing) and how results are rebuilt (FromCanonical). Bugs typically show up as reconstruction failures or unprovable-but-should-be-provable goals rather than Lean compile errors.
