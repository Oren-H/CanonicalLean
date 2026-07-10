import Lake
open Lake DSL

/-- Mirrors the releases of Lean -/
def buildArchive :=
  if System.Platform.isWindows then "windows"
  else if System.Platform.isOSX then
    if System.Platform.target.startsWith "x86_64" then "darwin"
    else "darwin_aarch64"
  else if System.Platform.numBits == 32 then "linux"
  else if System.Platform.target.startsWith "aarch64" then "linux_aarch64"
  else "linux_x86"

package Canonical where
  preferReleaseBuild := true
  buildArchive := buildArchive ++ ".tar.gz"

target canonical pkg : Dynlib := do
  let libPath := pkg.sharedLibDir / nameToSharedLib "canonical_lean"
  let lib := { path := libPath, name := "canonical_lean" }
  if !(← libPath.pathExists) then
    (← pkg.gitHubRelease.fetch).mapM (fun _ => do pure lib)
  else return Job.pure lib

@[default_target]
lean_lib Canonical where
  precompileModules := true
  moreLinkLibs := #[canonical]

@[test_driver]
lean_lib Test

/-- Programming-by-example problem construction for the `synthesize` tactic; see `Program Synthesis/ProgramByExample.md`. -/
lean_lib ProgramByExample where
  srcDir := "Program Synthesis"
  roots := #[`ProgramByExample]

/-- Predicate instantiation and verification for the `synthesize` tactic; see `Program Synthesis/ProgramByPredicate.md`. -/
lean_lib ProgramByPredicate where
  srcDir := "Program Synthesis"
  roots := #[`ProgramByPredicate]

/-- The `synthesize` tactic — program synthesis from examples and predicates inside `def … := by`. -/
lean_lib Synthesize where
  srcDir := "Program Synthesis"
  roots := #[`Synthesize, `Synthesize.Examples]

/-- Recursor-application → `match`-syntax rendering for synthesis suggestions; see `Program Synthesis/RecursorToMatch.md`. -/
lean_lib RecursorToMatch where
  srcDir := "Program Synthesis"
  roots := #[`RecursorToMatch, `RecursorToMatch.Examples]
