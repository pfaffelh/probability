import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"v4.29.0"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"main"
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.29.0"

package Probability where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib Probability where

lean_exe «blueprint-gen» where
  root := `ProbabilityMain
