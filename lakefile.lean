import Lake
open Lake DSL

package «safe-verity» where
  version := v!"0.1.0"

-- Verity, mab-xyz fork: branch `ours` + `feat/copybytes-struct-member` (copyBytes on a struct member).
require verity from git
  "https://github.com/mab-xyz/verity.git"@"56702299ff47d95d0b71b7a5d699c050f1a9db17"

@[default_target]
lean_lib «Safe» where
  roots := #[`Safe]

/-- Emits Yul + ABI: `lake exe safe-compile OUT_DIR`. -/
lean_exe «safe-compile» where
  root := `SafeCompile
  supportInterpreter := true

-- Scratch: minimal reproductions of fork bugs (not part of the library).
lean_lib «Repro» where
  globs := #[.andSubmodules `Repro]

lean_exe «repro-compile» where
  root := `ReproCompile
  supportInterpreter := true
