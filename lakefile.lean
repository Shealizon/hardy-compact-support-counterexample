import Lake
open Lake DSL

package «hardy-compact-support-counterexample» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib HardyCompactSupport where
