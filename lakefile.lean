import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «TraceLogic» where

@[default_target]
lean_lib «TraceLogic» where

@[default_target]
lean_lib «RequestProject» where
