import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package «matti-playground» where
  -- add package configuration options here

@[default_target]
lean_exe «matti-playground» where
  -- supportInterpreter := true
