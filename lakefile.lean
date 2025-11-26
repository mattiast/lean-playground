import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package «matti-playground» where
  -- add package configuration options here

@[default_target]
lean_lib «src/imo6» where
  -- add library configuration options here
