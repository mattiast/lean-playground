import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package «matti-playground» where
  -- add package configuration options here
  srcDir := "src"

@[default_target]
lean_lib «Playground» where
  -- add library configuration options here
