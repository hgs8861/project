import Lake
open Lake DSL

package «RepresentaionTheory» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RepThe» where
  srcDir := "."    -- ← "RepThe" → "." 으로 변경
