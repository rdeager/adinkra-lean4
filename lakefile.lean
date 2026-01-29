import Lake
open Lake DSL

package adinkra where
  -- Adinkra formalization for Mathlib
  -- A Lean4/mathlib formalization of Adinkras—decorated bipartite graphs from supersymmetry theory.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "7cccd8a4ca2caff3505b0419559f646e1824769f"

@[default_target]
lean_lib Adinkra where
  globs := #[.submodules `Adinkra]
