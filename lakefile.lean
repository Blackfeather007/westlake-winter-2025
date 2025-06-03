import Lake
open Lake DSL

package «westlake-winter-2025» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.14.0"

@[default_target]
lean_lib «WestlakeWinter2025» where
  -- add any library configuration options here
