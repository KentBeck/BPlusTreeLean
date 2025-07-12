import Lake
open Lake DSL

package «BPlusTreeLean» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

@[default_target]
lean_lib «BPlusTreeLean» where
  -- add any library configuration options here
