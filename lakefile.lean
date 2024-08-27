import Lake
open Lake DSL

package "lean4-dump" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  , ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "batteries" @ git "main"
