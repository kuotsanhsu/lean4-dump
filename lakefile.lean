import Lake
open Lake DSL

package "lean4-dump" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  , ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib Graph where
lean_lib RV32I

require "leanprover-community" / "mathlib" @ git "v4.16.0-rc2"
