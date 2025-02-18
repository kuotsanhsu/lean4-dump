import Lake
open Lake DSL

package "lean4-dump" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  , ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib Graph where
lean_lib RV32I
lean_lib Unicode
lean_lib Complexity

require "leanprover-community" / "mathlib" @ git "v4.16.0"
