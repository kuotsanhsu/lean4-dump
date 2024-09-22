import Batteries.Data.List
import Batteries.Data.RBMap

#check List.Perm
#check List.Nodup
#check List.isSetoid

namespace try1

/-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Basic.html#Multiset -/
def Multiset α := Quotient (List.isSetoid α)

#check List.perm_ext_iff_of_nodup
def Multiset.Nodup {α} : Multiset α → Prop :=
  Quotient.lift List.Nodup fun _ _ => propext ∘ List.Perm.nodup_iff

/-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset -/
structure Finset (α) where
  val : Multiset α
  nodup : val.Nodup

end try1

structure FinSet (α) where
  val : Quotient (List.isSetoid α)
  nodup : val.lift List.Nodup fun _ _ => propext ∘ List.Perm.nodup_iff

#check Lean.RBMap
#check Batteries.RBMap
#check Batteries.RBSet
