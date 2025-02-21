theorem Nat.add_pigeon {a b c d : Nat} (h : a + b ≤ c + d) : a ≤ c ∨ b ≤ d :=
  if h' : a ≤ c then
    .inl h'
  else
    have h' : c ≤ a := Nat.le_of_lt (gt_of_not_le h')
    suffices b ≤ d from .inr this
    Nat.le_of_add_le_add_left <|
      calc a + b
        _ ≤ c + d := h
        _ ≤ a + d := Nat.add_le_add_right h' d

namespace List
variable {α}

theorem foldl_append_cons (s : List α) :
    (ss : List (List α)) → (s::ss).foldl .append [] = s ++ ss.foldl .append []
  | [] => s.append_nil.symm
  | s'::ss =>
    let foldl_append : List α → List α := ss.foldl .append
    calc foldl_append (s ++ s')
      _ = s ++ s' ++ foldl_append [] := foldl_append_cons ..
      _ = s ++ (s' ++ foldl_append []) := append_assoc ..
      _ = s ++ foldl_append s' := congrArg _ (foldl_append_cons ..).symm

theorem mem_of_mem_append {a : α} {ys : List α} : {xs : List α} → a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
  | [], h => .inr h
  | _::xs, .head _ => .inl (.head xs)
  | x::_, .tail _ h => (mem_of_mem_append h).elim (.inl ∘ .tail x) .inr

#check replicate
/-- Repeats a string (appends it to itself) some number of times. -/
def napp (s : List α) : Nat → List α
  | 0 => []
  | .succ n => s ++ s.napp n

instance : Pow (List α) Nat where
  pow := napp

theorem napp_add (s : List α) : (m n : Nat) → s ^ (m + n) = s ^ m ++ s ^ n
  | 0, n => show s ^ (0 + n) = s ^ n from congrArg _ n.zero_add
  | .succ m, n =>
    calc s ^ (m.succ + n)
      _ = s ^ (m + n).succ := congrArg _ (m.succ_add n)
      _ = s ++ (s ^ m ++ s ^ n) := congrArg _ (s.napp_add m n)
      _ = s ^ m.succ ++ s ^ n := (append_assoc ..).symm

end List

class Star.{u} (α : Type u) where
  /-- Typically denotes Kleene star. Binds tighter than function application. -/
  star : α → α

@[inherit_doc] postfix:arg "*" => Star.star
macro_rules | `($x *) => ``(unop% Star.star $x)
