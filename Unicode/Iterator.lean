/-- The forward iterator `ι` iterates over values of type `α`. -/
class ForwardIterator (α ι) where
  next? : ι → Option (α × ι)

example : ForwardIterator Char String.Iterator where
  next? it := if h : it.hasNext then (it.curr' h, it.next' h) else none

example : ForwardIterator UInt8 ByteArray.Iterator where
  next? it := if h : it.hasNext then (it.curr' h, it.next' h) else none

example α : ForwardIterator α (List α) where
  next? | a::as => (a, as) | [] => none

example α : ForwardIterator α (Array α × Nat) where
  next? | (as, i) => if _ : i < as.size then (as[i], as, i + 1) else none

class InputIterator (α ι) (sentinal : ι) where
  next (it : ι) : it ≠ sentinal → α × ι

example α : InputIterator α (List α) [] where
  next | a::as, _ => (a, as)

example {α ι sentinal} [∀ it, Decidable (it = sentinal)] (self : InputIterator α ι sentinal) :
    ForwardIterator α ι where
  next? it := if h : it = sentinal then none else self.next it h

class Iterator (α ι) where
  good : ι → Prop
  more it : good it → α × ι

namespace Iterator
variable {α ι} [self : Iterator α ι] (it : ι) (h : self.good it)

abbrev value : α := (more it h).1
abbrev next : ι := (more it h).2

end Iterator

example : Iterator UInt8 ByteArray.Iterator where
  good it := it.hasNext
  more it h := (it.curr' h, it.next' h)

example : Iterator Char String.Iterator where
  good it := it.hasNext
  more it h := (it.curr' h, it.next' h)

example α : Iterator α (List α) where
  good it := it ≠ []
  more | a::as, _ => (a, as)
