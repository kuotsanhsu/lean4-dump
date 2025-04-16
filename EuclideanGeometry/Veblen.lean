class Between (α) where
  between : α → α → α → Prop

namespace Between
variable {α} [Between α]

notation:40 a "#" b:50 "#" c:40 => Between.between a b c

def Collinear (a b c : α) : Prop := a#b#c ∨ b#c#a ∨ c#a#b
def Triangular (a b c : α) : Prop := ¬Collinear a b c

end Between

open Between in
class Geometry (α) extends Between α where
  axiom1 : ∃ a b : α, a ≠ b
  axiom2 {a b c : α} : a#b#c → c#b#a
  axiom3 {a b c : α} : a#b#c → ¬a#c#b
  axiom4 {a b c : α} : a#b#c → a ≠ c
  axiom5 {a b : α} : a ≠ b → ∃ c, a#b#c
  axiom6 {a b c d : α} : a ≠ b → c ≠ d → Collinear a b c → Collinear a b d → Collinear c d a
  axiom7 : ∃ a b c : α, Triangular a b c
  axiom8 {a b c d e : α} : Triangular a b c → a#b#d → b#e#c → ∃ f, c#f#a ∧ d#e#f
