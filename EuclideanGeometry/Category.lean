structure Cat.{u, v} where
  Obj : Sort u
  Hom (α β : Obj) : Sort v
  /-- **Composition** `g ∘ f` -/
  comp {α β γ} (g : Hom β γ) (f : Hom α β) : Hom α γ
  /-- `(h ∘ g) ∘ f = h ∘ (g ∘ f)` -/
  comp_assoc {α β γ δ} {h : Hom γ δ} {g : Hom β γ} {f : Hom α β} :
      comp (comp h g) f = comp h (comp g f)
  id α : Hom α α
  id_comp {α β} {f : Hom α β} : comp (id β) f = f
  comp_id {α β} {f : Hom α β} : comp f (id α) = f

namespace Cat

def Prod (A B : Cat) : Cat where
  Obj := A.Obj × B.Obj
  Hom α β := A.Hom α.1 β.1 × B.Hom α.2 β.2
  comp g f := ⟨A.comp g.1 f.1, B.comp g.2 f.2⟩
  comp_assoc := Prod.ext A.comp_assoc B.comp_assoc
  id α := ⟨A.id α.1, B.id α.2⟩
  id_comp := Prod.ext A.id_comp B.id_comp
  comp_id := Prod.ext A.comp_id B.comp_id

/-- The category of sets -/
def Set : Cat where
  Obj := Sort _
  Hom α β := α → β
  comp g f := g ∘ f
  comp_assoc := rfl
  id := @_root_.id
  id_comp := rfl
  comp_id := rfl

structure Functor (A B : Cat) where
  objFun : A.Obj → B.Obj
  homFun {α β} : A.Hom α β → B.Hom (objFun α) (objFun β)
  homFun_id {α} : homFun (A.id α) = B.id (objFun α)
  homFun_comp {α β γ} {g : A.Hom β γ} {f : A.Hom α β} :
      homFun (A.comp g f) = B.comp (homFun g) (homFun f)

-- instance : CoeFun (Functor A B) (fun _ => A.Obj → B.Obj) where
--   coe F := F.objFun

-- instance : CoeFun (Functor A B) (fun F => ∀ {α β}, A.Hom α β → B.Hom (F α) (F β)) where
--   coe F := F.homFun

/-- Natural transformation
* [The determinant of a matrix](https://ncatlab.org/nlab/show/determinant#determinant_of_a_matrix)
-/
@[ext] structure Nat {A B} (F G : Functor A B) where
  /-- **Component** -/
  comp α : B.Hom (F.objFun α) (G.objFun α)
  /-- **Naturality** -/
  nat {α β} {f : A.Hom α β} : B.comp (comp β) (F.homFun f) = B.comp (G.homFun f) (comp α)

/-- [Functor category](https://en.wikipedia.org/wiki/Natural_transformation#Functor_categories) -/
def Funct (A B : Cat) : Cat where
  Obj := Functor A B
  Hom := Nat
  /- [Vertical composition](https://en.wikipedia.org/wiki/Natural_transformation#Vertical_composition) -/
  comp {F G H} η ε := {
    comp α := B.comp (η.comp α) (ε.comp α)
    nat {α β f} := by rw [B.comp_assoc, ε.nat, ←B.comp_assoc, η.nat, B.comp_assoc]
      /-
      calc B.comp (B.comp (η.comp β) (ε.comp β)) (F.homFun f)
        _ = B.comp (η.comp β) (B.comp (ε.comp β) (F.homFun f)) := B.comp_assoc
        _ = B.comp (η.comp β) (B.comp (G.homFun f) (ε.comp α)) := congrArg _ ε.nat
        _ = B.comp (B.comp (η.comp β) (G.homFun f)) (ε.comp α) := B.comp_assoc.symm
        _ = B.comp (B.comp (H.homFun f) (η.comp α)) (ε.comp α) := congrArg (B.comp · _) η.nat
        _ = B.comp (H.homFun f) (B.comp (η.comp α) (ε.comp α)) := B.comp_assoc
      -/
  }
  comp_assoc := Nat.ext (funext fun _ => B.comp_assoc)
  id F := {comp α := B.id (F.objFun α), nat := B.id_comp.trans B.comp_id.symm}
  id_comp := Nat.ext (funext fun _ => B.id_comp)
  comp_id := Nat.ext (funext fun _ => B.comp_id)

/-- [Hom-functor](https://en.wikipedia.org/wiki/Hom_functor#Formal_definition) `Hom(A,-)` -/
def HomFunctor {A} (α : A.Obj) : Functor A Set where
  objFun := A.Hom α
  homFun := A.comp
  homFun_id := funext fun _ => A.id_comp
  homFun_comp := funext fun _ => A.comp_assoc

/-- Every morphism `f : α → β` gives rise to a natural transformation
`Hom(f,-) : Hom(α,-) → Hom(β,-)`.
-/
def HomNat {A : Cat} {α β} (f : A.Hom α β) : Nat (HomFunctor β) (HomFunctor α) where
  comp _ g := A.comp g f
  nat := funext fun _ => A.comp_assoc

/-- [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma#Formal_statement) -/
def Yoneda {A : Cat} (F : Functor A Set) {α : A.Obj} (β : F.objFun α) : Nat (HomFunctor α) F where
  comp _ f := F.homFun f β
  nat := funext fun _ => congrFun F.homFun_comp β

end Cat
