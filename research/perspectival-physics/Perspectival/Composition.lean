/-
Perspectival Physics — Composition
===================================

If reality is the structure of meetings (Axiom III), composition asks:
given two domains of wanting, how does the combined domain behave?

The minimal compositional axiom we impose: complement acts component-wise
on a disjoint union. Cross-component meetings are PROHIBITED at the
level of the Wantable structure — that is, the bare disjoint union has
no cross-side complements. This corresponds to no-signaling at the
classical level: independent systems do not, by themselves, interact.

Calibrated status:
  ✓ Disjoint union Wantable instance
  ✓ No cross-system meetings (proved as a structural fact about the
    disjoint-union complement)
  ✓ Component-wise PTrans on the disjoint union
  ▲ Sequential composition placeholder — sketched only
-/

import Perspectival.Ontology
import Perspectival.Transformations

namespace Perspectival

/-! ## Disjoint union of Wantables

The complement on `W₁ ⊕ W₂` acts component-wise. This is the
"no-interaction" baseline composition. Real interactions require
additional structure (couplings, see future work).
-/

instance instWantableSum (W₁ W₂ : Type u) [Wantable W₁] [Wantable W₂] :
    Wantable (W₁ ⊕ W₂) where
  complement := fun
    | .inl w => .inl (Wantable.complement w)
    | .inr w => .inr (Wantable.complement w)
  complement_involutive := by
    intro w
    cases w with
    | inl w => simp [Wantable.complement_involutive]
    | inr w => simp [Wantable.complement_involutive]

/-- Embed a meeting in `W₁` as a meeting in `W₁ ⊕ W₂` (via the left
injection). -/
def Meeting.sumInl {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting W₁) : Meeting (W₁ ⊕ W₂) where
  side₁ := Sum.inl m.side₁
  side₂ := Sum.inl m.side₂
  complementary := by
    show (Sum.inl (Wantable.complement m.side₁) : W₁ ⊕ W₂)
       = Sum.inl m.side₂
    rw [m.complementary]

/-- Embed a meeting in `W₂` as a meeting in `W₁ ⊕ W₂` (via the right
injection). -/
def Meeting.sumInr {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting W₂) : Meeting (W₁ ⊕ W₂) where
  side₁ := Sum.inr m.side₁
  side₂ := Sum.inr m.side₂
  complementary := by
    show (Sum.inr (Wantable.complement m.side₁) : W₁ ⊕ W₂)
       = Sum.inr m.side₂
    rw [m.complementary]

/-- `sumInl` commutes with swap. -/
@[simp] theorem Meeting.sumInl_swap {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (m : Meeting W₁) :
    (Meeting.sumInl (W₂ := W₂) m).swap = Meeting.sumInl m.swap := by
  cases m
  rfl

/-- `sumInr` commutes with swap. -/
@[simp] theorem Meeting.sumInr_swap {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (m : Meeting W₂) :
    (Meeting.sumInr (W₁ := W₁) m).swap = Meeting.sumInr m.swap := by
  cases m
  rfl

/-- A meeting in the disjoint union never has cross-component sides:
    both sides are in the same summand. This is the structural form of
    no-interaction across independent systems. -/
theorem Meeting.sum_no_cross
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting (W₁ ⊕ W₂)) :
    (∃ a b, m.side₁ = .inl a ∧ m.side₂ = .inl b) ∨
    (∃ a b, m.side₁ = .inr a ∧ m.side₂ = .inr b) := by
  have hc := m.complementary
  rcases hs₁ : m.side₁ with a | a <;> rcases hs₂ : m.side₂ with b | b
  · exact Or.inl ⟨a, b, rfl, rfl⟩
  · -- (.inl a, .inr b): contradiction with complementary
    exfalso
    rw [hs₁, hs₂] at hc
    simp [Wantable.complement] at hc
  · exfalso
    rw [hs₁, hs₂] at hc
    simp [Wantable.complement] at hc
  · exact Or.inr ⟨a, b, rfl, rfl⟩

/-! ## Component-wise PTrans

A pair of transformations on the components yields a transformation on
the disjoint union. -/

/-! ## Product of Wantables

The disjoint-union composition `W₁ ⊕ W₂` forbids cross-system meetings.
The PRODUCT composition `W₁ × W₂` instead PAIRS the two Wantables —
each meeting in the composite involves a meeting in W₁ AND a meeting
in W₂ simultaneously. Different physics: independent sectors vs.
correlated sectors.
-/

instance instWantableProd (W₁ W₂ : Type u) [Wantable W₁] [Wantable W₂] :
    Wantable (W₁ × W₂) where
  complement p := (Wantable.complement p.1, Wantable.complement p.2)
  complement_involutive p := by
    show (Wantable.complement (Wantable.complement p.1),
          Wantable.complement (Wantable.complement p.2)) = p
    rw [Wantable.complement_involutive, Wantable.complement_involutive]

/-- A meeting in the product Wantable projects to a meeting in the
first component. -/
def Meeting.prodFst {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting (W₁ × W₂)) : Meeting W₁ where
  side₁ := m.side₁.1
  side₂ := m.side₂.1
  complementary := by
    have h : Wantable.complement m.side₁ = m.side₂ := m.complementary
    have h1 : (Wantable.complement m.side₁).1 = m.side₂.1 := by rw [h]
    -- (complement m.side₁).1 = complement m.side₁.1 by the instance definition
    exact h1

/-- A meeting in the product Wantable projects to a meeting in the
second component. -/
def Meeting.prodSnd {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting (W₁ × W₂)) : Meeting W₂ where
  side₁ := m.side₁.2
  side₂ := m.side₂.2
  complementary := by
    have h : Wantable.complement m.side₁ = m.side₂ := m.complementary
    have h1 : (Wantable.complement m.side₁).2 = m.side₂.2 := by rw [h]
    exact h1

/-- Inverse direction: a pair of meetings, one in each component,
combines into a meeting in the product Wantable. -/
def Meeting.prodMk {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m₁ : Meeting W₁) (m₂ : Meeting W₂) : Meeting (W₁ × W₂) where
  side₁ := (m₁.side₁, m₂.side₁)
  side₂ := (m₁.side₂, m₂.side₂)
  complementary := by
    show (Wantable.complement m₁.side₁, Wantable.complement m₂.side₁)
       = (m₁.side₂, m₂.side₂)
    rw [m₁.complementary, m₂.complementary]

@[simp] theorem Meeting.prodFst_prodMk {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂]
    (m₁ : Meeting W₁) (m₂ : Meeting W₂) :
    (Meeting.prodMk m₁ m₂).prodFst = m₁ := by
  cases m₁; rfl

@[simp] theorem Meeting.prodSnd_prodMk {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂]
    (m₁ : Meeting W₁) (m₂ : Meeting W₂) :
    (Meeting.prodMk m₁ m₂).prodSnd = m₂ := by
  cases m₂; rfl

/-- Component-wise PTrans on the product Wantable. -/
def PTrans.prodMap {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (f₁ : PTrans W₁) (f₂ : PTrans W₂) : PTrans (W₁ × W₂) where
  toFun p := (f₁.toFun p.1, f₂.toFun p.2)
  invFun p := (f₁.invFun p.1, f₂.invFun p.2)
  left_inv p := by
    show (f₁.invFun (f₁.toFun p.1), f₂.invFun (f₂.toFun p.2)) = p
    rw [f₁.left_inv, f₂.left_inv]
  right_inv p := by
    show (f₁.toFun (f₁.invFun p.1), f₂.toFun (f₂.invFun p.2)) = p
    rw [f₁.right_inv, f₂.right_inv]
  resp_complement p := by
    show (f₁.toFun (Wantable.complement p.1), f₂.toFun (Wantable.complement p.2))
       = (Wantable.complement (f₁.toFun p.1), Wantable.complement (f₂.toFun p.2))
    rw [f₁.resp_complement, f₂.resp_complement]

/-- `prodMap` of identities is the identity. -/
@[simp] theorem PTrans.prodMap_one_one (W₁ W₂ : Type u)
    [Wantable W₁] [Wantable W₂] :
    PTrans.prodMap (1 : PTrans W₁) (1 : PTrans W₂) = 1 := by
  apply PTrans.ext
  intro p
  cases p
  rfl

-- sumMap_one_one moved below the sumMap definition

/-- Swap on a product meeting equals the prodMk of the component swaps. -/
theorem Meeting.prod_swap {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting (W₁ × W₂)) :
    m.swap = Meeting.prodMk m.prodFst.swap m.prodSnd.swap := by
  cases m
  rfl

/-- Project from product Meeting back gives the original (functoriality). -/
@[simp] theorem Meeting.prodMk_prodFst_prodSnd {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (m : Meeting (W₁ × W₂)) :
    Meeting.prodMk m.prodFst m.prodSnd = m := by
  cases m
  rfl

def PTrans.sumMap {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (f₁ : PTrans W₁) (f₂ : PTrans W₂) : PTrans (W₁ ⊕ W₂) where
  toFun := fun
    | .inl w => .inl (f₁.toFun w)
    | .inr w => .inr (f₂.toFun w)
  invFun := fun
    | .inl w => .inl (f₁.invFun w)
    | .inr w => .inr (f₂.invFun w)
  left_inv := by
    intro w; cases w with
    | inl w => simp [f₁.left_inv]
    | inr w => simp [f₂.left_inv]
  right_inv := by
    intro w; cases w with
    | inl w => simp [f₁.right_inv]
    | inr w => simp [f₂.right_inv]
  resp_complement := by
    intro w; cases w with
    | inl w => simp [Wantable.complement, f₁.resp_complement]
    | inr w => simp [Wantable.complement, f₂.resp_complement]

/-- `sumMap` of identities is the identity. -/
@[simp] theorem PTrans.sumMap_one_one (W₁ W₂ : Type u)
    [Wantable W₁] [Wantable W₂] :
    PTrans.sumMap (1 : PTrans W₁) (1 : PTrans W₂) = 1 := by
  apply PTrans.ext
  intro w
  cases w <;> rfl

end Perspectival
