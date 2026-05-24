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

end Perspectival
