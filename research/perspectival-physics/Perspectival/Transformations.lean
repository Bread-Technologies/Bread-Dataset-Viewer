/-
Perspectival Physics — Transformations
======================================

Perspectival transformations: maps W → W that commute with complementation.
Axiom IV says particulars are stable patterns; "stable" requires a notion
of how things change. Group-theoretic transformations on Wantables are the
natural carrier (Axiom IV explicitly mentions group structure).

Calibrated status:
  ✓ This file: transformation type, identity, composition, group laws.
  ✓ The category of Wantable preserved by complement-respecting maps.
  ✗ NOT here: Lie / topological structure (needs Mathlib), Wigner
    classification, gauge group derivation.
-/

import Perspectival.Ontology

namespace Perspectival

/-! ## Perspectival transformations

A perspectival transformation of a Wantable W is a self-bijection of W
that commutes with complementation. The commutation requirement
encodes Axiom II's relational character: a transformation that
mangled the complement structure would not be a transformation of the
*relational* structure of wanting; it would be vandalism.
-/

structure PTrans (W : Type u) [Wantable W] where
  toFun : W → W
  invFun : W → W
  left_inv : ∀ w, invFun (toFun w) = w
  right_inv : ∀ w, toFun (invFun w) = w
  resp_complement : ∀ w, toFun (Wantable.complement w) = Wantable.complement (toFun w)

namespace PTrans

variable {W : Type u} [Wantable W]

instance : CoeFun (PTrans W) (fun _ => W → W) := ⟨PTrans.toFun⟩

/-- Two PTrans agreeing pointwise on `toFun` also agree on `invFun`. Proof:
    `invFun` is the unique two-sided inverse, so it's determined by `toFun`. -/
theorem invFun_unique (f g : PTrans W) (h : ∀ w, f.toFun w = g.toFun w) :
    ∀ w, f.invFun w = g.invFun w := by
  intro w
  have hgw : g.toFun (g.invFun w) = w := g.right_inv w
  have hfw : f.toFun (f.invFun w) = w := f.right_inv w
  have : f.toFun (g.invFun w) = w := by rw [h]; exact hgw
  have : f.invFun (f.toFun (g.invFun w)) = f.invFun w := by rw [this]
  rw [f.left_inv] at this
  exact this.symm

theorem ext {f g : PTrans W} (h : ∀ w, f.toFun w = g.toFun w) : f = g := by
  cases f; cases g
  congr 1
  · funext w; exact h w
  · funext w
    exact invFun_unique ⟨_, _, ‹_›, ‹_›, ‹_›⟩ ⟨_, _, ‹_›, ‹_›, ‹_›⟩ h w

/-- The identity transformation. -/
def id : PTrans W where
  toFun := fun w => w
  invFun := fun w => w
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  resp_complement := fun _ => rfl

/-- Composition of transformations. -/
def comp (g f : PTrans W) : PTrans W where
  toFun := fun w => g.toFun (f.toFun w)
  invFun := fun w => f.invFun (g.invFun w)
  left_inv := by
    intro w
    show f.invFun (g.invFun (g.toFun (f.toFun w))) = w
    rw [g.left_inv, f.left_inv]
  right_inv := by
    intro w
    show g.toFun (f.toFun (f.invFun (g.invFun w))) = w
    rw [f.right_inv, g.right_inv]
  resp_complement := by
    intro w
    show g.toFun (f.toFun (Wantable.complement w))
       = Wantable.complement (g.toFun (f.toFun w))
    rw [f.resp_complement, g.resp_complement]

instance : Mul (PTrans W) := ⟨comp⟩

theorem id_comp (f : PTrans W) : comp id f = f := by
  cases f; rfl

theorem comp_id (f : PTrans W) : comp f id = f := by
  cases f; rfl

theorem comp_assoc (h g f : PTrans W) :
    comp (comp h g) f = comp h (comp g f) := by
  rfl

/-! ## Action on meetings

A perspectival transformation acts on meetings by transforming each side.
The resp_complement law ensures the result is still a meeting.
-/

def actMeeting (f : PTrans W) (m : Meeting W) : Meeting W where
  side₁ := f.toFun m.side₁
  side₂ := f.toFun m.side₂
  complementary := by
    have h := m.complementary
    calc Wantable.complement (f.toFun m.side₁)
        = f.toFun (Wantable.complement m.side₁) := (f.resp_complement _).symm
      _ = f.toFun m.side₂ := by rw [h]

@[simp] theorem actMeeting_id (m : Meeting W) :
    actMeeting (id : PTrans W) m = m := by
  cases m; rfl

theorem actMeeting_comp (g f : PTrans W) (m : Meeting W) :
    actMeeting (comp g f) m = actMeeting g (actMeeting f m) := rfl

end PTrans

end Perspectival
