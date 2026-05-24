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
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Basic

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

/-- Inverse of a perspectival transformation. -/
def inv (f : PTrans W) : PTrans W where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  resp_complement := by
    intro w
    -- f.resp_complement : ∀ w, f (complement w) = complement (f w)
    -- Apply invFun to both sides: invFun (f (complement w)) = invFun (complement (f w))
    -- LHS = complement w (by left_inv). RHS = ?. We need invFun (complement (f w)) = complement (invFun (f w)).
    -- Let u := invFun w. Then complement w = complement (f u) [since w = f u] = f (complement u).
    -- So invFun (complement w) = invFun (f (complement u)) = complement u = complement (invFun w).
    let u := f.invFun w
    have hw : f.toFun u = w := f.right_inv w
    have h1 : f.toFun (Wantable.complement u) = Wantable.complement (f.toFun u) :=
      f.resp_complement u
    -- Apply invFun: complement u = invFun (complement w).
    have h2 : f.invFun (f.toFun (Wantable.complement u)) =
              f.invFun (Wantable.complement (f.toFun u)) := by rw [h1]
    rw [f.left_inv] at h2
    -- h2 : complement u = invFun (complement (f u))
    -- f u = w
    rw [hw] at h2
    -- h2 : complement u = invFun (complement w)
    -- Goal: invFun (complement w) = complement (invFun w) = complement u
    exact h2.symm

instance : Group (PTrans W) where
  mul := comp
  one := id
  inv := inv
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  inv_mul_cancel f := by
    -- inv f * f = id, i.e. comp (inv f) f = id
    show comp (inv f) f = id
    -- comp (inv f) f has toFun (inv f).toFun ∘ f.toFun = f.invFun ∘ f.toFun = id
    apply PTrans.ext
    intro w
    show (inv f).toFun (f.toFun w) = w
    exact f.left_inv w

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

/-- The natural action of `PTrans W` on `Meeting W` (via `actMeeting`)
is a Mathlib `MulAction`. -/
instance : MulAction (PTrans W) (Meeting W) where
  smul := actMeeting
  one_smul := actMeeting_id
  mul_smul := actMeeting_comp

/-- `PTrans W` is inhabited by the identity. -/
instance : Inhabited (PTrans W) := ⟨1⟩

/-- The complement function on a Wantable, packaged as a perspectival
transformation. Available for any Wantable, not just finite ones. -/
def complement : PTrans W where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive
  resp_complement := fun _ => rfl

/-- The complement PTrans is an involution. -/
@[simp] theorem complement_sq : (complement : PTrans W) * complement = 1 := by
  apply PTrans.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

theorem complement_inv : (complement : PTrans W)⁻¹ = complement :=
  inv_eq_of_mul_eq_one_right complement_sq

/-- The complement PTrans, acting on a meeting, exchanges its two sides.
That is, `actMeeting complement = Meeting.swap`. This is the key
identification between the PTrans-level complement and the
meeting-level swap. -/
@[simp] theorem actMeeting_complement (m : Meeting W) :
    actMeeting (complement : PTrans W) m = m.swap := by
  apply Meeting.ext_of_side₁
  show Wantable.complement m.side₁ = m.side₂
  exact m.complementary

/-- Acting by `complement` twice is the identity action. -/
theorem actMeeting_complement_sq (m : Meeting W) :
    actMeeting (complement : PTrans W) (actMeeting complement m) = m := by
  rw [actMeeting_complement, actMeeting_complement, Meeting.swap_swap]

/-- The action of `PTrans W` on `Meeting W` is faithful: if two
transformations act identically on every meeting, they are equal. -/
theorem actMeeting_faithful (f g : PTrans W)
    (h : ∀ m : Meeting W, actMeeting f m = actMeeting g m) : f = g := by
  apply PTrans.ext
  intro w
  have hm := h (Meeting.mk_fromSide W w)
  have : (actMeeting f (Meeting.mk_fromSide W w)).side₁
       = (actMeeting g (Meeting.mk_fromSide W w)).side₁ := by rw [hm]
  exact this

/-! ## The forgetful bridge: PTrans → Equiv.Perm

A perspectival transformation forgets its `resp_complement` law and
becomes a plain self-bijection of `W` — an `Equiv.Perm W`. This is
a `MonoidHom` (because PTrans's composition matches Mathlib's
permutation multiplication) and it is injective. -/

/-- The underlying self-bijection of a perspectival transformation. -/
def toEquivPerm (φ : PTrans W) : Equiv.Perm W where
  toFun := φ.toFun
  invFun := φ.invFun
  left_inv := φ.left_inv
  right_inv := φ.right_inv

@[simp] theorem toEquivPerm_apply (φ : PTrans W) (w : W) :
    toEquivPerm φ w = φ.toFun w := rfl

@[simp] theorem toEquivPerm_symm_apply (φ : PTrans W) (w : W) :
    (toEquivPerm φ).symm w = φ.invFun w := rfl

@[simp] theorem toEquivPerm_one : toEquivPerm (1 : PTrans W) = 1 := rfl

theorem toEquivPerm_mul (g f : PTrans W) :
    toEquivPerm (g * f) = toEquivPerm g * toEquivPerm f := rfl

/-- The forgetful bridge as a `MonoidHom` from `PTrans W` to the
permutation group on `W`. -/
def toEquivPermHom : PTrans W →* Equiv.Perm W where
  toFun := toEquivPerm
  map_one' := toEquivPerm_one
  map_mul' := toEquivPerm_mul

@[simp] theorem toEquivPermHom_apply (φ : PTrans W) :
    toEquivPermHom φ = toEquivPerm φ := rfl

/-- The forgetful bridge is injective: a perspectival transformation
is determined by its underlying permutation (the `resp_complement`
law is propositional). -/
theorem toEquivPermHom_injective :
    Function.Injective (toEquivPermHom : PTrans W →* Equiv.Perm W) := by
  intro f g h
  apply PTrans.ext
  intro w
  have hh : toEquivPerm f = toEquivPerm g := h
  have : (toEquivPerm f) w = (toEquivPerm g) w := by rw [hh]
  exact this

/-- Image-characterizing fact: the underlying permutation of any
PTrans commutes with the complement permutation. (PTrans embeds into
the centralizer of `complement` inside `Equiv.Perm W`.) -/
theorem toEquivPerm_commutes_complement (φ : PTrans W) :
    toEquivPerm φ * toEquivPerm (complement : PTrans W)
    = toEquivPerm (complement : PTrans W) * toEquivPerm φ := by
  apply Equiv.ext
  intro w
  show φ.toFun (Wantable.complement w) = Wantable.complement (φ.toFun w)
  exact φ.resp_complement w

end PTrans

end Perspectival
