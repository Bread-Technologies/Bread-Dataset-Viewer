/-
Perspectival Physics — Wantable → GPT (partial bridge)
========================================================

The framework's central technical claim is that operational
probabilistic structure (`GPT`) *emerges* from the metaphysical
perspective-wanting structure (`Wantable`). The full bridge is open;
this module provides a *partial* construction.

Given a *finite* Wantable `W`, we construct:
  - `V W := W → ℝ` (functions on outcomes).
  - The "WantableGPT" with states = probability distributions on `W`
    (states are convex; this is just the standard simplex on `W`).
  - The complement involution on `W` induces a linear involution on
    `V W` that *preserves* the state space.

This is a real connection: the complement structure on `W` *acts* on
the GPT's state space. It does NOT yet show the GPT structure *emerges*
from `W` alone — the convex/normalized states are imposed, not derived.

Status:
  ✓ The Wantable-complement action on `V W` is a well-defined linear
    involution.
  ✓ It preserves the state space (since complement is a bijection on W).
  ▲ Whether this gives the "right" GPT in a framework-distinctive
    sense is open. The construction is one of many possible bridges.

Honest qualification: this is the *thinnest* possible connection, not
a derivation. It shows the metaphysical level can *act* on the
operational level but does not show one produces the other.
-/

import Perspectival.Ontology
import Perspectival.GPT
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Real.Basic

namespace Perspectival
namespace WantableGPT

variable (W : Type u) [Wantable W] [Fintype W] [DecidableEq W]

/-- The carrier vector space of the Wantable-induced GPT. -/
abbrev V := W → ℝ

/-- The complement action on `V W`: pull back by `Wantable.complement`. -/
def complementAction : V W →ₗ[ℝ] V W where
  toFun f := fun w => f (Wantable.complement w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complement action is an involution. -/
theorem complementAction_involutive (f : V W) :
    complementAction W (complementAction W f) = f := by
  funext w
  show f (Wantable.complement (Wantable.complement w)) = f w
  rw [Wantable.complement_involutive]

/-- The states (probability distributions on `W`). -/
def states : Set (V W) := stdSimplex ℝ W

/-- Complement action sends states to states (it permutes outcome
probabilities). -/
theorem complementAction_preserves_states (f : V W) (hf : f ∈ states W) :
    complementAction W f ∈ states W := by
  refine ⟨?_, ?_⟩
  · intro w
    show 0 ≤ f (Wantable.complement w)
    exact hf.1 _
  · -- ∑ w, f (complement w) = ∑ w, f w = 1
    show ∑ w, f (Wantable.complement w) = 1
    rw [← hf.2]
    -- Reindex via the complement involution
    refine Equiv.sum_comp ⟨Wantable.complement, Wantable.complement,
        Wantable.complement_involutive, Wantable.complement_involutive⟩ f

/-- The Wantable-induced GPT: states are probability distributions on W,
effects are bounded inner-product functionals with the standard basis. -/
def unitFn : V W →ₗ[ℝ] ℝ where
  toFun f := ∑ w, f w
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- Inner-product functional: a coefficient vector `g` defines
`f ↦ ∑ w, g w * f w`. -/
def innerLin (g : V W) : V W →ₗ[ℝ] ℝ where
  toFun f := ∑ w, g w * f w
  map_add' f₁ f₂ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

/-- Coefficient vectors representing valid effects: components in [0,1]. -/
def effectVec : Set (V W) := { g | ∀ w, 0 ≤ g w ∧ g w ≤ 1 }

/-- The effects of the WantableGPT: inner-product functionals with
coefficient vectors in [0,1]^W. -/
def effects : Set (V W →ₗ[ℝ] ℝ) := innerLin W '' effectVec W

/-- The Wantable-induced GPT. (Mirrors `Classical.gpt` but with the
ambient outcome set being a Wantable rather than `Fin n`. The
complement structure acts on the state space via
`complementAction`.) -/
def gpt : Perspectival.GPT (V W) where
  unit := unitFn W
  states := states W
  effects := effects W
  states_convex := convex_stdSimplex ℝ W
  effects_convex := by
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩ a b ha hb hab
    refine ⟨a • g₁ + b • g₂, ?_, ?_⟩
    · intro w
      refine ⟨?_, ?_⟩
      · have := add_nonneg (mul_nonneg ha (hg₁ w).1) (mul_nonneg hb (hg₂ w).1)
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
      · have h1 : a * g₁ w ≤ a * 1 := mul_le_mul_of_nonneg_left (hg₁ w).2 ha
        have h2 : b * g₂ w ≤ b * 1 := mul_le_mul_of_nonneg_left (hg₂ w).2 hb
        have : a * g₁ w + b * g₂ w ≤ a + b := by linarith
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hab] using this.trans hab.le
    · apply LinearMap.ext
      intro f
      show ∑ w, (a • g₁ + b • g₂) w * f w = a * (∑ w, g₁ w * f w) + b * (∑ w, g₂ w * f w)
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
            Finset.mul_sum, mul_assoc]
  states_normalized := fun _ hρ => hρ.2
  prob_in_unit_interval := by
    rintro _ ⟨g, hg, rfl⟩ ρ ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∑ w, g w * ρ w
      exact Finset.sum_nonneg fun w _ => mul_nonneg (hg w).1 (hpos w)
    · show ∑ w, g w * ρ w ≤ 1
      calc ∑ w, g w * ρ w
          ≤ ∑ w, 1 * ρ w := Finset.sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_right (hg w).2 (hpos w)
        _ = ∑ w, ρ w := by simp
        _ = 1 := hsum
  unit_is_effect := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro w; exact ⟨zero_le_one, le_refl _⟩
    · apply LinearMap.ext
      intro f
      show (innerLin W fun _ => 1) f = (unitFn W) f
      show ∑ w, 1 * f w = ∑ w, f w
      simp

/-- The unit functional is preserved by the complement action. -/
theorem unitFn_complementAction (f : V W) :
    unitFn W (complementAction W f) = unitFn W f := by
  show ∑ w, f (Wantable.complement w) = ∑ w, f w
  exact Equiv.sum_comp ⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩ f

/-- The Wantable-complement action is a structure-preserving GPT
transformation: a Transform from `gpt W` to itself. -/
def complementTransform : Perspectival.GPT.Transform (gpt W) (gpt W) where
  toLin := complementAction W
  preserves_states := complementAction_preserves_states W
  preserves_unit := by
    apply LinearMap.ext
    intro f
    show unitFn W (complementAction W f) = unitFn W f
    exact unitFn_complementAction W f

end WantableGPT
end Perspectival
