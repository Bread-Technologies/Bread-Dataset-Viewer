/-
Perspectival Physics — No-Cloning Theorem (linear-algebra form)
================================================================

If `C : V →ₗ[ℝ] V ⊗ V` satisfies `C v = v ⊗ v` on a set `S` that is
closed under sums and contains two linearly independent vectors,
contradiction. Equivalently: any *set on which a linear cloner exists*
lies in a one-dimensional subspace.

Framework reading: a "want" cannot be duplicated into two isolated
copies, because wanting is intrinsically two-sided (Axiom II).
Linearity is the structural shadow of this two-sidedness.

Calibrated status:
  ✓ The cross-term identity `v₁ ⊗ v₂ + v₂ ⊗ v₁ = 0` is formally proven
    from linearity (lemma `cross_terms_vanish`).
  ▲ Concluding `False` from this identity plus linear independence
    requires a small fact: `v₁ ⊗ v₂` and `v₂ ⊗ v₁` are linearly
    independent when `v₁, v₂` are. This is true but the Mathlib lemma
    of the right shape isn't immediately at hand — see `sorry` mark.
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace Perspectival

open TensorProduct

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A linear cloner on a set `S` is a linear map `V →ₗ[ℝ] V ⊗ V`
that sends every `v ∈ S` to `v ⊗ v`. -/
def IsLinearCloner (S : Set V) (C : V →ₗ[ℝ] V ⊗[ℝ] V) : Prop :=
  ∀ v ∈ S, C v = v ⊗ₜ[ℝ] v

/-- From linearity of the cloner, the cross-terms in the expansion of
`(v₁+v₂) ⊗ (v₁+v₂)` must cancel. This is the structural heart of the
no-cloning theorem. -/
theorem cross_terms_vanish {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S) :
    v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁ = 0 := by
  -- Two ways to compute C (v₁ + v₂); equate and cancel duplicates.
  have hlin : C (v₁ + v₂) = v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂ := by
    rw [map_add, hC v₁ h₁, hC v₂ h₂]
  have hclone : C (v₁ + v₂) = (v₁ + v₂) ⊗ₜ[ℝ] (v₁ + v₂) := hC _ h_sum
  have hexpand : (v₁ + v₂) ⊗ₜ[ℝ] (v₁ + v₂)
      = (v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂) + (v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁) := by
    rw [add_tmul, tmul_add, tmul_add]
    abel
  -- From hlin = hclone via hexpand:
  --   v₁⊗v₁ + v₂⊗v₂ = (v₁⊗v₁ + v₂⊗v₂) + (cross terms)
  have hEq : v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂
           = (v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂) + (v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁) := by
    calc v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂
        = C (v₁ + v₂) := hlin.symm
      _ = (v₁ + v₂) ⊗ₜ[ℝ] (v₁ + v₂) := hclone
      _ = (v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂) + (v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁) := hexpand
  -- a = a + c  ⟹  c = 0 (additive cancellation).
  have hCancel : (v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂) + 0
              = (v₁ ⊗ₜ[ℝ] v₁ + v₂ ⊗ₜ[ℝ] v₂) + (v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁) := by
    rw [add_zero]; exact hEq
  exact (add_left_cancel hCancel).symm

/-- **No-cloning theorem (linear-algebra form, bilinear-form
hypothesis).**

Given a set `S` closed under sums and containing two vectors `v₁, v₂`
that are distinguished by some bilinear form `B` — that is,
`B v₁ v₂ + B v₂ v₁ ≠ 0` — there is no linear cloner on `S`.

This formulation has a cleanly verifiable proof: the cross-terms must
vanish (from `cross_terms_vanish`), so any bilinear form lifts to a
linear functional sending them to zero; if `B v₁ v₂ + B v₂ v₁ ≠ 0`,
contradiction.

Linear independence of `v₁, v₂` *implies* the existence of such a `B`
(via the dual basis), but we take the bilinear form as the input
rather than extracting it from linear independence — keeping the proof
self-contained at this level. -/
theorem no_cloning {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S)
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hB : B v₁ v₂ + B v₂ v₁ ≠ 0) : False := by
  have hcross : v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁ = 0 :=
    cross_terms_vanish hC h₁ h₂ h_sum
  have hlift : (TensorProduct.lift B) (v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁) = 0 := by
    rw [hcross]; exact map_zero _
  rw [map_add, TensorProduct.lift.tmul, TensorProduct.lift.tmul] at hlift
  exact hB hlift

end Perspectival
