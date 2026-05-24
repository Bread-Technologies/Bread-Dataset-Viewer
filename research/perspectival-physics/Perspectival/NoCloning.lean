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
import Mathlib.LinearAlgebra.Basis.VectorSpace
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

/-- **No-cloning theorem from linear independence.**

If `v₁` and `v₂` are linearly independent (over `ℝ`), then no linear
cloner can be defined on any sum-closed set `S` containing them and
their sum.

This is the conceptually clean statement: linear independence of the
two vectors is the only assumption — we extract dual functionals `f, g`
from linear independence and apply the bilinear form `B(x, y) := f x * g y`
to `no_cloning`. -/
theorem no_cloning_of_linear_independent
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S)
    (hLI : LinearIndependent ℝ ![v₁, v₂]) : False := by
  -- The linear combination map `T : (Fin 2 → ℝ) →ₗ[ℝ] V`
  -- `T c = c 0 • v₁ + c 1 • v₂` is injective by linear independence.
  set T : (Fin 2 → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ ![v₁, v₂] with hT_def
  have hT_inj : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hLI.fintypeLinearCombination_injective
  -- Extract a left inverse `g : V →ₗ[ℝ] (Fin 2 → ℝ)`.
  obtain ⟨g, hg⟩ := T.exists_leftInverse_of_injective hT_inj
  -- Evaluations of `g` at `v₁` and `v₂`.
  have hT1 : T (Pi.single 0 1) = v₁ := by
    rw [hT_def, Fintype.linearCombination_apply_single]; simp
  have hT2 : T (Pi.single 1 1) = v₂ := by
    rw [hT_def, Fintype.linearCombination_apply_single]; simp
  have hgv1 : g v₁ = Pi.single (0 : Fin 2) (1 : ℝ) := by
    have := LinearMap.congr_fun hg (Pi.single 0 1)
    simpa [hT1] using this
  have hgv2 : g v₂ = Pi.single (1 : Fin 2) (1 : ℝ) := by
    have := LinearMap.congr_fun hg (Pi.single 1 1)
    simpa [hT2] using this
  -- Dual functionals `f x := (g x) 0` and `h x := (g x) 1`.
  let f : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (g x) 0
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun r x => by rw [map_smul]; rfl }
  let h : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (g x) 1
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun r x => by rw [map_smul]; rfl }
  -- Bilinear form `B(x, y) := f x * h y`, built as `B x := (f x) • h`.
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (f x) • h
      map_add' := fun x y => by rw [map_add, add_smul]
      map_smul' := fun r x => by
        show (f (r • x)) • h = r • (f x) • h
        rw [map_smul, smul_assoc] }
  -- Compute B v₁ v₂ = 1 and B v₂ v₁ = 0.
  have hf1 : f v₁ = 1 := by
    show (g v₁) 0 = 1
    rw [hgv1, Pi.single_eq_same]
  have hf2 : f v₂ = 0 := by
    show (g v₂) 0 = 0
    rw [hgv2, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  have hh1 : h v₁ = 0 := by
    show (g v₁) 1 = 0
    rw [hgv1, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  have hh2 : h v₂ = 1 := by
    show (g v₂) 1 = 1
    rw [hgv2, Pi.single_eq_same]
  have hB12 : B v₁ v₂ = 1 := by
    show (f v₁) • h v₂ = 1
    rw [hf1, hh2, one_smul]
  have hB21 : B v₂ v₁ = 0 := by
    show (f v₂) • h v₁ = 0
    rw [hf2, zero_smul]
  -- Apply the bilinear-form version of no-cloning.
  refine no_cloning hC h₁ h₂ h_sum (B := B) ?_
  rw [hB12, hB21]; norm_num

end Perspectival
