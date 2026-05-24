/-
Perspectival Physics — Distinguishability lemmas
=================================================

Structural lemmas connecting *operational* notions (distinguishability
via effects) to *linear-algebraic* notions (linear independence) in a
GPT.

  ✓ `distinguishable_imp_linear_independent` — if two states are
    distinguishable then they are linearly independent.

This is a small but real bridge: it shows that distinguishability —
defined by Hardy in operational terms — has a linear-algebraic
shadow that the framework can verify cleanly.
-/

import Perspectival.GPT
import Perspectival.Hardy
import Perspectival.NoCloning
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace Perspectival
namespace Distinguish

open TensorProduct

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- If two states are perfectly distinguishable (some effect gives 1 on
one, 0 on the other), they cannot be equal. -/
theorem distinguishable_ne {G : GPT V} {ρ₁ ρ₂ : V}
    (h : Hardy.Distinguishable G ρ₁ ρ₂) : ρ₁ ≠ ρ₂ := by
  obtain ⟨e, _, hone, hzero⟩ := h
  intro heq
  rw [heq] at hone
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- A state cannot be the zero vector: the unit functional gives 1 on
states, but is zero on zero. -/
theorem state_ne_zero {G : GPT V} {ρ : V} (h : ρ ∈ G.states) : ρ ≠ 0 := by
  intro heq
  have hunit_zero : G.unit ρ = 0 := by rw [heq]; exact map_zero _
  have hunit_one : G.unit ρ = 1 := G.states_normalized ρ h
  rw [hunit_zero] at hunit_one
  exact one_ne_zero hunit_one.symm

/-- **Distinguishable states are linearly independent.**

The proof is structural: a linear-dependence relation on the pair
implies one state is a scalar multiple of the other; the unit
functional then forces the scalar to be 1, contradicting
distinguishability. -/
theorem distinguishable_imp_linear_independent
    {G : GPT V} {ρ₁ ρ₂ : V}
    (h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
    (hd : Hardy.Distinguishable G ρ₁ ρ₂) :
    LinearIndependent ℝ ![ρ₁, ρ₂] := by
  obtain ⟨e, _, he₁, he₂⟩ := hd
  -- We prove LinearIndependent by showing the only zero linear
  -- combination is the trivial one.
  rw [LinearIndependent.pair_iff]
  intro a b hcomb
  -- hcomb : a • ρ₁ + b • ρ₂ = 0
  -- Apply e: a * e ρ₁ + b * e ρ₂ = 0, i.e. a * 1 + b * 0 = 0, so a = 0.
  have happly_e : e (a • ρ₁ + b • ρ₂) = 0 := by
    rw [hcomb]; exact map_zero _
  rw [map_add, map_smul, map_smul, he₁, he₂, smul_eq_mul, smul_eq_mul,
      mul_one, mul_zero, add_zero] at happly_e
  -- happly_e : a = 0
  refine ⟨happly_e, ?_⟩
  -- With a = 0, hcomb becomes b • ρ₂ = 0. Apply unit functional.
  have hcomb' : b • ρ₂ = 0 := by
    have := hcomb
    rw [happly_e, zero_smul, zero_add] at this
    exact this
  have hunit : G.unit (b • ρ₂) = 0 := by rw [hcomb']; exact map_zero _
  rw [map_smul, smul_eq_mul, G.states_normalized ρ₂ h₂, mul_one] at hunit
  exact hunit

/-- The outer product of two linear functionals as a bilinear form
`V → V → ℝ`, packaged as `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`. -/
def outerForm (e u : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => e x * u y
      map_add' := fun y₁ y₂ => by simp [mul_add, map_add]
      map_smul' := fun c y => by simp [mul_left_comm, map_smul] }
  map_add' x₁ x₂ := by
    ext y
    show e (x₁ + x₂) * u y = e x₁ * u y + e x₂ * u y
    simp [map_add, add_mul]
  map_smul' c x := by
    ext y
    show e (c • x) * u y = c * (e x * u y)
    simp [map_smul, mul_assoc]

@[simp] theorem outerForm_apply (e u : V →ₗ[ℝ] ℝ) (x y : V) :
    outerForm e u x y = e x * u y := rfl

/-- **No-cloning from distinguishability.**

If a linear cloner exists on a set `S` containing two states `ρ₁, ρ₂`
(and their sum) that are *operationally distinguishable* by some
effect of the GPT, then contradiction.

The bridge is via the outer form `B(x, y) = e(x) · unit(y)`. For
distinguishable states with `e ρ₁ = 1, e ρ₂ = 0` and normalized states
(`unit ρᵢ = 1`):

    B(ρ₁, ρ₂) + B(ρ₂, ρ₁) = 1·1 + 0·1 = 1 ≠ 0,

which contradicts `cross_terms_vanish`. -/
theorem no_cloning_of_distinguishable {G : GPT V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    {S : Set V} (hC : IsLinearCloner S C)
    {ρ₁ ρ₂ : V} (h₁ : ρ₁ ∈ S) (h₂ : ρ₂ ∈ S) (h_sum : ρ₁ + ρ₂ ∈ S)
    (hst₁ : ρ₁ ∈ G.states) (hst₂ : ρ₂ ∈ G.states)
    (hd : Hardy.Distinguishable G ρ₁ ρ₂) : False := by
  obtain ⟨e, _, he₁, he₂⟩ := hd
  apply no_cloning hC h₁ h₂ h_sum (B := outerForm e G.unit)
  simp only [outerForm_apply]
  rw [he₁, he₂, G.states_normalized ρ₁ hst₁, G.states_normalized ρ₂ hst₂]
  norm_num

end Distinguish
end Perspectival
