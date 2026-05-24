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
import Mathlib.LinearAlgebra.Dimension.Finite

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

/-- **Linearly dependent states are equal.**

In a GPT, if `ρ₁, ρ₂` are both states and the pair is linearly
dependent, then `ρ₁ = ρ₂`. (Equivalently: distinct states are
linearly independent.)

Proof: linear dependence means some nontrivial relation
`a • ρ₁ + b • ρ₂ = 0`. Applying the unit functional gives
`a + b = 0`. If `a ≠ 0`, then `ρ₂ = -(b/a) ρ₁ = ρ₁` (since b = -a).
If `a = 0`, then `b ≠ 0` and `b • ρ₂ = 0` forces `ρ₂ = 0`, contradicting
`state_ne_zero`. -/
theorem linear_dependent_states_eq
    {G : GPT V} {ρ₁ ρ₂ : V}
    (h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
    (hdep : ¬ LinearIndependent ℝ ![ρ₁, ρ₂]) :
    ρ₁ = ρ₂ := by
  -- Negation of `LinearIndependent.pair_iff`: some (a, b) ≠ (0, 0) with
  -- a • ρ₁ + b • ρ₂ = 0.
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨a, b, hcomb, hne⟩ := hdep
  -- Apply unit: a * 1 + b * 1 = 0, i.e. a + b = 0.
  have hunit : G.unit (a • ρ₁ + b • ρ₂) = 0 := by rw [hcomb]; exact map_zero _
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      G.states_normalized ρ₁ h₁, G.states_normalized ρ₂ h₂, mul_one, mul_one] at hunit
  -- hunit : a + b = 0, so b = -a
  have hb : b = -a := by linarith
  -- Now a • ρ₁ + (-a) • ρ₂ = 0, i.e. a • (ρ₁ - ρ₂) = 0.
  have hcombrw : a • ρ₁ + b • ρ₂ = a • (ρ₁ - ρ₂) := by
    rw [hb, smul_sub, neg_smul]; abel
  rw [hcombrw] at hcomb
  -- hcomb : a • (ρ₁ - ρ₂) = 0
  by_cases ha : a = 0
  · -- a = 0, hb gives b = 0, contradicting hne.
    exfalso
    apply hne ha
    rw [hb, ha, neg_zero]
  · -- a ≠ 0, so ρ₁ - ρ₂ = 0, hence ρ₁ = ρ₂.
    have hzero : ρ₁ - ρ₂ = 0 := by
      rcases smul_eq_zero.mp hcomb with h | h
      · exact absurd h ha
      · exact h
    exact sub_eq_zero.mp hzero

/-- **Distinguishable states are linearly independent.**

The proof is structural: a linear-dependence relation on the pair
implies one state is a scalar multiple of the other; the unit
functional then forces the scalar to be 1, contradicting
distinguishability. -/
theorem distinguishable_imp_linear_independent
    {G : GPT V} {ρ₁ ρ₂ : V}
    (_h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
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

/-! ## Perfect distinguishability (Hardy-style)

A family of states is *perfectly distinguishable* if there is a
single measurement — i.e., a family of effects summing to the unit —
that picks each state out with certainty. -/

/-- A perfect-distinguishability witness for a family `ρ : ι → V`:
effects `e : ι → V →ₗ[ℝ] ℝ` with `e i (ρ j) = δᵢⱼ`. -/
structure PerfectWitness {G : GPT V} {ι : Type*} [DecidableEq ι] (ρ : ι → V) where
  e : ι → V →ₗ[ℝ] ℝ
  kronecker : ∀ i j, e i (ρ j) = if i = j then 1 else 0

/-- **N perfectly distinguishable states are linearly independent.**

Given a finite family `ρ : Fin n → V` of states with a perfect-
distinguishability witness, `ρ` is linearly independent.

Proof: from `∑ aⱼ • ρⱼ = 0`, apply `e i` to both sides; the sum
collapses by the Kronecker condition to `aᵢ · 1 = 0`, so `aᵢ = 0`. -/
theorem perfect_distinguishable_imp_linear_independent
    {G : GPT V} {n : ℕ} (ρ : Fin n → V)
    (w : PerfectWitness (G := G) ρ) :
    LinearIndependent ℝ ρ := by
  rw [Fintype.linearIndependent_iff]
  intro a hcomb i
  -- Apply e i to both sides; surviving term is a i * 1.
  have happly : w.e i (∑ j, a j • ρ j) = w.e i (0 : V) := by rw [hcomb]
  rw [map_zero, map_sum] at happly
  simp only [map_smul, smul_eq_mul, w.kronecker] at happly
  -- happly : ∑ j, a j * (if i = j then 1 else 0) = 0
  have : ∑ j : Fin n, a j * (if i = j then (1 : ℝ) else 0) = a i := by
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [if_neg (Ne.symm hji)])
        (fun h => by exact absurd (Finset.mem_univ i) h)]
    simp
  rw [this] at happly
  exact happly

/-- **N perfectly distinguishable states require an N-dimensional state space.**

This is the structural form of Hardy's "operational dimension ≤
state-space dimension" inequality, derived in our framework. -/
theorem operational_dim_le_state_dim
    {G : GPT V} [Module.Finite ℝ V]
    {n : ℕ} (ρ : Fin n → V) (w : PerfectWitness (G := G) ρ) :
    n ≤ Module.finrank ℝ V := by
  have hLI := perfect_distinguishable_imp_linear_independent ρ w
  have := hLI.fintype_card_le_finrank
  simpa using this

/-- **Equivalent formulation.** No injective family of perfectly
distinguishable states of cardinality exceeding the state-space
dimension exists. -/
theorem no_oversized_perfect_distinguishability
    {G : GPT V} [Module.Finite ℝ V]
    {n : ℕ} (h : n > Module.finrank ℝ V)
    (ρ : Fin n → V) (w : PerfectWitness (G := G) ρ) : False :=
  Nat.lt_irrefl _ (lt_of_lt_of_le h (operational_dim_le_state_dim ρ w))

/-- A single state always has a trivial PerfectWitness: the unit
effect (giving probability 1 on that state). Useful as a base case. -/
def perfectWitness_singleton {G : GPT V}
    (ρ : V) (hρ : ρ ∈ G.states) :
    PerfectWitness (G := G) (fun _ : Fin 1 => ρ) where
  e := fun _ => G.unit
  kronecker i j := by
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp
    exact G.states_normalized ρ hρ

/-- A PerfectWitness gives effects such that diagonal entries equal 1. -/
@[simp] theorem PerfectWitness.diag {G : GPT V} {n : ℕ} {ρ : Fin n → V}
    (w : PerfectWitness (G := G) ρ) (i : Fin n) :
    w.e i (ρ i) = 1 := by
  have := w.kronecker i i
  simpa using this

/-- A PerfectWitness gives effects such that off-diagonal entries equal 0. -/
theorem PerfectWitness.offdiag {G : GPT V} {n : ℕ} {ρ : Fin n → V}
    (w : PerfectWitness (G := G) ρ) {i j : Fin n} (hij : i ≠ j) :
    w.e i (ρ j) = 0 := by
  have := w.kronecker i j
  simpa [hij] using this

end Distinguish
end Perspectival
