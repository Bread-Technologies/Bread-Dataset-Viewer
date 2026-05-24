/-
Perspectival Physics — Classical GPT instance
==============================================

A concrete classical Generalized Probabilistic Theory: the n-outcome
classical theory. State space is the standard simplex Δⁿ; effects are
the unit hypercube [0,1]ⁿ; unit functional is the all-ones map.

Status:
  ✓ The classical n-outcome GPT is constructed and verified as an
    instance of `Perspectival.GPT (Fin n → ℝ)`.
  ✓ Convexity of the standard simplex (states) and unit hypercube
    (effects) are proven by reduction to Mathlib's stdSimplex / Convex
    lemmas.
  ✓ Probabilities lie in [0, 1] for any state and effect.

Framework reading: classical theory is what you get from the
perspective-wanting structure when complement is trivial (a perspective
"meets" its own complement in a fully deterministic way), no
nontrivial interference, and the algebra of facts is commutative.
In Hardy's terms: K = N. The framework allows this case; it does not
distinguish it from quantum until additional axioms are added.
-/

import Perspectival.GPT
import Perspectival.Distinguish
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.StdSimplex

namespace Perspectival
namespace Classical

open scoped BigOperators

variable (n : ℕ)

/-- The carrier vector space: real-valued functions on `Fin n`. -/
abbrev V := Fin n → ℝ

/-- The unit functional: sum of components. -/
def unitFn : V n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- States: probability distributions (the standard simplex). -/
def states : Set (V n) := stdSimplex ℝ (Fin n)

/-- The states set is convex (standard simplex). -/
theorem states_convex : Convex ℝ (states n) := convex_stdSimplex ℝ (Fin n)

/-- States are normalized: the unit functional gives 1 on every state. -/
theorem unit_eq_one_on_states (x : V n) (hx : x ∈ states n) :
    unitFn n x = 1 := hx.2

/-- Effects: linear functionals given by inner product with vectors
whose components are in [0, 1]. -/
def effectVec : Set (V n) := { f | ∀ i, 0 ≤ f i ∧ f i ≤ 1 }

/-- Inner-product map: a coefficient vector `f` defines the linear
functional `x ↦ ∑ f i * x i`. -/
def innerLin (f : V n) : V n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, f i * x i
  map_add' x y := by
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.mul_sum, mul_left_comm]

/-- Set of valid effects. -/
def effects : Set (V n →ₗ[ℝ] ℝ) := innerLin n '' effectVec n

/-- The effect vector `(1, 1, ..., 1)` gives the unit functional. -/
theorem unit_is_innerLin_one :
    unitFn n = innerLin n (fun _ => 1) := by
  apply LinearMap.ext
  intro x
  show ∑ i, x i = ∑ i, 1 * x i
  simp

/-- The unit functional is in `effects`. -/
theorem unit_in_effects : unitFn n ∈ effects n := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i; exact ⟨zero_le_one, le_refl _⟩
  · exact (unit_is_innerLin_one n).symm

/-- Probability of an effect on a state lies in [0, 1]. -/
theorem prob_in_unit_interval (e : V n →ₗ[ℝ] ℝ) (he : e ∈ effects n)
    (x : V n) (hx : x ∈ states n) :
    0 ≤ e x ∧ e x ≤ 1 := by
  obtain ⟨f, hf, rfl⟩ := he
  obtain ⟨hpos, hsum⟩ := hx
  refine ⟨?_, ?_⟩
  · -- 0 ≤ ∑ f i * x i
    show 0 ≤ ∑ i, f i * x i
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hf i).1 (hpos i)
  · -- ∑ f i * x i ≤ 1
    show ∑ i, f i * x i ≤ 1
    calc ∑ i, f i * x i
        ≤ ∑ i, 1 * x i := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (hf i).2 (hpos i)
      _ = ∑ i, x i := by simp
      _ = 1 := hsum

/-- Convexity of `effects`: a convex combination of inner-prod functionals
remains an inner-prod functional with coefficients in [0,1]. -/
theorem effects_convex : Convex ℝ (effects n) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ a b ha hb hab
  refine ⟨a • f + b • g, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · -- 0 ≤ a * f i + b * g i
      have := add_nonneg (mul_nonneg ha (hf i).1) (mul_nonneg hb (hg i).1)
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    · -- a * f i + b * g i ≤ 1
      have hf1 : a * f i ≤ a * 1 := mul_le_mul_of_nonneg_left (hf i).2 ha
      have hg1 : b * g i ≤ b * 1 := mul_le_mul_of_nonneg_left (hg i).2 hb
      have : a * f i + b * g i ≤ a + b := by linarith
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hab] using
        this.trans hab.le
  · apply LinearMap.ext
    intro x
    show ∑ i, (a • f + b • g) i * x i = a * (∑ i, f i * x i) + b * (∑ i, g i * x i)
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, mul_assoc]

/-! ## Vertices of the classical simplex are perfectly distinguishable -/

/-- The i-th vertex of the standard simplex: probability mass 1 at i,
0 elsewhere. -/
def vertex (i : Fin n) : V n := fun j => if i = j then 1 else 0

/-- Vertices are states. -/
theorem vertex_in_states (i : Fin n) : vertex n i ∈ states n := by
  refine ⟨?_, ?_⟩
  · intro j; show 0 ≤ (if i = j then (1 : ℝ) else 0); split <;> simp
  · show ∑ j, (if i = j then (1 : ℝ) else 0) = 1
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [if_neg hji.symm])
        (by intro h; exact absurd (Finset.mem_univ i) h)]
    simp

/-- The i-th coordinate projection as a linear functional. -/
def proj (i : Fin n) : V n →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Coordinate projections evaluate vertices to Kronecker deltas. -/
@[simp] theorem proj_vertex (i j : Fin n) :
    proj n i (vertex n j) = if j = i then 1 else 0 := by
  show (if j = i then (1 : ℝ) else 0) = if j = i then 1 else 0
  rfl

/-- The classical n-outcome GPT. -/
def gpt : Perspectival.GPT (V n) where
  unit := unitFn n
  states := states n
  effects := effects n
  states_convex := states_convex n
  effects_convex := effects_convex n
  states_normalized := fun ρ hρ => unit_eq_one_on_states n ρ hρ
  prob_in_unit_interval := prob_in_unit_interval n
  unit_is_effect := unit_in_effects n

/-- The vertices of the classical simplex are perfectly distinguishable
by the coordinate projections. -/
def perfectWitness :
    Perspectival.Distinguish.PerfectWitness (G := gpt n) (vertex n) where
  e := proj n
  kronecker i j := by
    show proj n i (vertex n j) = if i = j then 1 else 0
    rw [proj_vertex]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]

/-- **Vertices of the n-simplex are linearly independent** — the
classical-instance corollary of `perfect_distinguishable_imp_linear_independent`. -/
theorem vertex_linear_independent :
    LinearIndependent ℝ (vertex n) :=
  Perspectival.Distinguish.perfect_distinguishable_imp_linear_independent
    (vertex n) (perfectWitness n)

end Classical
end Perspectival
