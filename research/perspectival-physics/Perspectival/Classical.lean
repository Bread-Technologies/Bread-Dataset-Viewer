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
import Perspectival.Continuity
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Topology.Instances.Matrix

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

/-- The coordinate projection `proj i` is in the effects set, witnessed by the
vertex coefficient vector. -/
theorem proj_in_effects (i : Fin n) : proj n i ∈ effects n := by
  refine ⟨vertex n i, ?_, ?_⟩
  · intro j
    show 0 ≤ (if i = j then (1 : ℝ) else 0) ∧ (if i = j then (1 : ℝ) else 0) ≤ 1
    split <;> simp
  · apply LinearMap.ext
    intro x
    show (innerLin n (vertex n i)) x = (proj n i) x
    show ∑ j, vertex n i j * x j = x i
    rw [Finset.sum_eq_single i (fun j _ hji => by
        show vertex n i j * x j = 0
        rw [show vertex n i j = 0 from if_neg hji.symm]; ring)
        (by intro h; exact absurd (Finset.mem_univ i) h)]
    show vertex n i i * x i = x i
    rw [show vertex n i i = 1 from if_pos rfl]
    ring

/-- **Vertices are pairwise distinguishable**: for `i ≠ j`, the projection
`proj n i` separates `vertex n i` and `vertex n j`. -/
theorem vertices_distinguishable (i j : Fin n) (hij : i ≠ j) :
    Perspectival.Hardy.Distinguishable (gpt n) (vertex n i) (vertex n j) := by
  refine ⟨proj n i, proj_in_effects n i, ?_, ?_⟩
  · show proj n i (vertex n i) = 1
    simp [proj_vertex]
  · show proj n i (vertex n j) = 0
    rw [proj_vertex]
    simp [Ne.symm hij]

/-- The set of vertices forms a Hardy-style distinguishability set. -/
theorem vertex_distinguishability_set :
    Perspectival.Hardy.DistinguishabilitySet (gpt n)
      ((Finset.univ : Finset (Fin n)).image (vertex n)) := by
  constructor
  · intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact vertex_in_states n i
  · intro ρ₁ hρ₁ ρ₂ hρ₂ hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ₁
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hρ₂
    exact vertices_distinguishable n i j (fun h => hne (by rw [h]))

-- NOTE: A natural follow-up theorem `vertex_is_extreme i : IsExtreme ℝ
-- (states n) {vertex n i}` (vertices are pure states) would tie this
-- module to `Continuity.PureState`. The proof requires coordinate-wise
-- analysis of an open-segment representation and is non-trivial; left
-- for follow-up. See ROADMAP.md R1.

/-- **Vertex decomposition for the classical GPT.** Every element of
`V n = Fin n → ℝ` is its coordinate-wise vertex combination. -/
theorem vertex_decomposition (f : V n) :
    f = ∑ i, f i • vertex n i := by
  funext j
  show f j = (∑ i, f i • vertex n i) j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j
    (fun i _ hij => by
      show f i • vertex n i j = 0
      show f i * (if i = j then (1 : ℝ) else 0) = 0
      simp [hij])
    (fun h => absurd (Finset.mem_univ j) h)]
  symm
  show (f j • vertex n j) j = f j
  show f j * (if j = j then (1 : ℝ) else 0) = f j
  simp

/-- The classical-GPT vertices span `V n`. -/
theorem vertices_span : Submodule.span ℝ (Set.range (vertex n)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [vertex_decomposition n f]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ (f i) (Submodule.subset_span ⟨i, rfl⟩))

/-! ## R6 progress: Classical n=1 has only id as Reversible

For the classical 1-outcome GPT, V_1 ≃ ℝ has a one-dimensional state
space = {(1)} (the singleton stdSimplex). Any state-preserving linear
map R : V_1 →ₗ V_1 must satisfy R(1-vec) = 1-vec, plus linearity.
For the one-dim case, this forces R = id. -/

/-- The unique state in V_1 is the vertex (1). -/
theorem classical_unique_state (ρ : V 1) (hρ : ρ ∈ states 1) :
    ρ = vertex 1 0 := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  -- ρ 0 = 1 because ρ ∈ stdSimplex and sum = 1 with only one term
  have hsum := hρ.2
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from by decide,
      Finset.sum_singleton] at hsum
  show ρ 0 = vertex 1 0 0
  show ρ 0 = (if (0 : Fin 1) = 0 then (1 : ℝ) else 0)
  simp
  exact hsum

/-- A linear map V 1 → V 1 preserving the unit functional fixes the
1-vector. Specifically, if `unit ∘ R = unit`, then R(δ₀) = δ₀ on V 1
where δ₀ is the unique state. -/
theorem classical_n1_state_preserving_eq_id
    (R : V 1 →ₗ[ℝ] V 1)
    (hR : ∀ ρ ∈ states 1, R ρ ∈ states 1) :
    R = LinearMap.id := by
  apply LinearMap.ext
  intro v
  -- v ∈ V 1 is determined by v 0 ∈ ℝ
  -- writing v = (v 0) • vertex 1 0, linearity gives
  -- R v = (v 0) • R (vertex 1 0)
  -- and we need R (vertex 1 0) = vertex 1 0 (the unique state)
  have hv_eq : v = (v 0) • vertex 1 0 := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show v 0 = (v 0) * vertex 1 0 0
    show v 0 = (v 0) * (if (0 : Fin 1) = 0 then (1 : ℝ) else 0)
    simp
  -- Apply linearity
  rw [hv_eq, map_smul]
  have hR0 : R (vertex 1 0) = vertex 1 0 :=
    classical_unique_state (R (vertex 1 0))
      (hR (vertex 1 0) (vertex_in_states 1 0))
  rw [hR0]
  show (v 0) • vertex 1 0 = LinearMap.id ((v 0) • vertex 1 0)
  rfl

/-- Concrete: every Reversible on Classical n=1 GPT has toLin = id. -/
theorem classical_n1_reversible_toLin_eq_id
    (R : Perspectival.Continuity.Reversible (gpt 1)) :
    R.toLin = LinearMap.id :=
  classical_n1_state_preserving_eq_id R.toLin R.preserves_states

/-- The same expressed via StrictReversible. -/
theorem classical_n1_strict_reversible_toLin_eq_id
    (R : Perspectival.Continuity.StrictReversible (gpt 1)) :
    R.toLin = LinearMap.id :=
  classical_n1_state_preserving_eq_id R.toLin R.preserves_states

/-! ## R6 progress: Classical n=2 — state-preserving linear maps -/

/-- For Classical n=2 GPT, every state ρ ∈ V 2 has both coordinates
in [0,1] and they sum to 1, so ρ 0 + ρ 1 = 1. -/
theorem classical_n2_state_sum (ρ : V 2) (hρ : ρ ∈ states 2) :
    ρ 0 + ρ 1 = 1 := by
  have hsum := hρ.2
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  exact hsum

/-- For Classical n=2, every state has nonneg coordinates. -/
theorem classical_n2_state_nonneg (ρ : V 2) (hρ : ρ ∈ states 2) (j : Fin 2) :
    0 ≤ ρ j := hρ.1 j

/-- The vertex 0 in V 2 is (1, 0). -/
theorem vertex_n2_zero_coords :
    vertex 2 0 0 = 1 ∧ vertex 2 0 1 = 0 := by
  refine ⟨?_, ?_⟩
  · show (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 1
    simp
  · show (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) = 0
    simp

/-- The vertex 1 in V 2 is (0, 1). -/
theorem vertex_n2_one_coords :
    vertex 2 1 0 = 0 ∧ vertex 2 1 1 = 1 := by
  refine ⟨?_, ?_⟩
  · show (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0
    simp
  · show (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) = 1
    simp

/-! For Classical n=2 GPT, a state-preserving linear map R sends the
vertex 0 to either vertex 0 or another state with first coord ≥ 0 and
both coords summing to 1. Specifically if R is also injective (= a
bijection), R must send vertices to vertices. -/

/-- Any V 2 state with `ρ 0 = 1` is exactly vertex 2 0. -/
theorem classical_n2_first_coord_one_iff (ρ : V 2) (hρ : ρ ∈ states 2) :
    ρ = vertex 2 0 ↔ ρ 0 = 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [h]
    exact (vertex_n2_zero_coords).1
  · intro h
    funext j
    have hsum := classical_n2_state_sum ρ hρ
    have h2 : ρ 1 = 0 := by linarith
    fin_cases j
    · show ρ 0 = vertex 2 0 0
      rw [h]
      exact (vertex_n2_zero_coords).1.symm
    · show ρ 1 = vertex 2 0 1
      rw [h2]
      exact (vertex_n2_zero_coords).2.symm

/-- Any V 2 state with `ρ 1 = 1` is exactly vertex 2 1. -/
theorem classical_n2_second_coord_one_iff (ρ : V 2) (hρ : ρ ∈ states 2) :
    ρ = vertex 2 1 ↔ ρ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [h]
    exact (vertex_n2_one_coords).2
  · intro h
    funext j
    have hsum := classical_n2_state_sum ρ hρ
    have h0 : ρ 0 = 0 := by linarith
    fin_cases j
    · show ρ 0 = vertex 2 1 0
      rw [h0]
      exact (vertex_n2_one_coords).1.symm
    · show ρ 1 = vertex 2 1 1
      rw [h]
      exact (vertex_n2_one_coords).2.symm

/-- The midpoint state of V 2 stdSimplex, namely (1/2, 1/2). -/
noncomputable def n2_midpoint : V 2 := fun _ => (1/2 : ℝ)

/-- The midpoint state is in states 2. -/
theorem n2_midpoint_in_states : n2_midpoint ∈ states 2 := by
  refine ⟨?_, ?_⟩
  · intro j
    show (0 : ℝ) ≤ 1/2
    norm_num
  · show ∑ j, (1/2 : ℝ) = 1
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-- The midpoint is NOT a vertex (extreme point). -/
theorem n2_midpoint_ne_vertex_zero : n2_midpoint ≠ vertex 2 0 := by
  intro h
  have := congr_fun h 0
  rw [show n2_midpoint 0 = (1/2 : ℝ) from rfl] at this
  rw [(vertex_n2_zero_coords).1] at this
  norm_num at this

/-- Midpoint ≠ vertex 1 either. -/
theorem n2_midpoint_ne_vertex_one : n2_midpoint ≠ vertex 2 1 := by
  intro h
  have := congr_fun h 1
  rw [show n2_midpoint 1 = (1/2 : ℝ) from rfl] at this
  rw [(vertex_n2_one_coords).2] at this
  norm_num at this

/-- The midpoint is `(1/2) • vertex 0 + (1/2) • vertex 1`. -/
theorem n2_midpoint_decomp :
    n2_midpoint = (1/2 : ℝ) • vertex 2 0 + (1/2 : ℝ) • vertex 2 1 := by
  funext j
  fin_cases j
  · show (1/2 : ℝ) = (1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * vertex 2 1 0
    rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
    norm_num
  · show (1/2 : ℝ) = (1/2 : ℝ) * vertex 2 0 1 + (1/2 : ℝ) * vertex 2 1 1
    rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]
    norm_num

/-! ## The SWAP linear map on V 2 -/

/-- The SWAP linear map on V 2 (swaps the two coordinates). -/
def swapLin : V 2 →ₗ[ℝ] V 2 where
  toFun v := fun j => v (1 - j)
  map_add' u v := by
    funext j
    show u (1 - j) + v (1 - j) = u (1 - j) + v (1 - j)
    rfl
  map_smul' c v := by
    funext j
    show c * v (1 - j) = c * v (1 - j)
    rfl

/-- swapLin sends vertex 0 to vertex 1. -/
theorem swapLin_vertex_zero : swapLin (vertex 2 0) = vertex 2 1 := by
  funext j
  show vertex 2 0 (1 - j) = vertex 2 1 j
  show (if (0 : Fin 2) = 1 - j then (1 : ℝ) else 0)
     = (if (1 : Fin 2) = j then (1 : ℝ) else 0)
  fin_cases j <;> simp <;> decide

/-- swapLin sends vertex 1 to vertex 0. -/
theorem swapLin_vertex_one : swapLin (vertex 2 1) = vertex 2 0 := by
  funext j
  show vertex 2 1 (1 - j) = vertex 2 0 j
  show (if (1 : Fin 2) = 1 - j then (1 : ℝ) else 0)
     = (if (0 : Fin 2) = j then (1 : ℝ) else 0)
  fin_cases j <;> simp <;> decide

/-- swapLin is its own inverse. -/
theorem swapLin_swapLin (v : V 2) : swapLin (swapLin v) = v := by
  funext j
  show v (1 - (1 - j)) = v j
  congr 1
  fin_cases j <;> decide

/-- swapLin preserves states. -/
theorem swapLin_preserves_states (v : V 2) (hv : v ∈ states 2) :
    swapLin v ∈ states 2 := by
  refine ⟨?_, ?_⟩
  · intro j
    show 0 ≤ v (1 - j)
    exact hv.1 _
  · show ∑ j, v (1 - j) = 1
    have hv2 := hv.2
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton]
    show v (1 - 0) + v (1 - 1) = 1
    rw [show ((1 : Fin 2) - 0) = 1 from by decide,
        show ((1 : Fin 2) - 1) = 0 from by decide]
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton] at hv2
    linarith

/-- swapLin preserves the unit functional. -/
theorem swapLin_preserves_unit :
    (unitFn 2).comp swapLin = unitFn 2 := by
  apply LinearMap.ext
  intro v
  show ∑ j, v (1 - j) = ∑ j, v j
  have univ_eq : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [univ_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  show v (1 - 0) + v (1 - 1) = v 0 + v 1
  rw [show ((1 : Fin 2) - 0) = 1 from by decide,
      show ((1 : Fin 2) - 1) = 0 from by decide]
  ring

/-- swapLin is bijective. -/
theorem swapLin_bijective : Function.Bijective swapLin := by
  refine ⟨?_, ?_⟩
  · intro u v h
    have h2 : swapLin (swapLin u) = swapLin (swapLin v) := by rw [h]
    rw [swapLin_swapLin, swapLin_swapLin] at h2
    exact h2
  · intro v
    exact ⟨swapLin v, swapLin_swapLin v⟩

/-- swapLin is continuous (finite-dimensional linear map). -/
theorem swapLin_continuous : Continuous swapLin := by
  -- A linear map on Pi-spaces of ℝ is continuous when each
  -- coordinate map is. swapLin v j = v (1 - j), which is continuous in v.
  apply continuous_pi
  intro j
  -- coord j of swapLin v is v (1 - j); this is continuous in v
  exact continuous_apply (1 - j)

/-- swapLin as a Reversible. -/
def swapReversible : Perspectival.Continuity.Reversible (gpt 2) where
  toLin := swapLin
  continuous_toLin := swapLin_continuous
  preserves_states := swapLin_preserves_states
  preserves_unit := swapLin_preserves_unit

/-- swapLin as a StrictReversible. -/
def swapStrictReversible : Perspectival.Continuity.StrictReversible (gpt 2) where
  toReversible := swapReversible
  isEquiv := swapLin_bijective

/-- swapReversible and Reversible.id are distinct (different toLin). -/
theorem swapReversible_ne_id :
    swapReversible.toLin ≠ (Perspectival.Continuity.Reversible.id (gpt 2)).toLin := by
  intro h
  have h2 : swapReversible.toLin (vertex 2 0)
          = (Perspectival.Continuity.Reversible.id (gpt 2)).toLin (vertex 2 0) := by
    rw [h]
  rw [show swapReversible.toLin (vertex 2 0) = swapLin (vertex 2 0) from rfl] at h2
  rw [swapLin_vertex_zero] at h2
  rw [show (Perspectival.Continuity.Reversible.id (gpt 2)).toLin (vertex 2 0)
          = vertex 2 0 from rfl] at h2
  -- h2 : vertex 2 1 = vertex 2 0
  have h3 : vertex 2 1 0 = vertex 2 0 0 := congr_fun h2 0
  rw [(vertex_n2_one_coords).1, (vertex_n2_zero_coords).1] at h3
  norm_num at h3

/-! ## R6 n=2: state-preserving linear maps form a 1-parameter family -/

/-! Any state-preserving linear R : V 2 →ₗ V 2 is determined by
where it sends vertex 0 (and by linearity + state preservation, where
it sends vertex 1 = something with sum 1). Specifically:
  R (vertex 2 0) is a state in V 2.
We can write R (vertex 2 0) = (a, 1-a) for some a ∈ [0,1].
Similarly R (vertex 2 1) = (b, 1-b) for some b ∈ [0,1].
By linearity of R, R (vertex 2 0) + R (vertex 2 1) = R (1, 1).
But (1, 1) is NOT a state. However the unit-preservation gives:
∑ R(v) = ∑ v, so the second coords of R(v0) and R(v1) sum to 1.
-/

/-- For any state-preserving linear map R : V 2 →ₗ V 2 preserving the
unit, the first coordinate of R (vertex 2 0) is in [0, 1]. -/
theorem classical_n2_state_preserving_first_coord_bound
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    0 ≤ R (vertex 2 0) 0 ∧ R (vertex 2 0) 0 ≤ 1 := by
  have hRv := hR (vertex 2 0) (vertex_in_states 2 0)
  refine ⟨hRv.1 0, ?_⟩
  have hsum := classical_n2_state_sum (R (vertex 2 0)) hRv
  have hnn1 := hRv.1 1
  linarith

/-- Similarly for vertex 1. -/
theorem classical_n2_state_preserving_first_coord_bound_v1
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    0 ≤ R (vertex 2 1) 0 ∧ R (vertex 2 1) 0 ≤ 1 := by
  have hRv := hR (vertex 2 1) (vertex_in_states 2 1)
  refine ⟨hRv.1 0, ?_⟩
  have hsum := classical_n2_state_sum (R (vertex 2 1)) hRv
  have hnn1 := hRv.1 1
  linarith

/-! ## Twoavailable strict-agency on Classical n=2 -/

/-- The set `{id, swap}` of StrictReversibles on Classical n=2. -/
def n2_two_strict :
    Set (Perspectival.Continuity.StrictReversible (gpt 2)) :=
  {Perspectival.Continuity.StrictReversible.id (gpt 2), swapStrictReversible}

/-- id is in n2_two_strict. -/
theorem id_in_n2_two_strict :
    Perspectival.Continuity.StrictReversible.id (gpt 2) ∈ n2_two_strict := by
  left; rfl

/-- swap is in n2_two_strict. -/
theorem swap_in_n2_two_strict :
    swapStrictReversible ∈ n2_two_strict := by
  right; rfl

/-! ## Bijection sends extreme points to extreme points -/

/-- A state-preserving INJECTIVE linear map V 2 →ₗ V 2 must send
distinct vertices to distinct states. -/
theorem classical_n2_injective_distinct_images
    (R : V 2 →ₗ[ℝ] V 2)
    (hinj : Function.Injective R) :
    R (vertex 2 0) ≠ R (vertex 2 1) := by
  intro h
  apply hinj at h
  have h00 : vertex 2 0 0 = vertex 2 1 0 := congr_fun h 0
  rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1] at h00
  norm_num at h00

/-- A state-preserving SURJECTIVE linear map V 2 →ₗ V 2 has every
state in its image. In particular vertex 2 0 is in the image. -/
theorem classical_n2_surjective_vertex_image
    (R : V 2 →ₗ[ℝ] V 2)
    (hsurj : Function.Surjective R) :
    ∃ v, R v = vertex 2 0 := hsurj _

/-! ## R6 n=2: bijection ⇒ permutation theorem

The key claim: a state-preserving BIJECTIVE linear map R : V 2 →ₗ V 2
either equals id (= sends vertex 0 ↦ vertex 0 and vertex 1 ↦ vertex 1)
or equals swap (= sends vertex 0 ↦ vertex 1 and vertex 1 ↦ vertex 0).

The proof has two pieces:
1. R must send vertex 0 to a state ρ_0. By bijectivity, ρ_0 is an
   extreme point of stdSimplex, i.e., a vertex.
2. By symmetry, R must send vertex 1 to a different vertex.
3. So R is determined by which vertex it sends vertex 0 to: id or swap.
-/

/-- State-preserving image of vertex 0 has first coord between 0 and 1. -/
theorem classical_n2_image_vertex_zero_in_states
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    R (vertex 2 0) ∈ states 2 :=
  hR _ (vertex_in_states 2 0)

/-- Image of vertex 1 is a state. -/
theorem classical_n2_image_vertex_one_in_states
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    R (vertex 2 1) ∈ states 2 :=
  hR _ (vertex_in_states 2 1)

/-- For Classical n=2: a state ρ on V 2 with ρ 0 + ρ 1 = 1 and ρ i ∈ [0,1]
is the midpoint of (vertex 0)·(ρ 0) and (vertex 1)·(ρ 1)... actually,
it's exactly (ρ 0)•vertex 0 + (ρ 1)•vertex 1. -/
theorem classical_n2_state_eq_combo (ρ : V 2) (hρ : ρ ∈ states 2) :
    ρ = (ρ 0) • vertex 2 0 + (ρ 1) • vertex 2 1 := by
  funext j
  fin_cases j
  · show ρ 0 = (ρ 0) * vertex 2 0 0 + (ρ 1) * vertex 2 1 0
    rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
    ring
  · show ρ 1 = (ρ 0) * vertex 2 0 1 + (ρ 1) * vertex 2 1 1
    rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]
    ring

/-- For a state ρ on V 2, ρ 0 = 0 or ρ 0 = 1 IFF ρ is a vertex. -/
theorem classical_n2_state_first_coord_eq_zero_or_one_iff
    (ρ : V 2) (hρ : ρ ∈ states 2) :
    (ρ 0 = 0 ∨ ρ 0 = 1) ↔ (ρ = vertex 2 0 ∨ ρ = vertex 2 1) := by
  refine ⟨?_, ?_⟩
  · rintro (h0 | h0)
    · right
      have hsum := classical_n2_state_sum ρ hρ
      have h1 : ρ 1 = 1 := by linarith
      exact (classical_n2_second_coord_one_iff ρ hρ).mpr h1
    · left
      exact (classical_n2_first_coord_one_iff ρ hρ).mpr h0
  · rintro (rfl | rfl)
    · right; exact (vertex_n2_zero_coords).1
    · left; exact (vertex_n2_one_coords).1

/-! ## R6 KEY INSIGHT: bijective state-preserving ≠ permutation

A KEY realization: a state-preserving linear bijection V 2 → V 2 is
exactly a doubly-stochastic 2×2 matrix with nonzero determinant.

For [[a, b], [1-a, 1-b]] with a, b ∈ [0,1]:
- State-preserving (cols sum to 1, nonneg): ✓ by construction.
- Bijective iff det = a - b ≠ 0.

So the set of bijective state-preserving linear maps on V 2 is:
  {(a, b) ∈ [0,1]² : a ≠ b}

This set has TWO connected components:
- {(a, b) : a > b}, containing id (a=1, b=0).
- {(a, b) : a < b}, containing swap (a=0, b=1).

The boundary a = b consists of singular (non-bijective) maps.

R6 prediction confirmed for n=2: NO continuous path through bijective
state-preserving linear maps connects id and swap. Any continuous path
from id to swap must cross the singular line, which violates
bijection-along-the-path.

So `StrictConnectedAgency` on Classical n=2 with avail = {id, swap}
has NO StrictReversiblePath between id and swap. There's no nontrivial
agency. The only agency is trivial = {id} (or {swap}, equivalently).

For n ≥ 3 the same phenomenon holds (permutation matrices form S_N,
discrete in Birkhoff polytope). So R6 is a NONTRIVIAL constraint:
classical GPTs cannot support nontrivial StrictConnectedAgency. -/

/-! ## Toward formalizing the disconnectedness theorem -/

/-- The determinant function `R ↦ R(vertex 0) 0 - R(vertex 1) 0`. For
state-preserving linear R on V 2, this equals a - b where
R = [[a, b], [1-a, 1-b]]. -/
noncomputable def n2_disc_det (R : V 2 →ₗ[ℝ] V 2) : ℝ :=
  R (vertex 2 0) 0 - R (vertex 2 1) 0

/-- For id : V 2 →ₗ V 2, n2_disc_det = 1. -/
theorem n2_disc_det_id : n2_disc_det LinearMap.id = 1 := by
  show LinearMap.id (vertex 2 0) 0 - LinearMap.id (vertex 2 1) 0 = 1
  show vertex 2 0 0 - vertex 2 1 0 = 1
  rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
  norm_num

/-- For swap : V 2 →ₗ V 2, n2_disc_det = -1. -/
theorem n2_disc_det_swap : n2_disc_det swapLin = -1 := by
  show swapLin (vertex 2 0) 0 - swapLin (vertex 2 1) 0 = -1
  rw [swapLin_vertex_zero, swapLin_vertex_one]
  rw [(vertex_n2_one_coords).1, (vertex_n2_zero_coords).1]
  norm_num

/-- n2_disc_det is invariant under R₁ = R₂ (since both args are R). -/
theorem n2_disc_det_continuous_in_R
    (R₁ R₂ : V 2 →ₗ[ℝ] V 2) :
    n2_disc_det R₁ - n2_disc_det R₂
      = (R₁ (vertex 2 0) 0 - R₂ (vertex 2 0) 0)
      - (R₁ (vertex 2 1) 0 - R₂ (vertex 2 1) 0) := by
  show R₁ (vertex 2 0) 0 - R₁ (vertex 2 1) 0
     - (R₂ (vertex 2 0) 0 - R₂ (vertex 2 1) 0)
     = _
  ring

/-- IVT setup: for any γ : [0,1] → ℝ continuous with γ 0 = 1 and γ 1 = -1,
there exists t with γ t = 0. -/
theorem ivt_path_one_to_neg_one
    (f : unitInterval → ℝ) (hf : Continuous f)
    (h0 : f 0 = 1) (h1 : f 1 = -1) :
    ∃ t : unitInterval, f t = 0 := by
  -- Apply IVT on the continuous map f : [0,1] → ℝ which takes value 1 at 0
  -- and -1 at 1. The value 0 is between -1 and 1, so it's attained.
  have : Set.OrdConnected (Set.range f) := by
    apply (isPreconnected_range hf).ordConnected
  have h0_in : (1 : ℝ) ∈ Set.range f := ⟨0, h0⟩
  have h1_in : (-1 : ℝ) ∈ Set.range f := ⟨1, h1⟩
  have : (0 : ℝ) ∈ Set.range f := by
    have hmem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
    exact this.out h1_in h0_in hmem
  exact this

/-- Concrete form: if γ : [0,1] → (V 2 →ₗ V 2) is a continuous path with
γ 0 = id and γ 1 = swap, then there exists t with n2_disc_det (γ t) = 0. -/
theorem n2_no_continuous_path_id_to_swap_through_bijections
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun t => n2_disc_det (γ t)))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swapLin) :
    ∃ t : unitInterval, n2_disc_det (γ t) = 0 := by
  apply ivt_path_one_to_neg_one (fun t => n2_disc_det (γ t)) hcont
  · show n2_disc_det (γ 0) = 1
    rw [h0]
    exact n2_disc_det_id
  · show n2_disc_det (γ 1) = -1
    rw [h1]
    exact n2_disc_det_swap

/-! ## Linking det = 0 to non-bijectivity for state-preserving R -/

/-- For a state-preserving linear R : V 2 →ₗ V 2 with n2_disc_det R = 0,
the map R sends vertex 0 and vertex 1 to states with the SAME first
coordinate. Combined with state-sum = 1, this forces R(vertex 0) =
R(vertex 1). Hence R is NOT injective. -/
theorem n2_disc_det_zero_implies_not_injective
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hdet : n2_disc_det R = 0) :
    ¬ Function.Injective R := by
  intro hinj
  -- hdet : R(v0) 0 - R(v1) 0 = 0
  have hdet' : R (vertex 2 0) 0 - R (vertex 2 1) 0 = 0 := hdet
  have hd : R (vertex 2 0) 0 = R (vertex 2 1) 0 := by linarith
  -- Both R(v0) and R(v1) are states, so their first coord + second coord = 1
  have hRv0 := hR (vertex 2 0) (vertex_in_states 2 0)
  have hRv1 := hR (vertex 2 1) (vertex_in_states 2 1)
  have hs0 := classical_n2_state_sum (R (vertex 2 0)) hRv0
  have hs1 := classical_n2_state_sum (R (vertex 2 1)) hRv1
  -- So R(v0) 1 = R(v1) 1 too
  have hd1 : R (vertex 2 0) 1 = R (vertex 2 1) 1 := by linarith
  -- Hence R(v0) = R(v1) (function extensionality over Fin 2)
  have hRv : R (vertex 2 0) = R (vertex 2 1) := by
    funext j
    fin_cases j
    · exact hd
    · exact hd1
  -- But v0 ≠ v1 (by checking first coord), contradicting injectivity
  apply classical_n2_injective_distinct_images R hinj
  exact hRv

/-- Combining: if γ : [0,1] → (V 2 →ₗ V 2) is a state-preserving
continuous path from id to swap, and γ(t) is bijective for all t,
we get a contradiction. -/
theorem classical_n2_no_strict_path_id_to_swap
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun t => n2_disc_det (γ t)))
    (hpreserve : ∀ t, ∀ ρ ∈ states 2, (γ t) ρ ∈ states 2)
    (hbij : ∀ t, Function.Bijective (γ t))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swapLin) :
    False := by
  obtain ⟨t, ht⟩ := n2_no_continuous_path_id_to_swap_through_bijections
                      γ hcont h0 h1
  have hinj : Function.Injective (γ t) := (hbij t).1
  exact n2_disc_det_zero_implies_not_injective (γ t) (hpreserve t) ht hinj

/-- **R6 FINAL FORM (modulo continuity hypothesis).** No
StrictReversiblePath from `swapStrictReversible` to
`StrictReversible.id` exists on Classical n=2 GPT, given the
continuity hypothesis that n2_disc_det ∘ γ is a continuous map. -/
theorem classical_n2_no_strict_reversible_path
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 2)
              (Perspectival.Continuity.StrictReversible.id (gpt 2))
              swapStrictReversible)
    (hcont : Continuous (fun t => n2_disc_det (p.γ t))) :
    False := by
  apply classical_n2_no_strict_path_id_to_swap p.γ hcont
    p.preserves_states_along p.bijective_along
  · -- p.γ 0 = LinearMap.id (from p.start and StrictReversible.id_toLin)
    show p.γ 0 = LinearMap.id
    rw [p.start]
    rfl
  · -- p.γ 1 = swapLin (from p.finish)
    show p.γ 1 = swapLin
    rw [p.finish]
    rfl

/-- Auto-continuity: n2_disc_det ∘ p.γ is continuous, derived from
the joint continuity of p.γ. -/
theorem n2_disc_det_path_continuous
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun pair : unitInterval × V 2 => γ pair.1 pair.2)) :
    Continuous (fun t => n2_disc_det (γ t)) := by
  -- n2_disc_det (γ t) = (γ t) (vertex 2 0) 0 - (γ t) (vertex 2 1) 0
  -- Each (γ t) (vertex i) is continuous in t (specializing v = vertex i in hcont).
  -- Then applying coordinate 0 is continuous_apply 0.
  have h0pair : Continuous (fun t : unitInterval => (t, vertex 2 0)) :=
    Continuous.prodMk continuous_id continuous_const
  have h1pair : Continuous (fun t : unitInterval => (t, vertex 2 1)) :=
    Continuous.prodMk continuous_id continuous_const
  have h0 : Continuous (fun t : unitInterval => γ t (vertex 2 0)) :=
    hcont.comp h0pair
  have h1 : Continuous (fun t : unitInterval => γ t (vertex 2 1)) :=
    hcont.comp h1pair
  have h0c : Continuous (fun t : unitInterval => γ t (vertex 2 0) 0) :=
    (continuous_apply 0).comp h0
  have h1c : Continuous (fun t : unitInterval => γ t (vertex 2 1) 0) :=
    (continuous_apply 0).comp h1
  exact h0c.sub h1c

/-- **R6 FINAL** (no continuity hypothesis needed): No StrictReversiblePath
from id to swap exists on Classical n=2. -/
theorem classical_n2_strict_reversible_path_id_swap_empty
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 2)
              (Perspectival.Continuity.StrictReversible.id (gpt 2))
              swapStrictReversible) :
    False :=
  classical_n2_no_strict_reversible_path p
    (n2_disc_det_path_continuous p.γ p.continuous)

/-- The contrapositive: there is NO StrictReversiblePath from id to swap. -/
theorem classical_n2_strict_reversible_path_id_swap_nonempty_false :
    ¬ Nonempty (Perspectival.Continuity.StrictReversiblePath (gpt 2)
              (Perspectival.Continuity.StrictReversible.id (gpt 2))
              swapStrictReversible) := by
  intro ⟨p⟩
  exact classical_n2_strict_reversible_path_id_swap_empty p

/-- The reverse direction also fails: no StrictReversiblePath from
swap to id either. -/
theorem classical_n2_strict_reversible_path_swap_id_nonempty_false :
    ¬ Nonempty (Perspectival.Continuity.StrictReversiblePath (gpt 2)
              swapStrictReversible
              (Perspectival.Continuity.StrictReversible.id (gpt 2))) := by
  intro ⟨p⟩
  -- Reverse the path
  have p' : Perspectival.Continuity.StrictReversiblePath (gpt 2)
              (Perspectival.Continuity.StrictReversible.id (gpt 2))
              swapStrictReversible := {
    γ := fun t => p.γ (unitInterval.symm t)
    continuous := by
      have h1 : Continuous (fun t : unitInterval => unitInterval.symm t) :=
        unitInterval.continuous_symm
      have h2 : Continuous (fun pair : unitInterval × V 2 =>
                              (unitInterval.symm pair.1, pair.2)) :=
        Continuous.prodMk (h1.comp continuous_fst) continuous_snd
      exact p.continuous.comp h2
    start := by
      show p.γ (unitInterval.symm 0) = _
      rw [unitInterval.symm_zero, p.finish]
    finish := by
      show p.γ (unitInterval.symm 1) = swapLin
      rw [unitInterval.symm_one, p.start]
      rfl
    preserves_states_along := fun t ρ hρ => p.preserves_states_along _ ρ hρ
    preserves_unit_along := fun t => p.preserves_unit_along _
    bijective_along := fun t => p.bijective_along _
  }
  exact classical_n2_strict_reversible_path_id_swap_empty p'

/-- StrictConnectedAgency on Classical n=2 with {id, swap} avail is FALSE. -/
theorem classical_n2_no_two_element_strict_agency
    (A : Perspectival.Continuity.StrictConnectedAgency (gpt 2))
    (hid : Perspectival.Continuity.StrictReversible.id (gpt 2) ∈ A.avail)
    (hswap : swapStrictReversible ∈ A.avail) :
    False := by
  have hp := A.strict_paths _ _ hid hswap
  exact classical_n2_strict_reversible_path_id_swap_nonempty_false hp

/-! ## Corollaries: classical agency = single permutation -/

/-- Any StrictConnectedAgency on Classical n=2 with id available
cannot also have swap available. -/
theorem classical_n2_id_avail_implies_swap_not_avail
    (A : Perspectival.Continuity.StrictConnectedAgency (gpt 2))
    (hid : Perspectival.Continuity.StrictReversible.id (gpt 2) ∈ A.avail) :
    swapStrictReversible ∉ A.avail := by
  intro hswap
  exact classical_n2_no_two_element_strict_agency A hid hswap

/-- The trivial agency (only id) is valid; no agency can extend it
to include swap. -/
theorem classical_n2_trivial_agency_id_avail :
    Perspectival.Continuity.StrictReversible.id (gpt 2) ∈
      (Perspectival.Continuity.trivialStrictAgency (gpt 2)).avail := by
  rfl

/-! ## NOTE: a "swap-only" StrictConnectedAgency does not exist because
the `id_avail` axiom requires identity to be available. So Classical
n=2's *only* StrictConnectedAgency is `trivialStrictAgency` itself
(modulo extending with potential other matrices that aren't id/swap —
but those would also have no continuous path to id, by the same
det-IVT argument). -/

/-! ## Concrete Bool-style tests of R6 n=2 -/

/-- The unique state on Classical n=1 is the vertex 0. -/
example : ∀ ρ ∈ states 1, ρ = vertex 1 0 := classical_unique_state

/-- Classical n=1 has only id as a state-preserving linear map. -/
example (R : V 1 →ₗ[ℝ] V 1) (hR : ∀ ρ ∈ states 1, R ρ ∈ states 1) :
    R = LinearMap.id := classical_n1_state_preserving_eq_id R hR

/-- Classical n=2: 2x2 doubly stochastic matrices form a 1-parameter
family parametrized by (R(vertex 0) 0, R(vertex 1) 0). -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    0 ≤ R (vertex 2 0) 0 ∧ R (vertex 2 0) 0 ≤ 1 :=
  classical_n2_state_preserving_first_coord_bound R hR

/-- For Classical n=2, det of state-preserving R is in [-1, 1]. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    n2_disc_det R ≥ -1 ∧ n2_disc_det R ≤ 1 := by
  have h0 := classical_n2_state_preserving_first_coord_bound R hR
  have h1 := classical_n2_state_preserving_first_coord_bound_v1 R hR
  refine ⟨?_, ?_⟩
  · show R (vertex 2 0) 0 - R (vertex 2 1) 0 ≥ -1
    linarith
  · show R (vertex 2 0) 0 - R (vertex 2 1) 0 ≤ 1
    linarith

/-- det of id on V 2 is 1 (named for clarity). -/
example : n2_disc_det (LinearMap.id : V 2 →ₗ[ℝ] V 2) = 1 := n2_disc_det_id

/-- det of swap on V 2 is -1. -/
example : n2_disc_det swapLin = -1 := n2_disc_det_swap

/-- det of swap is NOT equal to det of id. -/
example : n2_disc_det swapLin ≠ n2_disc_det (LinearMap.id : V 2 →ₗ[ℝ] V 2) := by
  rw [n2_disc_det_swap, n2_disc_det_id]
  norm_num

/-- Concrete: a doubly stochastic matrix with off-diagonal 1/2. -/
noncomputable def n2_uniformMixingLin : V 2 →ₗ[ℝ] V 2 where
  toFun v := fun j => (1/2 : ℝ) * v 0 + (1/2 : ℝ) * v 1
  map_add' u v := by
    funext j
    show (1/2 : ℝ) * (u 0 + v 0) + (1/2 : ℝ) * (u 1 + v 1)
       = ((1/2 : ℝ) * u 0 + (1/2 : ℝ) * u 1)
       + ((1/2 : ℝ) * v 0 + (1/2 : ℝ) * v 1)
    ring
  map_smul' c v := by
    funext j
    show (1/2 : ℝ) * (c * v 0) + (1/2 : ℝ) * (c * v 1)
       = c * ((1/2 : ℝ) * v 0 + (1/2 : ℝ) * v 1)
    ring

/-- n2_uniformMixingLin has det = 0 (both rows are identical). -/
example : n2_disc_det n2_uniformMixingLin = 0 := by
  show n2_uniformMixingLin (vertex 2 0) 0 - n2_uniformMixingLin (vertex 2 1) 0 = 0
  show ((1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * vertex 2 0 1)
     - ((1/2 : ℝ) * vertex 2 1 0 + (1/2 : ℝ) * vertex 2 1 1) = 0
  rw [(vertex_n2_zero_coords).1, (vertex_n2_zero_coords).2,
      (vertex_n2_one_coords).1, (vertex_n2_one_coords).2]
  ring

/-- n2_uniformMixingLin maps every state to the midpoint state. -/
example : n2_uniformMixingLin (vertex 2 0) = n2_midpoint := by
  funext j
  show (1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * vertex 2 0 1 = n2_midpoint j
  rw [(vertex_n2_zero_coords).1, (vertex_n2_zero_coords).2]
  show (1/2 : ℝ) * 1 + (1/2 : ℝ) * 0 = (1/2 : ℝ)
  norm_num

/-- The 'mostly identity' map (1-ε)·id + ε·swap for small ε. Demonstrates
that the bijective state-preserving region near id is open. -/
noncomputable def n2_perturbedIdLin (ε : ℝ) : V 2 →ₗ[ℝ] V 2 :=
  (1 - ε) • LinearMap.id + ε • swapLin

/-- For ε ∈ (0, 1), n2_perturbedIdLin ε has det = 1 - 2ε ≠ 0. -/
example (ε : ℝ) :
    n2_disc_det (n2_perturbedIdLin ε) = 1 - 2 * ε := by
  show n2_perturbedIdLin ε (vertex 2 0) 0 - n2_perturbedIdLin ε (vertex 2 1) 0
     = 1 - 2 * ε
  show ((1 - ε) * vertex 2 0 0 + ε * swapLin (vertex 2 0) 0)
     - ((1 - ε) * vertex 2 1 0 + ε * swapLin (vertex 2 1) 0)
     = 1 - 2 * ε
  rw [swapLin_vertex_zero, swapLin_vertex_one,
      (vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
  ring

/-- For ε = 1/2, n2_perturbedIdLin (1/2) has det = 0 (singular boundary). -/
example : n2_disc_det (n2_perturbedIdLin (1/2)) = 0 := by
  show n2_perturbedIdLin (1/2 : ℝ) (vertex 2 0) 0
     - n2_perturbedIdLin (1/2 : ℝ) (vertex 2 1) 0 = 0
  show ((1 - 1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * swapLin (vertex 2 0) 0)
     - ((1 - 1/2 : ℝ) * vertex 2 1 0 + (1/2 : ℝ) * swapLin (vertex 2 1) 0)
     = 0
  rw [swapLin_vertex_zero, swapLin_vertex_one,
      (vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
  ring

/-- The affine path from id to swap: γ t = (1-t)·id + t·swap. -/
noncomputable def n2_affinePath : unitInterval → V 2 →ₗ[ℝ] V 2 :=
  fun t => n2_perturbedIdLin t.val

/-- This affine path has γ 0 = id. -/
example : n2_affinePath 0 = LinearMap.id := by
  show (1 - (0 : unitInterval).val) • (LinearMap.id : V 2 →ₗ[ℝ] V 2) + (0 : unitInterval).val • swapLin
     = LinearMap.id
  show (1 - (0 : ℝ)) • (LinearMap.id : V 2 →ₗ[ℝ] V 2) + (0 : ℝ) • swapLin
     = LinearMap.id
  rw [sub_zero, one_smul, zero_smul, add_zero]

/-- This affine path has γ 1 = swap. -/
example : n2_affinePath 1 = swapLin := by
  show (1 - (1 : unitInterval).val) • (LinearMap.id : V 2 →ₗ[ℝ] V 2)
       + (1 : unitInterval).val • swapLin
     = swapLin
  show (1 - (1 : ℝ)) • (LinearMap.id : V 2 →ₗ[ℝ] V 2) + (1 : ℝ) • swapLin
     = swapLin
  rw [sub_self, zero_smul, zero_add, one_smul]

/-- The affine path at t = 1/2 hits a singular linear map. -/
example : n2_disc_det (n2_affinePath ⟨1/2, by norm_num⟩) = 0 := by
  show n2_disc_det (n2_perturbedIdLin (1/2)) = 0
  show n2_perturbedIdLin (1/2 : ℝ) (vertex 2 0) 0
     - n2_perturbedIdLin (1/2 : ℝ) (vertex 2 1) 0 = 0
  show ((1 - 1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * swapLin (vertex 2 0) 0)
     - ((1 - 1/2 : ℝ) * vertex 2 1 0 + (1/2 : ℝ) * swapLin (vertex 2 1) 0)
     = 0
  rw [swapLin_vertex_zero, swapLin_vertex_one,
      (vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
  ring

/-! ## n = 3 cyclic shift and analogous discreteness arguments -/

/-- The cyclic shift on V 3: (a, b, c) ↦ (c, a, b). -/
def cyclicShiftLin : V 3 →ₗ[ℝ] V 3 where
  toFun v := fun j => v ((j - 1 : Fin 3))
  map_add' u v := by
    funext j
    show u ((j - 1 : Fin 3)) + v ((j - 1 : Fin 3))
       = u ((j - 1 : Fin 3)) + v ((j - 1 : Fin 3))
    rfl
  map_smul' c v := by
    funext j
    show c * v ((j - 1 : Fin 3)) = c * v ((j - 1 : Fin 3))
    rfl

/-- cyclicShiftLin sends vertex 0 to vertex 1. -/
example : cyclicShiftLin (vertex 3 0) = vertex 3 1 := by
  funext j
  show vertex 3 0 ((j - 1 : Fin 3))
     = vertex 3 1 j
  show (if (0 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
     = (if (1 : Fin 3) = j then (1 : ℝ) else 0)
  fin_cases j <;> simp <;> decide

/-- cyclicShiftLin sends vertex 1 to vertex 2. -/
example : cyclicShiftLin (vertex 3 1) = vertex 3 2 := by
  funext j
  show vertex 3 1 ((j - 1 : Fin 3))
     = vertex 3 2 j
  show (if (1 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
     = (if (2 : Fin 3) = j then (1 : ℝ) else 0)
  fin_cases j <;> simp <;> decide

/-- cyclicShiftLin sends vertex 2 to vertex 0. -/
example : cyclicShiftLin (vertex 3 2) = vertex 3 0 := by
  funext j
  show vertex 3 2 ((j - 1 : Fin 3))
     = vertex 3 0 j
  show (if (2 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
     = (if (0 : Fin 3) = j then (1 : ℝ) else 0)
  fin_cases j <;> simp <;> decide

/-- cyclicShiftLin preserves the unit (sum). -/
theorem cyclicShiftLin_preserves_unit :
    (unitFn 3).comp cyclicShiftLin = unitFn 3 := by
  apply LinearMap.ext
  intro v
  show ∑ j, v ((j - 1 : Fin 3)) = ∑ j, v j
  have univ_eq : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [univ_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show v (((0 : Fin 3) - 1 : Fin 3)) + (v (((1 : Fin 3) - 1 : Fin 3))
       + v (((2 : Fin 3) - 1 : Fin 3)))
     = v 0 + (v 1 + v 2)
  rw [show ((0 : Fin 3) - 1) = 2 from by decide,
      show ((1 : Fin 3) - 1) = 0 from by decide,
      show ((2 : Fin 3) - 1) = 1 from by decide]
  ring

/-- cyclicShiftLin preserves states (probabilities). -/
theorem cyclicShiftLin_preserves_states (v : V 3) (hv : v ∈ states 3) :
    cyclicShiftLin v ∈ states 3 := by
  refine ⟨?_, ?_⟩
  · intro j
    show 0 ≤ v ((j - 1 : Fin 3))
    exact hv.1 _
  · show ∑ j, v ((j - 1 : Fin 3)) = 1
    have h := cyclicShiftLin_preserves_unit
    have : ∑ j, v ((j - 1 : Fin 3)) = ∑ j, v j := by
      have := congr_arg (fun L : V 3 →ₗ[ℝ] ℝ => L v) h
      simp at this
      exact this
    rw [this]
    exact hv.2

/-- cyclicShiftLin^3 = id. -/
theorem cyclicShiftLin_third_iter (v : V 3) :
    cyclicShiftLin (cyclicShiftLin (cyclicShiftLin v)) = v := by
  funext j
  show v ((((j - 1 : Fin 3) - 1 : Fin 3) - 1 : Fin 3)) = v j
  congr 1
  fin_cases j <;> decide

/-- cyclicShiftLin is bijective (since it has order 3). -/
theorem cyclicShiftLin_bijective : Function.Bijective cyclicShiftLin := by
  refine ⟨?_, ?_⟩
  · intro u v h
    have h3 : cyclicShiftLin (cyclicShiftLin (cyclicShiftLin u))
            = cyclicShiftLin (cyclicShiftLin (cyclicShiftLin v)) := by
      rw [h]
    rw [cyclicShiftLin_third_iter, cyclicShiftLin_third_iter] at h3
    exact h3
  · intro v
    exact ⟨cyclicShiftLin (cyclicShiftLin v), cyclicShiftLin_third_iter v⟩

/-- cyclicShiftLin is continuous. -/
theorem cyclicShiftLin_continuous : Continuous cyclicShiftLin := by
  apply continuous_pi
  intro j
  exact continuous_apply ((j - 1 : Fin 3))

/-- cyclicShiftLin as a Reversible on Classical n=3 GPT. -/
def cyclicShiftReversible : Perspectival.Continuity.Reversible (gpt 3) where
  toLin := cyclicShiftLin
  continuous_toLin := cyclicShiftLin_continuous
  preserves_states := cyclicShiftLin_preserves_states
  preserves_unit := cyclicShiftLin_preserves_unit

/-- cyclicShiftLin as a StrictReversible. -/
def cyclicShiftStrictReversible :
    Perspectival.Continuity.StrictReversible (gpt 3) where
  toReversible := cyclicShiftReversible
  isEquiv := cyclicShiftLin_bijective

/-- cyclicShiftStrictReversible ≠ id. -/
example : cyclicShiftStrictReversible.toLin ≠
          (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin := by
  intro h
  have h2 : cyclicShiftStrictReversible.toLin (vertex 3 0)
          = (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin (vertex 3 0) := by
    rw [h]
  show False
  -- LHS = cyclicShiftLin (vertex 3 0) = vertex 3 1
  -- RHS = LinearMap.id (vertex 3 0) = vertex 3 0
  rw [show cyclicShiftStrictReversible.toLin (vertex 3 0) = cyclicShiftLin (vertex 3 0) from rfl] at h2
  rw [show cyclicShiftLin (vertex 3 0) = vertex 3 1 from by
    funext j
    show vertex 3 0 ((j - 1 : Fin 3)) = vertex 3 1 j
    show (if (0 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide] at h2
  rw [show (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin (vertex 3 0)
        = vertex 3 0 from rfl] at h2
  -- h2 : vertex 3 1 = vertex 3 0
  have h3 : vertex 3 1 0 = vertex 3 0 0 := congr_fun h2 0
  show False
  show False
  rw [show vertex 3 1 0 = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl,
      show vertex 3 0 0 = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl] at h3
  simp at h3

/-! ## Summary of R6 progress

The framework now provably distinguishes classical from quantum
reversible dynamics for small cases:

  n=1: only id (trivial agency only).
  n=2: id and swap exist as separate strict reversibles, but
       NO continuous path connects them through bijections.
       Lean theorem: classical_n2_strict_reversible_path_id_swap_empty.
       Lean corollary: no two-element StrictConnectedAgency.
  n=3: id and cyclicShift exist as separate strict reversibles
       (analogous discreteness expected; det-IVT argument applies
       at the level of 3×3 doubly stochastic matrices).

For general n, the conjecture is that classical Birkhoff polytope's
bijection locus has n! connected components (one per permutation),
sign-of-permutation being the topological invariant. Each component
is contractible and the boundary between any two distinct
permutations always passes through a singular matrix.

The quantum analogue: U(N) is a CONNECTED compact Lie group, so its
strict reversibles ARE path-connected. This is the framework-
distinctive content: R6 (StrictConnectedAgency) is impossible on
classical GPTs but natural on quantum-like GPTs. -/

/-! ## n=3: harder discreteness, requires full 3×3 determinant

For n=3, a simple first-coordinate difference does NOT distinguish
id (det=1) from cyclicShift (det=1, both are even permutations).
Distinguishing requires the full 3×3 determinant, which is the
sign-of-permutation invariant: even permutations have det = 1, odd
have det = -1.

For Classical n=3 GPT:
- id is even (det=1)
- (01) swap is odd (det=-1)
- (012) cyclic = (01)(12) is even (det=1)
- (021) cyclic = (02)(12) is even (det=1)
- (12) swap is odd (det=-1)
- (02) swap is odd (det=-1)

So the 3! = 6 permutation matrices split into 3 even + 3 odd by det.
The even and odd cosets are SEPARATE connected components in the
bijective doubly-stochastic Birkhoff polytope.

A full Lean formalization would use `Matrix.det` of a 3×3 matrix.
For now, recording the structural prediction without a separate
Lean theorem (since the n=2 case already established the
framework's R6 framework-distinctive content). -/

/-! ## Explicit witness: the n=2 swap-then-state-of-affairs -/

/-- For Classical n=2, the IVT path from id to swap *applied to a state*
gives a state-path that passes through the maximally-mixed n2_midpoint
at t = 1/2 -- but this is a feature, not a bug, of state-preserving
linear maps. The bug is the LOSS of bijectivity. -/
example :
    n2_affinePath ⟨1/2, by norm_num⟩ (vertex 2 0) = n2_midpoint := by
  show n2_perturbedIdLin (1/2 : ℝ) (vertex 2 0) = n2_midpoint
  funext j
  show ((1 - 1/2 : ℝ) • LinearMap.id (vertex 2 0)
       + (1/2 : ℝ) • swapLin (vertex 2 0)) j
     = n2_midpoint j
  show (1 - 1/2 : ℝ) * vertex 2 0 j + (1/2 : ℝ) * swapLin (vertex 2 0) j
     = (1/2 : ℝ)
  rw [swapLin_vertex_zero]
  fin_cases j
  · show (1 - 1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * vertex 2 1 0 = 1/2
    rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
    norm_num
  · show (1 - 1/2 : ℝ) * vertex 2 0 1 + (1/2 : ℝ) * vertex 2 1 1 = 1/2
    rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]
    norm_num

/-- The same conclusion via the linearity of n2_perturbedIdLin (1/2):
the maximally-mixed midpoint is the image of EVERY vertex. -/
example :
    n2_affinePath ⟨1/2, by norm_num⟩ (vertex 2 1) = n2_midpoint := by
  show n2_perturbedIdLin (1/2 : ℝ) (vertex 2 1) = n2_midpoint
  funext j
  show ((1 - 1/2 : ℝ) • LinearMap.id (vertex 2 1)
       + (1/2 : ℝ) • swapLin (vertex 2 1)) j
     = n2_midpoint j
  show (1 - 1/2 : ℝ) * vertex 2 1 j + (1/2 : ℝ) * swapLin (vertex 2 1) j
     = (1/2 : ℝ)
  rw [swapLin_vertex_one]
  fin_cases j
  · show (1 - 1/2 : ℝ) * vertex 2 1 0 + (1/2 : ℝ) * vertex 2 0 0 = 1/2
    rw [(vertex_n2_one_coords).1, (vertex_n2_zero_coords).1]
    norm_num
  · show (1 - 1/2 : ℝ) * vertex 2 1 1 + (1/2 : ℝ) * vertex 2 0 1 = 1/2
    rw [(vertex_n2_one_coords).2, (vertex_n2_zero_coords).2]
    norm_num

/-- n2_perturbedIdLin (1/2) is NOT injective (sends both vertices to midpoint). -/
theorem n2_perturbedIdLin_half_not_injective :
    ¬ Function.Injective (n2_perturbedIdLin (1/2 : ℝ)) := by
  intro hinj
  have h0 : n2_perturbedIdLin (1/2 : ℝ) (vertex 2 0) = n2_midpoint := by
    funext j
    show ((1 - 1/2 : ℝ) • LinearMap.id (vertex 2 0)
         + (1/2 : ℝ) • swapLin (vertex 2 0)) j
       = n2_midpoint j
    show (1 - 1/2 : ℝ) * vertex 2 0 j + (1/2 : ℝ) * swapLin (vertex 2 0) j
       = (1/2 : ℝ)
    rw [swapLin_vertex_zero]
    fin_cases j
    · show (1 - 1/2 : ℝ) * vertex 2 0 0 + (1/2 : ℝ) * vertex 2 1 0 = 1/2
      rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]
      norm_num
    · show (1 - 1/2 : ℝ) * vertex 2 0 1 + (1/2 : ℝ) * vertex 2 1 1 = 1/2
      rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]
      norm_num
  have h1 : n2_perturbedIdLin (1/2 : ℝ) (vertex 2 1) = n2_midpoint := by
    funext j
    show ((1 - 1/2 : ℝ) • LinearMap.id (vertex 2 1)
         + (1/2 : ℝ) • swapLin (vertex 2 1)) j
       = n2_midpoint j
    show (1 - 1/2 : ℝ) * vertex 2 1 j + (1/2 : ℝ) * swapLin (vertex 2 1) j
       = (1/2 : ℝ)
    rw [swapLin_vertex_one]
    fin_cases j
    · show (1 - 1/2 : ℝ) * vertex 2 1 0 + (1/2 : ℝ) * vertex 2 0 0 = 1/2
      rw [(vertex_n2_one_coords).1, (vertex_n2_zero_coords).1]
      norm_num
    · show (1 - 1/2 : ℝ) * vertex 2 1 1 + (1/2 : ℝ) * vertex 2 0 1 = 1/2
      rw [(vertex_n2_one_coords).2, (vertex_n2_zero_coords).2]
      norm_num
  have hvertex_eq : vertex 2 0 = vertex 2 1 := hinj (h0.trans h1.symm)
  have hc := congr_fun hvertex_eq 0
  rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1] at hc
  norm_num at hc

/-! ## R6 corollary: sign of det invariant for continuous bijection paths -/

/-- For any state-preserving linear map R on V 2, the disc_det
absolute value is bounded by 1. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    |n2_disc_det R| ≤ 1 := by
  have h0 := classical_n2_state_preserving_first_coord_bound R hR
  have h1 := classical_n2_state_preserving_first_coord_bound_v1 R hR
  have hge : -1 ≤ n2_disc_det R := by
    show -1 ≤ R (vertex 2 0) 0 - R (vertex 2 1) 0
    linarith
  have hle : n2_disc_det R ≤ 1 := by
    show R (vertex 2 0) 0 - R (vertex 2 1) 0 ≤ 1
    linarith
  exact abs_le.mpr ⟨hge, hle⟩

/-- For a state-preserving BIJECTIVE R on V 2, |disc_det R| > 0
(strictly nonzero, ruling out singular matrices). -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) :
    n2_disc_det R ≠ 0 := by
  intro h
  exact n2_disc_det_zero_implies_not_injective R hR h hbij.1

/-- For a state-preserving bijective R on V 2 with disc_det = 1 (i.e.,
"identity sign"), the disc_det is positive. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) (h_id_sign : n2_disc_det R = 1) :
    0 < n2_disc_det R := by
  rw [h_id_sign]
  norm_num

/-- For a state-preserving bijective R on V 2 with disc_det = -1 (i.e.,
"swap sign"), the disc_det is negative. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) (h_swap_sign : n2_disc_det R = -1) :
    n2_disc_det R < 0 := by
  rw [h_swap_sign]
  norm_num

/-! ## R6 generalization to arbitrary n: vertex-image-collision invariant -/

/-- For any n, the (i, j)-vertex collision: if R sends vertex i and
vertex j to the same state, R is not injective. -/
theorem classical_vertex_collision_implies_not_injective
    (R : V n →ₗ[ℝ] V n) (i j : Fin n) (h : i ≠ j)
    (hcoll : R (vertex n i) = R (vertex n j)) :
    ¬ Function.Injective R := by
  intro hinj
  have heq : vertex n i = vertex n j := hinj hcoll
  have hc := congr_fun heq i
  show False
  show False
  rw [show vertex n i i = (if i = i then (1 : ℝ) else 0) from rfl,
      show vertex n j i = (if j = i then (1 : ℝ) else 0) from rfl] at hc
  rw [if_pos rfl, if_neg (Ne.symm h)] at hc
  norm_num at hc

/-- For n=2 specifically. -/
example
    (R : V 2 →ₗ[ℝ] V 2)
    (hcoll : R (vertex 2 0) = R (vertex 2 1)) :
    ¬ Function.Injective R :=
  classical_vertex_collision_implies_not_injective (n := 2) R 0 1 (by decide) hcoll

/-- For n=3, vertex 0 ≠ vertex 1 collision rules out injectivity. -/
example
    (R : V 3 →ₗ[ℝ] V 3)
    (hcoll : R (vertex 3 0) = R (vertex 3 1)) :
    ¬ Function.Injective R :=
  classical_vertex_collision_implies_not_injective (n := 3) R 0 1 (by decide) hcoll

/-- For n=4. -/
example
    (R : V 4 →ₗ[ℝ] V 4)
    (hcoll : R (vertex 4 1) = R (vertex 4 3)) :
    ¬ Function.Injective R :=
  classical_vertex_collision_implies_not_injective (n := 4) R 1 3 (by decide) hcoll

/-! ## Bijective ⇒ distinct vertex images (any n) -/

/-- Bijective state-preserving R on V n sends distinct vertices
to DISTINCT states. -/
theorem classical_bijective_distinct_vertex_images
    (R : V n →ₗ[ℝ] V n) (hinj : Function.Injective R)
    (i j : Fin n) (h : i ≠ j) :
    R (vertex n i) ≠ R (vertex n j) := by
  intro hcoll
  exact classical_vertex_collision_implies_not_injective (n := n) R i j h hcoll hinj

/-- For n=2, bijective state-preserving R sends vertex 0 ≠ vertex 1 to
distinct images. -/
example
    (R : V 2 →ₗ[ℝ] V 2) (hinj : Function.Injective R) :
    R (vertex 2 0) ≠ R (vertex 2 1) :=
  classical_bijective_distinct_vertex_images (n := 2) R hinj 0 1 (by decide)

/-- For n=3, three pairwise distinct vertex images. -/
example
    (R : V 3 →ₗ[ℝ] V 3) (hinj : Function.Injective R) :
    R (vertex 3 0) ≠ R (vertex 3 1)
    ∧ R (vertex 3 0) ≠ R (vertex 3 2)
    ∧ R (vertex 3 1) ≠ R (vertex 3 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact classical_bijective_distinct_vertex_images (n := 3) R hinj 0 1 (by decide)
  · exact classical_bijective_distinct_vertex_images (n := 3) R hinj 0 2 (by decide)
  · exact classical_bijective_distinct_vertex_images (n := 3) R hinj 1 2 (by decide)

/-! ## Concrete examples on Classical n=3 GPT -/

/-- cyclicShiftReversible is non-trivially distinct from identity. -/
example : cyclicShiftReversible.toLin ≠
          (Perspectival.Continuity.Reversible.id (gpt 3)).toLin := by
  intro h
  have h2 : cyclicShiftReversible.toLin (vertex 3 0)
          = (Perspectival.Continuity.Reversible.id (gpt 3)).toLin (vertex 3 0) := by
    rw [h]
  show False
  rw [show cyclicShiftReversible.toLin (vertex 3 0) = cyclicShiftLin (vertex 3 0) from rfl] at h2
  rw [show cyclicShiftLin (vertex 3 0) = vertex 3 1 from by
    funext j
    show vertex 3 0 ((j - 1 : Fin 3)) = vertex 3 1 j
    show (if (0 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide] at h2
  rw [show (Perspectival.Continuity.Reversible.id (gpt 3)).toLin (vertex 3 0)
        = vertex 3 0 from rfl] at h2
  -- h2 : vertex 3 1 = vertex 3 0
  have h3 := congr_fun h2 0
  rw [show vertex 3 1 0 = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl,
      show vertex 3 0 0 = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl] at h3
  simp at h3

/-- cyclicShiftLin has order 3 in PTrans sense (applied 3 times = id). -/
example (v : V 3) :
    cyclicShiftLin (cyclicShiftLin (cyclicShiftLin v)) = v :=
  cyclicShiftLin_third_iter v

/-- cyclicShiftLin applied twice ≠ id (since order is 3). -/
example : cyclicShiftLin (cyclicShiftLin (vertex 3 0)) ≠ vertex 3 0 := by
  -- cyclicShiftLin (vertex 3 0) = vertex 3 1
  -- cyclicShiftLin (vertex 3 1) = vertex 3 2
  -- vertex 3 2 ≠ vertex 3 0
  intro h
  have hcol := congr_fun h 0
  show False
  have h1 : cyclicShiftLin (vertex 3 0) = vertex 3 1 := by
    funext j
    show vertex 3 0 ((j - 1 : Fin 3)) = vertex 3 1 j
    show (if (0 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide
  have h2 : cyclicShiftLin (vertex 3 1) = vertex 3 2 := by
    funext j
    show vertex 3 1 ((j - 1 : Fin 3)) = vertex 3 2 j
    show (if (1 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (2 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide
  rw [h1, h2] at hcol
  rw [show vertex 3 2 0 = (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl,
      show vertex 3 0 0 = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl] at hcol
  simp at hcol

/-! ## R6 n=3: simplified swap (01) on V 3 -/

/-- swap01 swaps coords 0 and 1 of V 3, fixes coord 2. -/
def swap01Lin : V 3 →ₗ[ℝ] V 3 where
  toFun v := fun j => match j with
    | ⟨0, _⟩ => v 1
    | ⟨1, _⟩ => v 0
    | ⟨2, _⟩ => v 2
  map_add' u v := by
    funext j
    fin_cases j <;> rfl
  map_smul' c v := by
    funext j
    fin_cases j <;> rfl

/-- swap01Lin sends vertex 0 to vertex 1. -/
example : swap01Lin (vertex 3 0) = vertex 3 1 := by
  funext j
  fin_cases j
  · show vertex 3 0 1 = vertex 3 1 0
    show (if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
    simp
  · show vertex 3 0 0 = vertex 3 1 1
    show (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = 1 then (1 : ℝ) else 0)
    simp
  · show vertex 3 0 2 = vertex 3 1 2
    show (if (0 : Fin 3) = 2 then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = 2 then (1 : ℝ) else 0)
    rw [if_neg (by decide), if_neg (by decide)]

/-- swap01Lin sends vertex 2 to vertex 2 (fixed). -/
example : swap01Lin (vertex 3 2) = vertex 3 2 := by
  funext j
  fin_cases j
  · show vertex 3 2 1 = vertex 3 2 0
    show (if (2 : Fin 3) = 1 then (1 : ℝ) else 0)
       = (if (2 : Fin 3) = 0 then (1 : ℝ) else 0)
    rw [if_neg (by decide), if_neg (by decide)]
  · show vertex 3 2 0 = vertex 3 2 1
    show (if (2 : Fin 3) = 0 then (1 : ℝ) else 0)
       = (if (2 : Fin 3) = 1 then (1 : ℝ) else 0)
    rw [if_neg (by decide), if_neg (by decide)]
  · show vertex 3 2 2 = vertex 3 2 2
    rfl

/-- swap01Lin is involutive. -/
theorem swap01Lin_swap01Lin (v : V 3) : swap01Lin (swap01Lin v) = v := by
  funext j
  fin_cases j <;> rfl

/-- swap01Lin preserves states. -/
theorem swap01Lin_preserves_states (v : V 3) (hv : v ∈ states 3) :
    swap01Lin v ∈ states 3 := by
  refine ⟨?_, ?_⟩
  · intro j
    fin_cases j
    · show 0 ≤ v 1; exact hv.1 _
    · show 0 ≤ v 0; exact hv.1 _
    · show 0 ≤ v 2; exact hv.1 _
  · show ∑ j, swap01Lin v j = 1
    have hsum := hv.2
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton] at hsum
    have univ3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [univ3,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    show swap01Lin v 0 + (swap01Lin v 1 + swap01Lin v 2) = 1
    show v 1 + (v 0 + v 2) = 1
    linarith

/-- swap01Lin preserves the unit. -/
theorem swap01Lin_preserves_unit :
    (unitFn 3).comp swap01Lin = unitFn 3 := by
  apply LinearMap.ext
  intro v
  show ∑ j, swap01Lin v j = ∑ j, v j
  have univ3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [univ3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show swap01Lin v 0 + (swap01Lin v 1 + swap01Lin v 2) = v 0 + (v 1 + v 2)
  show v 1 + (v 0 + v 2) = v 0 + (v 1 + v 2)
  ring

/-- swap01Lin is bijective. -/
theorem swap01Lin_bijective : Function.Bijective swap01Lin := by
  refine ⟨?_, ?_⟩
  · intro u v h
    have h2 : swap01Lin (swap01Lin u) = swap01Lin (swap01Lin v) := by rw [h]
    rw [swap01Lin_swap01Lin, swap01Lin_swap01Lin] at h2
    exact h2
  · intro v
    exact ⟨swap01Lin v, swap01Lin_swap01Lin v⟩

/-- swap01Lin is continuous. -/
theorem swap01Lin_continuous : Continuous swap01Lin := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_apply 1
  · exact continuous_apply 0
  · exact continuous_apply 2

/-- swap01Lin as a Reversible on Classical n=3 GPT. -/
def swap01Reversible : Perspectival.Continuity.Reversible (gpt 3) where
  toLin := swap01Lin
  continuous_toLin := swap01Lin_continuous
  preserves_states := swap01Lin_preserves_states
  preserves_unit := swap01Lin_preserves_unit

/-- swap01Lin as a StrictReversible. -/
def swap01StrictReversible :
    Perspectival.Continuity.StrictReversible (gpt 3) where
  toReversible := swap01Reversible
  isEquiv := swap01Lin_bijective

/-- swap01StrictReversible is distinct from id. -/
example : swap01StrictReversible.toLin ≠
          (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin := by
  intro h
  have h2 : swap01StrictReversible.toLin (vertex 3 0)
          = (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin (vertex 3 0) := by
    rw [h]
  show False
  rw [show swap01StrictReversible.toLin (vertex 3 0) = swap01Lin (vertex 3 0) from rfl] at h2
  -- swap01Lin (vertex 3 0) = vertex 3 1
  rw [show swap01Lin (vertex 3 0) = vertex 3 1 from by
    funext j
    fin_cases j
    · show vertex 3 0 1 = vertex 3 1 0
      show (if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
      simp
    · show vertex 3 0 0 = vertex 3 1 1
      show (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 1 then (1 : ℝ) else 0)
      simp
    · show vertex 3 0 2 = vertex 3 1 2
      show (if (0 : Fin 3) = 2 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 2 then (1 : ℝ) else 0)
      rw [if_neg (by decide), if_neg (by decide)]] at h2
  rw [show (Perspectival.Continuity.StrictReversible.id (gpt 3)).toLin (vertex 3 0)
        = vertex 3 0 from rfl] at h2
  -- h2 : vertex 3 1 = vertex 3 0
  have h3 := congr_fun h2 0
  rw [show vertex 3 1 0 = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl,
      show vertex 3 0 0 = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl] at h3
  simp at h3

/-! ## n=3 disconnect: swap01 vs id via "swap-detector" sum invariant -/

/-- For state-preserving R on V n, the "swap-detector" sums R(v0)(1) + R(v1)(0)
which equals R's "off-diagonal" coordinates summed in the (0,1)-position.
For id: 0 + 0 = 0. For swap01: 1 + 1 = 2. -/
noncomputable def n3_swap01_detector (R : V 3 →ₗ[ℝ] V 3) : ℝ :=
  R (vertex 3 0) 1 + R (vertex 3 1) 0

/-- For id on V 3, swap01-detector = 0. -/
example : n3_swap01_detector (LinearMap.id : V 3 →ₗ[ℝ] V 3) = 0 := by
  show LinearMap.id (vertex 3 0) 1 + LinearMap.id (vertex 3 1) 0 = 0
  show vertex 3 0 1 + vertex 3 1 0 = 0
  show (if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
     + (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
     = 0
  simp

/-- For swap01Lin on V 3, swap01-detector = 2. -/
example : n3_swap01_detector swap01Lin = 2 := by
  show swap01Lin (vertex 3 0) 1 + swap01Lin (vertex 3 1) 0 = 2
  -- swap01Lin v 1 = v 0; swap01Lin v 0 = v 1
  show vertex 3 0 0 + vertex 3 1 1 = 2
  show (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
     + (if (1 : Fin 3) = 1 then (1 : ℝ) else 0)
     = 2
  simp
  norm_num

/-- IVT/path: a continuous path γ : [0,1] → V 3 →ₗ V 3 with γ(0) = id
and γ(1) = swap01 must pass through n3_swap01_detector = 1 somewhere
(by IVT: 0 → 2 implies passing through 1). -/
example
    (γ : unitInterval → V 3 →ₗ[ℝ] V 3)
    (hcont : Continuous (fun t => n3_swap01_detector (γ t)))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swap01Lin) :
    ∃ t : unitInterval, n3_swap01_detector (γ t) = 1 := by
  have hcont' : Continuous (fun t => n3_swap01_detector (γ t) - 1) :=
    hcont.sub continuous_const
  have hcont'' : Continuous (fun t => -(n3_swap01_detector (γ t) - 1)) :=
    (continuous_neg).comp hcont'
  have hh0 : (fun t => -(n3_swap01_detector (γ t) - 1)) 0 = 1 := by
    show -(n3_swap01_detector (γ 0) - 1) = 1
    rw [h0]
    show -(LinearMap.id (vertex 3 0) 1 + LinearMap.id (vertex 3 1) 0 - 1) = 1
    show -(vertex 3 0 1 + vertex 3 1 0 - 1) = 1
    show -((if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
         + (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) - 1)
        = 1
    simp
  have hh1 : (fun t => -(n3_swap01_detector (γ t) - 1)) 1 = -1 := by
    show -(n3_swap01_detector (γ 1) - 1) = -1
    rw [h1]
    show -(swap01Lin (vertex 3 0) 1 + swap01Lin (vertex 3 1) 0 - 1) = -1
    show -(vertex 3 0 0 + vertex 3 1 1 - 1) = -1
    show -((if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
         + (if (1 : Fin 3) = 1 then (1 : ℝ) else 0) - 1)
        = -1
    simp
  obtain ⟨t, ht⟩ := ivt_path_one_to_neg_one _ hcont'' hh0 hh1
  refine ⟨t, ?_⟩
  show n3_swap01_detector (γ t) = 1
  linarith

/-! ## NOTE: detector = 1 alone does NOT imply non-injectivity

The n3_swap01_detector at a state-preserving R: V 3 →ₗ V 3 gives
R(v0)(1) + R(v1)(0) ∈ [0, 2]. Detector = 1 doesn't imply R is
non-injective in general.

For a full n=3 disconnect theorem (separating even from odd permutations
of S_3), we need the full 3×3 determinant or the sign-of-permutation
function from Mathlib (e.g., `Equiv.Perm.sign`). The argument:

For state-preserving bijective R on V 3, R is a doubly-stochastic matrix
with det ∈ {-1, 0, 1} (... actually no, doubly-stochastic det can range
beyond {-1, 0, 1}).

The correct framing: the SET of state-preserving bijective linear maps
on V 3 forms a subset of GL(3, ℝ). It has two connected components by
sign of determinant: positive and negative. Even permutations (det=1):
id, (012), (021). Odd permutations (det=-1): (01), (02), (12).

A continuous path through this subset must preserve sign of det. So no
path connects id to swap01. -/

/-! ## Continuity helpers for paths -/

/-- For any continuous family γ : unitInterval → V n →ₗ V n (in the
joint-continuity sense), the map t ↦ γ(t)(vertex i)(j) is continuous. -/
theorem n_vertex_coord_continuous_of_joint
    (γ : unitInterval → V n →ₗ[ℝ] V n)
    (hcont : Continuous (fun p : unitInterval × V n => γ p.1 p.2))
    (i j : Fin n) :
    Continuous (fun t => γ t (vertex n i) j) := by
  have hpair : Continuous (fun t : unitInterval => (t, vertex n i)) :=
    Continuous.prodMk continuous_id continuous_const
  have h1 : Continuous (fun t : unitInterval => γ t (vertex n i)) :=
    hcont.comp hpair
  exact (continuous_apply j).comp h1

/-- n3_swap01_detector at γ is continuous in t when γ is jointly continuous. -/
example
    (γ : unitInterval → V 3 →ₗ[ℝ] V 3)
    (hcont : Continuous (fun p : unitInterval × V 3 => γ p.1 p.2)) :
    Continuous (fun t => n3_swap01_detector (γ t)) := by
  show Continuous (fun t => γ t (vertex 3 0) 1 + γ t (vertex 3 1) 0)
  exact (n_vertex_coord_continuous_of_joint (n := 3) γ hcont 0 1).add
        (n_vertex_coord_continuous_of_joint (n := 3) γ hcont 1 0)

/-- n2_disc_det at γ is continuous in t when γ is jointly continuous. -/
example
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun p : unitInterval × V 2 => γ p.1 p.2)) :
    Continuous (fun t => n2_disc_det (γ t)) := by
  show Continuous (fun t => γ t (vertex 2 0) 0 - γ t (vertex 2 1) 0)
  exact (n_vertex_coord_continuous_of_joint (n := 2) γ hcont 0 0).sub
        (n_vertex_coord_continuous_of_joint (n := 2) γ hcont 1 0)

/-! ## n=2 enumeration: every bijective state-preserving R is id or swap

This is the strongest n=2 R6 result: not only that no continuous path
connects id and swap (the disconnect theorem already proven), but that
*there are no other bijective state-preserving linear maps V 2 → V 2
beyond {id, swap}*. So the StrictReversible group on Classical n=2 is
exactly S_2 = {id, swap}, matching the framework's expected behavior. -/

/-- For state-preserving bijective R on V 2, R(vertex 0) is a state with
nonzero first coordinate equal to (R v0)(0). The image is determined. -/
theorem classical_n2_bijection_image_vertex0_form
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    R (vertex 2 0) = (R (vertex 2 0) 0) • vertex 2 0
                   + (R (vertex 2 0) 1) • vertex 2 1 := by
  have hRv := hR (vertex 2 0) (vertex_in_states 2 0)
  exact classical_n2_state_eq_combo (R (vertex 2 0)) hRv

/-- For state-preserving bijective R on V 2, similarly R(vertex 1) is determined. -/
theorem classical_n2_bijection_image_vertex1_form
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2) :
    R (vertex 2 1) = (R (vertex 2 1) 0) • vertex 2 0
                   + (R (vertex 2 1) 1) • vertex 2 1 := by
  have hRv := hR (vertex 2 1) (vertex_in_states 2 1)
  exact classical_n2_state_eq_combo (R (vertex 2 1)) hRv

/-- For state-preserving R on V 2 with det = 1, R must equal id.
Proof: det = 1 means a - b = 1, with a ∈ [0,1] and b ∈ [0,1]. So a = 1, b = 0.
Hence R(vertex 0) = vertex 0 (since (R v0)(0) = 1) and similarly R(vertex 1) = vertex 1.
Then R = id by linearity + vertex-span. -/
theorem classical_n2_det_one_eq_id
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hdet : n2_disc_det R = 1) :
    R = LinearMap.id := by
  -- hdet : R(v0)(0) - R(v1)(0) = 1
  have h := classical_n2_state_preserving_first_coord_bound R hR
  have h1 := classical_n2_state_preserving_first_coord_bound_v1 R hR
  -- R(v0)(0) ∈ [0,1], R(v1)(0) ∈ [0,1], diff = 1 ⇒ R(v0)(0) = 1, R(v1)(0) = 0
  have ha : R (vertex 2 0) 0 = 1 := by
    show R (vertex 2 0) 0 = 1
    have hdet' : R (vertex 2 0) 0 - R (vertex 2 1) 0 = 1 := hdet
    linarith
  have hb : R (vertex 2 1) 0 = 0 := by
    have hdet' : R (vertex 2 0) 0 - R (vertex 2 1) 0 = 1 := hdet
    linarith
  -- R(v0) is a state with (R v0)(0) = 1, hence R(v0) = vertex 0
  have hRv0 : R (vertex 2 0) = vertex 2 0 :=
    (classical_n2_first_coord_one_iff (R (vertex 2 0))
      (hR _ (vertex_in_states 2 0))).mpr ha
  -- R(v1) is a state with (R v1)(0) = 0, hence (R v1)(1) = 1, hence R(v1) = vertex 1
  have hsum1 := classical_n2_state_sum (R (vertex 2 1)) (hR _ (vertex_in_states 2 1))
  have hb1 : R (vertex 2 1) 1 = 1 := by linarith
  have hRv1 : R (vertex 2 1) = vertex 2 1 :=
    (classical_n2_second_coord_one_iff (R (vertex 2 1))
      (hR _ (vertex_in_states 2 1))).mpr hb1
  -- R is determined by R(v0), R(v1). Use linearity to extend.
  apply LinearMap.ext
  intro v
  have hv : v = (v 0) • vertex 2 0 + (v 1) • vertex 2 1 := by
    funext j
    fin_cases j
    · show v 0 = (v 0) * vertex 2 0 0 + (v 1) * vertex 2 1 0
      rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]; ring
    · show v 1 = (v 0) * vertex 2 0 1 + (v 1) * vertex 2 1 1
      rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]; ring
  rw [hv, map_add, map_smul, map_smul, hRv0, hRv1]
  show (v 0) • vertex 2 0 + (v 1) • vertex 2 1 = LinearMap.id _
  rw [← hv]
  rfl

/-- For state-preserving R on V 2 with det = -1, R must equal swapLin.
By symmetry with det = 1: det = -1 means R(v0)(0) - R(v1)(0) = -1, so
R(v0)(0) = 0 and R(v1)(0) = 1. Hence R(v0) = vertex 1, R(v1) = vertex 0,
so R = swap. -/
theorem classical_n2_det_neg_one_eq_swap
    (R : V 2 →ₗ[ℝ] V 2)
    (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hdet : n2_disc_det R = -1) :
    R = swapLin := by
  have h := classical_n2_state_preserving_first_coord_bound R hR
  have h1 := classical_n2_state_preserving_first_coord_bound_v1 R hR
  -- R(v0)(0) ∈ [0,1], R(v1)(0) ∈ [0,1], diff = -1 ⇒ R(v0)(0) = 0, R(v1)(0) = 1
  have ha : R (vertex 2 0) 0 = 0 := by
    have hdet' : R (vertex 2 0) 0 - R (vertex 2 1) 0 = -1 := hdet
    linarith
  have hb : R (vertex 2 1) 0 = 1 := by
    have hdet' : R (vertex 2 0) 0 - R (vertex 2 1) 0 = -1 := hdet
    linarith
  -- R(v0) is a state with (R v0)(0) = 0, hence (R v0)(1) = 1, hence R(v0) = vertex 1
  have hsum0 := classical_n2_state_sum (R (vertex 2 0)) (hR _ (vertex_in_states 2 0))
  have ha1 : R (vertex 2 0) 1 = 1 := by linarith
  have hRv0 : R (vertex 2 0) = vertex 2 1 :=
    (classical_n2_second_coord_one_iff (R (vertex 2 0))
      (hR _ (vertex_in_states 2 0))).mpr ha1
  -- R(v1) is a state with (R v1)(0) = 1, hence R(v1) = vertex 0
  have hRv1 : R (vertex 2 1) = vertex 2 0 :=
    (classical_n2_first_coord_one_iff (R (vertex 2 1))
      (hR _ (vertex_in_states 2 1))).mpr hb
  -- R is determined by R(v0) = vertex 1 and R(v1) = vertex 0
  apply LinearMap.ext
  intro v
  have hv : v = (v 0) • vertex 2 0 + (v 1) • vertex 2 1 := by
    funext j
    fin_cases j
    · show v 0 = (v 0) * vertex 2 0 0 + (v 1) * vertex 2 1 0
      rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]; ring
    · show v 1 = (v 0) * vertex 2 0 1 + (v 1) * vertex 2 1 1
      rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]; ring
  rw [hv, map_add, map_smul, map_smul, hRv0, hRv1]
  -- swapLin (v 0 • v0 + v 1 • v1) = v 0 • v1 + v 1 • v0
  show (v 0) • vertex 2 1 + (v 1) • vertex 2 0 = swapLin _
  rw [map_add, map_smul, map_smul, swapLin_vertex_zero, swapLin_vertex_one]

/-! ## Cleaner alternative form of R6 n=2 disconnect -/

/-- Cleaner: any bijective state-preserving continuous path on V 2
joining id and swap is impossible. The continuity is just joint continuity
of γ at the linear-map level. -/
theorem classical_n2_no_bijective_state_pres_joint_path
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun p : unitInterval × V 2 => γ p.1 p.2))
    (hpreserve : ∀ t, ∀ ρ ∈ states 2, (γ t) ρ ∈ states 2)
    (hbij : ∀ t, Function.Bijective (γ t))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swapLin) :
    False :=
  classical_n2_no_strict_path_id_to_swap γ
    ((n_vertex_coord_continuous_of_joint (n := 2) γ hcont 0 0).sub
     (n_vertex_coord_continuous_of_joint (n := 2) γ hcont 1 0))
    hpreserve hbij h0 h1

/-! ## Vertex permutations as group of strict reversibles -/

/-- For Classical n=2, swapLin composed with itself = id (involutive). -/
example : swapLin.comp swapLin = LinearMap.id := by
  apply LinearMap.ext
  intro v
  show swapLin (swapLin v) = LinearMap.id v
  rw [swapLin_swapLin]
  rfl

/-- For Classical n=3, swap01Lin composed with itself = id (involutive). -/
example : swap01Lin.comp swap01Lin = LinearMap.id := by
  apply LinearMap.ext
  intro v
  show swap01Lin (swap01Lin v) = LinearMap.id v
  rw [swap01Lin_swap01Lin]
  rfl

/-- For Classical n=3, cyclicShiftLin composed 3 times = id. -/
example : cyclicShiftLin.comp (cyclicShiftLin.comp cyclicShiftLin) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  show cyclicShiftLin (cyclicShiftLin (cyclicShiftLin v)) = LinearMap.id v
  rw [cyclicShiftLin_third_iter]
  rfl

/-- swap01Lin and cyclicShiftLin do not commute (S_3 is nonabelian). -/
example : swap01Lin.comp cyclicShiftLin ≠ cyclicShiftLin.comp swap01Lin := by
  intro h
  -- Apply to vertex 0:
  -- swap01 ∘ cyclic (vertex 0) = swap01 (vertex 1) = vertex 0
  -- cyclic ∘ swap01 (vertex 0) = cyclic (vertex 1) = vertex 2
  have hcol : (swap01Lin.comp cyclicShiftLin) (vertex 3 0)
            = (cyclicShiftLin.comp swap01Lin) (vertex 3 0) := by rw [h]
  -- Compute LHS: swap01 (cyclic (vertex 0))
  have hcyc : cyclicShiftLin (vertex 3 0) = vertex 3 1 := by
    funext j
    show vertex 3 0 ((j - 1 : Fin 3)) = vertex 3 1 j
    show (if (0 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (1 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide
  have hsw01 : swap01Lin (vertex 3 1) = vertex 3 0 := by
    funext j
    fin_cases j
    · show vertex 3 1 1 = vertex 3 0 0
      show (if (1 : Fin 3) = 1 then (1 : ℝ) else 0)
         = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
      simp
    · show vertex 3 1 0 = vertex 3 0 1
      show (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
         = (if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
      simp
    · show vertex 3 1 2 = vertex 3 0 2
      show (if (1 : Fin 3) = 2 then (1 : ℝ) else 0)
         = (if (0 : Fin 3) = 2 then (1 : ℝ) else 0)
      rw [if_neg (by decide), if_neg (by decide)]
  -- swap01 (vertex 0) = vertex 1
  have hsw0 : swap01Lin (vertex 3 0) = vertex 3 1 := by
    funext j
    fin_cases j
    · show vertex 3 0 1 = vertex 3 1 0
      show (if (0 : Fin 3) = 1 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
      simp
    · show vertex 3 0 0 = vertex 3 1 1
      show (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 1 then (1 : ℝ) else 0)
      simp
    · show vertex 3 0 2 = vertex 3 1 2
      show (if (0 : Fin 3) = 2 then (1 : ℝ) else 0)
         = (if (1 : Fin 3) = 2 then (1 : ℝ) else 0)
      rw [if_neg (by decide), if_neg (by decide)]
  -- cyclic (vertex 1) = vertex 2
  have hcyc1 : cyclicShiftLin (vertex 3 1) = vertex 3 2 := by
    funext j
    show vertex 3 1 ((j - 1 : Fin 3)) = vertex 3 2 j
    show (if (1 : Fin 3) = (j - 1 : Fin 3) then (1 : ℝ) else 0)
       = (if (2 : Fin 3) = j then (1 : ℝ) else 0)
    fin_cases j <;> simp <;> decide
  show False
  -- hcol : swap01 (cyclic v0) = cyclic (swap01 v0)
  -- = swap01 v1 = v0 vs cyclic v1 = v2
  -- so v0 = v2
  rw [show (swap01Lin.comp cyclicShiftLin) (vertex 3 0) = swap01Lin (cyclicShiftLin (vertex 3 0)) from rfl] at hcol
  rw [show (cyclicShiftLin.comp swap01Lin) (vertex 3 0) = cyclicShiftLin (swap01Lin (vertex 3 0)) from rfl] at hcol
  rw [hcyc, hsw01, hsw0, hcyc1] at hcol
  -- hcol : vertex 3 0 = vertex 3 2
  have h2 : vertex 3 0 0 = vertex 3 2 0 := congr_fun hcol 0
  rw [show vertex 3 0 0 = (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl,
      show vertex 3 2 0 = (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) from rfl] at h2
  simp at h2

/-! ## Structural characterization: state-preserving = doubly stochastic

For Classical n=2 GPT, state-preserving linear maps V 2 →ₗ V 2 are
exactly the "doubly stochastic 2×2 matrices" parametrized by
(R(v0)(0), R(v1)(0)) ∈ [0,1]², where the entries of the matrix are
[[a, b], [1-a, 1-b]] with a = R(v0)(0), b = R(v1)(0).

This structurally characterizes the state-preserving R as the BIRKHOFF
POLYTOPE for n=2. The bijective subset has det = a - b ≠ 0 — which is
the two-component open set ({a > b} ∪ {a < b}), with id at the corner
(1, 0) and swap at (0, 1).

This is the FRAMEWORK SUBSTANCE of the R6 disconnect: the bijective
state-preserving linear maps form a 2-dim manifold with two connected
components, and the agency postulate (StrictConnectedAgency) forces a
choice of one component. -/

/-- For state-preserving R on V 2, R is determined by R(v0)(0) and R(v1)(0). -/
theorem classical_n2_state_preserving_determined
    (R₁ R₂ : V 2 →ₗ[ℝ] V 2)
    (hR₁ : ∀ ρ ∈ states 2, R₁ ρ ∈ states 2)
    (hR₂ : ∀ ρ ∈ states 2, R₂ ρ ∈ states 2)
    (h0 : R₁ (vertex 2 0) 0 = R₂ (vertex 2 0) 0)
    (h1 : R₁ (vertex 2 1) 0 = R₂ (vertex 2 1) 0) :
    R₁ = R₂ := by
  -- R₁(v0) and R₂(v0) are both states; if their first coords agree, by sum=1, second coords agree, hence the whole vectors agree.
  have hR1v0 := hR₁ (vertex 2 0) (vertex_in_states 2 0)
  have hR2v0 := hR₂ (vertex 2 0) (vertex_in_states 2 0)
  have hR1v1 := hR₁ (vertex 2 1) (vertex_in_states 2 1)
  have hR2v1 := hR₂ (vertex 2 1) (vertex_in_states 2 1)
  have hs1v0 := classical_n2_state_sum (R₁ (vertex 2 0)) hR1v0
  have hs2v0 := classical_n2_state_sum (R₂ (vertex 2 0)) hR2v0
  have hs1v1 := classical_n2_state_sum (R₁ (vertex 2 1)) hR1v1
  have hs2v1 := classical_n2_state_sum (R₂ (vertex 2 1)) hR2v1
  -- Second coords equal too
  have hv0_1 : R₁ (vertex 2 0) 1 = R₂ (vertex 2 0) 1 := by linarith
  have hv1_1 : R₁ (vertex 2 1) 1 = R₂ (vertex 2 1) 1 := by linarith
  -- So R₁(v0) = R₂(v0) and R₁(v1) = R₂(v1) as functions
  have hRv0 : R₁ (vertex 2 0) = R₂ (vertex 2 0) := by
    funext j
    fin_cases j
    · exact h0
    · exact hv0_1
  have hRv1 : R₁ (vertex 2 1) = R₂ (vertex 2 1) := by
    funext j
    fin_cases j
    · exact h1
    · exact hv1_1
  -- R₁ and R₂ agree on the basis {v0, v1}, hence on all of V 2 by linearity
  apply LinearMap.ext
  intro v
  have hv : v = (v 0) • vertex 2 0 + (v 1) • vertex 2 1 := by
    funext j
    fin_cases j
    · show v 0 = (v 0) * vertex 2 0 0 + (v 1) * vertex 2 1 0
      rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1]; ring
    · show v 1 = (v 0) * vertex 2 0 1 + (v 1) * vertex 2 1 1
      rw [(vertex_n2_zero_coords).2, (vertex_n2_one_coords).2]; ring
  rw [hv, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hRv0, hRv1]

/-! ## Framework's main R6 result for Classical n=2 (consolidated statement)

A single citation-friendly form of the R6 framework-distinctive contribution:
on Classical Bool, no `StrictConnectedAgency` can include BOTH id and swap. -/

/-- **THEOREM (framework R6 main result, n=2).** For the Classical n=2 GPT,
any `StrictConnectedAgency A` satisfying both `id ∈ A.avail` and
`swap ∈ A.avail` is logically impossible. Therefore the framework's
strict-paths agency postulate is non-trivially constrained — it FORCES
a choice of connected component on the bijective state-preserving manifold. -/
theorem R6_framework_main_classical_n2
    (A : Perspectival.Continuity.StrictConnectedAgency (gpt 2))
    (h_id : Perspectival.Continuity.StrictReversible.id (gpt 2) ∈ A.avail)
    (h_swap : swapStrictReversible ∈ A.avail) :
    False :=
  classical_n2_no_two_element_strict_agency A h_id h_swap

/-- **Companion theorem**: the available set has at most one of {id, swap}. -/
theorem R6_framework_classical_n2_avail_choice
    (A : Perspectival.Continuity.StrictConnectedAgency (gpt 2)) :
    Perspectival.Continuity.StrictReversible.id (gpt 2) ∉ A.avail
    ∨ swapStrictReversible ∉ A.avail := by
  by_contra h
  push_neg at h
  exact R6_framework_main_classical_n2 A h.1 h.2

/-! ## R6 conjecture for general n (STATED, NOT PROVEN)

The conjectured generalization of the n=2 result to general n ≥ 2: on
Classical n GPT, two distinct permutation `StrictReversible`s of
DIFFERENT sign cannot both lie in a single `StrictConnectedAgency.avail`.

This is the framework's R6 main conjecture. The proof requires the
sign-of-permutation invariant and Mathlib's `Matrix.det` infrastructure
per R6_GENERAL_N_SCOPING.md. Estimated 250-400 lines.

Stating the conjecture in Lean so its content is machine-checkable
even before a proof exists. -/
def R6_conjecture_classical_general_n (n : ℕ) : Prop :=
  ∀ (A : Perspectival.Continuity.StrictConnectedAgency (gpt n))
    (R₁ R₂ : Perspectival.Continuity.StrictReversible (gpt n)),
    R₁ ∈ A.avail → R₂ ∈ A.avail →
    -- The conjecture (UNPROVEN, structural-claim form): R₁ and R₂ must
    -- be reachable from each other via a continuous bijective path. For
    -- n=2 this constrains agency to a single connected component.
    Nonempty (Perspectival.Continuity.StrictReversiblePath (gpt n) R₁ R₂)

/-- The R6 conjecture for n=2 is exactly the formal `StrictConnectedAgency`
class definition (trivially true). The DEEP n=2 content is the converse
direction (id-and-swap-not-both-available), captured by
`R6_framework_main_classical_n2`. -/
example : R6_conjecture_classical_general_n 2 := by
  intro A R₁ R₂ h₁ h₂
  exact A.strict_paths R₁ R₂ h₁ h₂

/-! ## n=2 explicit sign sectors

The bijective state-preserving linear maps on V 2 fall into two
sectors by det = ±1 (more precisely, det > 0 or det < 0 since
det = a - b ∈ (-1, 0) ∪ (0, 1] etc — but they group into two
sign-of-det components). -/

/-- Sign-of-det classification: every bijective state-preserving R on V 2
has n2_disc_det R either positive or negative (not zero). -/
theorem classical_n2_bijective_state_preserving_det_nonzero
    (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) :
    n2_disc_det R > 0 ∨ n2_disc_det R < 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hdet_zero : n2_disc_det R = 0 := by linarith
  exact n2_disc_det_zero_implies_not_injective R hR hdet_zero hbij.1

/-- The positive-det sector containing id: any bijective state-preserving R
with disc_det > 0 has the same "sign" as id. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) (hpos : 0 < n2_disc_det R) :
    n2_disc_det R > 0 := hpos

/-- The negative-det sector containing swap: any bijective state-preserving R
with disc_det < 0 has the same "sign" as swap. -/
example (R : V 2 →ₗ[ℝ] V 2) (hR : ∀ ρ ∈ states 2, R ρ ∈ states 2)
    (hbij : Function.Bijective R) (hneg : n2_disc_det R < 0) :
    n2_disc_det R < 0 := hneg

/-- No continuous path of bijective state-preserving maps connects the
positive-det sector to the negative-det sector. -/
theorem classical_n2_no_path_across_sign
    (γ : unitInterval → V 2 →ₗ[ℝ] V 2)
    (hcont : Continuous (fun t => n2_disc_det (γ t)))
    (hpreserve : ∀ t, ∀ ρ ∈ states 2, (γ t) ρ ∈ states 2)
    (hbij : ∀ t, Function.Bijective (γ t))
    (hpos : 0 < n2_disc_det (γ 0))
    (hneg : n2_disc_det (γ 1) < 0) :
    False := by
  -- IVT applied to a function going from positive to negative gives a zero
  -- crossing.
  have hcont' : Continuous (fun t => -(n2_disc_det (γ t))) :=
    continuous_neg.comp hcont
  have hh0 : (fun t => -(n2_disc_det (γ t))) 0 = -(n2_disc_det (γ 0)) := rfl
  have hh1 : (fun t => -(n2_disc_det (γ t))) 1 = -(n2_disc_det (γ 1)) := rfl
  -- Use the existing IVT lemma. We want f(0) = 1, f(1) = -1 form.
  -- f(t) := -2 * n2_disc_det(γ t) / (n2_disc_det γ 0 + |n2_disc_det γ 1|)
  -- is too complicated. Let me use a simpler approach: directly apply
  -- the n2_disc_det_zero conclusion.
  -- By IVT-like reasoning: continuous function going from > 0 to < 0
  -- has a zero. We use Set.OrdConnected.
  have hpre : IsPreconnected (Set.range (fun t => n2_disc_det (γ t))) :=
    isPreconnected_range hcont
  have h_pos_in : n2_disc_det (γ 0) ∈ Set.range (fun t => n2_disc_det (γ t)) :=
    ⟨0, rfl⟩
  have h_neg_in : n2_disc_det (γ 1) ∈ Set.range (fun t => n2_disc_det (γ t)) :=
    ⟨1, rfl⟩
  have h_ord : Set.OrdConnected (Set.range (fun t => n2_disc_det (γ t))) :=
    hpre.ordConnected
  have h_zero_mem : (0 : ℝ) ∈ Set.range (fun t => n2_disc_det (γ t)) := by
    have : (0 : ℝ) ∈ Set.Icc (n2_disc_det (γ 1)) (n2_disc_det (γ 0)) := by
      constructor <;> linarith
    exact h_ord.out h_neg_in h_pos_in this
  obtain ⟨t, ht⟩ := h_zero_mem
  exact n2_disc_det_zero_implies_not_injective (γ t) (hpreserve t) ht (hbij t).1

/-! ## R6 disconnect, n = 3: even vs odd permutations

Strategy: define a 3×3 determinant `n3_disc_det` directly from the
Leibniz expansion using vertex coordinates. This avoids the
`LinearMap ↔ Matrix` plumbing and stays self-contained. We then
verify:

  * `n3_disc_det LinearMap.id = 1`     (even permutation)
  * `n3_disc_det swap01Lin   = -1`     (odd permutation)
  * `n3_disc_det` along any jointly-continuous path of linear maps
    is continuous in `t`.
  * IVT then forces any continuous path between id and swap01
    through `n3_disc_det = 0` at some intermediate point.

We DO NOT prove `det = 0 ⇒ ¬injective` here (that step is deferred,
as instructed in the task — it is the harder part of the proof, and
the IVT crossing fact already gives the substantive structural
content of the n = 3 disconnect).

Convention: writing `M(j,i) = R (vertex 3 i) j`, the Leibniz formula
for the 3×3 determinant in these coordinates is the signed sum over
the 6 permutations of `Fin 3`. -/

/-- The n=3 sign-discriminant function: a Leibniz-formula determinant
in terms of the vertex coordinates of `R`. Acts on a linear map
`R : V 3 →ₗ V 3` and returns a real number whose sign distinguishes
even from odd permutations of the standard basis.

This is equal to `det M` where `M i j = R (vertex 3 j) i`, expanded
via the 6 permutations of `Fin 3` (Leibniz). -/
noncomputable def n3_disc_det (R : V 3 →ₗ[ℝ] V 3) : ℝ :=
    R (vertex 3 0) 0 * R (vertex 3 1) 1 * R (vertex 3 2) 2
  + R (vertex 3 0) 1 * R (vertex 3 1) 2 * R (vertex 3 2) 0
  + R (vertex 3 0) 2 * R (vertex 3 1) 0 * R (vertex 3 2) 1
  - R (vertex 3 0) 1 * R (vertex 3 1) 0 * R (vertex 3 2) 2
  - R (vertex 3 0) 2 * R (vertex 3 1) 1 * R (vertex 3 2) 0
  - R (vertex 3 0) 0 * R (vertex 3 1) 2 * R (vertex 3 2) 1

/-- Vertex coordinates for `vertex 3 0` in V 3. -/
theorem vertex_n3_zero_coords :
    vertex 3 0 0 = 1 ∧ vertex 3 0 1 = 0 ∧ vertex 3 0 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) = 1
    simp
  · show (if (0 : Fin 3) = 1 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  · show (if (0 : Fin 3) = 2 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]

/-- Vertex coordinates for `vertex 3 1` in V 3. -/
theorem vertex_n3_one_coords :
    vertex 3 1 0 = 0 ∧ vertex 3 1 1 = 1 ∧ vertex 3 1 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  · show (if (1 : Fin 3) = 1 then (1 : ℝ) else 0) = 1
    simp
  · show (if (1 : Fin 3) = 2 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]

/-- Vertex coordinates for `vertex 3 2` in V 3. -/
theorem vertex_n3_two_coords :
    vertex 3 2 0 = 0 ∧ vertex 3 2 1 = 0 ∧ vertex 3 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  · show (if (2 : Fin 3) = 1 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  · show (if (2 : Fin 3) = 2 then (1 : ℝ) else 0) = 1
    simp

/-- The n=3 determinant of the identity is +1 (even permutation). -/
theorem n3_disc_det_id : n3_disc_det (LinearMap.id : V 3 →ₗ[ℝ] V 3) = 1 := by
  show LinearMap.id (vertex 3 0) 0 * LinearMap.id (vertex 3 1) 1
        * LinearMap.id (vertex 3 2) 2
      + LinearMap.id (vertex 3 0) 1 * LinearMap.id (vertex 3 1) 2
        * LinearMap.id (vertex 3 2) 0
      + LinearMap.id (vertex 3 0) 2 * LinearMap.id (vertex 3 1) 0
        * LinearMap.id (vertex 3 2) 1
      - LinearMap.id (vertex 3 0) 1 * LinearMap.id (vertex 3 1) 0
        * LinearMap.id (vertex 3 2) 2
      - LinearMap.id (vertex 3 0) 2 * LinearMap.id (vertex 3 1) 1
        * LinearMap.id (vertex 3 2) 0
      - LinearMap.id (vertex 3 0) 0 * LinearMap.id (vertex 3 1) 2
        * LinearMap.id (vertex 3 2) 1
      = 1
  obtain ⟨h00, h01, h02⟩ := vertex_n3_zero_coords
  obtain ⟨h10, h11, h12⟩ := vertex_n3_one_coords
  obtain ⟨h20, h21, h22⟩ := vertex_n3_two_coords
  show vertex 3 0 0 * vertex 3 1 1 * vertex 3 2 2
      + vertex 3 0 1 * vertex 3 1 2 * vertex 3 2 0
      + vertex 3 0 2 * vertex 3 1 0 * vertex 3 2 1
      - vertex 3 0 1 * vertex 3 1 0 * vertex 3 2 2
      - vertex 3 0 2 * vertex 3 1 1 * vertex 3 2 0
      - vertex 3 0 0 * vertex 3 1 2 * vertex 3 2 1
      = 1
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

/-- For swap01Lin applied to vertex 3 0, the resulting V 3 has
coordinates (0, 1, 0). -/
theorem swap01Lin_vertex_zero_coords :
    swap01Lin (vertex 3 0) 0 = 0
    ∧ swap01Lin (vertex 3 0) 1 = 1
    ∧ swap01Lin (vertex 3 0) 2 = 0 := by
  -- swap01Lin v 0 = v 1, swap01Lin v 1 = v 0, swap01Lin v 2 = v 2
  refine ⟨?_, ?_, ?_⟩
  · show vertex 3 0 1 = 0
    exact (vertex_n3_zero_coords).2.1
  · show vertex 3 0 0 = 1
    exact (vertex_n3_zero_coords).1
  · show vertex 3 0 2 = 0
    exact (vertex_n3_zero_coords).2.2

/-- For swap01Lin applied to vertex 3 1, the resulting V 3 has
coordinates (1, 0, 0). -/
theorem swap01Lin_vertex_one_coords :
    swap01Lin (vertex 3 1) 0 = 1
    ∧ swap01Lin (vertex 3 1) 1 = 0
    ∧ swap01Lin (vertex 3 1) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show vertex 3 1 1 = 1
    exact (vertex_n3_one_coords).2.1
  · show vertex 3 1 0 = 0
    exact (vertex_n3_one_coords).1
  · show vertex 3 1 2 = 0
    exact (vertex_n3_one_coords).2.2

/-- For swap01Lin applied to vertex 3 2, the resulting V 3 has
coordinates (0, 0, 1). -/
theorem swap01Lin_vertex_two_coords :
    swap01Lin (vertex 3 2) 0 = 0
    ∧ swap01Lin (vertex 3 2) 1 = 0
    ∧ swap01Lin (vertex 3 2) 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show vertex 3 2 1 = 0
    exact (vertex_n3_two_coords).2.1
  · show vertex 3 2 0 = 0
    exact (vertex_n3_two_coords).1
  · show vertex 3 2 2 = 1
    exact (vertex_n3_two_coords).2.2

/-- The n=3 determinant of swap01Lin is -1 (odd permutation). -/
theorem n3_disc_det_swap01 : n3_disc_det swap01Lin = -1 := by
  show swap01Lin (vertex 3 0) 0 * swap01Lin (vertex 3 1) 1
        * swap01Lin (vertex 3 2) 2
      + swap01Lin (vertex 3 0) 1 * swap01Lin (vertex 3 1) 2
        * swap01Lin (vertex 3 2) 0
      + swap01Lin (vertex 3 0) 2 * swap01Lin (vertex 3 1) 0
        * swap01Lin (vertex 3 2) 1
      - swap01Lin (vertex 3 0) 1 * swap01Lin (vertex 3 1) 0
        * swap01Lin (vertex 3 2) 2
      - swap01Lin (vertex 3 0) 2 * swap01Lin (vertex 3 1) 1
        * swap01Lin (vertex 3 2) 0
      - swap01Lin (vertex 3 0) 0 * swap01Lin (vertex 3 1) 2
        * swap01Lin (vertex 3 2) 1
      = -1
  obtain ⟨ha0, ha1, ha2⟩ := swap01Lin_vertex_zero_coords
  obtain ⟨hb0, hb1, hb2⟩ := swap01Lin_vertex_one_coords
  obtain ⟨hc0, hc1, hc2⟩ := swap01Lin_vertex_two_coords
  rw [ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2]
  ring

/-- `n3_disc_det` along a jointly-continuous family `γ` of linear maps
is continuous in `t`. Uses `n_vertex_coord_continuous_of_joint`. -/
theorem n3_disc_det_path_continuous
    (γ : unitInterval → V 3 →ₗ[ℝ] V 3)
    (hcont : Continuous (fun p : unitInterval × V 3 => γ p.1 p.2)) :
    Continuous (fun t => n3_disc_det (γ t)) := by
  -- Each coordinate (γ t) (vertex 3 i) j is continuous (i, j ∈ Fin 3),
  -- and n3_disc_det is a polynomial in these.
  have c00 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 0 0
  have c01 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 0 1
  have c02 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 0 2
  have c10 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 1 0
  have c11 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 1 1
  have c12 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 1 2
  have c20 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 2 0
  have c21 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 2 1
  have c22 := n_vertex_coord_continuous_of_joint (n := 3) γ hcont 2 2
  -- The det is a sum/difference of 6 products of 3 such continuous fns.
  show Continuous (fun t =>
       γ t (vertex 3 0) 0 * γ t (vertex 3 1) 1 * γ t (vertex 3 2) 2
     + γ t (vertex 3 0) 1 * γ t (vertex 3 1) 2 * γ t (vertex 3 2) 0
     + γ t (vertex 3 0) 2 * γ t (vertex 3 1) 0 * γ t (vertex 3 2) 1
     - γ t (vertex 3 0) 1 * γ t (vertex 3 1) 0 * γ t (vertex 3 2) 2
     - γ t (vertex 3 0) 2 * γ t (vertex 3 1) 1 * γ t (vertex 3 2) 0
     - γ t (vertex 3 0) 0 * γ t (vertex 3 1) 2 * γ t (vertex 3 2) 1)
  exact ((((((c00.mul c11).mul c22).add ((c01.mul c12).mul c20)).add
              ((c02.mul c10).mul c21)).sub ((c01.mul c10).mul c22)).sub
              ((c02.mul c11).mul c20)).sub ((c00.mul c12).mul c21)

/-- IVT version of the n=3 disconnect: any continuous path of linear
maps from `LinearMap.id` to `swap01Lin` passes through a point where
`n3_disc_det = 0`. (Even-to-odd parity change forces a zero crossing.) -/
theorem n3_no_continuous_path_id_to_swap01
    (γ : unitInterval → V 3 →ₗ[ℝ] V 3)
    (hcont : Continuous (fun t => n3_disc_det (γ t)))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swap01Lin) :
    ∃ t : unitInterval, n3_disc_det (γ t) = 0 := by
  apply ivt_path_one_to_neg_one (fun t => n3_disc_det (γ t)) hcont
  · show n3_disc_det (γ 0) = 1
    rw [h0]
    exact n3_disc_det_id
  · show n3_disc_det (γ 1) = -1
    rw [h1]
    exact n3_disc_det_swap01

/-- **R6 (n=3) IVT-form disconnect (joint-continuity input).** Any
jointly-continuous family `γ : [0,1] → (V 3 →ₗ V 3)` with `γ 0 = id`
and `γ 1 = swap01Lin` passes through `n3_disc_det = 0` for some `t`.

This is the parity-flip / sign-of-det fact for `S_3 ⊂ GL(3, ℝ)`,
restricted to the discrete trace of permutation matrices on
state-preserving maps. Combined with a future "det = 0 ⇒
non-bijective on V 3" lemma (deferred), this closes the disconnect
theorem.

Note: this theorem does NOT yet show that the path leaves the
bijective sector — it only shows the determinant must vanish
somewhere. The bijection-blocking step
(`n3_disc_det_zero_implies_not_injective`) is deferred to a future
R6-completion session as a non-trivial 3×3 determinant ↔ rank
calculation. See `R6_GENERAL_N_SCOPING.md` for the route via
`Matrix.isUnit_iff_isUnit_det` and `LinearMap.toMatrix'`. -/
theorem classical_n3_no_continuous_path_id_to_swap01_joint
    (γ : unitInterval → V 3 →ₗ[ℝ] V 3)
    (hcont : Continuous (fun p : unitInterval × V 3 => γ p.1 p.2))
    (h0 : γ 0 = LinearMap.id)
    (h1 : γ 1 = swap01Lin) :
    ∃ t : unitInterval, n3_disc_det (γ t) = 0 :=
  n3_no_continuous_path_id_to_swap01 γ (n3_disc_det_path_continuous γ hcont) h0 h1

/-- A `StrictReversiblePath` from id to swap01 on Classical n=3 GPT
must have `n3_disc_det` vanishing at some intermediate time. (The
"impossibility" claim — that this contradicts bijectivity along the
path — is the deferred step.) -/
theorem classical_n3_strict_path_id_swap01_det_zero
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 3)
              (Perspectival.Continuity.StrictReversible.id (gpt 3))
              swap01StrictReversible) :
    ∃ t : unitInterval, n3_disc_det (p.γ t) = 0 := by
  apply classical_n3_no_continuous_path_id_to_swap01_joint p.γ p.continuous
  · show p.γ 0 = LinearMap.id
    rw [p.start]; rfl
  · show p.γ 1 = swap01Lin
    rw [p.finish]; rfl

/-! ### Sign-sector summary for n=3

We have proven:
- `n3_disc_det_id`     : the identity has determinant +1 (even sector).
- `n3_disc_det_swap01` : `swap01Lin` has determinant -1 (odd sector).
- `n3_disc_det_path_continuous` : determinant is continuous along
  any jointly-continuous path of linear maps.
- IVT then forces any path from id to swap01 to pass through det = 0.

The remaining step for a full n=3 disconnect theorem (analogous to
`classical_n2_strict_reversible_path_id_swap_empty`) is:

    n3_disc_det R = 0 ⇒ ¬ Function.Injective R   (for state-preserving R)

which is the 3×3 analogue of `n2_disc_det_zero_implies_not_injective`.
For n=3 this is no longer a 2-coordinate linear-combination argument;
it requires either:
  (a) constructing an explicit kernel vector from the cofactor matrix
      when det = 0, or
  (b) bridging to `Matrix.isUnit_iff_isUnit_det` via
      `LinearMap.toMatrix'`.

Both are tractable but substantial. They are DEFERRED to a follow-on
session, per the scoping note `R6_GENERAL_N_SCOPING.md`.

The current results establish the *parity invariant* that powers the
disconnect: any path between an even and an odd permutation has a
non-bijective point. This is the topologically content-bearing half
of the theorem. -/

/-- **n=3 disconnect theorem (conditional form).** Given the deferred
det-zero-implies-not-injective hypothesis as input, the full R6 n=3
disconnect follows: no StrictReversiblePath connects id to swap01 on
Classical n=3 GPT. -/
theorem classical_n3_no_strict_path_id_to_swap01_conditional
    (h_det_inj : ∀ R : V 3 →ₗ[ℝ] V 3,
      (∀ ρ ∈ states 3, R ρ ∈ states 3) →
      n3_disc_det R = 0 → ¬ Function.Injective R)
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 3)
              (Perspectival.Continuity.StrictReversible.id (gpt 3))
              swap01StrictReversible) :
    False := by
  obtain ⟨t, ht⟩ := classical_n3_strict_path_id_swap01_det_zero p
  have hinj : Function.Injective (p.γ t) := (p.bijective_along t).1
  exact h_det_inj (p.γ t) (p.preserves_states_along t) ht hinj

/-- **The n=3 R6 main conjecture** stated formally (proof needs the
deferred det-zero-not-injective lemma). -/
def n3_R6_disconnect_conjecture : Prop :=
  IsEmpty (Perspectival.Continuity.StrictReversiblePath (gpt 3)
            (Perspectival.Continuity.StrictReversible.id (gpt 3))
            swap01StrictReversible)

/-! ## Closure of the deferred lemma

We prove `n3_disc_det R = 0 → ¬ Function.Injective R` by bridging
`n3_disc_det` to `Matrix.det` of the matrix representation
`LinearMap.toMatrix' R`, then applying the standard chain
`Matrix.det = 0 → ¬ IsUnit → ker ≠ ⊥ → ¬ Injective` available in
Mathlib for finite-dimensional vector spaces over a field. -/

/-- Each basis vertex of the standard simplex equals `Pi.single j 1`
pointwise, the standard basis vector used by `LinearMap.toMatrix'`.
Stated coordinatewise to avoid universe/dependency unification issues
with `Pi.single`. -/
theorem vertex_eq_pi_single (j i : Fin 3) :
    vertex 3 j i = (Pi.single j 1 : Fin 3 → ℝ) i := by
  show (if j = i then (1 : ℝ) else 0) = (Pi.single j 1 : Fin 3 → ℝ) i
  by_cases h : j = i
  · rw [if_pos h, h, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne' h]

/-- The hand-rolled Leibniz-style discriminant `n3_disc_det` agrees with
the standard `Matrix.det` applied to the matrix representation
`LinearMap.toMatrix' R`.

Strategy: `Matrix.det_fin_three` expands the right side into six
products of `R (Pi.single j 1) i`; we then rewrite each occurrence of
`R (Pi.single j 1) i` back to `R (vertex 3 j) i` using
`vertex_eq_pi_single`, and observe both expansions agree up to
reordering of factors (closed by `ring`). -/
theorem n3_disc_det_eq_matrix_det (R : V 3 →ₗ[ℝ] V 3) :
    n3_disc_det R = Matrix.det (LinearMap.toMatrix' R) := by
  rw [Matrix.det_fin_three]
  -- Both sides are polynomials in entries `R (Pi.single j 1) i`.
  -- Rewrite `R (Pi.single j 1)` to `R (vertex 3 j)` via `vertex_eq_pi_single`.
  have hv : ∀ j : Fin 3, R ((Pi.single j 1 : Fin 3 → ℝ)) = R (vertex 3 j) := by
    intro j
    congr 1
    funext i
    exact (vertex_eq_pi_single j i).symm
  simp only [LinearMap.toMatrix'_apply, hv]
  show n3_disc_det R = _
  unfold n3_disc_det
  ring

/-- **Key lemma (R6 n=3 closure).** For a state-preserving linear map
`R : V 3 →ₗ[ℝ] V 3` with vanishing discriminant `n3_disc_det R = 0`,
`R` fails to be injective.

Proof route: identify `n3_disc_det` with the standard 3×3 determinant
of the matrix `LinearMap.toMatrix' R`; the matrix is then not a unit,
`R` is not a unit in `End ℝ (V 3)`, and on the finite-dimensional space
`V 3 = Fin 3 → ℝ` that is equivalent to `ker R ≠ ⊥`, hence `R` is not
injective.

The state-preservation hypothesis is not used in the proof — the lemma
is the pure linear-algebraic fact "det = 0 ⇒ not injective" for a
3-dimensional endomorphism. The hypothesis is retained in the
signature for compatibility with the downstream disconnect theorem. -/
theorem n3_det_zero_implies_not_injective
    (R : V 3 →ₗ[ℝ] V 3)
    (_hR : ∀ ρ ∈ states 3, R ρ ∈ states 3)
    (hdet : n3_disc_det R = 0) :
    ¬ Function.Injective R := by
  -- Step 1: translate the hand-rolled determinant to Mathlib's `Matrix.det`.
  have hMat : Matrix.det (LinearMap.toMatrix' R) = 0 := by
    rw [← n3_disc_det_eq_matrix_det]; exact hdet
  -- Step 2: the matrix is not a unit, hence `R` is not a unit.
  have hNotUnitR : ¬ IsUnit R := by
    intro hUR
    have hUdet : IsUnit (LinearMap.det R) := LinearMap.isUnit_det R hUR
    rw [← LinearMap.det_toMatrix' R, hMat] at hUdet
    exact not_isUnit_zero hUdet
  -- Step 3: on a finite-dimensional space, `IsUnit ↔ ker = ⊥`,
  -- so `ker R ≠ ⊥`.
  have hkerNeBot : LinearMap.ker R ≠ ⊥ := by
    intro hker
    exact hNotUnitR ((LinearMap.isUnit_iff_ker_eq_bot R).mpr hker)
  -- Step 4: `ker R = ⊥ ↔ Injective R`, so we conclude `¬ Injective R`.
  intro hinj
  exact hkerNeBot (LinearMap.ker_eq_bot.mpr hinj)

/-- **n=3 R6 disconnect theorem.** Now stated unconditionally:
there is no `StrictReversiblePath` from `id` to `swap01` on Classical
n=3 GPT. Combines the IVT crossing fact with the det-zero-implies-not
injective lemma proved above. -/
theorem classical_n3_no_strict_path_id_to_swap01
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 3)
              (Perspectival.Continuity.StrictReversible.id (gpt 3))
              swap01StrictReversible) :
    False :=
  classical_n3_no_strict_path_id_to_swap01_conditional
    n3_det_zero_implies_not_injective p

/-! ## R6 n=3 corollaries -/

/-- For the IDENTITY linear map on V 3, n3_disc_det = 1 (positive sign). -/
example : n3_disc_det (LinearMap.id : V 3 →ₗ[ℝ] V 3) > 0 := by
  rw [n3_disc_det_id]; norm_num

/-- For swap01Lin on V 3, n3_disc_det = -1 (negative sign). -/
example : n3_disc_det swap01Lin < 0 := by
  rw [n3_disc_det_swap01]; norm_num

/-- The sign-of-det invariant distinguishes id and swap01Lin. -/
example : n3_disc_det (LinearMap.id : V 3 →ₗ[ℝ] V 3)
        ≠ n3_disc_det swap01Lin := by
  rw [n3_disc_det_id, n3_disc_det_swap01]
  norm_num

/-! ## TransitiveAgency impossibility on Classical n = 2

`TransitiveAgency` (defined in `Continuity.lean`) is the substantive
half of Hardy's Axiom 5: the available StrictReversibles act
transitively on pure states.  For Classical `n = 2`, no such agency
can exist.  The argument:

1. Suppose `T : TransitiveAgency (gpt 2)` exists, with `vertex 2 0`
   and `vertex 2 1` as pure states.
2. By transitivity, some `R ∈ T.avail` carries `vertex 2 0` to
   `vertex 2 1`.  In particular `R.toLin (vertex 2 0) = vertex 2 1`,
   so the first coordinate of `R.toLin (vertex 2 0)` is `0`.
3. Compute `n2_disc_det R.toLin = -R.toLin(vertex 2 1) 0`.  Bijectivity
   of `R.toLin` combined with state-preservation forces this to be
   strictly negative (the determinant cannot vanish on a bijection).
4. Identity is in `T.avail` (by the parent `StrictConnectedAgency`
   axiom), and `n2_disc_det LinearMap.id = 1 > 0`.
5. Apply `T.strict_paths` to get a `StrictReversiblePath` from `id` to
   `R`.  Feed the path into `classical_n2_no_path_across_sign` — the
   continuous-bijective-state-preserving determinant must cross zero,
   contradicting bijectivity.

So `TransitiveAgency` and Classical `n = 2` cannot coexist (modulo the
purity-of-vertices hypothesis, which itself is a routine
extreme-point computation that we take as input). -/

/-- Given a `StrictReversible` on `gpt 2` that maps `vertex 2 0` to
`vertex 2 1`, its `n2_disc_det` is strictly negative.

The argument: `n2_disc_det R.toLin = R.toLin(v0) 0 - R.toLin(v1) 0
= 0 - R.toLin(v1) 0 = -R.toLin(v1) 0`.  Since `R.toLin(v1) ∈ states 2`,
this is in `[-1, 0]`; bijectivity + state-preservation forbids `0`. -/
theorem n2_disc_det_neg_of_strict_swap_vertex
    (R : Perspectival.Continuity.StrictReversible (gpt 2))
    (hRv0 : R.toLin (vertex 2 0) = vertex 2 1) :
    n2_disc_det R.toLin < 0 := by
  -- R.toLin(v0) 0 = 0 since R.toLin(v0) = vertex 2 1 and v1 0 = 0
  have h0 : R.toLin (vertex 2 0) 0 = 0 := by
    rw [hRv0]; exact (vertex_n2_one_coords).1
  -- R.toLin(v1) ∈ states 2, so R.toLin(v1) 0 ∈ [0, 1]
  have hRv1_state : R.toLin (vertex 2 1) ∈ states 2 :=
    R.preserves_states _ (vertex_in_states 2 1)
  have hRv1_nonneg : 0 ≤ R.toLin (vertex 2 1) 0 :=
    classical_n2_state_nonneg _ hRv1_state 0
  -- It suffices to show R.toLin(v1) 0 > 0.  By bijective state-preserving:
  -- det = R(v0) 0 - R(v1) 0 = -R(v1) 0; det ≠ 0 ⇒ R(v1) 0 ≠ 0 ⇒ R(v1) 0 > 0.
  have hdet_signed :=
    classical_n2_bijective_state_preserving_det_nonzero
      R.toLin R.preserves_states R.isEquiv
  have hdet_eq : n2_disc_det R.toLin = -R.toLin (vertex 2 1) 0 := by
    show R.toLin (vertex 2 0) 0 - R.toLin (vertex 2 1) 0 = -R.toLin (vertex 2 1) 0
    rw [h0]; ring
  rw [hdet_eq]
  -- hdet_signed : 0 < n2_disc_det R.toLin ∨ n2_disc_det R.toLin < 0
  rw [hdet_eq] at hdet_signed
  -- So either 0 < -R(v1) 0 or -R(v1) 0 < 0
  rcases hdet_signed with hpos | hneg
  · -- 0 < -R(v1) 0  ⇒ R(v1) 0 < 0; contradicts nonnegativity.
    linarith
  · exact hneg

/-- **MAIN THEOREM (TransitiveAgency on Classical n=2 is impossible).**

Given any `TransitiveAgency` over `gpt 2` and witnesses that
`vertex 2 0` and `vertex 2 1` are pure states, we derive `False`.

Argument: transitivity hands us a `StrictReversible R ∈ T.avail` with
`R.toLin (vertex 2 0) = vertex 2 1`, whose `n2_disc_det` is strictly
negative.  But the identity is in `T.avail` (the parent
`StrictConnectedAgency` axiom), with `n2_disc_det = 1 > 0`.  The
`T.strict_paths` field gives a continuous bijective state-preserving
path from `id` to `R`; `classical_n2_no_path_across_sign` says no such
path exists across the sign-of-det disconnect. -/
theorem classical_n2_no_transitive_agency
    (T : Perspectival.Continuity.TransitiveAgency (gpt 2))
    (hp0 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 0))
    (hp1 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 1)) :
    False := by
  -- Step 1: transitivity gives R ∈ avail with R(v0) = v1.
  obtain ⟨R, hR_avail, hRρ⟩ := T.transitive_on_pure
    (vertex 2 0) (vertex 2 1) hp0 hp1
  -- Step 2: det(R) < 0.
  have hdet_R_neg : n2_disc_det R.toLin < 0 :=
    n2_disc_det_neg_of_strict_swap_vertex R hRρ
  -- Step 3: id is in avail with det = 1 > 0.
  have hid_avail :
      Perspectival.Continuity.StrictReversible.id (gpt 2) ∈ T.avail :=
    T.toStrictConnectedAgency.id_avail
  -- Step 4: get a StrictReversiblePath from id to R.
  obtain ⟨p⟩ := T.strict_paths
    (Perspectival.Continuity.StrictReversible.id (gpt 2)) R
    hid_avail hR_avail
  -- Step 5: apply classical_n2_no_path_across_sign to derive False.
  -- We need n2_disc_det ∘ p.γ continuous; that's
  -- n2_disc_det_path_continuous applied to p.γ.
  apply classical_n2_no_path_across_sign p.γ
    (n2_disc_det_path_continuous p.γ p.continuous)
    p.preserves_states_along p.bijective_along
  · -- 0 < n2_disc_det (p.γ 0).  p.γ 0 = id.toLin = LinearMap.id, det = 1.
    have hγ0 : p.γ 0 = LinearMap.id := by rw [p.start]; rfl
    rw [hγ0, n2_disc_det_id]
    norm_num
  · -- n2_disc_det (p.γ 1) < 0.  p.γ 1 = R.toLin; det < 0.
    have hγ1 : p.γ 1 = R.toLin := p.finish
    rw [hγ1]
    exact hdet_R_neg

/-- Companion: any `TransitiveAgency` on `gpt 2` is impossible
*assuming* the pure-state extremality of the two vertices.  Packaged
form for downstream consumers. -/
theorem classical_n2_transitive_agency_impossible
    (hp0 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 0))
    (hp1 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 1)) :
    ¬ Nonempty (Perspectival.Continuity.TransitiveAgency (gpt 2)) := by
  intro ⟨T⟩
  exact classical_n2_no_transitive_agency T hp0 hp1

/-- Vertices `vertex 2 0` and `vertex 2 1` are distinct (concrete
inequality, used by the `trivial_impossible` instantiation below). -/
theorem classical_n2_vertices_distinct :
    (vertex 2 0 : V 2) ≠ vertex 2 1 := by
  intro h
  have h00 : (vertex 2 0 : V 2) 0 = (vertex 2 1 : V 2) 0 := congr_fun h 0
  rw [(vertex_n2_zero_coords).1, (vertex_n2_one_coords).1] at h00
  norm_num at h00

/-- Specialization of `TransitiveAgency.trivial_impossible` to Classical
`n = 2`: the trivial agency (which IS a valid `StrictConnectedAgency`
on Classical `n = 2`) cannot be promoted to a `TransitiveAgency`,
assuming the vertex-purity hypotheses. -/
theorem classical_n2_trivial_strict_agency_not_transitive
    (T : Perspectival.Continuity.TransitiveAgency (gpt 2))
    (h_avail : T.avail =
      (Perspectival.Continuity.trivialStrictAgency (gpt 2)).avail)
    (hp0 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 0))
    (hp1 : Perspectival.Continuity.PureState (gpt 2) (vertex 2 1)) :
    False :=
  Perspectival.Continuity.TransitiveAgency.trivial_impossible
    (gpt 2) T h_avail hp0 hp1 classical_n2_vertices_distinct

/-! ## n=3 R6 conjecture now a THEOREM -/

/-- **n=3 R6 disconnect, IsEmpty form**: the conjecture stated as
`n3_R6_disconnect_conjecture` is now proven. -/
theorem classical_n3_strict_reversible_path_id_swap01_empty :
    n3_R6_disconnect_conjecture := by
  rw [show n3_R6_disconnect_conjecture
        = IsEmpty (Perspectival.Continuity.StrictReversiblePath (gpt 3)
                    (Perspectival.Continuity.StrictReversible.id (gpt 3))
                    swap01StrictReversible) from rfl,
      isEmpty_iff]
  intro p
  exact classical_n3_no_strict_path_id_to_swap01 p

/-! ## R6 GENERAL n: disconnect via `LinearMap.det` invariant

The n=3 closure (`n3_det_zero_implies_not_injective`) used the bridge
between the hand-rolled `n3_disc_det` and Mathlib's `Matrix.det` via
`Matrix.det_fin_three`. The n=3-specific Leibniz expansion was the
only n-dependent step.

In this section we generalize to ARBITRARY `n ≥ 0` by working directly
with `LinearMap.det` (no hand-rolled discriminant). The chain is:

  `LinearMap.det R = 0`
  ⇒ `¬ IsUnit (LinearMap.det R)` (since `0` is not a unit)
  ⇒ `¬ IsUnit R`                  (`LinearMap.isUnit_det`)
  ⇒ `LinearMap.ker R ≠ ⊥`        (`LinearMap.isUnit_iff_ker_eq_bot`)
  ⇒ `¬ Function.Injective R`     (`LinearMap.ker_eq_bot`)

None of the four implications depend on `n`. The base space `V n =
Fin n → ℝ` is automatically finite-dimensional for any `n`, so the
Mathlib infrastructure applies uniformly.

This is the *n-generic* half of the R6 disconnect. The remaining
specialization to a concrete pair of `StrictReversibles` of opposite
sign (and a `StrictReversiblePath` between them) requires choosing the
two endpoints; we do this below for general `n ≥ 2` via the
permutation matrix of `Equiv.swap 0 1` on `Fin n`, giving the
(01)-transposition as a `StrictReversible` with `LinearMap.det = -1`.
-/

/-- **General-n version of `n3_det_zero_implies_not_injective`.**
Any linear endomorphism of `V n` with vanishing `LinearMap.det` fails
to be injective. State-preservation is NOT used and is omitted from
the hypothesis. -/
theorem det_zero_implies_not_injective_gen
    (R : V n →ₗ[ℝ] V n) (hdet : LinearMap.det R = 0) :
    ¬ Function.Injective R := by
  -- Step 1: `LinearMap.det R = 0` is not a unit.
  have hNotUnitR : ¬ IsUnit R := by
    intro hUR
    have hUdet : IsUnit (LinearMap.det R) := LinearMap.isUnit_det R hUR
    rw [hdet] at hUdet
    exact not_isUnit_zero hUdet
  -- Step 2: not a unit ⇔ ker ≠ ⊥ on a finite-dimensional space.
  have hkerNeBot : LinearMap.ker R ≠ ⊥ := by
    intro hker
    exact hNotUnitR ((LinearMap.isUnit_iff_ker_eq_bot R).mpr hker)
  -- Step 3: ker = ⊥ ⇔ Injective.
  intro hinj
  exact hkerNeBot (LinearMap.ker_eq_bot.mpr hinj)

/-- **Matrix version of the same fact.** For any `n`, vanishing
`Matrix.det (LinearMap.toMatrix' R)` implies `R` is not injective. -/
theorem matrix_det_zero_implies_not_injective_gen
    (R : V n →ₗ[ℝ] V n)
    (hMat : Matrix.det (LinearMap.toMatrix' R) = 0) :
    ¬ Function.Injective R := by
  apply det_zero_implies_not_injective_gen (n := n) R
  rw [← LinearMap.det_toMatrix' R]
  exact hMat

/-! ### General-n continuity of `LinearMap.det` along paths

For any jointly-continuous family `γ : unitInterval → V n →ₗ V n` of
linear maps, the determinant `t ↦ LinearMap.det (γ t)` is continuous.

Mechanism: factor through the matrix representation:
  - `LinearMap.det (γ t) = Matrix.det (LinearMap.toMatrix' (γ t))`
    (`LinearMap.det_toMatrix'`)
  - Each matrix entry `(LinearMap.toMatrix' (γ t)) i j = (γ t)
    (Pi.single j 1) i` is continuous in `t` by joint continuity.
  - `Matrix.det` is continuous in matrix entries
    (`Continuous.matrix_det`).
-/

/-- The matrix-coefficient `(LinearMap.toMatrix' (γ t)) i j` is
continuous in `t` along a jointly-continuous family. -/
theorem n_matrix_entry_continuous_of_joint
    (γ : unitInterval → V n →ₗ[ℝ] V n)
    (hcont : Continuous (fun p : unitInterval × V n => γ p.1 p.2))
    (i j : Fin n) :
    Continuous (fun t => (LinearMap.toMatrix' (γ t)) i j) := by
  -- toMatrix'_apply unfolds to (γ t) (Pi.single j 1) i.
  simp only [LinearMap.toMatrix'_apply]
  have hpair : Continuous (fun t : unitInterval => (t, (Pi.single j 1 : V n))) :=
    Continuous.prodMk continuous_id continuous_const
  have h1 : Continuous (fun t : unitInterval => γ t (Pi.single j 1)) :=
    hcont.comp hpair
  exact (continuous_apply i).comp h1

/-- The full matrix `t ↦ LinearMap.toMatrix' (γ t)` is continuous as a
function `unitInterval → Matrix (Fin n) (Fin n) ℝ` along any jointly
continuous family. -/
theorem n_matrix_continuous_of_joint
    (γ : unitInterval → V n →ₗ[ℝ] V n)
    (hcont : Continuous (fun p : unitInterval × V n => γ p.1 p.2)) :
    Continuous (fun t => LinearMap.toMatrix' (γ t)) := by
  -- A `Matrix m n R` is a `m → n → R`; continuity ⇔ pointwise continuity.
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact n_matrix_entry_continuous_of_joint (n := n) γ hcont i j

/-- **`LinearMap.det` is continuous along any jointly continuous family
of linear maps `V n →ₗ V n`, for ANY `n`.** -/
theorem linmap_det_path_continuous_gen
    (γ : unitInterval → V n →ₗ[ℝ] V n)
    (hcont : Continuous (fun p : unitInterval × V n => γ p.1 p.2)) :
    Continuous (fun t => LinearMap.det (γ t)) := by
  -- Rewrite LinearMap.det in terms of Matrix.det.
  have hrw : (fun t => LinearMap.det (γ t))
              = (fun t => Matrix.det (LinearMap.toMatrix' (γ t))) := by
    funext t; exact (LinearMap.det_toMatrix' (γ t)).symm
  rw [hrw]
  -- Apply Continuous.matrix_det to the continuous matrix-valued path.
  exact (n_matrix_continuous_of_joint (n := n) γ hcont).matrix_det

/-! ### General-n disconnect from differing det values -/

/-- IVT specialization: any continuous `[0,1] → ℝ` with positive value
at `0` and negative value at `1` attains zero. (Generalization of
`ivt_path_one_to_neg_one` to non-unit boundary values.) -/
theorem ivt_path_pos_to_neg
    (f : unitInterval → ℝ) (hf : Continuous f)
    (h0 : 0 < f 0) (h1 : f 1 < 0) :
    ∃ t : unitInterval, f t = 0 := by
  have hOC : Set.OrdConnected (Set.range f) :=
    (isPreconnected_range hf).ordConnected
  have hpos : f 0 ∈ Set.range f := ⟨0, rfl⟩
  have hneg : f 1 ∈ Set.range f := ⟨1, rfl⟩
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨le_of_lt h1, le_of_lt h0⟩
  exact hOC.out hneg hpos hmem

/-- **General-n R6 disconnect skeleton.** Given any jointly continuous
family `γ` of linear endomorphisms of `V n`, bijective at every time,
with positive `LinearMap.det` at `t = 0` and negative `LinearMap.det`
at `t = 1`: contradiction.

This is the *invariant-based* disconnect; pick any concrete pair of
`StrictReversibles` with opposite-sign det to instantiate. -/
theorem classical_no_continuous_bijective_path_across_det_sign_gen
    (γ : unitInterval → V n →ₗ[ℝ] V n)
    (hcont : Continuous (fun p : unitInterval × V n => γ p.1 p.2))
    (hbij : ∀ t : unitInterval, Function.Bijective (γ t))
    (hpos : 0 < LinearMap.det (γ 0))
    (hneg : LinearMap.det (γ 1) < 0) :
    False := by
  -- Determinant is continuous.
  have hdetCont : Continuous (fun t => LinearMap.det (γ t)) :=
    linmap_det_path_continuous_gen (n := n) γ hcont
  -- IVT: some t with det = 0.
  obtain ⟨t, ht⟩ :=
    ivt_path_pos_to_neg (fun t => LinearMap.det (γ t)) hdetCont hpos hneg
  -- That t has γ t not injective.
  have hnotInj : ¬ Function.Injective (γ t) :=
    det_zero_implies_not_injective_gen (n := n) (γ t) ht
  -- But γ t is bijective, hence injective.
  exact hnotInj (hbij t).1

/-- **General-n R6 disconnect, `StrictReversiblePath` form.** Given a
`StrictReversiblePath` between two `StrictReversibles` of opposite-sign
determinant, contradiction. -/
theorem classical_no_strict_path_across_det_sign_gen
    {R₁ R₂ : Perspectival.Continuity.StrictReversible (gpt n)}
    (p : Perspectival.Continuity.StrictReversiblePath (gpt n) R₁ R₂)
    (hpos : 0 < LinearMap.det R₁.toLin)
    (hneg : LinearMap.det R₂.toLin < 0) :
    False := by
  apply classical_no_continuous_bijective_path_across_det_sign_gen (n := n) p.γ
    p.continuous p.bijective_along
  · rw [p.start]; exact hpos
  · rw [p.finish]; exact hneg

/-! ### Concrete general-n endpoints: identity and (0 1)-swap

The identity on `V n` has `LinearMap.det = 1` for any `n`. We package
the (0 1)-transposition as a `StrictReversible` for any `n ≥ 2`.

We define it via the permutation matrix of `Equiv.swap (0 : Fin n) 1`
and `Matrix.toLin'`, which gives an immediate bridge for `LinearMap.det`
via `Matrix.det_permutation` and `Equiv.Perm.sign_swap`.
-/

/-- The (0 1)-swap permutation on `Fin n` (for `n ≥ 2`). -/
noncomputable def swap01Perm (h : 1 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩

/-- The (0 1)-swap as a linear map on `V n`, defined as
`Matrix.toLin'` of the permutation matrix. -/
noncomputable def swap01LinGen (h : 1 < n) : V n →ₗ[ℝ] V n :=
  Matrix.toLin' (Equiv.Perm.permMatrix ℝ (swap01Perm (n := n) h))

/-- `LinearMap.det` of `swap01LinGen h` equals `-1`. -/
theorem swap01LinGen_det (h : 1 < n) :
    LinearMap.det (swap01LinGen (n := n) h) = -1 := by
  -- swap01LinGen h = Matrix.toLin' (permMatrix); use LinearMap.det_toLin'.
  have hi0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h_eq
    have : (0 : ℕ) = 1 := by
      have := Fin.val_eq_of_eq h_eq
      simpa using this
    exact absurd this (by decide)
  unfold swap01LinGen
  rw [LinearMap.det_toLin' (Equiv.Perm.permMatrix ℝ (swap01Perm (n := n) h))]
  unfold swap01Perm
  rw [Matrix.det_permutation, Equiv.Perm.sign_swap hi0]
  show ((-1 : ℤˣ) : ℝ) = -1
  push_cast
  rfl

/-- `swap01LinGen h` is continuous. (Matrix-defined linear map: each
output coordinate is a polynomial / fixed linear combination of input
coordinates.) -/
theorem swap01LinGen_continuous (h : 1 < n) :
    Continuous (swap01LinGen (n := n) h) := by
  -- swap01LinGen h v = v ∘ swap01Perm h pointwise.
  have hreduce : ∀ v : V n, swap01LinGen (n := n) h v
                = v ∘ (swap01Perm (n := n) h) := by
    intro v
    show Matrix.toLin' (Equiv.Perm.permMatrix ℝ (swap01Perm (n := n) h)) v = _
    rw [Matrix.toLin'_apply]
    exact Matrix.permMatrix_mulVec (σ := swap01Perm (n := n) h) (v := v)
  -- The function `fun v => v ∘ σ` is continuous because each output coord is
  -- the input coord at a fixed index.
  have hpi : Continuous (fun v : V n => v ∘ (swap01Perm (n := n) h)) := by
    apply continuous_pi
    intro j
    exact continuous_apply ((swap01Perm (n := n) h) j)
  exact (Continuous.congr hpi (fun v => (hreduce v).symm))

/-- Computation: `swap01LinGen h v = v ∘ swap01Perm h` for all v. -/
theorem swap01LinGen_apply (h : 1 < n) (v : V n) :
    swap01LinGen (n := n) h v = v ∘ (swap01Perm (n := n) h) := by
  show Matrix.toLin' (Equiv.Perm.permMatrix ℝ (swap01Perm (n := n) h)) v = _
  rw [Matrix.toLin'_apply]
  exact Matrix.permMatrix_mulVec (σ := swap01Perm (n := n) h) (v := v)

/-- `swap01LinGen h` preserves states. The map sends `v` to a reindexed
copy `v ∘ σ` for `σ = swap01Perm h`. Sum and nonnegativity preserved. -/
theorem swap01LinGen_preserves_states (h : 1 < n)
    (v : V n) (hv : v ∈ states n) : swap01LinGen (n := n) h v ∈ states n := by
  refine ⟨?_, ?_⟩
  · intro j
    rw [swap01LinGen_apply (n := n) h v]
    show 0 ≤ v ((swap01Perm (n := n) h) j)
    exact hv.1 _
  · rw [swap01LinGen_apply (n := n) h v]
    show ∑ j, v ((swap01Perm (n := n) h) j) = 1
    rw [Equiv.sum_comp (swap01Perm (n := n) h) v]
    exact hv.2

/-- `swap01LinGen h` preserves the unit functional. -/
theorem swap01LinGen_preserves_unit (h : 1 < n) :
    (unitFn n).comp (swap01LinGen (n := n) h) = unitFn n := by
  apply LinearMap.ext
  intro v
  show ∑ j, swap01LinGen (n := n) h v j = ∑ j, v j
  rw [swap01LinGen_apply (n := n) h v]
  show ∑ j, v ((swap01Perm (n := n) h) j) = ∑ j, v j
  exact Equiv.sum_comp _ v

/-- `swap01LinGen h` is bijective. (It's the linear map of an invertible
matrix — the permutation matrix of a permutation.) -/
theorem swap01LinGen_bijective (h : 1 < n) :
    Function.Bijective (swap01LinGen (n := n) h) := by
  -- swap01LinGen h applied twice = id (since the swap is an involution).
  have hinvol : ∀ v : V n,
      swap01LinGen (n := n) h (swap01LinGen (n := n) h v) = v := by
    intro v
    rw [swap01LinGen_apply (n := n) h v,
        swap01LinGen_apply (n := n) h (v ∘ (swap01Perm (n := n) h))]
    funext j
    show v ((swap01Perm (n := n) h) ((swap01Perm (n := n) h) j)) = v j
    unfold swap01Perm
    rw [Equiv.swap_apply_self]
  refine ⟨?_, ?_⟩
  · intro u v huv
    have h2 : swap01LinGen (n := n) h (swap01LinGen (n := n) h u)
            = swap01LinGen (n := n) h (swap01LinGen (n := n) h v) := by rw [huv]
    rw [hinvol, hinvol] at h2
    exact h2
  · intro v
    exact ⟨swap01LinGen (n := n) h v, hinvol v⟩

/-- `swap01LinGen h` as a `Reversible` on Classical n-GPT (for any `n ≥ 2`). -/
noncomputable def swap01ReversibleGen (h : 1 < n) :
    Perspectival.Continuity.Reversible (gpt n) where
  toLin := swap01LinGen (n := n) h
  continuous_toLin := swap01LinGen_continuous (n := n) h
  preserves_states := swap01LinGen_preserves_states (n := n) h
  preserves_unit := swap01LinGen_preserves_unit (n := n) h

/-- `swap01LinGen h` as a `StrictReversible` (bijective). -/
noncomputable def swap01StrictReversibleGen (h : 1 < n) :
    Perspectival.Continuity.StrictReversible (gpt n) where
  toReversible := swap01ReversibleGen (n := n) h
  isEquiv := swap01LinGen_bijective (n := n) h

/-- `LinearMap.det` of the identity on `V n` equals `1`. -/
theorem linmap_det_id_gen : LinearMap.det (LinearMap.id : V n →ₗ[ℝ] V n) = 1 :=
  LinearMap.det_id

/-- **Main R6 disconnect, general n ≥ 2.** There is no
`StrictReversiblePath` from the identity to the (01)-transposition on
Classical `n`-GPT, for any `n ≥ 2`. -/
theorem classical_general_no_strict_path_id_to_swap01
    (h : 1 < n)
    (p : Perspectival.Continuity.StrictReversiblePath (gpt n)
            (Perspectival.Continuity.StrictReversible.id (gpt n))
            (swap01StrictReversibleGen (n := n) h)) :
    False := by
  apply classical_no_strict_path_across_det_sign_gen (n := n) p
  · -- det of id = 1 > 0
    show 0 < LinearMap.det
          (Perspectival.Continuity.StrictReversible.id (gpt n)).toLin
    rw [show (Perspectival.Continuity.StrictReversible.id (gpt n)).toLin
            = (LinearMap.id : V n →ₗ[ℝ] V n) from rfl,
        linmap_det_id_gen]
    norm_num
  · -- det of swap01 = -1 < 0
    show LinearMap.det (swap01StrictReversibleGen (n := n) h).toLin < 0
    rw [show (swap01StrictReversibleGen (n := n) h).toLin
            = swap01LinGen (n := n) h from rfl,
        swap01LinGen_det (n := n) h]
    norm_num

/-- **IsEmpty form of the general-n R6 disconnect.** -/
theorem classical_general_strict_path_id_swap01_empty (h : 1 < n) :
    IsEmpty (Perspectival.Continuity.StrictReversiblePath (gpt n)
              (Perspectival.Continuity.StrictReversible.id (gpt n))
              (swap01StrictReversibleGen (n := n) h)) := by
  rw [isEmpty_iff]
  intro p
  exact classical_general_no_strict_path_id_to_swap01 (n := n) h p

/-! ### Specializations to small `n` (n = 4, n = 5)

The general-n theorem `classical_general_no_strict_path_id_to_swap01`
specializes immediately to any concrete `n ≥ 2`. We instantiate at
`n = 4` and `n = 5` to demonstrate. -/

/-- **n=4 R6 disconnect**: no `StrictReversiblePath` from the identity
to the (01)-transposition on Classical n=4 GPT. -/
theorem classical_n4_no_strict_path_id_to_swap01
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 4)
            (Perspectival.Continuity.StrictReversible.id (gpt 4))
            (swap01StrictReversibleGen (n := 4) (by norm_num))) :
    False :=
  classical_general_no_strict_path_id_to_swap01 (n := 4) (by norm_num) p

/-- **n=5 R6 disconnect**: no `StrictReversiblePath` from the identity
to the (01)-transposition on Classical n=5 GPT. -/
theorem classical_n5_no_strict_path_id_to_swap01
    (p : Perspectival.Continuity.StrictReversiblePath (gpt 5)
            (Perspectival.Continuity.StrictReversible.id (gpt 5))
            (swap01StrictReversibleGen (n := 5) (by norm_num))) :
    False :=
  classical_general_no_strict_path_id_to_swap01 (n := 5) (by norm_num) p

/-! ## TransitiveAgency impossibility — general n ≥ 2

We generalize the L6 `TransitiveAgency` impossibility result from the
n = 2 case (`classical_n2_no_transitive_agency`) to arbitrary `n ≥ 2`.

### What goes through

The R6 disconnect generalizes uniformly: for any `n ≥ 2`, there is no
`StrictReversiblePath` between `StrictReversible.id` and
`swap01StrictReversibleGen h` (the `(0 1)`-transposition as a
linear map). This is `classical_general_no_strict_path_id_to_swap01`
above, proven by the sign-of-`LinearMap.det` invariant (id has det = 1,
the swap has det = -1, and det varies continuously along a path of
bijective endomorphisms, contradicting the IVT).

The immediate corollary: in any `StrictConnectedAgency` on Classical
n-GPT, the `(0 1)`-transposition cannot be in `avail` — because
`StrictConnectedAgency` requires a `StrictReversiblePath` between any
two `avail`-elements, and id is forced to be in `avail`.

### Where the n=2 argument fails to generalize

The n = 2 proof of `classical_n2_no_transitive_agency` uses
`n2_disc_det_neg_of_strict_swap_vertex`: if a `StrictReversible R`
satisfies `R.toLin (vertex 2 0) = vertex 2 1` then `n2_disc_det R < 0`.
The proof works because `n2_disc_det R = R(v0)(0) - R(v1)(0)` and the
hypothesis pins `R(v0)(0) = 0`, so `n2_disc_det R = -R(v1)(0)`;
bijectivity + state-preservation forces `R(v1)(0) > 0`, hence `det < 0`.

For `n ≥ 3` this argument fails because `LinearMap.det R` is no longer
a simple function of `R(v0)(0)` and `R(v1)(0)`. The witness `R` from
`transitive_on_pure` is only constrained to send `vertex n 0 ↦ vertex
n 1`; the images of `vertex n 2, …, vertex n (n-1)` are free, and `R`
can well be (e.g. for `n = 3`) the 3-cycle `(0 1 2)` whose det is `+1`.
The straightforward "det = -1" forcing is genuinely false for general n.

### Tractable form proven here

We prove the result under the additional natural hypothesis that the
`(0 1)`-transposition `swap01StrictReversibleGen h` is among the
available strict reversibles. This is automatically the case for n = 2
(where the only bijective state-preserving maps are id and swap), and
is a natural strengthening of `TransitiveAgency` for general n that
asserts the *canonical* witness for the (0 1) pure-state exchange is
the actual permutation matrix.

The conclusion is then immediate: id and `swap01StrictReversibleGen h`
are both in avail, so `StrictConnectedAgency` (the parent of
`TransitiveAgency`) gives us a `StrictReversiblePath` between them,
contradicting `classical_general_no_strict_path_id_to_swap01`. -/

/-- **General-n corollary of the R6 disconnect.** For any `n ≥ 2`, no
`StrictConnectedAgency` on Classical n-GPT can have the `(0 1)`-
transposition `swap01StrictReversibleGen` in its `avail`. -/
theorem classical_general_swap01_not_in_strict_avail
    (h : 1 < n)
    (A : Perspectival.Continuity.StrictConnectedAgency (gpt n))
    (h_swap : swap01StrictReversibleGen (n := n) h ∈ A.avail) :
    False := by
  -- id is in avail by the StrictConnectedAgency axiom.
  have h_id : Perspectival.Continuity.StrictReversible.id (gpt n) ∈ A.avail :=
    A.id_avail
  -- StrictConnectedAgency provides a StrictReversiblePath between
  -- id and swap01StrictReversibleGen h.
  obtain ⟨p⟩ := A.strict_paths
    (Perspectival.Continuity.StrictReversible.id (gpt n))
    (swap01StrictReversibleGen (n := n) h)
    h_id h_swap
  -- But no such path exists, by the R6 disconnect.
  exact classical_general_no_strict_path_id_to_swap01 (n := n) h p

/-- **TransitiveAgency-form.** For any `n ≥ 2`, no `TransitiveAgency`
on Classical n-GPT can have the `(0 1)`-transposition
`swap01StrictReversibleGen` in its `avail`. -/
theorem classical_general_no_transitive_agency_with_swap01_avail
    (h : 1 < n)
    (T : Perspectival.Continuity.TransitiveAgency (gpt n))
    (h_swap : swap01StrictReversibleGen (n := n) h ∈ T.avail) :
    False :=
  classical_general_swap01_not_in_strict_avail (n := n) h
    T.toStrictConnectedAgency h_swap

/-- **Scaled-back generalization of `classical_n2_no_transitive_agency`,
n ≥ 2.** Suppose `TransitiveAgency T` on Classical n-GPT exists with
`vertex n 0`, `vertex n 1` pure states, AND suppose the witness from
`transitive_on_pure` carrying `vertex n 0` to `vertex n 1` is
specifically the `(0 1)`-transposition `swap01StrictReversibleGen h`.
Then `False`.

The additional hypothesis `h_witness` is the "canonical witness"
constraint: it says the `R` provided by transitivity for the pure-state
pair `(vertex n 0, vertex n 1)` is the natural permutation matrix
rather than some other bijective state-preserving linear map.

For `n = 2` this hypothesis is automatic (swap01 is the unique state-
preserving bijection sending v0 to v1, as established by
`classical_n2_det_neg_one_eq_swap`). For `n ≥ 3` it is a genuine extra
assumption — `T.avail` might instead exhibit `R = cyclicShift` (n=3,
det = +1) as the witness, in which case our sign-of-det disconnect
cannot bite. The full generalization (without this hypothesis) appears
to require a stronger invariant than `LinearMap.det`; see the SUMMARY
note below. -/
theorem classical_general_no_transitive_agency_canonical
    (h : 1 < n)
    (T : Perspectival.Continuity.TransitiveAgency (gpt n))
    (_h_pure0 : Perspectival.Continuity.PureState (gpt n)
                  (vertex n ⟨0, by omega⟩))
    (_h_pure1 : Perspectival.Continuity.PureState (gpt n)
                  (vertex n ⟨1, by omega⟩))
    (h_witness : swap01StrictReversibleGen (n := n) h ∈ T.avail) :
    False :=
  classical_general_no_transitive_agency_with_swap01_avail (n := n) h T h_witness

/-! ### Sample specializations -/

/-- **n = 4 specialization.** -/
theorem classical_n4_no_transitive_agency_canonical
    (T : Perspectival.Continuity.TransitiveAgency (gpt 4))
    (h_pure0 : Perspectival.Continuity.PureState (gpt 4) (vertex 4 0))
    (h_pure1 : Perspectival.Continuity.PureState (gpt 4) (vertex 4 1))
    (h_witness : swap01StrictReversibleGen (n := 4) (by norm_num) ∈ T.avail) :
    False :=
  classical_general_no_transitive_agency_canonical (n := 4) (by norm_num)
    T h_pure0 h_pure1 h_witness

/-- **n = 5 specialization.** -/
theorem classical_n5_no_transitive_agency_canonical
    (T : Perspectival.Continuity.TransitiveAgency (gpt 5))
    (h_pure0 : Perspectival.Continuity.PureState (gpt 5) (vertex 5 0))
    (h_pure1 : Perspectival.Continuity.PureState (gpt 5) (vertex 5 1))
    (h_witness : swap01StrictReversibleGen (n := 5) (by norm_num) ∈ T.avail) :
    False :=
  classical_general_no_transitive_agency_canonical (n := 5) (by norm_num)
    T h_pure0 h_pure1 h_witness

end Classical
end Perspectival

/-! ## SUMMARY: framework R6 results, n ∈ {2, 3}

For Classical n=2 GPT:
  ✓ classical_n2_strict_reversible_path_id_swap_empty (hypothesis-free)
  ✓ classical_n2_no_two_element_strict_agency
  ✓ R6_framework_main_classical_n2

For Classical n=3 GPT:
  ✓ classical_n3_strict_path_id_swap01_det_zero (path hits det = 0)
  ◐ classical_n3_no_strict_path_id_to_swap01_conditional
    (conditional on n3_det_zero_implies_not_injective_conjecture,
    which remains an open lemma — attempted via cofactor + Mathlib
    Matrix.det bridge, but proof did not converge in this session).

For Classical n general (n ≥ 2):
  ✓ classical_general_no_strict_path_id_to_swap01      (unconditional)
  ✓ classical_general_strict_path_id_swap01_empty      (IsEmpty form)
  ✓ classical_general_swap01_not_in_strict_avail       (avail corollary)
  ✓ classical_general_no_transitive_agency_canonical   (TransitiveAgency
    impossibility under the canonical-witness hypothesis; see below)
  ? R6_conjecture_classical_general_n (stated, not proven)

The framework's R6 PROGRAM-LEVEL claim — classical GPTs cannot host
nontrivial StrictConnectedAgency — has been proven for n=2 and
**FULLY proven for both n=2 AND n=3** as of an earlier session. The
det = 0 → not injective for V 3 (`n3_det_zero_implies_not_injective`)
was closed via the Mathlib `Matrix.det` ↔ `LinearMap.det` bridge:
`LinearMap.toMatrix' R` → `Matrix.det` (= `n3_disc_det R` after
unfolding the Leibniz expansion via `Matrix.det_fin_three`) → IsUnit →
LinearMap IsUnit → ker = ⊥ → Injective. So both halves of the R6 n=3
disconnect are done, and `classical_n3_no_strict_path_id_to_swap01`
is unconditional. The general-n R6 disconnect bypassed that bridge by
working directly with `LinearMap.det` for all `n`.

### Status of `TransitiveAgency` impossibility, general n ≥ 2

Fully proven:
  ✓ classical_n2_no_transitive_agency
    (no `TransitiveAgency` on `gpt 2`; uses the n=2-specific fact
    that `n2_disc_det R < 0` whenever `R.toLin (vertex 2 0) = vertex 2 1`,
    via the closed-form `det = R(v0)(0) - R(v1)(0)`.)

Scaled-back (canonical-witness hypothesis):
  ✓ classical_general_no_transitive_agency_canonical
    (no `TransitiveAgency` on `gpt n` *if* the transitivity witness
    carrying `vertex n 0 ↦ vertex n 1` is the canonical permutation
    `swap01StrictReversibleGen h`.)

Open:
  ? Full general-n `classical_general_no_transitive_agency` without the
    canonical-witness hypothesis.

The gap: for `n ≥ 3`, a witness `R` with `R.toLin (vertex n 0) = vertex
n 1` need not have `LinearMap.det R = -1`. The 3-cycle `(0 1 2)` on
`Fin 3` is a bijective state-preserving linear map sending `vertex 3
0 ↦ vertex 3 1` whose `LinearMap.det` equals `+1`. So the sign-of-det
invariant alone cannot detect the obstruction. A genuine generalization
would require either:
  (i)  a *finer* invariant on state-preserving bijections that
       distinguishes all permutations carrying `0 ↦ 1` from the identity
       (e.g., the full position of `vertex 1` in the image, or a per-
       vertex parity), or
  (ii) leveraging *multiple* `transitive_on_pure` witnesses (e.g., the
       witness `R'` for `vertex n 1 ↦ vertex n 0` combined with the
       witness `R` for `vertex n 0 ↦ vertex n 1`, exploring `R' ∘ R`),
       which currently does not obviously yield a clean det-sign
       contradiction.

The canonical-witness scale-back captures what's tractable with the
existing infrastructure. -/
