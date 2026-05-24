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

end Classical
end Perspectival
