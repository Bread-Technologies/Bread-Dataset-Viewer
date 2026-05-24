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

end Classical
end Perspectival
