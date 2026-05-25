/-
Perspectival Physics — Qutrit GPT (complex-QM N = 3 signature)
==============================================================

The Qutrit GPT: the complex-QM 3-level system, sitting at Hardy's
signature `K = N² = 9` for `N = 3`.  Together with `Classical` (K=N=2),
`CircleGPT` (rebit, K=3 at N=2), and `QubitGPT` (qubit, K=4 at N=2),
this extends the Hardy K-trichotomy beyond `N = 2`:

  classical N=2  K = N         = 2     (line segment)
  rebit     N=2  K = N(N+1)/2 = 3     (unit disk; `CircleGPT`)
  qubit     N=2  K = N²        = 4     (Bloch ball; `QubitGPT`)
  qutrit    N=3  K = N²        = 9     (8-Bloch body lifted to ℝ⁹; THIS FILE)

The carrier is `V = Fin 9 → ℝ`, with the first 8 coordinates encoding
the Bloch vector (the components of the density matrix in the Gell-Mann
basis) and the 9th coordinate `ρ 8` encoding the trace (= 1 for
normalized states).

Strategy: pragmatic outer approximation.  The genuine qutrit state body
inside ℝ⁸ has a complicated boundary (a 7-dimensional submanifold of the
8-sphere with cusps and ridges, determined by the positive-semidefiniteness
of the density matrix).  Encoding it precisely requires the full
SU(3)/Gell-Mann algebra.  We instead use the *outer* 8-ball:

  states := { ρ : V | ρ 8 = 1 ∧ Σᵢ (ρ i)² ≤ 1 }    (closed 8-ball at ρ 8 = 1)

This is convex, contains the genuine qutrit state body, and gives the
correct Hardy dimension `K = 9`.  It is the qutrit analog of using the
Bloch ball in `QubitGPT`.  The "rotZ"-style coordinate rotations of the
8-ball remain symmetries of this outer set.

Status (this file):
  ✓ `qutritGPT : GPT (Fin 9 → ℝ)` constructed with full convexity and
    normalization proofs.
  ✓ `qutrit_hardy_K : Module.finrank ℝ (Fin 9 → ℝ) = 9` — the
    complex-QM Hardy signature `K = N² = 9` at `N = 3`.
  ✓ One rotation generator family `rotL3 : ℝ → V →ₗ[ℝ] V`,
    rotation in the (0, 1)-coordinate plane (the diagonal "λ3 phase"
    on the qutrit at the Bloch level).  Shown to be linear, continuous,
    state- and unit-preserving, bijective, with the standard
    composition law.
  ✓ `rotL3StrictReversible` packaging.

Deferred (the harder pieces):
  - The full set of 8 Gell-Mann-type generators (only one is defined
    here; adding 7 more is mechanical but tedious).
  - The SU(3) group product structure on these generators.
  - The genuine qutrit state body (a strict subset of the 8-ball with
    a complicated boundary determined by det(ρ) ≥ 0 conditions).  The
    outer-ball formulation here gives the correct K but is geometrically
    coarser than the actual qutrit Bloch body.
-/

import Perspectival.GPT
import Perspectival.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Perspectival
namespace QutritGPT

open Real

/-! ## Underlying vector space

The carrier `V = Fin 9 → ℝ`.  Indices 0..7 are the 8 Bloch-vector
components (in the Gell-Mann basis); index 8 is the trace/normalization
coordinate. -/

abbrev V := Fin 9 → ℝ

/-! ## The unit functional (trace projection) -/

/-- The unit functional `u(ρ) = ρ 8` (the trace coordinate). -/
def unitLin : V →ₗ[ℝ] ℝ where
  toFun ρ := ρ 8
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem unitLin_apply (ρ : V) : unitLin ρ = ρ 8 := rfl

/-! ## States: closed 8-ball lifted to ρ 8 = 1

The 8-dimensional ball is the outer approximation of the qutrit state
body.  The genuine state body is a strict (and irregular) subset, but
the ball already realises the correct Hardy dimension and is convex. -/

/-- Sum of squares of the 8 Bloch-vector coordinates. -/
def sqNorm (ρ : V) : ℝ :=
  ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 + ρ 3 ^ 2 +
  ρ 4 ^ 2 + ρ 5 ^ 2 + ρ 6 ^ 2 + ρ 7 ^ 2

/-- The state space: vectors with `ρ 8 = 1` and Bloch norm ≤ 1. -/
def states : Set V := { ρ : V | ρ 8 = 1 ∧ sqNorm ρ ≤ 1 }

theorem mem_states_iff (ρ : V) :
    ρ ∈ states ↔ ρ 8 = 1 ∧ sqNorm ρ ≤ 1 := Iff.rfl

/-- States are normalized: `unit ρ = 1`. -/
theorem unit_eq_one_on_states (ρ : V) (hρ : ρ ∈ states) : unitLin ρ = 1 := hρ.1

/-! ### Convexity of the 8-ball -/

/-- Jensen-style convexity of `u²` along a convex combination.  Used
componentwise in the proof that the 8-ball is convex. -/
private theorem sq_convex_step
    (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
  have key :
      a * u ^ 2 + b * v ^ 2 - (a * u + b * v) ^ 2 = a * b * (u - v) ^ 2 := by
    have hb_eq : b = 1 - a := by linarith
    rw [hb_eq]; ring
  have hnn : 0 ≤ a * b * (u - v) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  linarith

/-- Convexity of `sqNorm ≤ 1` along a convex combination. -/
private theorem sqNorm_convex
    (ρ₁ ρ₂ : V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h₁ : sqNorm ρ₁ ≤ 1) (h₂ : sqNorm ρ₂ ≤ 1) :
    (a * ρ₁ 0 + b * ρ₂ 0) ^ 2 + (a * ρ₁ 1 + b * ρ₂ 1) ^ 2 +
    (a * ρ₁ 2 + b * ρ₂ 2) ^ 2 + (a * ρ₁ 3 + b * ρ₂ 3) ^ 2 +
    (a * ρ₁ 4 + b * ρ₂ 4) ^ 2 + (a * ρ₁ 5 + b * ρ₂ 5) ^ 2 +
    (a * ρ₁ 6 + b * ρ₂ 6) ^ 2 + (a * ρ₁ 7 + b * ρ₂ 7) ^ 2 ≤ 1 := by
  have h0 := sq_convex_step a b (ρ₁ 0) (ρ₂ 0) ha hb hab
  have h1 := sq_convex_step a b (ρ₁ 1) (ρ₂ 1) ha hb hab
  have h2 := sq_convex_step a b (ρ₁ 2) (ρ₂ 2) ha hb hab
  have h3 := sq_convex_step a b (ρ₁ 3) (ρ₂ 3) ha hb hab
  have h4 := sq_convex_step a b (ρ₁ 4) (ρ₂ 4) ha hb hab
  have h5 := sq_convex_step a b (ρ₁ 5) (ρ₂ 5) ha hb hab
  have h6 := sq_convex_step a b (ρ₁ 6) (ρ₂ 6) ha hb hab
  have h7 := sq_convex_step a b (ρ₁ 7) (ρ₂ 7) ha hb hab
  have hsum :
      (a * ρ₁ 0 + b * ρ₂ 0) ^ 2 + (a * ρ₁ 1 + b * ρ₂ 1) ^ 2 +
      (a * ρ₁ 2 + b * ρ₂ 2) ^ 2 + (a * ρ₁ 3 + b * ρ₂ 3) ^ 2 +
      (a * ρ₁ 4 + b * ρ₂ 4) ^ 2 + (a * ρ₁ 5 + b * ρ₂ 5) ^ 2 +
      (a * ρ₁ 6 + b * ρ₂ 6) ^ 2 + (a * ρ₁ 7 + b * ρ₂ 7) ^ 2
        ≤ a * sqNorm ρ₁ + b * sqNorm ρ₂ := by
    unfold sqNorm
    nlinarith [h0, h1, h2, h3, h4, h5, h6, h7]
  have hle :
      a * sqNorm ρ₁ + b * sqNorm ρ₂ ≤ a + b := by
    have hA : a * sqNorm ρ₁ ≤ a * 1 := mul_le_mul_of_nonneg_left h₁ ha
    have hB : b * sqNorm ρ₂ ≤ b * 1 := mul_le_mul_of_nonneg_left h₂ hb
    linarith
  linarith [hsum.trans hle]

/-- `states` is convex. -/
theorem states_convex : Convex ℝ states := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · show a * ρ₁ 8 + b * ρ₂ 8 = 1
    rw [hρ₁.1, hρ₂.1]; linarith
  · show sqNorm (a • ρ₁ + b • ρ₂) ≤ 1
    -- a • ρ₁ + b • ρ₂ at coordinate i is (a * ρ₁ i + b * ρ₂ i).
    unfold sqNorm
    show (a * ρ₁ 0 + b * ρ₂ 0) ^ 2 + (a * ρ₁ 1 + b * ρ₂ 1) ^ 2 +
         (a * ρ₁ 2 + b * ρ₂ 2) ^ 2 + (a * ρ₁ 3 + b * ρ₂ 3) ^ 2 +
         (a * ρ₁ 4 + b * ρ₂ 4) ^ 2 + (a * ρ₁ 5 + b * ρ₂ 5) ^ 2 +
         (a * ρ₁ 6 + b * ρ₂ 6) ^ 2 + (a * ρ₁ 7 + b * ρ₂ 7) ^ 2 ≤ 1
    exact sqNorm_convex ρ₁ ρ₂ a b ha hb hab hρ₁.2 hρ₂.2

/-! ## Effects -/

/-- Valid effects: linear functionals `e : V →ₗ[ℝ] ℝ` with `0 ≤ e ρ ≤ 1`
for every state `ρ`. -/
def effects : Set (V →ₗ[ℝ] ℝ) :=
  { e | ∀ ρ ∈ states, 0 ≤ e ρ ∧ e ρ ≤ 1 }

/-- `effects` is convex. -/
theorem effects_convex : Convex ℝ effects := by
  intro e₁ he₁ e₂ he₂ a b ha hb hab ρ hρ
  refine ⟨?_, ?_⟩
  · show 0 ≤ a * e₁ ρ + b * e₂ ρ
    exact add_nonneg (mul_nonneg ha (he₁ ρ hρ).1) (mul_nonneg hb (he₂ ρ hρ).1)
  · show a * e₁ ρ + b * e₂ ρ ≤ 1
    have h1 : a * e₁ ρ ≤ a * 1 := mul_le_mul_of_nonneg_left (he₁ ρ hρ).2 ha
    have h2 : b * e₂ ρ ≤ b * 1 := mul_le_mul_of_nonneg_left (he₂ ρ hρ).2 hb
    linarith

/-- The unit functional is itself an effect. -/
theorem unit_in_effects : unitLin ∈ effects := by
  intro ρ hρ
  rw [unitLin_apply, hρ.1]
  exact ⟨by norm_num, le_refl _⟩

/-- Probabilities lie in `[0, 1]`. -/
theorem prob_in_unit_interval (e : V →ₗ[ℝ] ℝ) (he : e ∈ effects)
    (ρ : V) (hρ : ρ ∈ states) : 0 ≤ e ρ ∧ e ρ ≤ 1 :=
  he ρ hρ

/-! ## The Qutrit GPT -/

/-- The Qutrit GPT: the closed 8-ball lifted to `ρ 8 = 1`, with all
`[0,1]`-bounded linear functionals as effects. -/
def qutritGPT : Perspectival.GPT V where
  unit := unitLin
  states := states
  effects := effects
  states_convex := states_convex
  effects_convex := effects_convex
  states_normalized := unit_eq_one_on_states
  prob_in_unit_interval := prob_in_unit_interval
  unit_is_effect := unit_in_effects

/-! ## Hardy signature: `K = N² = 9`

This is the headline statement of this file: the qutrit carrier has
real dimension 9, matching the complex-QM Hardy signature `K = N² = 9`
for `N = 3`.  Together with `Classical` (N=2, K=2), `CircleGPT` (N=2,
K=3), and `QubitGPT` (N=2, K=4), it extends the Hardy K-trichotomy
beyond `N = 2`. -/

/-- **Hardy's `K = N²` for the qutrit.** The carrier space has real
dimension `9 = N² = 3²`, matching the complex-QM signature for
`N = 3`. -/
theorem qutrit_hardy_K : Module.finrank ℝ (Fin 9 → ℝ) = 9 := by
  simp [Module.finrank_fintype_fun_eq_card]

/-! ## A rotation generator: the λ3 phase rotation

At the qutrit level, the Gell-Mann matrix λ3 = diag(1, -1, 0) generates
a U(1) subgroup of SU(3).  The conjugation action on density matrices
restricts to a 2-dimensional rotation of the Bloch coordinates
(a₁, a₂) (the components of ρ along λ1 and λ2), fixing the remaining
six Bloch coordinates and the trace.

We encode this in coordinates `(ρ 0, ρ 1)` ↦ rotate, others fixed. -/

/-- Helper: a `Fin 9` index that is none of 0,1,2,3,4,5,6,7 must be 8. -/
private theorem fin9_is_eight (i : Fin 9)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3)
    (h4 : i ≠ 4) (h5 : i ≠ 5) (h6 : i ≠ 6) (h7 : i ≠ 7) : i = 8 := by
  fin_cases i <;>
    first | rfl
          | (exact absurd rfl h0) | (exact absurd rfl h1)
          | (exact absurd rfl h2) | (exact absurd rfl h3)
          | (exact absurd rfl h4) | (exact absurd rfl h5)
          | (exact absurd rfl h6) | (exact absurd rfl h7)

/-- `rotL3 θ : V →ₗ[ℝ] V` is rotation by angle θ in the (0, 1)-coord
plane, fixing coordinates 2..8.  This is the diagonal λ3-phase generator
acting on the Bloch picture. -/
noncomputable def rotL3 (θ : ℝ) : V →ₗ[ℝ] V where
  toFun ρ := fun i =>
    if i = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
    else if i = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
    else ρ i
  map_add' ρ σ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show (ρ 0 + σ 0) * Real.cos θ - (ρ 1 + σ 1) * Real.sin θ =
           (ρ 0 * Real.cos θ - ρ 1 * Real.sin θ) +
           (σ 0 * Real.cos θ - σ 1 * Real.sin θ)
      ring
    · by_cases h1 : i = 1
      · subst h1
        show (ρ 0 + σ 0) * Real.sin θ + (ρ 1 + σ 1) * Real.cos θ =
             (ρ 0 * Real.sin θ + ρ 1 * Real.cos θ) +
             (σ 0 * Real.sin θ + σ 1 * Real.cos θ)
        ring
      · -- i ≠ 0, i ≠ 1; both sides reduce to ρ i + σ i.
        rw [if_neg h0, if_neg h1]
        show ρ i + σ i = ((fun j : Fin 9 =>
          if j = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
          else if j = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
          else ρ j) +
          (fun j : Fin 9 =>
          if j = 0 then σ 0 * Real.cos θ - σ 1 * Real.sin θ
          else if j = 1 then σ 0 * Real.sin θ + σ 1 * Real.cos θ
          else σ j)) i
        rw [Pi.add_apply, if_neg h0, if_neg h1, if_neg h0, if_neg h1]
  map_smul' c ρ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show c * ρ 0 * Real.cos θ - c * ρ 1 * Real.sin θ =
           c • (ρ 0 * Real.cos θ - ρ 1 * Real.sin θ)
      show c * ρ 0 * Real.cos θ - c * ρ 1 * Real.sin θ =
           c * (ρ 0 * Real.cos θ - ρ 1 * Real.sin θ)
      ring
    · by_cases h1 : i = 1
      · subst h1
        show c * ρ 0 * Real.sin θ + c * ρ 1 * Real.cos θ =
             c • (ρ 0 * Real.sin θ + ρ 1 * Real.cos θ)
        show c * ρ 0 * Real.sin θ + c * ρ 1 * Real.cos θ =
             c * (ρ 0 * Real.sin θ + ρ 1 * Real.cos θ)
        ring
      · rw [if_neg h0, if_neg h1]
        -- Goal: c • ρ i = (c • (fun j => ifte ...)) i
        show c • ρ i = (c • (fun j : Fin 9 =>
          if j = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
          else if j = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
          else ρ j)) i
        rw [Pi.smul_apply]
        rw [if_neg h0, if_neg h1]

@[simp] theorem rotL3_apply_zero (θ : ℝ) (ρ : V) :
    rotL3 θ ρ 0 = ρ 0 * Real.cos θ - ρ 1 * Real.sin θ := rfl

@[simp] theorem rotL3_apply_one (θ : ℝ) (ρ : V) :
    rotL3 θ ρ 1 = ρ 0 * Real.sin θ + ρ 1 * Real.cos θ := rfl

theorem rotL3_apply_other (θ : ℝ) (ρ : V) (i : Fin 9)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : rotL3 θ ρ i = ρ i := by
  show (if i = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
        else if i = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
        else ρ i) = ρ i
  rw [if_neg h0, if_neg h1]

@[simp] theorem rotL3_apply_two (θ : ℝ) (ρ : V) : rotL3 θ ρ 2 = ρ 2 :=
  rotL3_apply_other θ ρ 2 (by decide) (by decide)
@[simp] theorem rotL3_apply_three (θ : ℝ) (ρ : V) : rotL3 θ ρ 3 = ρ 3 :=
  rotL3_apply_other θ ρ 3 (by decide) (by decide)
@[simp] theorem rotL3_apply_four (θ : ℝ) (ρ : V) : rotL3 θ ρ 4 = ρ 4 :=
  rotL3_apply_other θ ρ 4 (by decide) (by decide)
@[simp] theorem rotL3_apply_five (θ : ℝ) (ρ : V) : rotL3 θ ρ 5 = ρ 5 :=
  rotL3_apply_other θ ρ 5 (by decide) (by decide)
@[simp] theorem rotL3_apply_six (θ : ℝ) (ρ : V) : rotL3 θ ρ 6 = ρ 6 :=
  rotL3_apply_other θ ρ 6 (by decide) (by decide)
@[simp] theorem rotL3_apply_seven (θ : ℝ) (ρ : V) : rotL3 θ ρ 7 = ρ 7 :=
  rotL3_apply_other θ ρ 7 (by decide) (by decide)
@[simp] theorem rotL3_apply_eight (θ : ℝ) (ρ : V) : rotL3 θ ρ 8 = ρ 8 :=
  rotL3_apply_other θ ρ 8 (by decide) (by decide)

/-- `rotL3 0 = id`. -/
theorem rotL3_zero : rotL3 0 = LinearMap.id := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0
    show ρ 0 * Real.cos 0 - ρ 1 * Real.sin 0 = ρ 0
    rw [Real.cos_zero, Real.sin_zero]; ring
  · by_cases h1 : i = 1
    · subst h1
      show ρ 0 * Real.sin 0 + ρ 1 * Real.cos 0 = ρ 1
      rw [Real.cos_zero, Real.sin_zero]; ring
    · rw [rotL3_apply_other 0 ρ i h0 h1]; rfl

/-- `rotL3 θ` preserves the (0,1)-norm squared. -/
theorem rotL3_preserves_01_norm (θ : ℝ) (ρ : V) :
    (rotL3 θ ρ) 0 ^ 2 + (rotL3 θ ρ) 1 ^ 2 = ρ 0 ^ 2 + ρ 1 ^ 2 := by
  rw [rotL3_apply_zero, rotL3_apply_one]
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  nlinarith [hc]

/-- `rotL3 θ` preserves the full Bloch norm (sqNorm). -/
theorem rotL3_preserves_sqNorm (θ : ℝ) (ρ : V) :
    sqNorm (rotL3 θ ρ) = sqNorm ρ := by
  unfold sqNorm
  have h01 := rotL3_preserves_01_norm θ ρ
  rw [rotL3_apply_two, rotL3_apply_three, rotL3_apply_four,
      rotL3_apply_five, rotL3_apply_six, rotL3_apply_seven]
  linarith [h01]

/-- `rotL3 θ` preserves the state space. -/
theorem rotL3_preserves_states (θ : ℝ) (ρ : V) (hρ : ρ ∈ states) :
    rotL3 θ ρ ∈ states := by
  refine ⟨?_, ?_⟩
  · rw [rotL3_apply_eight]; exact hρ.1
  · rw [rotL3_preserves_sqNorm]; exact hρ.2

/-- `rotL3 θ` preserves the unit functional. -/
theorem rotL3_preserves_unit (θ : ℝ) :
    unitLin.comp (rotL3 θ) = unitLin := by
  apply LinearMap.ext; intro ρ
  show (rotL3 θ ρ) 8 = ρ 8
  rfl

/-- `rotL3 θ` is continuous. -/
theorem rotL3_continuous (θ : ℝ) : Continuous (rotL3 θ) := by
  apply continuous_pi
  intro i
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun ρ : V => ρ 0 * Real.cos θ - ρ 1 * Real.sin θ)
    exact ((continuous_apply 0).mul continuous_const).sub
      ((continuous_apply 1).mul continuous_const)
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun ρ : V => ρ 0 * Real.sin θ + ρ 1 * Real.cos θ)
      exact ((continuous_apply 0).mul continuous_const).add
        ((continuous_apply 1).mul continuous_const)
    · -- Fixed coordinate: continuous_apply i.
      have h : (fun ρ : V => rotL3 θ ρ i) = fun ρ : V => ρ i := by
        funext ρ; exact rotL3_apply_other θ ρ i h0 h1
      rw [h]
      exact continuous_apply i

/-- Composition law: `rotL3 θ₁ ∘ rotL3 θ₂ = rotL3 (θ₁ + θ₂)`. -/
theorem rotL3_comp (θ₁ θ₂ : ℝ) :
    (rotL3 θ₁).comp (rotL3 θ₂) = rotL3 (θ₁ + θ₂) := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0
    show (rotL3 θ₁ (rotL3 θ₂ ρ)) 0 = (rotL3 (θ₁ + θ₂) ρ) 0
    rw [rotL3_apply_zero (θ := θ₁), rotL3_apply_zero (θ := θ₂),
        rotL3_apply_one (θ := θ₂), rotL3_apply_zero (θ := θ₁ + θ₂),
        Real.cos_add, Real.sin_add]
    ring
  · by_cases h1 : i = 1
    · subst h1
      show (rotL3 θ₁ (rotL3 θ₂ ρ)) 1 = (rotL3 (θ₁ + θ₂) ρ) 1
      rw [rotL3_apply_one (θ := θ₁), rotL3_apply_zero (θ := θ₂),
          rotL3_apply_one (θ := θ₂), rotL3_apply_one (θ := θ₁ + θ₂),
          Real.cos_add, Real.sin_add]
      ring
    · rw [rotL3_apply_other (θ₁ + θ₂) ρ i h0 h1]
      show (rotL3 θ₁ (rotL3 θ₂ ρ)) i = ρ i
      rw [rotL3_apply_other θ₁ (rotL3 θ₂ ρ) i h0 h1,
          rotL3_apply_other θ₂ ρ i h0 h1]

theorem rotL3_comp_neg (θ : ℝ) :
    (rotL3 θ).comp (rotL3 (-θ)) = LinearMap.id := by
  rw [rotL3_comp, add_neg_cancel, rotL3_zero]

theorem rotL3_neg_comp (θ : ℝ) :
    (rotL3 (-θ)).comp (rotL3 θ) = LinearMap.id := by
  rw [rotL3_comp, neg_add_cancel, rotL3_zero]

/-- `rotL3 θ` is bijective. -/
theorem rotL3_bijective (θ : ℝ) : Function.Bijective (rotL3 θ) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    have hv : rotL3 (-θ) (rotL3 θ v) = v := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotL3_neg_comp θ)
      simpa using h_eq
    have hw : rotL3 (-θ) (rotL3 θ w) = w := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f w) (rotL3_neg_comp θ)
      simpa using h_eq
    have h_app := congr_arg (rotL3 (-θ)) h
    rw [hv, hw] at h_app
    exact h_app
  · intro v
    refine ⟨rotL3 (-θ) v, ?_⟩
    have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotL3_comp_neg θ)
    simpa using h_eq

/-! ## Packaging as `Reversible` / `StrictReversible` -/

/-- `rotL3 θ` as a `Reversible qutritGPT`. -/
noncomputable def rotL3Reversible (θ : ℝ) :
    Perspectival.Continuity.Reversible qutritGPT where
  toLin := rotL3 θ
  continuous_toLin := rotL3_continuous θ
  preserves_states := rotL3_preserves_states θ
  preserves_unit := rotL3_preserves_unit θ

/-- `rotL3 θ` as a `StrictReversible qutritGPT`. -/
noncomputable def rotL3StrictReversible (θ : ℝ) :
    Perspectival.Continuity.StrictReversible qutritGPT where
  toReversible := rotL3Reversible θ
  isEquiv := rotL3_bijective θ

@[simp] theorem rotL3StrictReversible_toLin (θ : ℝ) :
    (rotL3StrictReversible θ).toLin = rotL3 θ := rfl

end QutritGPT
end Perspectival
