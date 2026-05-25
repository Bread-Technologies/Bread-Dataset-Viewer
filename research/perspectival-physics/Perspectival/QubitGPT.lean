/-
Perspectival Physics — Qubit GPT (Bloch ball, complex-QM N = 2 signature)
========================================================================

The Qubit GPT: the full complex-QM 2-level system encoded as the closed
unit Bloch ball lifted to `w = 1` in `ℝ⁴`.  Together with `CircleGPT`
(the rebit, `K = N(N+1)/2 = 3` at `N = 2`) and the classical 2-level
GPT (`K = N = 2`), this rounds out the framework's Hardy-signature
trichotomy:

  classical  K = N           = 2     (line segment)
  rebit      K = N(N+1)/2   = 3     (unit disk; `CircleGPT`)
  qubit      K = N²          = 4     (Bloch ball; THIS FILE)
  qQM        K = N(2N-1)    = 6     (quaternionic)

The carrier is `V = Fin 4 → ℝ`, with coordinates `(x, y, z, w)`.  The
`w` coordinate is the trace/2 (= 1 for normalized states).  Hardy's
signature `K = N² = 4` is realized as `Module.finrank ℝ V`.

Strategy: Option A from the qubit construction prompt — work in the
real 4-dimensional Bloch representation rather than the equivalent
complex Hermitian-matrix picture.  Avoids importing complex numbers
while preserving the geometry.

State space and effects:

  V := Fin 4 → ℝ                       (Bloch coordinates `(x, y, z, w)`)
  unit ρ := ρ 3                        (`w`-coordinate projection)
  states := { (x, y, z, 1) : x² + y² + z² ≤ 1 }   (closed Bloch ball at w = 1)
  effects := { e : V →ₗ[ℝ] ℝ | 0 ≤ e ρ ≤ 1 on states }
  pure states := { (x, y, z, 1) : x² + y² + z² = 1 }    (Bloch sphere)

Reversible transformations are rotations of the Bloch ball
(generators of SO(3) on the `(x, y, z)` subspace, fixing `w`):

  rotX θ : (x, y, z, w) ↦ (x, y cos θ - z sin θ, y sin θ + z cos θ, w)
  rotY θ : (x, y, z, w) ↦ (x cos θ + z sin θ, y, -x sin θ + z cos θ, w)
  rotZ θ : (x, y, z, w) ↦ (x cos θ - y sin θ, x sin θ + y cos θ, z, w)

Each of these is linear, continuous, state-preserving, unit-preserving,
and bijective (inverse is the rotation by `-θ`).  Composition of
generators (this file doesn't fully formalize the SO(3) group product,
but provides the three families and their basic properties) generates
all of SO(3).

Status (this file):
  ✓ `qubitGPT : GPT (Fin 4 → ℝ)` constructed with full convexity and
    normalization proofs.
  ✓ `qubit_hardy_K : Module.finrank ℝ (Fin 4 → ℝ) = 4` — the complex-QM
    Hardy signature `K = N² = 4` at `N = 2`.
  ✓ Three rotation families `rotX`, `rotY`, `rotZ`, each shown to be
    linear, continuous, state- and unit-preserving, and bijective.
  ✓ Each rotation packaged as a `Reversible` and `StrictReversible`.
  ✓ An affine-θ `StrictReversiblePath` between any two `rotZ`
    Reversibles (analogous to `CircleGPT`'s `rotStrictPath`).
  ✓ `qubitStrictConnectedAgency` populated with the `rotZ`-family as
    the avail set (the full SO(3) avail set is deferred; the program
    in this file already gives a non-degenerate continuous-symmetry
    instance, matching `CircleGPT`'s structure).
-/

import Perspectival.GPT
import Perspectival.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Perspectival
namespace QubitGPT

open Real

/-! ## Underlying vector space -/

/-- The carrier vector space `V = Fin 4 → ℝ`, with coordinates
`(x, y, z, w)` for the Bloch ball representation. -/
abbrev V := Fin 4 → ℝ

/-! ## The unit functional (`w`-coordinate projection) -/

/-- The unit functional `u(ρ) = ρ 3` (the `w`-coordinate). -/
def unitLin : V →ₗ[ℝ] ℝ where
  toFun ρ := ρ 3
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem unitLin_apply (ρ : V) : unitLin ρ = ρ 3 := rfl

/-! ## States: closed Bloch ball lifted to `w = 1` -/

/-- The state space: vectors `(x, y, z, 1)` with `x² + y² + z² ≤ 1`. -/
def states : Set V :=
  { ρ : V | ρ 3 = 1 ∧ ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 ≤ 1 }

theorem mem_states_iff (ρ : V) :
    ρ ∈ states ↔ ρ 3 = 1 ∧ ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 ≤ 1 := Iff.rfl

/-- States are normalized: `unit ρ = 1`. -/
theorem unit_eq_one_on_states (ρ : V) (hρ : ρ ∈ states) : unitLin ρ = 1 := hρ.1

/-! ### Convexity of the Bloch ball -/

/-- Convexity of `x² + y² + z²` along a convex combination: the square
of a weighted sum is at most the weighted sum of squares (Jensen). -/
private theorem sq3_convex
    (x₁ y₁ z₁ x₂ y₂ z₂ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2 ≤ 1)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2 ≤ 1) :
    (a * x₁ + b * x₂) ^ 2 + (a * y₁ + b * y₂) ^ 2 + (a * z₁ + b * z₂) ^ 2
      ≤ 1 := by
  have h_sq : ∀ u v : ℝ,
      (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
    intro u v
    have key :
        a * u ^ 2 + b * v ^ 2 - (a * u + b * v) ^ 2 = a * b * (u - v) ^ 2 := by
      have hb_eq : b = 1 - a := by linarith
      rw [hb_eq]; ring
    have hnn : 0 ≤ a * b * (u - v) ^ 2 :=
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    linarith
  have hx : (a * x₁ + b * x₂) ^ 2 ≤ a * x₁ ^ 2 + b * x₂ ^ 2 := h_sq x₁ x₂
  have hy : (a * y₁ + b * y₂) ^ 2 ≤ a * y₁ ^ 2 + b * y₂ ^ 2 := h_sq y₁ y₂
  have hz : (a * z₁ + b * z₂) ^ 2 ≤ a * z₁ ^ 2 + b * z₂ ^ 2 := h_sq z₁ z₂
  have hsum :
      (a * x₁ + b * x₂) ^ 2 + (a * y₁ + b * y₂) ^ 2 + (a * z₁ + b * z₂) ^ 2
        ≤ a * (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) + b * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
    nlinarith [hx, hy, hz]
  have h_le_aplusb :
      a * (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) + b * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) ≤ a + b := by
    have h1 : a * (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) ≤ a * 1 :=
      mul_le_mul_of_nonneg_left h₁ ha
    have h2 : b * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) ≤ b * 1 :=
      mul_le_mul_of_nonneg_left h₂ hb
    linarith
  linarith [hsum.trans h_le_aplusb]

/-- `states` is convex. -/
theorem states_convex : Convex ℝ states := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · show a * ρ₁ 3 + b * ρ₂ 3 = 1
    rw [hρ₁.1, hρ₂.1]; linarith
  · show (a * ρ₁ 0 + b * ρ₂ 0) ^ 2 + (a * ρ₁ 1 + b * ρ₂ 1) ^ 2
        + (a * ρ₁ 2 + b * ρ₂ 2) ^ 2 ≤ 1
    exact sq3_convex _ _ _ _ _ _ a b ha hb hab hρ₁.2 hρ₂.2

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

/-! ## The Qubit GPT -/

/-- The Qubit GPT: the closed Bloch ball lifted to `w = 1`, with all
`[0,1]`-bounded linear functionals as effects. -/
def qubitGPT : Perspectival.GPT V where
  unit := unitLin
  states := states
  effects := effects
  states_convex := states_convex
  effects_convex := effects_convex
  states_normalized := unit_eq_one_on_states
  prob_in_unit_interval := prob_in_unit_interval
  unit_is_effect := unit_in_effects

/-! ## Hardy signature: `K = N² = 4` -/

/-- **Hardy's `K = N²` for the qubit.** The carrier space has real
dimension `4 = N² = 2²`, matching the complex-QM signature for
`N = 2`. -/
theorem qubit_hardy_K : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
  simp [Module.finrank_fintype_fun_eq_card]

/-! ## Rotation generators: SO(3) on the Bloch ball

We define the three coordinate-axis rotations `rotX`, `rotY`, `rotZ`.
Each is a linear map `V → V` fixing the `w` coordinate.

Convention (right-handed):
  rotX θ : (y, z) ↦ (y cos θ - z sin θ, y sin θ + z cos θ)  (x fixed)
  rotY θ : (z, x) ↦ (z cos θ - x sin θ, z sin θ + x cos θ)  (y fixed)
              ↔ x ↦ x cos θ + z sin θ, z ↦ -x sin θ + z cos θ
  rotZ θ : (x, y) ↦ (x cos θ - y sin θ, x sin θ + y cos θ)  (z fixed)
-/

/-- A small helper: a Fin 4 index that is not 0, 1, or 2 must equal 3. -/
private theorem fin4_is_three (i : Fin 4) (h0 : i ≠ 0) (h1 : i ≠ 1)
    (h2 : i ≠ 2) : i = 3 := by
  fin_cases i <;>
    first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
          | (exact absurd rfl h2)

/-! ### Rotation around the x-axis -/

/-- `rotX θ : V →ₗ[ℝ] V` is rotation by angle θ around the x-axis. -/
noncomputable def rotX (θ : ℝ) : V →ₗ[ℝ] V where
  toFun ρ := fun i =>
    if i = 0 then ρ 0
    else if i = 1 then ρ 1 * Real.cos θ - ρ 2 * Real.sin θ
    else if i = 2 then ρ 1 * Real.sin θ + ρ 2 * Real.cos θ
    else ρ 3
  map_add' ρ σ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show ρ 0 + σ 0 = ρ 0 + σ 0
      rfl
    · by_cases h1 : i = 1
      · subst h1
        show (ρ 1 + σ 1) * Real.cos θ - (ρ 2 + σ 2) * Real.sin θ =
             (ρ 1 * Real.cos θ - ρ 2 * Real.sin θ) +
             (σ 1 * Real.cos θ - σ 2 * Real.sin θ)
        ring
      · by_cases h2 : i = 2
        · subst h2
          show (ρ 1 + σ 1) * Real.sin θ + (ρ 2 + σ 2) * Real.cos θ =
               (ρ 1 * Real.sin θ + ρ 2 * Real.cos θ) +
               (σ 1 * Real.sin θ + σ 2 * Real.cos θ)
          ring
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show ρ 3 + σ 3 = ρ 3 + σ 3
          rfl
  map_smul' c ρ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show c * ρ 0 = c • ρ 0
      rfl
    · by_cases h1 : i = 1
      · subst h1
        show c * ρ 1 * Real.cos θ - c * ρ 2 * Real.sin θ =
             c • (ρ 1 * Real.cos θ - ρ 2 * Real.sin θ)
        show c * ρ 1 * Real.cos θ - c * ρ 2 * Real.sin θ =
             c * (ρ 1 * Real.cos θ - ρ 2 * Real.sin θ)
        ring
      · by_cases h2 : i = 2
        · subst h2
          show c * ρ 1 * Real.sin θ + c * ρ 2 * Real.cos θ =
               c • (ρ 1 * Real.sin θ + ρ 2 * Real.cos θ)
          show c * ρ 1 * Real.sin θ + c * ρ 2 * Real.cos θ =
               c * (ρ 1 * Real.sin θ + ρ 2 * Real.cos θ)
          ring
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show c * ρ 3 = c • (ρ 3)
          rfl

@[simp] theorem rotX_apply_zero (θ : ℝ) (ρ : V) : rotX θ ρ 0 = ρ 0 := rfl
@[simp] theorem rotX_apply_one (θ : ℝ) (ρ : V) :
    rotX θ ρ 1 = ρ 1 * Real.cos θ - ρ 2 * Real.sin θ := rfl
@[simp] theorem rotX_apply_two (θ : ℝ) (ρ : V) :
    rotX θ ρ 2 = ρ 1 * Real.sin θ + ρ 2 * Real.cos θ := rfl
@[simp] theorem rotX_apply_three (θ : ℝ) (ρ : V) : rotX θ ρ 3 = ρ 3 := rfl

/-- `rotX 0 = id`. -/
theorem rotX_zero : rotX 0 = LinearMap.id := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0; show ρ 0 = ρ 0; rfl
  · by_cases h1 : i = 1
    · subst h1
      show ρ 1 * Real.cos 0 - ρ 2 * Real.sin 0 = ρ 1
      rw [Real.cos_zero, Real.sin_zero]; ring
    · by_cases h2 : i = 2
      · subst h2
        show ρ 1 * Real.sin 0 + ρ 2 * Real.cos 0 = ρ 2
        rw [Real.cos_zero, Real.sin_zero]; ring
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; show ρ 3 = ρ 3; rfl

/-- `rotX θ` preserves `(y, z)`-norm squared. -/
theorem rotX_preserves_yz_norm (θ : ℝ) (ρ : V) :
    (rotX θ ρ) 1 ^ 2 + (rotX θ ρ) 2 ^ 2 = ρ 1 ^ 2 + ρ 2 ^ 2 := by
  rw [rotX_apply_one, rotX_apply_two]
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  nlinarith [hc]

/-- `rotX θ` preserves the squared Bloch norm. -/
theorem rotX_preserves_sq_norm (θ : ℝ) (ρ : V) :
    (rotX θ ρ) 0 ^ 2 + (rotX θ ρ) 1 ^ 2 + (rotX θ ρ) 2 ^ 2 =
      ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 := by
  have hyz := rotX_preserves_yz_norm θ ρ
  rw [rotX_apply_zero]
  linarith [hyz]

/-- `rotX θ` preserves the state space. -/
theorem rotX_preserves_states (θ : ℝ) (ρ : V) (hρ : ρ ∈ states) :
    rotX θ ρ ∈ states := by
  refine ⟨?_, ?_⟩
  · rw [rotX_apply_three]; exact hρ.1
  · rw [rotX_preserves_sq_norm]; exact hρ.2

/-- `rotX θ` preserves the unit functional. -/
theorem rotX_preserves_unit (θ : ℝ) :
    unitLin.comp (rotX θ) = unitLin := by
  apply LinearMap.ext; intro ρ
  show (rotX θ ρ) 3 = ρ 3
  rfl

/-- `rotX θ` is continuous as a map `V → V`. -/
theorem rotX_continuous (θ : ℝ) : Continuous (rotX θ) := by
  apply continuous_pi
  intro i
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun ρ : V => ρ 0)
    exact continuous_apply 0
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun ρ : V => ρ 1 * Real.cos θ - ρ 2 * Real.sin θ)
      exact ((continuous_apply 1).mul continuous_const).sub
        ((continuous_apply 2).mul continuous_const)
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun ρ : V => ρ 1 * Real.sin θ + ρ 2 * Real.cos θ)
        exact ((continuous_apply 1).mul continuous_const).add
          ((continuous_apply 2).mul continuous_const)
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun ρ : V => ρ 3)
        exact continuous_apply 3

/-- `rotX θ` is JOINTLY continuous in `(θ, ρ)`. -/
theorem rotX_continuous_pair :
    Continuous (fun p : ℝ × V => rotX p.1 p.2) := by
  apply continuous_pi
  intro i
  have hp1_cont : Continuous (fun p : ℝ × V => p.1) := continuous_fst
  have hcos : Continuous (fun p : ℝ × V => Real.cos p.1) :=
    Real.continuous_cos.comp hp1_cont
  have hsin : Continuous (fun p : ℝ × V => Real.sin p.1) :=
    Real.continuous_sin.comp hp1_cont
  have h0c : Continuous (fun p : ℝ × V => p.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have h1c : Continuous (fun p : ℝ × V => p.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have h2c : Continuous (fun p : ℝ × V => p.2 2) :=
    (continuous_apply 2).comp continuous_snd
  have h3c : Continuous (fun p : ℝ × V => p.2 3) :=
    (continuous_apply 3).comp continuous_snd
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun p : ℝ × V => p.2 0)
    exact h0c
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun p : ℝ × V =>
        p.2 1 * Real.cos p.1 - p.2 2 * Real.sin p.1)
      exact (h1c.mul hcos).sub (h2c.mul hsin)
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun p : ℝ × V =>
          p.2 1 * Real.sin p.1 + p.2 2 * Real.cos p.1)
        exact (h1c.mul hsin).add (h2c.mul hcos)
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun p : ℝ × V => p.2 3)
        exact h3c

/-- Composition law: `rotX θ₁ ∘ rotX θ₂ = rotX (θ₁ + θ₂)`. -/
theorem rotX_comp (θ₁ θ₂ : ℝ) :
    (rotX θ₁).comp (rotX θ₂) = rotX (θ₁ + θ₂) := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0; rfl
  · by_cases h1 : i = 1
    · subst h1
      show (rotX θ₁ (rotX θ₂ ρ)) 1 = (rotX (θ₁ + θ₂) ρ) 1
      rw [rotX_apply_one (θ := θ₁), rotX_apply_one (θ := θ₂),
          rotX_apply_two (θ := θ₂), rotX_apply_one (θ := θ₁ + θ₂),
          Real.cos_add, Real.sin_add]
      ring
    · by_cases h2 : i = 2
      · subst h2
        show (rotX θ₁ (rotX θ₂ ρ)) 2 = (rotX (θ₁ + θ₂) ρ) 2
        rw [rotX_apply_two (θ := θ₁), rotX_apply_one (θ := θ₂),
            rotX_apply_two (θ := θ₂), rotX_apply_two (θ := θ₁ + θ₂),
            Real.cos_add, Real.sin_add]
        ring
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; rfl

theorem rotX_comp_neg (θ : ℝ) :
    (rotX θ).comp (rotX (-θ)) = LinearMap.id := by
  rw [rotX_comp, add_neg_cancel, rotX_zero]

theorem rotX_neg_comp (θ : ℝ) :
    (rotX (-θ)).comp (rotX θ) = LinearMap.id := by
  rw [rotX_comp, neg_add_cancel, rotX_zero]

/-- `rotX θ` is bijective. -/
theorem rotX_bijective (θ : ℝ) : Function.Bijective (rotX θ) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    have hv : rotX (-θ) (rotX θ v) = v := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotX_neg_comp θ)
      simpa using h_eq
    have hw : rotX (-θ) (rotX θ w) = w := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f w) (rotX_neg_comp θ)
      simpa using h_eq
    have h_app := congr_arg (rotX (-θ)) h
    rw [hv, hw] at h_app
    exact h_app
  · intro v
    refine ⟨rotX (-θ) v, ?_⟩
    have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotX_comp_neg θ)
    simpa using h_eq

/-! ### Rotation around the y-axis -/

/-- `rotY θ : V →ₗ[ℝ] V` is rotation by angle θ around the y-axis. -/
noncomputable def rotY (θ : ℝ) : V →ₗ[ℝ] V where
  toFun ρ := fun i =>
    if i = 0 then ρ 0 * Real.cos θ + ρ 2 * Real.sin θ
    else if i = 1 then ρ 1
    else if i = 2 then -ρ 0 * Real.sin θ + ρ 2 * Real.cos θ
    else ρ 3
  map_add' ρ σ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show (ρ 0 + σ 0) * Real.cos θ + (ρ 2 + σ 2) * Real.sin θ =
           (ρ 0 * Real.cos θ + ρ 2 * Real.sin θ) +
           (σ 0 * Real.cos θ + σ 2 * Real.sin θ)
      ring
    · by_cases h1 : i = 1
      · subst h1
        show ρ 1 + σ 1 = ρ 1 + σ 1
        rfl
      · by_cases h2 : i = 2
        · subst h2
          show -(ρ 0 + σ 0) * Real.sin θ + (ρ 2 + σ 2) * Real.cos θ =
               (-ρ 0 * Real.sin θ + ρ 2 * Real.cos θ) +
               (-σ 0 * Real.sin θ + σ 2 * Real.cos θ)
          ring
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show ρ 3 + σ 3 = ρ 3 + σ 3
          rfl
  map_smul' c ρ := by
    funext i
    by_cases h0 : i = 0
    · subst h0
      show c * ρ 0 * Real.cos θ + c * ρ 2 * Real.sin θ =
           c • (ρ 0 * Real.cos θ + ρ 2 * Real.sin θ)
      show c * ρ 0 * Real.cos θ + c * ρ 2 * Real.sin θ =
           c * (ρ 0 * Real.cos θ + ρ 2 * Real.sin θ)
      ring
    · by_cases h1 : i = 1
      · subst h1
        show c * ρ 1 = c • ρ 1
        rfl
      · by_cases h2 : i = 2
        · subst h2
          show -(c * ρ 0) * Real.sin θ + c * ρ 2 * Real.cos θ =
               c • (-ρ 0 * Real.sin θ + ρ 2 * Real.cos θ)
          show -(c * ρ 0) * Real.sin θ + c * ρ 2 * Real.cos θ =
               c * (-ρ 0 * Real.sin θ + ρ 2 * Real.cos θ)
          ring
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show c * ρ 3 = c • (ρ 3)
          rfl

@[simp] theorem rotY_apply_zero (θ : ℝ) (ρ : V) :
    rotY θ ρ 0 = ρ 0 * Real.cos θ + ρ 2 * Real.sin θ := rfl
@[simp] theorem rotY_apply_one (θ : ℝ) (ρ : V) : rotY θ ρ 1 = ρ 1 := rfl
@[simp] theorem rotY_apply_two (θ : ℝ) (ρ : V) :
    rotY θ ρ 2 = -ρ 0 * Real.sin θ + ρ 2 * Real.cos θ := rfl
@[simp] theorem rotY_apply_three (θ : ℝ) (ρ : V) : rotY θ ρ 3 = ρ 3 := rfl

theorem rotY_zero : rotY 0 = LinearMap.id := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0
    show ρ 0 * Real.cos 0 + ρ 2 * Real.sin 0 = ρ 0
    rw [Real.cos_zero, Real.sin_zero]; ring
  · by_cases h1 : i = 1
    · subst h1; rfl
    · by_cases h2 : i = 2
      · subst h2
        show -ρ 0 * Real.sin 0 + ρ 2 * Real.cos 0 = ρ 2
        rw [Real.cos_zero, Real.sin_zero]; ring
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; rfl

theorem rotY_preserves_xz_norm (θ : ℝ) (ρ : V) :
    (rotY θ ρ) 0 ^ 2 + (rotY θ ρ) 2 ^ 2 = ρ 0 ^ 2 + ρ 2 ^ 2 := by
  rw [rotY_apply_zero, rotY_apply_two]
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  nlinarith [hc]

theorem rotY_preserves_sq_norm (θ : ℝ) (ρ : V) :
    (rotY θ ρ) 0 ^ 2 + (rotY θ ρ) 1 ^ 2 + (rotY θ ρ) 2 ^ 2 =
      ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 := by
  have hxz := rotY_preserves_xz_norm θ ρ
  rw [rotY_apply_one]
  linarith [hxz]

theorem rotY_preserves_states (θ : ℝ) (ρ : V) (hρ : ρ ∈ states) :
    rotY θ ρ ∈ states := by
  refine ⟨?_, ?_⟩
  · rw [rotY_apply_three]; exact hρ.1
  · rw [rotY_preserves_sq_norm]; exact hρ.2

theorem rotY_preserves_unit (θ : ℝ) :
    unitLin.comp (rotY θ) = unitLin := by
  apply LinearMap.ext; intro ρ
  show (rotY θ ρ) 3 = ρ 3
  rfl

theorem rotY_continuous (θ : ℝ) : Continuous (rotY θ) := by
  apply continuous_pi
  intro i
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun ρ : V => ρ 0 * Real.cos θ + ρ 2 * Real.sin θ)
    exact ((continuous_apply 0).mul continuous_const).add
      ((continuous_apply 2).mul continuous_const)
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun ρ : V => ρ 1)
      exact continuous_apply 1
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun ρ : V => -ρ 0 * Real.sin θ + ρ 2 * Real.cos θ)
        exact (((continuous_apply 0).neg).mul continuous_const).add
          ((continuous_apply 2).mul continuous_const)
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun ρ : V => ρ 3)
        exact continuous_apply 3

/-- `rotY θ` is JOINTLY continuous in `(θ, ρ)`. -/
theorem rotY_continuous_pair :
    Continuous (fun p : ℝ × V => rotY p.1 p.2) := by
  apply continuous_pi
  intro i
  have hp1_cont : Continuous (fun p : ℝ × V => p.1) := continuous_fst
  have hcos : Continuous (fun p : ℝ × V => Real.cos p.1) :=
    Real.continuous_cos.comp hp1_cont
  have hsin : Continuous (fun p : ℝ × V => Real.sin p.1) :=
    Real.continuous_sin.comp hp1_cont
  have h0c : Continuous (fun p : ℝ × V => p.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have h1c : Continuous (fun p : ℝ × V => p.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have h2c : Continuous (fun p : ℝ × V => p.2 2) :=
    (continuous_apply 2).comp continuous_snd
  have h3c : Continuous (fun p : ℝ × V => p.2 3) :=
    (continuous_apply 3).comp continuous_snd
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun p : ℝ × V =>
      p.2 0 * Real.cos p.1 + p.2 2 * Real.sin p.1)
    exact (h0c.mul hcos).add (h2c.mul hsin)
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun p : ℝ × V => p.2 1)
      exact h1c
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun p : ℝ × V =>
          -p.2 0 * Real.sin p.1 + p.2 2 * Real.cos p.1)
        exact (h0c.neg.mul hsin).add (h2c.mul hcos)
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun p : ℝ × V => p.2 3)
        exact h3c

theorem rotY_comp (θ₁ θ₂ : ℝ) :
    (rotY θ₁).comp (rotY θ₂) = rotY (θ₁ + θ₂) := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0
    show (rotY θ₁ (rotY θ₂ ρ)) 0 = (rotY (θ₁ + θ₂) ρ) 0
    rw [rotY_apply_zero (θ := θ₁), rotY_apply_zero (θ := θ₂),
        rotY_apply_two (θ := θ₂), rotY_apply_zero (θ := θ₁ + θ₂),
        Real.cos_add, Real.sin_add]
    ring
  · by_cases h1 : i = 1
    · subst h1; rfl
    · by_cases h2 : i = 2
      · subst h2
        show (rotY θ₁ (rotY θ₂ ρ)) 2 = (rotY (θ₁ + θ₂) ρ) 2
        rw [rotY_apply_two (θ := θ₁), rotY_apply_zero (θ := θ₂),
            rotY_apply_two (θ := θ₂), rotY_apply_two (θ := θ₁ + θ₂),
            Real.cos_add, Real.sin_add]
        ring
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; rfl

theorem rotY_comp_neg (θ : ℝ) :
    (rotY θ).comp (rotY (-θ)) = LinearMap.id := by
  rw [rotY_comp, add_neg_cancel, rotY_zero]

theorem rotY_neg_comp (θ : ℝ) :
    (rotY (-θ)).comp (rotY θ) = LinearMap.id := by
  rw [rotY_comp, neg_add_cancel, rotY_zero]

theorem rotY_bijective (θ : ℝ) : Function.Bijective (rotY θ) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    have hv : rotY (-θ) (rotY θ v) = v := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotY_neg_comp θ)
      simpa using h_eq
    have hw : rotY (-θ) (rotY θ w) = w := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f w) (rotY_neg_comp θ)
      simpa using h_eq
    have h_app := congr_arg (rotY (-θ)) h
    rw [hv, hw] at h_app
    exact h_app
  · intro v
    refine ⟨rotY (-θ) v, ?_⟩
    have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotY_comp_neg θ)
    simpa using h_eq

/-! ### Rotation around the z-axis -/

/-- `rotZ θ : V →ₗ[ℝ] V` is rotation by angle θ around the z-axis. -/
noncomputable def rotZ (θ : ℝ) : V →ₗ[ℝ] V where
  toFun ρ := fun i =>
    if i = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
    else if i = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
    else if i = 2 then ρ 2
    else ρ 3
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
      · by_cases h2 : i = 2
        · subst h2
          show ρ 2 + σ 2 = ρ 2 + σ 2
          rfl
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show ρ 3 + σ 3 = ρ 3 + σ 3
          rfl
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
      · by_cases h2 : i = 2
        · subst h2
          show c * ρ 2 = c • (ρ 2)
          rfl
        · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
          subst hi3
          show c * ρ 3 = c • (ρ 3)
          rfl

@[simp] theorem rotZ_apply_zero (θ : ℝ) (ρ : V) :
    rotZ θ ρ 0 = ρ 0 * Real.cos θ - ρ 1 * Real.sin θ := rfl
@[simp] theorem rotZ_apply_one (θ : ℝ) (ρ : V) :
    rotZ θ ρ 1 = ρ 0 * Real.sin θ + ρ 1 * Real.cos θ := rfl
@[simp] theorem rotZ_apply_two (θ : ℝ) (ρ : V) : rotZ θ ρ 2 = ρ 2 := rfl
@[simp] theorem rotZ_apply_three (θ : ℝ) (ρ : V) : rotZ θ ρ 3 = ρ 3 := rfl

theorem rotZ_zero : rotZ 0 = LinearMap.id := by
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
    · by_cases h2 : i = 2
      · subst h2; rfl
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; rfl

theorem rotZ_preserves_xy_norm (θ : ℝ) (ρ : V) :
    (rotZ θ ρ) 0 ^ 2 + (rotZ θ ρ) 1 ^ 2 = ρ 0 ^ 2 + ρ 1 ^ 2 := by
  rw [rotZ_apply_zero, rotZ_apply_one]
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  nlinarith [hc]

theorem rotZ_preserves_sq_norm (θ : ℝ) (ρ : V) :
    (rotZ θ ρ) 0 ^ 2 + (rotZ θ ρ) 1 ^ 2 + (rotZ θ ρ) 2 ^ 2 =
      ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 := by
  have hxy := rotZ_preserves_xy_norm θ ρ
  rw [rotZ_apply_two]
  linarith [hxy]

theorem rotZ_preserves_states (θ : ℝ) (ρ : V) (hρ : ρ ∈ states) :
    rotZ θ ρ ∈ states := by
  refine ⟨?_, ?_⟩
  · rw [rotZ_apply_three]; exact hρ.1
  · rw [rotZ_preserves_sq_norm]; exact hρ.2

theorem rotZ_preserves_unit (θ : ℝ) :
    unitLin.comp (rotZ θ) = unitLin := by
  apply LinearMap.ext; intro ρ
  show (rotZ θ ρ) 3 = ρ 3
  rfl

theorem rotZ_continuous (θ : ℝ) : Continuous (rotZ θ) := by
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
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun ρ : V => ρ 2)
        exact continuous_apply 2
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun ρ : V => ρ 3)
        exact continuous_apply 3

/-- `rotZ θ` is JOINTLY continuous in `(θ, ρ)` — analog of
`CircleGPT.rotZ_continuous_pair` for the Bloch ball. -/
theorem rotZ_continuous_pair :
    Continuous (fun p : ℝ × V => rotZ p.1 p.2) := by
  apply continuous_pi
  intro i
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun p : ℝ × V =>
      p.2 0 * Real.cos p.1 - p.2 1 * Real.sin p.1)
    have hp1_cont : Continuous (fun p : ℝ × V => p.1) := continuous_fst
    have hcos : Continuous (fun p : ℝ × V => Real.cos p.1) :=
      Real.continuous_cos.comp hp1_cont
    have hsin : Continuous (fun p : ℝ × V => Real.sin p.1) :=
      Real.continuous_sin.comp hp1_cont
    have h0c : Continuous (fun p : ℝ × V => p.2 0) :=
      (continuous_apply 0).comp continuous_snd
    have h1c : Continuous (fun p : ℝ × V => p.2 1) :=
      (continuous_apply 1).comp continuous_snd
    exact (h0c.mul hcos).sub (h1c.mul hsin)
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun p : ℝ × V =>
        p.2 0 * Real.sin p.1 + p.2 1 * Real.cos p.1)
      have hp1_cont : Continuous (fun p : ℝ × V => p.1) := continuous_fst
      have hcos : Continuous (fun p : ℝ × V => Real.cos p.1) :=
        Real.continuous_cos.comp hp1_cont
      have hsin : Continuous (fun p : ℝ × V => Real.sin p.1) :=
        Real.continuous_sin.comp hp1_cont
      have h0c : Continuous (fun p : ℝ × V => p.2 0) :=
        (continuous_apply 0).comp continuous_snd
      have h1c : Continuous (fun p : ℝ × V => p.2 1) :=
        (continuous_apply 1).comp continuous_snd
      exact (h0c.mul hsin).add (h1c.mul hcos)
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun p : ℝ × V => p.2 2)
        exact (continuous_apply 2).comp continuous_snd
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun p : ℝ × V => p.2 3)
        exact (continuous_apply 3).comp continuous_snd

theorem rotZ_comp (θ₁ θ₂ : ℝ) :
    (rotZ θ₁).comp (rotZ θ₂) = rotZ (θ₁ + θ₂) := by
  apply LinearMap.ext; intro ρ
  funext i
  by_cases h0 : i = 0
  · subst h0
    show (rotZ θ₁ (rotZ θ₂ ρ)) 0 = (rotZ (θ₁ + θ₂) ρ) 0
    rw [rotZ_apply_zero (θ := θ₁), rotZ_apply_zero (θ := θ₂),
        rotZ_apply_one (θ := θ₂), rotZ_apply_zero (θ := θ₁ + θ₂),
        Real.cos_add, Real.sin_add]
    ring
  · by_cases h1 : i = 1
    · subst h1
      show (rotZ θ₁ (rotZ θ₂ ρ)) 1 = (rotZ (θ₁ + θ₂) ρ) 1
      rw [rotZ_apply_one (θ := θ₁), rotZ_apply_zero (θ := θ₂),
          rotZ_apply_one (θ := θ₂), rotZ_apply_one (θ := θ₁ + θ₂),
          Real.cos_add, Real.sin_add]
      ring
    · by_cases h2 : i = 2
      · subst h2; rfl
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3; rfl

theorem rotZ_comp_neg (θ : ℝ) :
    (rotZ θ).comp (rotZ (-θ)) = LinearMap.id := by
  rw [rotZ_comp, add_neg_cancel, rotZ_zero]

theorem rotZ_neg_comp (θ : ℝ) :
    (rotZ (-θ)).comp (rotZ θ) = LinearMap.id := by
  rw [rotZ_comp, neg_add_cancel, rotZ_zero]

theorem rotZ_bijective (θ : ℝ) : Function.Bijective (rotZ θ) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    have hv : rotZ (-θ) (rotZ θ v) = v := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotZ_neg_comp θ)
      simpa using h_eq
    have hw : rotZ (-θ) (rotZ θ w) = w := by
      have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f w) (rotZ_neg_comp θ)
      simpa using h_eq
    have h_app := congr_arg (rotZ (-θ)) h
    rw [hv, hw] at h_app
    exact h_app
  · intro v
    refine ⟨rotZ (-θ) v, ?_⟩
    have h_eq := congr_arg (fun (f : V →ₗ[ℝ] V) => f v) (rotZ_comp_neg θ)
    simpa using h_eq

/-! ## Packaging the rotations as `Reversible` / `StrictReversible` -/

/-- `rotX θ` as a `Reversible qubitGPT`. -/
noncomputable def rotXReversible (θ : ℝ) :
    Perspectival.Continuity.Reversible qubitGPT where
  toLin := rotX θ
  continuous_toLin := rotX_continuous θ
  preserves_states := rotX_preserves_states θ
  preserves_unit := rotX_preserves_unit θ

/-- `rotY θ` as a `Reversible qubitGPT`. -/
noncomputable def rotYReversible (θ : ℝ) :
    Perspectival.Continuity.Reversible qubitGPT where
  toLin := rotY θ
  continuous_toLin := rotY_continuous θ
  preserves_states := rotY_preserves_states θ
  preserves_unit := rotY_preserves_unit θ

/-- `rotZ θ` as a `Reversible qubitGPT`. -/
noncomputable def rotZReversible (θ : ℝ) :
    Perspectival.Continuity.Reversible qubitGPT where
  toLin := rotZ θ
  continuous_toLin := rotZ_continuous θ
  preserves_states := rotZ_preserves_states θ
  preserves_unit := rotZ_preserves_unit θ

/-- `rotX θ` as a `StrictReversible qubitGPT`. -/
noncomputable def rotXStrictReversible (θ : ℝ) :
    Perspectival.Continuity.StrictReversible qubitGPT where
  toReversible := rotXReversible θ
  isEquiv := rotX_bijective θ

/-- `rotY θ` as a `StrictReversible qubitGPT`. -/
noncomputable def rotYStrictReversible (θ : ℝ) :
    Perspectival.Continuity.StrictReversible qubitGPT where
  toReversible := rotYReversible θ
  isEquiv := rotY_bijective θ

/-- `rotZ θ` as a `StrictReversible qubitGPT`. -/
noncomputable def rotZStrictReversible (θ : ℝ) :
    Perspectival.Continuity.StrictReversible qubitGPT where
  toReversible := rotZReversible θ
  isEquiv := rotZ_bijective θ

@[simp] theorem rotXStrictReversible_toLin (θ : ℝ) :
    (rotXStrictReversible θ).toLin = rotX θ := rfl
@[simp] theorem rotYStrictReversible_toLin (θ : ℝ) :
    (rotYStrictReversible θ).toLin = rotY θ := rfl
@[simp] theorem rotZStrictReversible_toLin (θ : ℝ) :
    (rotZStrictReversible θ).toLin = rotZ θ := rfl

/-! ## Continuous path of `rotZ` rotations (affine in θ)

We construct a `StrictReversiblePath` between any two `rotZ` Reversibles.
This gives the `qubitGPT` a non-trivial path-connected family of
Reversibles, suitable for the `StrictConnectedAgency` structure below.

The full SO(3) action — paths between arbitrary `rotX`/`rotY`/`rotZ`
rotations through the SO(3) group manifold — is deferred to a later
session; here we provide the `rotZ` slice, which is already enough to
exhibit a non-degenerate `StrictConnectedAgency`. -/

/-- Affine interpolation of angles. -/
private noncomputable def angleInterp (θ₁ θ₂ : ℝ) (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * θ₁ + (t : ℝ) * θ₂

@[simp] private theorem angleInterp_zero (θ₁ θ₂ : ℝ) :
    angleInterp θ₁ θ₂ 0 = θ₁ := by
  show (1 - ((0 : unitInterval) : ℝ)) * θ₁ + ((0 : unitInterval) : ℝ) * θ₂ = θ₁
  simp

@[simp] private theorem angleInterp_one (θ₁ θ₂ : ℝ) :
    angleInterp θ₁ θ₂ 1 = θ₂ := by
  show (1 - ((1 : unitInterval) : ℝ)) * θ₁ + ((1 : unitInterval) : ℝ) * θ₂ = θ₂
  simp

private theorem angleInterp_continuous (θ₁ θ₂ : ℝ) :
    Continuous (angleInterp θ₁ θ₂) := by
  unfold angleInterp
  have ht : Continuous (fun t : unitInterval => (t : ℝ)) :=
    continuous_subtype_val
  exact ((continuous_const.sub ht).mul continuous_const).add
    (ht.mul continuous_const)

/-- The rotation-path `γ(t) := rotZ ((1-t) θ₁ + t θ₂)`. -/
noncomputable def rotZPath (θ₁ θ₂ : ℝ) (t : unitInterval) : V →ₗ[ℝ] V :=
  rotZ (angleInterp θ₁ θ₂ t)

@[simp] theorem rotZPath_zero (θ₁ θ₂ : ℝ) :
    rotZPath θ₁ θ₂ 0 = rotZ θ₁ := by
  unfold rotZPath; rw [angleInterp_zero]

@[simp] theorem rotZPath_one (θ₁ θ₂ : ℝ) :
    rotZPath θ₁ θ₂ 1 = rotZ θ₂ := by
  unfold rotZPath; rw [angleInterp_one]

/-- Joint continuity of `(t, v) ↦ rotZPath θ₁ θ₂ t v`. -/
theorem rotZPath_continuous (θ₁ θ₂ : ℝ) :
    Continuous (fun p : unitInterval × V => rotZPath θ₁ θ₂ p.1 p.2) := by
  apply continuous_pi
  intro i
  have hθ : Continuous (fun p : unitInterval × V => angleInterp θ₁ θ₂ p.1) :=
    (angleInterp_continuous θ₁ θ₂).comp continuous_fst
  have hcos : Continuous
      (fun p : unitInterval × V => Real.cos (angleInterp θ₁ θ₂ p.1)) :=
    Real.continuous_cos.comp hθ
  have hsin : Continuous
      (fun p : unitInterval × V => Real.sin (angleInterp θ₁ θ₂ p.1)) :=
    Real.continuous_sin.comp hθ
  have h0c : Continuous (fun p : unitInterval × V => p.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have h1c : Continuous (fun p : unitInterval × V => p.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have h2c : Continuous (fun p : unitInterval × V => p.2 2) :=
    (continuous_apply 2).comp continuous_snd
  have h3c : Continuous (fun p : unitInterval × V => p.2 3) :=
    (continuous_apply 3).comp continuous_snd
  by_cases h0 : i = 0
  · subst h0
    show Continuous (fun p : unitInterval × V =>
      p.2 0 * Real.cos (angleInterp θ₁ θ₂ p.1) -
      p.2 1 * Real.sin (angleInterp θ₁ θ₂ p.1))
    exact (h0c.mul hcos).sub (h1c.mul hsin)
  · by_cases h1 : i = 1
    · subst h1
      show Continuous (fun p : unitInterval × V =>
        p.2 0 * Real.sin (angleInterp θ₁ θ₂ p.1) +
        p.2 1 * Real.cos (angleInterp θ₁ θ₂ p.1))
      exact (h0c.mul hsin).add (h1c.mul hcos)
    · by_cases h2 : i = 2
      · subst h2
        show Continuous (fun p : unitInterval × V => p.2 2)
        exact h2c
      · have hi3 : i = 3 := fin4_is_three i h0 h1 h2
        subst hi3
        show Continuous (fun p : unitInterval × V => p.2 3)
        exact h3c

/-- A `StrictReversiblePath` between two `rotZ` rotations. -/
noncomputable def rotZStrictPath (θ₁ θ₂ : ℝ) :
    Perspectival.Continuity.StrictReversiblePath qubitGPT
      (rotZStrictReversible θ₁) (rotZStrictReversible θ₂) where
  γ := rotZPath θ₁ θ₂
  continuous := rotZPath_continuous θ₁ θ₂
  start := by
    show rotZPath θ₁ θ₂ 0 = (rotZStrictReversible θ₁).toLin
    rw [rotZPath_zero, rotZStrictReversible_toLin]
  finish := by
    show rotZPath θ₁ θ₂ 1 = (rotZStrictReversible θ₂).toLin
    rw [rotZPath_one, rotZStrictReversible_toLin]
  preserves_states_along := fun t ρ hρ =>
    rotZ_preserves_states (angleInterp θ₁ θ₂ t) ρ hρ
  preserves_unit_along := fun t =>
    rotZ_preserves_unit (angleInterp θ₁ θ₂ t)
  bijective_along := fun t =>
    rotZ_bijective (angleInterp θ₁ θ₂ t)

/-! ## Structure equality lemmas (copied verbatim from CircleGPT) -/

/-- `Reversible` is determined by its `toLin`. -/
theorem Reversible_eq_of_toLin {V' : Type _} [AddCommGroup V'] [Module ℝ V']
    [TopologicalSpace V'] {G : Perspectival.GPT V'}
    {R₁ R₂ : Perspectival.Continuity.Reversible G}
    (h : R₁.toLin = R₂.toLin) : R₁ = R₂ := by
  cases R₁; cases R₂; congr

/-- `StrictReversible` is determined by its `toLin`. -/
theorem StrictReversible_eq_of_toLin {V' : Type _} [AddCommGroup V'] [Module ℝ V']
    [TopologicalSpace V'] {G : Perspectival.GPT V'}
    {R₁ R₂ : Perspectival.Continuity.StrictReversible G}
    (h : R₁.toLin = R₂.toLin) : R₁ = R₂ := by
  cases R₁ with
  | mk R₁₁ _ => cases R₂ with
    | mk R₂₁ _ =>
      have := Reversible_eq_of_toLin (R₁ := R₁₁) (R₂ := R₂₁) h
      subst this; rfl

/-- `rotZStrictReversible 0 = StrictReversible.id qubitGPT`. -/
theorem rotZStrictReversible_zero :
    rotZStrictReversible 0 =
      Perspectival.Continuity.StrictReversible.id qubitGPT := by
  apply StrictReversible_eq_of_toLin
  show rotZ 0 = LinearMap.id
  exact rotZ_zero

/-! ## The avail set: all `rotZ` rotations -/

/-- The avail set: every `rotZ θ`. -/
noncomputable def rotZAvail :
    Set (Perspectival.Continuity.StrictReversible qubitGPT) :=
  Set.range rotZStrictReversible

theorem rotZ_in_avail (θ : ℝ) : rotZStrictReversible θ ∈ rotZAvail :=
  ⟨θ, rfl⟩

/-- The identity is in the avail set. -/
theorem id_in_rotZAvail :
    Perspectival.Continuity.StrictReversible.id qubitGPT ∈ rotZAvail := by
  refine ⟨0, ?_⟩
  exact rotZStrictReversible_zero

/-! ## `StrictConnectedAgency` for the Qubit GPT

We populate `StrictConnectedAgency qubitGPT` with the `rotZ` family.
The full SO(3) action would replace `rotZAvail` with the orbit of all
finite products of `rotX`, `rotY`, `rotZ`; this is deferred. -/

@[reducible]
noncomputable def qubitStrictConnectedAgency :
    Perspectival.Continuity.StrictConnectedAgency qubitGPT where
  avail := rotZAvail
  id_avail := id_in_rotZAvail
  strict_paths R₁ R₂ h₁ h₂ := by
    obtain ⟨θ₁, hθ₁⟩ := h₁
    obtain ⟨θ₂, hθ₂⟩ := h₂
    subst hθ₁; subst hθ₂
    exact ⟨rotZStrictPath θ₁ θ₂⟩

/-! ## Bloch-sphere points: the pure-state surface

Convention: a unit-vector `(x, y, z)` with `x² + y² + z² = 1` lifted to
`w = 1` is a Bloch-sphere point.  By the standard Bloch picture these
are the qubit's pure states. -/

/-- Bloch-sphere lift: `(x, y, z) ↦ (x, y, z, 1)`. -/
def blochPoint (x y z : ℝ) : V := fun i =>
  if i = 0 then x else if i = 1 then y else if i = 2 then z else 1

@[simp] theorem blochPoint_apply_zero (x y z : ℝ) : blochPoint x y z 0 = x := rfl
@[simp] theorem blochPoint_apply_one (x y z : ℝ) : blochPoint x y z 1 = y := rfl
@[simp] theorem blochPoint_apply_two (x y z : ℝ) : blochPoint x y z 2 = z := rfl
@[simp] theorem blochPoint_apply_three (x y z : ℝ) : blochPoint x y z 3 = 1 := rfl

/-- Bloch-sphere points (with `x² + y² + z² ≤ 1`) are states. -/
theorem blochPoint_in_states (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ 1) :
    blochPoint x y z ∈ states := by
  refine ⟨?_, ?_⟩
  · show blochPoint x y z 3 = 1; rfl
  · show (blochPoint x y z) 0 ^ 2 + (blochPoint x y z) 1 ^ 2
        + (blochPoint x y z) 2 ^ 2 ≤ 1
    rw [blochPoint_apply_zero, blochPoint_apply_one, blochPoint_apply_two]
    exact h

/-- The Bloch-sphere unit-norm point at `(1, 0, 0)` (the `+x` pure state). -/
noncomputable def blochPlusX : V := blochPoint 1 0 0

/-- The Bloch-sphere unit-norm point at `(0, 0, 1)` (the `+z` pure state). -/
noncomputable def blochPlusZ : V := blochPoint 0 0 1

theorem blochPlusX_in_states : blochPlusX ∈ states := by
  unfold blochPlusX
  exact blochPoint_in_states 1 0 0 (by norm_num)

theorem blochPlusZ_in_states : blochPlusZ ∈ states := by
  unfold blochPlusZ
  exact blochPoint_in_states 0 0 1 (by norm_num)

/-! ## Headline statement: complex-QM Hardy signature -/

/-- **The qubit Hardy trichotomy entry.** The qubit GPT lives on a real
4-dimensional carrier — Hardy's signature `K = N² = 4` for `N = 2`,
exhibiting the complex-quantum point of the (classical / rebit / qubit /
quaternionic) trichotomy. -/
theorem qubit_hardy_signature : Module.finrank ℝ V = 4 := qubit_hardy_K

/-! ## Bloch-sphere boundary points and the pure-state classification

The full pure-state classification for the qubit GPT: the pure states
of `qubitGPT` are exactly the points of the Bloch sphere
`{ (x, y, z, 1) : x² + y² + z² = 1 }`.

This is the 3D analog of the CircleGPT `pure_state_classification`. The
proof has two directions:

  ✓ `blochSphere_point_is_pure_state` (easy direction): every parametric
    Bloch-sphere point `blochPoint x y z` with `x² + y² + z² = 1` is a
    pure state. Strict-convexity (Jensen-equality) on the 3D ball.
  ✓ `pure_state_implies_blochSphere` (hard direction): every pure state
    of `qubitGPT` arises as some `blochPoint x y z` with
    `x² + y² + z² = 1`. Proof: a strict-interior point can be written
    as the midpoint of two distinct nearby states (perturbing the
    first coordinate), so extremality forces the squared norm to be 1.
-/

/-- The Bloch-sphere boundary point as a state, for `(x, y, z)` with
`x² + y² + z² = 1`. This is just `blochPoint x y z` packaged with the
unit-norm hypothesis; the existing `blochPoint` already provides the
lift to `w = 1`. -/
noncomputable def blochSpherePoint (x y z : ℝ) (_h : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    : V := blochPoint x y z

@[simp] theorem blochSpherePoint_apply_zero (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : blochSpherePoint x y z h 0 = x := rfl
@[simp] theorem blochSpherePoint_apply_one (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : blochSpherePoint x y z h 1 = y := rfl
@[simp] theorem blochSpherePoint_apply_two (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : blochSpherePoint x y z h 2 = z := rfl
@[simp] theorem blochSpherePoint_apply_three (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : blochSpherePoint x y z h 3 = 1 := rfl

/-- A Bloch-sphere boundary point is itself a state. -/
theorem blochSpherePoint_in_states (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : blochSpherePoint x y z h ∈ states := by
  unfold blochSpherePoint
  exact blochPoint_in_states x y z (le_of_eq h)

/-! ### Easy direction: every Bloch-sphere point is a pure state -/

/-- **Easy direction:** every Bloch-sphere boundary point
`blochSpherePoint x y z h` is a pure state of `qubitGPT`.

Strategy: Jensen-equality on `x² + y² + z²`. If `t·a + (1-t)·b` lies on
the unit Bloch sphere with `a, b ∈ states`, then `a = b = (x, y, z, 1)`. -/
theorem blochSpherePoint_is_pure_state (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    Perspectival.Continuity.PureState qubitGPT
      (blochSpherePoint x y z h) := by
  refine ⟨blochSpherePoint_in_states x y z h, ?_, ?_⟩
  · -- {blochSpherePoint x y z h} ⊆ states
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact blochSpherePoint_in_states x y z h
  · -- Open-segment endpoints lie in {blochSpherePoint x y z h}.
    rintro p hp q hq r hr ⟨a, b, ha, hb, hab, hpq⟩
    rw [Set.mem_singleton_iff] at hr
    rw [Set.mem_singleton_iff]
    -- r = blochSpherePoint x y z h = a • p + b • q; want p = blochSpherePoint.
    -- p, q ∈ states.
    -- (a * p 0 + b * q 0, a * p 1 + b * q 1, a * p 2 + b * q 2)
    --   = blochSpherePoint x y z h on coords 0, 1, 2.
    have h0 : a * p 0 + b * q 0 = x := by
      have hh := congr_fun hpq 0
      have hr0 : r 0 = x := by rw [hr]; rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [hr0] at hh
      linarith
    have h1 : a * p 1 + b * q 1 = y := by
      have hh := congr_fun hpq 1
      have hr1 : r 1 = y := by rw [hr]; rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [hr1] at hh
      linarith
    have h2 : a * p 2 + b * q 2 = z := by
      have hh := congr_fun hpq 2
      have hr2 : r 2 = z := by rw [hr]; rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [hr2] at hh
      linarith
    -- ‖a p + b q‖² = 1.
    have hnormeq :
        (a * p 0 + b * q 0) ^ 2 + (a * p 1 + b * q 1) ^ 2
          + (a * p 2 + b * q 2) ^ 2 = 1 := by
      rw [h0, h1, h2]; exact h
    -- Jensen identity:
    --   a·(‖p‖²) + b·(‖q‖²) − ‖ap+bq‖²
    --     = a·b·((p0−q0)² + (p1−q1)² + (p2−q2)²)
    have hjensen :
        a * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)
          + b * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2)
          - ((a * p 0 + b * q 0) ^ 2 + (a * p 1 + b * q 1) ^ 2
              + (a * p 2 + b * q 2) ^ 2)
        = a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2) := by
      have hb_eq : b = 1 - a := by linarith
      rw [hb_eq]; ring
    have h_psq : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 ≤ 1 := hp.2
    have h_qsq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 ≤ 1 := hq.2
    -- a·‖p‖² + b·‖q‖² ≤ a + b = 1.
    have h_upper :
        a * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)
          + b * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) ≤ 1 := by
      have h1' : a * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left h_psq ha.le
      have h2' : b * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) ≤ b * 1 :=
        mul_le_mul_of_nonneg_left h_qsq hb.le
      linarith
    -- Combined: a·b·(sum of squares) ≤ 0.
    have hle_zero :
        a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2) ≤ 0 := by
      linarith [hnormeq]
    -- But a·b > 0 and the sum of squares ≥ 0, so the sum is 0.
    have hab_pos : 0 < a * b := mul_pos ha hb
    have h_nn :
        0 ≤ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
      have := sq_nonneg (p 0 - q 0)
      have := sq_nonneg (p 1 - q 1)
      have := sq_nonneg (p 2 - q 2)
      linarith
    have hsum_zero :
        (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 = 0 := by
      have hprod :
          a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2) = 0 := by
        have hnonneg :
            0 ≤ a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2) :=
          mul_nonneg hab_pos.le h_nn
        linarith
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hab_pos)
    -- Each square is 0.
    have h_sq0_nn : 0 ≤ (p 0 - q 0) ^ 2 := sq_nonneg _
    have h_sq1_nn : 0 ≤ (p 1 - q 1) ^ 2 := sq_nonneg _
    have h_sq2_nn : 0 ≤ (p 2 - q 2) ^ 2 := sq_nonneg _
    have h_sq0 : (p 0 - q 0) ^ 2 = 0 := by linarith
    have h_sq1 : (p 1 - q 1) ^ 2 = 0 := by linarith
    have h_sq2 : (p 2 - q 2) ^ 2 = 0 := by linarith
    have h0_eq : p 0 = q 0 := by
      have hzero : p 0 - q 0 = 0 :=
        pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq0
      linarith
    have h1_eq : p 1 = q 1 := by
      have hzero : p 1 - q 1 = 0 :=
        pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq1
      linarith
    have h2_eq : p 2 = q 2 := by
      have hzero : p 2 - q 2 = 0 :=
        pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq2
      linarith
    -- Also p 3 = 1 = q 3 (from state membership).
    have h3_eq : p 3 = q 3 := by rw [hp.1, hq.1]
    -- Now compute p coords.
    have h0p : p 0 = x := by
      have heq : a * p 0 + b * q 0 = (a + b) * p 0 := by rw [h0_eq]; ring
      rw [hab, one_mul] at heq
      linarith [h0]
    have h1p : p 1 = y := by
      have heq : a * p 1 + b * q 1 = (a + b) * p 1 := by rw [h1_eq]; ring
      rw [hab, one_mul] at heq
      linarith [h1]
    have h2p : p 2 = z := by
      have heq : a * p 2 + b * q 2 = (a + b) * p 2 := by rw [h2_eq]; ring
      rw [hab, one_mul] at heq
      linarith [h2]
    funext i
    by_cases hi0 : i = 0
    · subst hi0
      show p 0 = blochSpherePoint x y z h 0
      rw [h0p]; rfl
    · by_cases hi1 : i = 1
      · subst hi1
        show p 1 = blochSpherePoint x y z h 1
        rw [h1p]; rfl
      · by_cases hi2 : i = 2
        · subst hi2
          show p 2 = blochSpherePoint x y z h 2
          rw [h2p]; rfl
        · have hi3 : i = 3 := fin4_is_three i hi0 hi1 hi2
          subst hi3
          show p 3 = blochSpherePoint x y z h 3
          rw [hp.1]; rfl

/-! ### Hard direction: every pure state is a Bloch-sphere point -/

/-- **Helper.** Any state ρ with `ρ 0² + ρ 1² + ρ 2² < 1` is NOT
extreme: we can write ρ as the midpoint of two distinct nearby states
obtained by perturbing the first coordinate.

This is the 3D analog of `CircleGPT.state_interior_not_extreme`. -/
private theorem state_interior_not_extreme
    (ρ : V) (hρ : ρ ∈ states) (hint : ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 < 1) :
    ¬ IsExtreme ℝ states {ρ} := by
  intro hext
  -- Pick δ := min(1, (1 - ‖ρ‖²)/(2|ρ 0| + 2)) > 0.
  set c : ℝ := 1 - ρ 0 ^ 2 - ρ 1 ^ 2 - ρ 2 ^ 2 with hc_def
  have hc_pos : 0 < c := by simp only [hc_def]; linarith
  set δ : ℝ := min 1 (c / (2 * |ρ 0| + 2)) with hδ_def
  have h_denom_pos : 0 < 2 * |ρ 0| + 2 := by
    have := abs_nonneg (ρ 0); linarith
  have hδ_pos : 0 < δ := by
    simp only [hδ_def]
    exact lt_min (by norm_num) (div_pos hc_pos h_denom_pos)
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_quot : δ ≤ c / (2 * |ρ 0| + 2) := min_le_right _ _
  -- Define ρ⁺ = (ρ 0 + δ, ρ 1, ρ 2, 1) and ρ⁻ = (ρ 0 - δ, ρ 1, ρ 2, 1).
  let xp : V := fun i =>
    if i = 0 then ρ 0 + δ else if i = 1 then ρ 1
    else if i = 2 then ρ 2 else 1
  let xm : V := fun i =>
    if i = 0 then ρ 0 - δ else if i = 1 then ρ 1
    else if i = 2 then ρ 2 else 1
  have hxp0 : xp 0 = ρ 0 + δ := by
    show (if (0:Fin 4) = 0 then _ else _) = _; rfl
  have hxp1 : xp 1 = ρ 1 := by
    show (if (1:Fin 4) = 0 then ρ 0 + δ else
          if (1:Fin 4) = 1 then ρ 1 else
          if (1:Fin 4) = 2 then ρ 2 else 1) = ρ 1
    simp
  have hxp2 : xp 2 = ρ 2 := by
    show (if (2:Fin 4) = 0 then ρ 0 + δ else
          if (2:Fin 4) = 1 then ρ 1 else
          if (2:Fin 4) = 2 then ρ 2 else 1) = ρ 2
    simp
  have hxp3 : xp 3 = 1 := by
    show (if (3:Fin 4) = 0 then ρ 0 + δ else
          if (3:Fin 4) = 1 then ρ 1 else
          if (3:Fin 4) = 2 then ρ 2 else 1) = 1
    rfl
  have hxm0 : xm 0 = ρ 0 - δ := by
    show (if (0:Fin 4) = 0 then _ else _) = _; rfl
  have hxm1 : xm 1 = ρ 1 := by
    show (if (1:Fin 4) = 0 then ρ 0 - δ else
          if (1:Fin 4) = 1 then ρ 1 else
          if (1:Fin 4) = 2 then ρ 2 else 1) = ρ 1
    simp
  have hxm2 : xm 2 = ρ 2 := by
    show (if (2:Fin 4) = 0 then ρ 0 - δ else
          if (2:Fin 4) = 1 then ρ 1 else
          if (2:Fin 4) = 2 then ρ 2 else 1) = ρ 2
    simp
  have hxm3 : xm 3 = 1 := by
    show (if (3:Fin 4) = 0 then ρ 0 - δ else
          if (3:Fin 4) = 1 then ρ 1 else
          if (3:Fin 4) = 2 then ρ 2 else 1) = 1
    rfl
  -- Bound: (ρ 0 ± δ)² + ρ 1² + ρ 2² ≤ 1.
  have h_bound : ∀ s : ℝ, s = δ ∨ s = -δ →
      (ρ 0 + s) ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 ≤ 1 := by
    intro s hs
    have hs_abs : |s| ≤ δ := by
      rcases hs with rfl | rfl
      · rw [abs_of_pos hδ_pos]
      · rw [abs_neg]; rw [abs_of_pos hδ_pos]
    have hs_sq : s ^ 2 ≤ δ ^ 2 := by
      have : |s| ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hs_abs 2
      rwa [sq_abs] at this
    have h_expand : (ρ 0 + s) ^ 2 = ρ 0 ^ 2 + 2 * ρ 0 * s + s ^ 2 := by ring
    have h_cross : 2 * ρ 0 * s ≤ 2 * |ρ 0| * δ := by
      have h_le1 : 2 * ρ 0 * s ≤ 2 * |ρ 0| * |s| := by
        have h1' : ρ 0 * s ≤ |ρ 0 * s| := le_abs_self _
        have h2' : |ρ 0 * s| = |ρ 0| * |s| := abs_mul _ _
        linarith
      have h_le2 : 2 * |ρ 0| * |s| ≤ 2 * |ρ 0| * δ := by
        have := mul_le_mul_of_nonneg_left hs_abs
          (by positivity : (0 : ℝ) ≤ 2 * |ρ 0|)
        linarith
      linarith
    have hδ_sq_le_δ : δ ^ 2 ≤ δ := by
      have : δ ^ 2 = δ * δ := sq δ
      rw [this]
      calc δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ_le_one hδ_pos.le
        _ = δ := mul_one _
    have h_combine : 2 * |ρ 0| * δ + δ ^ 2 ≤ c := by
      have hsum_le : 2 * |ρ 0| * δ + δ ≤ (2 * |ρ 0| + 2) * δ := by
        have habs_nn : 0 ≤ |ρ 0| := abs_nonneg _
        nlinarith [hδ_pos]
      have hquot_ineq : (2 * |ρ 0| + 2) * δ ≤ c := by
        have := mul_le_mul_of_nonneg_left hδ_le_quot h_denom_pos.le
        rw [mul_div_cancel₀ _ (ne_of_gt h_denom_pos)] at this
        linarith
      linarith
    have h_step1 :
        (ρ 0 + s) ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2
          ≤ ρ 0 ^ 2 + 2 * |ρ 0| * δ + δ ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 := by
      rw [h_expand]
      linarith
    have h_step2 :
        (ρ 0 + s) ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2
          ≤ ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 + c := by linarith
    have hc_relation :
        ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 + c = 1 := by simp only [hc_def]; ring
    linarith
  -- Show xp, xm ∈ states.
  have hxp_in : xp ∈ states := by
    refine ⟨?_, ?_⟩
    · rw [hxp3]
    · rw [hxp0, hxp1, hxp2]
      have h := h_bound δ (Or.inl rfl)
      linarith
  have hxm_in : xm ∈ states := by
    refine ⟨?_, ?_⟩
    · rw [hxm3]
    · rw [hxm0, hxm1, hxm2]
      have h := h_bound (-δ) (Or.inr rfl)
      have h_neg : (ρ 0 - δ) = (ρ 0 + (-δ)) := by ring
      rw [h_neg]
      linarith
  -- Midpoint: (1/2)·xp + (1/2)·xm = ρ.
  have h_mid : ((1 / 2 : ℝ)) • xp + ((1 / 2 : ℝ)) • xm = ρ := by
    funext i
    by_cases hi0 : i = 0
    · subst hi0
      show (1 / 2 : ℝ) * xp 0 + (1 / 2 : ℝ) * xm 0 = ρ 0
      rw [hxp0, hxm0]; ring
    · by_cases hi1 : i = 1
      · subst hi1
        show (1 / 2 : ℝ) * xp 1 + (1 / 2 : ℝ) * xm 1 = ρ 1
        rw [hxp1, hxm1]; ring
      · by_cases hi2 : i = 2
        · subst hi2
          show (1 / 2 : ℝ) * xp 2 + (1 / 2 : ℝ) * xm 2 = ρ 2
          rw [hxp2, hxm2]; ring
        · have hi3 : i = 3 := fin4_is_three i hi0 hi1 hi2
          subst hi3
          show (1 / 2 : ℝ) * xp 3 + (1 / 2 : ℝ) * xm 3 = ρ 3
          rw [hxp3, hxm3, hρ.1]; ring
  -- ρ ∈ openSegment ℝ xp xm.
  have h_in_open_seg : ρ ∈ openSegment ℝ xp xm :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, h_mid⟩
  -- By extremality of {ρ}, xp = ρ.
  have hxp_eq : xp ∈ ({ρ} : Set V) :=
    hext.left_mem_of_mem_openSegment hxp_in hxm_in (Set.mem_singleton _)
      h_in_open_seg
  rw [Set.mem_singleton_iff] at hxp_eq
  -- But xp 0 = ρ 0 + δ ≠ ρ 0 since δ > 0.
  have hxp0_eq : xp 0 = ρ 0 := by rw [hxp_eq]
  rw [hxp0] at hxp0_eq
  linarith

/-- **Hard direction:** every pure state of `qubitGPT` equals some
`blochSpherePoint x y z h` with `x² + y² + z² = 1`. -/
theorem pure_state_implies_blochSphere (ρ : V)
    (hρ_pure : Perspectival.Continuity.PureState qubitGPT ρ) :
    ∃ (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1),
      ρ = blochSpherePoint x y z h := by
  obtain ⟨hρ_st, hρ_ext⟩ := hρ_pure
  have hρ3 : ρ 3 = 1 := hρ_st.1
  have hρ_le : ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 ≤ 1 := hρ_st.2
  -- ρ 0² + ρ 1² + ρ 2² = 1 by ruling out the strict case.
  have hρ_eq : ρ 0 ^ 2 + ρ 1 ^ 2 + ρ 2 ^ 2 = 1 := by
    rcases lt_or_eq_of_le hρ_le with hlt | heq
    · exfalso
      exact state_interior_not_extreme ρ hρ_st hlt hρ_ext
    · exact heq
  refine ⟨ρ 0, ρ 1, ρ 2, hρ_eq, ?_⟩
  funext i
  by_cases hi0 : i = 0
  · subst hi0
    show ρ 0 = blochSpherePoint (ρ 0) (ρ 1) (ρ 2) hρ_eq 0
    rfl
  · by_cases hi1 : i = 1
    · subst hi1
      show ρ 1 = blochSpherePoint (ρ 0) (ρ 1) (ρ 2) hρ_eq 1
      rfl
    · by_cases hi2 : i = 2
      · subst hi2
        show ρ 2 = blochSpherePoint (ρ 0) (ρ 1) (ρ 2) hρ_eq 2
        rfl
      · have hi3 : i = 3 := fin4_is_three i hi0 hi1 hi2
        subst hi3
        show ρ 3 = blochSpherePoint (ρ 0) (ρ 1) (ρ 2) hρ_eq 3
        rw [hρ3]; rfl

/-- **Pure-state classification (statement form).** Every pure state of
`qubitGPT` is exactly a Bloch-sphere boundary point. -/
def qubit_pure_state_classification_statement : Prop :=
  ∀ ρ : V, Perspectival.Continuity.PureState qubitGPT ρ →
    ∃ (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1),
      ρ = blochSpherePoint x y z h

/-- **The qubit pure-state classification holds.** -/
theorem qubit_pure_state_classification :
    qubit_pure_state_classification_statement :=
  pure_state_implies_blochSphere

/-! ## OneParameterFamily instances: rotX, rotY, rotZ — three independent
    SO(3)-axis 1-parameter subgroups -/

/-- The qubit's `rotZ` family packaged as a `OneParameterFamily` —
the framework's first non-trivial continuous-symmetry instance on a
complex-QM-signature GPT. -/
noncomputable def rotZOneParameterFamily :
    Perspectival.Continuity.OneParameterFamily qubitGPT where
  f := rotZStrictReversible
  continuous := rotZ_continuous_pair
  zero := by
    show (rotZStrictReversible 0).toLin = LinearMap.id
    rw [rotZStrictReversible_toLin, rotZ_zero]
  add θ₁ θ₂ := by
    show (rotZStrictReversible (θ₁ + θ₂)).toLin
        = (rotZStrictReversible θ₁).toLin.comp (rotZStrictReversible θ₂).toLin
    rw [rotZStrictReversible_toLin, rotZStrictReversible_toLin,
        rotZStrictReversible_toLin, ← rotZ_comp]

/-- The qubit's `rotX` family packaged as a `OneParameterFamily`. -/
noncomputable def rotXOneParameterFamily :
    Perspectival.Continuity.OneParameterFamily qubitGPT where
  f := rotXStrictReversible
  continuous := rotX_continuous_pair
  zero := by
    show (rotXStrictReversible 0).toLin = LinearMap.id
    rw [rotXStrictReversible_toLin, rotX_zero]
  add θ₁ θ₂ := by
    show (rotXStrictReversible (θ₁ + θ₂)).toLin
        = (rotXStrictReversible θ₁).toLin.comp (rotXStrictReversible θ₂).toLin
    rw [rotXStrictReversible_toLin, rotXStrictReversible_toLin,
        rotXStrictReversible_toLin, ← rotX_comp]

/-- The qubit's `rotY` family packaged as a `OneParameterFamily`. -/
noncomputable def rotYOneParameterFamily :
    Perspectival.Continuity.OneParameterFamily qubitGPT where
  f := rotYStrictReversible
  continuous := rotY_continuous_pair
  zero := by
    show (rotYStrictReversible 0).toLin = LinearMap.id
    rw [rotYStrictReversible_toLin, rotY_zero]
  add θ₁ θ₂ := by
    show (rotYStrictReversible (θ₁ + θ₂)).toLin
        = (rotYStrictReversible θ₁).toLin.comp (rotYStrictReversible θ₂).toLin
    rw [rotYStrictReversible_toLin, rotYStrictReversible_toLin,
        rotYStrictReversible_toLin, ← rotY_comp]

/-- QubitGPT satisfies `HasOneParameterAgency`. -/
noncomputable instance qubitHasOneParameterAgency :
    Perspectival.Continuity.HasOneParameterAgency qubitGPT where
  family := rotZOneParameterFamily

/-- **QubitGPT has 3-axis agency** (the three SO(3) generator families).
This is the framework's first instance of `HasMultiAxisAgency` —
scaffold toward a SU(2)/SO(3) gauge instance (Tier 2 #6 next-step). -/
noncomputable def qubitMultiAxisAgency :
    Perspectival.Continuity.HasMultiAxisAgency 3 qubitGPT where
  axes := fun i =>
    if i = 0 then rotXOneParameterFamily
    else if i = 1 then rotYOneParameterFamily
    else rotZOneParameterFamily

end QubitGPT
end Perspectival
