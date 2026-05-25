/-
Perspectival Physics — Circle GPT (non-degenerate `TransitiveAgency`)
======================================================================

A concrete toy GPT with a continuous symmetry group acting transitively
on pure states.  Complements the classical-side no-go result
`Perspectival.Classical.classical_n2_no_transitive_agency` by exhibiting
a non-degenerate POSITIVE example of `TransitiveAgency`.

  V := Fin 3 → ℝ
  unit ρ := ρ 2                     (third-coordinate projection)
  states := { (x, y, 1) : x² + y² ≤ 1 }   (closed unit disk at z = 1)
  effects := { e : V →ₗ[ℝ] ℝ | 0 ≤ e ρ ≤ 1 for all ρ ∈ states }
  pure states := { (cos α, sin α, 1) : α ∈ ℝ }    (the unit circle)

The reversible transformations are rotations around the z-axis:

  rotZ θ (x, y, z) := (x cos θ - y sin θ, x sin θ + y cos θ, z)

These are linear, jointly continuous in (θ, v), state-preserving
(preserve z and the disk), bijective (inverse is rotZ (-θ)), and act
transitively on the unit circle of pure states.  Hence the
`StrictConnectedAgency` and `TransitiveAgency` structures both
genuinely populate the framework's positive side.

Status:
  ✓ `circleGPT : GPT (Fin 3 → ℝ)` constructed with full convexity and
    normalization proofs.
  ✓ `rotZ θ` defined and shown to be linear, continuous, state-
    preserving, unit-preserving, bijective.
  ✓ `rotStrictReversible θ : StrictReversible circleGPT`.
  ✓ Affine-θ path `t ↦ rotZ ((1-t) θ₁ + t θ₂)` produces a
    `StrictReversiblePath` between any two `rotStrictReversible`.
  ✓ Transitivity of the rotation family on the parametric pure-state
    circle:  given α₁, α₂, the rotation by `α₂ - α₁` sends
    `(cos α₁, sin α₁, 1)` to `(cos α₂, sin α₂, 1)`.
  ✓ **Pure-state classification (CLOSED).** Both directions are now
    proven by direct convex-analytic argument:
      • `circlePoint_is_pure_state α` (every `circlePoint α` is pure).
      • `pure_state_classification ρ` (every pure state has the form
        `circlePoint α`). Strategy: extremality + nearby-perturbation
        argument forces `ρ 0² + ρ 1² = 1`, then `Real.arccos` produces
        the angle.
  ✓ `circleTransitiveAgency` is now an *unconditional* term —
    `pure_state_classification_holds` discharges the hypothesis.
-/

import Perspectival.GPT
import Perspectival.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval

namespace Perspectival
namespace CircleGPT

open Real

/-! ## Underlying vector space -/

/-- The carrier vector space `V = Fin 3 → ℝ`. -/
abbrev V := Fin 3 → ℝ

/-! ## The unit functional (third-coordinate projection) -/

/-- The unit functional `u(ρ) = ρ 2` (third coordinate). -/
def unitLin : V →ₗ[ℝ] ℝ where
  toFun ρ := ρ 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem unitLin_apply (ρ : V) : unitLin ρ = ρ 2 := rfl

/-! ## States: closed unit disk lifted to z = 1 -/

/-- The state space: vectors `(x, y, 1)` with `x² + y² ≤ 1`. -/
def states : Set V :=
  { ρ : V | ρ 2 = 1 ∧ ρ 0 ^ 2 + ρ 1 ^ 2 ≤ 1 }

theorem mem_states_iff (ρ : V) :
    ρ ∈ states ↔ ρ 2 = 1 ∧ ρ 0 ^ 2 + ρ 1 ^ 2 ≤ 1 := Iff.rfl

/-- States are normalized: `unit ρ = 1`. -/
theorem unit_eq_one_on_states (ρ : V) (hρ : ρ ∈ states) : unitLin ρ = 1 := hρ.1

/-! ### Convexity of the disk -/

/-- Convexity of `x² + y²` along a convex combination: the square of a
weighted sum is at most the weighted sum of squares (Jensen). -/
private theorem sq_add_sq_convex
    (x₁ y₁ x₂ y₂ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 ≤ 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 ≤ 1) :
    (a * x₁ + b * x₂) ^ 2 + (a * y₁ + b * y₂) ^ 2 ≤ 1 := by
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
  have hsum :
      (a * x₁ + b * x₂) ^ 2 + (a * y₁ + b * y₂) ^ 2
        ≤ a * (x₁ ^ 2 + y₁ ^ 2) + b * (x₂ ^ 2 + y₂ ^ 2) := by
    nlinarith [hx, hy]
  have h_le_aplusb :
      a * (x₁ ^ 2 + y₁ ^ 2) + b * (x₂ ^ 2 + y₂ ^ 2) ≤ a + b := by
    have h1 : a * (x₁ ^ 2 + y₁ ^ 2) ≤ a * 1 :=
      mul_le_mul_of_nonneg_left h₁ ha
    have h2 : b * (x₂ ^ 2 + y₂ ^ 2) ≤ b * 1 :=
      mul_le_mul_of_nonneg_left h₂ hb
    linarith
  linarith [hsum.trans h_le_aplusb]

/-- `states` is convex. -/
theorem states_convex : Convex ℝ states := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · show a * ρ₁ 2 + b * ρ₂ 2 = 1
    rw [hρ₁.1, hρ₂.1]; linarith
  · show (a * ρ₁ 0 + b * ρ₂ 0) ^ 2 + (a * ρ₁ 1 + b * ρ₂ 1) ^ 2 ≤ 1
    exact sq_add_sq_convex _ _ _ _ a b ha hb hab hρ₁.2 hρ₂.2

/-! ## Effects -/

/-- The set of valid effects: linear functionals `e : V →ₗ[ℝ] ℝ` with
`0 ≤ e ρ ≤ 1` for every state `ρ`. -/
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

/-- Probabilities lie in [0,1]. -/
theorem prob_in_unit_interval (e : V →ₗ[ℝ] ℝ) (he : e ∈ effects)
    (ρ : V) (hρ : ρ ∈ states) : 0 ≤ e ρ ∧ e ρ ≤ 1 :=
  he ρ hρ

/-! ## The Circle GPT -/

/-- The Circle GPT: closed unit disk lifted to z = 1, with all
[0,1]-bounded linear functionals as effects. -/
def circleGPT : Perspectival.GPT V where
  unit := unitLin
  states := states
  effects := effects
  states_convex := states_convex
  effects_convex := effects_convex
  states_normalized := unit_eq_one_on_states
  prob_in_unit_interval := prob_in_unit_interval
  unit_is_effect := unit_in_effects

/-! ## The rotation `rotZ θ` -/

/-- `rotZ θ : V →ₗ[ℝ] V` is rotation by angle θ around the third axis. -/
noncomputable def rotZ (θ : ℝ) : V →ₗ[ℝ] V where
  toFun ρ := fun i =>
    if i = 0 then ρ 0 * Real.cos θ - ρ 1 * Real.sin θ
    else if i = 1 then ρ 0 * Real.sin θ + ρ 1 * Real.cos θ
    else ρ 2
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
      · -- i = 2.
        have hi2 : i = 2 := by
          fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
        subst hi2
        show ρ 2 + σ 2 = ρ 2 + σ 2
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
      · have hi2 : i = 2 := by
          fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
        subst hi2
        show c * ρ 2 = c • (ρ 2)
        rfl

/-- Explicit coordinate values of `rotZ θ ρ`. -/
@[simp] theorem rotZ_apply_zero (θ : ℝ) (ρ : V) :
    rotZ θ ρ 0 = ρ 0 * Real.cos θ - ρ 1 * Real.sin θ := rfl

@[simp] theorem rotZ_apply_one (θ : ℝ) (ρ : V) :
    rotZ θ ρ 1 = ρ 0 * Real.sin θ + ρ 1 * Real.cos θ := rfl

@[simp] theorem rotZ_apply_two (θ : ℝ) (ρ : V) :
    rotZ θ ρ 2 = ρ 2 := rfl

/-- `rotZ 0 = id`. -/
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
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show ρ 2 = ρ 2
      rfl

/-- The 2D rotation preserves the squared norm in the (x, y) plane. -/
theorem rotZ_preserves_sq_norm (θ : ℝ) (ρ : V) :
    (rotZ θ ρ) 0 ^ 2 + (rotZ θ ρ) 1 ^ 2 = ρ 0 ^ 2 + ρ 1 ^ 2 := by
  rw [rotZ_apply_zero, rotZ_apply_one]
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  nlinarith [hc]

/-- `rotZ θ` preserves the state space. -/
theorem rotZ_preserves_states (θ : ℝ) (ρ : V) (hρ : ρ ∈ states) :
    rotZ θ ρ ∈ states := by
  refine ⟨?_, ?_⟩
  · rw [rotZ_apply_two]; exact hρ.1
  · rw [rotZ_preserves_sq_norm]; exact hρ.2

/-- `rotZ θ` preserves the unit functional. -/
theorem rotZ_preserves_unit (θ : ℝ) :
    unitLin.comp (rotZ θ) = unitLin := by
  apply LinearMap.ext; intro ρ
  show (rotZ θ ρ) 2 = ρ 2
  rfl

/-! ## Continuity of `rotZ` -/

/-- `rotZ θ` is jointly continuous in (θ, ρ). -/
theorem rotZ_continuous_pair :
    Continuous (fun p : ℝ × V => rotZ p.1 p.2) := by
  apply continuous_pi
  intro i
  -- Each coordinate is continuous; handle three cases.
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
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show Continuous (fun p : ℝ × V => p.2 2)
      exact (continuous_apply 2).comp continuous_snd

/-- For each fixed θ, `rotZ θ` is continuous as a map V → V. -/
theorem rotZ_continuous (θ : ℝ) : Continuous (rotZ θ) := by
  -- Rebuild via explicit continuity of components to avoid heavy isDefEq.
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
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show Continuous (fun ρ : V => ρ 2)
      exact continuous_apply 2

/-! ## Bijectivity of `rotZ` via the inverse `rotZ (-θ)` -/

/-- Composition law: `rotZ θ₁ ∘ rotZ θ₂ = rotZ (θ₁ + θ₂)`. -/
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
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show (rotZ θ₁ (rotZ θ₂ ρ)) 2 = (rotZ (θ₁ + θ₂) ρ) 2
      rfl

/-- `rotZ θ` composed with `rotZ (-θ)` is the identity. -/
theorem rotZ_comp_neg (θ : ℝ) :
    (rotZ θ).comp (rotZ (-θ)) = LinearMap.id := by
  rw [rotZ_comp, add_neg_cancel, rotZ_zero]

/-- `rotZ (-θ)` composed with `rotZ θ` is the identity. -/
theorem rotZ_neg_comp (θ : ℝ) :
    (rotZ (-θ)).comp (rotZ θ) = LinearMap.id := by
  rw [rotZ_comp, neg_add_cancel, rotZ_zero]

/-- `rotZ θ` is bijective. -/
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

/-! ## Packaging rotations as `Reversible` and `StrictReversible` -/

/-- `rotZ θ` packaged as a `Reversible circleGPT`. -/
noncomputable def rotReversible (θ : ℝ) :
    Perspectival.Continuity.Reversible circleGPT where
  toLin := rotZ θ
  continuous_toLin := rotZ_continuous θ
  preserves_states := rotZ_preserves_states θ
  preserves_unit := rotZ_preserves_unit θ

/-- `rotZ θ` packaged as a `StrictReversible circleGPT`. -/
noncomputable def rotStrictReversible (θ : ℝ) :
    Perspectival.Continuity.StrictReversible circleGPT where
  toReversible := rotReversible θ
  isEquiv := rotZ_bijective θ

@[simp] theorem rotReversible_toLin (θ : ℝ) :
    (rotReversible θ).toLin = rotZ θ := rfl

@[simp] theorem rotStrictReversible_toLin (θ : ℝ) :
    (rotStrictReversible θ).toLin = rotZ θ := rfl

/-! ## Continuous path of rotations: affine in θ -/

/-- The angular interpolation `(1 - t) θ₁ + t θ₂` as a function of t. -/
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

/-- The rotation path γ(t) := rotZ ((1-t) θ₁ + t θ₂). -/
noncomputable def rotPath (θ₁ θ₂ : ℝ) (t : unitInterval) : V →ₗ[ℝ] V :=
  rotZ (angleInterp θ₁ θ₂ t)

@[simp] theorem rotPath_zero (θ₁ θ₂ : ℝ) :
    rotPath θ₁ θ₂ 0 = rotZ θ₁ := by
  unfold rotPath; rw [angleInterp_zero]

@[simp] theorem rotPath_one (θ₁ θ₂ : ℝ) :
    rotPath θ₁ θ₂ 1 = rotZ θ₂ := by
  unfold rotPath; rw [angleInterp_one]

/-- Joint continuity of `(t, v) ↦ rotPath θ₁ θ₂ t v`. -/
theorem rotPath_continuous (θ₁ θ₂ : ℝ) :
    Continuous (fun p : unitInterval × V => rotPath θ₁ θ₂ p.1 p.2) := by
  -- Reconstruct via explicit coordinate continuities.
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
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show Continuous (fun p : unitInterval × V => p.2 2)
      exact h2c

/-! ## `StrictReversiblePath` between two rotations -/

/-- A continuous path of state-preserving bijective linear maps from
`rotZ θ₁` to `rotZ θ₂`. -/
noncomputable def rotStrictPath (θ₁ θ₂ : ℝ) :
    Perspectival.Continuity.StrictReversiblePath circleGPT
      (rotStrictReversible θ₁) (rotStrictReversible θ₂) where
  γ := rotPath θ₁ θ₂
  continuous := rotPath_continuous θ₁ θ₂
  start := by
    show rotPath θ₁ θ₂ 0 = (rotStrictReversible θ₁).toLin
    rw [rotPath_zero, rotStrictReversible_toLin]
  finish := by
    show rotPath θ₁ θ₂ 1 = (rotStrictReversible θ₂).toLin
    rw [rotPath_one, rotStrictReversible_toLin]
  preserves_states_along := fun t ρ hρ =>
    rotZ_preserves_states (angleInterp θ₁ θ₂ t) ρ hρ
  preserves_unit_along := fun t =>
    rotZ_preserves_unit (angleInterp θ₁ θ₂ t)
  bijective_along := fun t =>
    rotZ_bijective (angleInterp θ₁ θ₂ t)

/-! ## The avail set: all rotations -/

/-- The set of available StrictReversibles: every rotation `rotZ θ`. -/
noncomputable def rotAvail :
    Set (Perspectival.Continuity.StrictReversible circleGPT) :=
  Set.range rotStrictReversible

theorem rot_in_avail (θ : ℝ) : rotStrictReversible θ ∈ rotAvail :=
  ⟨θ, rfl⟩

/-! ### Structure equality lemmas for `Reversible` / `StrictReversible`

The identity `StrictReversible.id circleGPT` equals `rotStrictReversible 0`
at the level of underlying linear maps (both are `LinearMap.id`).  We
extract a structure-equality lemma to bridge the two presentations. -/

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

/-- `rotStrictReversible 0 = StrictReversible.id circleGPT`. -/
theorem rotStrictReversible_zero :
    rotStrictReversible 0 =
      Perspectival.Continuity.StrictReversible.id circleGPT := by
  apply StrictReversible_eq_of_toLin
  show rotZ 0 = LinearMap.id
  exact rotZ_zero

/-- Identity is in the avail set. -/
theorem id_in_rotAvail :
    Perspectival.Continuity.StrictReversible.id circleGPT ∈ rotAvail := by
  refine ⟨0, ?_⟩
  exact rotStrictReversible_zero

/-! ## `StrictConnectedAgency` instance -/

/-- The `StrictConnectedAgency` whose avail set consists of all rotations
around the z-axis. -/
@[reducible]
noncomputable def circleStrictConnectedAgency :
    Perspectival.Continuity.StrictConnectedAgency circleGPT where
  avail := rotAvail
  id_avail := id_in_rotAvail
  strict_paths R₁ R₂ h₁ h₂ := by
    obtain ⟨θ₁, hθ₁⟩ := h₁
    obtain ⟨θ₂, hθ₂⟩ := h₂
    subst hθ₁; subst hθ₂
    exact ⟨rotStrictPath θ₁ θ₂⟩

/-! ## Transitivity on the parametric pure-state circle -/

/-- The parametric pure state on the circle: `circlePoint α = (cos α, sin α, 1)`. -/
noncomputable def circlePoint (α : ℝ) : V := fun i =>
  if i = 0 then Real.cos α
  else if i = 1 then Real.sin α
  else 1

@[simp] theorem circlePoint_apply_zero (α : ℝ) :
    circlePoint α 0 = Real.cos α := rfl

@[simp] theorem circlePoint_apply_one (α : ℝ) :
    circlePoint α 1 = Real.sin α := rfl

@[simp] theorem circlePoint_apply_two (α : ℝ) :
    circlePoint α 2 = 1 := rfl

/-- Every `circlePoint α` is a state of circleGPT. -/
theorem circlePoint_in_states (α : ℝ) : circlePoint α ∈ states := by
  refine ⟨?_, ?_⟩
  · show circlePoint α 2 = 1; rfl
  · show (circlePoint α) 0 ^ 2 + (circlePoint α) 1 ^ 2 ≤ 1
    rw [circlePoint_apply_zero, circlePoint_apply_one,
        Real.cos_sq_add_sin_sq]

/-- Rotation acts on `circlePoint` by translating the angle:
`rotZ θ (circlePoint α) = circlePoint (α + θ)`. -/
theorem rotZ_circlePoint (θ α : ℝ) :
    rotZ θ (circlePoint α) = circlePoint (α + θ) := by
  funext i
  by_cases h0 : i = 0
  · subst h0
    -- (rotZ θ (cos α, sin α, 1)) 0 = cos α · cos θ - sin α · sin θ = cos (α + θ).
    show rotZ θ (circlePoint α) 0 = circlePoint (α + θ) 0
    rw [rotZ_apply_zero, circlePoint_apply_zero, circlePoint_apply_one,
        circlePoint_apply_zero, Real.cos_add]
  · by_cases h1 : i = 1
    · subst h1
      show rotZ θ (circlePoint α) 1 = circlePoint (α + θ) 1
      rw [rotZ_apply_one, circlePoint_apply_zero, circlePoint_apply_one,
          circlePoint_apply_one, Real.sin_add]
      ring
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl h0) | (exact absurd rfl h1)
      subst hi2
      show rotZ θ (circlePoint α) 2 = circlePoint (α + θ) 2
      rw [rotZ_apply_two, circlePoint_apply_two, circlePoint_apply_two]

/-- **Transitivity on the parametric pure-state circle.**  For any
α₁, α₂, the rotation `rotZ (α₂ - α₁)` sends `circlePoint α₁` to
`circlePoint α₂`. -/
theorem rotZ_transitive_on_circlePoints (α₁ α₂ : ℝ) :
    rotZ (α₂ - α₁) (circlePoint α₁) = circlePoint α₂ := by
  rw [rotZ_circlePoint]
  congr 1
  ring

/-- The transitivity result lifted to `StrictReversible`-with-membership form. -/
theorem rotAvail_transitive_on_circlePoints (α₁ α₂ : ℝ) :
    ∃ R ∈ rotAvail, R.toLin (circlePoint α₁) = circlePoint α₂ := by
  refine ⟨rotStrictReversible (α₂ - α₁), rot_in_avail (α₂ - α₁), ?_⟩
  show rotZ (α₂ - α₁) (circlePoint α₁) = circlePoint α₂
  exact rotZ_transitive_on_circlePoints α₁ α₂

/-! ## Pure-state classification for the Circle GPT

The full `TransitiveAgency circleGPT` instance requires the pure-state
classification: every `PureState circleGPT ρ` satisfies `ρ = circlePoint α`
for some `α`.

This section proves both directions:

  ✓ `circlePoint_is_pure_state` (easy direction): every `circlePoint α`
    is a pure state. Uses strict convexity of `x ↦ x²` directly.
  ✓ `pure_state_classification` (the hard direction): every pure state
    equals some `circlePoint α`. Proof: extremality + boundary argument
    forces `ρ 0² + ρ 1² = 1` (a strict-interior point can be written as
    the midpoint of two distinct nearby states), then `Real.arccos`
    produces the angle.

Together these close the deferred lemma. -/

/-- **Helper.** A point on the unit circle is `(cos α, sin α)` for some α.
Specifically, given `x² + y² = 1` with `x, y ∈ ℝ`, the angle
`α = arccos x` (if `y ≥ 0`) or `α = -arccos x` (if `y < 0`) works. -/
theorem exists_angle_of_unit_circle (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    ∃ α : ℝ, x = Real.cos α ∧ y = Real.sin α := by
  -- |x| ≤ 1 follows from x² ≤ x² + y² = 1.
  have hx_le : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
  have hxneg : -1 ≤ x := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  have hxpos : x ≤ 1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  -- y² = 1 - x²
  have hy_sq : y ^ 2 = 1 - x ^ 2 := by linarith
  by_cases hy : 0 ≤ y
  · -- y ≥ 0: take α = arccos x.
    refine ⟨Real.arccos x, ?_, ?_⟩
    · exact (Real.cos_arccos hxneg hxpos).symm
    · -- sin (arccos x) = √(1 - x²) = √(y²) = |y| = y.
      rw [Real.sin_arccos]
      rw [← hy_sq]
      rw [Real.sqrt_sq_eq_abs]
      exact (abs_of_nonneg hy).symm
  · -- y < 0: take α = -arccos x.
    have hy_neg : y < 0 := lt_of_not_ge hy
    refine ⟨-(Real.arccos x), ?_, ?_⟩
    · rw [Real.cos_neg]
      exact (Real.cos_arccos hxneg hxpos).symm
    · rw [Real.sin_neg, Real.sin_arccos]
      rw [← hy_sq]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg hy_neg]
      ring

/-! ### Easy direction: every `circlePoint α` is a pure state -/

/-- **Easy direction:** every parametric point `circlePoint α` is a
pure state of the Circle GPT. -/
theorem circlePoint_is_pure_state (α : ℝ) :
    Perspectival.Continuity.PureState circleGPT (circlePoint α) := by
  refine ⟨circlePoint_in_states α, ?_, ?_⟩
  · -- {circlePoint α} ⊆ states
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact circlePoint_in_states α
  · -- Open-segment endpoints lie in {circlePoint α}.
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hxy⟩
    rw [Set.mem_singleton_iff] at hz
    rw [Set.mem_singleton_iff]
    -- z = circlePoint α = a • x + b • y; want x = circlePoint α.
    -- Both x and y are in states.
    have hxa : (a * x 0 + b * y 0) ^ 2 + (a * x 1 + b * y 1) ^ 2 ≤ 1 :=
      sq_add_sq_convex (x 0) (x 1) (y 0) (y 1) a b ha.le hb.le hab
        hx.2 hy.2
    -- (a * x 0 + b * y 0, a * x 1 + b * y 1, a * x 2 + b * y 2) = circlePoint α
    have h0 : a * x 0 + b * y 0 = Real.cos α := by
      have hh := congr_fun hxy 0
      have hz0 : z 0 = Real.cos α := by rw [hz]; rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [hz0] at hh
      linarith
    have h1 : a * x 1 + b * y 1 = Real.sin α := by
      have hh := congr_fun hxy 1
      have hz1 : z 1 = Real.sin α := by rw [hz]; rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [hz1] at hh
      linarith
    -- ‖a x + b y‖² = 1 (since z = circlePoint α lies on the unit circle).
    have hnormeq : (a * x 0 + b * y 0) ^ 2 + (a * x 1 + b * y 1) ^ 2 = 1 := by
      rw [h0, h1, Real.cos_sq_add_sin_sq]
    -- We have ‖a x + b y‖² ≤ a ‖x‖² + b ‖y‖² ≤ a · 1 + b · 1 = 1.
    -- Equality forces both inequalities to be equalities.
    -- Specifically Jensen-equality (a ≠ 0, b ≠ 0) ⇒ x 0 = y 0 ∧ x 1 = y 1.
    -- Direct computation: a*b*((x 0 - y 0)² + (x 1 - y 1)²) = 0.
    have hjensen :
        a * (x 0 ^ 2 + x 1 ^ 2) + b * (y 0 ^ 2 + y 1 ^ 2)
          - ((a * x 0 + b * y 0) ^ 2 + (a * x 1 + b * y 1) ^ 2)
        = a * b * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
      have hb_eq : b = 1 - a := by linarith
      rw [hb_eq]; ring
    have h_xsq : x 0 ^ 2 + x 1 ^ 2 ≤ 1 := hx.2
    have h_ysq : y 0 ^ 2 + y 1 ^ 2 ≤ 1 := hy.2
    -- a · (x 0² + x 1²) + b · (y 0² + y 1²) ≤ a + b = 1.
    have h_upper :
        a * (x 0 ^ 2 + x 1 ^ 2) + b * (y 0 ^ 2 + y 1 ^ 2) ≤ 1 := by
      have h1' : a * (x 0 ^ 2 + x 1 ^ 2) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left h_xsq ha.le
      have h2' : b * (y 0 ^ 2 + y 1 ^ 2) ≤ b * 1 :=
        mul_le_mul_of_nonneg_left h_ysq hb.le
      linarith
    -- Combined: a*b*((x 0 - y 0)² + (x 1 - y 1)²) ≤ 0.
    have hle_zero : a * b * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) ≤ 0 := by
      linarith [hnormeq]
    -- But a*b > 0 and ((x 0 - y 0)² + (x 1 - y 1)²) ≥ 0, so it must equal 0.
    have hab_pos : 0 < a * b := mul_pos ha hb
    have hsum_zero : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 0 := by
      have h_nn : 0 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
        have := sq_nonneg (x 0 - y 0)
        have := sq_nonneg (x 1 - y 1)
        linarith
      have hprod : a * b * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) = 0 := by
        have hnonneg : 0 ≤ a * b * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) :=
          mul_nonneg hab_pos.le h_nn
        linarith
      have hcancel := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hab_pos)
      exact hcancel
    -- Thus (x 0 - y 0)² = 0 and (x 1 - y 1)² = 0.
    have h0_eq : x 0 = y 0 := by
      have : (x 0 - y 0) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      have hzero : x 0 - y 0 = 0 := by
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
      linarith
    have h1_eq : x 1 = y 1 := by
      have : (x 1 - y 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      have hzero : x 1 - y 1 = 0 := by
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
      linarith
    -- Also x 2 = 1 = y 2 (from state membership).
    have h2_eq : x 2 = y 2 := by rw [hx.1, hy.1]
    -- Now compute x = circlePoint α.
    -- a x 0 + b y 0 = cos α, x 0 = y 0 ⇒ x 0 = cos α (since a + b = 1).
    have h0x : x 0 = Real.cos α := by
      have : a * x 0 + b * y 0 = (a + b) * x 0 := by rw [h0_eq]; ring
      rw [hab, one_mul] at this
      linarith [h0]
    have h1x : x 1 = Real.sin α := by
      have : a * x 1 + b * y 1 = (a + b) * x 1 := by rw [h1_eq]; ring
      rw [hab, one_mul] at this
      linarith [h1]
    funext i
    by_cases hi0 : i = 0
    · subst hi0
      show x 0 = circlePoint α 0
      rw [h0x]; rfl
    · by_cases hi1 : i = 1
      · subst hi1
        show x 1 = circlePoint α 1
        rw [h1x]; rfl
      · have hi2 : i = 2 := by
          fin_cases i <;> first | rfl | (exact absurd rfl hi0) | (exact absurd rfl hi1)
        subst hi2
        show x 2 = circlePoint α 2
        rw [hx.1]; rfl

/-! ### Hard direction: every pure state is a `circlePoint` -/

/-- **Helper.** Any state ρ with `ρ 0² + ρ 1² < 1` is NOT extreme:
we can write ρ as the midpoint of two distinct nearby states obtained
by perturbing the first coordinate. -/
private theorem state_interior_not_extreme
    (ρ : V) (hρ : ρ ∈ states) (hint : ρ 0 ^ 2 + ρ 1 ^ 2 < 1) :
    ¬ IsExtreme ℝ states {ρ} := by
  intro hext
  -- Pick ε := min(1, (1 - ρ 0² - ρ 1²)/(2 · |ρ 0| + 1)) > 0.
  -- We then construct two perturbed states whose midpoint is ρ but
  -- which differ from ρ.
  set c : ℝ := 1 - ρ 0 ^ 2 - ρ 1 ^ 2 with hc_def
  have hc_pos : 0 < c := by simp only [hc_def]; linarith
  set δ : ℝ := min 1 (c / (2 * |ρ 0| + 2)) with hδ_def
  have h_denom_pos : 0 < 2 * |ρ 0| + 2 := by
    have := abs_nonneg (ρ 0); linarith
  have hδ_pos : 0 < δ := by
    simp only [hδ_def]
    exact lt_min (by norm_num) (div_pos hc_pos h_denom_pos)
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_quot : δ ≤ c / (2 * |ρ 0| + 2) := min_le_right _ _
  -- Define x⁺ = (ρ 0 + δ, ρ 1, 1) and x⁻ = (ρ 0 - δ, ρ 1, 1).
  let xp : V := fun i => if i = 0 then ρ 0 + δ else if i = 1 then ρ 1 else 1
  let xm : V := fun i => if i = 0 then ρ 0 - δ else if i = 1 then ρ 1 else 1
  have hxp0 : xp 0 = ρ 0 + δ := by show (if (0:Fin 3) = 0 then _ else _) = _; rfl
  have hxp1 : xp 1 = ρ 1 := by
    show (if (1:Fin 3) = 0 then ρ 0 + δ else if (1:Fin 3) = 1 then ρ 1 else 1) = ρ 1
    simp
  have hxp2 : xp 2 = 1 := by
    show (if (2:Fin 3) = 0 then ρ 0 + δ else if (2:Fin 3) = 1 then ρ 1 else 1) = 1
    rfl
  have hxm0 : xm 0 = ρ 0 - δ := by show (if (0:Fin 3) = 0 then _ else _) = _; rfl
  have hxm1 : xm 1 = ρ 1 := by
    show (if (1:Fin 3) = 0 then ρ 0 - δ else if (1:Fin 3) = 1 then ρ 1 else 1) = ρ 1
    simp
  have hxm2 : xm 2 = 1 := by
    show (if (2:Fin 3) = 0 then ρ 0 - δ else if (2:Fin 3) = 1 then ρ 1 else 1) = 1
    rfl
  -- Show both xp, xm ∈ states. Bound (ρ 0 ± δ)² ≤ ρ 0² + 2|ρ 0|δ + δ².
  have h_bound : ∀ s : ℝ, s = δ ∨ s = -δ →
      (ρ 0 + s) ^ 2 + ρ 1 ^ 2 ≤ 1 := by
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
    -- (ρ 0 + s)² + ρ 1² ≤ ρ 0² + 2|ρ 0|δ + δ² + ρ 1² = (1 - c) + 2|ρ 0|δ + δ².
    -- δ ≤ c / (2|ρ 0| + 2), and δ ≤ 1. So 2|ρ 0|δ + δ² ≤ 2|ρ 0|δ + δ
    -- ≤ (2|ρ 0| + 1)·δ ≤ (2|ρ 0| + 2)·δ ≤ c.
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
    -- Now combine.
    have : (ρ 0 + s) ^ 2 + ρ 1 ^ 2 ≤ ρ 0 ^ 2 + 2 * |ρ 0| * δ + δ ^ 2 + ρ 1 ^ 2 := by
      rw [h_expand]
      linarith
    have : (ρ 0 + s) ^ 2 + ρ 1 ^ 2 ≤ ρ 0 ^ 2 + ρ 1 ^ 2 + c := by linarith
    have hc_relation : ρ 0 ^ 2 + ρ 1 ^ 2 + c = 1 := by simp only [hc_def]; ring
    linarith
  have hxp_in : xp ∈ states := by
    refine ⟨?_, ?_⟩
    · rw [mem_states_iff] at hρ; rw [hxp2]
    · rw [hxp0, hxp1]
      have h := h_bound δ (Or.inl rfl)
      linarith
  have hxm_in : xm ∈ states := by
    refine ⟨?_, ?_⟩
    · rw [hxm2]
    · rw [hxm0, hxm1]
      have h := h_bound (-δ) (Or.inr rfl)
      have h_neg : (ρ 0 - δ) = (ρ 0 + (-δ)) := by ring
      rw [h_neg]
      linarith
  -- Compute the midpoint: (1/2) · xp + (1/2) · xm = ρ.
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
      · have hi2 : i = 2 := by
          fin_cases i <;> first | rfl | (exact absurd rfl hi0) | (exact absurd rfl hi1)
        subst hi2
        show (1 / 2 : ℝ) * xp 2 + (1 / 2 : ℝ) * xm 2 = ρ 2
        rw [hxp2, hxm2, hρ.1]; ring
  -- ρ ∈ openSegment ℝ xp xm.
  have h_in_open_seg : ρ ∈ openSegment ℝ xp xm :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, h_mid⟩
  -- By extremality of {ρ}, xp ∈ {ρ}, i.e., xp = ρ.
  have hxp_eq : xp ∈ ({ρ} : Set V) :=
    hext.left_mem_of_mem_openSegment hxp_in hxm_in (Set.mem_singleton _)
      h_in_open_seg
  rw [Set.mem_singleton_iff] at hxp_eq
  -- But xp 0 = ρ 0 + δ ≠ ρ 0 since δ > 0.
  have hxp0_eq : xp 0 = ρ 0 := by rw [hxp_eq]
  rw [hxp0] at hxp0_eq
  linarith

/-- **Hard direction:** every pure state of the Circle GPT equals
some `circlePoint α`. -/
theorem pure_state_classification (ρ : V)
    (hρ_pure : Perspectival.Continuity.PureState circleGPT ρ) :
    ∃ α : ℝ, ρ = circlePoint α := by
  obtain ⟨hρ_st, hρ_ext⟩ := hρ_pure
  have hρ2 : ρ 2 = 1 := hρ_st.1
  have hρ_le : ρ 0 ^ 2 + ρ 1 ^ 2 ≤ 1 := hρ_st.2
  -- Show ρ 0² + ρ 1² = 1 by ruling out the strict case.
  have hρ_eq : ρ 0 ^ 2 + ρ 1 ^ 2 = 1 := by
    rcases lt_or_eq_of_le hρ_le with hlt | heq
    · exfalso
      exact state_interior_not_extreme ρ hρ_st hlt hρ_ext
    · exact heq
  -- Apply exists_angle.
  obtain ⟨α, hcos, hsin⟩ := exists_angle_of_unit_circle (ρ 0) (ρ 1) hρ_eq
  refine ⟨α, ?_⟩
  funext i
  by_cases hi0 : i = 0
  · subst hi0
    show ρ 0 = circlePoint α 0
    rw [hcos]; rfl
  · by_cases hi1 : i = 1
    · subst hi1
      show ρ 1 = circlePoint α 1
      rw [hsin]; rfl
    · have hi2 : i = 2 := by
        fin_cases i <;> first | rfl | (exact absurd rfl hi0) | (exact absurd rfl hi1)
      subst hi2
      show ρ 2 = circlePoint α 2
      rw [hρ2]; rfl

/-- **Pure-state classification (statement form).** Combining
`pure_state_classification` directly: every pure state of `circleGPT`
arises as `circlePoint α` for some α. -/
def pure_state_classification_statement : Prop :=
  ∀ ρ : V, Perspectival.Continuity.PureState circleGPT ρ →
    ∃ α : ℝ, ρ = circlePoint α

/-- **The classification holds.** This closes the previously-deferred
lemma. -/
theorem pure_state_classification_holds :
    pure_state_classification_statement :=
  pure_state_classification

/-! ## `TransitiveAgency`, parameterized by the deferred classification -/

/-- **Full `TransitiveAgency circleGPT`, modulo pure-state classification.**

Given the pure-state classification `h_pure` (DEFERRED-LEMMA above),
the rotations form a `TransitiveAgency` on the Circle GPT. -/
@[reducible]
noncomputable def circleTransitiveAgency
    (h_pure : pure_state_classification_statement) :
    Perspectival.Continuity.TransitiveAgency circleGPT where
  toStrictConnectedAgency := circleStrictConnectedAgency
  transitive_on_pure := by
    intro ρ₁ ρ₂ hp₁ hp₂
    obtain ⟨α₁, hα₁⟩ := h_pure ρ₁ hp₁
    obtain ⟨α₂, hα₂⟩ := h_pure ρ₂ hp₂
    obtain ⟨R, hR, hRρ⟩ := rotAvail_transitive_on_circlePoints α₁ α₂
    refine ⟨R, hR, ?_⟩
    rw [hα₁, hα₂]
    exact hRρ

/-- The avail set is nonempty. -/
theorem rotAvail_nonempty : rotAvail.Nonempty := ⟨_, id_in_rotAvail⟩

/-- **Unconditional `TransitiveAgency circleGPT`** — discharges the
deferred classification hypothesis via `pure_state_classification_holds`. -/
@[reducible]
noncomputable def circleTransitiveAgency_unconditional :
    Perspectival.Continuity.TransitiveAgency circleGPT :=
  circleTransitiveAgency pure_state_classification_holds

/-! ## Summary

This file establishes a NON-DEGENERATE positive example complementing
the `Perspectival.Classical.classical_n2_no_transitive_agency` no-go:
the Circle GPT carries a `StrictConnectedAgency` whose avail set
(`rotAvail`) genuinely contains a 1-parameter continuous family of
StrictReversibles acting transitively on the parametric pure-state
circle.  The full `TransitiveAgency` instance follows once the pure-
state classification (`pure_state_classification_statement`,
DEFERRED-LEMMA) is supplied.

Key declarations:
  • `circleGPT : GPT V` — the lifted-disk GPT.
  • `rotZ θ : V →ₗ[ℝ] V` — rotation around the z-axis.
  • `rotZ_preserves_states`, `rotZ_preserves_unit`, `rotZ_bijective`,
    `rotZ_continuous_pair`.
  • `rotStrictReversible θ : StrictReversible circleGPT`.
  • `rotStrictPath θ₁ θ₂ : StrictReversiblePath …` — affine-θ path.
  • `circleStrictConnectedAgency : StrictConnectedAgency circleGPT`.
  • `circlePoint α : V`  and  `rotZ_transitive_on_circlePoints`.
  • `circleTransitiveAgency h_pure : TransitiveAgency circleGPT`,
    modulo the deferred pure-state classification.
-/

/-! ## Cardinality observations: rotAvail is non-trivial -/

/-- `rotZ π` is not the identity: it sends (1, 0, 1) to (-1, 0, 1). -/
theorem rotZ_pi_ne_id : rotZ Real.pi ≠ LinearMap.id := by
  intro h
  -- Apply both sides to (1, 0, 1).
  have hpt : rotZ Real.pi (fun i => if i = 0 then (1 : ℝ) else if i = 1 then 0 else 1)
            = (fun i => if i = 0 then (1 : ℝ) else if i = 1 then 0 else 1) := by
    rw [h]; rfl
  -- (rotZ π) at index 0 sends 1 to -1, not 1.
  have hzero : rotZ Real.pi (fun i => if i = 0 then (1 : ℝ) else if i = 1 then 0 else 1) 0
             = -1 := by
    rw [rotZ_apply_zero]
    show 1 * Real.cos Real.pi - 0 * Real.sin Real.pi = -1
    rw [Real.cos_pi]; ring
  have hzero_id : (fun i : Fin 3 => if i = 0 then (1 : ℝ) else if i = 1 then 0 else 1) 0
                = 1 := by
    show (if (0 : Fin 3) = 0 then (1 : ℝ) else if (0 : Fin 3) = 1 then 0 else 1) = 1
    simp
  have : (-1 : ℝ) = 1 := by rw [← hzero, hpt, hzero_id]
  norm_num at this

/-- `rotStrictReversible π` is not the identity StrictReversible. -/
theorem rotStrictReversible_pi_ne_id :
    rotStrictReversible Real.pi ≠ Perspectival.Continuity.StrictReversible.id circleGPT := by
  intro h
  have := congrArg (fun (R : Perspectival.Continuity.StrictReversible circleGPT) => R.toLin) h
  -- (rotStrictReversible π).toLin = rotZ π; (id).toLin = LinearMap.id.
  simp [rotStrictReversible_toLin] at this
  exact rotZ_pi_ne_id this

/-- **CircleGPT has at least two distinct elements in `rotAvail`** —
the identity and the 180° rotation. This shows the avail set is
non-trivial (not just `{id}`). -/
theorem rotAvail_has_two_distinct :
    ∃ R₁ R₂ : Perspectival.Continuity.StrictReversible circleGPT,
      R₁ ∈ rotAvail ∧ R₂ ∈ rotAvail ∧ R₁ ≠ R₂ := by
  refine ⟨Perspectival.Continuity.StrictReversible.id circleGPT,
          rotStrictReversible Real.pi,
          ?_, rot_in_avail Real.pi, ?_⟩
  · -- id = rotStrictReversible 0 ∈ rotAvail
    rw [← rotStrictReversible_zero]
    exact rot_in_avail 0
  · -- id ≠ rotStrictReversible π
    intro h
    exact rotStrictReversible_pi_ne_id h.symm

end CircleGPT
end Perspectival
