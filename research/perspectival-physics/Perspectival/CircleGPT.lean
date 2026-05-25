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
  ▲ The full `TransitiveAgency circleGPT` instance further requires a
    pure-state CLASSIFICATION lemma:  every extreme point of the disk-
    states is of the form `(cos α, sin α, 1)`.  This is the standard
    `extremePoints_closedBall_eq_sphere` result transported through the
    `z = 1` lift; we record the supporting facts but DEFER the final
    `IsExtreme` characterization to a later session (marked
    `DEFERRED-LEMMA` below).
-/

import Perspectival.GPT
import Perspectival.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Basic
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

/-! ## DEFERRED-LEMMA: pure-state classification

The full `TransitiveAgency circleGPT` instance requires showing that
every `Perspectival.Continuity.PureState circleGPT ρ` implies
`ρ = circlePoint α` for some α — i.e., that the extreme points of the
lifted closed unit disk are exactly the lifted unit circle.

Proof sketch:
  • Extreme points of `states = {(x,y,1) : x²+y² ≤ 1}` correspond
    bijectively to extreme points of `{(x,y) : x²+y² ≤ 1}` ⊂ ℝ² via
    the projection `(x,y,1) ↔ (x,y)`.
  • Mathlib's `StrictConvexSpace.extremePoints_closedBall_eq_sphere`
    (Analysis.Convex.Strict.Extreme) identifies the latter as the
    Euclidean unit circle.
  • Every point of the Euclidean unit circle equals `(cos α, sin α)`
    for some α.

This file proves the PARAMETRIC direction
(`rotAvail_transitive_on_circlePoints`); the deferred direction is
`PureState ρ → ∃ α, ρ = circlePoint α`. -/

/-- **Pure-state classification (statement, deferred proof).** -/
def pure_state_classification_statement : Prop :=
  ∀ ρ : V, Perspectival.Continuity.PureState circleGPT ρ →
    ∃ α : ℝ, ρ = circlePoint α

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

end CircleGPT
end Perspectival
