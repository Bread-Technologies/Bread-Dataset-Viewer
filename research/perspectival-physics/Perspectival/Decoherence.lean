/-
Perspectival Physics — Decoherence (Seam 4)
==============================================

The framework's formal correlate of the decoherence seam: a Tier B
phenomenon (exponential suppression of off-diagonal density-matrix
elements) understood as the accumulated effect of many small
Tier A actualization events at the system-environment interface.

Per `SEAMS.md` Seam 4: decoherence rates depend on the
"actualization density" of the environment, not just statistical
properties. This module formalizes the count-based content via
`RealityChain'.actualizationDensity` from `TierB.lean`.

## Key results (count-based structural level)

- `actualizationRate` : the (count, length) rate measure.
- `coherent_regime` : count = 0 → rate (0, length).
- `decoherence_regime` : bracketed = 0 → rate (length, length).
- `concatenated_decoherence` : rate composes coordinate-wise.
- `coherent_compose` : coherent + coherent → coherent.
- `coherent_and_decoherent_distinct_endpoints` : trajectories with
  same endpoints have trajectory-independent coherence status
  (via the strict-chain iff).
- `decoherence_certificate` : bundle of the four core facts.

## What's NOT formalized here

- The Tier B exponential-suppression dynamics (requires
  Mathlib's analysis-of-decoherence-time machinery).
- The system-environment factor structure (requires
  `gptTensor` + a partial-trace operation).
- Quantitative predictions of decoherence rates.

This module records the structural shadow + cites the entropy
addendum + SEAMS.md for the broader framing.
-/

import Perspectival.TierA
import Perspectival.TierB

namespace Perspectival
namespace Decoherence

open TierA
open TierB

universe u v

/-! ## Actualization rate

The framework's reading: decoherence happens at the rate at which
actualization events accumulate at the system-environment interface.
A high actualization rate corresponds to fast decoherence; a low
rate corresponds to coherent (Tier-B-isolated) dynamics. -/

/-- **The actualization rate along a strict chain.** Encoded as the
ratio (count, length) — the trajectory-relative seam-crossing rate. -/
def actualizationRate {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂) : ℕ × ℕ :=
  ch.actualizationDensity

/-- **Coherent regime: zero rate.** A chain with no actualizations has
rate (0, length) — the system stays in the bracketed (Tier B)
reversible-limit regime. -/
theorem coherent_regime {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂)
    (h : ch.actualizationCount = 0) :
    actualizationRate ch = (0, ch.length) := by
  show ch.actualizationDensity = (0, ch.length)
  exact RealityChain'.bare_tier_B_density ch h

/-- **Decoherence regime: maximal rate.** A chain with no bracketed
steps has rate (length, length) — every step crosses a seam. Maximal
decoherence per step. -/
theorem decoherence_regime {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂)
    (h : ch.bracketedCount = 0) :
    actualizationRate ch = (ch.length, ch.length) := by
  show ch.actualizationDensity = (ch.length, ch.length)
  exact RealityChain'.pure_actualization_density ch h

/-! ## Compositional content

Decoherence rates compose additively under trajectory concatenation:
running two trajectories in sequence accumulates their actualization
counts and lengths. This is the framework's "decoherence is path-
dependent and additive" content at the structural level. -/

/-- **Additivity of the rate's numerator (actualization count).** -/
theorem rate_count_additive {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃) :
    (actualizationRate (ch₁.append ch₂)).1
      = (actualizationRate ch₁).1 + (actualizationRate ch₂).1 :=
  RealityChain'.append_actualizationDensity_count ch₁ ch₂

/-- **Additivity of the rate's denominator (length).** -/
theorem rate_length_additive {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃) :
    (actualizationRate (ch₁.append ch₂)).2
      = (actualizationRate ch₁).2 + (actualizationRate ch₂).2 :=
  RealityChain'.append_actualizationDensity_length ch₁ ch₂

/-! ## Empirical signature (sketch)

The framework's prediction per Seam 4: environments rich in Tier A
content (lots of actualization events) decohere systems faster than
statistical models predict. This is testable in principle by
measuring decoherence rates as a function of environmental
actualization density — though "actualization density" needs an
operational proxy (e.g., interaction rate with macroscopic apparatus).

The full quantitative content requires:
  • A `Decoherence.lean` extension with exponential-suppression dynamics.
  • Operational definitions of "environment Tier A density".
  • Connection to standard decoherence-time calculations.

These are deferred. The current module records the structural shadow:
the framework's read of decoherence is via actualization-count
accumulation, not statistical-mechanical postulates.
-/

/-! ## Worked examples -/

/-- **Example: a pure actualization trajectory's rate.** Using
`actualizeAt_strict_step` to build a 1-step actualization chain
and verifying its rate is (1, 1) — maximal seam crossing per step. -/
example (P : Type u) (C : Type v)
    [DecidableEq (TierA.Meeting P C)] (R : TierA.Reality P C)
    (m : TierA.Meeting P C) (h_pot : R m = TierA.MeetingStatus.Potential) :
    actualizationRate
      (RealityChain'.singleton
        (TierB.actualizeAt_strict_step R m h_pot)) = (1, 1) := by
  show RealityChain'.actualizationDensity _ = (1, 1)
  show (RealityChain'.actualizationCount _, RealityChain'.length _) = (1, 1)
  refine Prod.ext ?_ ?_
  · -- actualizationCount = 1.
    rw [RealityChain'.singleton_actualizationCount]
    rfl
  · -- length = 1.
    exact RealityChain'.singleton_length_eq_one _

/-- **Example: a refl-bracketed trajectory's rate is (0, 1).** Pure
Tier B inter-event evolution, no decoherence. -/
example (P : Type u) (C : Type v) (R : Reality P C) :
    actualizationRate
      (RealityChain'.singleton
        (TierB.TrajectoryStep'.bracketed (TierB.bracketed_refl R))) = (0, 1) := by
  show RealityChain'.actualizationDensity _ = (0, 1)
  show (RealityChain'.actualizationCount _, RealityChain'.length _) = (0, 1)
  refine Prod.ext ?_ ?_
  · rw [RealityChain'.singleton_actualizationCount]; rfl
  · exact RealityChain'.singleton_length_eq_one _

/-- **Concatenated decoherence: composing two decoherence trajectories
adds their rates.** A direct corollary of rate_count_additive and
rate_length_additive — running two trajectories in sequence
accumulates both their seam-crossing counts and their lengths. -/
theorem concatenated_decoherence {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃) :
    actualizationRate (ch₁.append ch₂)
      = ((actualizationRate ch₁).1 + (actualizationRate ch₂).1,
         (actualizationRate ch₁).2 + (actualizationRate ch₂).2) := by
  refine Prod.ext ?_ ?_
  · exact rate_count_additive ch₁ ch₂
  · exact rate_length_additive ch₁ ch₂

/-- **Concatenating coherent + decoherent regimes.** If ch₁ has zero
actualizations (coherent regime) and ch₂ has zero bracketed steps
(decoherent regime), the composite chain has rate
(ch₂.length, ch₁.length + ch₂.length). The coherent part contributes
only to the length; the decoherent part contributes to both. -/
theorem coherent_plus_decoherent {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃)
    (h₁ : ch₁.actualizationCount = 0)
    (h₂ : ch₂.bracketedCount = 0) :
    actualizationRate (ch₁.append ch₂) = (ch₂.length, ch₁.length + ch₂.length) := by
  rw [concatenated_decoherence]
  -- actualizationRate ch₁ = (0, ch₁.length).
  have h_co₁ := coherent_regime ch₁ h₁
  -- actualizationRate ch₂ = (ch₂.length, ch₂.length).
  have h_deco₂ := decoherence_regime ch₂ h₂
  rw [h_co₁, h_deco₂]; simp

/-- **Reverse: decoherent + coherent.** Symmetric composition gives
rate (ch₁.length, ch₁.length + ch₂.length). The decoherent part
contributes its actualizations early; the coherent tail extends
length only. -/
theorem decoherent_plus_coherent {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃)
    (h₁ : ch₁.bracketedCount = 0)
    (h₂ : ch₂.actualizationCount = 0) :
    actualizationRate (ch₁.append ch₂) = (ch₁.length, ch₁.length + ch₂.length) := by
  rw [concatenated_decoherence]
  have h_deco₁ := decoherence_regime ch₁ h₁
  have h_co₂ := coherent_regime ch₂ h₂
  rw [h_deco₁, h_co₂]; simp

/-! ## Rate bounds

The actualization rate is bounded by the trivial bounds 0 ≤ count ≤ length. -/

/-- **Rate's count is non-negative.** Trivial since it's a `ℕ`. -/
theorem rate_count_nonneg {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂) :
    0 ≤ (actualizationRate ch).1 := Nat.zero_le _

/-- **Rate's count is bounded above by length.** -/
theorem rate_count_le_length {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂) :
    (actualizationRate ch).1 ≤ (actualizationRate ch).2 := by
  show ch.actualizationCount ≤ ch.length
  exact ch.actualizationCount_le_length

-- (Concrete two-actualization Bool example deferred — the strict
-- chain construction works but the proof had subtle goal-reduction
-- issues. The abstract `concatenated_decoherence` + `coherent_plus_decoherent`
-- + `decoherent_plus_coherent` theorems above provide the composable
-- machinery; instantiating on concrete types is a downstream exercise.)

/-- **Plain-chain version of actualization rate.** For RealityChain
(not strict), we use the plain count machinery. -/
def actualizationRatePlain {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂) : ℕ × ℕ :=
  (ch.actualizationCount, ch.length)

/-- **Forgetful map preserves rate.** -/
theorem actualizationRate_forget {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂) :
    actualizationRate ch = actualizationRatePlain ch.toRealityChain := by
  show (ch.actualizationCount, ch.length)
      = (ch.toRealityChain.actualizationCount, ch.toRealityChain.length)
  refine Prod.ext ?_ ?_
  · exact (RealityChain'.toRealityChain_actualizationCount ch).symm
  · exact (RealityChain'.toRealityChain_length ch).symm

/-- **Plain-chain coherent regime: same as strict.** -/
theorem coherent_regime_plain {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂)
    (h : ch.actualizationCount = 0) :
    actualizationRatePlain ch = (0, ch.length) := by
  show (ch.actualizationCount, ch.length) = (0, ch.length)
  rw [h]

/-- **Plain-chain decoherence regime: same as strict.** -/
theorem decoherence_regime_plain {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂)
    (h : ch.bracketedCount = 0) :
    actualizationRatePlain ch = (ch.length, ch.length) := by
  show (ch.actualizationCount, ch.length) = (ch.length, ch.length)
  have h_sum := ch.counts_sum
  rw [h] at h_sum
  rw [← h_sum]; simp

/-- **Plain-chain rate compositional under append.** -/
theorem actualizationRatePlain_append {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain P C R₁ R₂) (ch₂ : RealityChain P C R₂ R₃) :
    actualizationRatePlain (ch₁.append ch₂)
      = ((actualizationRatePlain ch₁).1 + (actualizationRatePlain ch₂).1,
         (actualizationRatePlain ch₁).2 + (actualizationRatePlain ch₂).2) := by
  refine Prod.ext ?_ ?_
  · show (ch₁.append ch₂).actualizationCount
        = ch₁.actualizationCount + ch₂.actualizationCount
    exact RealityChain.append_actualizationCount ch₁ ch₂
  · show (ch₁.append ch₂).length = ch₁.length + ch₂.length
    exact RealityChain.append_length ch₁ ch₂

/-- **Rate of an empty trajectory.** -/
@[simp] theorem actualizationRate_nil {P : Type u} {C : Type v}
    (R : Reality P C) :
    actualizationRate (RealityChain'.nil (P := P) (C := C) R) = (0, 0) := by
  show (RealityChain'.actualizationCount _, RealityChain'.length _) = (0, 0)
  refine Prod.ext ?_ ?_
  · exact RealityChain'.nil_actualizationCount R
  · exact RealityChain'.nil_length R

/-- **Plain-chain rate of an empty trajectory.** -/
@[simp] theorem actualizationRatePlain_nil {P : Type u} {C : Type v}
    (R : Reality P C) :
    actualizationRatePlain (RealityChain.nil (P := P) (C := C) R) = (0, 0) := rfl

/-- **The "no-decoherence" certificate: a coherent trajectory has
zero-count rate, which propagates additively.** Concatenating two
coherent trajectories yields a coherent trajectory. -/
theorem coherent_compose {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃)
    (h₁ : ch₁.actualizationCount = 0) (h₂ : ch₂.actualizationCount = 0) :
    (ch₁.append ch₂).actualizationCount = 0 := by
  rw [RealityChain'.append_actualizationCount, h₁, h₂]

/-- **Coherent composition + endpoints equal.** Two coherent
trajectories composed yield R₁ = R₃ via the iff. -/
theorem coherent_compose_eq {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (ch₁ : RealityChain' P C R₁ R₂) (ch₂ : RealityChain' P C R₂ R₃)
    (h₁ : ch₁.actualizationCount = 0) (h₂ : ch₂.actualizationCount = 0) :
    R₁ = R₃ :=
  (ch₁.append ch₂).zero_actualization_implies_eq (coherent_compose ch₁ ch₂ h₁ h₂)

-- (A theorem like "singleton actualization step has positive count"
-- is conceptually clear but constructing TrajectoryStep' from a bare
-- AtSeam witness requires also providing a RealitySuccessor witness,
-- which AtSeam alone doesn't imply. Use `actualizeAt_strict_step`
-- when constructing strict actualization steps from pointwise events.)

/-- **Decoherence-incompatible trajectories.** If two trajectories
have the same Reality endpoints AND one is coherent (count = 0)
while the other has positive count, that's a contradiction (by the
iff): both can't simultaneously connect the same endpoints. -/
theorem coherent_and_decoherent_distinct_endpoints
    {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (ch_coh : RealityChain' P C R₁ R₂) (ch_deco : RealityChain' P C R₁ R₂)
    (h_coh : ch_coh.actualizationCount = 0)
    (h_deco : 0 < ch_deco.actualizationCount) : False := by
  -- ch_coh's coherence + iff says R₁ = R₂.
  have h_eq : R₁ = R₂ := ch_coh.zero_actualization_implies_eq h_coh
  -- ch_deco's positive count + iff says R₁ ≠ R₂.
  have h_ne : R₁ ≠ R₂ := ch_deco.pos_count_implies_ne h_deco
  exact h_ne h_eq

/-- **Path-independent coherence.** Given two strict chains between
the same endpoints, their coherence statuses (count = 0 or > 0)
agree. This is the framework's expression of "coherence is a
property of the endpoint pair, not the trajectory taken." -/
theorem path_independent_coherence {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (ch₁ ch₂ : RealityChain' P C R₁ R₂) :
    ch₁.actualizationCount = 0 ↔ ch₂.actualizationCount = 0 := by
  rw [← ch₁.eq_iff_zero_count, ← ch₂.eq_iff_zero_count]

/-- **Pure-Tier-A trajectories: all steps actualize.** A strict chain
with `bracketedCount = 0` has every step as an actualization. -/
theorem pure_tier_A_no_bracketed {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂)
    (h : ch.bracketedCount = 0) :
    ch.actualizationCount = ch.length := by
  have h_sum := ch.counts_sum
  omega

/-- **Pure-Tier-A trajectories preserve all actualizations.** Since
every step is an actualization and strict chains preserve actualized
meetings, the past grows monotonically along the entire chain. -/
theorem pure_tier_A_past_monotone {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂)
    (_h : ch.bracketedCount = 0) :
    past R₁ ⊆ past R₂ := ch.past_monotone'

/-- **Decoherence certificate.** Single Lean expression bundling the
core results of this module — the framework's Seam 4 content
formalized at the count-based structural level. -/
theorem decoherence_certificate :
    -- 1. Coherent regime characterized.
    (∀ {P : Type} {C : Type} {R₁ R₂ : Reality P C}
        (ch : RealityChain' P C R₁ R₂),
      ch.actualizationCount = 0 →
      actualizationRate ch = (0, ch.length)) ∧
    -- 2. Decoherence regime characterized.
    (∀ {P : Type} {C : Type} {R₁ R₂ : Reality P C}
        (ch : RealityChain' P C R₁ R₂),
      ch.bracketedCount = 0 →
      actualizationRate ch = (ch.length, ch.length)) ∧
    -- 3. Rate is compositional.
    (∀ {P : Type} {C : Type} {R₁ R₂ R₃ : Reality P C}
        (ch₁ : RealityChain' P C R₁ R₂)
        (ch₂ : RealityChain' P C R₂ R₃),
      actualizationRate (ch₁.append ch₂)
        = ((actualizationRate ch₁).1 + (actualizationRate ch₂).1,
           (actualizationRate ch₁).2 + (actualizationRate ch₂).2)) ∧
    -- 4. Rate bounds.
    (∀ {P : Type} {C : Type} {R₁ R₂ : Reality P C}
        (ch : RealityChain' P C R₁ R₂),
      (actualizationRate ch).1 ≤ (actualizationRate ch).2) :=
  ⟨fun ch h => coherent_regime ch h,
   fun ch h => decoherence_regime ch h,
   fun ch₁ ch₂ => concatenated_decoherence ch₁ ch₂,
   fun ch => rate_count_le_length ch⟩

/-! ## Decoherence framework summary

This module provides the structural shadow of the framework's reading
of decoherence: a Tier B phenomenon (off-diagonal suppression)
understood as the cumulative effect of Tier A actualization events
at the system-environment interface.

**Key results:**
- `actualizationRate` : the count-based decoherence-rate measure.
- `coherent_regime` (rate (0, n)) and `decoherence_regime` (rate (n, n))
  characterize the two extremes.
- `rate_count_additive` and `rate_length_additive` : compositional
  structure under chain concatenation.
- `concatenated_decoherence` : trajectory composition adds rates.
- `coherent_plus_decoherent` : worked compound rate.

**Open work:**
- Connecting the count-based rate to a continuous-time exponential-
  suppression rate. This requires either Mathlib's `Real`-valued
  rate framework or a discrete-time approximation theorem.
- Operational definitions of "environment Tier A density" suitable
  for empirical comparison.
- Quantitative predictions vs. statistical decoherence-time models.

The framework's distinctive prediction (per `SEAMS.md` Seam 4 +
`ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md`): environments rich in
actualization content decohere systems faster than statistical
models alone predict. Testable in principle. -/

end Decoherence
end Perspectival
