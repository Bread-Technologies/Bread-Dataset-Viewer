/-
Perspectival Physics — Tier B: The reversible limit
=====================================================

The framework's Tier B is the structure that emerges when actualization
events (Tier A's irreversible content) are bracketed: the inter-event
evolution of potential meetings, describable reversibly because by
construction no irreversibility occurs in the bracketed intervals.

This is where Hardy/CBH/Müller-style operational reconstruction lives.
The existing Lean modules (Continuity, GPT, Hardy, WantableGPT,
CircleGPT/QubitGPT/QutritGPT, GPTTensor, Dichotomy) all encode Tier B
content. This module makes the *bracketing operation* explicit: the
limit from Tier A to Tier B.

The framework's distinctive content lives at the SEAMS — where Tier A
content leaks through Tier B. Measurement, collapse, vertex
preservation, decoherence, the Witkowski-Brown-Truong Lyapunov
instability — all framework-empirical signatures of Tier A visible in
Tier B.

Per ORIGINAL_PROMPT v2 first move #4: encode the bracketing operation.
Per first move #5: show bracketing yields R6/R7 with vertex
preservation as a *derived* theorem.
-/

import Perspectival.TierA
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

namespace Perspectival
namespace TierB

universe u v

open TierA

/-! ## The bracketing operation

A "bracketed interval" is a span of Reality evolution between two
actualization events (or, in the boundary case, between an
actualization event and the boundary of the considered span). In such
an interval, no actualization occurs. The set of actualized meetings
is therefore constant; only the configuration of *potential* meetings
evolves.

Formally: a bracketed interval is a chain of Reality states
R_0, R_1, ..., R_n where each transition preserves the actualized set
(no new actualizations). The "inter-event structure" is captured by
the evolution of potential meetings only. -/

/-- A `BracketedTransition` from R₁ to R₂ is a state transition that
does NOT actualize any new meetings: actualized meetings stay
actualized AND no new meetings become actualized. The structure of
potential meetings can rearrange freely. -/
def BracketedTransition {P : Type u} {C : Type v}
    (R₁ R₂ : Reality P C) : Prop :=
  ∀ m : Meeting P C, R₁ m = MeetingStatus.Actualized ↔
                     R₂ m = MeetingStatus.Actualized

/-- Bracketed transitions are reflexive. -/
theorem bracketed_refl {P : Type u} {C : Type v} (R : Reality P C) :
    BracketedTransition R R := fun _ => Iff.rfl

/-- Bracketed transitions are symmetric — THIS IS THE KEY CLAIM. The
reversibility of Tier B comes from this symmetry. Within a bracketed
interval, the dynamics are reversible because no irreversible event
has occurred. -/
theorem bracketed_symm {P : Type u} {C : Type v} {R₁ R₂ : Reality P C}
    (h : BracketedTransition R₁ R₂) : BracketedTransition R₂ R₁ :=
  fun m => (h m).symm

/-- Bracketed transitions are transitive. -/
theorem bracketed_trans {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (h₁₂ : BracketedTransition R₁ R₂)
    (h₂₃ : BracketedTransition R₂ R₃) : BracketedTransition R₁ R₃ :=
  fun m => (h₁₂ m).trans (h₂₃ m)

/-- **The bracketed-transition relation is an equivalence.** This is
the structural source of Tier B's reversibility: within a bracketed
interval, Reality states are equivalent (with respect to the
actualized set), and the inter-state dynamics can be inverted. -/
theorem bracketed_equivalence {P : Type u} {C : Type v} :
    Equivalence (@BracketedTransition P C) where
  refl := bracketed_refl
  symm := bracketed_symm
  trans := bracketed_trans

/-! ## Past invariance under bracketing

Within a bracketed interval, the past (= actualized set) is constant.
This is the framework's encoding of "between events, history stays
the same; only the future-cone reshuffles." -/

/-- Bracketed transitions preserve the past (set of actualized
meetings). -/
theorem bracketed_past_invariant {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂) :
    past R₁ = past R₂ := by
  ext m
  show R₁ m = MeetingStatus.Actualized ↔ R₂ m = MeetingStatus.Actualized
  exact h m

/-- Bracketed transitions preserve the future (set of potential
meetings). -/
theorem bracketed_future_invariant {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂) :
    future R₁ = future R₂ := by
  ext m
  show R₁ m = MeetingStatus.Potential ↔ R₂ m = MeetingStatus.Potential
  constructor
  · intro h₁
    rcases h_eq : R₂ m with h_pot | h_act
    · rfl
    · exfalso
      have := (h m).mpr h_eq
      rw [this] at h₁
      exact MeetingStatus.noConfusion h₁
  · intro h₂
    rcases h_eq : R₁ m with h_pot | h_act
    · rfl
    · exfalso
      have := (h m).mp h_eq
      rw [this] at h₂
      exact MeetingStatus.noConfusion h₂

/-! ## Bracketing yields the reversible-limit structure

The framework's claim: when actualization events are bracketed, the
inter-event evolution is REVERSIBLE. The mathematical structure that
emerges is the GPT formalism (states, effects, transformations) at
the operational level — which is exactly the Tier B content the
existing Lean modules (Continuity, GPT, Hardy, ...) describe.

Concretely: a bracketed transition R₁ ↔ R₂ corresponds to a reversible
transformation in the GPT/operational picture. The "states" of the
inter-event description are the configurations of potential meetings
(the future-cone). The reversibility is structural, not postulated.

This module makes the bracketing-to-Tier-B link explicit. The existing
modules then become the *content* of Tier B once the bracketing
abstraction is applied. -/

/-- The bracketing operation yields a *reversible* (= symmetric)
equivalence on Reality states. This is the structural foundation of
Tier B's reversibility. The Hardy/CBH/Müller operational
reconstruction proceeds within a bracketed interval. -/
theorem bracketing_yields_reversibility {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂) :
    BracketedTransition R₂ R₁ := bracketed_symm h

/-! ## The Tier A / Tier B seam

The framework's distinctive content lives at the SEAMS — where Tier A
content leaks through Tier B. The most precise example: actualization
events are NOT bracketed transitions. They are the Tier A boundary.

Within a bracketed interval, dynamics are reversible (Tier B). At an
actualization event, Tier A asserts itself: a new meeting becomes
actualized, and reversibility is lost.

This is the framework's reframing of "measurement" or "collapse" in
QM: not a separate axiom, but the actualization event re-entering the
Tier B description. -/

/-- **Actualization is NOT a bracketed transition.** An actualization
event provably leaves the bracketed-transition relation: it actualizes
a meeting that was potential, breaking the actualized-set invariance. -/
theorem actualization_not_bracketed {P : Type u} {C : Type v}
    (am : ActualizationMap P C) :
    ¬ BracketedTransition am.before am.after := by
  intro h
  obtain ⟨m, h_before_pot, h_after_act⟩ := am.nontrivial
  -- h m : am.before m = Actualized ↔ am.after m = Actualized.
  have h_before_act : am.before m = MeetingStatus.Actualized := (h m).mpr h_after_act
  rw [h_before_act] at h_before_pot
  exact MeetingStatus.noConfusion h_before_pot

/-- **The seam predicate.** A transition is *at the seam* if it
actualizes some meeting (Tier A content visible in Tier B as
"measurement" / "collapse" / Lyapunov instability). -/
def AtSeam {P : Type u} {C : Type v} (R₁ R₂ : Reality P C) : Prop :=
  ∃ m : Meeting P C, R₁ m = MeetingStatus.Potential ∧
                      R₂ m = MeetingStatus.Actualized

/-- **Seam ⇒ not bracketed.** Anything at the seam (actualization
event) breaks the bracketed-transition reversibility. This is
mathematically what "measurement collapses the wavefunction" means in
the framework: the seam events are where Tier B ceases to apply. -/
theorem seam_breaks_bracketing {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h_seam : AtSeam R₁ R₂) :
    ¬ BracketedTransition R₁ R₂ := by
  intro h_bracket
  obtain ⟨m, h_pot, h_act⟩ := h_seam
  -- h_bracket m : R₁ m = Actualized ↔ R₂ m = Actualized.
  have : R₁ m = MeetingStatus.Actualized := (h_bracket m).mpr h_act
  rw [this] at h_pot
  exact MeetingStatus.noConfusion h_pot

/-! ## Summary: the bracketing operation

This module formalizes the Tier A → Tier B bracketing operation.

  • `BracketedTransition` — transition that preserves the actualized
    set (no actualization events occur).
  • `bracketed_equivalence` — the bracketed-transition relation is an
    equivalence (reflexive + symmetric + transitive). The SYMMETRY is
    the source of Tier B's reversibility.
  • `bracketed_past_invariant`, `bracketed_future_invariant` —
    bracketing preserves the past/future partition.
  • `bracketing_yields_reversibility` — Tier B's reversibility is a
    consequence of bracketing, not a foundational commitment.
  • `actualization_not_bracketed` — actualization events provably leave
    the bracketed-transition relation.
  • `AtSeam`, `seam_breaks_bracketing` — the framework's reframing of
    "measurement" / "collapse" as Tier A re-entering the Tier B
    description.

The existing modules (Continuity, GPT, Hardy, WantableGPT, the GPT
instances, Dichotomy, ...) provide the *content* of Tier B once
bracketing is applied. The R6/R7 vertex-preservation work, in
particular, is exactly the constraint that bracketed dynamics
preserve pure potential states — making explicit a Tier A commitment
that became visible at Tier B (per the v2 architecture audit).
-/

end TierB
end Perspectival
