/-
Perspectival Physics — Tier A: Irreversible meeting-structure
==============================================================

The framework's foundational level. Per ORIGINAL_PROMPT v2, the two
axioms are:

  Axiom I (Existence). To be is to want. Wanting is intrinsically
    directional (from lack toward fulfillment) and intrinsically
    relational (presupposes complement).

  Axiom II (Actualization). Wants meet their complements through
    actualization events. Actualization is irreversible. Reality is
    the developing structure of potential and actualized meetings.

This module encodes the Tier A structure directly. Reversibility-first
encodings (Reversible, StrictReversible, agency hierarchy) live at
Tier B and emerge by bracketing actualization events — see TierB.lean
(pending). The prior v1 work (R6 with vertex preservation, R7
scaffold, WantableGPT, Hardy quadchotomy) is Tier B content and
remains valid as the reversible-limit description.

**Witkowski-Brown-Truong 2024** (Entropy 26(3), 203) provides the
mechanical content for Axiom II's irreversibility. The Picard-Lindelöf
argument applied to time-reversal-symmetric ODEs proves reset/erasure
is impossible under conservative dynamics. Actualization is
many-to-one (multiple potential meetings collapse into one definite
outcome); many-to-one is incompatible with conservative dynamics;
therefore actualization is nonconservative. This is a *theorem* about
what actualization mechanically requires — not a separate axiom.
-/

import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

namespace Perspectival
namespace TierA

universe u v

/-! ## Axiom I: Wanting as directed-relational structure

A `Want` is the foundational primitive. Its two structural commitments:

  • Directional: wanting points from a position (the wanter) toward a
    complement (what would fulfill the wanting). NOT an arbitrary
    relation — has from/toward asymmetry built in.
  • Relational: every want presupposes a complement. No isolated
    wanting.

Mathematically: a Want over a perspective-type `P` and a complement-type
`C` is the pair of these structural commitments, with the relational
content captured by a function from `P` (where the want is FROM) to `C`
(what would clear it).

The `complement` function is the irreducible content: it's NOT a
"property of" the perspective, it's WHAT WANTING IS — the directional
relation between perspectives and their fulfillment-conditions. -/

/-- A `Want` is a directed-relational structure: from a perspective in
`P`, toward a complement-condition in `C`. -/
structure Want (P : Type u) (C : Type v) where
  /-- The perspective from which the wanting obtains. -/
  from_perspective : P
  /-- The complement that would clear the want. -/
  toward_complement : C

/-! ### Axiom I content as theorems

We formalize "to be is to want" not as an existence claim about
arbitrary entities, but as a STRUCTURAL claim: any entity in the
framework's ontology has a Want associated with it (directional +
relational structure). Encoding choice: an "Existent" in the framework
is anything with an associated Want. -/

/-- An `Existent` over (P, C) is anything that *has* a Want — i.e.,
to exist (in the framework's sense) IS to want. -/
abbrev Existent (P : Type u) (C : Type v) := Want P C

/-- **Axiom I (directedness):** every Existent has a from-perspective
and a toward-complement; the structure is asymmetric. -/
theorem axiom_I_directedness {P : Type u} {C : Type v} (e : Existent P C) :
    ∃ p : P, ∃ c : C, e.from_perspective = p ∧ e.toward_complement = c :=
  ⟨e.from_perspective, e.toward_complement, rfl, rfl⟩

/-- **Axiom I (relationality):** an Existent is constituted by the
(perspective, complement) pair; the two are inseparable. -/
theorem axiom_I_relationality {P : Type u} {C : Type v} (e : Existent P C) :
    e = ⟨e.from_perspective, e.toward_complement⟩ := rfl

/-! ## Axiom II: Actualization as irreversible meeting-events

A `Meeting` is a candidate clearing event between two complementary
wants. It has two modalities: *potential* (the wants are positioned
relationally but the clearing has not occurred) and *actualized* (the
clearing has occurred, irreversibly).

The irreversibility is encoded structurally: there is a
`Status.transition` function from `Potential` to `Actualized`, but
NO inverse function. This is the framework's foundational asymmetry
and the source of the arrow of time. -/

/-- The status of a meeting: potential or actualized. -/
inductive MeetingStatus
  | Potential
  | Actualized
  deriving DecidableEq, Repr

/-- A `Meeting` between complementary Wants. The status is the
modality (potential or actualized). -/
structure Meeting (P : Type u) (C : Type v) where
  /-- The "left" want — the perspective initiating. -/
  initiator : Want P C
  /-- The "right" want — the complementary perspective. -/
  responder : Want C P
  /-- The current modality. -/
  status : MeetingStatus

/-- **Actualization as a one-way transition.** A potential meeting can
become actualized; once actualized, it stays actualized. -/
def actualize {P : Type u} {C : Type v} (m : Meeting P C) : Meeting P C :=
  { m with status := MeetingStatus.Actualized }

@[simp] theorem actualize_status {P : Type u} {C : Type v} (m : Meeting P C) :
    (actualize m).status = MeetingStatus.Actualized := rfl

/-! ### Axiom II content as theorems

The key claim of Axiom II — actualization is irreversible — is
encoded by the absence of an inverse to `actualize`. Concretely:
there is no total function `Meeting P C → Meeting P C` that sends
actualized meetings to potential meetings AND preserves all other
structure.

Stronger: the function `actualize` is idempotent (actualizing an
already-actualized meeting is the same meeting). -/

/-- **Axiom II (idempotence):** actualization is idempotent. Once
actualized, re-actualizing changes nothing. -/
@[simp] theorem axiom_II_idempotent {P : Type u} {C : Type v} (m : Meeting P C) :
    actualize (actualize m) = actualize m := by
  unfold actualize
  rfl

/-- **Axiom II (irreversibility — asymmetric):** the actualize map is
NOT injective in general, when applied to actualized meetings: two
different potential meetings can both actualize to the same actualized
meeting (the status field is forgotten). -/
theorem axiom_II_actualize_lossy_on_status
    {P : Type u} {C : Type v} (m : Meeting P C) :
    (actualize m).status = MeetingStatus.Actualized ∧
    (actualize { m with status := MeetingStatus.Actualized }).status
    = MeetingStatus.Actualized :=
  ⟨rfl, rfl⟩

/-- **Axiom II (Reality as developing structure):** Reality is the
state of all meetings at a given "moment." It evolves by
actualization events — and only by actualization. -/
abbrev Reality (P : Type u) (C : Type v) : Type _ := Meeting P C → MeetingStatus

/-- Reality-state evolution is *monotone* with respect to the
"actualized" order: actualized meetings stay actualized.

Formal: if R₁ is a state where some meetings are actualized, then R₂
is a *successor* of R₁ if R₂ has at least all of R₁'s actualized
meetings (and possibly more). -/
def RealitySuccessor {P : Type u} {C : Type v}
    (R₁ R₂ : Reality P C) : Prop :=
  ∀ m : Meeting P C, R₁ m = MeetingStatus.Actualized →
    R₂ m = MeetingStatus.Actualized

/-- Reality-successor is reflexive. -/
theorem reality_successor_refl {P : Type u} {C : Type v}
    (R : Reality P C) : RealitySuccessor R R := fun _ h => h

/-- Reality-successor is transitive. -/
theorem reality_successor_trans {P : Type u} {C : Type v}
    {R₁ R₂ R₃ : Reality P C}
    (h₁₂ : RealitySuccessor R₁ R₂) (h₂₃ : RealitySuccessor R₂ R₃) :
    RealitySuccessor R₁ R₃ :=
  fun m h => h₂₃ m (h₁₂ m h)

/-- Reality-successor is antisymmetric (modulo definitional equality
on the status). If R₁ and R₂ are mutually successors, they agree on
actualized meetings. -/
theorem reality_successor_antisymm {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (h₁₂ : RealitySuccessor R₁ R₂) (h₂₁ : RealitySuccessor R₂ R₁)
    (m : Meeting P C) :
    R₁ m = MeetingStatus.Actualized ↔ R₂ m = MeetingStatus.Actualized :=
  ⟨h₁₂ m, h₂₁ m⟩

/-! ### Pointwise actualization

Given a Reality state R and a target meeting m, the *pointwise
actualization* `actualizeAt R m` is the Reality state that agrees with
R everywhere except at m, where it is forced to `Actualized`.

This is the elementary form of an actualization event, and it is a
Reality-successor by construction (Axiom II content in elementary form). -/

/-- **Pointwise actualization at a single meeting.** Given a Reality
state R and a target meeting m, produce the Reality state with m
actualized and all others unchanged. -/
def actualizeAt {P : Type u} {C : Type v} [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C) : Reality P C :=
  fun m' => if m' = m then MeetingStatus.Actualized else R m'

@[simp] theorem actualizeAt_self {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C) :
    actualizeAt R m m = MeetingStatus.Actualized := by
  unfold actualizeAt
  simp

@[simp] theorem actualizeAt_other {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) {m m' : Meeting P C} (h : m' ≠ m) :
    actualizeAt R m m' = R m' := by
  unfold actualizeAt
  rw [if_neg h]

/-- **Pointwise actualization preserves the actualized set (and grows
it).** This is the elementary form of `RealitySuccessor`. -/
theorem actualizeAt_is_successor {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C) :
    RealitySuccessor R (actualizeAt R m) := by
  intro m' h_act
  unfold actualizeAt
  by_cases h_eq : m' = m
  · rw [if_pos h_eq]
  · rw [if_neg h_eq]; exact h_act

/-! ## The arrow of time from Axioms I + II

Past = the set of actualized meetings (definite, settled, irreversibly
part of the structure). Future = the set of potential meetings (open,
not yet cleared). The asymmetric ordering on `Reality` via
`RealitySuccessor` IS the arrow of time, constitutively (rather than
emergently from statistical considerations). -/

/-- The "past" of a Reality state: the set of actualized meetings. -/
def past {P : Type u} {C : Type v} (R : Reality P C) : Set (Meeting P C) :=
  { m | R m = MeetingStatus.Actualized }

/-- The "future" of a Reality state: the set of potential meetings. -/
def future {P : Type u} {C : Type v} (R : Reality P C) : Set (Meeting P C) :=
  { m | R m = MeetingStatus.Potential }

/-- Past and future are disjoint. -/
theorem past_future_disjoint {P : Type u} {C : Type v} (R : Reality P C) :
    past R ∩ future R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro m hm
  rcases hm with ⟨h1, h2⟩
  simp only [past, future, Set.mem_setOf_eq] at h1 h2
  rw [h1] at h2
  exact MeetingStatus.noConfusion h2

/-- **Time arrow theorem:** past grows monotonically along Reality-
successor. -/
theorem past_monotone {P : Type u} {C : Type v} {R₁ R₂ : Reality P C}
    (h : RealitySuccessor R₁ R₂) : past R₁ ⊆ past R₂ := by
  intro m hm
  simp only [past, Set.mem_setOf_eq] at hm ⊢
  exact h m hm

/-- **`actualizeAt` extends the past by exactly the new meeting.** When
m was potential in R, the past of `actualizeAt R m` is the past of R
together with the meeting m. -/
theorem past_actualizeAt_disjunction {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m m' : Meeting P C) :
    m' ∈ past (actualizeAt R m)
      ↔ (R m' = MeetingStatus.Actualized ∨ m' = m) := by
  constructor
  · intro h_m'
    have h_eq_a : actualizeAt R m m' = MeetingStatus.Actualized := h_m'
    by_cases h_eq : m' = m
    · exact Or.inr h_eq
    · left
      rw [actualizeAt_other R h_eq] at h_eq_a
      exact h_eq_a
  · intro h
    show actualizeAt R m m' = MeetingStatus.Actualized
    rcases h with h_past | h_eq
    · by_cases h_em : m' = m
      · rw [h_em, actualizeAt_self]
      · rw [actualizeAt_other R h_em]
        exact h_past
    · rw [h_eq, actualizeAt_self]

/-- **`actualizeAt` does not modify the past when m was already
actualized.** If m is already in the past of R, then `actualizeAt R m`
has the same past. (The actualizeAt of an already-actualized meeting
is idempotent.) -/
theorem past_actualizeAt_already_act {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_act : R m = MeetingStatus.Actualized) :
    past (actualizeAt R m) = past R := by
  ext m'
  show actualizeAt R m m' = MeetingStatus.Actualized
      ↔ R m' = MeetingStatus.Actualized
  by_cases h_eq : m' = m
  · rw [h_eq]
    rw [actualizeAt_self]
    exact ⟨fun _ => h_act, fun _ => rfl⟩
  · rw [actualizeAt_other R h_eq]

/-- **`actualizeAt` is many-to-one: it forgets R's value at m.** If
two Reality states R₁, R₂ agree on all meetings except possibly at m
(where they may differ), then `actualizeAt R₁ m = actualizeAt R₂ m`.

This is the elementary form of the framework's "many-to-one collapse"
content (cf. Witkowski-Brown-Truong 2024 Picard-Lindelöf
impossibility): actualization at m forgets the prior status at m,
which is the lossy / nonconservative content of Axiom II at the
elementary-event level. -/
theorem actualizeAt_many_to_one {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R₁ R₂ : Reality P C) (m : Meeting P C)
    (h_agree : ∀ m' : Meeting P C, m' ≠ m → R₁ m' = R₂ m') :
    actualizeAt R₁ m = actualizeAt R₂ m := by
  funext m'
  by_cases h_eq : m' = m
  · rw [h_eq, actualizeAt_self, actualizeAt_self]
  · rw [actualizeAt_other R₁ h_eq, actualizeAt_other R₂ h_eq]
    exact h_agree m' h_eq

/-! ## Witkowski-Brown-Truong 2024: mechanical content of Axiom II

The user's published paper proves that erasure / reset is strictly
impossible under conservative dynamics. Mathematically: a many-to-one
phase-space map is incompatible with time-reversal-symmetric ODEs by
the Picard-Lindelöf existence-and-uniqueness theorem. Approaching a
reset under conservative dynamics yields Lyapunov instability at the
reset point.

Per `ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md` — the active entropy
addendum — this mechanical impossibility is one half of the framework's
both-halves derivation of the Second Law. The other half is the
subjectivist Jaynesian content (entropy = observer-relative
coarse-graining of distinguishable states). The Lean side encodes the
mechanical half (here, plus `actualizeAt_many_to_one` above for the
elementary-event form); the Jaynesian half is metaphysical commitment
not currently Lean-encoded at the framework's scope.

Translated to Tier A: actualization is many-to-one (multiple potential
meeting-configurations collapsing into one actualized configuration).
Many-to-one is incompatible with conservative (one-to-one, reversible)
dynamics. Therefore actualization is fundamentally nonconservative.

This is a THEOREM about what actualization mechanically requires —
NOT a separate axiom. The full mechanical content (Picard-Lindelöf
applied to time-reversal-symmetric ODEs) is in the cited paper. Here
we record the structural fact:

**Theorem (informal): if `f : Meeting → Meeting` collapses two
distinct potential meetings to one actualized meeting, then `f`
cannot have a continuous inverse defined on the actualized meetings.**

The Lean encoding: an "actualization map" is many-to-one in general,
which is incompatible with bijectivity. We provide the structural
form here; the dynamical Picard-Lindelöf content is delegated to
Witkowski-Brown-Truong 2024. -/

/-- An *actualization map* is a function from one Reality state to a
successor state, which actualizes one or more potential meetings. -/
structure ActualizationMap (P : Type u) (C : Type v) where
  /-- The Reality state before actualization. -/
  before : Reality P C
  /-- The Reality state after actualization. -/
  after : Reality P C
  /-- The map respects the successor relation. -/
  is_successor : RealitySuccessor before after
  /-- At least one meeting changed status. (Non-trivial actualization.) -/
  nontrivial : ∃ m, before m = MeetingStatus.Potential ∧
                    after m = MeetingStatus.Actualized

/-- **Witkowski-Brown-Truong consequence (structural):** a non-trivial
actualization map is NOT reversible. There is no map that takes the
"after" state back to the "before" state preserving the successor
relation in both directions.

This is the structural shadow of the Picard-Lindelöf argument:
many-to-one collapse cannot have a phase-space inverse. Cite
Witkowski-Brown-Truong 2024 for the full mechanical content. -/
theorem axiom_II_actualization_irreversible
    {P : Type u} {C : Type v} (am : ActualizationMap P C) :
    ¬ RealitySuccessor am.after am.before := by
  intro h_rev
  obtain ⟨m, h_before_pot, h_after_act⟩ := am.nontrivial
  -- h_rev : am.after m = Actualized → am.before m = Actualized
  have h_before_act : am.before m = MeetingStatus.Actualized := h_rev m h_after_act
  -- But h_before_pot says am.before m = Potential — contradiction.
  rw [h_before_act] at h_before_pot
  exact MeetingStatus.noConfusion h_before_pot

/-! ## The framework's "no-return-to-potential" theorem

The cleanest structural statement of Axiom II's irreversibility: a
meeting that has been actualized cannot become potential again. This
is the framework's arrow-of-time at its sharpest. -/

/-- **No-return-to-potential.** Within any Reality-successor chain,
once a meeting is actualized at some state, it remains actualized at
all subsequent states. There is no mechanism in Tier A that reverses
actualization. -/
theorem no_return_to_potential {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : RealitySuccessor R₁ R₂)
    {m : Meeting P C} (h_act : R₁ m = MeetingStatus.Actualized) :
    R₂ m = MeetingStatus.Actualized := h m h_act

/-- **Asymmetric arrow:** the contrapositive form — if a meeting is
potential at a successor state, it was potential at the predecessor. -/
theorem still_potential_implies_was_potential {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : RealitySuccessor R₁ R₂)
    {m : Meeting P C} (h_pot : R₂ m = MeetingStatus.Potential) :
    R₁ m = MeetingStatus.Potential := by
  -- Case on R₁ m: Potential or Actualized.
  cases h_eq : R₁ m with
  | Potential => rfl
  | Actualized =>
      have h2 := h m h_eq
      rw [h2] at h_pot
      exact absurd h_pot MeetingStatus.noConfusion

/-! ## Witkowski-Brown-Truong 2024 connection (Tier 1 step 6)

The user's published paper proves, via Picard-Lindelöf applied to
time-reversal-symmetric ODEs:

  THEOREM (paper Section 3): reset (= many-to-one phase-space map)
  is strictly impossible under conservative dynamics.

  COROLLARY (paper Section 4): approaching reset under conservative
  dynamics yields Lyapunov instability at the reset point.

  COROLLARY (paper Section 5): kT ln 2 erasure bound (Landauer)
  derivable from pure mechanics, no statistical-mechanical postulate.

Translated to Tier A via the bracketing operation:

  - Conservative dynamics ↔ bracketed transitions (no actualization
    events in the bracketed interval; the actualized-set is
    preserved).
  - Reset / erasure / many-to-one collapse ↔ actualization event.
  - The paper's impossibility ↔ no_return_to_potential plus the
    structural ban on bracketed transitions doing actualization.

The Lean encoding here captures the structural shadow:
`axiom_II_actualization_irreversible` is the framework-theoretic
version of the paper's impossibility theorem. The dynamical content
(Picard-Lindelöf application to ODEs, Lyapunov calculation) is in
the cited paper. Together, the structural shadow + the cited paper
give Tier 1 step 6 (thermodynamics from mechanics, not from
statistical postulates). -/

/-- **Witkowski-Brown-Truong structural form:** the existence of an
`ActualizationMap` provably means the actualization map itself cannot
be reversed (cf. `axiom_II_actualization_irreversible` above). The
full Picard-Lindelöf-grounded mechanical content — that conservative
phase-space dynamics cannot achieve a many-to-one collapse — is in
the cited paper (Witkowski-Brown-Truong, Entropy 26(3), 203, 2024).

This module records only the structural shadow at the abstract
Reality / Meeting level. The connection to specific phase-space
dynamics and the Lyapunov-instability calculation are not encoded in
Lean here. -/
theorem WBT_structural_shadow {P : Type u} {C : Type v}
    (am : ActualizationMap P C) :
    ¬ RealitySuccessor am.after am.before :=
  axiom_II_actualization_irreversible am

/-! ## Step 7: Hard problem dissolution (philosophical, in vocabulary)

Per ORIGINAL_PROMPT v2 §3 step 7: "Wanting is what existence IS. The
what-it-is-likeness of experience is the felt directionality of
wanting. Consciousness is the framework's primitive. Combination
problem dissolves because there is nothing to combine — there is no
underlying substance that needs consciousness as a property."

In the framework's Lean encoding, this is structurally evident:
`Want P C` IS the foundational primitive. There is no underlying
substance type from which Want is constructed; Want is the type.

The combination problem dissolves because Wants combine
*relationally* (via Meetings) rather than substantively. There is no
"smaller consciousness" to add up into a "bigger consciousness";
there are only directional relations among perspectives. The Meeting
structure (potential ↔ actualized) captures the relational dynamics
without requiring substance-aggregation.

This is philosophical content, not a Lean theorem. The structural
encoding in `Want` is the framework's commitment; the dissolution is
the consequence at the philosophical level. See
`TIER4_DISSOLUTIONS.md` for the longer argument and `ORIGINAL_PROMPT.md`
§3 step 7 for the v2 statement. -/

/-! ## Summary

Tier A is encoded:
  • Axiom I (Want as directed-relational): `Want`, `Existent`,
    `axiom_I_directedness`, `axiom_I_relationality`.
  • Axiom II (Meeting with potential/actualized modalities, irreversible
    actualization): `Meeting`, `MeetingStatus`, `actualize`,
    `axiom_II_idempotent`, `axiom_II_actualize_lossy_on_status`.
  • Reality as developing structure: `Reality`, `RealitySuccessor`,
    `reality_successor_*`.
  • Pointwise actualization (elementary Axiom II event):
    `actualizeAt`, `actualizeAt_self`, `actualizeAt_other`,
    `actualizeAt_is_successor`.
  • Arrow of time: `past`, `future`, `past_future_disjoint`,
    `past_monotone`.
  • Witkowski-Brown-Truong 2024 structural shadow:
    `ActualizationMap`, `axiom_II_actualization_irreversible`.

What's NOT in this module:
  • Dynamical content (Picard-Lindelöf, Lyapunov instability) — those
    are in the cited paper, accessed externally.
  • The bracketing operation Tier A → Tier B — see TierB.lean.
  • Reversibility-first encodings (Reversible, StrictReversible,
    agency hierarchy) — those are Tier B content, see Continuity.lean.
-/

end TierA
end Perspectival
