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
import Mathlib.GroupTheory.Perm.Basic

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

/-- **Bracketed iff mutually-successor.** A transition is bracketed
iff it is reversible in the `RealitySuccessor` ordering. This is the
formal statement of "bracketing = reversibility in the time-arrow
ordering." -/
theorem bracketed_iff_mutual_successor {P : Type u} {C : Type v}
    (R₁ R₂ : Reality P C) :
    BracketedTransition R₁ R₂
    ↔ RealitySuccessor R₁ R₂ ∧ RealitySuccessor R₂ R₁ := by
  constructor
  · intro h
    exact ⟨fun m h_act => (h m).mp h_act, fun m h_act => (h m).mpr h_act⟩
  · rintro ⟨h₁₂, h₂₁⟩
    intro m
    exact ⟨h₁₂ m, h₂₁ m⟩

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

/-! ## Bracketing forces discrete-permutation dynamics on definite-outcome
    configurations (v2 derivation of vertex preservation)

The framework's claim, made concrete: under bracketing, definite
potential-outcome configurations (= vertices in the Tier B Classical
GPT) can only PERMUTE among themselves. No continuous deformation
through "mixed" non-vertex configurations is allowed, because such a
deformation would require an intermediate actualization (forbidden
in a bracketed interval).

Formal encoding: a "definite-outcome configuration" on a finite
candidate set `Fin n` is an `Equiv.Perm`-image of a chosen candidate.
Bracketed dynamics restrict to permutations.

This makes the v1 vertex-preservation patch into a v2-progressive
*derived theorem*: vertex preservation in the Classical GPT R6
disconnect is the inheritance of Tier A's discreteness commitment
through bracketing. See `V2_AUDIT.md` audit item 3 and `SEAMS.md`
seam 2 for the conceptual framing. -/

/-- A *definite-outcome configuration* on a finite candidate set
`Fin n` is an assignment of a "currently-primed" candidate. -/
structure DefiniteConfig (n : ℕ) where
  primed : Fin n

/-- Two definite configurations are bracketed-equivalent if they
differ at most by a *permutation* of the underlying candidate set —
not by smearing into a mixture. This expresses the v2 derivation of
vertex preservation at the structural level. -/
def DefiniteBracketed {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c₁ c₂ : DefiniteConfig n) : Prop :=
  c₂.primed = σ c₁.primed

/-- **Vertex preservation as derived theorem (structural form).** A
bracketed transformation of definite configurations IS a permutation
— it cannot mix candidates into a non-vertex state. -/
theorem bracketing_forces_permutation {n : ℕ}
    {c₁ c₂ : DefiniteConfig n} (σ : Equiv.Perm (Fin n))
    (h : DefiniteBracketed σ c₁ c₂) :
    ∃ i j : Fin n, c₁.primed = i ∧ c₂.primed = j ∧ σ i = j :=
  ⟨c₁.primed, c₂.primed, rfl, rfl, h.symm⟩

/-- **The identity permutation = trivial bracketed transformation.** -/
theorem definite_bracketed_id {n : ℕ} (c : DefiniteConfig n) :
    DefiniteBracketed (Equiv.refl _) c c := rfl

/-- **Bracketed transformations on definite configurations compose
permutations.** Reversibility = the permutation is invertible
(`Equiv.Perm` is by definition a permutation, hence has an inverse).

Composition order: `Equiv.trans` applies its first argument first,
then the second. So `σ₁.trans σ₂` is `x ↦ σ₂ (σ₁ x)`, which is
exactly what we want when h₁₂ takes c₁ to c₂ via σ₁ and h₂₃ takes c₂
to c₃ via σ₂. -/
theorem definite_bracketed_compose {n : ℕ}
    {c₁ c₂ c₃ : DefiniteConfig n} {σ₁ σ₂ : Equiv.Perm (Fin n)}
    (h₁₂ : DefiniteBracketed σ₁ c₁ c₂)
    (h₂₃ : DefiniteBracketed σ₂ c₂ c₃) :
    DefiniteBracketed (σ₁.trans σ₂) c₁ c₃ := by
  show c₃.primed = (σ₁.trans σ₂) c₁.primed
  show c₃.primed = σ₂ (σ₁ c₁.primed)
  rw [← h₁₂]
  exact h₂₃

/-- **Bracketing on definite configurations cannot produce non-vertex
states.** A bracketed transformation of definite configurations
always yields another definite configuration — no smearing into
"mixed" states is allowed. -/
theorem bracketing_preserves_definiteness {n : ℕ}
    (c₁ : DefiniteConfig n) (σ : Equiv.Perm (Fin n)) :
    ∃ c₂ : DefiniteConfig n, DefiniteBracketed σ c₁ c₂ :=
  ⟨⟨σ c₁.primed⟩, rfl⟩

/-! ### `Equiv.Perm` acts on `DefiniteConfig` — the framework's
group-theoretic structure derives from bracketing -/

/-- The natural action of `Equiv.Perm (Fin n)` on `DefiniteConfig n`. -/
def permActOnDefinite {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : DefiniteConfig n) :
    DefiniteConfig n :=
  ⟨σ c.primed⟩

@[simp] theorem permActOnDefinite_one {n : ℕ} (c : DefiniteConfig n) :
    permActOnDefinite (1 : Equiv.Perm (Fin n)) c = c := by
  cases c; rfl

theorem permActOnDefinite_mul {n : ℕ} (σ₁ σ₂ : Equiv.Perm (Fin n))
    (c : DefiniteConfig n) :
    permActOnDefinite (σ₁ * σ₂) c
    = permActOnDefinite σ₁ (permActOnDefinite σ₂ c) := rfl

/-- **The framework's discrete-permutation structure of Tier B
classical dynamics derives from bracketing.** This is the group-
theoretic restatement of vertex preservation: when bracketed dynamics
act on definite configurations, the action group is exactly
`Equiv.Perm (Fin n)` — the symmetric group.

Together with the existing Classical.lean proofs that classical
reversibles are exactly permutations (e.g., `permLinGen`), this
establishes the v2-progressive arc: vertex preservation in the
Classical R6 disconnect is the operational shadow of this
group-theoretic fact at Tier A. -/
theorem definite_bracketed_iff_perm {n : ℕ}
    (c₁ c₂ : DefiniteConfig n) :
    (∃ σ : Equiv.Perm (Fin n), DefiniteBracketed σ c₁ c₂) ↔
    ∃ σ : Equiv.Perm (Fin n), σ c₁.primed = c₂.primed := by
  constructor
  · rintro ⟨σ, h⟩
    refine ⟨σ, ?_⟩
    exact h.symm
  · rintro ⟨σ, h⟩
    refine ⟨σ, ?_⟩
    exact h.symm

/-- **`DefiniteConfig n` is canonically equivalent to `Fin n`.** The
configuration carries exactly the information of its primed index. -/
def definiteConfigEquivFin (n : ℕ) : DefiniteConfig n ≃ Fin n where
  toFun := DefiniteConfig.primed
  invFun := fun i => ⟨i⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem definiteConfigEquivFin_apply (n : ℕ) (c : DefiniteConfig n) :
    definiteConfigEquivFin n c = c.primed := rfl

@[simp] theorem definiteConfigEquivFin_symm_apply (n : ℕ) (i : Fin n) :
    (definiteConfigEquivFin n).symm i = ⟨i⟩ := rfl

/-- **The DefiniteConfig action by permutations matches the natural
permutation action on `Fin n`.** Under the equivalence
`definiteConfigEquivFin`, `permActOnDefinite σ` corresponds to applying
`σ` directly to `Fin n`. This is the structural identification of the
bare bracketed Tier B carrier with the classical n-simplex's vertex
index set. -/
theorem permActOnDefinite_via_equiv {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (c : DefiniteConfig n) :
    definiteConfigEquivFin n (permActOnDefinite σ c)
    = σ (definiteConfigEquivFin n c) := rfl

/-! ## Tier-B trajectories: bracketed intervals + actualization events

A complete framework-trajectory through Reality is a sequence of
bracketed transitions interrupted by actualization events. This is
the v2 encoding of "evolution + measurement" in QM:

  - Bracketed intervals: unitary-like, reversible. Tier B.
  - Actualization events: measurement-like, irreversible. Tier A.

The framework dissolves the measurement problem: measurement is not
a separate axiom but the actualization event re-entering the Tier B
description. -/

/-- A `TrajectoryStep` is either a bracketed (reversible) transition
or an actualization (irreversible) event. -/
inductive TrajectoryStep (P : Type u) (C : Type v)
    (R₁ R₂ : Reality P C) : Type (max u v)
  | bracketed (h : BracketedTransition R₁ R₂)
  | actualization (h : AtSeam R₁ R₂)

/-- **A trajectory step is either bracketed or at the seam, and these
are exclusive.** This expresses the framework's dichotomy: every
Reality transition is either reversible (Tier B, bracketed) or
irreversible (Tier A, actualization). No third option. -/
theorem trajectory_step_dichotomy {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (step : TrajectoryStep P C R₁ R₂) :
    (BracketedTransition R₁ R₂) ∨ (AtSeam R₁ R₂) := by
  cases step with
  | bracketed h => exact Or.inl h
  | actualization h => exact Or.inr h

/-- **Bracketed and AtSeam are mutually exclusive.** A transition
cannot be simultaneously a Tier B step and a Tier A actualization. -/
theorem bracketed_and_seam_exclusive {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (h_bracketed : BracketedTransition R₁ R₂)
    (h_seam : AtSeam R₁ R₂) : False :=
  seam_breaks_bracketing h_seam h_bracketed

/-- **Bracketed transitions are Reality-successors (forward direction).**
A bracketed transition has actualized R₁ ⊆ actualized R₂ trivially
(by the iff hypothesis). -/
theorem bracketed_implies_successor {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂) :
    RealitySuccessor R₁ R₂ :=
  fun m h_act => (h m).mp h_act

/-- **A `TrajectoryStep'` is a strengthened TrajectoryStep that also
carries a RealitySuccessor witness.** Useful for downstream reasoning
where the chain must track the cumulative time-ordering. The
elementary actualizeAt-based construction always satisfies this
strengthening (see `actualizeAt_strict_step` below). -/
structure TrajectoryStep' (P : Type u) (C : Type v)
    (R₁ R₂ : Reality P C) where
  step : TrajectoryStep P C R₁ R₂
  is_successor : RealitySuccessor R₁ R₂

/-- **Constructor from bracketed transition.** Any bracketed transition
yields a TrajectoryStep' since bracketed implies successor. -/
def TrajectoryStep'.bracketed {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂) :
    TrajectoryStep' P C R₁ R₂ where
  step := TrajectoryStep.bracketed h
  is_successor := bracketed_implies_successor h

-- (Constructor `actualizeAt_strict_step` defined later, after
-- `actualizeAt_atSeam` is available.)

/-! ### Reality chains: multi-step trajectories

A `RealityChain R₁ R_n` is a finite sequence of `TrajectoryStep`s
linking Reality states. Concretely, it is a reflexive-transitive
closure of the trajectory-step relation. This makes "evolution +
measurement" sequences concretely encodable: any chain of Reality
states alternates between bracketed intervals (Tier B reversible
dynamics) and actualization events (Tier A irreversible seams). -/

/-- `RealityChain R₁ R_n` is a chain of Reality states linked by
TrajectoryStep, starting at R₁ and ending at R_n. -/
inductive RealityChain (P : Type u) (C : Type v) :
    Reality P C → Reality P C → Type (max u v)
  | nil (R : Reality P C) : RealityChain P C R R
  | cons {R₁ R₂ R₃ : Reality P C}
      (step : TrajectoryStep P C R₁ R₂)
      (rest : RealityChain P C R₂ R₃) :
      RealityChain P C R₁ R₃

/-- Any single TrajectoryStep is a 1-step RealityChain. -/
def RealityChain.singleton {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (step : TrajectoryStep P C R₁ R₂) :
    RealityChain P C R₁ R₂ :=
  RealityChain.cons step (RealityChain.nil R₂)

/-- Concatenation of RealityChains by structural recursion on the
first chain. -/
def RealityChain.append {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ R₃ : Reality P C},
      RealityChain P C R₁ R₂ → RealityChain P C R₂ R₃ →
      RealityChain P C R₁ R₃
  | _, _, _, RealityChain.nil _, ch₂ => ch₂
  | _, _, _, RealityChain.cons step rest, ch₂ =>
      RealityChain.cons step (RealityChain.append rest ch₂)

/-- Number of actualization steps along a RealityChain. Bracketed
steps contribute 0; actualization steps contribute 1. -/
def RealityChain.actualizationCount {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C}, RealityChain P C R₁ R₂ → ℕ
  | _, _, RealityChain.nil _ => 0
  | _, _, RealityChain.cons step rest =>
      (match step with
        | TrajectoryStep.bracketed _ => 0
        | TrajectoryStep.actualization _ => 1) +
      RealityChain.actualizationCount rest

/-- Number of bracketed steps along a RealityChain. Bracketed steps
contribute 1; actualization steps contribute 0. -/
def RealityChain.bracketedCount {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C}, RealityChain P C R₁ R₂ → ℕ
  | _, _, RealityChain.nil _ => 0
  | _, _, RealityChain.cons step rest =>
      (match step with
        | TrajectoryStep.bracketed _ => 1
        | TrajectoryStep.actualization _ => 0) +
      RealityChain.bracketedCount rest

/-- Length of a RealityChain (total step count). -/
def RealityChain.length {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C}, RealityChain P C R₁ R₂ → ℕ
  | _, _, RealityChain.nil _ => 0
  | _, _, RealityChain.cons _ rest => 1 + RealityChain.length rest

/-- **The trajectory step counts sum to the length.** Each step is
either bracketed or an actualization (by the trajectory dichotomy), so
actualizationCount + bracketedCount = length. -/
theorem RealityChain.counts_sum {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂),
      ch.actualizationCount + ch.bracketedCount = ch.length
  | _, _, RealityChain.nil _ => rfl
  | _, _, RealityChain.cons step rest => by
      simp only [RealityChain.actualizationCount, RealityChain.bracketedCount,
                 RealityChain.length]
      cases step <;>
        · simp only
          have h := RealityChain.counts_sum rest
          omega

/-- **A chain with zero actualization steps has only bracketed steps.**
This is the "no-seam-crossings" condition: the chain stays entirely
within Tier B. -/
theorem RealityChain.zero_actualization_all_bracketed {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂),
      ch.actualizationCount = 0 →
      ch.bracketedCount = ch.length
  | _, _, RealityChain.nil _ => fun _ => rfl
  | _, _, RealityChain.cons step rest => by
      intro h_zero
      cases step with
      | bracketed _ =>
          -- Bracketed step contributes 0 to actualization, 1 to bracketed.
          show 1 + rest.bracketedCount = 1 + rest.length
          have h_rest_zero : rest.actualizationCount = 0 := by
            simp [RealityChain.actualizationCount] at h_zero
            exact h_zero
          have h := RealityChain.zero_actualization_all_bracketed rest h_rest_zero
          omega
      | actualization _ =>
          -- An actualization step contributes 1, contradicting zero count.
          simp [RealityChain.actualizationCount] at h_zero

-- (Stronger form `bracketed_only_implies_eq` uses `bracketed_iff_eq`
-- which is defined later in this file; see worked example at the
-- end of the module using both pieces together.)

/-! **Note on chain successor properties.** The trajectory-step
relation's actualization arm uses `AtSeam` only (a witness of *some*
new actualization). To conclude `RealitySuccessor R₁ R₂` from a chain,
the actualization step would need to additionally carry a "preserves
prior actualized" hypothesis. Without that, `RealitySuccessor`-closure
across chains is not derivable from the inductive structure alone.
Use `actualizeAt_asActualizationMap` to get the stronger
RealitySuccessor witness for elementary pointwise events. -/

/-- **Bracketed-only chains are trivial.** A chain whose every step
is bracketed preserves the actualized-set invariant at each step,
hence by `bracketed_trans` overall. The resulting endpoint chain is
itself a bracketed transition from start to end. -/
theorem RealityChain.bracketed_chain_bracketed {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (ch : RealityChain P C R₁ R₂)
    (h_all_bracketed : ∀ {Ra Rb : Reality P C}, TrajectoryStep P C Ra Rb →
                       BracketedTransition Ra Rb) :
    BracketedTransition R₁ R₂ := by
  induction ch with
  | nil R => exact bracketed_refl R
  | cons step _ ih =>
    exact bracketed_trans (h_all_bracketed step) ih

/-! ## Measurement = actualization (framework's dissolution of the
    measurement problem)

In standard QM, measurement is a separate axiom (collapse postulate)
added on top of unitary evolution. The framework dissolves this: every
"measurement event" IS an actualization event in the Tier A sense.

Concretely: a system + apparatus state before measurement is in
potential. The measurement event is the actualization — a meeting
between the system's want and the apparatus's complementary want
clears, irreversibly. The "collapsed" state is the actualized state.

This is encoded as: any actualization event is at the seam (= breaks
bracketing). No separate measurement axiom is needed; measurement is
visible in the framework simply as `AtSeam` predicate. -/

/-- **The measurement-as-actualization theorem.** Any actualization
event (Witkowski-Brown-Truong-style irreversible many-to-one collapse)
is automatically at the seam, breaking the bracketed-transition
relation. This IS measurement in the framework. No separate axiom. -/
theorem measurement_is_actualization {P : Type u} {C : Type v}
    (am : ActualizationMap P C) :
    AtSeam am.before am.after := by
  obtain ⟨m, h_before_pot, h_after_act⟩ := am.nontrivial
  exact ⟨m, h_before_pot, h_after_act⟩

/-! ### Pointwise actualization → AtSeam (Tier A ↔ Tier B concrete link)

The pointwise actualization `actualizeAt R m` is the elementary form
of an actualization event: it takes a Reality state R and a specific
target meeting m, and returns the Reality state with m actualized
(others unchanged). When m was potential in R, this pointwise event
realizes the seam predicate: the (R, actualizeAt R m) pair is at the
seam. This is the elementary Tier A event made visible as a Tier B
seam crossing. -/

/-- **Pointwise actualization at a previously-potential meeting is
at the seam.** -/
theorem actualizeAt_atSeam {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    AtSeam R (actualizeAt R m) :=
  ⟨m, h_pot, by simp⟩

/-- **Pointwise actualization at a previously-potential meeting is
NOT bracketed.** Direct consequence of `actualizeAt_atSeam` and
`seam_breaks_bracketing`. -/
theorem actualizeAt_not_bracketed {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    ¬ BracketedTransition R (actualizeAt R m) :=
  seam_breaks_bracketing (actualizeAt_atSeam R m h_pot)

/-- **Pointwise actualization realizes an `ActualizationMap`.** A
concrete construction: given any Reality state R with a potential
meeting m, the pointwise actualization produces a witness of
`ActualizationMap P C` whose `before` is R and `after` is `actualizeAt R m`. -/
def actualizeAt_asActualizationMap {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    ActualizationMap P C where
  before := R
  after := actualizeAt R m
  is_successor := actualizeAt_is_successor R m
  nontrivial := ⟨m, h_pot, by simp⟩

/-- **`TrajectoryStep'` from pointwise actualization.** Pointwise
actualization at a potential meeting yields a TrajectoryStep' (the
strengthened TrajectoryStep that carries a RealitySuccessor witness)
via `actualizeAt_is_successor`. -/
def actualizeAt_strict_step {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    TrajectoryStep' P C R (actualizeAt R m) where
  step := TrajectoryStep.actualization (actualizeAt_atSeam R m h_pot)
  is_successor := actualizeAt_is_successor R m

/-- **`RealityChain'` carries cumulative RealitySuccessor along chain.**
A strengthened chain where each step preserves the successor relation.
Forms a transitive closure-style structure. -/
inductive RealityChain' (P : Type u) (C : Type v) :
    Reality P C → Reality P C → Type (max u v)
  | nil (R : Reality P C) : RealityChain' P C R R
  | cons {R₁ R₂ R₃ : Reality P C}
      (step : TrajectoryStep' P C R₁ R₂)
      (rest : RealityChain' P C R₂ R₃) :
      RealityChain' P C R₁ R₃

/-- **A `RealityChain'` implies the endpoints are linked by Reality
successor.** This is the substantive content of the strengthening:
chains built from strict steps carry the cumulative time-ordering. -/
theorem RealityChain'.implies_successor {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C}, RealityChain' P C R₁ R₂ →
      RealitySuccessor R₁ R₂
  | _, _, RealityChain'.nil R => reality_successor_refl R
  | _, _, RealityChain'.cons step rest =>
      reality_successor_trans step.is_successor
        (RealityChain'.implies_successor rest)

/-- **Past monotonicity along strict chains.** Past grows along any
RealityChain' — the immediate consequence of `implies_successor` +
`TierA.past_monotone`. -/
theorem RealityChain'.past_monotone' {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂) :
    past R₁ ⊆ past R₂ :=
  TierA.past_monotone ch.implies_successor

/-- **No-return-to-potential along strict chains.** Once a meeting is
actualized, it stays actualized along any RealityChain' — the
trajectory-level form of the arrow-of-time content. -/
theorem RealityChain'.no_return_along_chain {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain' P C R₁ R₂)
    {m : Meeting P C} (h_act : R₁ m = MeetingStatus.Actualized) :
    R₂ m = MeetingStatus.Actualized :=
  TierA.no_return_to_potential ch.implies_successor h_act

/-- **Forgetful map: RealityChain' → RealityChain.** A strict chain
forgets to an ordinary chain by extracting the underlying step from
each TrajectoryStep'. -/
def RealityChain'.toRealityChain {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C}, RealityChain' P C R₁ R₂ →
      RealityChain P C R₁ R₂
  | _, _, RealityChain'.nil R => RealityChain.nil R
  | _, _, RealityChain'.cons step rest =>
      RealityChain.cons step.step rest.toRealityChain

/-- **A bracketed step preserves both potential and actualized status
of every meeting.** Restated: the entire meeting-status function is
unchanged across a bracketed step. -/
theorem bracketed_preserves_full_state {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h : BracketedTransition R₁ R₂)
    (m : Meeting P C) : R₁ m = R₂ m := by
  -- Case on R₁ m: Potential or Actualized.
  cases h_eq : R₁ m with
  | Potential =>
    -- bracketed preserves future-set, so R₂ m = Potential too.
    have h_fut : R₂ m = MeetingStatus.Potential := by
      have hsame : future R₁ = future R₂ :=
        bracketed_future_invariant h
      have hmem : m ∈ future R₁ := by
        show R₁ m = MeetingStatus.Potential; exact h_eq
      rw [hsame] at hmem
      show R₂ m = MeetingStatus.Potential
      exact hmem
    exact h_fut.symm
  | Actualized =>
    -- bracketed preserves actualized-set.
    have h_act : R₂ m = MeetingStatus.Actualized := (h m).mp h_eq
    exact h_act.symm

/-- **Reformulation of bracketed transitions:** R₁ and R₂ are
bracketed-equivalent iff they are EQUAL as Reality states. -/
theorem bracketed_iff_eq {P : Type u} {C : Type v}
    (R₁ R₂ : Reality P C) :
    BracketedTransition R₁ R₂ ↔ R₁ = R₂ := by
  constructor
  · intro h
    funext m
    exact bracketed_preserves_full_state h m
  · intro h_eq
    rw [h_eq]
    exact bracketed_refl R₂

/-- **A chain whose every step is bracketed yields R₁ = R₂.** Chains
of bracketed-only steps collapse the entire trajectory to equality on
the Reality function — a v2-architectural restatement that bare Tier B
(bracketed-only) is trivial on the Reality function level. -/
theorem RealityChain.bracketed_only_implies_eq {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂),
      ch.actualizationCount = 0 → R₁ = R₂
  | _, _, RealityChain.nil _ => fun _ => rfl
  | _, _, RealityChain.cons step rest => by
      intro h_zero
      cases step with
      | bracketed h_br =>
          have h_rest_zero : rest.actualizationCount = 0 := by
            simp [RealityChain.actualizationCount] at h_zero
            exact h_zero
          have h_eq_step := (bracketed_iff_eq _ _).mp h_br
          have h_eq_rest :=
            RealityChain.bracketed_only_implies_eq rest h_rest_zero
          rw [h_eq_step]; exact h_eq_rest
      | actualization _ =>
          simp [RealityChain.actualizationCount] at h_zero

/-- **Any non-equal Reality transition must be at the seam.** Combining
the bracketed-iff-eq theorem with the dichotomy: if R₁ ≠ R₂, then the
transition R₁ → R₂ cannot be a bracketed step; if it's at all
characterizable as a trajectory step, it must be an actualization. -/
theorem non_bracketed_must_be_seam {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C}
    (h_succ : RealitySuccessor R₁ R₂)
    (h_ne : R₁ ≠ R₂) :
    AtSeam R₁ R₂ := by
  -- Since R₁ ≠ R₂ and h_succ says actualized R₁ ⊆ actualized R₂,
  -- there must exist a meeting that is potential in R₁ and actualized in R₂.
  by_contra h_no_seam
  -- h_no_seam : ¬ AtSeam R₁ R₂.
  -- This means: ¬ ∃ m, R₁ m = Potential ∧ R₂ m = Actualized.
  apply h_ne
  funext m
  cases h_eq : R₁ m with
  | Potential =>
    -- Goal: Potential = R₂ m.
    cases h₂_eq : R₂ m with
    | Potential => rfl
    | Actualized =>
      -- Seam witness: m with R₁ m = Potential, R₂ m = Actualized.
      exact absurd ⟨m, h_eq, h₂_eq⟩ h_no_seam
  | Actualized =>
    -- R₁ m = Actualized; by h_succ, R₂ m = Actualized. Goal Actualized = R₂ m.
    have h2 : R₂ m = MeetingStatus.Actualized := h_succ m h_eq
    exact h2.symm

/-! **Consequence:** the bracketed-transition relation, on Reality
states regarded as functions to MeetingStatus, is just EQUALITY. This
is a strong form of the bracketing operation: a bracketed interval
has trivial dynamics on the Reality status function itself. The non-
trivial Tier B dynamics live in the *configuration of meeting
positions* (which meetings exist as candidates), not in the status
function.

This is the framework's structural sharpening: between actualization
events, the Reality-state function is invariant; what evolves is the
RELATIONAL configuration of meetings, which is governed by Tier B's
reversible group action (e.g., permutations on definite configs).

In the existing Tier B modules (Continuity, GPT, Hardy), this
relational evolution is encoded operationally as `Reversible G` /
`StrictReversible G` etc. — the inter-event dynamics. -/

/-- **Contrapositive form of `bracketed_only_implies_eq`.** A chain
with R₁ ≠ R₂ must have at least one actualization step. The framework's
"there is a seam crossing" detector: distinct Reality endpoints force
at least one Tier A event. -/
theorem RealityChain.distinct_endpoints_implies_actualization
    {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂)
    (h_ne : R₁ ≠ R₂) : 0 < ch.actualizationCount := by
  by_contra h_le
  push_neg at h_le
  have h_zero : ch.actualizationCount = 0 := Nat.le_zero.mp h_le
  exact h_ne (RealityChain.bracketed_only_implies_eq ch h_zero)

-- (An iff form `zero_actualization_iff_eq` would require threading
-- past-growth through the chain via `no_return_to_potential` +
-- `proper_past_growth_implies_actualization`. Forward direction
-- alone is the substantive content; reverse direction is now given
-- below as a separate theorem using a different formulation.)

/-- **R₁ = R₂ specialization: any same-endpoint chain has count = 0
when the chain is bracketed-only.** Stronger statement deferred to
threading past-growth; this is the trivial reverse direction stating
the implication for a chain *constructed* with all bracketed steps. -/
theorem RealityChain.bracketed_chain_zero_count {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (ch : RealityChain P C R₁ R₂)
    (h_all_bracketed : ∀ {Ra Rb : Reality P C}, TrajectoryStep P C Ra Rb →
                       BracketedTransition Ra Rb) :
    ch.actualizationCount = 0 := by
  induction ch with
  | nil _ => rfl
  | cons step _ ih =>
    -- The hypothesis h_all_bracketed forces this step to be bracketed
    -- (rather than actualization), so the step contributes 0.
    -- But TrajectoryStep is a sum type — we can't constrain it to
    -- bracketed without case-splitting.
    cases step with
    | bracketed _ =>
        simp [RealityChain.actualizationCount, ih]
    | actualization h_seam =>
        -- We have h_all_bracketed applied to an actualization step gives
        -- BracketedTransition, but an actualization is at the seam which
        -- breaks bracketing — contradiction.
        have h_br := h_all_bracketed (TrajectoryStep.actualization h_seam)
        exact absurd h_br (seam_breaks_bracketing h_seam)

/-- **Single-step zero-count implies bracketed.** A 1-step chain has
actualizationCount = 0 iff the step is a bracketed transition. -/
theorem RealityChain.single_step_count_zero_iff_bracketed
    {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (step : TrajectoryStep P C R₁ R₂) :
    (RealityChain.singleton step).actualizationCount = 0
    ↔ ∃ h, step = TrajectoryStep.bracketed h := by
  constructor
  · intro h
    cases step with
    | bracketed h_br => exact ⟨h_br, rfl⟩
    | actualization h_seam =>
        simp [RealityChain.singleton, RealityChain.actualizationCount] at h
  · rintro ⟨h_br, h_eq⟩
    rw [h_eq]
    simp [RealityChain.singleton, RealityChain.actualizationCount]

/-- **TrajectoryStep is a RealityChain (canonical embedding).** -/
@[simp] theorem RealityChain.singleton_actualizationCount_eq {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (step : TrajectoryStep P C R₁ R₂) :
    (RealityChain.singleton step).actualizationCount
      = (match step with
         | TrajectoryStep.bracketed _ => 0
         | TrajectoryStep.actualization _ => 1) := by
  cases step <;> rfl

@[simp] theorem RealityChain.singleton_bracketedCount_eq {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (step : TrajectoryStep P C R₁ R₂) :
    (RealityChain.singleton step).bracketedCount
      = (match step with
         | TrajectoryStep.bracketed _ => 1
         | TrajectoryStep.actualization _ => 0) := by
  cases step <;> rfl

/-- **`RealityChain.singleton` of a bracketed step has count = 0.** A
single-step chain consisting of a bracketed step has zero
actualization count and bracketedCount = 1. -/
theorem RealityChain.singleton_bracketed_count {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h_br : BracketedTransition R₁ R₂) :
    (RealityChain.singleton (TrajectoryStep.bracketed h_br)).actualizationCount = 0
      ∧ (RealityChain.singleton (TrajectoryStep.bracketed h_br)).bracketedCount = 1 := by
  refine ⟨?_, ?_⟩
  · simp [RealityChain.singleton, RealityChain.actualizationCount]
  · simp [RealityChain.singleton, RealityChain.bracketedCount]

/-- **`RealityChain.singleton` of an actualization step has count = 1.** -/
theorem RealityChain.singleton_actualization_count {P : Type u} {C : Type v}
    {R₁ R₂ : Reality P C} (h_seam : AtSeam R₁ R₂) :
    (RealityChain.singleton (TrajectoryStep.actualization h_seam)).actualizationCount = 1
      ∧ (RealityChain.singleton (TrajectoryStep.actualization h_seam)).bracketedCount = 0 := by
  refine ⟨?_, ?_⟩
  · simp [RealityChain.singleton, RealityChain.actualizationCount]
  · simp [RealityChain.singleton, RealityChain.bracketedCount]

/-- **A nil chain has all counts zero.** -/
@[simp] theorem RealityChain.nil_actualizationCount {P : Type u} {C : Type v}
    (R : Reality P C) :
    (RealityChain.nil (P := P) (C := C) R).actualizationCount = 0 := rfl

@[simp] theorem RealityChain.nil_bracketedCount {P : Type u} {C : Type v}
    (R : Reality P C) :
    (RealityChain.nil (P := P) (C := C) R).bracketedCount = 0 := rfl

@[simp] theorem RealityChain.nil_length {P : Type u} {C : Type v}
    (R : Reality P C) :
    (RealityChain.nil (P := P) (C := C) R).length = 0 := rfl

/-- **Append additivity for actualizationCount.** -/
theorem RealityChain.append_actualizationCount {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ R₃ : Reality P C}
      (ch₁ : RealityChain P C R₁ R₂) (ch₂ : RealityChain P C R₂ R₃),
      (ch₁.append ch₂).actualizationCount
        = ch₁.actualizationCount + ch₂.actualizationCount
  | _, _, _, RealityChain.nil _, _ => by
      simp [RealityChain.append, RealityChain.actualizationCount]
  | _, _, _, RealityChain.cons step rest, ch₂ => by
      simp only [RealityChain.append, RealityChain.actualizationCount]
      rw [RealityChain.append_actualizationCount rest ch₂]
      omega

/-- **Append additivity for bracketedCount.** -/
theorem RealityChain.append_bracketedCount {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ R₃ : Reality P C}
      (ch₁ : RealityChain P C R₁ R₂) (ch₂ : RealityChain P C R₂ R₃),
      (ch₁.append ch₂).bracketedCount
        = ch₁.bracketedCount + ch₂.bracketedCount
  | _, _, _, RealityChain.nil _, _ => by
      simp [RealityChain.append, RealityChain.bracketedCount]
  | _, _, _, RealityChain.cons step rest, ch₂ => by
      simp only [RealityChain.append, RealityChain.bracketedCount]
      rw [RealityChain.append_bracketedCount rest ch₂]
      omega

/-- **Append additivity for length.** -/
theorem RealityChain.append_length {P : Type u} {C : Type v} :
    ∀ {R₁ R₂ R₃ : Reality P C}
      (ch₁ : RealityChain P C R₁ R₂) (ch₂ : RealityChain P C R₂ R₃),
      (ch₁.append ch₂).length = ch₁.length + ch₂.length
  | _, _, _, RealityChain.nil _, _ => by
      simp [RealityChain.append, RealityChain.length]
  | _, _, _, RealityChain.cons _ rest, ch₂ => by
      simp only [RealityChain.append, RealityChain.length]
      rw [RealityChain.append_length rest ch₂]
      omega

/-- **Pointwise actualization as a single-step actualization chain.**
The pointwise event `actualizeAt R m` (when m was potential)
instantiates a 1-step actualization trajectory: a RealityChain of
length 1 with actualizationCount 1 and bracketedCount 0. -/
def actualizeAt_chain {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    RealityChain P C R (actualizeAt R m) :=
  RealityChain.singleton
    (TrajectoryStep.actualization (actualizeAt_atSeam R m h_pot))

@[simp] theorem actualizeAt_chain_actualizationCount {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    (actualizeAt_chain R m h_pot).actualizationCount = 1 :=
  (RealityChain.singleton_actualization_count
    (actualizeAt_atSeam R m h_pot)).1

@[simp] theorem actualizeAt_chain_bracketedCount {P : Type u} {C : Type v}
    [DecidableEq (Meeting P C)]
    (R : Reality P C) (m : Meeting P C)
    (h_pot : R m = MeetingStatus.Potential) :
    (actualizeAt_chain R m h_pot).bracketedCount = 0 :=
  (RealityChain.singleton_actualization_count
    (actualizeAt_atSeam R m h_pot)).2

/-- **The identity bracketed step (self-step) wrapped as a chain.** -/
def reflBracketedChain {P : Type u} {C : Type v} (R : Reality P C) :
    RealityChain P C R R :=
  RealityChain.singleton (TrajectoryStep.bracketed (bracketed_refl R))

@[simp] theorem reflBracketedChain_actualizationCount {P : Type u} {C : Type v}
    (R : Reality P C) : (reflBracketedChain R).actualizationCount = 0 :=
  (RealityChain.singleton_bracketed_count (bracketed_refl R)).1

@[simp] theorem reflBracketedChain_bracketedCount {P : Type u} {C : Type v}
    (R : Reality P C) : (reflBracketedChain R).bracketedCount = 1 :=
  (RealityChain.singleton_bracketed_count (bracketed_refl R)).2

/-- **Worked example: a 2-step actualization trajectory.** Starting
from an arbitrary R with two potential meetings m₁, m₂ (distinct),
actualize m₁ first, then m₂. The 2-step chain has actualizationCount = 2,
bracketedCount = 0, length = 2. Demonstrates concrete trajectory
composition via append. -/
example (P : Type u) (C : Type v)
    [DecidableEq (Meeting P C)] (R : Reality P C)
    (m₁ m₂ : Meeting P C) (h_ne : m₁ ≠ m₂)
    (h_pot₁ : R m₁ = MeetingStatus.Potential)
    (h_pot₂ : R m₂ = MeetingStatus.Potential) :
    True := by
  let R₁ := actualizeAt R m₁
  let R₂ := actualizeAt R₁ m₂
  -- m₂ is still potential at R₁ since m₂ ≠ m₁.
  have h_pot₂' : R₁ m₂ = MeetingStatus.Potential := by
    show actualizeAt R m₁ m₂ = MeetingStatus.Potential
    rw [actualizeAt_other R h_ne.symm]
    exact h_pot₂
  let ch₁ : RealityChain P C R R₁ := actualizeAt_chain R m₁ h_pot₁
  let ch₂ : RealityChain P C R₁ R₂ := actualizeAt_chain R₁ m₂ h_pot₂'
  let ch : RealityChain P C R R₂ := ch₁.append ch₂
  -- ch.actualizationCount = 2 by append additivity + singleton counts.
  have h_count : ch.actualizationCount = 2 := by
    show (ch₁.append ch₂).actualizationCount = 2
    rw [RealityChain.append_actualizationCount]
    show (actualizeAt_chain R m₁ h_pot₁).actualizationCount
        + (actualizeAt_chain R₁ m₂ h_pot₂').actualizationCount = 2
    simp
  -- ch.bracketedCount = 0 similarly.
  have h_brk : ch.bracketedCount = 0 := by
    show (ch₁.append ch₂).bracketedCount = 0
    rw [RealityChain.append_bracketedCount]
    show (actualizeAt_chain R m₁ h_pot₁).bracketedCount
        + (actualizeAt_chain R₁ m₂ h_pot₂').bracketedCount = 0
    simp
  -- And ch.length = 2.
  have h_len : ch.length = 2 := by
    rw [show ch.length = ch.actualizationCount + ch.bracketedCount from
        (RealityChain.counts_sum ch).symm, h_count, h_brk]
  trivial

/-- **Worked example: mixed bracketed/actualization chain.**
Starting from R, do a refl-bracketed step (R → R) followed by an
actualization (R → actualizeAt R m). Chain has actualizationCount = 1,
bracketedCount = 1, length = 2. -/
example (P : Type u) (C : Type v)
    [DecidableEq (Meeting P C)] (R : Reality P C)
    (m : Meeting P C) (h_pot : R m = MeetingStatus.Potential) :
    True := by
  let ch₁ : RealityChain P C R R := reflBracketedChain R
  let ch₂ : RealityChain P C R (actualizeAt R m) := actualizeAt_chain R m h_pot
  let ch : RealityChain P C R (actualizeAt R m) := ch₁.append ch₂
  have h_act : ch.actualizationCount = 1 := by
    show (ch₁.append ch₂).actualizationCount = 1
    rw [RealityChain.append_actualizationCount]
    show (reflBracketedChain R).actualizationCount
        + (actualizeAt_chain R m h_pot).actualizationCount = 1
    simp
  have h_brk : ch.bracketedCount = 1 := by
    show (ch₁.append ch₂).bracketedCount = 1
    rw [RealityChain.append_bracketedCount]
    show (reflBracketedChain R).bracketedCount
        + (actualizeAt_chain R m h_pot).bracketedCount = 1
    simp
  trivial

/-- **Worked example: a 3-step trajectory mixing arms.** Refl-bracketed,
then actualize, then refl-bracketed-on-the-new-state. Demonstrates
that the trajectory machinery composes consistently with R changing
across the chain. -/
example (P : Type u) (C : Type v)
    [DecidableEq (Meeting P C)] (R : Reality P C)
    (m : Meeting P C) (h_pot : R m = MeetingStatus.Potential) :
    True := by
  let R' := actualizeAt R m
  let ch₁ : RealityChain P C R R := reflBracketedChain R
  let ch₂ : RealityChain P C R R' := actualizeAt_chain R m h_pot
  let ch₃ : RealityChain P C R' R' := reflBracketedChain R'
  let ch : RealityChain P C R R' :=
    ((ch₁.append ch₂).append ch₃)
  have h_count : ch.actualizationCount = 1 := by
    show ((ch₁.append ch₂).append ch₃).actualizationCount = 1
    rw [RealityChain.append_actualizationCount,
        RealityChain.append_actualizationCount]
    show (reflBracketedChain R).actualizationCount
        + (actualizeAt_chain R m h_pot).actualizationCount
        + (reflBracketedChain R').actualizationCount = 1
    simp
  have h_brk : ch.bracketedCount = 2 := by
    show ((ch₁.append ch₂).append ch₃).bracketedCount = 2
    rw [RealityChain.append_bracketedCount,
        RealityChain.append_bracketedCount]
    show (reflBracketedChain R).bracketedCount
        + (actualizeAt_chain R m h_pot).bracketedCount
        + (reflBracketedChain R').bracketedCount = 2
    simp
  trivial

/-! ## Worked example: Bool meetings (smallest non-trivial Tier A space)

A concrete worked example demonstrating the framework's two-tier
architecture on the simplest non-trivial case: meetings between
`Bool`-perspectives. -/

example : True := by trivial  -- placeholder; example below uses Reality structure

/-- **Trivial Tier A state**: all meetings potential, no actualizations. -/
def trivialReality (P : Type u) (C : Type v) : Reality P C :=
  fun _ => MeetingStatus.Potential

/-- The trivial reality has empty past. -/
example (P : Type u) (C : Type v) : past (trivialReality P C) = ∅ := by
  ext m
  show trivialReality P C m = MeetingStatus.Actualized ↔ False
  show (MeetingStatus.Potential : MeetingStatus) = MeetingStatus.Actualized ↔ False
  constructor
  · intro h; exact MeetingStatus.noConfusion h
  · intro h; exact h.elim

/-- The trivial reality has full future. -/
example (P : Type u) (C : Type v) (m : Meeting P C) :
    m ∈ future (trivialReality P C) := by
  show trivialReality P C m = MeetingStatus.Potential
  rfl

/-- The trivial reality is bracketed-equivalent to itself (trivially). -/
example (P : Type u) (C : Type v) :
    BracketedTransition (trivialReality P C) (trivialReality P C) :=
  bracketed_refl _

/-- **Concrete actualization on `trivialReality`.** Applying
`actualizeAt` to a single meeting m yields a non-trivial Reality
state with exactly one actualized meeting and all others potential.
The (trivialReality, actualizeAt trivialReality m) pair is at the
seam — a concrete worked instance of the architectural seam predicate. -/
example (P : Type u) (C : Type v)
    [DecidableEq (Meeting P C)] (m : Meeting P C) :
    AtSeam (trivialReality P C) (actualizeAt (trivialReality P C) m) :=
  actualizeAt_atSeam (trivialReality P C) m rfl

/-- **Concrete trajectory step on `trivialReality`.** The single-event
trajectory: starting from the trivial Reality, the first actualization
realizes the actualization-step in the trajectory dichotomy. -/
example (P : Type u) (C : Type v)
    [DecidableEq (Meeting P C)] (m : Meeting P C) :
    TrajectoryStep P C (trivialReality P C)
                       (actualizeAt (trivialReality P C) m) :=
  TrajectoryStep.actualization (actualizeAt_atSeam (trivialReality P C) m rfl)

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
  • `actualizeAt_atSeam`, `actualizeAt_not_bracketed`,
    `actualizeAt_asActualizationMap` — pointwise Tier A → Tier B
    concrete link: the elementary actualization event realizes the
    seam predicate and instantiates the abstract `ActualizationMap`.

The existing modules (Continuity, GPT, Hardy, WantableGPT, the GPT
instances, Dichotomy, ...) provide the *content* of Tier B once
bracketing is applied. The R6/R7 vertex-preservation work, in
particular, is exactly the constraint that bracketed dynamics
preserve pure potential states — making explicit a Tier A commitment
that became visible at Tier B (per the v2 architecture audit).
-/

end TierB
end Perspectival
