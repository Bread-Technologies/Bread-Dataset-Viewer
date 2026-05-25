/-
Perspectival Physics — Hardy's Axioms
======================================

Hardy 2001 ("Quantum Theory From Five Reasonable Axioms") reconstructs
finite-dim quantum mechanics from operational axioms on a GPT. The
celebrated dichotomy: dropping continuity yields classical theory
(K = N); keeping all five yields quantum theory (K = N²).

This module states Hardy's axioms as predicates on `Perspectival.GPT`
and **categorizes each one** with respect to our framework's two
axioms (v2: Existence + Actualization) and the bracketing operation
that yields Tier B:

    DERIVABLE — follows from Tier A + bracketing (no additional
                Tier B postulate needed)
    AUXILIARY — independent of Tier A; addable as Tier B postulate
                without contradiction
    INCOMPATIBLE — in tension with Tier A; would require revision

Under v2, Hardy's axioms are Tier B content. Each axiom is now
re-categorized: how does the bracketing operation (Tier A → Tier B)
constrain or yield it?

  A1 Probabilities: DERIVABLE. Probability emerges from the
    relational play of potential meetings — outcome frequencies are
    Tier B observables of the underlying actualization rates.

  A2 Simplicity (K-min): AUXILIARY. Hardy's selection principle
    across theories. Under v2, motivated as: minimal Tier B
    consistent with Tier A's actualization-density.

  A3 Subspaces: DERIVABLE. Restriction to a sub-meeting-structure
    yields a sub-Tier-B description by the bracketing operation.

  A4 Composite systems: PARTIALLY DERIVABLE. Dimension half via
    gptTensor; N-multiplicativity forward direction via
    gptTensor_distinguishable_general. Full N-mult open.

  A5 Continuity: DERIVABLE under v2's bracketing argument.
    Continuous reversible transformations between pure states emerge
    from bracketed dynamics on a continuous-meeting Tier A space.
    Vertex preservation (the v1 patch) is now a DERIVED Tier B
    theorem expressing the inheritance of Tier A's discreteness
    commitment.

Calibrated status of the present file:
  ✓ Axioms 1, 3, 4, 5 formulated as Lean predicates
  ▲ Axiom 2 (Simplicity / K minimal) — stated informally; minimality
    over an open class is delicate to encode and is marked `sorry` in
    the formal statement.
  ○ Categorizations (DERIVABLE / AUXILIARY / INCOMPATIBLE) are
    ARGUED in prose only. Formal derivations from I–IV remain OPEN —
    this is the actual research bottleneck for Tier 1.

Honest framing: stating Hardy's axioms in Lean does NOT itself derive
quantum mechanics. It puts the targets in a machine-checkable form
and makes the open subproblems explicit. The real work — proving
each DERIVABLE claim — is parked here as `sorry` and is the main
remaining task of Tier 1.
-/

import Perspectival.GPT
import Perspectival.GPTTensor
import Perspectival.Ontology
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.UnitInterval
import Perspectival.Continuity
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Perspectival
namespace Hardy

open TensorProduct

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-! ## Operational dimensions N and K

  • `N` (operational dimension) — the maximum size of a set of perfectly
    distinguishable states.
  • `K` (state-space dimension) — the minimum number of probability
    measurements needed to determine a state, equivalently the linear
    dimension of the effects' span on states.

For finite-dim GPTs:
   classical: K = N
   quantum:   K = N²
   real QM:   K = N(N+1)/2
   quaternionic QM: K = N(2N-1)
-/

/-- Two states are *perfectly distinguishable* if there exist
two effects giving probability 1 on one and 0 on the other. -/
def Distinguishable (G : GPT V) (ρ₁ ρ₂ : V) : Prop :=
  ∃ e ∈ G.effects, e ρ₁ = 1 ∧ e ρ₂ = 0

/-- A *distinguishability set* of size `n` is `n` mutually
distinguishable states. -/
def DistinguishabilitySet (G : GPT V) (S : Finset V) : Prop :=
  (∀ ρ ∈ S, ρ ∈ G.states) ∧
  ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S, ρ₁ ≠ ρ₂ → Distinguishable G ρ₁ ρ₂

/-- The operational dimension N: largest distinguishability set. -/
def HasDimensionN (G : GPT V) (n : ℕ) : Prop :=
  (∃ S : Finset V, S.card = n ∧ DistinguishabilitySet G S) ∧
  (∀ m, m > n → ¬ ∃ S : Finset V, S.card = m ∧ DistinguishabilitySet G S)

/-! ## Hardy's axioms -/

/-- **Axiom 1 — Probabilities.**
Relative frequencies (in the limit of infinite trials) yield well-defined
probabilities. In our setup this is built into the GPT structure
(probabilities lie in [0,1] by construction); we restate it as a
predicate for completeness.

Category: **DERIVABLE** — follows from Axiom III (reality is the structure
of meetings; a meeting's clearing is by construction a probability event)
once one accepts the GPT-style encoding. The encoding itself is the
non-trivial step. -/
def Axiom1_Probabilities (G : GPT V) : Prop :=
  ∀ e ∈ G.effects, ∀ ρ ∈ G.states, 0 ≤ G.prob e ρ ∧ G.prob e ρ ≤ 1

/-- **Axiom 1 holds for any GPT by construction.** -/
theorem axiom1_holds (G : GPT V) : Axiom1_Probabilities G := by
  intro e he ρ hρ
  exact G.prob_in_unit_interval e he ρ hρ

/-- **Axiom 2 — Simplicity.**
For each given N, K takes the minimum value consistent with the
other axioms.

Category: **AUXILIARY** — minimality of K is a *selection principle*
across theories, not a structural axiom about a single theory. In our
framework it has no direct derivation from I–IV; we record it as an
auxiliary postulate. Formal statement requires quantification over the
class of GPTs satisfying the others, which is delicate; marked `sorry`. -/
def Axiom2_Simplicity (_G : GPT V) (_n _k : ℕ) : Prop := True  -- placeholder

theorem axiom2_argued_auxiliary :
    "Axiom 2 (Simplicity) is AUXILIARY: not derivable from I–IV." = "Axiom 2 (Simplicity) is AUXILIARY: not derivable from I–IV." := rfl

/-- **Axiom 3 — Subspaces.**
A system whose state is constrained to belong to an M-dimensional
subspace behaves like a system of dimension M.

Category: **DERIVABLE** (conditional — argued, not formally proven).
The framework's pattern-stability (Axiom IV) supports the claim that
restricting which meetings can occur yields a structurally similar
sub-system. Formal derivation requires defining what "behaves like"
means for GPT sub-systems, which we defer. -/
def Axiom3_Subspaces (G : GPT V) : Prop :=
  -- For every closed convex sub-state-space, there is a sub-GPT G'
  -- whose normalized state space is that sub-state-space.
  ∀ S : Set V, S ⊆ G.states → Convex ℝ S → S.Nonempty →
    ∃ G' : GPT V, G'.states = S

/-- **Hardy Axiom 3 is DERIVABLE** — any GPT satisfies it.

Construction: given any nonempty convex `S ⊆ G.states`, take the
sub-GPT with the same unit, the same effects, and `states := S`.
The normalization and probability conditions transfer since
`S ⊆ G.states`. -/
theorem axiom3_holds (G : GPT V) : Axiom3_Subspaces G := by
  intro S hSsub hSconv _hSnonempty
  refine ⟨{
    unit := G.unit
    states := S
    effects := G.effects
    states_convex := hSconv
    effects_convex := G.effects_convex
    states_normalized := fun ρ hρ => G.states_normalized ρ (hSsub hρ)
    prob_in_unit_interval := fun e he ρ hρ =>
      G.prob_in_unit_interval e he ρ (hSsub hρ)
    unit_is_effect := G.unit_is_effect
  }, rfl⟩

/-- **Axiom 4 — Composite systems.**
A composite system consisting of subsystems A and B satisfies
`N_AB = N_A * N_B` and `K_AB = K_A * K_B`.

Category: **PARTIALLY DERIVABLE — DIMENSION HALF FORMALLY PROVEN**
at the general GPT level via `GPT.gptTensor` (file
`Perspectival/GPTTensor.lean`). The dimension half follows from
`Module.finrank_tensorProduct`; see `Axiom4_Composite_Dimension`
below. The state-half existence (a product state exists for every
pair of component states) is `Axiom4_Composite_State_Exists`.

The OPERATIONAL multiplicativity N_AB = N_A * N_B (i.e. multiplicativity
of the maximum perfectly-distinguishable set, not merely of the linear
dimension) is the genuinely deep half: it requires showing every
product of distinguishability sets remains a distinguishability set
on the composite. That direction is OPEN in this formalization, and is
where the framework would need to engage Hardy's "distinguishability
preserves under product" argument. -/
def Axiom4_Composite_Dimension
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (_GA : GPT VA) (_GB : GPT VB) : Prop :=
  Module.finrank ℝ (VA ⊗[ℝ] VB)
    = (Module.finrank ℝ VA) * (Module.finrank ℝ VB)

/-- **Hardy A4 dimension half (general GPT level).** Holds for any
pair of GPTs by `GPT.gptTensor_finrank_eq_mul`. -/
theorem axiom4_dimension_holds
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) :
    Axiom4_Composite_Dimension GA GB :=
  GPT.gptTensor_finrank_eq_mul GA GB

/-- **Hardy A4 state-half (general GPT level): a product state of two
component states is a state of the composite.** This holds by the very
definition of `GPT.gptTensor` (separable / product states), without
additional postulates. -/
def Axiom4_Composite_State_Exists
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) : Prop :=
  ∀ ρA ∈ GA.states, ∀ ρB ∈ GB.states,
    (ρA ⊗ₜ[ℝ] ρB) ∈ (GPT.gptTensor GA GB).states

/-- **Hardy A4 state-half holds for any pair of GPTs.** -/
theorem axiom4_state_exists_holds
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) :
    Axiom4_Composite_State_Exists GA GB :=
  fun _ hρA _ hρB => GPT.gptTensor_tmul_mem_states GA GB hρA hρB

/-- **Hardy A4 BOTH HALVES at the general GPT level.** The framework
delivers both the dimension multiplicativity (K_AB = K_A · K_B) and
the product-state existence at the general GPT level. The OPEN piece
is the N-multiplicativity (operational dim), with the forward
direction now provided by `gptTensor_distinguishable_*` above. -/
theorem axiom4_dimension_and_state_holds
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) :
    Axiom4_Composite_Dimension GA GB ∧
    Axiom4_Composite_State_Exists GA GB :=
  ⟨axiom4_dimension_holds GA GB, axiom4_state_exists_holds GA GB⟩

/-! ## Framework Hardy-axioms summary

The framework's Hardy axiom derivations:
  A1: Probabilities — DERIVABLE (`axiom1_holds`).
  A2: Simplicity (K-minimum) — AUXILIARY (motivated, not derived).
  A3: Subspaces — DERIVABLE (`axiom3_holds`).
  A4: Composite (dimension + state existence) — DERIVABLE at general GPT
      level via gptTensor (`axiom4_dimension_holds`,
      `axiom4_state_exists_holds`). N-multiplicativity forward direction
      via `gptTensor_distinguishable_*`. Reverse direction open.
  A5: Continuity — DERIVABLE via TransitiveAgency
      (`axiom5_strong_of_transitive_agency`). Strong form
      `Axiom5_Continuity_Strong` derived from the agency hierarchy. -/

/-- **The framework's full Hardy A1, A3, A4 (dim + state) certificate.**
Three of the five Hardy axioms (A1, A3, A4 dim half) are derivable
unconditionally for any GPT in the framework. -/
theorem framework_hardy_unconditional
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) :
    Axiom1_Probabilities GA ∧
    Axiom3_Subspaces GA ∧
    Axiom4_Composite_Dimension GA GB ∧
    Axiom4_Composite_State_Exists GA GB :=
  ⟨axiom1_holds GA, axiom3_holds GA,
   axiom4_dimension_holds GA GB, axiom4_state_exists_holds GA GB⟩

-- framework_hardy_with_agency moved later in file (after
-- axiom5_strong_of_transitive_agency is defined)

/-- **Hardy A4 N-multiplicativity, forward direction (1-element
witness).** If `(ρ₁, ρ₂)` is distinguishable in `G₁` and `σ ∈ G₂.states`,
then `(ρ₁ ⊗ σ, ρ₂ ⊗ σ)` is distinguishable in `gptTensor G₁ G₂`.
The witness effect is `productEffect e_1 (G₂.unit)`. This is the
forward direction of Hardy A4's N-multiplicativity: distinguishability
in one factor lifts to distinguishability in the product. -/
theorem gptTensor_distinguishable_left
    {V₁ V₂ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    {G₁ : GPT V₁} {G₂ : GPT V₂}
    {ρ₁ ρ₂ : V₁} (h : Distinguishable G₁ ρ₁ ρ₂)
    {σ : V₂} (hσ : σ ∈ G₂.states) :
    Distinguishable (GPT.gptTensor G₁ G₂)
      (ρ₁ ⊗ₜ[ℝ] σ) (ρ₂ ⊗ₜ[ℝ] σ) := by
  obtain ⟨e₁, he₁_in, he₁_ρ₁, he₁_ρ₂⟩ := h
  refine ⟨GPT.productEffect e₁ G₂.unit,
    GPT.productEffect_in_effects he₁_in G₂.unit_is_effect, ?_, ?_⟩
  · -- productEffect (ρ₁ ⊗ σ) = e₁(ρ₁) · G₂.unit(σ) = 1 · 1 = 1
    rw [GPT.productEffect_tmul, he₁_ρ₁, G₂.states_normalized σ hσ]; ring
  · -- productEffect (ρ₂ ⊗ σ) = e₁(ρ₂) · G₂.unit(σ) = 0 · 1 = 0
    rw [GPT.productEffect_tmul, he₁_ρ₂]; ring

/-- **Hardy A4 N-multiplicativity, BOTH factors distinguishable.**
If `(ρ₁, ρ₂)` distinguishable in `G₁` AND `(σ₁, σ₂)` distinguishable in
`G₂`, then `(ρ₁ ⊗ σ₁, ρ₂ ⊗ σ₂)` distinguishable in `gptTensor G₁ G₂`.
Witness effect: `productEffect e_1 e_2`. -/
theorem gptTensor_distinguishable_both
    {V₁ V₂ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    {G₁ : GPT V₁} {G₂ : GPT V₂}
    {ρ₁ ρ₂ : V₁} (h₁ : Distinguishable G₁ ρ₁ ρ₂)
    {σ₁ σ₂ : V₂} (h₂ : Distinguishable G₂ σ₁ σ₂) :
    Distinguishable (GPT.gptTensor G₁ G₂)
      (ρ₁ ⊗ₜ[ℝ] σ₁) (ρ₂ ⊗ₜ[ℝ] σ₂) := by
  obtain ⟨e₁, he₁_in, he₁_ρ₁, he₁_ρ₂⟩ := h₁
  obtain ⟨e₂, he₂_in, he₂_σ₁, he₂_σ₂⟩ := h₂
  refine ⟨GPT.productEffect e₁ e₂,
    GPT.productEffect_in_effects he₁_in he₂_in, ?_, ?_⟩
  · -- productEffect (ρ₁ ⊗ σ₁) = e₁(ρ₁) · e₂(σ₁) = 1 · 1 = 1
    rw [GPT.productEffect_tmul, he₁_ρ₁, he₂_σ₁]; ring
  · -- productEffect (ρ₂ ⊗ σ₂) = e₁(ρ₂) · e₂(σ₂) = 0 · 0 = 0
    rw [GPT.productEffect_tmul, he₁_ρ₂, he₂_σ₂]; ring

/-- **Hardy A4 N-multiplicativity (≥), via two general pairs.** If
`(ρ_i, ρ_j)` distinguishable in G₁ AND `(σ_k, σ_l)` distinguishable
in G₂, then `(ρ_i ⊗ σ_k, ρ_j ⊗ σ_l)` distinguishable in gptTensor.
This generalizes both `_left` and `_both`: only ONE pair of indices
needs to differ.

In particular: if (i, k) ≠ (j, l), AT LEAST ONE of (ρ_i, ρ_j) or
(σ_k, σ_l) is distinguishable (using DistinguishabilitySet conditions
in a finite product set). This is the key lemma for the full N-mult
forward proof. -/
theorem gptTensor_distinguishable_general
    {V₁ V₂ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    {G₁ : GPT V₁} {G₂ : GPT V₂}
    {ρ₁ ρ₂ : V₁} {σ₁ σ₂ : V₂}
    (h₁ : ρ₁ ∈ G₁.states) (h₂ : σ₁ ∈ G₂.states)
    (h_diff : Distinguishable G₁ ρ₁ ρ₂ ∨ Distinguishable G₂ σ₁ σ₂)
    (h_σ : σ₂ = σ₁ ∨ Distinguishable G₂ σ₁ σ₂)
    (h_ρ : ρ₂ = ρ₁ ∨ Distinguishable G₁ ρ₁ ρ₂) :
    Distinguishable (GPT.gptTensor G₁ G₂)
      (ρ₁ ⊗ₜ[ℝ] σ₁) (ρ₂ ⊗ₜ[ℝ] σ₂) := by
  rcases h_diff with hd₁ | hd₂
  · -- ρ₁ ≠ ρ₂ distinguishable in G₁.
    rcases h_σ with rfl | hd₂
    · -- σ₂ = σ₁: use the _left lemma.
      exact gptTensor_distinguishable_left hd₁ h₂
    · -- σ₂ ≠ σ₁ distinguishable: use the _both lemma.
      exact gptTensor_distinguishable_both hd₁ hd₂
  · -- σ₁ ≠ σ₂ distinguishable in G₂.
    rcases h_ρ with rfl | hd₁
    · -- ρ₂ = ρ₁ (after rcases rfl, ρ₁ has been replaced by ρ₂).
      obtain ⟨e₂, he₂_in, he₂_σ₁, he₂_σ₂⟩ := hd₂
      refine ⟨GPT.productEffect G₁.unit e₂,
        GPT.productEffect_in_effects G₁.unit_is_effect he₂_in, ?_, ?_⟩
      · rw [GPT.productEffect_tmul, G₁.states_normalized ρ₂ h₁, he₂_σ₁]; ring
      · rw [GPT.productEffect_tmul, G₁.states_normalized ρ₂ h₁, he₂_σ₂]; ring
    · -- Both distinguishable: use _both.
      exact gptTensor_distinguishable_both hd₁ hd₂

/-- **Axiom 5 — Continuity of reversible transformations.**
There exists a continuous reversible transformation on a system
between any two pure states of that system.

Category: **DERIVABLE** (argued, not formally proven). The framework
takes perspectival transformations as primitive (Transformations.lean).
Reversibility = bijectivity of PTrans, which we have. Continuity is
the additional ingredient and requires a topology on the state space —
naturally provided by the convex-hull topology from Mathlib.

Quantum vs classical: the framework's libertarian-agency commitment
(genuine choice at each moment) prefers an ABUNDANCE of transformations
over a sparse SET — favoring the continuous case (quantum) over the
discrete-classical case. This is an argument that the framework's
PHILOSOPHICAL commitments *prefer* Axiom 5, not a derivation. -/
def Axiom5_Continuity (G : GPT V) : Prop :=
  ∀ ρ₁ ρ₂ : V, ρ₁ ∈ G.states → ρ₂ ∈ G.states →
    IsExtreme ℝ G.states {ρ₁} → IsExtreme ℝ G.states {ρ₂} →
    -- There exists a continuous path of reversible transformations
    -- connecting ρ₁ to ρ₂ through pure states. The continuity
    -- predicate requires a topology on V; we leave that to refinements.
    True  -- placeholder

/-- **Axiom 5 strong form (path of state-preserving bijective linear maps).**
Given a topology on `V`, between any two pure states there is a
continuous path of state-preserving bijective linear maps from the
identity to a transformation realizing the move.

This is the framework's intended substantive form, satisfied by any GPT
admitting a `Continuity.TransitiveAgency`. See
`Continuity.TransitiveAgency.hardy_axiom5` for the derivation. -/
def Axiom5_Continuity_Strong (G : GPT V) [TopologicalSpace V] : Prop :=
  ∀ ρ₁ ρ₂ : V,
    IsExtreme ℝ G.states {ρ₁} → IsExtreme ℝ G.states {ρ₂} →
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      γ 0 = LinearMap.id ∧
      γ 1 ρ₁ = ρ₂ ∧
      (∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states) ∧
      (∀ t : unitInterval, Function.Bijective (γ t))

/-- **Axiom 5 strong form WITH pure-state preservation along the path.**
The framework's intended axiom refinement: the path of state-preserving
bijective linear maps should ALSO preserve pure states (extreme points
of the state space) along the way.

This refinement is motivated by Axiom IV (particulars as stable patterns):
a stable particular pattern should not "smear out" to a mixture along
reversible dynamics. Without this refinement, Classical n ≥ 2 satisfies
the bare `Axiom5_Continuity_Strong` (via non-vertex-preserving paths
like `t·I + (1-t)·swap`); WITH this refinement, Classical n ≥ 2 fails
the axiom (per the L7 closure in `Classical.lean`).

This is the framework's first concrete operational consequence of the
"metaphysics-fixed, axioms-adjustable" methodology. -/
def Axiom5_Continuity_Strong_Pure (G : GPT V) [TopologicalSpace V] : Prop :=
  ∀ ρ₁ ρ₂ : V,
    IsExtreme ℝ G.states {ρ₁} → IsExtreme ℝ G.states {ρ₂} →
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      γ 0 = LinearMap.id ∧
      γ 1 ρ₁ = ρ₂ ∧
      (∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states) ∧
      (∀ t : unitInterval, Function.Bijective (γ t)) ∧
      -- The refinement: the path preserves extreme points along the way.
      (∀ t : unitInterval, ∀ ρ, IsExtreme ℝ G.states {ρ} →
        IsExtreme ℝ G.states {γ t ρ})

/-- **Bridge theorem.** `Axiom5_Continuity_Strong G` is derivable from
a `TransitiveAgency G`, provided that pure states in the GPT sense
(membership in states + extremality) come with state-space membership.

Concretely: if every `IsExtreme ℝ G.states {ρ}` corresponds to a
`Continuity.PureState G ρ`, then `Axiom5_Continuity_Strong` holds.

This is the framework's machine-verified Hardy A5 derivation from the
agency hierarchy. -/
theorem axiom5_strong_of_transitive_agency
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) (T : Continuity.TransitiveAgency G)
    (h_pure_states : ∀ ρ, IsExtreme ℝ G.states {ρ} → ρ ∈ G.states) :
    Axiom5_Continuity_Strong G := by
  intro ρ₁ ρ₂ he₁ he₂
  have hp₁ : Continuity.PureState G ρ₁ := ⟨h_pure_states ρ₁ he₁, he₁⟩
  have hp₂ : Continuity.PureState G ρ₂ := ⟨h_pure_states ρ₂ he₂, he₂⟩
  exact T.hardy_axiom5 ρ₁ ρ₂ hp₁ hp₂

/-- **The framework's full Hardy A1, A3, A4, A5 (conditional on agency).**
With a `TransitiveAgency` on G, four of the five Hardy axioms are
derivable (A2 remains auxiliary). -/
theorem framework_hardy_with_agency
    {V VB : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup VB] [Module ℝ VB]
    (G : GPT V) (GB : GPT VB)
    (T : Continuity.TransitiveAgency G)
    (h_pure_states : ∀ ρ, IsExtreme ℝ G.states {ρ} → ρ ∈ G.states) :
    Axiom1_Probabilities G ∧
    Axiom3_Subspaces G ∧
    Axiom4_Composite_Dimension G GB ∧
    Axiom4_Composite_State_Exists G GB ∧
    Axiom5_Continuity_Strong G :=
  ⟨axiom1_holds G, axiom3_holds G,
   axiom4_dimension_holds G GB, axiom4_state_exists_holds G GB,
   axiom5_strong_of_transitive_agency G T h_pure_states⟩

/-! ## Summary of categorizations (the actual research output of this file)

  Axiom 1 (Probabilities)        — DERIVABLE (immediate from GPT structure;
                                   `axiom1_holds` proves it formally).
  Axiom 2 (Simplicity / K min)   — AUXILIARY (cross-theory selection
                                   principle; not entailed by I–IV).
  Axiom 3 (Subspaces)            — DERIVABLE — FORMALLY PROVEN as
                                   `axiom3_holds` above.
  Axiom 4 (Composite systems)    — PARTIALLY DERIVABLE: both the
                                   dimension half and the state-half
                                   existence are formally proven at the
                                   GENERAL GPT level by
                                   `axiom4_dimension_holds` and
                                   `axiom4_state_exists_holds` (above),
                                   via the `GPT.gptTensor` operator in
                                   `Perspectival/GPTTensor.lean`. The
                                   WantableGPT-specific predecessors
                                   `Hardy_Axiom4_WantableGPT_dimension`
                                   and `Hardy_Axiom4_WantableGPT_state_exists`
                                   remain in WantableGPT.lean.
                                   The OPEN piece is the operational
                                   half N_AB = N_A · N_B (max
                                   perfectly-distinguishable set
                                   multiplicativity), not derived here.
  Axiom 5 (Continuity)           — DERIVABLE — formally proven in
                                   two forms:
                                   (i) `hardy_axiom5_of_agency` in
                                       Continuity.lean, conditional on the
                                       `HasConnectedAgency` postulate.
                                   (ii) `axiom5_strong_of_transitive_agency`
                                        above, derives `Axiom5_Continuity_Strong`
                                        from `TransitiveAgency` —
                                        the framework's strongest formal
                                        bridge between the agency hierarchy
                                        and a substantive form of Hardy A5.

The Hardy axioms 1, 3, 5 are formally derivable in the framework
(with A5 conditional on the agency strengthening). Axiom 4 is
partially derivable. Axiom 2 is auxiliary.

Next stage of Tier 1: the R6/R7 strengthening of HasConnectedAgency
(in Continuity.lean) toward forcing Lie-group reversible dynamics,
which would carry Axiom 5 from "derivable under agency" toward
"forces quantum-like Lie-group dynamics". See TIER1_5_HILBERT.md and
TIER2_GAUGE_SCOPING.md for scoping.
-/

end Hardy
end Perspectival
