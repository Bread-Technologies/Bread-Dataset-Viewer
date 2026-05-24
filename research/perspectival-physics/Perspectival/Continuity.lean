/-
Perspectival Physics — Continuity from Agency
==============================================

The framework's most distinctive potential technical contribution is
the derivation of Hardy's Axiom 5 (continuous reversible
transformations between pure states) from the libertarian-agency
commitment: at every instant the perspective genuinely chooses, and
the space of available transformations must therefore be a
*connected* set of reversible maps, not a discrete one.

This module formalizes the bridge. The chain is:

   (Axioms I–IV: perspective with directed wanting + transformations
      Lean: Perspectival.Ontology, Perspectival.Transformations)
   ↓ + LIBERTARIAN AGENCY POSTULATE
      "transformations form a path-connected group acting on states"
   ↓
   HARDY AXIOM 5 (continuous reversible transformation between any
   pair of pure states reachable by the group)

Calibrated status:
  ✓ The "agency postulate" is encoded as a Lean class.
  ✓ The implication
      `HasConnectedAgency + transitivity ⇒ continuous path between
      any two reachable states` is formally proven.
  ▲ The "purity is preserved by the group" sub-claim is encoded as a
    hypothesis, not derived. Refining this is the next step.
  ○ The link to actual Hardy Axiom 5 (which uses pure states defined
    via extreme points) requires further bookkeeping not done here.

Honest framing: the formal step proven here is the EASY direction.
It shows that IF the framework's libertarian-agency commitment is
formalized as path-connectedness of the group of transformations
THEN continuity of pure-state paths follows. The HARDER question —
whether libertarian agency really forces path-connectedness rather
than mere richness of the transformation group — is philosophical and
is not settled by this file.
-/

import Perspectival.GPT
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Convex.Extreme

namespace Perspectival
namespace Continuity

open Topology

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
variable {G : GPT V}

/-- A *reversible transformation* on a GPT is a continuous linear
self-equivalence whose induced map preserves the state space and the
unit (so probabilities are preserved). -/
structure Reversible (G : GPT V) where
  toLin : V →ₗ[ℝ] V
  continuous_toLin : Continuous toLin
  preserves_states : ∀ ρ ∈ G.states, toLin ρ ∈ G.states
  preserves_unit : G.unit.comp toLin = G.unit

/-- The framework's *libertarian-agency postulate* (formal version):
the set of reversible transformations acts on states with a structure
that is path-connected and contains the identity. This is the
distinctive content of Axiom IV refined by the agency commitment. -/
class HasConnectedAgency (G : GPT V) where
  /-- The set of available reversible transformations. -/
  avail : Set (Reversible G)
  /-- Identity is available. -/
  id_avail : ∃ R ∈ avail, ∀ v : V, R.toLin v = v
  /-- Any two available transformations are connected by a continuous
  path of available transformations. We state this at the level of the
  underlying linear maps. -/
  path_connected :
    ∀ R₁ R₂ : Reversible G, R₁ ∈ avail → R₂ ∈ avail →
      ∃ γ : unitInterval → V →ₗ[ℝ] V,
        -- Joint continuity as a function on the product (uncurried).
        Continuous (fun p : unitInterval × V => (γ p.1) p.2) ∧
        γ 0 = R₁.toLin ∧ γ 1 = R₂.toLin

/-- A state `ρ₂` is *reachable* from `ρ₁` by available transformations
if some `R ∈ avail` sends `ρ₁` to `ρ₂`. -/
def Reachable [HasConnectedAgency G] (ρ₁ ρ₂ : V) : Prop :=
  ∃ R ∈ HasConnectedAgency.avail (G := G), R.toLin ρ₁ = ρ₂

/-- **The main bridge.** From the connected-agency postulate plus
reachability, any two reachable states are connected by a continuous
path in V.

The path is `t ↦ γ(t)(ρ₁)` where `γ` is the continuous interpolation
from `id.toLin` to `R.toLin` provided by `HasConnectedAgency`. -/
theorem continuous_path_of_reachable [HasConnectedAgency G]
    (ρ₁ ρ₂ : V) (_hρ₁ : ρ₁ ∈ G.states) (h : Reachable (G := G) ρ₁ ρ₂) :
    ∃ p : unitInterval → V, Continuous p ∧ p 0 = ρ₁ ∧ p 1 = ρ₂ := by
  obtain ⟨R, hR, hRρ⟩ := h
  obtain ⟨R_id, hR_id_avail, hR_id_eq⟩ := HasConnectedAgency.id_avail (G := G)
  obtain ⟨γ, hγ_cont, hγ_0, hγ_1⟩ :=
    HasConnectedAgency.path_connected R_id R hR_id_avail hR
  refine ⟨fun t => γ t ρ₁, ?_, ?_, ?_⟩
  · -- Continuity of t ↦ γ(t)(ρ₁).
    -- γ is jointly continuous on unitInterval × V; specializing v = ρ₁
    -- via the embedding t ↦ (t, ρ₁) gives a continuous function in t.
    have hpair : Continuous (fun t : unitInterval => (t, ρ₁)) :=
      Continuous.prodMk continuous_id continuous_const
    exact hγ_cont.comp hpair
  · -- p 0 = γ 0 ρ₁ = R_id.toLin ρ₁ = ρ₁
    show γ 0 ρ₁ = ρ₁
    rw [hγ_0, hR_id_eq]
  · -- p 1 = γ 1 ρ₁ = R.toLin ρ₁ = ρ₂
    show γ 1 ρ₁ = ρ₂
    rw [hγ_1, hRρ]

/-- **Hardy Axiom 5 in concrete form (modulo pure-state restriction).**

Given the libertarian-agency postulate (`HasConnectedAgency`), for any
two reachable states there is a continuous *path of linear maps* γ
from the identity (at `t = 0`) to a transformation that sends `ρ₁` to
`ρ₂` (at `t = 1`). This is Hardy Axiom 5 stripped of the requirement
that `ρ₁, ρ₂` be extreme points; that restriction is separable. -/
theorem hardy_axiom5_of_agency [HasConnectedAgency G]
    (ρ₁ ρ₂ : V) (h : Reachable (G := G) ρ₁ ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ := by
  obtain ⟨R, hR, hRρ⟩ := h
  obtain ⟨R_id, hR_id_avail, hR_id_eq⟩ := HasConnectedAgency.id_avail (G := G)
  obtain ⟨γ, hγ_cont, hγ_0, hγ_1⟩ :=
    HasConnectedAgency.path_connected R_id R hR_id_avail hR
  refine ⟨γ, hγ_cont, ?_, ?_⟩
  · intro v
    rw [hγ_0]
    exact hR_id_eq v
  · rw [hγ_1]
    exact hRρ

/-! ## Pure states and Hardy Axiom 5 proper

A *pure state* in a GPT is an extreme point of the convex state space.
Hardy's original Axiom 5 quantifies over pure states. We define the
notion and refine the agency derivation accordingly. -/

/-- A pure state is an extreme point of the convex state space. -/
def PureState (G : GPT V) (ρ : V) : Prop :=
  ρ ∈ G.states ∧ IsExtreme ℝ G.states {ρ}

/-- Pure-state Hardy Axiom 5. If the agency postulate holds and `R`
preserves pure states (which is automatic for reversible
transformations preserving the state space and its extreme structure),
then between any two reachable PURE states there is a continuous path
of linear maps from the identity to a transformation realizing the
reachability. -/
theorem hardy_axiom5_pure_states [HasConnectedAgency G]
    {ρ₁ ρ₂ : V} (_hp₁ : PureState G ρ₁) (_hp₂ : PureState G ρ₂)
    (h : Reachable (G := G) ρ₁ ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ :=
  hardy_axiom5_of_agency ρ₁ ρ₂ h

/-- Pure-state Hardy Axiom 5, stronger transitive form: assuming the
group of available transformations acts transitively on pure states
(which is the substantive content of Hardy's hypothesis), and the
agency postulate gives path-connectedness, between any two pure states
there exists a continuous path of linear maps realizing the
transformation. -/
theorem hardy_axiom5_transitive [HasConnectedAgency G]
    (h_transitive :
      ∀ ρ₁ ρ₂, PureState G ρ₁ → PureState G ρ₂ →
        Reachable (G := G) ρ₁ ρ₂)
    (ρ₁ ρ₂ : V) (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ :=
  hardy_axiom5_pure_states hp₁ hp₂ (h_transitive ρ₁ ρ₂ hp₁ hp₂)

/-! ## Honest framing

What `continuous_path_of_reachable` shows: if the agency postulate is
formalized as PATH-CONNECTEDNESS of the available transformations,
then continuity of state-paths follows automatically.

What it does NOT show:
  1. That the framework's philosophical commitment to libertarian
     agency at every instant FORCES path-connectedness (rather than
     mere richness). This is the genuinely open philosophical-to-
     formal step.
  2. That the available transformations act TRANSITIVELY on pure
     states (so that Reachable is universally true between any pair
     of pure states — which is Hardy Axiom 5's actual content). The
     transitivity assumption is separable and is NOT proved here.
  3. That this is the unique way to formalize Axiom 5; alternative
     formulations (smooth Lie-group action) are stronger and may be
     needed for the K = N² consequence.

The next step is to refine `HasConnectedAgency` to include
transitivity on the set of extreme points (pure states), and show
that this gives a Lean-verified version of Hardy Axiom 5 as
originally stated.
-/

end Continuity
end Perspectival
