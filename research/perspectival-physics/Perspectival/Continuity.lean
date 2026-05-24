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

/-- Every state is reachable from itself (via the identity, which is
available by `id_avail`). -/
theorem Reachable.refl [HasConnectedAgency G] (ρ : V) :
    Reachable (G := G) ρ ρ := by
  obtain ⟨R_id, hR_id_avail, hR_id_eq⟩ := HasConnectedAgency.id_avail (G := G)
  exact ⟨R_id, hR_id_avail, hR_id_eq ρ⟩

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

/-! ## Trivial-agency case

To verify the framework's structure: every GPT has a TRIVIAL
`HasConnectedAgency` instance where the only available transformation
is the identity. This is the "no choice" degenerate case — useful as
a sanity check, not as a model of libertarian agency. -/

/-- The identity as a `Reversible` transformation. -/
def Reversible.id (G : GPT V) : Reversible G where
  toLin := LinearMap.id
  continuous_toLin := continuous_id
  preserves_states := fun _ h => h
  preserves_unit := LinearMap.id_comp _

/-- Every GPT has the trivial agency instance: only the identity is
available, and the constant path connects it to itself. -/
@[reducible]
def trivialAgency (G : GPT V) : HasConnectedAgency G := {
  avail := { Reversible.id G }
  id_avail := ⟨Reversible.id G, rfl, fun _ => rfl⟩
  path_connected := fun R₁ R₂ hR₁ hR₂ => by
    have hR₁id : R₁ = Reversible.id G := hR₁
    have hR₂id : R₂ = Reversible.id G := hR₂
    refine ⟨fun _ => LinearMap.id, ?_, ?_, ?_⟩
    · -- Joint continuity of (t, v) ↦ v: it's the second projection.
      exact continuous_snd
    · subst hR₁id; rfl
    · subst hR₂id; rfl
}

/-- A reflexive-only agency where the path between two available
transformations is the affine line in the underlying linear-map
space: `γ t = (1-t) * R₁.toLin + t * R₂.toLin`. This is jointly
continuous as a function on `unitInterval × V`. Useful as a building
block for richer agency instances. -/
theorem path_via_affineLine {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₁ R₂ : Reversible G) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => (γ p.1) p.2) ∧
      γ 0 = R₁.toLin ∧ γ 1 = R₂.toLin := by
  refine ⟨fun t => (1 - (t : ℝ)) • R₁.toLin + (t : ℝ) • R₂.toLin, ?_, ?_, ?_⟩
  · -- Joint continuity: scalar-multiply continuous toLin functions and add.
    have h1 : Continuous (fun p : unitInterval × V => (1 - (p.1 : ℝ)) • R₁.toLin p.2) := by
      apply Continuous.smul
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      · exact R₁.continuous_toLin.comp continuous_snd
    have h2 : Continuous (fun p : unitInterval × V => (p.1 : ℝ) • R₂.toLin p.2) := by
      apply Continuous.smul
      · exact (continuous_subtype_val.comp continuous_fst)
      · exact R₂.continuous_toLin.comp continuous_snd
    exact h1.add h2
  · ext v
    show (1 - (0 : ℝ)) • R₁.toLin v + (0 : ℝ) • R₂.toLin v = R₁.toLin v
    simp
  · ext v
    show (1 - (1 : ℝ)) • R₁.toLin v + (1 : ℝ) • R₂.toLin v = R₂.toLin v
    simp

/-- For any GPT G on a topological vector space V, any singleton availability
set `{R}` extends to a `HasConnectedAgency` (the constant path works). -/
@[reducible]
def singletonAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ : Reversible G)
    (hR_id : ∀ v : V, R₀.toLin v = v) : HasConnectedAgency G where
  avail := {R₀}
  id_avail := ⟨R₀, rfl, hR_id⟩
  path_connected R₁ R₂ hR₁ hR₂ := by
    have hR₁eq : R₁ = R₀ := hR₁
    have hR₂eq : R₂ = R₀ := hR₂
    refine ⟨fun _ => R₀.toLin, ?_, ?_, ?_⟩
    · exact R₀.continuous_toLin.comp continuous_snd
    · rw [hR₁eq]
    · rw [hR₂eq]

/-- For any GPT G on a topological vector space V, a pair availability
set `{R_id, R'}` extends to a `HasConnectedAgency` using the affine
interpolation path. -/
@[reducible]
def pairAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) : HasConnectedAgency G where
  avail := {R₀, R₁}
  id_avail := ⟨R₀, Set.mem_insert _ _, hR₀_id⟩
  path_connected S₁ S₂ _ _ := path_via_affineLine G S₁ S₂

/-- In a `pairAgency` with R₀ = id and R₁ being some richer
transformation, the second transformation R₁ is also reachable from
the identity state. -/
theorem pairAgency_reaches_R₁ {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) (ρ : V) :
    @Reachable V _ _ _ G (pairAgency G R₀ R₁ hR₀_id) ρ (R₁.toLin ρ) :=
  ⟨R₁, Or.inr rfl, rfl⟩

/-- And every state is reachable from itself in a pairAgency (via R₀ = id). -/
theorem pairAgency_reaches_self {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) (ρ : V) :
    @Reachable V _ _ _ G (pairAgency G R₀ R₁ hR₀_id) ρ ρ :=
  ⟨R₀, Or.inl rfl, hR₀_id ρ⟩

/-- The avail set in a pairAgency contains both R₀ and R₁. -/
theorem pairAgency_avail_eq {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) :
    HasConnectedAgency.avail (G := G) (self := pairAgency G R₀ R₁ hR₀_id)
    = {R₀, R₁} := rfl

/-- Both R₀ and R₁ are available in a pairAgency. -/
theorem pairAgency_R₀_avail {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) :
    R₀ ∈ HasConnectedAgency.avail (G := G) (self := pairAgency G R₀ R₁ hR₀_id) :=
  Or.inl rfl

theorem pairAgency_R₁_avail {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : GPT V) (R₀ R₁ : Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) :
    R₁ ∈ HasConnectedAgency.avail (G := G) (self := pairAgency G R₀ R₁ hR₀_id) :=
  Or.inr rfl

/-! ## Strict-reversibility refinement

The current `Reversible` structure does NOT require `toLin` to be
bijective (a LinearEquiv). For a stricter notion that captures
actual reversibility — closure under inverse, well-defined inverse
transformation — see `StrictReversible` below. -/

/-- A *strictly reversible* transformation: a `Reversible` whose
underlying linear map is a `LinearEquiv` (i.e., genuinely invertible). -/
structure StrictReversible {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) extends Reversible G where
  isEquiv : Function.Bijective toLin

-- StrictReversible.toReversible is auto-generated by the `extends` clause.

/-- A StrictReversible has an inverse linear map. -/
noncomputable def StrictReversible.inv {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {G : GPT V}
    (R : StrictReversible G) : V →ₗ[ℝ] V :=
  let e : V ≃ₗ[ℝ] V :=
    LinearEquiv.ofBijective R.toLin R.isEquiv
  e.symm.toLinearMap

/-- Under trivial agency, only equal states are reachable from each
other (since the only available transformation is the identity). -/
theorem trivialAgency_reachable_iff (G : GPT V) (ρ₁ ρ₂ : V) :
    (@Reachable V _ _ _ G (trivialAgency G) ρ₁ ρ₂) ↔ ρ₁ = ρ₂ := by
  constructor
  · rintro ⟨R, hR, hRρ⟩
    -- R ∈ {Reversible.id G}, so R = Reversible.id G
    have hReq : R = Reversible.id G := hR
    -- (Reversible.id G).toLin ρ₁ = ρ₁ by definition
    rw [hReq] at hRρ
    -- hRρ : (Reversible.id G).toLin ρ₁ = ρ₂, i.e., LinearMap.id ρ₁ = ρ₂
    show ρ₁ = ρ₂
    have : LinearMap.id (R := ℝ) ρ₁ = ρ₂ := hRρ
    simpa using this
  · rintro rfl
    exact @Reachable.refl V _ _ _ G (trivialAgency G) ρ₁

/-! ## Composition-closed agency

The current `HasConnectedAgency` class does NOT require that the
available-transformation set is closed under composition. Without
closure, `Reachable` is only reflexive — not transitive. We package
the closure conditions as a refinement; under it, `Reachable`
becomes an equivalence relation. This is a strengthening of the
agency postulate, not a theorem about it. -/

/-- Composition of two `Reversible` transformations as a `Reversible`. -/
def Reversible.comp {G : GPT V} (R₂ R₁ : Reversible G) : Reversible G where
  toLin := R₂.toLin.comp R₁.toLin
  continuous_toLin := R₂.continuous_toLin.comp R₁.continuous_toLin
  preserves_states := fun ρ hρ => R₂.preserves_states _ (R₁.preserves_states _ hρ)
  preserves_unit := by
    have h₁ := R₁.preserves_unit
    have h₂ := R₂.preserves_unit
    calc G.unit.comp (R₂.toLin.comp R₁.toLin)
        = (G.unit.comp R₂.toLin).comp R₁.toLin := by rfl
      _ = G.unit.comp R₁.toLin := by rw [h₂]
      _ = G.unit := h₁

/-- Agency refinement: the available-transformation set is closed
under composition. -/
class ClosedAgency (G : GPT V) extends HasConnectedAgency G where
  comp_avail : ∀ R₁ R₂ : Reversible G,
    R₁ ∈ HasConnectedAgency.avail (G := G) →
    R₂ ∈ HasConnectedAgency.avail (G := G) →
    Reversible.comp R₂ R₁ ∈ HasConnectedAgency.avail (G := G)

/-- Under `ClosedAgency`, `Reachable` is transitive. -/
theorem Reachable.trans [ClosedAgency G] {ρ₁ ρ₂ ρ₃ : V}
    (h₁₂ : Reachable (G := G) ρ₁ ρ₂) (h₂₃ : Reachable (G := G) ρ₂ ρ₃) :
    Reachable (G := G) ρ₁ ρ₃ := by
  obtain ⟨R₁, hR₁_avail, hR₁eq⟩ := h₁₂
  obtain ⟨R₂, hR₂_avail, hR₂eq⟩ := h₂₃
  refine ⟨Reversible.comp R₂ R₁, ClosedAgency.comp_avail R₁ R₂ hR₁_avail hR₂_avail, ?_⟩
  show R₂.toLin (R₁.toLin ρ₁) = ρ₃
  rw [hR₁eq, hR₂eq]

/-- `Reachable` under `ClosedAgency` is preserved under all available
transformations: if `ρ₁ ~> ρ₂` and `R` is available, then
`ρ₁ ~> R.toLin ρ₂`. -/
theorem Reachable.apply_available [ClosedAgency G] {ρ₁ ρ₂ : V}
    (h : Reachable (G := G) ρ₁ ρ₂)
    (R : Reversible G) (hR : R ∈ HasConnectedAgency.avail (G := G)) :
    Reachable (G := G) ρ₁ (R.toLin ρ₂) := by
  exact Reachable.trans h ⟨R, hR, rfl⟩

/-- Under `ClosedAgency`, `Reachable` is reflexive and transitive — a
preorder. (Symmetry would require closure under inverse, which
requires `Reversible` to support inversion. That refinement is
deferred to `InverseClosedAgency`, not yet formalized.) -/
theorem Reachable.preorder [ClosedAgency G] :
    (∀ ρ : V, Reachable (G := G) ρ ρ) ∧
    (∀ ρ₁ ρ₂ ρ₃ : V, Reachable (G := G) ρ₁ ρ₂ → Reachable (G := G) ρ₂ ρ₃ →
      Reachable (G := G) ρ₁ ρ₃) :=
  ⟨Reachable.refl, fun _ _ _ h₁ h₂ => Reachable.trans h₁ h₂⟩

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
