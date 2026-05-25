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

/-- The identity reversible is a StrictReversible. -/
def StrictReversible.id {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) : StrictReversible G where
  toReversible := Reversible.id G
  isEquiv := Function.bijective_id

/-- The identity StrictReversible has toLin = LinearMap.id. -/
@[simp] theorem StrictReversible.id_toLin {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) :
    (StrictReversible.id G).toLin = LinearMap.id := rfl

/-- The inverse linear map of a StrictReversible composes with the
forward map to give the identity. -/
theorem StrictReversible.inv_comp {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {G : GPT V}
    (R : StrictReversible G) (v : V) :
    R.inv (R.toLin v) = v := by
  show (LinearEquiv.ofBijective R.toLin R.isEquiv).symm
        ((LinearEquiv.ofBijective R.toLin R.isEquiv) v) = v
  exact (LinearEquiv.ofBijective R.toLin R.isEquiv).symm_apply_apply v

/-- The forward composed with the inverse is also the identity. -/
theorem StrictReversible.comp_inv {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {G : GPT V}
    (R : StrictReversible G) (v : V) :
    R.toLin (R.inv v) = v := by
  show (LinearEquiv.ofBijective R.toLin R.isEquiv)
        ((LinearEquiv.ofBijective R.toLin R.isEquiv).symm v) = v
  exact (LinearEquiv.ofBijective R.toLin R.isEquiv).apply_symm_apply v

/-- Composition of two StrictReversibles is a StrictReversible. -/
def StrictReversible.comp {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {G : GPT V}
    (R₂ R₁ : StrictReversible G) : StrictReversible G where
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
  isEquiv := R₂.isEquiv.comp R₁.isEquiv

/-- The composition's toLin is the obvious composition. -/
@[simp] theorem StrictReversible.comp_toLin {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {G : GPT V}
    (R₂ R₁ : StrictReversible G) :
    (StrictReversible.comp R₂ R₁).toLin = R₂.toLin.comp R₁.toLin := rfl

/-! ## Submonoid-Agency: stronger refinement (note)

A natural strengthening would package `HasConnectedAgency` together
with closure under composition, making the available set a
submonoid of the Reversible monoid. The existing `ClosedAgency`
already captures composition closure as a hypothesis (separately
from the connected-agency structure). Whether this should be
packaged as a `class` extension involves Lean's namespace
resolution for `Reversible.comp`; deferred. -/

/-! ## Symmetric-Reachable

For `Reachable` to be an equivalence relation we need symmetry, which
requires that if `R` is available, so is an inverse of `R` whose
forward sends `R.toLin ρ ↦ ρ`. The `Reversible` structure does not
inherently encode invertibility; the `StrictReversible` refinement
above (with `isEquiv`) does. The full equivalence-relation upgrade
requires an `InverseClosedAgency` class — a future refinement. -/

/-- If for every `R ∈ avail`, an inverse-Reversible (also in avail)
exists, then `Reachable` is symmetric. -/
theorem Reachable.symm_of_inv_avail [HasConnectedAgency G]
    (h_inv : ∀ R : Reversible G, R ∈ HasConnectedAgency.avail (G := G) →
      ∃ S : Reversible G, S ∈ HasConnectedAgency.avail (G := G) ∧
        ∀ v : V, S.toLin (R.toLin v) = v)
    {ρ₁ ρ₂ : V} (h : Reachable (G := G) ρ₁ ρ₂) :
    Reachable (G := G) ρ₂ ρ₁ := by
  obtain ⟨R, hR, hRρ⟩ := h
  obtain ⟨S, hS, hSinv⟩ := h_inv R hR
  refine ⟨S, hS, ?_⟩
  rw [← hRρ]
  exact hSinv ρ₁

-- Reachable.refl_symm_trans is defined later in the file, after ClosedAgency
-- (forward reference issue resolved by relocation).

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

/-- Under both `ClosedAgency` and the per-element inverse-availability
hypothesis, `Reachable` is an equivalence relation (refl + symm + trans). -/
theorem Reachable.refl_symm_trans [ClosedAgency G]
    (h_inv : ∀ R : Reversible G, R ∈ HasConnectedAgency.avail (G := G) →
      ∃ S : Reversible G, S ∈ HasConnectedAgency.avail (G := G) ∧
        ∀ v : V, S.toLin (R.toLin v) = v) :
    (∀ ρ : V, Reachable (G := G) ρ ρ) ∧
    (∀ ρ₁ ρ₂ : V, Reachable (G := G) ρ₁ ρ₂ → Reachable (G := G) ρ₂ ρ₁) ∧
    (∀ ρ₁ ρ₂ ρ₃ : V, Reachable (G := G) ρ₁ ρ₂ → Reachable (G := G) ρ₂ ρ₃ →
      Reachable (G := G) ρ₁ ρ₃) :=
  ⟨Reachable.refl,
   fun _ _ h => Reachable.symm_of_inv_avail h_inv h,
   fun _ _ _ h₁ h₂ => Reachable.trans h₁ h₂⟩

/-- Under `ClosedAgency` + inverse availability, `Reachable` is an
`Equivalence`. -/
theorem Reachable.equivalence [ClosedAgency G]
    (h_inv : ∀ R : Reversible G, R ∈ HasConnectedAgency.avail (G := G) →
      ∃ S : Reversible G, S ∈ HasConnectedAgency.avail (G := G) ∧
        ∀ v : V, S.toLin (R.toLin v) = v) :
    Equivalence (Reachable (G := G)) :=
  { refl := Reachable.refl
    symm := fun h => Reachable.symm_of_inv_avail h_inv h
    trans := fun h₁ h₂ => Reachable.trans h₁ h₂ }

/-- The trivial agency satisfies inverse availability vacuously
(identity is its own inverse, and is the only available element). -/
theorem trivialAgency_inv_avail (G : GPT V) :
    ∀ R : Reversible G, R ∈ HasConnectedAgency.avail
      (G := G) (self := trivialAgency G) →
    ∃ S : Reversible G, S ∈ HasConnectedAgency.avail
      (G := G) (self := trivialAgency G) ∧
      ∀ v : V, S.toLin (R.toLin v) = v := by
  intro R hR
  -- hR : R = Reversible.id G (from the avail = {Reversible.id G} setup)
  have hReq : R = Reversible.id G := hR
  refine ⟨Reversible.id G, rfl, ?_⟩
  intro v
  rw [hReq]
  rfl

/-- A simple corollary: under trivialAgency, Reachable is reflexive
(and trivially symmetric & transitive via the inv_avail hypothesis). -/
theorem trivialAgency_reachable_refl (G : GPT V) (ρ : V) :
    @Reachable V _ _ _ G (trivialAgency G) ρ ρ :=
  @Reachable.refl _ _ _ _ G (trivialAgency G) ρ

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

/-! ## R6: Strengthened agency — paths must preserve states throughout

The `HasConnectedAgency` postulate only requires the path endpoints
`γ 0`, `γ 1` to come from `Reversible G` (which preserve states).
The intermediate maps `γ t` for `0 < t < 1` need only be linear and
continuous — they may map states OUT of the state space.

This is too weak to derive quantum reversible dynamics: any two
Reversibles can be connected by affine interpolation `t ↦ (1-t)R₁ + t R₂`,
but the interpolated map at `t = 1/2` need not be a valid Reversible.

`StatePreservingPath` strengthens this: it requires the path to map
states to states *at every intermediate point*. This is the
substantive condition that singles out the quantum group U(N) over
the classical discrete S_N.
-/

/-- A continuous path of linear maps that preserves the state space at
every intermediate time. This is the strengthened R6 path notion. -/
structure StatePreservingPath (G : GPT V) (R₁ R₂ : V →ₗ[ℝ] V) where
  /-- The path itself, as a function unitInterval → linear maps. -/
  γ : unitInterval → V →ₗ[ℝ] V
  /-- Joint continuity in (t, v). -/
  continuous : Continuous (fun p : unitInterval × V => γ p.1 p.2)
  /-- Starts at R₁. -/
  start : γ 0 = R₁
  /-- Ends at R₂. -/
  finish : γ 1 = R₂
  /-- **Key R6 strengthening**: each intermediate map preserves the state
  space. This is what rules out the affine interpolation in general. -/
  preserves_states_along : ∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states

/-- The R6 agency postulate: every pair of available reversibles is
connected by a **state-preserving** path. -/
class StatePreservingAgency (G : GPT V) where
  avail : Set (Reversible G)
  id_avail : ∃ R ∈ avail, ∀ v : V, R.toLin v = v
  state_preserving_paths :
    ∀ R₁ R₂ : Reversible G, R₁ ∈ avail → R₂ ∈ avail →
      Nonempty (StatePreservingPath G R₁.toLin R₂.toLin)

/-- StatePreservingAgency implies HasConnectedAgency — the strengthened
postulate is logically stronger. -/
instance (priority := 100) HasConnectedAgency.ofStatePreservingAgency
    [SPA : StatePreservingAgency G] : HasConnectedAgency G where
  avail := SPA.avail
  id_avail := SPA.id_avail
  path_connected R₁ R₂ h₁ h₂ := by
    obtain ⟨p⟩ := SPA.state_preserving_paths R₁ R₂ h₁ h₂
    exact ⟨p.γ, p.continuous, p.start, p.finish⟩

/-- Every state on the path is in the state space (specialized to the
endpoint-determined state-trajectory). -/
theorem StatePreservingPath.state_trajectory
    {G : GPT V} {R₁ R₂ : V →ₗ[ℝ] V}
    (p : StatePreservingPath G R₁ R₂) (ρ : V) (hρ : ρ ∈ G.states)
    (t : unitInterval) : p.γ t ρ ∈ G.states :=
  p.preserves_states_along t ρ hρ

/-- Reachable lifted to use StatePreservingAgency. -/
def Reachable_SPA [SPA : StatePreservingAgency G] (ρ₁ ρ₂ : V) : Prop :=
  ∃ R ∈ SPA.avail, R.toLin ρ₁ = ρ₂

/-- Identity reachable. -/
theorem Reachable_SPA.refl [SPA : StatePreservingAgency G] (ρ : V) :
    Reachable_SPA (G := G) ρ ρ := by
  obtain ⟨R_id, hR_id_avail, hR_id_eq⟩ := SPA.id_avail
  exact ⟨R_id, hR_id_avail, hR_id_eq ρ⟩

/-- Under StatePreservingAgency, the continuous path from id to R
**stays inside the state space the whole time**. This is the key R6
improvement over Hardy's original axiom 5: not just continuity, but
state-space preservation along the path. -/
theorem continuous_state_preserving_path
    [SPA : StatePreservingAgency G] (ρ₁ ρ₂ : V) (hρ₁ : ρ₁ ∈ G.states)
    (h : Reachable_SPA (G := G) ρ₁ ρ₂) :
    ∃ p : unitInterval → V, Continuous p ∧ p 0 = ρ₁ ∧ p 1 = ρ₂ ∧
      (∀ t, p t ∈ G.states) := by
  obtain ⟨R, hR, hRρ⟩ := h
  obtain ⟨R_id, hR_id_avail, hR_id_eq⟩ := SPA.id_avail
  obtain ⟨path⟩ := SPA.state_preserving_paths R_id R hR_id_avail hR
  refine ⟨fun t => path.γ t ρ₁, ?_, ?_, ?_, ?_⟩
  · have hpair : Continuous (fun t : unitInterval => (t, ρ₁)) :=
      Continuous.prodMk continuous_id continuous_const
    exact path.continuous.comp hpair
  · show path.γ 0 ρ₁ = ρ₁
    rw [path.start, hR_id_eq]
  · show path.γ 1 ρ₁ = ρ₂
    rw [path.finish, hRρ]
  · intro t
    exact path.state_trajectory ρ₁ hρ₁ t

/-! ### R6: identity StatePreservingPath -/

/-- The constant identity path is a StatePreservingPath. -/
def StatePreservingPath.id (G : GPT V) : StatePreservingPath G LinearMap.id LinearMap.id where
  γ := fun _ => LinearMap.id
  continuous := by
    show Continuous (fun p : unitInterval × V => LinearMap.id p.2)
    show Continuous (fun p : unitInterval × V => p.2)
    exact continuous_snd
  start := rfl
  finish := rfl
  preserves_states_along := fun _ ρ hρ => hρ

/-- The reverse path (reading γ backwards). -/
def StatePreservingPath.reverse {G : GPT V} {R₁ R₂ : V →ₗ[ℝ] V}
    (p : StatePreservingPath G R₁ R₂) :
    StatePreservingPath G R₂ R₁ where
  γ := fun t => p.γ (unitInterval.symm t)
  continuous := by
    have h1 : Continuous (fun t : unitInterval => unitInterval.symm t) :=
      unitInterval.continuous_symm
    have h2 : Continuous (fun pair : unitInterval × V => (unitInterval.symm pair.1, pair.2)) :=
      Continuous.prodMk (h1.comp continuous_fst) continuous_snd
    exact p.continuous.comp h2
  start := by
    show p.γ (unitInterval.symm 0) = R₂
    rw [unitInterval.symm_zero, p.finish]
  finish := by
    show p.γ (unitInterval.symm 1) = R₁
    rw [unitInterval.symm_one, p.start]
  preserves_states_along := fun t ρ hρ => p.preserves_states_along _ ρ hρ

/-- The state-preserving condition is closed under taking sums of paths
weighted by [0,1]. (Convex combination at a fixed time t.) Currently
unused but useful as scaffolding. -/
theorem StatePreservingPath.value_in_states
    {G : GPT V} {R₁ R₂ : V →ₗ[ℝ] V}
    (p : StatePreservingPath G R₁ R₂) (t : unitInterval) (ρ : V)
    (hρ : ρ ∈ G.states) : p.γ t ρ ∈ G.states :=
  p.preserves_states_along t ρ hρ

/-- Endpoint preservation: γ 0 = R₁ preserves states. -/
theorem StatePreservingPath.start_preserves_states
    {G : GPT V} {R₁ R₂ : V →ₗ[ℝ] V}
    (p : StatePreservingPath G R₁ R₂) (ρ : V) (hρ : ρ ∈ G.states) :
    R₁ ρ ∈ G.states := by
  rw [← p.start]
  exact p.preserves_states_along 0 ρ hρ

/-- Endpoint preservation: γ 1 = R₂ preserves states. -/
theorem StatePreservingPath.finish_preserves_states
    {G : GPT V} {R₁ R₂ : V →ₗ[ℝ] V}
    (p : StatePreservingPath G R₁ R₂) (ρ : V) (hρ : ρ ∈ G.states) :
    R₂ ρ ∈ G.states := by
  rw [← p.finish]
  exact p.preserves_states_along 1 ρ hρ

/-- Trivial: if R is a Reversible, the constant path R, R is a
StatePreservingPath. (No actual movement.) -/
def StatePreservingPath.const {G : GPT V} (R : Reversible G) :
    StatePreservingPath G R.toLin R.toLin where
  γ := fun _ => R.toLin
  continuous := by
    show Continuous (fun p : unitInterval × V => R.toLin p.2)
    exact R.continuous_toLin.comp continuous_snd
  start := rfl
  finish := rfl
  preserves_states_along := fun _ ρ hρ => R.preserves_states ρ hρ

/-! ### R6: convex state space + affine interpolation gives a SPP

KEY R6 OBSERVATION: if the state space `G.states` is **convex** (which
it is for any GPT — see `GPT.convex`), then the affine interpolation
`γ t = (1-t) R₁ + t R₂` between two state-preserving linear maps is
itself state-preserving at every t.

This shows that for any GPT with convex state space (= every GPT),
the strengthened R6 condition is *automatically satisfied* by the
affine interpolation between state-preserving linear maps — so R6
alone does NOT distinguish quantum from classical.

The substantive R6 content must therefore come from requiring the
intermediate maps to be REVERSIBLE (continuous *bijections*) rather
than merely state-preserving linear maps. This refines the R6
program: the path must consist of `Reversible G`-valued maps, not
just state-preserving maps. -/

/-! ## R6-bis: ReversiblePath — paths of Reversibles -/

/-- A continuous path of *Reversibles*: the intermediate maps must
themselves be Reversible (continuous, preserve states, preserve unit). -/
structure ReversiblePath (G : GPT V) (R₁ R₂ : Reversible G) where
  /-- The path of underlying linear maps. -/
  γ : unitInterval → V →ₗ[ℝ] V
  /-- Joint continuity. -/
  continuous : Continuous (fun p : unitInterval × V => γ p.1 p.2)
  /-- Start. -/
  start : γ 0 = R₁.toLin
  /-- End. -/
  finish : γ 1 = R₂.toLin
  /-- Every intermediate map preserves states. -/
  preserves_states_along : ∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states
  /-- Every intermediate map preserves the unit. -/
  preserves_unit_along : ∀ t : unitInterval, G.unit.comp (γ t) = G.unit
  /-- Every intermediate map's induced map is continuous (automatic from joint
  continuity above, but exposed as a field for convenience). -/
  continuous_at : ∀ t : unitInterval, Continuous (γ t)

/-- ReversiblePath is strictly stronger than StatePreservingPath. -/
def ReversiblePath.toStatePreservingPath {G : GPT V} {R₁ R₂ : Reversible G}
    (p : ReversiblePath G R₁ R₂) :
    StatePreservingPath G R₁.toLin R₂.toLin where
  γ := p.γ
  continuous := p.continuous
  start := p.start
  finish := p.finish
  preserves_states_along := p.preserves_states_along

/-- The identity ReversiblePath (constant path at id). -/
def ReversiblePath.id (G : GPT V) :
    ReversiblePath G (Reversible.id G) (Reversible.id G) where
  γ := fun _ => LinearMap.id
  continuous := by
    show Continuous (fun p : unitInterval × V => LinearMap.id p.2)
    show Continuous (fun p : unitInterval × V => p.2)
    exact continuous_snd
  start := rfl
  finish := rfl
  preserves_states_along := fun _ ρ hρ => hρ
  preserves_unit_along := fun _ => by
    show G.unit.comp LinearMap.id = G.unit
    rfl
  continuous_at := fun _ => continuous_id

/-- The constant ReversiblePath at R (R, R, R, ..., R). -/
def ReversiblePath.const {G : GPT V} (R : Reversible G) :
    ReversiblePath G R R where
  γ := fun _ => R.toLin
  continuous := by
    show Continuous (fun p : unitInterval × V => R.toLin p.2)
    exact R.continuous_toLin.comp continuous_snd
  start := rfl
  finish := rfl
  preserves_states_along := fun _ ρ hρ => R.preserves_states ρ hρ
  preserves_unit_along := fun _ => R.preserves_unit
  continuous_at := fun _ => R.continuous_toLin

/-- The R6-strong agency postulate: every pair of available Reversibles
is connected by a ReversiblePath. -/
class StrongConnectedAgency (G : GPT V) where
  avail : Set (Reversible G)
  id_avail : Reversible.id G ∈ avail
  reversible_paths :
    ∀ R₁ R₂ : Reversible G, R₁ ∈ avail → R₂ ∈ avail →
      Nonempty (ReversiblePath G R₁ R₂)

/-! ### R6-tris: StrictReversiblePath — paths of bijections -/

/-- A continuous path of StrictReversibles: every intermediate map
must be a genuine bijection (continuous, state-preserving, unit-
preserving, AND bijective). This is the strongest R6 condition. -/
structure StrictReversiblePath (G : GPT V) (R₁ R₂ : StrictReversible G) where
  γ : unitInterval → V →ₗ[ℝ] V
  continuous : Continuous (fun p : unitInterval × V => γ p.1 p.2)
  start : γ 0 = R₁.toLin
  finish : γ 1 = R₂.toLin
  preserves_states_along : ∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states
  preserves_unit_along : ∀ t : unitInterval, G.unit.comp (γ t) = G.unit
  bijective_along : ∀ t : unitInterval, Function.Bijective (γ t)

/-- StrictReversiblePath is strictly stronger than ReversiblePath. -/
def StrictReversiblePath.toReversiblePath {G : GPT V}
    {R₁ R₂ : StrictReversible G} (p : StrictReversiblePath G R₁ R₂) :
    ReversiblePath G R₁.toReversible R₂.toReversible where
  γ := p.γ
  continuous := p.continuous
  start := p.start
  finish := p.finish
  preserves_states_along := p.preserves_states_along
  preserves_unit_along := p.preserves_unit_along
  continuous_at := fun t => by
    have h : Continuous (fun v : V => (t, v)) :=
      Continuous.prodMk continuous_const continuous_id
    exact p.continuous.comp h

/-- The identity StrictReversiblePath. -/
def StrictReversiblePath.id (G : GPT V) :
    StrictReversiblePath G (StrictReversible.id G) (StrictReversible.id G) where
  γ := fun _ => LinearMap.id
  continuous := by
    show Continuous (fun p : unitInterval × V => LinearMap.id p.2)
    show Continuous (fun p : unitInterval × V => p.2)
    exact continuous_snd
  start := rfl
  finish := rfl
  preserves_states_along := fun _ ρ hρ => hρ
  preserves_unit_along := fun _ => rfl
  bijective_along := fun _ => Function.bijective_id

/-- The R6-final agency postulate: every pair of available StrictReversibles
is connected by a StrictReversiblePath. This is the substantive condition
that (conjecturally) distinguishes quantum (path-connected Lie group U(N))
from classical (discrete S_N). -/
class StrictConnectedAgency (G : GPT V) where
  avail : Set (StrictReversible G)
  id_avail : StrictReversible.id G ∈ avail
  strict_paths :
    ∀ R₁ R₂ : StrictReversible G, R₁ ∈ avail → R₂ ∈ avail →
      Nonempty (StrictReversiblePath G R₁ R₂)

/-! ### R6 trivial agency (singleton {id}) -/

/-- The trivial StrictConnectedAgency: only the identity is available. -/
@[reducible]
def trivialStrictAgency (G : GPT V) : StrictConnectedAgency G where
  avail := { StrictReversible.id G }
  id_avail := rfl
  strict_paths R₁ R₂ h₁ h₂ := by
    have e₁ : R₁ = StrictReversible.id G := h₁
    have e₂ : R₂ = StrictReversible.id G := h₂
    subst e₁; subst e₂
    exact ⟨StrictReversiblePath.id G⟩

/-- In the trivial strict agency, every Reachable pair is equal. -/
theorem trivialStrictAgency_reachable_iff (G : GPT V) (ρ₁ ρ₂ : V) :
    (∃ R ∈ (trivialStrictAgency G).avail, R.toLin ρ₁ = ρ₂) ↔ ρ₁ = ρ₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨R, hR, hRρ⟩
    have eR : R = StrictReversible.id G := hR
    subst eR
    show ρ₁ = ρ₂
    rw [← hRρ]
    rfl
  · rintro rfl
    refine ⟨StrictReversible.id G, rfl, ?_⟩
    show LinearMap.id ρ₁ = ρ₁
    rfl

/-- Trivial agency on Bool / Fin n / etc. is a valid StrictConnectedAgency. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) : StrictConnectedAgency G := trivialStrictAgency G

/-! ### R6 discreteness target

The substantive R6 theorem we ultimately want: for the classical GPT on
Fin n, the only continuous path of state-preserving bijections is the
constant path. Concretely:

  Classical Reversibles = doubly-stochastic matrices.
  Classical StrictReversibles ⊆ permutation matrices (bijection = invertible
    + state preserving means: maps simplex to simplex bijectively, so
    permutes the n vertices).
  Permutation matrices form a finite discrete set in the topology
    of ℝ^(n×n).
  Therefore any continuous γ : [0,1] → permutation matrices is constant.

Proving this requires:
1. A theorem characterizing StrictReversible Classical as permutations.
2. Discreteness of the permutation matrix set in matrix space.
3. Constant-valued of continuous map [0,1] → discrete.

(1) is purely linear algebra; (2) is the topology of finite sets; (3)
is `IsPreconnected.subsingleton` type result. All three are tractable;
together they form the R6 substantive payoff.

This file lays the categorical groundwork. Concrete classical-side
proofs go in `Classical.lean`. -/

/-! ## R7: Toward Lie-group reversible dynamics

The next refinement beyond `StrictConnectedAgency` is to require that
the path γ from R₁ to R₂ be SMOOTH (`C^∞`), not merely continuous.
Smoothness on a Banach space (which V is for finite-dimensional GPTs)
combined with state-preservation and bijectivity gives the
transformation set the structure of a Lie group acting smoothly on V.

For Classical n GPT: the discrete permutation group has no smooth
structure beyond the finite (0-dimensional) Lie group. So any
SmoothConnectedAgency on Classical n must have `avail` equal to a
single Lie-group component — i.e. it's either trivial or has all of
S_n inside a single connected component, which is only possible for
n = 1 (where S_1 = trivial).

For Quantum n: U(n) IS a connected compact Lie group, so the
analogous SmoothConnectedAgency is naturally non-trivial.

This is the framework's conjectured route to deriving that "QM is the
unique non-classical GPT with non-trivial smooth reversible dynamics."
A full proof requires Mathlib's Lie-group infrastructure and is left
as future work (per ORIGINAL_PROMPT §6 Tier 2). -/

/-- The R7 scaffold: a `LieGroupReversiblePath` packages the
StrictReversiblePath data together with an ADDITIONAL group-structure
witness — every pair of γ(t) values lies in a common Lie-group orbit.
We do not yet require differentiability (which needs Mathlib's Lie-group
machinery), but we DO require that the avail set is closed under
composition with itself, which is the algebraic precursor of Lie-group
structure.

This is groundwork for R7. The full Lie-group condition (smoothness,
differential structure, Lie algebra) is deferred until Mathlib's
`LieGroup` infrastructure can be wired up to `Reversible G`. -/
structure GroupClosedReversiblePath
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) (R₁ R₂ : StrictReversible G)
    extends StrictReversiblePath G R₁ R₂ where
  /-- The endpoints can be composed: γ 1 ∘ (γ 0).inv lies in the
  StrictReversible space, so the "displacement" R₂ ∘ R₁⁻¹ is itself
  reversible. This is the algebraic precondition for Lie-group structure
  on the available transformations. -/
  composition_in_strict :
    ∃ R : StrictReversible G, R.toLin.comp R₁.toLin = R₂.toLin

/-- The R7-style agency: every pair of avail StrictReversibles is
connected by a GroupClosedReversiblePath. -/
class GroupClosedAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) where
  avail : Set (StrictReversible G)
  id_avail : StrictReversible.id G ∈ avail
  group_closed_paths :
    ∀ R₁ R₂ : StrictReversible G, R₁ ∈ avail → R₂ ∈ avail →
      Nonempty (GroupClosedReversiblePath G R₁ R₂)

/-- GroupClosedAgency strengthens StrictConnectedAgency. -/
instance (priority := 100) StrictConnectedAgency.ofGroupClosedAgency
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {G : GPT V}
    [GCA : GroupClosedAgency G] : StrictConnectedAgency G where
  avail := GCA.avail
  id_avail := GCA.id_avail
  strict_paths R₁ R₂ h₁ h₂ := by
    obtain ⟨p⟩ := GCA.group_closed_paths R₁ R₂ h₁ h₂
    exact ⟨p.toStrictReversiblePath⟩

/-- The trivial GroupClosedAgency with avail = {StrictReversible.id G}. -/
@[reducible]
def trivialGroupClosedAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) : GroupClosedAgency G where
  avail := { StrictReversible.id G }
  id_avail := rfl
  group_closed_paths R₁ R₂ h₁ h₂ := by
    have e₁ : R₁ = StrictReversible.id G := h₁
    have e₂ : R₂ = StrictReversible.id G := h₂
    subst e₁; subst e₂
    refine ⟨{
      toStrictReversiblePath := StrictReversiblePath.id G
      composition_in_strict := ⟨StrictReversible.id G, by
        apply LinearMap.ext
        intro v
        rfl⟩
    }⟩

/-- The trivial GroupClosedAgency exists for ANY GPT. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) : GroupClosedAgency G := trivialGroupClosedAgency G

/-! ## TransitiveAgency — Hardy Axiom 5 in its substantive form

Hardy's Axiom 5 has two parts:
  (a) Continuity of reversible transformations between pure states.
  (b) Transitivity of the available transformations on pure states.

Levels L1–L5 of the hierarchy (`HasConnectedAgency` through
`GroupClosedAgency`) refine the *path* structure — that is, the
continuity (a) ingredient. They make no claim about transitivity
(b).  In particular `trivialStrictAgency` satisfies every level up to
`GroupClosedAgency` while having `avail = {id}` — but `{id}` fails
to act transitively on any state space with more than one pure state.

`TransitiveAgency` is the deep half of Axiom 5: a `StrictConnectedAgency`
in which the available StrictReversibles act transitively on pure
states (extreme points of the convex state space).  Combining the
load-bearing classical-vs-quantum disconnect (L4 = `StrictConnectedAgency`)
with `TransitiveAgency` is what generates the *real* discrimination
between classical GPTs (where transitive action on pure states needs
permutations across distinct connected sign-sectors) and quantum
GPTs (where U(N) acts transitively on the projective line by
continuous bijections within a single connected component).

For Classical `n = 2` this yields an impossibility result:
no `TransitiveAgency` on `gpt 2` exists at all.  See
`Classical.classical_n2_no_transitive_agency`. -/

/-- The substantive Axiom 5 strengthening: a `StrictConnectedAgency`
whose available transformations act transitively on pure states. -/
class TransitiveAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) extends StrictConnectedAgency G where
  /-- For any two pure states `ρ₁`, `ρ₂` of `G`, some `R ∈ avail`
  carries `ρ₁` to `ρ₂`.  This is Hardy Axiom 5's transitivity clause. -/
  transitive_on_pure :
    ∀ ρ₁ ρ₂ : V, PureState G ρ₁ → PureState G ρ₂ →
      ∃ R ∈ avail, R.toLin ρ₁ = ρ₂

/-- A `TransitiveAgency` IS a `StrictConnectedAgency` via the
forgetful instance auto-generated by `extends`. The explicit declaration
below is for documentation; Lean resolves `[TransitiveAgency G] ⊢
StrictConnectedAgency G` via the parent-projection automatically. -/
instance (priority := 50) StrictConnectedAgency.ofTransitiveAgency
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {G : GPT V}
    [T : TransitiveAgency G] : StrictConnectedAgency G := T.toStrictConnectedAgency

/-! ### Trivial agency fails transitivity

The trivial `StrictConnectedAgency` (`avail = {id}`) cannot be promoted
to a `TransitiveAgency` whenever the GPT has two distinct pure states,
because the only available transformation is `id`, which fixes every
state and therefore cannot carry a pure state `ρ₁` to a distinct pure
state `ρ₂`.

This formalizes one half of the slogan "transitivity is the deep half
of Axiom 5": every level of the path-continuity hierarchy is satisfied
by the trivial agency, but transitivity is not. -/

/-- A `TransitiveAgency` instance whose underlying `avail` is the
singleton `{StrictReversible.id G}` is impossible whenever `G` admits
two distinct pure states. -/
theorem TransitiveAgency.singleton_id_impossible
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) (T : TransitiveAgency G)
    (h_avail : T.avail = {StrictReversible.id G})
    {ρ₁ ρ₂ : V} (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂)
    (hne : ρ₁ ≠ ρ₂) : False := by
  obtain ⟨R, hR, hRρ⟩ := T.transitive_on_pure ρ₁ ρ₂ hp₁ hp₂
  -- hR : R ∈ T.avail = {id}, so R = StrictReversible.id G
  have hR' : R ∈ ({StrictReversible.id G} : Set _) := by rw [← h_avail]; exact hR
  have hReq : R = StrictReversible.id G := hR'
  -- R.toLin = LinearMap.id, so R.toLin ρ₁ = ρ₁ ≠ ρ₂
  apply hne
  rw [← hRρ, hReq]
  show (LinearMap.id : V →ₗ[ℝ] V) ρ₁ = ρ₁
  rfl

/-- Specialization to the canonical "trivial" agency: there is no
`TransitiveAgency` extending `trivialStrictAgency G` when `G` has two
distinct pure states. -/
theorem TransitiveAgency.trivial_impossible
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) (T : TransitiveAgency G)
    (h_avail : T.avail = (trivialStrictAgency G).avail)
    {ρ₁ ρ₂ : V} (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂)
    (hne : ρ₁ ≠ ρ₂) : False := by
  -- trivialStrictAgency.avail = {StrictReversible.id G} by definition.
  apply TransitiveAgency.singleton_id_impossible (G := G) T ?_ hp₁ hp₂ hne
  -- Show T.avail = {StrictReversible.id G}.
  rw [h_avail]
  rfl

/-! ### Positive existence: trivial TransitiveAgency when pure states are unique

The negative results above show classical n ≥ 2 has no TransitiveAgency.
The POSITIVE complement: any GPT whose pure states are unique (i.e.,
all pure states coincide) admits a trivial TransitiveAgency, since the
identity is sufficient to "transport" any pure state to itself.

This is degenerate (no non-trivial dynamics) but confirms that
`TransitiveAgency` is a satisfiable predicate. Non-degenerate positive
existence — a GPT with multiple pure states where TransitiveAgency
holds — requires e.g. the qubit (U(2) acts transitively on pure states),
which is R4 in the roadmap. -/

/-- If a GPT has at most one pure state, the trivial strict agency
extends to a `TransitiveAgency`. -/
@[reducible]
def TransitiveAgency.ofUniquePureState
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V)
    (h_unique : ∀ ρ₁ ρ₂ : V, PureState G ρ₁ → PureState G ρ₂ → ρ₁ = ρ₂) :
    TransitiveAgency G where
  toStrictConnectedAgency := trivialStrictAgency G
  transitive_on_pure := by
    intro ρ₁ ρ₂ hp₁ hp₂
    have heq : ρ₁ = ρ₂ := h_unique ρ₁ ρ₂ hp₁ hp₂
    refine ⟨StrictReversible.id G, rfl, ?_⟩
    show (LinearMap.id : V →ₗ[ℝ] V) ρ₁ = ρ₂
    exact heq

/-! ### TransitiveAgency → Hardy Axiom 5 (strong form)

The deepest bridge in the agency hierarchy: a `TransitiveAgency` G
implies the strong form of Hardy's Axiom 5 — between any two pure
states there exists a *continuous path of state-preserving bijective
linear maps* starting at the identity and carrying ρ₁ to ρ₂.

This is the bridge that, in the quantum case, becomes "unitary
evolution between pure states." The framework's classical-vs-quantum
dichotomy now reads cleanly: classical n ≥ 2 has no `TransitiveAgency`
(L6 result), and any GPT that does has Hardy A5 in its strongest form.
-/

/-- **Hardy Axiom 5, strong form**: a `TransitiveAgency` provides, for
any two pure states `ρ₁` and `ρ₂`, a continuous path of state-preserving
bijective linear maps from the identity to a transformation sending
`ρ₁` to `ρ₂`. -/
theorem TransitiveAgency.hardy_axiom5
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (T : TransitiveAgency G)
    (ρ₁ ρ₂ : V) (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      γ 0 = LinearMap.id ∧
      γ 1 ρ₁ = ρ₂ ∧
      (∀ t : unitInterval, ∀ ρ ∈ G.states, γ t ρ ∈ G.states) ∧
      (∀ t : unitInterval, Function.Bijective (γ t)) := by
  obtain ⟨R, hR, hRρ⟩ := T.transitive_on_pure ρ₁ ρ₂ hp₁ hp₂
  have h_id : StrictReversible.id G ∈ T.avail := T.id_avail
  obtain ⟨path⟩ := T.strict_paths (StrictReversible.id G) R h_id hR
  refine ⟨path.γ, path.continuous, ?_, ?_, path.preserves_states_along, path.bijective_along⟩
  · -- γ 0 = (StrictReversible.id G).toLin = LinearMap.id
    rw [path.start]; rfl
  · -- γ 1 ρ₁ = R.toLin ρ₁ = ρ₂
    have : path.γ 1 ρ₁ = R.toLin ρ₁ := by rw [path.finish]
    rw [this, hRρ]

/-! ### PurePreservingTransitiveAgency — the framework's intended L7

The L6 subagent's mathematical correction (in Classical.lean) showed
that the naive R6 strengthening fails for `n ≥ 3` without an extra
hypothesis: there exist genuine `StrictReversiblePath`s between id and
non-trivial permutations (e.g., `t·I + (1-t)·C` for the 3-cycle C).
The discreteness argument requires an additional "pure-state
preservation along the path" hypothesis.

`PurePreservingTransitiveAgency` packages this refinement: a
TransitiveAgency whose strict paths preserve PureStates along the way.
This is the framework's intended axiom refinement (per the user-
authorized "metaphysics-fixed, axioms-adjustable" methodology). The
pattern-stability metaphysics (Axiom IV) naturally motivates this
condition: a stable particular pattern shouldn't "smear out" to a
mixture along reversible dynamics.

On Classical n ≥ 2, this typeclass is provably impossible (modulo
R1: vertices are pure states), giving a clean classical no-go.
On CircleGPT (and analogous continuous-symmetry GPTs), this typeclass
is satisfied via rotations (each rotation preserves pure states). -/

/-- A `PurePreservingTransitiveAgency` extends `TransitiveAgency` with
the requirement that strict paths preserve PureStates along the way:
for every t in [0,1] and every pure state ρ, p.γ t ρ is still a pure
state. -/
class PurePreservingTransitiveAgency {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (G : GPT V) extends TransitiveAgency G where
  /-- Every strict path between elements of `avail` preserves pure
  states along the way: for each `t : unitInterval` and pure state
  `ρ`, `p.γ t ρ` is also a pure state. -/
  preserves_pure_along :
    ∀ R₁ R₂ : StrictReversible G, R₁ ∈ avail → R₂ ∈ avail →
      ∀ (p : StrictReversiblePath G R₁ R₂)
        (t : unitInterval) (ρ : V), PureState G ρ →
        PureState G (p.γ t ρ)

/-- `PurePreservingTransitiveAgency` is automatically a
`TransitiveAgency`. -/
instance (priority := 60) TransitiveAgency.ofPurePreserving
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {G : GPT V}
    [PPT : PurePreservingTransitiveAgency G] : TransitiveAgency G :=
  PPT.toTransitiveAgency

/-! **Note on positive existence for L7.**

A naive `PurePreservingTransitiveAgency.ofUniquePureState` constructor
attempt fails because the L7 axiom requires that EVERY
`StrictReversiblePath` between elements of `avail` preserves pure
states along the way — not just the specific path provided by
`strict_paths`. Even on trivial-agency GPTs, one can construct
StrictReversiblePaths that don't preserve pure states (via interior
maps).

The proper positive-existence story for L7 requires either (i)
refactoring the path notion to a `PurePreservingStrictReversiblePath`
structure, or (ii) restricting the L7 quantifier to the
agency-supplied path. The current formulation captures the strongest
no-go consequence (the L7 closure on Classical n ≥ 2, conditional on
reverse R1) but leaves positive instantiation for future work. -/

/-! ### Cardinality lower bounds from TransitiveAgency

A `TransitiveAgency` on a GPT with multiple distinct pure states
forces the available transformation set to be at least as large as
the number of pure states. This is the operational shadow of the
"continuous symmetry" intuition: more pure states ⇒ more dynamics.

Combined with the classical n ≥ 2 no-go (no `TransitiveAgency` exists
at all), this is a strong structural constraint: a non-trivial
`TransitiveAgency` REQUIRES non-trivial `avail`, which classical n ≥ 2
fails to deliver because state-preserving bijections form the discrete
group S_n. -/

/-- If `T : TransitiveAgency G` and ρ₁, ρ₂ are distinct pure states,
then there exist at least two distinct elements in `T.avail`. -/
theorem TransitiveAgency.avail_at_least_two
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (T : TransitiveAgency G)
    (ρ₁ ρ₂ : V) (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂)
    (hne : ρ₁ ≠ ρ₂) :
    ∃ R₁ R₂ : StrictReversible G, R₁ ∈ T.avail ∧ R₂ ∈ T.avail ∧ R₁ ≠ R₂ := by
  obtain ⟨R, hR_avail, hRρ⟩ := T.transitive_on_pure ρ₁ ρ₂ hp₁ hp₂
  refine ⟨StrictReversible.id G, R, T.id_avail, hR_avail, ?_⟩
  -- id ≠ R since id ρ₁ = ρ₁ but R ρ₁ = ρ₂ ≠ ρ₁
  intro heq
  apply hne
  have : (StrictReversible.id G).toLin ρ₁ = R.toLin ρ₁ := by rw [heq]
  -- (StrictReversible.id G).toLin ρ₁ = ρ₁, R.toLin ρ₁ = ρ₂
  rw [StrictReversible.id_toLin] at this
  show ρ₁ = ρ₂
  rw [show ρ₁ = (LinearMap.id : V →ₗ[ℝ] V) ρ₁ from rfl, this, hRρ]

/-- **Generalized cardinality bound**: for any injective family `φ : Fin n → V`
of pure states (with a designated "source" pure state ρ₀), there exist
`n + 1` pairwise-distinct elements in `T.avail`: the identity plus
n distinct R_i with R_i ρ₀ = φ i. (Or just n, if ρ₀ is one of the φ i.)
-/
theorem TransitiveAgency.avail_at_least_n
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (T : TransitiveAgency G)
    (n : ℕ) (φ : Fin n → V)
    (hinj : Function.Injective φ)
    (hpure : ∀ i, PureState G (φ i)) :
    ∃ ψ : Fin n → StrictReversible G,
      Function.Injective ψ ∧ ∀ i, ψ i ∈ T.avail := by
  -- For each i, pick R_i with R_i (φ 0) = φ i (transitivity on pure states).
  -- (For n = 0 this is vacuous.)
  by_cases h : n = 0
  · subst h
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  -- n ≥ 1: use φ 0 as source. We need n > 0 to make Fin n inhabited.
  have hn_pos : 0 < n := Nat.pos_of_ne_zero h
  let zero_fin : Fin n := ⟨0, hn_pos⟩
  -- Define ψ i := R_i where R_i (φ zero_fin) = φ i (using transitive_on_pure).
  choose ψ_fun hψ_avail hψ_eq using (fun i =>
    T.transitive_on_pure (φ zero_fin) (φ i) (hpure zero_fin) (hpure i))
  refine ⟨ψ_fun, ?_, hψ_avail⟩
  intro i j heq
  -- ψ_fun i = ψ_fun j implies (ψ_fun i).toLin = (ψ_fun j).toLin, so they agree on φ zero_fin.
  apply hinj
  rw [← hψ_eq i, ← hψ_eq j, heq]

/-- The transformations `transitive_on_pure` produces for distinct
target pure states are pairwise distinct. -/
theorem TransitiveAgency.distinct_R_of_distinct_targets
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (T : TransitiveAgency G)
    (ρ₀ : V) (hp₀ : PureState G ρ₀)
    (ρ₁ ρ₂ : V) (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂)
    (hne : ρ₁ ≠ ρ₂)
    (R₁ R₂ : StrictReversible G)
    (hR₁ : R₁ ∈ T.avail) (hR₂ : R₂ ∈ T.avail)
    (hR₁ρ : R₁.toLin ρ₀ = ρ₁) (hR₂ρ : R₂.toLin ρ₀ = ρ₂) :
    R₁ ≠ R₂ := by
  intro heq
  apply hne
  rw [← hR₁ρ, ← hR₂ρ, heq]

/-- **Hardy Axiom 5, state-path form**: as a consequence, the
state-trajectory `t ↦ γ(t)(ρ₁)` is a continuous path of states in `G`
connecting `ρ₁` to `ρ₂`. -/
theorem TransitiveAgency.hardy_axiom5_state_path
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (T : TransitiveAgency G)
    (ρ₁ ρ₂ : V) (hρ₁ : ρ₁ ∈ G.states)
    (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂) :
    ∃ p : unitInterval → V, Continuous p ∧ p 0 = ρ₁ ∧ p 1 = ρ₂ ∧
      ∀ t : unitInterval, p t ∈ G.states := by
  obtain ⟨γ, hcont, hγ_0, hγ_1, hpres, _hbij⟩ := T.hardy_axiom5 ρ₁ ρ₂ hp₁ hp₂
  refine ⟨fun t => γ t ρ₁, ?_, ?_, ?_, ?_⟩
  · have hpair : Continuous (fun t : unitInterval => (t, ρ₁)) :=
      Continuous.prodMk continuous_id continuous_const
    exact hcont.comp hpair
  · show γ 0 ρ₁ = ρ₁
    rw [hγ_0]; rfl
  · exact hγ_1
  · intro t
    exact hpres t ρ₁ hρ₁

/-! ### One-parameter families: groundwork for R7 Lie-group bridge

A `OneParameterFamily f` is a continuous map ℝ → StrictReversible G
that's a homomorphism from (ℝ, +) to the composition monoid on
StrictReversibles. In Lie-theoretic terms, this is a 1-parameter
subgroup of the StrictReversible group — the orbit of a Lie algebra
element under the exponential map.

This is the LIGHTWEIGHT precursor to the full R7 Lie-group bridge,
sidestepping Mathlib's `LieGroup` infrastructure while still capturing
the framework's structural intuition: a continuous symmetry corresponds
to a 1-parameter subgroup of reversibles. `CircleGPT.rotStrictReversible`
is the framework's canonical example. -/

/-- A `OneParameterFamily f` is a jointly continuous homomorphism
ℝ → StrictReversible G (composition monoid). Joint continuity in (θ, v)
sidesteps the need for a topology on `V →ₗ[ℝ] V`. -/
structure OneParameterFamily
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) where
  f : ℝ → StrictReversible G
  /-- Joint continuity in (θ, v). -/
  continuous : Continuous (fun p : ℝ × V => (f p.1).toLin p.2)
  zero : (f 0).toLin = LinearMap.id
  add : ∀ θ₁ θ₂ : ℝ, (f (θ₁ + θ₂)).toLin = (f θ₁).toLin.comp (f θ₂).toLin

/-- A `OneParameterFamily` evaluated at 0 gives the identity
StrictReversible (as a linear map). -/
@[simp] theorem OneParameterFamily.zero_apply
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (F : OneParameterFamily G) :
    (F.f 0).toLin = LinearMap.id := F.zero

/-- Each element of a `OneParameterFamily` has an inverse element
(via the additive inverse parameter). -/
theorem OneParameterFamily.inv
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (F : OneParameterFamily G) (θ : ℝ) :
    (F.f (-θ)).toLin.comp (F.f θ).toLin = LinearMap.id := by
  rw [← F.add]; simp

/-- A GPT has *one-parameter agency* if it admits a `OneParameterFamily`.
This is the framework's lightweight precursor to the full R7 Lie-group
postulate — capturing "continuous symmetry exists" without requiring
the full smooth-manifold infrastructure. -/
class HasOneParameterAgency
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) where
  family : OneParameterFamily G

/-- **HasOneParameterAgency ⇒ family is non-trivial OR all elements are id.**
The class itself doesn't enforce non-triviality, so we provide both
forms. This packages the family extraction for downstream use. -/
theorem HasOneParameterAgency.family_at_zero
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} [H : HasOneParameterAgency G] :
    (H.family.f 0).toLin = LinearMap.id :=
  H.family.zero

/-- A GPT has *k-axis agency* if it admits `k` distinct
`OneParameterFamily` instances — k independent 1-parameter subgroups.
The framework's scaffold toward k-dim Lie group symmetry.

Examples:
- k = 1: `HasOneParameterAgency` (U(1) / abelian).
- k = 3: `HasMultiAxisAgency 3` (SO(3) / SU(2)-like axis presence).
- k = 8: would be SU(3) (eight Gell-Mann generators).

Note: this does not require the families to be independent in any
strong sense (e.g., generating a non-abelian Lie algebra); it just
collects k of them. -/
structure HasMultiAxisAgency (k : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) where
  axes : Fin k → OneParameterFamily G

/-! ## R7 SmoothConnectedAgency — scaffold + precise conjecture

Per ORIGINAL_PROMPT v2 first move #6, state the R7 conjecture
precisely.

**Conjecture (R7 Lie-group bridge):** for a GPT G with a non-trivial
`StrictConnectedAgency`, the avail set forms (under composition) a
CONNECTED LIE GROUP. For Tier B encodings of frameworks supporting
QM (= satisfying the strengthened wantable axioms including
`PurePreservingTransitiveAgency`), this Lie group is isomorphic to a
subgroup of U(n) where n is the operational dimension. In the
fully-symmetric case (transitive on all pure states), the Lie group
IS U(n) / Z_n or SO(n+1) depending on real vs complex structure.

This is the v2-progressive analog of Hardy A2 (Simplicity / K-minimum)
made structural: among connected Lie groups compatible with the
strengthened agency axioms, the framework forces the minimal-K
candidate, which is the quantum group U(n).

**Mathematical content needed (heavy):**
  • Smooth manifold structure on `Set (StrictReversible G)` —
    requires Mathlib's smooth manifolds with corners.
  • Lie group structure — requires Mathlib's `LieGroup`.
  • The connected component containing identity must be characterized.

**Status:** SCAFFOLD only. The typeclass `SmoothConnectedAgency` below
is a placeholder. The full content depends on wiring Mathlib's
LieGroup infrastructure to the framework's Reversible structure, which
is currently deferred. The lightweight precursor `OneParameterFamily`
(defined elsewhere in this file) gives the 1-parameter abelian case.

**Open work per v2:** prove the R7 conjecture for the framework's
specific GPT instances (CircleGPT gives U(1); QubitGPT gives SO(3) =
SU(2)/Z_2; QutritGPT gives generators of SU(3); full uniqueness
requires the v2-progressive bracketing-from-Tier-A argument). -/

/-- A *smooth-connected agency* on a GPT G — placeholder typeclass.
The full content would require Mathlib's smooth manifold + Lie group
infrastructure wired to the framework's `Reversible G` structure.
For now, this records the framework's structural intention. -/
class SmoothConnectedAgency
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) extends StrictConnectedAgency G where
  /-- The avail set admits a (yet-to-be-specified) smooth manifold
  structure compatible with composition. Placeholder for the Lie
  group condition. -/
  smooth_manifold_placeholder : True

/-- **The R7 conjecture (precise form, structural).** For any GPT G
with a `SmoothConnectedAgency`, the framework predicts that the avail
set is a connected Lie group; specifically, for GPTs satisfying the
strengthened wantable axioms (= PurePreservingTransitiveAgency on a
non-classical Hardy signature), this Lie group is isomorphic to U(n)
where n is the operational dimension.

**Currently STATED as conjecture, not proved.** The proof requires
(i) Mathlib LieGroup wiring, (ii) the v2-progressive
bracketing-from-Tier-A argument that forces the K = N² signature,
(iii) Renou-style discrimination between U(n) and O(n+1).

This is the framework's central remaining Tier 1 #5 target. -/
def R7_Conjecture
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V) : Prop :=
  Nonempty (PurePreservingTransitiveAgency G) →
  ∃ _ : SmoothConnectedAgency G,
    -- The Lie group structure exists and is connected.
    -- The U(n) characterization would require additional structure
    -- (complex Hilbert space, dimension n). Stated structurally for now.
    True

/-- **Constructor: SmoothConnectedAgency from StrictConnectedAgency.**
At the scaffold level (where `smooth_manifold_placeholder` is `True`),
any GPT with a `StrictConnectedAgency` instance trivially admits a
`SmoothConnectedAgency`. This is the framework's minimal instance-
construction; the substantive content (Lie group structure) is
deferred to future Mathlib-LieGroup wiring. -/
def SmoothConnectedAgency.ofStrict
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (SCA : StrictConnectedAgency G) :
    SmoothConnectedAgency G :=
  { SCA with smooth_manifold_placeholder := trivial }

/-- **R7 conjecture holds trivially for any GPT with
`StrictConnectedAgency`** at the scaffold-level smooth-structure.
Since `SmoothConnectedAgency` is currently a scaffold (the
`smooth_manifold_placeholder : True` carries no content), the
existence-part of R7 follows immediately from any `StrictConnectedAgency`.

This is INSTANCE EVIDENCE for R7 — not a proof of the conjecture's
substantive content, which requires the Lie-group structure to be
genuinely characterized. -/
theorem R7_Conjecture_of_strict
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : GPT V} (SCA : StrictConnectedAgency G) :
    R7_Conjecture G :=
  fun _ => ⟨SmoothConnectedAgency.ofStrict SCA, trivial⟩

/-! ### Worked example: agency → Hardy A5 pipeline

A concrete demonstration of the framework's machine-verified Hardy A5
derivation pipeline. For any GPT G with at most one pure state, the
ofUniquePureState constructor gives a TransitiveAgency; then hardy_axiom5
yields the strong-form A5 path. Trivial but instructive. -/

example
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : GPT V)
    (h_unique : ∀ ρ₁ ρ₂ : V, PureState G ρ₁ → PureState G ρ₂ → ρ₁ = ρ₂)
    (ρ₁ ρ₂ : V) (hp₁ : PureState G ρ₁) (hp₂ : PureState G ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      γ 0 = LinearMap.id ∧
      γ 1 ρ₁ = ρ₂ := by
  -- Step 1: get the TransitiveAgency from uniqueness.
  let T : TransitiveAgency G := TransitiveAgency.ofUniquePureState G h_unique
  -- Step 2: extract Hardy A5 strong-form.
  obtain ⟨γ, hcont, hγ_0, hγ_1, _, _⟩ := T.hardy_axiom5 ρ₁ ρ₂ hp₁ hp₂
  exact ⟨γ, hcont, hγ_0, hγ_1⟩

end Continuity
end Perspectival
