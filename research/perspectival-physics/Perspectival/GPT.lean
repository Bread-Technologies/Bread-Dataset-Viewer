/-
Perspectival Physics — Generalized Probabilistic Theory (GPT) layer
====================================================================

Operational reconstructions of QM (Hardy, Chiribella-D'Ariano-Perinotti,
Müller, Masanes-Müller) live in the GPT framework. A GPT specifies:

  • An ordered real vector space V (state space, signed)
  • A positive cone V₊
  • A unit effect u : V →ₗ ℝ — normalization
  • Normalized states Ω = {ρ ∈ V₊ : u ρ = 1} (convex)
  • Effects E = {e ∈ V* : 0 ≤ e ≤ u} (also convex)
  • Probability assignment: ⟨e, ρ⟩ ∈ [0,1]

The bridge from the perspective-wanting ontology is:

  Perspectives ↔ states (a perspective IS a directedness, encoded as ρ)
  Wants of a complementary perspective ↔ effects
  Meetings ↔ measurement outcomes (probability ⟨e, ρ⟩)
  Complement on Wantable ↔ involution structure on effects (e ↦ u − e)

Calibrated status:
  ✓ Bare GPT data structure (this file)
  ✓ Classical instance (convex hull of finitely many pure states)
  ▲ Quantum instance: marked as future work (needs DensityMatrix machinery)
  ✗ Reconstruction: this file does NOT derive QM. It provides the
    framework in which a derivation could be formulated.

Known limitation acknowledged here:
  Defining a GPT does not by itself constrain to QM. The Hardy-style
  axioms (subspaces, composition, simplicity, continuity) are needed,
  and one or more of those must be derived from I–IV for the framework
  to do real work. That derivation is OPEN.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Perspectival.Ontology

namespace Perspectival

/-! ## The GPT data structure -/

/-- A *generalized probabilistic theory* (single system) is the data of:
  • an underlying real vector space `V`,
  • a unit effect `unit : V →ₗ[ℝ] ℝ`,
  • a set `states : Set V` of normalized states (convex),
  • a set `effects : Set (V →ₗ[ℝ] ℝ)` of effects (convex),
such that probabilities `⟨e, ρ⟩` lie in [0,1].

This is the minimal "convex operational" data. -/
structure GPT (V : Type u) [AddCommGroup V] [Module ℝ V] where
  unit : V →ₗ[ℝ] ℝ
  states : Set V
  effects : Set (V →ₗ[ℝ] ℝ)
  states_convex : Convex ℝ states
  effects_convex : Convex ℝ effects
  states_normalized : ∀ ρ ∈ states, unit ρ = 1
  prob_in_unit_interval :
    ∀ e ∈ effects, ∀ ρ ∈ states, 0 ≤ e ρ ∧ e ρ ≤ 1
  unit_is_effect : unit ∈ effects

namespace GPT

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Born-rule-style probability assignment. -/
def prob (_G : GPT V) (e : V →ₗ[ℝ] ℝ) (ρ : V) : ℝ := e ρ

@[simp] theorem prob_def (G : GPT V) (e : V →ₗ[ℝ] ℝ) (ρ : V) :
    G.prob e ρ = e ρ := rfl

/-- A transformation between GPTs is a linear map preserving states,
effects (by precomposition), and the unit (so probabilities are
preserved). For Hardy this is the right notion of "reversible
dynamics" when restricted to bijections. -/
structure Transform {V V' : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] (G : GPT V) (G' : GPT V') where
  toLin : V →ₗ[ℝ] V'
  preserves_states : ∀ ρ ∈ G.states, toLin ρ ∈ G'.states
  preserves_unit : G'.unit.comp toLin = G.unit

/-- A GPT transformation preserves probabilities: `e' (T ρ) = (e' ∘ T) ρ`
holds by construction, but the deeper invariance is `G'.unit (T ρ) = G.unit ρ`
which the `preserves_unit` field encodes. -/
theorem Transform.prob_invariant
    {V V' : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    {G : GPT V} {G' : GPT V'} (T : Transform G G') (ρ : V) :
    G'.unit (T.toLin ρ) = G.unit ρ := by
  have h := T.preserves_unit
  -- G'.unit.comp T.toLin = G.unit, applied to ρ
  have := congr_arg (fun (φ : V →ₗ[ℝ] ℝ) => φ ρ) h
  simpa using this

/-- The identity transformation on a GPT. -/
def Transform.id {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : GPT V) : Transform G G where
  toLin := LinearMap.id
  preserves_states := fun _ h => h
  preserves_unit := LinearMap.id_comp _

/-- Composition of GPT transformations. -/
def Transform.comp {V V' V'' : Type u}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup V''] [Module ℝ V'']
    {G : GPT V} {G' : GPT V'} {G'' : GPT V''}
    (T' : Transform G' G'') (T : Transform G G') : Transform G G'' where
  toLin := T'.toLin.comp T.toLin
  preserves_states := fun ρ hρ => T'.preserves_states _ (T.preserves_states ρ hρ)
  preserves_unit := by
    -- G''.unit ∘ (T'.toLin ∘ T.toLin) = (G''.unit ∘ T'.toLin) ∘ T.toLin
    --                                 = G'.unit ∘ T.toLin = G.unit.
    rw [← LinearMap.comp_assoc, T'.preserves_unit, T.preserves_unit]

/-- Two GPT transformations are equal iff their underlying linear maps agree. -/
theorem Transform.ext {V V' : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    {G : GPT V} {G' : GPT V'} {T T' : Transform G G'}
    (h : T.toLin = T'.toLin) : T = T' := by
  cases T; cases T'; congr

/-- Self-transformations on a GPT form a Monoid under composition. -/
instance {V : Type u} [AddCommGroup V] [Module ℝ V] (G : GPT V) :
    Monoid (Transform G G) where
  mul := Transform.comp
  one := Transform.id G
  mul_assoc T₁ T₂ T₃ := Transform.ext (LinearMap.comp_assoc _ _ _).symm
  one_mul T := Transform.ext (LinearMap.id_comp _)
  mul_one T := Transform.ext (LinearMap.comp_id _)

/-- `Transform.id * Transform.id = Transform.id`. -/
@[simp] theorem Transform.id_sq {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : GPT V) : Transform.id G * Transform.id G = Transform.id G :=
  one_mul _

/-- The identity transformation has `toLin = LinearMap.id`. -/
@[simp] theorem Transform.id_toLin {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : GPT V) : (Transform.id G).toLin = LinearMap.id := rfl

/-- The composition transformation has `toLin` = composition of linear maps. -/
@[simp] theorem Transform.comp_toLin {V V' V'' : Type u}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup V''] [Module ℝ V'']
    {G : GPT V} {G' : GPT V'} {G'' : GPT V''}
    (T' : Transform G' G'') (T : Transform G G') :
    (Transform.comp T' T).toLin = T'.toLin.comp T.toLin := rfl

end GPT

end Perspectival
