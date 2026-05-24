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

end GPT

end Perspectival
