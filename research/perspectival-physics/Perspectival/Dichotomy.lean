/-
Perspectival Physics — The Classical-vs-Quantum Dichotomy
=========================================================

This file consolidates the formal dichotomy between classical and
continuous-symmetry GPTs at the level of the `TransitiveAgency`
typeclass — Hardy Axiom 5's transitivity clause.

The dichotomy:
- Classical n ≥ 2 (`Classical.gpt n`): no `TransitiveAgency` exists
  when the strict-paths are required to preserve vertices along the
  way (a refinement of the bare `StrictConnectedAgency` motivated by
  the framework's pattern-stability metaphysics).
- CircleGPT: an UNCONDITIONAL `TransitiveAgency` exists — the
  U(1)-rotation group acts transitively on the parametric pure-state
  circle.

This is the framework's first formal classical-vs-quantum
discrimination beyond cardinality arguments. The Hardy A5 axiom is
machine-derivable from the `TransitiveAgency` typeclass
(`Continuity.TransitiveAgency.hardy_axiom5`), so this dichotomy lifts
to Hardy A5: Classical n ≥ 2 fails strong-form A5; CircleGPT
satisfies it.
-/

import Perspectival.Classical
import Perspectival.CircleGPT
import Perspectival.Continuity
import Perspectival.Hardy

namespace Perspectival
namespace Dichotomy

/-! ## Negative side: Classical n ≥ 2 fails L6 under vertex-preservation -/

/-- **Classical no-go (L6 closure).** No `TransitiveAgency` exists on
the Classical n GPT (n ≥ 2) when the underlying strict paths preserve
vertices along the way. -/
theorem classical_n2_no_transitive_agency_under_vertex_preservation
    (T : Continuity.TransitiveAgency (Classical.gpt 2))
    (hvp_paths :
      ∀ R₁ R₂ : Continuity.StrictReversible (Classical.gpt 2),
        R₁ ∈ T.avail → R₂ ∈ T.avail →
        ∀ (p : Continuity.StrictReversiblePath (Classical.gpt 2) R₁ R₂)
          (t : unitInterval) (i : Fin 2),
          p.γ t (Classical.vertex 2 i) ∈ Classical.vertexSet 2) :
    False :=
  Classical.classical_general_vertex_preserving_no_transitive_agency_unconditional
    (n := 2) (by omega) T hvp_paths

/-! ## Positive side: CircleGPT supports an UNCONDITIONAL TransitiveAgency -/

/-- **CircleGPT positive existence.** The Circle GPT admits an
unconditional `TransitiveAgency` instance. -/
@[reducible]
noncomputable def circle_transitive_agency :
    Continuity.TransitiveAgency CircleGPT.circleGPT :=
  CircleGPT.circleTransitiveAgency_unconditional

/-! ## Combined dichotomy at the Hardy A5 level

The framework's claim now becomes formally verifiable: continuous-
symmetry GPTs (like CircleGPT) satisfy the strong form of Hardy A5;
classical GPTs (n ≥ 2) provably fail it under the framework's
pattern-stability refinement of `StrictConnectedAgency`. -/

/-- **CircleGPT satisfies Hardy A5 strong form.** Via the
TransitiveAgency → hardy_axiom5 bridge, the Circle GPT delivers the
substantive form of Hardy Axiom 5: continuous paths of state-
preserving bijective linear maps between pure states. -/
theorem circle_hardy_axiom5
    (ρ₁ ρ₂ : Fin 3 → ℝ)
    (hp₁ : Continuity.PureState CircleGPT.circleGPT ρ₁)
    (hp₂ : Continuity.PureState CircleGPT.circleGPT ρ₂) :
    ∃ γ : unitInterval → (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ),
      Continuous (fun p : unitInterval × (Fin 3 → ℝ) => γ p.1 p.2) ∧
      γ 0 = LinearMap.id ∧
      γ 1 ρ₁ = ρ₂ ∧
      (∀ t : unitInterval, ∀ ρ ∈ CircleGPT.circleGPT.states, γ t ρ ∈
        CircleGPT.circleGPT.states) ∧
      (∀ t : unitInterval, Function.Bijective (γ t)) :=
  circle_transitive_agency.hardy_axiom5 ρ₁ ρ₂ hp₁ hp₂

/-- **CircleGPT satisfies Hardy A5 strong-form predicate.** -/
theorem circle_axiom5_strong
    (h_pure_states : ∀ ρ, IsExtreme ℝ CircleGPT.circleGPT.states {ρ} →
                          ρ ∈ CircleGPT.circleGPT.states) :
    Hardy.Axiom5_Continuity_Strong CircleGPT.circleGPT :=
  Hardy.axiom5_strong_of_transitive_agency CircleGPT.circleGPT
    circle_transitive_agency h_pure_states

end Dichotomy
end Perspectival
