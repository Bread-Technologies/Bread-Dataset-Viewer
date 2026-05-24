/-
Perspectival Physics — Wantable → GPT (partial bridge)
========================================================

The framework's central technical claim is that operational
probabilistic structure (`GPT`) *emerges* from the metaphysical
perspective-wanting structure (`Wantable`). The full bridge is open;
this module provides a *partial* construction.

Given a *finite* Wantable `W`, we construct:
  - `V W := W → ℝ` (functions on outcomes).
  - The "WantableGPT" with states = probability distributions on `W`
    (states are convex; this is just the standard simplex on `W`).
  - The complement involution on `W` induces a linear involution on
    `V W` that *preserves* the state space.

This is a real connection: the complement structure on `W` *acts* on
the GPT's state space. It does NOT yet show the GPT structure *emerges*
from `W` alone — the convex/normalized states are imposed, not derived.

Status:
  ✓ The Wantable-complement action on `V W` is a well-defined linear
    involution.
  ✓ It preserves the state space (since complement is a bijection on W).
  ▲ Whether this gives the "right" GPT in a framework-distinctive
    sense is open. The construction is one of many possible bridges.

Honest qualification: this is the *thinnest* possible connection, not
a derivation. It shows the metaphysical level can *act* on the
operational level but does not show one produces the other.
-/

import Perspectival.Ontology
import Perspectival.GPT
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Real.Basic

namespace Perspectival
namespace WantableGPT

variable (W : Type u) [Wantable W] [Fintype W] [DecidableEq W]

/-- The carrier vector space of the Wantable-induced GPT. -/
abbrev V := W → ℝ

/-- The complement action on `V W`: pull back by `Wantable.complement`. -/
def complementAction : V W →ₗ[ℝ] V W where
  toFun f := fun w => f (Wantable.complement w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complement action is an involution. -/
theorem complementAction_involutive (f : V W) :
    complementAction W (complementAction W f) = f := by
  funext w
  show f (Wantable.complement (Wantable.complement w)) = f w
  rw [Wantable.complement_involutive]

/-- The states (probability distributions on `W`). -/
def states : Set (V W) := stdSimplex ℝ W

/-- Complement action sends states to states (it permutes outcome
probabilities). -/
theorem complementAction_preserves_states (f : V W) (hf : f ∈ states W) :
    complementAction W f ∈ states W := by
  refine ⟨?_, ?_⟩
  · intro w
    show 0 ≤ f (Wantable.complement w)
    exact hf.1 _
  · -- ∑ w, f (complement w) = ∑ w, f w = 1
    show ∑ w, f (Wantable.complement w) = 1
    rw [← hf.2]
    -- Reindex via the complement involution
    refine Equiv.sum_comp ⟨Wantable.complement, Wantable.complement,
        Wantable.complement_involutive, Wantable.complement_involutive⟩ f

end WantableGPT
end Perspectival
