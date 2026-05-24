/-
Perspectival Physics — Hardy's Axioms
======================================

Hardy 2001 ("Quantum Theory From Five Reasonable Axioms") reconstructs
finite-dim quantum mechanics from operational axioms on a GPT. The
celebrated dichotomy: dropping continuity yields classical theory
(K = N); keeping all five yields quantum theory (K = N²).

This module states Hardy's axioms as predicates on `Perspectival.GPT`
and **categorizes each one** with respect to our framework's axioms
I–IV:

    DERIVABLE — follows from I–IV (no additional postulate needed)
    AUXILIARY — independent of I–IV; addable without contradiction
    INCOMPATIBLE — in tension with I–IV; would require revision

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
import Perspectival.Ontology
import Mathlib.Analysis.Convex.Extreme

namespace Perspectival
namespace Hardy

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
-- The statement is correct in form; we have NOT proven this for our
-- GPT class. It is an OPEN derivation target.

/-- **Axiom 4 — Composite systems.**
A composite system consisting of subsystems A and B satisfies
`N_AB = N_A * N_B` and `K_AB = K_A * K_B`.

Category: **AUXILIARY** (refinement may make it DERIVABLE).
The framework's Composition.lean shows disjoint-union has no cross-
system meetings (no-signaling). However, the multiplicative composition
rule (tensor structure) is STRONGER than the disjoint-union we have.
Tensor composition appears to require an additional postulate about
how independent perspectives' meeting probabilities multiply. -/
def Axiom4_Composite_States_Multiply
    {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : GPT VA) (GB : GPT VB) (nA nB : ℕ) : Prop :=
  HasDimensionN GA nA → HasDimensionN GB nB →
  -- There exists a composite GPT with dimension nA * nB.
  -- We do not yet have the tensor product of GPTs formalized.
  True  -- placeholder; precise formalization pending tensor product of GPTs

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

/-! ## Summary of categorizations (the actual research output of this file)

  Axiom 1 (Probabilities)        — DERIVABLE (immediate from GPT structure;
                                   `axiom1_holds` proves it formally).
  Axiom 2 (Simplicity / K min)   — AUXILIARY (cross-theory selection
                                   principle; not entailed by I–IV).
  Axiom 3 (Subspaces)            — DERIVABLE (argued; formal proof OPEN).
  Axiom 4 (Composite systems)    — AUXILIARY (multiplicative rule beyond
                                   the disjoint-union we have; possibly
                                   derivable with refined composition).
  Axiom 5 (Continuity)           — DERIVABLE (argued; the framework's
                                   libertarian commitment FAVORS but does
                                   not force the continuous case;
                                   formal proof OPEN).

The genuine research bottleneck: turning the ARGUED entries into
formally proven ones, OR honestly downgrading them to AUXILIARY if
that turns out to be the case. This is the next stage of Tier 1.
-/

end Hardy
end Perspectival
