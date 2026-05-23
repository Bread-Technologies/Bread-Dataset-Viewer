/-
Perspectival Physics — CHSH / Tsirelson Bridge
==============================================

This module connects the perspective–wanting ontology to Mathlib's
algebraic formulation of the CHSH inequality and Tsirelson's bound.

The honest content of this module:
  - We use Mathlib's `IsCHSHTuple` (four self-adjoint involutions in a
    *-ring, with the A's commuting with the B's) as the carrier of a
    "spacelike-separated pair of binary perspectival observables."
  - We give explicit perspective-wanting names to the algebraic objects.
  - We re-state Mathlib's two bounds in our language:
      • REALIST case (the algebra is commutative — there is an
        observer-independent joint ledger of all four facts) ⇒ ≤ 2.
      • PERSPECTIVAL case (the algebra need only have the spacelike
        commutations; different observers may have different ledgers,
        per Frauchiger–Renner C-drop) ⇒ ≤ 2√2.

What is verified here:
  ✓ The re-statement (`PerspectivalCHSH.bound_realist`,
    `PerspectivalCHSH.bound_perspectival`) — these compile as direct
    consequences of Mathlib's `CHSH_inequality_of_comm` and
    `tsirelson_inequality`.

What is NOT verified (and not claimed):
  ✗ That the framework's axioms I–IV FORCE the algebra of observables
    to be a *-ring. The C*-algebra picture is the standard QM
    apparatus and is here imported, not derived from I–IV.
  ✗ That the perspectival case is FORCED to saturate Tsirelson;
    saturation is a tightness result (open in Mathlib at present).

What this module does establish, modestly but cleanly:
  • Given the *-ring picture and the framework's rejection of an
    observer-independent ledger, the relevant bound is Tsirelson 2√2,
    not the local-realist 2. This places the framework on the correct
    side of the experimentally verified Bell/CHSH violations.
  • The "spacelike separation" hypothesis is identified with the
    cross-commutation conditions in the CHSH tuple — i.e., it is
    structural, not metaphysical.
-/

import Mathlib.Algebra.Star.CHSH
import Mathlib.Data.Real.Sqrt
import Perspectival.Ontology

namespace Perspectival

/-! ## Binary perspectival observables -/

/-- A *binary perspectival observable* in a *-ring `R` is a self-adjoint
involution: in the QM dictionary, an observable taking values ±1.
In the framework, it is a question asked of a perspective whose
answer is one of two complementary directions of want. -/
structure BinaryObservable (R : Type u) [Monoid R] [StarMul R] where
  val : R
  is_involution : val ^ 2 = 1
  self_adjoint : star val = val

/-- A *spacelike pair of perspectives* with two binary observables each:
this is the perspective-wanting reading of Mathlib's `IsCHSHTuple`.
The A's are observables of perspective P, the B's are observables of
perspective Q, and the cross-commutation `Aᵢ Bⱼ = Bⱼ Aᵢ` encodes
spacelike separation — neither observer's question disturbs the other
side. -/
structure SpacelikePair (R : Type u) [Monoid R] [StarMul R] where
  /-- Perspective P's first binary observable. -/
  A₀ : BinaryObservable R
  /-- Perspective P's second binary observable. -/
  A₁ : BinaryObservable R
  /-- Perspective Q's first binary observable. -/
  B₀ : BinaryObservable R
  /-- Perspective Q's second binary observable. -/
  B₁ : BinaryObservable R
  /-- Spacelike commutation: P's questions do not disturb Q's. -/
  A₀B₀_commutes : A₀.val * B₀.val = B₀.val * A₀.val
  A₀B₁_commutes : A₀.val * B₁.val = B₁.val * A₀.val
  A₁B₀_commutes : A₁.val * B₀.val = B₀.val * A₁.val
  A₁B₁_commutes : A₁.val * B₁.val = B₁.val * A₁.val

namespace SpacelikePair

variable {R : Type u} [Monoid R] [StarMul R]

/-- A spacelike pair gives rise to a Mathlib CHSH tuple. -/
def toCHSHTuple (s : SpacelikePair R) : IsCHSHTuple s.A₀.val s.A₁.val s.B₀.val s.B₁.val where
  A₀_inv := s.A₀.is_involution
  A₁_inv := s.A₁.is_involution
  B₀_inv := s.B₀.is_involution
  B₁_inv := s.B₁.is_involution
  A₀_sa := s.A₀.self_adjoint
  A₁_sa := s.A₁.self_adjoint
  B₀_sa := s.B₀.self_adjoint
  B₁_sa := s.B₁.self_adjoint
  A₀B₀_commutes := s.A₀B₀_commutes
  A₀B₁_commutes := s.A₀B₁_commutes
  A₁B₀_commutes := s.A₁B₀_commutes
  A₁B₁_commutes := s.A₁B₁_commutes

end SpacelikePair

/-- The "CHSH expression" in perspective-wanting language: the sum of
correlations across the four (A_i, B_j) settings, with the (1,1)
correlation negated. Defined where the ring operations are available. -/
def SpacelikePair.chshExpr {R : Type u} [Ring R] [StarMul R]
    (s : SpacelikePair R) : R :=
  s.A₀.val * s.B₀.val + s.A₀.val * s.B₁.val + s.A₁.val * s.B₀.val - s.A₁.val * s.B₁.val

/-! ## The two bounds, re-stated -/

/-- REALIST CASE.

If the *-ring of observables is commutative — equivalently, if there
is an observer-independent joint ledger assigning consistent ±1 values
to all four observables simultaneously — then the CHSH expression is
bounded by 2.

This is the local-realist bound. The framework rejects the commutativity
hypothesis (different observers, different facts; Frauchiger–Renner C-drop),
so this bound is NOT the prediction of the framework — it is only
included to mark the foil the framework defines itself against. -/
theorem bound_realist {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R]
    (s : SpacelikePair R) :
    s.chshExpr ≤ 2 := by
  unfold SpacelikePair.chshExpr
  exact CHSH_inequality_of_comm _ _ _ _ s.toCHSHTuple

/-- PERSPECTIVAL CASE (Tsirelson).

Without commutativity of the full algebra (only the spacelike
cross-commutations are required), the bound is `2√2 = √2^3`.
This is the bound that experimentally verified Bell-CHSH violations
saturate up to. It is the bound consistent with the framework's
rejection of an observer-independent ledger. -/
theorem bound_perspectival {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (s : SpacelikePair R) :
    s.chshExpr ≤ Real.sqrt 2 ^ 3 • (1 : R) := by
  unfold SpacelikePair.chshExpr
  exact tsirelson_inequality _ _ _ _ s.toCHSHTuple

/-! ## Interpretation, briefly

The Mathlib results are pure algebra. What this module adds is the
*identification*:

   `IsCHSHTuple`  ≅  spacelike pair of binary perspectival observables
   commutativity  ≅  observer-independent joint ledger of facts
   noncommutativity (only spacelike commutations) ≅ different observers, different facts

Under this identification, the framework's philosophical commitment
"reality is the structure of meetings, not a substantial ledger" is
exactly the hypothesis on the algebra that yields Tsirelson rather
than Bell. The work of *deriving* the C*-algebra picture itself from
axioms I–IV is open and is NOT done here. -/

end Perspectival
