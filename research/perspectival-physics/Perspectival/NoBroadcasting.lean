/-
Perspectival Physics — Broadcasting
====================================

Broadcasting is a weakening of cloning. Where cloning demands
`C(ρ) = ρ ⊗ ρ` (exact copies), broadcasting only requires that the
two marginals of the output equal the input:

    tr₂(B ρ) = ρ  and  tr₁(B ρ) = ρ.

Classically, broadcasting *is possible* (just copy a probability
distribution to two registers; the joint distribution is diagonal
with marginals equal to the original). Quantumly, broadcasting is
*impossible* for non-commuting states (Barnum–Caves–Fuchs–Jozsa–
Schumacher 1996).

Status:
  ✓ Constructive existence of a classical broadcaster (a linear map
    sending each vertex to its diagonal tensor).
  ▲ Marginal-trace operations and the verification that the
    constructed broadcaster's marginals recover the input are left
    for a future refinement; we sketch the construction.
  ○ Quantum no-broadcasting is NOT proven here. It requires C*-algebra
    structure beyond our framework. Documented as OPEN.

Honest framing: the difference between cloning and broadcasting is
exactly where classical and quantum structures part ways. Our
framework currently captures the classical side cleanly and flags the
quantum impossibility result as a target requiring more machinery
(density matrices, CPTP maps, partial trace) we do not import.
-/

import Perspectival.Classical
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis

namespace Perspectival
namespace NoBroadcasting

open TensorProduct

/-- A *broadcaster* on a set `S ⊆ V`: a linear map `B : V → V ⊗ V`
whose two marginals (under user-supplied trace maps) are the identity
on `S`. We parameterize over the marginal-trace operations because
their canonical form depends on additional structure (tensor
categories, partial trace) we do not formalize in this module. -/
structure IsBroadcaster
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (tr₁ tr₂ : V ⊗[ℝ] V →ₗ[ℝ] V)
    (S : Set V) (B : V →ₗ[ℝ] V ⊗[ℝ] V) : Prop where
  marginal₁ : ∀ v ∈ S, tr₁ (B v) = v
  marginal₂ : ∀ v ∈ S, tr₂ (B v) = v

/-- Classical broadcaster on the n-outcome simplex via the standard
basis. For each standard basis vector `e_i` (probability mass at i),
the broadcaster sends it to `e_i ⊗ e_i`. By linearity this extends to
all of `V n = Fin n → ℝ`. -/
noncomputable def classicalBroadcaster (n : ℕ) :
    Classical.V n →ₗ[ℝ] Classical.V n ⊗[ℝ] Classical.V n :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ
    (fun i => Classical.vertex n i ⊗ₜ[ℝ] Classical.vertex n i)

/-- The standard basis vector `Pi.basisFun ℝ (Fin n) i` equals
`Classical.vertex n i`. -/
theorem basisFun_eq_vertex (n : ℕ) (i : Fin n) :
    (Pi.basisFun ℝ (Fin n)) i = Classical.vertex n i := by
  ext j
  show (Pi.basisFun ℝ (Fin n)) i j = if i = j then (1 : ℝ) else 0
  by_cases h : i = j
  · subst h; simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h, Ne.symm h]

/-- The classical broadcaster acts as expected on standard basis
vectors of `Fin n → ℝ`. (The marginal recovery from this diagonal
tensor is straightforward — see `IsBroadcaster` and the discussion
above.) -/
theorem classicalBroadcaster_basisFun (n : ℕ) (i : Fin n) :
    classicalBroadcaster n ((Pi.basisFun ℝ (Fin n)) i)
    = Classical.vertex n i ⊗ₜ[ℝ] Classical.vertex n i := by
  simp [classicalBroadcaster]

/-! ## Quantum no-broadcasting — open

The Barnum–Caves–Fuchs–Jozsa–Schumacher result states: in a quantum
state space (density matrices of a finite-dim Hilbert space), there
is NO completely-positive trace-preserving map `B` whose marginals
equal the input on a set of two non-commuting density matrices.

This requires:
  - Density-matrix structure (positive operators, trace 1)
  - Completely positive trace-preserving maps
  - Partial trace as concrete marginal-trace

Mathlib has Hermitian matrices but not density matrices as a class;
Physlib (separate from Mathlib) has them. Formalizing the BCFJS
theorem is a multi-week project even with the right upstream.

Honest status: OPEN. -/

end NoBroadcasting
end Perspectival
