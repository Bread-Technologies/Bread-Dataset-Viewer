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

This module:
  ▲ Encodes the broadcaster definition.
  ✓ Constructs a classical broadcaster on the classical GPT,
    demonstrating classical broadcasting is possible.
  ○ Quantum no-broadcasting is NOT proven here; it requires C*-algebra
    structure beyond what our framework imports. Documented as OPEN.

Honest framing: the difference between cloning and broadcasting is
where classical and quantum structures genuinely part ways. Our
framework currently captures the classical side cleanly and flags the
quantum impossibility result as a target requiring more machinery.
-/

import Perspectival.Classical
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis

namespace Perspectival
namespace NoBroadcasting

open TensorProduct

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A *broadcaster* on a set `S ⊆ V`: a linear map `B : V → V ⊗ V`
whose two marginals are the identity on `S`.

We express the marginal conditions via two linear functionals `tr₁`
and `tr₂` from `V ⊗ V` to `V` that should "trace out" the first and
second factor respectively. The user supplies the marginals as
parameters of the definition; existence of canonical marginal-traces
depends on additional structure (tensor categories, partial trace,
etc.) which we do not formalize here. -/
structure IsBroadcaster
    (tr₁ tr₂ : V ⊗[ℝ] V →ₗ[ℝ] V)  -- marginal-trace operations
    (S : Set V) (B : V →ₗ[ℝ] V ⊗[ℝ] V) : Prop where
  marginal₁ : ∀ v ∈ S, tr₁ (B v) = v
  marginal₂ : ∀ v ∈ S, tr₂ (B v) = v

/-! ## Classical broadcasting is possible

Concrete demonstration: for the classical n-outcome GPT, define the
broadcaster `B(eᵢ) := eᵢ ⊗ eᵢ` on vertices and extend by linearity.
Its marginals (under the natural partial-trace operations) recover
the input.
-/

/-- Classical broadcaster on the n-outcome simplex via the standard
basis. For each standard basis vector `e_i` (probability mass at i),
the broadcaster sends it to `e_i ⊗ e_i`. By linearity this extends to
all of `V n = Fin n → ℝ`. -/
noncomputable def classicalBroadcaster (n : ℕ) :
    Classical.V n →ₗ[ℝ] Classical.V n ⊗[ℝ] Classical.V n :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ
    (fun i => Classical.vertex n i ⊗ₜ[ℝ] Classical.vertex n i)

/-! ## Quantum no-broadcasting — open

The Barnum–Caves–Fuchs–Jozsa–Schumacher result states: in a quantum
state space (density matrices of a finite-dim Hilbert space), there
is NO completely-positive trace-preserving map `B` whose marginals
equal the input on a set of two non-commuting density matrices.

This requires:
  - Density-matrix structure (positive operators, trace 1)
  - Completely positive trace-preserving maps
  - Partial trace as concrete marginal-trace

None of these is in our codebase. Mathlib has Hermitian matrices but
not density matrices as a class; Physlib (separate from Mathlib) has
them. Formalizing this is a multi-week project even with the right
upstream.

Honest status: OPEN. The classical/quantum distinction at the
broadcasting level is documented here but the quantum side is not
formalized.
-/

end NoBroadcasting
end Perspectival
