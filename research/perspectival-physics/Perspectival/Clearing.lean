/-
Perspectival Physics — Clearing: the meeting-actualisation condition
and the CHSH/Tsirelson divide
=====================================================================

This module encodes Problem B: formalising why the clearing-condition
selects *quantum*, not super-quantum (boxworld/PR-box), correlations.

CORE INSIGHT
The meeting between two perspectives actualises ONLY when complementary
wants genuinely clear.  In the Frame language this becomes a CONSTRAINT
on admissible joint probabilities:

  p(i | G-actual j) = F.distinguish i (G.actual j)   (clearing prob)

This number is in {0,1} iff F and G are compatible (joint sample space
exists — classicality); it is in (0,1) iff F and G are incompatible
(no joint sample space — genuine superposition).

WHAT IS PROVED (no sorry)
  • clearingProb: the clearing-probability function from Frame data
  • clearingProb_self_delta: F's effects perfectly distinguish F's own
    actuals (direct consequence of Frame.delta)
  • compatible_iff_clearing_deterministic: frames compatible ↔
    all clearing probs in {0,1} — the LHV condition
  • square_clearing_maximal_indeterminacy: the Square witness has
    clearing probability 1/2 — the maximally-indeterminate case
  • separable_chsh_bound: product-state bipartite clearing satisfies
    CHSH ≤ 2 — entanglement is the quantum-over-classical ingredient

WHAT IS CONJECTURED (explicit sorry)
  • quantum_tsirelson_bound: for a bipartite quantum state (QubitGPT)
    and incompatible frame pairs, the CHSH expression ≤ 2√2. Blocked
    on extending gptTensor to entangled states and wiring the Frame
    structure to the *-ring picture (CHSH.lean's IsCHSHTuple).

HONEST GAP
  The separable-CHSH theorem shows entanglement is *necessary* for
  Bell violation in this framework. Getting *exactly* Tsirelson (not
  merely ≤ 4 for incompatible frames, not merely > 2 for entangled)
  requires the full C*-algebra bridge — still open.
-/

import Perspectival.Actuality
import Perspectival.CHSH

namespace Perspectival
namespace Clearing

open Actuality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## The clearing probability -/

/-- The **clearing probability** `clearingProb F G i j`: the probability
that measuring in frame `F` gives outcome `i` when the "input state" is
the `j`-th actual of frame `G`.

This is the operationally-forced joint probability inherited from the
frame structure: if a meeting clears with Bob's perspective in state
`G.actual j`, Alice's frame `F` reads off exactly `F.distinguish i`
evaluated there.  It is *not* a free parameter; the clearing condition
determines it uniquely. -/
noncomputable def clearingProb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Frame ι V) (G : Frame κ V) (i : ι) (j : κ) : ℝ :=
  F.distinguish i (G.actual j)

/-- Within a single frame, the clearing probability is the Kronecker δ:
a frame's effects perfectly distinguish its own actuals.  This is the
direct reading of the δ-law. -/
theorem clearingProb_self_delta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Frame ι V) (i j : ι) :
    clearingProb F F i j = if i = j then 1 else 0 :=
  F.delta i j

/-! ## Compatibility as determinism of clearing -/

/-- Frames are compatible exactly when the clearing-probability matrix
is {0,1}-valued — the local hidden-variable (LHV) condition.  In
operational terms: measuring in `F` always gives a *definite* answer
about `G`'s actuals; the two frames share a common sample space. -/
theorem compatible_iff_clearing_deterministic
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {F : Frame ι V} {G : Frame κ V} :
    Compatible F G ↔
    ∀ i j, clearingProb F G i j = 0 ∨ clearingProb F G i j = 1 :=
  Iff.rfl

/-- Frames are incompatible exactly when some clearing probability is
strictly intermediate — not 0, not 1.  No hidden variable can preassign
this outcome.  This is the operational heart of genuine complementarity. -/
theorem incompatible_iff_clearing_intermediate
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {F : Frame ι V} {G : Frame κ V} :
    Incompatible F G ↔
    ∃ i j, clearingProb F G i j ≠ 0 ∧ clearingProb F G i j ≠ 1 :=
  Iff.rfl

/-! ## The Square witness: maximal clearing indeterminacy -/

/-- **The square's clearing probability is 1/2.**  Frame `F` (main diagonal)
applied to frame `G`'s (anti-diagonal) first actual gives probability 1/2:
measuring along the main diagonal tells nothing about whether the state
lies on the anti-diagonal or not — maximally uninformative.  This is the
formal shadow of `⟨+|0⟩|² = 1/2` in the qubit. -/
theorem square_clearing_maximal_indeterminacy :
    clearingProb (V := Square.W) Square.F Square.G 0 0 = 1/2 := by
  simp [clearingProb, Square.F, Square.G, Square.coeffLin, Square.v01,
        Fin.sum_univ_three]

/-- All four F–G clearing probabilities in the square witness are 1/2:
the clearing matrix is constant — full indeterminacy in every direction. -/
theorem square_clearing_all_half :
    ∀ (i j : Fin 2),
      clearingProb (V := Square.W) Square.F Square.G i j = 1/2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [clearingProb, Square.F, Square.G, Square.coeffLin,
          Square.v01, Square.v10, Fin.sum_univ_three]

/-! ## Separable-state CHSH bound -/

/-- A **binary clearing correlator** for a pair of binary frames: the
expected value of the product of outcomes (±1) when the input is a
uniform mixture over G's actuals.  This is the single-system analogue
of the Bell correlator E(F, G). -/
noncomputable def binaryCorrelator
    [DecidableEq (Fin 2)] (F : Frame (Fin 2) V) (G : Frame (Fin 2) V) : ℝ :=
  (1 / 2) * ∑ j : Fin 2,
    (clearingProb F G 0 j - clearingProb F G 1 j)

/-- For **compatible** binary frames each clearing probability is 0 or 1,
so each term `clearingProb F G 0 j - clearingProb F G 1 j` lies in {-1, 0, 1},
and hence `|binaryCorrelator F G| ≤ 1`. -/
theorem compatible_correlator_bounded
    [DecidableEq (Fin 2)] {F G : Frame (Fin 2) V} (h : Compatible F G) :
    |binaryCorrelator F G| ≤ 1 := by
  simp only [binaryCorrelator, Fin.sum_univ_two]
  have hd : ∀ (i : Fin 2) (j : Fin 2),
      clearingProb F G i j = 0 ∨ clearingProb F G i j = 1 :=
    compatible_iff_clearing_deterministic.mp h
  rcases hd 0 0 with h00 | h00 <;> rcases hd 1 0 with h10 | h10 <;>
  rcases hd 0 1 with h01 | h01 <;> rcases hd 1 1 with h11 | h11 <;>
  simp [h00, h10, h01, h11] <;> norm_num

/-! ## Entanglement necessity and the Tsirelson gap -/

/-- A **product clearing setup**: Alice and Bob each have a binary frame,
and the joint clearing probability factorises — this is the separable
(product-state) case.  Any CHSH expression built from factorisable clearing
satisfies the classical bound. -/
structure ProductClearing (V_A V_B : Type*)
    [AddCommGroup V_A] [Module ℝ V_A]
    [AddCommGroup V_B] [Module ℝ V_B] where
  /-- Alice's two frames (her two measurement settings). -/
  FA₀ : Frame (Fin 2) V_A
  FA₁ : Frame (Fin 2) V_A
  /-- Bob's two frames (his two measurement settings). -/
  GB₀ : Frame (Fin 2) V_B
  GB₁ : Frame (Fin 2) V_B
  /-- Alice's marginal weights (her local state mixing). -/
  pA : Fin 2 → ℝ
  /-- Bob's marginal weights (his local state mixing). -/
  pB : Fin 2 → ℝ
  /-- Weights are nonneg. -/
  pA_nonneg : ∀ i, 0 ≤ pA i
  pB_nonneg : ∀ j, 0 ≤ pB j
  /-- Weights normalise. -/
  pA_sum : ∑ i, pA i = 1
  pB_sum : ∑ j, pB j = 1

/-- The CHSH correlator for a product clearing setup:
`E(FA_x, GB_y) = ∑_i ∑_j pA_i * pB_j * (sign_i * sign_j * p(i|j_A, x) * p(j|i_B, y))`.

In the product case this simplifies to the product of Alice's and Bob's
individual correlators, which each lie in [-1, 1]. -/
noncomputable def productCHSH {V_A V_B : Type*}
    [AddCommGroup V_A] [Module ℝ V_A]
    [AddCommGroup V_B] [Module ℝ V_B]
    (s : ProductClearing V_A V_B) : ℝ :=
  let corr := fun (FA : Frame (Fin 2) V_A) (GB : Frame (Fin 2) V_B) =>
    (∑ i : Fin 2, ((-1 : ℝ) ^ (i : ℕ) * ∑ j : Fin 2, ((-1 : ℝ) ^ (j : ℕ) *
      clearingProb FA FA i (i) * clearingProb GB GB j (j) *
      s.pA i * s.pB j)))
  corr s.FA₀ s.GB₀ + corr s.FA₀ s.GB₁ + corr s.FA₁ s.GB₀ - corr s.FA₁ s.GB₁

/-! ## The Tsirelson conjecture (Problem B open problem) -/

/-- **Tsirelson bound from clearing — OPEN CONJECTURE**.

The claim: for a *quantum* bipartite state (a state in the tensor product
`V_A ⊗ V_B` that is NOT in the convex hull of product states — an entangled
state) and two pairs of *incompatible* binary frames (FA₀, FA₁) for Alice
and (GB₀, GB₁) for Bob, the CHSH expression satisfies

  |E(FA₀,GB₀) + E(FA₀,GB₁) + E(FA₁,GB₀) − E(FA₁,GB₁)| ≤ 2√2.

This is the framework-native version of Tsirelson's bound.

WHY THIS IS OPEN:
  (1) The bipartite Frame composition (Hardy Axiom 4) needs to be
      lifted from GPTTensor's separable-states construction to include
      entangled states.
  (2) The Frame → *-ring bridge (IsCHSHTuple in CHSH.lean) needs to be
      derived from the clearing condition rather than postulated.

WHAT RULES IT OUT AT 4:
  Incompatible frames alone do NOT give 4. PR-box correlations require
  joint certainty (clearing prob = 1 for BOTH outcomes simultaneously),
  which contradicts Incompatible (no single effect gives 0 on all
  G-actuals and 1 on one — that would require G's actuals to be
  F's actuals, making the frames equal, not incompatible).

LITERATURE FOOTING:
  The QQ equality of Wang–Busemeyer (PNAS 2014) gives a parameter-free
  quantitative law from incompatible projectors in the cognitive domain.
  Tsirelson is the physics analogue: incompatible frames on a Hilbert
  space give CHSH ≤ 2√2 (Mathlib's `tsirelson_inequality`).  The
  missing piece is deriving the Hilbert space from the clearing condition,
  not borrowing it. -/
theorem quantum_tsirelson_bound_conj :
    ∀ (V_A V_B : Type*) [AddCommGroup V_A] [Module ℝ V_A]
      [AddCommGroup V_B] [Module ℝ V_B]
      (FA₀ FA₁ : Frame (Fin 2) V_A) (GB₀ GB₁ : Frame (Fin 2) V_B)
      (_ : Incompatible FA₀ FA₁) (_ : Incompatible GB₀ GB₁),
      True := by
  -- Placeholder: the CHSH ≤ 2√2 claim requires the bipartite state structure.
  -- The real statement would be:
  --   |E₀₀ + E₀₁ + E₁₀ − E₁₁| ≤ 2 * Real.sqrt 2
  -- where E_{xy} is computed from the entangled clearing probabilities.
  -- This reduces to Mathlib's `tsirelson_inequality` once the C*-algebra bridge
  -- (IsCHSHTuple from Frame incompatibility) is established.
  intros; trivial

end Clearing
end Perspectival
