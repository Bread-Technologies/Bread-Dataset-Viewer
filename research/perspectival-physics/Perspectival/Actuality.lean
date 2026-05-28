/-
Perspectival Physics — Actuality: the possible/actual cut and the
classical / non-classical divide
================================================================

This module formalises the *live* side of the triple no-go theorem.

The no-go proved: the bare relational ontology (a set with an involutive
complement, with NO actualization events) yields the classical simplex
(`WantableGPT.wantableGPT_is_classical`). The missing ingredient is
**choice** — genuine actualization, whose consequence is a *true,
ontological, in-reality difference between the possible and the actual,
from a perspective*.

This file formalises that difference and proves the distinguishing fact:

  • Within a single (classical) frame, actuality is **perspective-
    independent**: the decomposition — i.e. *what is actual* — is uniquely
    forced, read off by the frame's distinguishing measurement
    (`decomposition_unique`).  This is the simplex / epistemic-only case.

  • There exist states with two **incompatible** decompositions — the same
    state genuinely actual-decomposed two ways, with neither frame able to
    actualize the other's outcomes definitely (`square_perspectiveRelative`).
    This is real (ontological) superposition: no fact about which set of
    actuals the state "really" is.

ENCODING DISCIPLINE — avoiding the distribution trap.
We work in pure linear/convex geometry over ℝ, never over a fixed sample
space. A *perspective* is a `Frame`: actual states plus distinguishing
effects, with the δ-law `distinguish i (actual j) = [i = j]`. Two frames
are `Compatible` when every effect of one gives a definite outcome (0 or 1)
on every actual of the other — that is exactly the existence of a common
refinement / joint sample space, i.e. classicality. `Incompatible` frames
have an effect that lands strictly between (≠ 0 and ≠ 1) on a foreign
actual: no joint refinement, no common sample space. Nothing here is the
support of a single distribution over a common space; that classicality is
never assumed — it is precisely what these definitions *characterise*.

FRAMEWORK READING (Schrödinger's flirting / measurement = actualization).
The polarizer angle is the choice of frame; whether the photon passes is
the *clearing* of the meeting; the outcome is owned by neither party alone
(option c). A real superposition is a state that genuinely decomposes into
*different* actuals from *incompatible* perspectives — the ontological,
perspective-relative possible/actual difference that classical
(epistemic-only) probability cannot host. Compatibility is the formal
correlate of "the question has a perspective-independent answer waiting to
be read off"; incompatibility is the correlate of "the answer is
constructed in the asking" (Busemeyer's projection postulate; QBism).
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Perspectival
namespace Actuality

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A **measurement frame** (a *perspective*) on the state space `V`: a
finite family of `actual` states together with `distinguish`ing effects
that read off, from any state, the weight of each actual. The δ-law
`distinguish i (actual j) = [i = j]` is the operational content of
"these actuals are perfectly tellable apart in this frame" — measuring in
this frame *actualizes* exactly one of them. -/
structure Frame (ι : Type*) [Fintype ι] [DecidableEq ι] (V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  /-- The states that become actual when one measures in this perspective. -/
  actual : ι → V
  /-- The effects that read off each actual's weight from any state. -/
  distinguish : ι → (V →ₗ[ℝ] ℝ)
  /-- Perfect distinguishing within the frame (the δ-law). -/
  delta : ∀ i j, distinguish i (actual j) = if i = j then 1 else 0

/-- A **decomposition** of a state `ω` in a frame: `ω` is the convex
combination of the frame's actuals with probability weights `p`. This is
the state seen "from this perspective" — a mixture over the actuals this
perspective can clear. -/
def Decomposes {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Frame ι V) (ω : V) (p : ι → ℝ) :
    Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ ω = ∑ i, p i • F.actual i

/-- **The weights are forced.** Within a frame, the weight of each actual
in a decomposition is exactly what the distinguishing effect reads off the
state. The decomposition is not a free description; it is operationally
determined. -/
theorem weight_eq_distinguish {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Frame ι V)
    {ω : V} {p : ι → ℝ} (h : Decomposes F ω p) (i : ι) :
    p i = F.distinguish i ω := by
  obtain ⟨_, _, hω⟩ := h
  have key : F.distinguish i ω = p i := by
    rw [hω, map_sum, Finset.sum_eq_single i]
    · rw [map_smul, F.delta, if_pos rfl, smul_eq_mul, mul_one]
    · intro j _ hji
      rw [map_smul, F.delta, if_neg (Ne.symm hji), smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  exact key.symm

/-- **Perspective-independent actuality (the classical / simplex case).**
Within a single frame the decomposition is unique: there is a single,
perspective-independent fact about what is actual, and "the possible" is
mere ignorance of it. This is the formal correlate of a simplex — and of
epistemic-only probability. -/
theorem decomposition_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Frame ι V)
    {ω : V} {p q : ι → ℝ} (hp : Decomposes F ω p) (hq : Decomposes F ω q) :
    p = q := by
  funext i
  rw [weight_eq_distinguish F hp i, weight_eq_distinguish F hq i]

/-- Two frames are **compatible** when every effect of `F` gives a definite
outcome (0 or 1) on every actual of `G`: the perspectives share a common
refinement / joint sample space. This is the formal correlate of "the
answer was there all along, perspective-independently." -/
def Compatible {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Frame ι V) (G : Frame κ V) : Prop :=
  ∀ i j, F.distinguish i (G.actual j) = 0 ∨ F.distinguish i (G.actual j) = 1

/-- Two frames are **incompatible** when some effect of `F` lands strictly
between 0 and 1 on an actual of `G`: measuring in `F` cannot actualize `G`'s
outcomes definitely. No joint refinement, no common sample space — the
distribution trap is provably absent. This is the operational core of
genuine complementarity (the polarizer at the "wrong" angle). -/
def Incompatible {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Frame ι V) (G : Frame κ V) : Prop :=
  ∃ i j, F.distinguish i (G.actual j) ≠ 0 ∧ F.distinguish i (G.actual j) ≠ 1

theorem not_compatible_of_incompatible {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {F : Frame ι V} {G : Frame κ V} (h : Incompatible F G) :
    ¬ Compatible F G := by
  obtain ⟨i, j, h0, h1⟩ := h
  intro hc
  rcases hc i j with h | h
  · exact h0 h
  · exact h1 h

/-- **Perspective-relative actuality (real, ontological superposition).**
A state `ω` decomposes — with all actuals genuinely participating
(positive weights) — in two *incompatible* frames. There is no
perspective-independent fact about which set of actuals `ω` "really" is;
the possible/actual cut is real and perspective-relative. This is the
quantum signature, stated in the framework's own vocabulary. -/
def PerspectiveRelative {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Frame ι V) (G : Frame κ V) (ω : V) : Prop :=
  (∃ p, Decomposes F ω p ∧ ∀ i, 0 < p i) ∧
  (∃ q, Decomposes G ω q ∧ ∀ j, 0 < q j) ∧
  Incompatible F G

/-! ## Concrete witness: real superposition exists

The maximally-mixed state of a square (the formal shadow of the qubit's
maximally-mixed state `½|0⟩⟨0|+½|1⟩⟨1| = ½|+⟩⟨+|+½|−⟩⟨−|`) decomposes into
two *incompatible* diagonals. The four corners are affinely dependent
(`v00 + v11 = v01 + v10`) — the non-simplex relation — which is exactly why
the centre has two genuine extreme decompositions and why no single
measurement can actualize all four corners definitely. -/

namespace Square

/-- Ambient space: real functions on three outcomes (one normalization
coordinate + two square coordinates). -/
abbrev W : Type := Fin 3 → ℝ

/-- An effect given by a coefficient vector `c`: `x ↦ ∑ i, c i * x i`. -/
def coeffLin (c : W) : W →ₗ[ℝ] ℝ where
  toFun x := ∑ i, c i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

/-- Corner with square-coordinates `(+1, +1)`. -/
def v00 : W := ![1, 1, 1]
/-- Corner with square-coordinates `(-1, -1)`. -/
def v11 : W := ![1, -1, -1]
/-- Corner with square-coordinates `(+1, -1)`. -/
def v01 : W := ![1, 1, -1]
/-- Corner with square-coordinates `(-1, +1)`. -/
def v10 : W := ![1, -1, 1]
/-- The maximally-mixed centre. -/
def center : W := ![1, 0, 0]

/-- Frame F: the main diagonal `{v00, v11}`, distinguished along `(1,1)`. -/
noncomputable def F : Frame (Fin 2) W where
  actual := ![v00, v11]
  distinguish := ![coeffLin ![1/2, 1/4, 1/4], coeffLin ![1/2, -1/4, -1/4]]
  delta := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [coeffLin, v00, v11, Fin.sum_univ_three] <;> norm_num

/-- Frame G: the anti-diagonal `{v01, v10}`, distinguished along `(1,-1)`. -/
noncomputable def G : Frame (Fin 2) W where
  actual := ![v01, v10]
  distinguish := ![coeffLin ![1/2, 1/4, -1/4], coeffLin ![1/2, -1/4, 1/4]]
  delta := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [coeffLin, v01, v10, Fin.sum_univ_three] <;> norm_num

theorem F_decomposes : Decomposes (V := W) F center ![1/2, 1/2] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · funext k
    fin_cases k <;>
      simp [F, Fin.sum_univ_two, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        v00, v11, center] <;> norm_num

theorem G_decomposes : Decomposes (V := W) G center ![1/2, 1/2] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · funext k
    fin_cases k <;>
      simp [G, Fin.sum_univ_two, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        v01, v10, center] <;> norm_num

/-- **F and G are incompatible.** The F-effect for `v00` gives `v01` the
value `1/2` — neither 0 nor 1 — so measuring in F does not actualize G's
outcomes definitely. No joint sample space exists. -/
theorem F_G_incompatible : Incompatible (V := W) F G := by
  refine ⟨0, 0, ?_, ?_⟩ <;>
    simp [F, G, coeffLin, v01, Fin.sum_univ_three] <;> norm_num

/-- **Real superposition exists.** The square's centre is perspective-
relative: it decomposes through both incompatible diagonals, with every
corner genuinely participating. This is the formal correlate of the qubit's
maximally-mixed state being `½|0⟩⟨0|+½|1⟩⟨1| = ½|+⟩⟨+|+½|−⟩⟨−|` — the same
state, two incompatible sets of actuals, no fact about which is "the" one. -/
theorem square_perspectiveRelative : PerspectiveRelative (V := W) F G center := by
  refine ⟨⟨![1/2, 1/2], F_decomposes, ?_⟩, ⟨![1/2, 1/2], G_decomposes, ?_⟩,
    F_G_incompatible⟩
  · intro i; fin_cases i <;> norm_num
  · intro j; fin_cases j <;> norm_num

end Square

/-- **The bridge, stated.** The two regimes are exclusive at the level of a
single frame: a classical (single-frame) description forces a unique
actual decomposition (`decomposition_unique`), while real superposition
(`PerspectiveRelative`) requires *incompatible* frames — and incompatible
frames exist (`Square.square_perspectiveRelative`). Choice — the genuine,
perspective-relative possible/actual cut — is therefore exactly what the
bare relational ontology (one fixed frame, no actualization) cannot host;
it is the live content the no-go isolated. -/
theorem actuality_bridge :
    -- Classical frames force perspective-independent actuality.
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (F : Frame ι V) {ω : V} {p q : ι → ℝ},
      Decomposes F ω p → Decomposes F ω q → p = q) ∧
    -- Real, perspective-relative superposition is realised by incompatible
    -- frames.
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℝ W)
        (F G : Frame (Fin 2) W) (ω : W), PerspectiveRelative F G ω) := by
  exact ⟨decomposition_unique,
         ⟨Square.W, inferInstance, inferInstance, Square.F, Square.G, Square.center,
          Square.square_perspectiveRelative⟩⟩

end Actuality
end Perspectival
