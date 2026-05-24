/-
Perspectival Physics — Worked Examples
========================================

Concrete instantiations of the framework's abstract theorems on small
worked examples. Each example chains together multiple verified
results to show the framework operating end-to-end.

Status: ✓ all examples compile without `sorry`.
-/

import Perspectival.Ontology
import Perspectival.Transformations
import Perspectival.Composition
import Perspectival.Classical
import Perspectival.Distinguish
import Perspectival.NoCloning
import Perspectival.NoBroadcasting
import Perspectival.WantableGPT
import Perspectival.Hardy
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace Perspectival
namespace Examples

open TensorProduct

/-! ## Example 1 — A boolean Wantable

The simplest non-trivial Wantable: `Bool` with `complement := not`.
-/

instance : Wantable Bool where
  complement := not
  complement_involutive := by intro b; cases b <;> rfl

/-- The integers form a Wantable with `complement := Neg.neg`
(signed-wanting; positive wants meet their negation). -/
instance : Wantable ℤ where
  complement := Neg.neg
  complement_involutive := neg_neg

example : (Wantable.complement (3 : ℤ)) = -3 := rfl
example : Wantable.complement (Wantable.complement (5 : ℤ)) = 5 := by
  exact neg_neg 5

/-- `Fin 2` as a Wantable: complement is the swap 0 ↔ 1. -/
instance : Wantable (Fin 2) where
  complement
    | 0 => 1
    | 1 => 0
  complement_involutive
    | 0 => rfl
    | 1 => rfl

/-- The trivial Wantable: `Unit` with `complement := id`. The
"existence-without-direction" degenerate case. -/
instance : Wantable Unit where
  complement := id
  complement_involutive _ := rfl

example : (Wantable.complement () = ()) := rfl

/-- The empty Wantable: `Empty` has no elements so vacuously involutive.
"No existence" — nothing to direct, nothing to meet. -/
instance : Wantable Empty where
  complement := fun e => e.elim
  complement_involutive := fun e => e.elim

/-! ## Examples of the product-Wantable structure -/

/-- On `Bool × Bool`, complement is componentwise `not`. -/
example : (Wantable.complement ((true, true) : Bool × Bool)) = (false, false) := rfl
example : (Wantable.complement ((true, false) : Bool × Bool)) = (false, true) := rfl

/-- A meeting on `Bool × Bool`: the pair (true, false) meets its complement
(false, true). -/
def boolBoolMeeting : Meeting (Bool × Bool) where
  side₁ := (true, false)
  side₂ := (false, true)
  complementary := rfl

/-- The product Wantable structure is consistent with the component
Wantable structure. -/
example (b₁ b₂ : Bool) :
    Wantable.complement ((b₁, b₂) : Bool × Bool)
    = (Wantable.complement b₁, Wantable.complement b₂) := rfl

/-- Constructing a meeting from a side: mk_fromSide on Bool. -/
example : (Perspectival.Meeting.mk_fromSide Bool true).side₂ = false := rfl
example : (Perspectival.Meeting.mk_fromSide Bool false).side₂ = true := rfl

/-- Every meeting on Bool is determined by its first side. -/
example (m : Meeting Bool) :
    m = Perspectival.Meeting.mk_fromSide Bool m.side₁ :=
  (Perspectival.Meeting.mk_fromSide_side₁_inv Bool m).symm

/-- A meeting on `Fin 2` constructed from its first side. -/
example : (Perspectival.Meeting.mk_fromSide (Fin 2) 0).side₂ = 1 := rfl
example : (Perspectival.Meeting.mk_fromSide (Fin 2) 1).side₂ = 0 := rfl

/-- `Fin 4` with reflection `complement i := 3 - i` is a Wantable
(0↔3, 1↔2). -/
instance : Wantable (Fin 4) where
  complement i := 3 - i
  complement_involutive i := by fin_cases i <;> decide

example : Wantable.complement (0 : Fin 4) = 3 := by decide
example : Wantable.complement (1 : Fin 4) = 2 := by decide
example : Wantable.complement (2 : Fin 4) = 1 := by decide
example : Wantable.complement (3 : Fin 4) = 0 := by decide

/-- The WantableGPT on `Fin 2` has 2-dimensional carrier vector space. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 2)) = 2 := by
  show Module.finrank ℝ (Fin 2 → ℝ) = 2
  simp

/-- The WantableGPT on `Fin 4` has 4-dimensional carrier. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) = 4 := by
  show Module.finrank ℝ (Fin 4 → ℝ) = 4
  simp

/-- The operational dimension of `Classical.gpt n` is bounded by its
linear dimension. Combined with the vertex distinguishability set, this
gives the framework's verified N ≤ K direction in concrete form. -/
example (n : ℕ) {S : Fin n → Perspectival.Classical.V n}
    (w : Perspectival.Distinguish.PerfectWitness (G := Perspectival.Classical.gpt n) S) :
    n ≤ Module.finrank ℝ (Perspectival.Classical.V n) :=
  Perspectival.Distinguish.operational_dim_le_state_dim S w

/-- The unit Wantable's only meeting. -/
example (m : Meeting Unit) : m.side₁ = () := rfl

example (m : Meeting Unit) : m.side₂ = () := rfl

/-- All meetings on Unit are equal: the unit Wantable has a single
meeting up to equality. -/
example (m₁ m₂ : Meeting Unit) : m₁ = m₂ := by
  cases m₁
  cases m₂
  rfl

/-- The disjoint union Bool ⊕ Bool inherits a Wantable structure
from each Bool. -/
example : Wantable (Bool ⊕ Bool) := inferInstance

/-- The product Bool × Bool inherits a Wantable structure. -/
example : Wantable (Bool × Bool) := inferInstance

/-- The complement in Bool ⊕ Bool acts component-wise. -/
example : Wantable.complement (Sum.inl true : Bool ⊕ Bool) = Sum.inl false := rfl
example : Wantable.complement (Sum.inr false : Bool ⊕ Bool) = Sum.inr true := rfl

/-- On `ℤ` with `complement := Neg.neg`, the complement PTrans is
not the identity. -/
example : (PTrans.complement : PTrans ℤ) ≠ 1 := by
  intro h
  have hap : (PTrans.complement : PTrans ℤ).toFun 1 = (1 : PTrans ℤ).toFun 1 := by
    rw [h]
  -- (complement).toFun 1 = -1, while (1).toFun 1 = 1
  have : (-1 : ℤ) = 1 := hap
  linarith

/-- Squared complement on ℤ is identity. -/
example : (PTrans.complement : PTrans ℤ) * PTrans.complement = 1 :=
  PTrans.complement_sq

/-- The disjoint union `Bool ⊕ Empty` inherits a Wantable structure.
Effectively isomorphic to Bool (Empty contributes nothing). -/
example : Wantable (Bool ⊕ Empty) := inferInstance

/-- The product `Bool × Unit` inherits Wantable. Effectively
isomorphic to Bool. -/
example : Wantable (Bool × Unit) := inferInstance

/-- The `complement` on `Bool ⊕ Empty` acts only on the Bool side
(Empty side has no elements). -/
example : Wantable.complement (Sum.inl true : Bool ⊕ Empty) = Sum.inl false := rfl

/-- The `PTrans.complement` on a product Wantable equals the
componentwise prodMap of the per-component complements. -/
example : (PTrans.complement : PTrans (Bool × Bool))
        = PTrans.prodMap PTrans.complement PTrans.complement := by
  apply PTrans.ext
  intro p
  cases p
  rfl

/-- Similarly for the disjoint union. -/
example : (PTrans.complement : PTrans (Bool ⊕ Bool))
        = PTrans.sumMap PTrans.complement PTrans.complement := by
  apply PTrans.ext
  intro p
  cases p <;> rfl

/-- `Fin 3` with `complement := id` — every want is its own complement.
The "self-meeting" Wantable: an odd-cardinality finite set forced to
use identity-complement. -/
instance : Wantable (Fin 3) where
  complement := id
  complement_involutive _ := rfl

example : Wantable.complement (1 : Fin 3) = 1 := rfl

/-- In a self-meeting Wantable, every meeting has both sides equal. -/
example (m : Meeting (Fin 3)) : m.side₁ = m.side₂ := by
  have := m.complementary
  show m.side₁ = m.side₂
  rw [← this]
  rfl

/-- The complement PTrans on Fin 3 (with id complement) IS the identity. -/
example : (PTrans.complement : PTrans (Fin 3)) = 1 := by
  apply PTrans.ext
  intro i
  rfl

/-- The `Option` type lifts a Wantable structure: `none` is its own
complement, `some w` complements to `some (complement w)`. -/
instance {W : Type u} [Wantable W] : Wantable (Option W) where
  complement
    | some w => some (Wantable.complement w)
    | none => none
  complement_involutive
    | some w => by show some (Wantable.complement (Wantable.complement w)) = some w
                   rw [Wantable.complement_involutive]
    | none => rfl

example : Wantable.complement (some true : Option Bool) = some false := rfl
example : (Wantable.complement (none : Option Bool)) = none := rfl

/-- Function spaces lift Wantable: `(A → W)` is Wantable when `W` is,
with complement applied pointwise. -/
instance {A : Type u} {W : Type u} [Wantable W] : Wantable (A → W) where
  complement f := fun a => Wantable.complement (f a)
  complement_involutive f := by
    funext a
    exact Wantable.complement_involutive (f a)

/-- Lists over a Wantable: `List W` lifts the complement pointwise via
`List.map`. -/
instance {W : Type u} [Wantable W] : Wantable (List W) where
  complement := List.map Wantable.complement
  complement_involutive l := by
    induction l with
    | nil => rfl
    | cons a as ih =>
      show List.map Wantable.complement (List.map Wantable.complement (a :: as)) = a :: as
      simp [List.map, Wantable.complement_involutive, ih]

example : Wantable.complement ([true, false, true] : List Bool) = [false, true, false] := rfl

/-- Double complement is identity on a concrete list. -/
example :
    Wantable.complement (Wantable.complement ([true, false] : List Bool))
    = [true, false] :=
  Wantable.complement_involutive _

/-- The PTrans group on Unit is trivial: only the identity. -/
example (f : PTrans Unit) : f = 1 := by
  apply PTrans.ext
  intro u
  cases u
  -- f.toFun () = () (only one possible value for Unit)
  rfl

/-- The PTrans group on Empty is also trivial (vacuously: no elements). -/
example (f : PTrans Empty) : f = 1 := by
  apply PTrans.ext
  intro e
  exact e.elim

/-- `PTrans Unit` is a subsingleton. -/
instance : Subsingleton (PTrans Unit) := ⟨by
  intro f g
  apply PTrans.ext
  intro u
  cases u
  rfl⟩

/-- `PTrans Empty` is a subsingleton. -/
instance : Subsingleton (PTrans Empty) := ⟨by
  intro f g
  apply PTrans.ext
  intro e
  exact e.elim⟩

-- NOTE: PTrans Bool has exactly 2 elements (identity and complement).
-- Proof omitted for brevity; the structural argument is standard
-- (case analysis on f.toFun true).

/-- The classical broadcaster exists for the 2-outcome classical GPT. -/
noncomputable example : Perspectival.Classical.V 2 →ₗ[ℝ]
          Perspectival.Classical.V 2 ⊗[ℝ] Perspectival.Classical.V 2 :=
  Perspectival.NoBroadcasting.classicalBroadcaster 2

/-- The classical broadcaster exists for any n-outcome classical GPT. -/
noncomputable example (n : ℕ) : Perspectival.Classical.V n →ₗ[ℝ]
          Perspectival.Classical.V n ⊗[ℝ] Perspectival.Classical.V n :=
  Perspectival.NoBroadcasting.classicalBroadcaster n

/-- WantableGPT(Bool) admits a perfect-witness via projections. -/
example : Perspectival.Distinguish.PerfectWitness
    (G := Perspectival.WantableGPT.gpt Bool)
    (Perspectival.WantableGPT.vertex Bool) :=
  Perspectival.WantableGPT.perfectWitness Bool

/-- Linearly independent vertices in WantableGPT(Bool). -/
example : LinearIndependent ℝ
    (fun b : Bool => Perspectival.WantableGPT.vertex Bool b) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype Bool

-- NOTE: a String Wantable via reversal exists but stating it depends
-- on Lean's specific representation of String. Skipped for portability.

/-- Symmetric formulation: complement on Bool. -/
example : (Wantable.complement true = false) ↔ true = Wantable.complement false :=
  Wantable.complement_eq_iff true false

/-- fromPTrans of PTrans.complement on Bool gives the complement action. -/
example :
    (Perspectival.WantableGPT.fromPTrans Bool PTrans.complement).toLin
    = Perspectival.WantableGPT.complementAction Bool := by
  apply LinearMap.ext
  intro f
  funext b
  cases b <;> rfl

/-- WantableGPT(Bool) has 2-dimensional carrier. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 := by
  show Module.finrank ℝ (Bool → ℝ) = 2
  rw [Module.finrank_pi]
  simp

/-- WantableGPT(Unit) has 1-dimensional carrier. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Unit) = 1 := by
  show Module.finrank ℝ (Unit → ℝ) = 1
  rw [Module.finrank_pi]
  simp

/-- WantableGPT(Fin 3) has 3-dimensional carrier. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) = 3 := by
  show Module.finrank ℝ (Fin 3 → ℝ) = 3
  simp

/-- WantableGPT(Bool × Bool) has 4-dim carrier (the product Wantable). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 := by
  show Module.finrank ℝ (Bool × Bool → ℝ) = 4
  rw [Module.finrank_pi]
  simp

/-- WantableGPT(Bool ⊕ Bool) has 4-dim carrier (disjoint union). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 := by
  show Module.finrank ℝ (Bool ⊕ Bool → ℝ) = 4
  rw [Module.finrank_pi]
  simp

/-- For product Wantables, finrank multiplies. -/
example {W₁ W₂ : Type u} [Fintype W₁] [Fintype W₂] :
    Module.finrank ℝ (W₁ × W₂ → ℝ)
    = Module.finrank ℝ (W₁ → ℝ) * Module.finrank ℝ (W₂ → ℝ) := by
  rw [Module.finrank_pi, Module.finrank_pi, Module.finrank_pi]
  exact Fintype.card_prod W₁ W₂

/-- For disjoint-union Wantables, finrank ADDS (not multiplies). This
distinguishes our two composition modes — the disjoint union gives
N(W₁ ⊕ W₂) = N(W₁) + N(W₂), while the product gives N(W₁ × W₂) =
N(W₁) · N(W₂). Hardy's Axiom 4 demands multiplicativity. -/
example {W₁ W₂ : Type u} [Fintype W₁] [Fintype W₂] :
    Module.finrank ℝ (W₁ ⊕ W₂ → ℝ)
    = Module.finrank ℝ (W₁ → ℝ) + Module.finrank ℝ (W₂ → ℝ) := by
  rw [Module.finrank_pi, Module.finrank_pi, Module.finrank_pi]
  exact Fintype.card_sum

/-- The product Wantable admits component-wise complement-PTrans that
are non-trivial. -/
example : PTrans.prodMap (PTrans.complement : PTrans Bool) (1 : PTrans Bool) ≠ 1 := by
  intro h
  have hap : (PTrans.prodMap (PTrans.complement : PTrans Bool) (1 : PTrans Bool)).toFun
              (true, true) = (1 : PTrans (Bool × Bool)).toFun (true, true) := by rw [h]
  -- LHS = (false, true), RHS = (true, true) — first components differ.
  have heq : ((false, true) : Bool × Bool) = (true, true) := hap
  have : false = true := (Prod.mk.injEq _ _ _ _).mp heq |>.1
  exact Bool.false_ne_true this

/-- PTrans.complement on Bool × Bool acts on both components. -/
example : (PTrans.complement : PTrans (Bool × Bool)).toFun (true, true) = (false, false) :=
  rfl

/-- PTrans.complement on Bool ⊕ Bool acts within each component. -/
example : (PTrans.complement : PTrans (Bool ⊕ Bool)).toFun (Sum.inl true) = Sum.inl false :=
  rfl

example : (PTrans.complement : PTrans (Bool ⊕ Bool)).toFun (Sum.inr false) = Sum.inr true :=
  rfl

/-- Complement on a function space (Bool → Bool) acts pointwise. -/
example (f : Bool → Bool) : Wantable.complement f = fun b => not (f b) := rfl

/-- The constant-true function complements to constant-false. -/
example : Wantable.complement (fun _ : Bool => true) = (fun _ => false) := rfl

/-- The identity function on Bool complements to negation. -/
example : Wantable.complement (id : Bool → Bool) = not := rfl

/-- Negation complements to identity. -/
example : Wantable.complement (not : Bool → Bool) = id := by
  funext b
  cases b <;> rfl

/-- The empty list is its own complement. -/
example : Wantable.complement ([] : List Bool) = [] := rfl

/-- A singleton list complements its single element. -/
example : Wantable.complement ([true] : List Bool) = [false] := rfl

/-- The complement of an Option is none-preserving. -/
example : Wantable.complement (none : Option (Fin 2)) = none := rfl

/-- The complement of `some 0 : Option (Fin 2)` is `some 1`. -/
example : Wantable.complement (some 0 : Option (Fin 2)) = some 1 := rfl

/-- For ℤ, the complement of 0 is 0 (fixed point). -/
example : Wantable.complement (0 : ℤ) = 0 := neg_zero

/-- For ℤ, no positive integer is its own complement (no fixed points
of negation among positives). -/
example (n : ℤ) (h : 0 < n) : Wantable.complement n ≠ n := by
  intro heq
  -- heq : -n = n
  have : -n = n := heq
  linarith

/-- 1 and -1 form a complementary pair in ℤ. -/
example : (Wantable.complement (1 : ℤ) = -1) ∧ (Wantable.complement (-1 : ℤ) = 1) :=
  ⟨rfl, by show -(-1 : ℤ) = 1; ring⟩

/-- Meetings on ℤ are pairs of opposite integers. -/
example : Meeting ℤ := Perspectival.Meeting.mk_fromSide ℤ 5

example : (Perspectival.Meeting.mk_fromSide ℤ 5).side₂ = -5 := rfl

example : (Perspectival.Meeting.mk_fromSide ℤ 100).side₂ = -100 := rfl

example : (Perspectival.Meeting.mk_fromSide ℤ 0).side₂ = 0 := rfl

/-- Meeting with 0 in ℤ is a self-meeting (both sides equal). -/
example : (Perspectival.Meeting.mk_fromSide ℤ 0).side₁
        = (Perspectival.Meeting.mk_fromSide ℤ 0).side₂ := rfl

/-- 0 is the only ℤ-self-meeting (n is a self-meeting iff n = 0). -/
example (n : ℤ) :
    (Perspectival.Meeting.mk_fromSide ℤ n).side₁
    = (Perspectival.Meeting.mk_fromSide ℤ n).side₂ ↔ n = 0 := by
  constructor
  · intro h
    show n = 0
    have : n = -n := h
    linarith
  · intro h
    subst h
    rfl

/-- For ℤ, the meeting is self-meeting iff the want is a complement-
fixed-point. This is a general principle. -/
example {W : Type u} [Wantable W] (w : W) :
    (Perspectival.Meeting.mk_fromSide W w).side₁
    = (Perspectival.Meeting.mk_fromSide W w).side₂
    ↔ Wantable.complement w = w := by
  constructor
  · intro h
    show Wantable.complement w = w
    exact h.symm
  · intro h
    show w = Wantable.complement w
    exact h.symm

/-- On Unit, every meeting is a self-meeting (complement = id). -/
example (m : Meeting Unit) : m.side₁ = m.side₂ := by
  have := m.complementary
  exact this.symm  -- complement m.side₁ = m.side₂, i.e. m.side₁ = m.side₂ since complement = id

/-- The Bool Wantable has no fixed-point-free... wait, Bool's complement
IS fixed-point-free (not has no fixed point). -/
example (b : Bool) : Wantable.complement b ≠ b := by
  cases b <;> simp [Wantable.complement]

example : (Wantable.complement true : Bool) = false := rfl
example : Wantable.complement (Wantable.complement true : Bool) = true := by
  exact (Wantable.complement_involutive true)

/-- A specific meeting in the boolean Wantable. -/
def trueMeetsFalse : Meeting Bool where
  side₁ := true
  side₂ := false
  complementary := rfl

example : trueMeetsFalse.swap.swap = trueMeetsFalse := Meeting.swap_swap _

/-! ## Example 2 — The classical 2-outcome GPT (classical bit)

Build the n=2 classical GPT and verify concrete properties.
-/

abbrev TwoOutcome := Classical.V 2

/-- The "heads" state: vertex 0 of the 2-simplex. -/
def heads : TwoOutcome := Classical.vertex 2 0

/-- The "tails" state: vertex 1 of the 2-simplex. -/
def tails : TwoOutcome := Classical.vertex 2 1

example : heads ∈ (Classical.gpt 2).states := Classical.vertex_in_states 2 0
example : tails ∈ (Classical.gpt 2).states := Classical.vertex_in_states 2 1

/-- The "is heads" effect: project onto coordinate 0. -/
def isHeads : TwoOutcome →ₗ[ℝ] ℝ := Classical.proj 2 0

example : isHeads heads = 1 := by
  show Classical.proj 2 0 (Classical.vertex 2 0) = 1
  simp [Classical.proj_vertex]

example : isHeads tails = 0 := by
  show Classical.proj 2 0 (Classical.vertex 2 1) = 0
  simp [Classical.proj_vertex]

/-! ## Example 3 — Vertices of the 3-simplex are linearly independent

A direct instance of the abstract theorem on a concrete classical GPT. -/

example : LinearIndependent ℝ (Classical.vertex 3) :=
  Classical.vertex_linear_independent 3

/-! ## Example 4 — Composition: heads-of-coin-1 has no meeting with tails-of-coin-2

A direct instance of the structural no-cross-system meeting theorem. -/

example (m : Meeting (Bool ⊕ Bool)) :
    (∃ a b : Bool, m.side₁ = .inl a ∧ m.side₂ = .inl b) ∨
    (∃ a b : Bool, m.side₁ = .inr a ∧ m.side₂ = .inr b) :=
  Meeting.sum_no_cross m

/-! ## Example 5 — Group structure on Wantable transformations

PTrans Bool is a group; here we verify the identity and inverse laws
on a concrete element. -/

/-- The "swap" perspectival transformation on Bool (negation). -/
def boolSwap : PTrans Bool where
  toFun := not
  invFun := not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl
  resp_complement := by intro b; cases b <;> rfl

example : boolSwap * boolSwap = (1 : PTrans Bool) := by
  apply PTrans.ext
  intro b
  cases b <;> rfl

example : boolSwap⁻¹ = boolSwap := by
  apply PTrans.ext
  intro b
  cases b <;> rfl

/-! ## Example 6 — No linear cloner on classical vertices (chained theorem)

A concrete instance combining: (a) vertices are states, (b) distinct
vertices are distinguishable via coordinate projections, (c) the
no-cloning chain (`no_cloning_of_distinguishable`). -/

example (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    {S : Set (Classical.V n)}
    (h_vi : Classical.vertex n i ∈ S) (h_vj : Classical.vertex n j ∈ S)
    (h_sum : Classical.vertex n i + Classical.vertex n j ∈ S)
    {C : Classical.V n →ₗ[ℝ] Classical.V n ⊗[ℝ] Classical.V n}
    (hC : Perspectival.IsLinearCloner S C) : False :=
  Perspectival.Distinguish.no_cloning_of_distinguishable
    hC h_vi h_vj h_sum
    (Classical.vertex_in_states n i)
    (Classical.vertex_in_states n j)
    (Classical.vertices_distinguishable n i j hij)

/-! ## Example 7 — Same no-cloning result via the lin-indep route

The lin-indep formulation of no-cloning, applied to classical
vertices, gives the same conclusion through different machinery. -/

example (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    {S : Set (Classical.V n)}
    (h_vi : Classical.vertex n i ∈ S) (h_vj : Classical.vertex n j ∈ S)
    (h_sum : Classical.vertex n i + Classical.vertex n j ∈ S)
    {C : Classical.V n →ₗ[ℝ] Classical.V n ⊗[ℝ] Classical.V n}
    (hC : Perspectival.IsLinearCloner S C) : False :=
  Perspectival.no_cloning_of_linear_independent
    hC h_vi h_vj h_sum
    (Perspectival.Distinguish.distinguishable_imp_linear_independent
      (Classical.vertex_in_states n i)
      (Classical.vertex_in_states n j)
      (Classical.vertices_distinguishable n i j hij))

/-! ## Example 8 — Coe from PTrans to GPT.Transform

Demonstrates the Coe instance: any perspectival transformation on a
Wantable can be used directly as a GPT-transformation. -/

example {W : Type*} [Wantable W] [Fintype W] [DecidableEq W]
    (φ : PTrans W) :
    Perspectival.GPT.Transform (Perspectival.WantableGPT.gpt W)
                                (Perspectival.WantableGPT.gpt W) :=
  φ  -- Lean inserts the Coe.

/-! ## Example 9 — Boolean WantableGPT and complement-as-transformation

A concrete instance: the Wantable structure on `Bool` produces a
WantableGPT whose complement-action sends `vertex true` to
`vertex false` and vice versa. -/

example : Perspectival.GPT (Perspectival.WantableGPT.V Bool) :=
  Perspectival.WantableGPT.gpt Bool

example : Perspectival.WantableGPT.complementAction Bool
    (Perspectival.WantableGPT.vertex Bool true)
    = Perspectival.WantableGPT.vertex Bool false :=
  Perspectival.WantableGPT.complementAction_vertex Bool true

example : Perspectival.WantableGPT.complementAction Bool
    (Perspectival.WantableGPT.vertex Bool false)
    = Perspectival.WantableGPT.vertex Bool true := by
  have := Perspectival.WantableGPT.complementAction_vertex Bool false
  -- vertex (complement false) = vertex true since complement = not
  show Perspectival.WantableGPT.complementAction Bool _
       = Perspectival.WantableGPT.vertex Bool true
  rw [this]
  -- need: vertex (complement false) = vertex true, i.e. vertex (not false) = vertex true = vertex true. Trivial.
  rfl

/-! ## Example 10 — Hardy axioms on WantableGPT

Every WantableGPT (over a finite Wantable) satisfies Hardy Axiom 1
(probabilities in [0,1]) and Axiom 3 (subspaces). These follow from
the general theorems applied to the WantableGPT instance. -/

example {W : Type*} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.Hardy.Axiom1_Probabilities (Perspectival.WantableGPT.gpt W) :=
  Perspectival.Hardy.axiom1_holds _

example {W : Type*} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.Hardy.Axiom3_Subspaces (Perspectival.WantableGPT.gpt W) :=
  Perspectival.Hardy.axiom3_holds _

/-! ## Example 11 — Hardy axioms on Classical -/

example (n : ℕ) :
    Perspectival.Hardy.Axiom1_Probabilities (Perspectival.Classical.gpt n) :=
  Perspectival.Hardy.axiom1_holds _

example (n : ℕ) :
    Perspectival.Hardy.Axiom3_Subspaces (Perspectival.Classical.gpt n) :=
  Perspectival.Hardy.axiom3_holds _

/-! ## Example 12 — Concrete bridge instance: boolSwap as complementAction

On the boolean WantableGPT, the perspectival transformation `boolSwap`
(which is just `not`) lifts via `fromPTrans` to a linear map equal to
`complementAction`. The bridge is concretely computable. -/

example :
    (Perspectival.WantableGPT.fromPTrans Bool boolSwap).toLin
    = Perspectival.WantableGPT.complementAction Bool := by
  apply LinearMap.ext
  intro f
  funext b
  show f (boolSwap.invFun b) = f (Wantable.complement b)
  cases b <;> rfl

/-- On the boolean Wantable, `boolSwap` and `Perspectival.WantableGPT.complementPTrans Bool`
are equal as PTrans elements: both implement the negation. -/
example : boolSwap = Perspectival.WantableGPT.complementPTrans Bool := by
  apply PTrans.ext
  intro b
  cases b <;> rfl

/-- The two vertices of the boolean WantableGPT are distinguishable. -/
example : Perspectival.Hardy.Distinguishable
    (Perspectival.WantableGPT.gpt Bool)
    (Perspectival.WantableGPT.vertex Bool true)
    (Perspectival.WantableGPT.vertex Bool false) :=
  Perspectival.WantableGPT.vertices_distinguishable Bool true false (by decide)

/-- The vertices of the boolean WantableGPT are linearly independent. -/
example : LinearIndependent ℝ
    (fun b : Bool => Perspectival.WantableGPT.vertex Bool b) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype Bool

/-- The identity GPT-transformation on the boolean WantableGPT. -/
example : Perspectival.GPT.Transform
    (Perspectival.WantableGPT.gpt Bool)
    (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.GPT.Transform.id _

/-- Composition of the boolean WantableGPT's complement-Transform with
itself is the identity (at the Transform level). -/
example :
    (Perspectival.WantableGPT.complementTransform Bool *
     Perspectival.WantableGPT.complementTransform Bool : Perspectival.GPT.Transform _ _).toLin
    = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext b
  show f (Wantable.complement (Wantable.complement b)) = f b
  rw [Wantable.complement_involutive]

end Examples
end Perspectival
