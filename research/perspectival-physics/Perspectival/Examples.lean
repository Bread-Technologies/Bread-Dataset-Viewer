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
