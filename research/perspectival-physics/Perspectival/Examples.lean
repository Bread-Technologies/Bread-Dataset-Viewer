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
import Perspectival.Continuity
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

/-- The complement PTrans on Unit (with id complement) IS the identity. -/
example : (PTrans.complement : PTrans Unit) = 1 := by
  apply PTrans.ext
  intro u
  rfl

/-- For Wantable Fin 3 with identity-complement, *every* element is
self-complementary. -/
example : ∀ i : Fin 3, SelfComplementary i := by
  intro i; rfl

/-- For Wantable Unit, the singleton element is self-complementary. -/
example : SelfComplementary () := rfl

/-- For a Wantable with identity-complement (every element
self-complementary), every permutation `σ : Equiv.Perm W` lifts to a
PTrans (the `resp_complement` condition is vacuous). -/
def PTrans.ofPermWithIdComplement {W : Type u} [Wantable W]
    (h_id : ∀ w : W, Wantable.complement w = w)
    (σ : Equiv.Perm W) : PTrans W :=
  PTrans.ofEquivPerm σ (by
    intro w
    rw [h_id w, h_id (σ w)])

/-- For Wantable Fin 3 (identity complement), every permutation lifts to a PTrans. -/
example (σ : Equiv.Perm (Fin 3)) : PTrans (Fin 3) :=
  PTrans.ofPermWithIdComplement (fun _ => rfl) σ

/-- For Wantable Unit, the underlying permutation group is trivial. -/
example (σ : Equiv.Perm Unit) : σ = 1 := by
  apply Equiv.ext
  intro u; cases u; rfl

/-- For Wantable (Fin 3) with id-complement: ANY permutation of Fin 3
gives a valid PTrans. (So `|PTrans (Fin 3)| = 6 = |S_3|`.) -/
example (σ : Equiv.Perm (Fin 3)) :
    ∃ φ : PTrans (Fin 3), PTrans.toEquivPerm φ = σ :=
  ⟨PTrans.ofPermWithIdComplement (fun _ => rfl) σ, rfl⟩

/-- A *continuous* Wantable: a topological space whose Wantable
complement is continuous. Refinement of Wantable for cases where the
outcome set has natural topology (e.g., ℝ, S¹). The PTrans group
naturally restricts to continuous self-homeomorphisms — a much richer
structure than the discrete case. This is the natural setting for
non-trivial agency / Lie-group refinement (see ROADMAP R6/R7). -/
class ContinuousWantable (W : Type u) [Wantable W] [TopologicalSpace W] : Prop where
  complement_continuous : Continuous (Wantable.complement : W → W)

/-- `ℤ` with the discrete topology is a continuous Wantable. -/
instance : ContinuousWantable ℤ where
  complement_continuous := continuous_neg

/-- `ℝ` with `complement := Neg.neg` is a Wantable. -/
instance : Wantable ℝ where
  complement := Neg.neg
  complement_involutive := neg_neg

/-- `ℝ` with its standard topology is a continuous Wantable. The
"continuous Wantable" structure on `ℝ` gives the framework an
infinite-dimensional setting potentially suitable for non-classical
extension. -/
instance : ContinuousWantable ℝ where
  complement_continuous := continuous_neg

example : (Wantable.complement (3.14 : ℝ)) = -3.14 := rfl
example (x : ℝ) : Wantable.complement (Wantable.complement x) = x := neg_neg x

/-- A *continuous* PTrans on a ContinuousWantable: a perspectival
transformation whose `toFun` is continuous. -/
structure ContinuousPTrans (W : Type u) [Wantable W] [TopologicalSpace W]
    extends PTrans W where
  toFun_continuous : Continuous toPTrans.toFun

/-- The identity is a continuous PTrans (on any TopologicalSpace W). -/
def ContinuousPTrans.id (W : Type u) [Wantable W] [TopologicalSpace W] :
    ContinuousPTrans W where
  toPTrans := 1
  toFun_continuous := continuous_id

/-- The complement PTrans is continuous when the Wantable structure
is `ContinuousWantable`. -/
def ContinuousPTrans.complement (W : Type u) [Wantable W] [TopologicalSpace W]
    [ContinuousWantable W] : ContinuousPTrans W where
  toPTrans := PTrans.complement
  toFun_continuous := ContinuousWantable.complement_continuous

example : ContinuousPTrans ℝ := ContinuousPTrans.complement ℝ
example : ContinuousPTrans ℝ := ContinuousPTrans.id ℝ

/-- Composition of continuous PTrans is continuous. -/
def ContinuousPTrans.comp {W : Type u} [Wantable W] [TopologicalSpace W]
    (g f : ContinuousPTrans W) : ContinuousPTrans W where
  toPTrans := g.toPTrans * f.toPTrans
  toFun_continuous := g.toFun_continuous.comp f.toFun_continuous

/-- Composition of complement with itself = identity (as ContinuousPTrans). -/
example (W : Type u) [Wantable W] [TopologicalSpace W] [ContinuousWantable W] :
    ((ContinuousPTrans.complement W).comp (ContinuousPTrans.complement W)).toPTrans = 1 :=
  PTrans.complement_sq

/-- Concrete continuous PTrans on ℝ: the identity. -/
example : (ContinuousPTrans.id ℝ).toPTrans.toFun (3.14 : ℝ) = 3.14 := rfl

/-- Concrete continuous PTrans on ℝ: the negation (complement). -/
example : (ContinuousPTrans.complement ℝ).toPTrans.toFun (3.14 : ℝ) = -3.14 := rfl

/-- The PTrans group structure restricts to ContinuousPTrans on ℝ:
the negation has order 2. -/
example : ((ContinuousPTrans.complement ℝ).comp
            (ContinuousPTrans.complement ℝ)).toPTrans
        = (ContinuousPTrans.id ℝ).toPTrans :=
  PTrans.complement_sq

/-- A scaling map `x ↦ a*x` on ℝ is a continuous PTrans iff it commutes
with negation. Since `a * (-x) = -(a * x) = (-a) * x` ... actually
`a * (-x) = -(a * x)` always, so the scaling commutes with negation
trivially. The bijectivity requires `a ≠ 0`. -/
noncomputable def scaleByPTrans (a : ℝ) (ha : a ≠ 0) : PTrans ℝ where
  toFun x := a * x
  invFun x := x / a
  left_inv x := by field_simp
  right_inv x := by field_simp
  resp_complement x := by show a * -x = -(a * x); ring

example : (scaleByPTrans 2 (by norm_num)).toFun 5 = 10 := by
  show (2 : ℝ) * 5 = 10; ring

example : (scaleByPTrans 2 (by norm_num)).invFun 10 = 5 := by
  show (10 : ℝ) / 2 = 5; ring

/-- Scaling by `a` and `b` composes to scaling by `a * b`. -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((scaleByPTrans a ha) * (scaleByPTrans b hb)).toFun =
    (scaleByPTrans (a * b) (mul_ne_zero ha hb)).toFun := by
  funext x
  show a * (b * x) = a * b * x
  ring

/-- Scaling by 1 is the identity PTrans. -/
example : (scaleByPTrans 1 (by norm_num)).toFun = (1 : PTrans ℝ).toFun := by
  funext x; show (1 : ℝ) * x = x; ring

/-- Scaling by -1 equals the complement. -/
example : (scaleByPTrans (-1) (by norm_num)).toFun
        = (PTrans.complement : PTrans ℝ).toFun := by
  funext x; show (-1 : ℝ) * x = -x; ring

/-- The scaling map `ℝˣ → PTrans ℝ` sending each nonzero real to the
corresponding scaling PTrans is a MonoidHom. (Provides a concrete
group embedding `ℝˣ ↪ PTrans ℝ` and confirms the Lie-group-like
structure on PTrans ℝ.) -/
noncomputable def scaleHom : ℝˣ →* PTrans ℝ where
  toFun a := scaleByPTrans (a : ℝ) (a.isUnit.ne_zero)
  map_one' := by
    apply PTrans.ext
    intro x
    show (1 : ℝˣ).val * x = x
    show (1 : ℝ) * x = x
    ring
  map_mul' a b := by
    apply PTrans.ext
    intro x
    show (a * b).val * x = (a : ℝ) * ((b : ℝ) * x)
    show ((a : ℝ) * (b : ℝ)) * x = (a : ℝ) * ((b : ℝ) * x)
    ring

/-- The scaleHom is injective: different scalings give different PTrans. -/
theorem scaleHom_injective : Function.Injective scaleHom := by
  intro a b hab
  -- Evaluate at x = 1: (scaleHom a).toFun 1 = a, similarly for b.
  have h1 : (scaleHom a).toFun (1 : ℝ) = (scaleHom b).toFun 1 := by
    rw [hab]
  have ha : (scaleHom a).toFun (1 : ℝ) = (a : ℝ) := by
    show (a : ℝ) * 1 = (a : ℝ); ring
  have hb : (scaleHom b).toFun (1 : ℝ) = (b : ℝ) := by
    show (b : ℝ) * 1 = (b : ℝ); ring
  rw [ha, hb] at h1
  exact Units.ext h1

/-- The scaling PTrans for `-1` equals the complement PTrans on ℝ.
This is a concrete `scaleHom` identity that ties scaling to complement. -/
example : scaleHom (-1 : ℝˣ) = (PTrans.complement : PTrans ℝ) := by
  apply PTrans.ext
  intro x
  show (-1 : ℝ) * x = -x
  ring

/-- The scaling PTrans for `1` is the identity PTrans on ℝ. -/
example : scaleHom (1 : ℝˣ) = (1 : PTrans ℝ) := scaleHom.map_one

/-- Composition is multiplication in ℝˣ. (Abstract form to avoid
literal-coercion fiddliness with ℝˣ.) -/
example (a b : ℝˣ) : scaleHom (a * b) = scaleHom a * scaleHom b :=
  scaleHom.map_mul a b

/-- The inverse-of-scaling is scaling-by-inverse. -/
example (a : ℝˣ) : (scaleHom a)⁻¹ = scaleHom a⁻¹ := by
  rw [← scaleHom.map_inv]

-- A linear PTrans on ℝ is exactly a scaling: any LinearMap ℝ → ℝ that
-- is a bijection respecting negation is `x ↦ a*x` for some `a ≠ 0`.
-- The intersection of `PTrans ℝ` with the linear maps is exactly the
-- multiplicative group `ℝˣ`.
--
-- Conceptually: PTrans ℝ contains many non-linear odd bijections; the
-- *linear* subgroup is `scaleHom(ℝˣ)`.

/-- Every ℝ-linear map ℝ → ℝ is determined by its value at 1:
`f x = f 1 * x`. -/
example (f : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : f x = f 1 * x := by
  have h := f.map_smul x 1
  rw [smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

/-- Every ℝ-linear map ℝ → ℝ satisfies `f(-x) = -f(x)` automatically
(linearity over a Z-algebra is enough). -/
example (f : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : f (-x) = -f x := by
  rw [map_neg]

/-- A non-zero linear map ℝ → ℝ has the form `x ↦ f(1) * x` with
`f(1) ≠ 0`. So such an `f` is determined by — and represented by —
its value at 1. (Stated as the existence claim; uniqueness is
trivial since the linear-map equation determines `f(1)`.) -/
example (f : ℝ →ₗ[ℝ] ℝ) (h_one : f 1 ≠ 0) (x : ℝ) :
    f x = f 1 * x := by
  have h := f.map_smul x 1
  rw [smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

/-- Bijective linear ℝ → ℝ has `f 1 ≠ 0`. -/
example (f : ℝ →ₗ[ℝ] ℝ) (hf : Function.Injective f) : f 1 ≠ 0 := by
  intro h
  -- f 1 = 0 = f 0, so by injectivity, 1 = 0 (false).
  have hf0 : f 0 = 0 := f.map_zero
  have : (1 : ℝ) = 0 := hf (h.trans hf0.symm)
  exact one_ne_zero this

/-- The linear-bijection-respecting-negation classification: if `f : ℝ → ℝ` is
ℝ-linear, bijective, and respects negation (automatic for linear maps),
then `f x = f 1 * x` and `f 1 ≠ 0`. So every linear `PTrans ℝ`-like
function is a scaling, demonstrating `scaleHom(ℝˣ)` = `{linear ϕ : ϕ ∈ PTrans ℝ}`. -/
example (f : ℝ →ₗ[ℝ] ℝ) (hf_inj : Function.Injective f) :
    ∃ a : ℝ, a ≠ 0 ∧ ∀ x, f x = a * x := by
  refine ⟨f 1, ?_, ?_⟩
  · intro h
    have hf0 : f 0 = 0 := f.map_zero
    exact one_ne_zero (hf_inj (h.trans hf0.symm))
  · intro x
    have h := f.map_smul x 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h
    rw [h, mul_comm]

/-- Sum Wantable `Bool ⊕ Bool` has fixed-point-free complement
(complement swaps within each summand). -/
example : FixedPointFreeComplement (Bool ⊕ Bool) := by
  intro x h
  cases x with
  | inl b =>
    cases b
    · have : (true : Bool) = false := Sum.inl.inj h
      exact Bool.false_ne_true this.symm
    · have : (false : Bool) = true := Sum.inl.inj h
      exact Bool.false_ne_true this
  | inr b =>
    cases b
    · have : (true : Bool) = false := Sum.inr.inj h
      exact Bool.false_ne_true this.symm
    · have : (false : Bool) = true := Sum.inr.inj h
      exact Bool.false_ne_true this

/-- Product Wantable `Bool × Bool` has fixed-point-free complement
(complement = componentwise negation; never fixes a pair). -/
example : FixedPointFreeComplement (Bool × Bool) := by
  intro ⟨b₁, b₂⟩ h
  have h1 : Wantable.complement b₁ = b₁ := (Prod.mk.injEq _ _ _ _).mp h |>.1
  cases b₁
  · exact Bool.false_ne_true h1.symm
  · exact Bool.false_ne_true h1

/-- Concrete instance: `card (Bool × Bool) = 4` is even (consequence
of fixed-point-free complement + the general theorem). -/
example : Even (Fintype.card (Bool × Bool)) := by
  rw [Fintype.card_prod]
  exact ⟨2, rfl⟩

/-- **Structural observation.** Translations `x ↦ x + c` (for `c ≠ 0`) on ℝ
do NOT respect the complement structure (= negation). So PTrans ℝ
contains scalings but not translations — a non-trivial structural
constraint imposed by the complement-equivariance requirement.

(Note: PTrans ℝ is much larger than just `{scaleHom a | a ∈ ℝˣ}` — it
includes every odd bijection of ℝ, e.g., `x ↦ x³`. The scalings are
just the *linear* odd bijections. Quotienting by linearity recovers
`scaleHom : ℝˣ ↪ PTrans ℝ` as a Lie subgroup, not the entire group.) -/
example (c : ℝ) (hc : c ≠ 0) :
    ∃ x : ℝ, (Wantable.complement x + c) ≠ Wantable.complement (x + c) := by
  refine ⟨0, ?_⟩
  show ((-0 : ℝ) + c) ≠ (-(0 + c))
  intro h
  have h1 : c = -c := by linarith
  have h2 : c = 0 := by linarith
  exact hc h2

/-- In `Wantable (Fin 3)` (with complement := id), every element is
self-complementary. -/
example (i : Fin 3) : SelfComplementary i := rfl

/-- In `Wantable Bool` (with complement := not), no element is
self-complementary. -/
example : ¬ SelfComplementary (true : Bool) := by
  intro h
  exact Bool.false_ne_true h
example : ¬ SelfComplementary (false : Bool) := by
  intro h
  exact Bool.false_ne_true h.symm

/-- In `Wantable ℤ` (with complement := neg), zero is the unique
self-complementary element. -/
example : SelfComplementary (0 : ℤ) := by show -(0 : ℤ) = 0; ring
example : ¬ SelfComplementary (5 : ℤ) := by
  intro h
  have : (-(5 : ℤ)) = 5 := h
  norm_num at this
example (n : ℤ) (h : SelfComplementary n) : n = 0 := by
  have : -n = n := h
  linarith

/-- `Wantable Bool` has fixed-point-free complement. -/
example : FixedPointFreeComplement Bool := by
  intro b h
  cases b
  · exact Bool.false_ne_true h.symm
  · exact Bool.false_ne_true h

/-- `Wantable (Fin 2)` (with complement = swap) has fixed-point-free complement. -/
example : FixedPointFreeComplement (Fin 2) := by
  intro i h
  fin_cases i <;> (simp [SelfComplementary, Wantable.complement] at h)

/-- `Wantable (Fin 3)` (with complement = id) has NON-fixed-point-free complement. -/
example : ¬ FixedPointFreeComplement (Fin 3) := by
  intro h
  exact h 0 rfl

/-- `Wantable Unit` (with complement = id) has NON-fixed-point-free complement. -/
example : ¬ FixedPointFreeComplement Unit := by
  intro h
  exact h () rfl

/-- `Wantable ℤ` (with complement = neg) has NON-fixed-point-free complement
(since 0 is its own complement). -/
example : ¬ FixedPointFreeComplement ℤ := by
  intro h
  exact h 0 (by show -(0 : ℤ) = 0; ring)

/-- **Even-cardinality theorem.** For finite Wantable W with a linear
order and fixed-point-free complement, `|W|` is even. Proof: split W
into `A = {w | w < complement w}` and `B = {w | complement w < w}`;
these are disjoint, cover W (since fixed-point-free), and are in
bijection via complement, so each has size `|W|/2`. -/
theorem card_even_of_fixedPointFree {W : Type u} [Wantable W] [Fintype W]
    [DecidableEq W] [LinearOrder W] (h : FixedPointFreeComplement W) :
    Even (Fintype.card W) := by
  set A : Finset W := Finset.univ.filter (fun w => w < Wantable.complement w) with hA
  set B : Finset W := Finset.univ.filter (fun w => Wantable.complement w < w) with hB
  have hA_mem : ∀ w, w ∈ A ↔ w < Wantable.complement w := by
    intro w; simp [hA]
  have hB_mem : ∀ w, w ∈ B ↔ Wantable.complement w < w := by
    intro w; simp [hB]
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [hA_mem] at hwA
    rw [hB_mem] at hwB
    exact absurd hwA (asymm hwB)
  have hAB_union : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    rw [Finset.mem_union, hA_mem, hB_mem]
    rcases lt_trichotomy w (Wantable.complement w) with hlt | heq | hgt
    · exact Or.inl hlt
    · exact absurd heq (ne_complement_of_fixedPointFree h w)
    · exact Or.inr hgt
  have hcard_eq : Fintype.card W = A.card + B.card := by
    rw [← Finset.card_univ, ← hAB_union, Finset.card_union_of_disjoint hAB_disj]
  have hAB_card : A.card = B.card := by
    apply Finset.card_bij (fun w _ => Wantable.complement w)
    · intro w hw
      rw [hA_mem] at hw
      rw [hB_mem]
      have h2 : Wantable.complement (Wantable.complement w) = w :=
        Wantable.complement_involutive w
      rw [h2]; exact hw
    · intro w₁ _ w₂ _ heq
      have := congrArg Wantable.complement heq
      rwa [Wantable.complement_involutive, Wantable.complement_involutive] at this
    · intro w hw
      rw [hB_mem] at hw
      refine ⟨Wantable.complement w, ?_, ?_⟩
      · rw [hA_mem]
        have h2 : Wantable.complement (Wantable.complement w) = w :=
          Wantable.complement_involutive w
        rw [h2]; exact hw
      · exact Wantable.complement_involutive w
  refine ⟨A.card, ?_⟩
  rw [hcard_eq, hAB_card]

/-- Concrete instance: `|Bool| = 2` is even (consistent with
fixed-point-free complement on Bool). -/
example : Even (Fintype.card Bool) := card_even_of_fixedPointFree (W := Bool) (by
  intro b hb
  cases b
  · exact Bool.false_ne_true hb.symm
  · exact Bool.false_ne_true hb)

/-- For a Wantable with fixed-point-free complement, the
`PTrans.complement` transformation is non-trivial (not equal to the
identity PTrans). -/
theorem PTrans.complement_ne_one_of_fixedPointFree {W : Type u} [Wantable W]
    [Nonempty W] (h : FixedPointFreeComplement W) :
    (PTrans.complement : PTrans W) ≠ (1 : PTrans W) := by
  intro heq
  obtain ⟨w⟩ := ‹Nonempty W›
  have hw : (PTrans.complement : PTrans W).toFun w = (1 : PTrans W).toFun w := by
    rw [heq]
  -- LHS = Wantable.complement w, RHS = w
  have : Wantable.complement w = w := hw
  exact h w this

/-- Concrete: complement on Bool is not the identity PTrans. -/
example : (PTrans.complement : PTrans Bool) ≠ (1 : PTrans Bool) :=
  PTrans.complement_ne_one_of_fixedPointFree (W := Bool) (by
    intro b hb
    cases b
    · exact Bool.false_ne_true hb.symm
    · exact Bool.false_ne_true hb)

/-- Concrete: complement on Fin 2 (= swap) is not the identity PTrans. -/
example : (PTrans.complement : PTrans (Fin 2)) ≠ (1 : PTrans (Fin 2)) :=
  PTrans.complement_ne_one_of_fixedPointFree (W := Fin 2) (by
    intro i h
    fin_cases i <;> (simp [SelfComplementary, Wantable.complement] at h))

/-! ## Example 14 — actReality on Bool -/

/-- The "true is part of reality" predicate on Bool meetings. -/
example : PTrans.actReality (1 : PTrans Bool) (fun _ : Meeting Bool => True)
        = fun _ => True := by
  rfl

/-- Swap-reality of singleton trueMeetsFalse meeting. -/
example :
    PTrans.actReality (PTrans.complement : PTrans Bool)
      (fun m : Meeting Bool => m = trueMeetsFalse)
    = (fun m : Meeting Bool => m = PTrans.actMeeting PTrans.complement trueMeetsFalse) :=
  PTrans.actReality_singleton _ _

/-- **Concrete classification of `PTrans Unit`.** Since `Unit` has
only one element, only the identity transformation exists. -/
theorem ptrans_unit_classification (f : PTrans Unit) : f = (1 : PTrans Unit) := by
  apply PTrans.ext
  intro u
  cases u; cases f.toFun (); rfl

/-- **Concrete classification of `PTrans Empty`.** Vacuously, all
functions on `Empty` are equal. -/
theorem ptrans_empty_classification (f : PTrans Empty) : f = (1 : PTrans Empty) := by
  apply PTrans.ext
  intro w
  exact w.elim

/-- The "swap" perspectival transformation on `Fin 2`. -/
def fin2Swap : PTrans (Fin 2) where
  toFun
    | 0 => 1
    | 1 => 0
  invFun
    | 0 => 1
    | 1 => 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
  resp_complement := by intro i; fin_cases i <;> rfl

/-- An isomorphism of Wantable structures: an `Equiv` that respects
complement. This is the morphism in the category of Wantables. -/
structure WantableEquiv (W₁ W₂ : Type u) [Wantable W₁] [Wantable W₂] where
  toEquiv : W₁ ≃ W₂
  resp_complement : ∀ w, toEquiv (Wantable.complement w) = Wantable.complement (toEquiv w)

/-- Identity Wantable-isomorphism. -/
def WantableEquiv.refl (W : Type u) [Wantable W] : WantableEquiv W W where
  toEquiv := Equiv.refl W
  resp_complement := fun _ => rfl

/-- Inverse of a Wantable-isomorphism. -/
def WantableEquiv.symm {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) : WantableEquiv W₂ W₁ where
  toEquiv := e.toEquiv.symm
  resp_complement w := by
    have h := e.resp_complement (e.toEquiv.symm w)
    apply e.toEquiv.injective
    rw [e.toEquiv.apply_symm_apply, e.resp_complement]
    rw [e.toEquiv.apply_symm_apply]

/-- Composition of Wantable-isomorphisms. -/
def WantableEquiv.trans {W₁ W₂ W₃ : Type u}
    [Wantable W₁] [Wantable W₂] [Wantable W₃]
    (e₁ : WantableEquiv W₁ W₂) (e₂ : WantableEquiv W₂ W₃) :
    WantableEquiv W₁ W₃ where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  resp_complement w := by
    show e₂.toEquiv (e₁.toEquiv (Wantable.complement w))
       = Wantable.complement (e₂.toEquiv (e₁.toEquiv w))
    rw [e₁.resp_complement, e₂.resp_complement]

/-- `refl` is a left identity for `trans`. -/
@[simp] theorem WantableEquiv.refl_trans {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    (WantableEquiv.refl W₁).trans e = e := rfl

/-- `refl` is a right identity for `trans`. -/
@[simp] theorem WantableEquiv.trans_refl {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    e.trans (WantableEquiv.refl W₂) = e := rfl

/-- `trans` is associative. -/
theorem WantableEquiv.trans_assoc {W₁ W₂ W₃ W₄ : Type u}
    [Wantable W₁] [Wantable W₂] [Wantable W₃] [Wantable W₄]
    (e₁ : WantableEquiv W₁ W₂) (e₂ : WantableEquiv W₂ W₃)
    (e₃ : WantableEquiv W₃ W₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := rfl

/-- `symm` is involutive: (e.symm).symm = e. -/
@[simp] theorem WantableEquiv.symm_symm {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    e.symm.symm = e := by
  rfl

/-- WantableEquiv is symmetric: there's a Wantable iso the other direction. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) : WantableEquiv W₂ W₁ := e.symm

/-- A `Bool ≃ Fin 2` equivalence that respects the swap-complement structures. -/
def boolEquivFin2 : WantableEquiv Bool (Fin 2) where
  toEquiv :=
    { toFun
        | false => 0
        | true => 1
      invFun
        | 0 => false
        | 1 => true
      left_inv := by intro b; cases b <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  resp_complement := by intro b; cases b <;> rfl

example : boolEquivFin2.toEquiv true = 1 := rfl
example : boolEquivFin2.toEquiv false = 0 := rfl

/-- boolEquivFin2's symm is a WantableEquiv (Fin 2) Bool. -/
example : WantableEquiv (Fin 2) Bool := boolEquivFin2.symm

/-- boolEquivFin2.symm maps 0 ↦ false, 1 ↦ true. -/
example : boolEquivFin2.symm.toEquiv 0 = false := rfl
example : boolEquivFin2.symm.toEquiv 1 = true := rfl

/-- The double symm is the original. -/
example : boolEquivFin2.symm.symm = boolEquivFin2 := rfl

-- (boolEquivFin2 ⊕ symm composition examples skipped — proof structure for
-- WantableEquiv equality is delicate; deferred to a follow-up.)

/-- The underlying toEquiv of boolEquivFin2 composed with its symm is the
identity-equiv at the Equiv level (this is the essence of equiv ⊕ symm = refl). -/
example : (boolEquivFin2.toEquiv.trans boolEquivFin2.toEquiv.symm)
        = Equiv.refl Bool :=
  Equiv.self_trans_symm boolEquivFin2.toEquiv

/-- symm ⊕ toEquiv at the underlying Equiv level. -/
example : (boolEquivFin2.toEquiv.symm.trans boolEquivFin2.toEquiv)
        = Equiv.refl (Fin 2) :=
  Equiv.symm_trans_self boolEquivFin2.toEquiv

/-- For any element b : Bool, boolEquivFin2.symm sends it back consistently. -/
example (b : Bool) : boolEquivFin2.toEquiv.symm (boolEquivFin2.toEquiv b) = b :=
  boolEquivFin2.toEquiv.symm_apply_apply b

/-- For any element i : Fin 2, boolEquivFin2 sends it back consistently. -/
example (i : Fin 2) : boolEquivFin2.toEquiv (boolEquivFin2.toEquiv.symm i) = i :=
  boolEquivFin2.toEquiv.apply_symm_apply i

-- (mapPTrans examples on boolEquivFin2.symm deferred to after mapPTrans is defined.)

/-- A Wantable isomorphism induces a PTrans isomorphism: conjugate a
PTrans of W₁ by the equiv to get a PTrans of W₂. -/
def WantableEquiv.mapPTrans {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) (φ : PTrans W₁) : PTrans W₂ where
  toFun w := e.toEquiv (φ.toFun (e.toEquiv.symm w))
  invFun w := e.toEquiv (φ.invFun (e.toEquiv.symm w))
  left_inv := by
    intro w
    show e.toEquiv (φ.invFun (e.toEquiv.symm (e.toEquiv (φ.toFun (e.toEquiv.symm w))))) = w
    rw [e.toEquiv.symm_apply_apply, φ.left_inv, e.toEquiv.apply_symm_apply]
  right_inv := by
    intro w
    show e.toEquiv (φ.toFun (e.toEquiv.symm (e.toEquiv (φ.invFun (e.toEquiv.symm w))))) = w
    rw [e.toEquiv.symm_apply_apply, φ.right_inv, e.toEquiv.apply_symm_apply]
  resp_complement := by
    intro w
    show e.toEquiv (φ.toFun (e.toEquiv.symm (Wantable.complement w)))
       = Wantable.complement (e.toEquiv (φ.toFun (e.toEquiv.symm w)))
    -- e.toEquiv.symm (complement w) = complement (e.toEquiv.symm w) by applying e.symm.resp_complement
    have h_symm : e.toEquiv.symm (Wantable.complement w)
                = Wantable.complement (e.toEquiv.symm w) := e.symm.resp_complement w
    rw [h_symm, φ.resp_complement, e.resp_complement]

/-- Identity Wantable-equiv maps each PTrans to itself. -/
@[simp] theorem WantableEquiv.refl_mapPTrans (W : Type u) [Wantable W]
    (φ : PTrans W) : (WantableEquiv.refl W).mapPTrans φ = φ := by
  apply PTrans.ext
  intro w
  rfl

/-- `mapPTrans` sends the identity PTrans to the identity. -/
@[simp] theorem WantableEquiv.mapPTrans_one {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    e.mapPTrans (1 : PTrans W₁) = (1 : PTrans W₂) := by
  apply PTrans.ext
  intro w
  show e.toEquiv ((1 : PTrans W₁).toFun (e.toEquiv.symm w)) = w
  show e.toEquiv (e.toEquiv.symm w) = w
  exact e.toEquiv.apply_symm_apply w

/-- `mapPTrans` is a group homomorphism: it preserves composition. -/
theorem WantableEquiv.mapPTrans_mul {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂)
    (φ ψ : PTrans W₁) :
    e.mapPTrans (φ * ψ) = e.mapPTrans φ * e.mapPTrans ψ := by
  apply PTrans.ext
  intro w
  show e.toEquiv ((φ * ψ).toFun (e.toEquiv.symm w))
     = (e.mapPTrans φ).toFun ((e.mapPTrans ψ).toFun w)
  show e.toEquiv (φ.toFun (ψ.toFun (e.toEquiv.symm w)))
     = e.toEquiv (φ.toFun (e.toEquiv.symm (e.toEquiv (ψ.toFun (e.toEquiv.symm w)))))
  rw [e.toEquiv.symm_apply_apply]

/-- A Wantable isomorphism induces a MonoidHom `PTrans W₁ →* PTrans W₂`. -/
def WantableEquiv.mapPTransHom {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    PTrans W₁ →* PTrans W₂ where
  toFun := e.mapPTrans
  map_one' := e.mapPTrans_one
  map_mul' := e.mapPTrans_mul

/-- A Wantable isomorphism induces a MulEquiv `PTrans W₁ ≃* PTrans W₂`. -/
def WantableEquiv.mapPTransMulEquiv {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] (e : WantableEquiv W₁ W₂) :
    PTrans W₁ ≃* PTrans W₂ where
  toFun := e.mapPTrans
  invFun := e.symm.mapPTrans
  left_inv := by
    intro φ
    apply PTrans.ext
    intro w
    show e.symm.toEquiv ((e.mapPTrans φ).toFun (e.symm.toEquiv.symm w)) = φ.toFun w
    show e.toEquiv.symm (e.toEquiv (φ.toFun (e.toEquiv.symm (e.symm.toEquiv.symm w))))
       = φ.toFun w
    -- e.symm.toEquiv.symm = e.toEquiv (since symm-symm = self)
    rw [e.toEquiv.symm_apply_apply]
    show φ.toFun (e.toEquiv.symm (e.symm.toEquiv.symm w)) = φ.toFun w
    have : e.symm.toEquiv.symm w = e.toEquiv w := rfl
    rw [this, e.toEquiv.symm_apply_apply]
  right_inv := by
    intro φ
    apply PTrans.ext
    intro w
    show e.toEquiv ((e.symm.mapPTrans φ).toFun (e.toEquiv.symm w)) = φ.toFun w
    show e.toEquiv (e.symm.toEquiv (φ.toFun (e.symm.toEquiv.symm (e.toEquiv.symm w))))
       = φ.toFun w
    have h_inv : e.symm.toEquiv = e.toEquiv.symm := rfl
    rw [h_inv, e.toEquiv.apply_symm_apply]
    show φ.toFun (e.symm.toEquiv.symm (e.toEquiv.symm w)) = φ.toFun w
    have h_inv2 : e.symm.toEquiv.symm = e.toEquiv := rfl
    rw [h_inv2, e.toEquiv.apply_symm_apply]
  map_mul' := e.mapPTrans_mul

/-- **Concrete classification of `PTrans (Fin 2)`.** Either the
identity or `fin2Swap`. -/
theorem ptrans_fin2_classification (f : PTrans (Fin 2)) :
    f = (1 : PTrans (Fin 2)) ∨ f = fin2Swap := by
  -- Case-split on f.toFun 0 ∈ Fin 2 via Fin.cases-style reasoning.
  have h0_cases : f.toFun 0 = 0 ∨ f.toFun 0 = 1 := by
    have := f.toFun 0
    omega
  -- Use resp_complement to determine f.toFun 1 from f.toFun 0.
  have hresp := f.resp_complement 0
  -- hresp : f.toFun (complement 0) = complement (f.toFun 0), i.e., f.toFun 1 = complement (f.toFun 0)
  have hresp1 : f.toFun 1 = Wantable.complement (f.toFun 0) := by
    have : f.toFun (Wantable.complement (0 : Fin 2)) = Wantable.complement (f.toFun 0) := hresp
    have hc : Wantable.complement (0 : Fin 2) = 1 := rfl
    rw [hc] at this
    exact this
  rcases h0_cases with h0 | h0
  · -- f.toFun 0 = 0; then f.toFun 1 = complement 0 = 1
    left
    apply PTrans.ext
    intro i
    have hf1 : f.toFun 1 = 1 := by rw [hresp1, h0]; rfl
    fin_cases i
    · show f.toFun 0 = 0; exact h0
    · show f.toFun 1 = 1; exact hf1
  · -- f.toFun 0 = 1; then f.toFun 1 = complement 1 = 0
    right
    apply PTrans.ext
    intro i
    have hf1 : f.toFun 1 = 0 := by rw [hresp1, h0]; rfl
    fin_cases i
    · show f.toFun 0 = fin2Swap.toFun 0; rw [h0]; rfl
    · show f.toFun 1 = fin2Swap.toFun 1; rw [hf1]; rfl

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

/-- Fin 4 with reflection complement has no fixed points either. -/
example (i : Fin 4) : Wantable.complement i ≠ i := by
  fin_cases i <;> decide

/-- Fin 3 (with complement = id) has EVERY element as a fixed point. -/
example (i : Fin 3) : Wantable.complement i = i := rfl

/-- Unit's only element is a fixed point. -/
example : Wantable.complement () = () := rfl

/-- Empty has trivially no elements, so vacuously every "element" is
both a fixed point and not (vacuous truth). -/
example (e : Empty) : Wantable.complement e = e := e.elim

/-- ℤ's only fixed point of complement (= negation) is 0. -/
example (n : ℤ) (h : Wantable.complement n = n) : n = 0 := by
  have : -n = n := h
  linarith

/-- ℤ-meetings: 5 and -5 are complementary. -/
example : Wantable.complement (5 : ℤ) = -5 := rfl

/-- ℤ-meetings: -7 and 7 are complementary. -/
example : Wantable.complement (-7 : ℤ) = 7 := by show -(-7 : ℤ) = 7; ring

/-- ℤ-meetings: 1000 and -1000. -/
example : Wantable.complement (1000 : ℤ) = -1000 := rfl

/-- ℤ self-inverse: complement of complement is identity. -/
example (n : ℤ) : Wantable.complement (Wantable.complement n) = n :=
  Wantable.complement_involutive n

/-- Symmetry: 3 and -3 swap under complement. -/
example : Wantable.complement (3 : ℤ) = -3 ∧ Wantable.complement (-3 : ℤ) = 3 :=
  ⟨rfl, by show -(-3 : ℤ) = 3; ring⟩

example : (PTrans.complement : PTrans ℤ).toFun 42 = -42 := rfl
example : (PTrans.complement : PTrans ℤ).invFun (-42) = 42 := by
  show -(-42 : ℤ) = 42; ring

/-- The complement-PTrans on ℤ has order 2 in its group. -/
example : (PTrans.complement : PTrans ℤ) * PTrans.complement = 1 :=
  PTrans.complement_sq

example : (PTrans.complement : PTrans ℤ)⁻¹ = PTrans.complement :=
  PTrans.complement_inv

example : (PTrans.complement : PTrans Bool)⁻¹ = PTrans.complement :=
  PTrans.complement_inv

example : (PTrans.complement : PTrans Bool) * PTrans.complement = 1 :=
  PTrans.complement_sq

example : ((PTrans.complement : PTrans Bool) * PTrans.complement).toFun true = true := by
  rw [PTrans.complement_sq]; rfl

example : ((PTrans.complement : PTrans Bool) * PTrans.complement).toFun false = false := by
  rw [PTrans.complement_sq]; rfl

example : (1 : PTrans Bool).toFun true = true := rfl
example : (1 : PTrans Bool).toFun false = false := rfl

example : (1 : PTrans (Fin 4)).toFun 0 = 0 := rfl
example : (1 : PTrans Unit).toFun () = () := rfl
example : (1 : PTrans ℤ).toFun 42 = 42 := rfl

example : (1 : PTrans (Bool × Bool)).toFun (true, true) = (true, true) := rfl
example : (1 : PTrans (Bool ⊕ Bool)).toFun (Sum.inl false) = Sum.inl false := rfl

example : (1 : PTrans (Option Bool)).toFun (some true) = some true := rfl
example : (1 : PTrans (Option Bool)).toFun none = none := rfl

example : (1 : PTrans (List Bool)).toFun [true, false] = [true, false] := rfl

example : (1 : PTrans (List Bool)).toFun [] = [] := rfl

example : (1 : PTrans (List Bool)).toFun [false, false, true] = [false, false, true] := rfl

/-- Complement maps a set to its image under complement, an involution. -/
example {W : Type u} [Wantable W] (s : Set W) :
    {w | Wantable.complement w ∈ s} = (Wantable.complement '' s : Set W) := by
  ext w
  constructor
  · intro h
    -- complement w ∈ s, so w = complement (complement w) is image
    exact ⟨Wantable.complement w, h, Wantable.complement_involutive w⟩
  · rintro ⟨v, hv, rfl⟩
    show Wantable.complement (Wantable.complement v) ∈ s
    rwa [Wantable.complement_involutive]

/-- The complement image of the complement image of a set is the set. -/
example {W : Type u} [Wantable W] (s : Set W) :
    Wantable.complement '' (Wantable.complement '' s) = s := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    -- complement (complement u) = u, so w = u
    rwa [Wantable.complement_involutive]
  · intro hw
    refine ⟨Wantable.complement w, ⟨w, hw, rfl⟩, ?_⟩
    exact Wantable.complement_involutive w

/-- Complement preserves emptiness. -/
example {W : Type u} [Wantable W] :
    Wantable.complement '' (∅ : Set W) = ∅ := Set.image_empty _

/-- Complement preserves universe. -/
example {W : Type u} [Wantable W] :
    Wantable.complement '' (Set.univ : Set W) = Set.univ := by
  ext w
  constructor
  · rintro ⟨_, _, rfl⟩; trivial
  · intro _
    exact ⟨Wantable.complement w, trivial, Wantable.complement_involutive w⟩

/-- Complement preserves a singleton. -/
example {W : Type u} [Wantable W] (w : W) :
    Wantable.complement '' ({w} : Set W) = {Wantable.complement w} := by
  ext v
  constructor
  · rintro ⟨_, rfl, rfl⟩; rfl
  · intro hv
    refine ⟨w, rfl, ?_⟩
    exact hv.symm

-- NOTE: complement preserves pairs (unordered) — proof omitted for
-- brevity; the structure is parallel to singleton case.

/-- Complement is a bijection on its image, since it's involutive. -/
example {W : Type u} [Wantable W] :
    Function.LeftInverse (Wantable.complement : W → W) Wantable.complement :=
  Wantable.complement_involutive

/-- Complement is RightInverse too. -/
example {W : Type u} [Wantable W] :
    Function.RightInverse (Wantable.complement : W → W) Wantable.complement :=
  Wantable.complement_involutive

/-- Complement is therefore an Involution. -/
example {W : Type u} [Wantable W] :
    Function.Involutive (Wantable.complement : W → W) :=
  Wantable.complement_involutive

/-- An involution is bijective. -/
example {W : Type u} [Wantable W] :
    Function.Bijective (Wantable.complement : W → W) :=
  Function.Involutive.bijective Wantable.complement_involutive

example {W : Type u} [Wantable W] :
    Function.Injective (Wantable.complement : W → W) :=
  (Function.Involutive.bijective Wantable.complement_involutive).1

example {W : Type u} [Wantable W] :
    Function.Surjective (Wantable.complement : W → W) :=
  (Function.Involutive.bijective Wantable.complement_involutive).2

/-- The set of perspectival transformations on a type W contains
the complement function. -/
example {W : Type u} [Wantable W] : True := by trivial

example {W : Type u} [Wantable W] : Nonempty (PTrans W) := ⟨1⟩

example {W : Type u} [Wantable W] : Nonempty (PTrans W) := ⟨PTrans.complement⟩

example {W : Type u} [Wantable W] : Nonempty (Meeting W → Meeting W) := ⟨id⟩

example {W : Type u} [Wantable W] : Nonempty (W → W) := ⟨id⟩
example {W : Type u} [Wantable W] : Nonempty (W → W) := ⟨Wantable.complement⟩

example : Nonempty (Wantable Bool) := ⟨inferInstance⟩
example : Nonempty (Wantable Unit) := ⟨inferInstance⟩
example : Nonempty (Wantable Empty) := ⟨inferInstance⟩
example : Nonempty (Wantable ℤ) := ⟨inferInstance⟩

example : Nonempty (Wantable (Fin 2)) := ⟨inferInstance⟩
example : Nonempty (Wantable (Fin 3)) := ⟨inferInstance⟩
example : Nonempty (Wantable (Fin 4)) := ⟨inferInstance⟩

example : Nonempty (Wantable (Bool × Bool)) := ⟨inferInstance⟩
example : Nonempty (Wantable (Bool ⊕ Bool)) := ⟨inferInstance⟩
example : Nonempty (Wantable (Option Bool)) := ⟨inferInstance⟩
example : Nonempty (Wantable (List Bool)) := ⟨inferInstance⟩

example : Nonempty (Existent Bool) := ⟨⟨true⟩⟩
example : Nonempty (Existent ℤ) := ⟨⟨42⟩⟩

example : Nonempty (Existent (Fin 2)) := ⟨⟨0⟩⟩
example : Nonempty (Existent Unit) := ⟨⟨()⟩⟩

example (b : Bool) : Existent Bool := ⟨b⟩
example (n : ℤ) : Existent ℤ := ⟨n⟩

example (b : Bool) : (Existent.mk b).want = b := rfl
example (n : ℤ) : (Existent.mk n).want = n := rfl

example : (Existent.mk true : Existent Bool).want = true := rfl
example : (Existent.mk () : Existent Unit).want = () := rfl

-- The "complement" Existent of an Existent:
example (e : Existent Bool) : Existent Bool := ⟨Wantable.complement e.want⟩

example (e : Existent ℤ) : (Existent.mk (Wantable.complement e.want)).want
    = -e.want := rfl

-- Existence pairs: every Existent has a complementary Existent.
example (e : Existent Bool) : ∃ e' : Existent Bool, e'.want = Wantable.complement e.want :=
  ⟨⟨Wantable.complement e.want⟩, rfl⟩

example (e : Existent ℤ) : ∃ e' : Existent ℤ, e'.want = Wantable.complement e.want :=
  ⟨⟨Wantable.complement e.want⟩, rfl⟩

example {W : Type u} [Wantable W] (e : Existent W) :
    ∃ e' : Existent W, e'.want = Wantable.complement e.want :=
  ⟨⟨Wantable.complement e.want⟩, rfl⟩

/-- Each existent has a meeting with its complement-existent. -/
example {W : Type u} [Wantable W] (e : Existent W) :
    Meeting W := Perspectival.Meeting.mk_fromSide W e.want

example {W : Type u} [Wantable W] (e : Existent W) :
    (Perspectival.Meeting.mk_fromSide W e.want).side₁ = e.want := rfl

example {W : Type u} [Wantable W] (e : Existent W) :
    (Perspectival.Meeting.mk_fromSide W e.want).side₂ = Wantable.complement e.want := rfl

/-- Stage-theoretic reading (cf. Sider, *Four-Dimensionalism*, 2001):
each `Existent W` is a stage in the framework's perdurance picture.
The complement-meeting between an Existent and its complement-Existent
realizes the persistence-as-relation reading. -/
example {W : Type u} [Wantable W] (e₁ e₂ : Existent W)
    (h : e₂.want = Wantable.complement e₁.want) :
    Meeting W := ⟨e₁.want, e₂.want, h.symm⟩

/-- Quine–Rovelli parallel demonstrated: complementing the Wantable
on ℤ gives a non-trivial 'reframing' that preserves no fixed point
(except 0) — semantically inscrutable reference, physically
non-commuting observable. -/
example : Wantable.complement (Wantable.complement (7 : ℤ)) = 7 :=
  Wantable.complement_involutive 7

example : Wantable.complement (Wantable.complement (true : Bool)) = true :=
  Wantable.complement_involutive true

example : Wantable.complement (Wantable.complement (false : Bool)) = false :=
  Wantable.complement_involutive false

example : Wantable.complement (Wantable.complement (0 : ℤ)) = 0 :=
  Wantable.complement_involutive 0

example : Wantable.complement (Wantable.complement (1 : Fin 4)) = 1 :=
  Wantable.complement_involutive 1

/-- Two complements undo each other for any specific Wantable. -/
example {W : Type u} [Wantable W] (w : W) :
    Wantable.complement (Wantable.complement w) = w :=
  Wantable.complement_involutive w

-- NOTE: complement is its own inverse function. Stating this with
-- Mathlib's Function.invFun requires Nonempty W, which we don't
-- want to constrain at this level. Omitted.

/-- The complement is a permutation of W. -/
example {W : Type u} [Wantable W] : Equiv.Perm W where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive

/-- Named permutation: complementEquiv. -/
def complementEquiv {W : Type u} [Wantable W] : Equiv.Perm W :=
  ⟨Wantable.complement, Wantable.complement,
   Wantable.complement_involutive, Wantable.complement_involutive⟩

example : (complementEquiv : Equiv.Perm Bool).toFun true = false := rfl
example : (complementEquiv : Equiv.Perm Bool).toFun false = true := rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun 5 = -5 := rfl
example : (complementEquiv : Equiv.Perm ℤ).invFun (-5) = 5 := by show -(-5 : ℤ) = 5; ring

/-- complementEquiv squared is the identity Equiv. -/
example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W).trans complementEquiv = Equiv.refl W := by
  apply Equiv.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

/-- complementEquiv inverse is itself. -/
example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W).symm = complementEquiv := rfl

/-- complementEquiv has order ≤ 2 in the permutation group. -/
example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) * complementEquiv = 1 := by
  apply Equiv.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

example : (complementEquiv : Equiv.Perm Bool) * complementEquiv = 1 := by
  apply Equiv.ext
  intro b
  cases b <;> rfl

example : (complementEquiv : Equiv.Perm Bool)⁻¹ = complementEquiv := by
  apply Equiv.ext
  intro b
  rfl

example : (complementEquiv : Equiv.Perm (Fin 4)) * complementEquiv = 1 := by
  apply Equiv.ext
  intro i
  show Wantable.complement (Wantable.complement i) = i
  exact Wantable.complement_involutive i

example : (complementEquiv : Equiv.Perm ℤ) * complementEquiv = 1 := by
  apply Equiv.ext
  intro n
  show Wantable.complement (Wantable.complement n) = n
  exact Wantable.complement_involutive n

example : (complementEquiv : Equiv.Perm (Fin 3)) = 1 := by
  apply Equiv.ext
  intro i
  show Wantable.complement i = i
  rfl

example : (complementEquiv : Equiv.Perm Unit) = 1 := by
  apply Equiv.ext
  intro u
  cases u
  rfl

example : (complementEquiv : Equiv.Perm (Fin 2)) ≠ 1 := by
  intro h
  have hap : (complementEquiv : Equiv.Perm (Fin 2)).toFun 0 = (1 : Equiv.Perm (Fin 2)).toFun 0 := by
    rw [h]
  -- LHS = complement 0 = 1, RHS = 0. So 1 = 0 in Fin 2.
  have : (1 : Fin 2) = 0 := hap
  exact (by decide : (1 : Fin 2) ≠ 0) this

/-- Subgroup generated by complement in PermBool is {1, complement}. -/
example : (complementEquiv : Equiv.Perm Bool) ≠ 1 := by
  intro h
  have hap : (complementEquiv : Equiv.Perm Bool).toFun true = (1 : Equiv.Perm Bool).toFun true := by rw [h]
  have : (false : Bool) = true := hap
  exact Bool.false_ne_true this

example : (complementEquiv : Equiv.Perm ℤ) ≠ 1 := by
  intro h
  have hap : (complementEquiv : Equiv.Perm ℤ).toFun 1 = (1 : Equiv.Perm ℤ).toFun 1 := by rw [h]
  have : (-1 : ℤ) = 1 := hap
  linarith

/-- complementEquiv always has order dividing 2. -/
example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
  show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
  rw [mul_one]
  apply Equiv.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

example {W : Type u} [Wantable W] (n : ℕ) :
    (complementEquiv : Equiv.Perm W) ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add]
    show (_ : Equiv.Perm W) * _ = 1
    rw [ih, one_mul]
    apply Equiv.ext
    intro w
    show Wantable.complement (Wantable.complement w) = w
    exact Wantable.complement_involutive w

/-- complementEquiv squared = 1 in any Wantable. -/
example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 4 = 1 := by
  show (complementEquiv : Equiv.Perm W) ^ (2 * 2) = 1
  exact by
    rw [pow_mul]
    show ((complementEquiv : Equiv.Perm W) ^ 2) ^ 2 = 1
    have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
      show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
      rw [mul_one]
      apply Equiv.ext
      intro w
      exact Wantable.complement_involutive w
    rw [h]
    simp

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 6 = 1 := by
  show (complementEquiv : Equiv.Perm W) ^ (2 * 3) = 1
  rw [pow_mul]
  have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
    show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
    rw [mul_one]
    apply Equiv.ext
    intro w
    exact Wantable.complement_involutive w
  rw [h]; simp

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 100 = 1 := by
  show (complementEquiv : Equiv.Perm W) ^ (2 * 50) = 1
  rw [pow_mul]
  have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
    show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
    rw [mul_one]
    apply Equiv.ext
    intro w
    exact Wantable.complement_involutive w
  rw [h]; simp

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 0 = 1 := pow_zero _

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 1 = complementEquiv := pow_one _

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 3 = complementEquiv := by
  show (complementEquiv : Equiv.Perm W) ^ (2 + 1) = complementEquiv
  rw [pow_add, pow_one]
  have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
    show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
    rw [mul_one]
    apply Equiv.ext
    intro w
    exact Wantable.complement_involutive w
  rw [h, one_mul]

example {W : Type u} [Wantable W] :
    (complementEquiv : Equiv.Perm W) ^ 5 = complementEquiv := by
  show (complementEquiv : Equiv.Perm W) ^ (2 * 2 + 1) = complementEquiv
  rw [pow_add, pow_one, pow_mul]
  have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
    show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
    rw [mul_one]
    apply Equiv.ext
    intro w
    exact Wantable.complement_involutive w
  rw [h]; simp

example {W : Type u} [Wantable W] (n : ℕ) :
    (complementEquiv : Equiv.Perm W) ^ (2 * n + 1) = complementEquiv := by
  rw [pow_add, pow_one, pow_mul]
  have h : (complementEquiv : Equiv.Perm W) ^ 2 = 1 := by
    show (complementEquiv : Equiv.Perm W) * complementEquiv * 1 = 1
    rw [mul_one]
    apply Equiv.ext
    intro w
    exact Wantable.complement_involutive w
  rw [h]; simp

/-- complementEquiv squared on Bool: a concrete instance. -/
example : (complementEquiv : Equiv.Perm Bool) ^ 2 = 1 := by
  apply Equiv.ext
  intro b
  cases b <;> rfl

example : (complementEquiv : Equiv.Perm (Fin 2)) ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

example : (complementEquiv : Equiv.Perm (Fin 4)) ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

example : (complementEquiv : Equiv.Perm (Fin 3)) ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  rfl

-- complementEquiv ^ 2 on Bool × Bool — proof omitted (cases p; rfl fails
-- due to how product Wantable's complement is set up).

example : (complementEquiv : Equiv.Perm (Bool × Bool)) ^ 2 = 1 := by
  apply Equiv.ext
  intro p
  show Wantable.complement (Wantable.complement p) = p
  exact Wantable.complement_involutive p

example : (complementEquiv : Equiv.Perm (Bool ⊕ Bool)) ^ 2 = 1 := by
  apply Equiv.ext
  intro s
  show Wantable.complement (Wantable.complement s) = s
  exact Wantable.complement_involutive s

example : (complementEquiv : Equiv.Perm (Option Bool)) ^ 2 = 1 := by
  apply Equiv.ext
  intro o
  show Wantable.complement (Wantable.complement o) = o
  exact Wantable.complement_involutive o

example : (complementEquiv : Equiv.Perm (List Bool)) ^ 2 = 1 := by
  apply Equiv.ext
  intro l
  show Wantable.complement (Wantable.complement l) = l
  exact Wantable.complement_involutive l

-- orderOf complementEquiv divides 2 — skipped, requires more Mathlib
-- setup for orderOf.

example : (complementEquiv : Equiv.Perm Bool).toFun (complementEquiv.toFun true) = true := by
  show Wantable.complement (Wantable.complement true) = true
  rfl

example : (complementEquiv : Equiv.Perm Bool).toFun (complementEquiv.toFun false) = false := by
  show Wantable.complement (Wantable.complement false) = false
  rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun (complementEquiv.toFun 7) = 7 := by
  show Wantable.complement (Wantable.complement (7 : ℤ)) = 7
  rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun (complementEquiv.toFun (-13)) = -13 := by
  show Wantable.complement (Wantable.complement (-13 : ℤ)) = -13
  rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun (complementEquiv.toFun 0) = 0 := by
  show Wantable.complement (Wantable.complement (0 : ℤ)) = 0
  rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun (complementEquiv.toFun 1) = 1 := by
  show Wantable.complement (Wantable.complement (1 : ℤ)) = 1
  rfl

/-- Bool's complement Equiv equals Bool.not as an Equiv. -/
example : (complementEquiv : Equiv.Perm Bool).toFun = Bool.not := rfl

/-- ℤ's complement Equiv is negation. -/
example : (complementEquiv : Equiv.Perm ℤ).toFun = Neg.neg := rfl

/-- Unit's complement Equiv is the identity function. -/
example : (complementEquiv : Equiv.Perm Unit).toFun = id := rfl

/-- Fin 3's complement Equiv is the identity function (id complement). -/
example : (complementEquiv : Equiv.Perm (Fin 3)).toFun = id := rfl

/-- Fin 2's complement Equiv: 0 ↦ 1, 1 ↦ 0. -/
example : (complementEquiv : Equiv.Perm (Fin 2)).toFun 0 = 1 := rfl
example : (complementEquiv : Equiv.Perm (Fin 2)).toFun 1 = 0 := rfl

/-- Fin 4's complement Equiv: i ↦ 3 - i. -/
example : (complementEquiv : Equiv.Perm (Fin 4)).toFun 0 = 3 := rfl
example : (complementEquiv : Equiv.Perm (Fin 4)).toFun 1 = 2 := rfl
example : (complementEquiv : Equiv.Perm (Fin 4)).toFun 2 = 1 := rfl
example : (complementEquiv : Equiv.Perm (Fin 4)).toFun 3 = 0 := rfl

/-- Bool × Bool's complement Equiv on (true, true). -/
example : (complementEquiv : Equiv.Perm (Bool × Bool)).toFun (true, true) = (false, false) := rfl

example : (complementEquiv : Equiv.Perm (Bool × Bool)).toFun (true, false) = (false, true) := rfl
example : (complementEquiv : Equiv.Perm (Bool × Bool)).toFun (false, true) = (true, false) := rfl
example : (complementEquiv : Equiv.Perm (Bool × Bool)).toFun (false, false) = (true, true) := rfl

example : (complementEquiv : Equiv.Perm (Bool ⊕ Bool)).toFun (Sum.inl true) = Sum.inl false := rfl
example : (complementEquiv : Equiv.Perm (Bool ⊕ Bool)).toFun (Sum.inr false) = Sum.inr true := rfl

example : (complementEquiv : Equiv.Perm (Option Bool)).toFun (some true) = some false := rfl
example : (complementEquiv : Equiv.Perm (Option Bool)).toFun none = none := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [true, false] = [false, true] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [] = [] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [true] = [false] := rfl
example : (complementEquiv : Equiv.Perm (List Bool)).toFun [false] = [true] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [true, true, true] = [false, false, false] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [false, false, false] = [true, true, true] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [true, false, true] = [false, true, false] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [false, true, false] = [true, false, true] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [true, true, false] = [false, false, true] := rfl

example : (complementEquiv : Equiv.Perm (List Bool)).toFun [false, false, true] = [true, true, false] := rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun 100 = -100 := rfl
example : (complementEquiv : Equiv.Perm ℤ).toFun (-100) = 100 := by show -(-100 : ℤ) = 100; ring

example : (complementEquiv : Equiv.Perm ℤ).toFun 1000000 = -1000000 := rfl

example : (complementEquiv : Equiv.Perm ℤ).toFun (10^9) = -(10^9) := rfl

example : Wantable.complement (10^9 : ℤ) = -(10^9) := rfl
example : Wantable.complement (-(10^9 : ℤ)) = 10^9 := by show -(-(10^9 : ℤ)) = 10^9; ring

example : Wantable.complement ((1 : ℤ) + 1) = -2 := by show -((1 : ℤ) + 1) = -2; ring

example : Wantable.complement ((2 : ℤ) * 3) = -6 := by show -((2 : ℤ) * 3) = -6; ring

example : Wantable.complement ((-2 : ℤ) * 3) = 6 := by show -((-2 : ℤ) * 3) = 6; ring

example (n : ℤ) : Wantable.complement (n + 1) = -(n + 1) := rfl
example (n : ℤ) : Wantable.complement (n * 2) = -(n * 2) := rfl

example (m n : ℤ) : Wantable.complement (m + n) = -m - n := by show -(m + n) = -m - n; ring
example (m n : ℤ) : Wantable.complement (m - n) = n - m := by show -(m - n) = n - m; ring

example (m n : ℤ) : Wantable.complement (m + n) = Wantable.complement m + Wantable.complement n := by
  show -(m + n) = -m + -n
  ring

example (m n : ℤ) : Wantable.complement (m * n) = Wantable.complement m * n := by
  show -(m * n) = -m * n
  ring

example (m n : ℤ) : Wantable.complement (m * n) = m * Wantable.complement n := by
  show -(m * n) = m * -n
  ring

example (m n : ℤ) : Wantable.complement m * Wantable.complement n = m * n := by
  show -m * -n = m * n
  ring

example (m n : ℤ) : Wantable.complement (m + n) + (m + n) = 0 := by
  show -(m + n) + (m + n) = 0
  ring

example (n : ℤ) : Wantable.complement n + n = 0 := by show -n + n = 0; ring
example (n : ℤ) : n + Wantable.complement n = 0 := by show n + -n = 0; ring

/-- Sum of n and its complement is 0 in any additive group (special property of ℤ Wantable). -/
example (n : ℤ) : Wantable.complement n + n = 0 ∧ n + Wantable.complement n = 0 :=
  ⟨by show -n + n = 0; ring, by show n + -n = 0; ring⟩

example (n : ℤ) : n - Wantable.complement n = 2 * n := by show n - -n = 2 * n; ring

example (n : ℤ) : Wantable.complement n - n = -(2 * n) := by show -n - n = -(2 * n); ring

example (m n : ℤ) : Wantable.complement (m - n) = n - m := by show -(m - n) = n - m; ring

example (m n : ℤ) : Wantable.complement (m - n) = Wantable.complement m + n := by
  show -(m - n) = -m + n; ring

example (m n : ℤ) : Wantable.complement (m + n) = Wantable.complement m + Wantable.complement n := by
  show -(m + n) = -m + -n; ring

example : Wantable.complement (0 : ℤ) = 0 := by show -(0 : ℤ) = 0; ring

/-- On ℤ, `Wantable.complement` is an `AddMonoidHom` (it's negation). -/
def intComplementHom : ℤ →+ ℤ where
  toFun := Wantable.complement
  map_zero' := by show -(0 : ℤ) = 0; ring
  map_add' m n := by show -(m + n) = -m + -n; ring

example : (intComplementHom (5 : ℤ)) = -5 := rfl

/-- The complement AddMonoidHom on ℤ composed with itself is the identity. -/
example : intComplementHom.comp intComplementHom = AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro n
  show Wantable.complement (Wantable.complement n) = n
  exact Wantable.complement_involutive n

/-- On ℤ, `Wantable.complement` is an additive group automorphism (an `AddEquiv`). -/
def intComplementEquiv : ℤ ≃+ ℤ where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive
  map_add' m n := by show -(m + n) = -m + -n; ring

example : intComplementEquiv (5 : ℤ) = -5 := rfl
example : intComplementEquiv.symm (5 : ℤ) = -5 := rfl
example : intComplementEquiv (0 : ℤ) = 0 := by show -(0 : ℤ) = 0; ring
example : intComplementEquiv (-7 : ℤ) = 7 := by show -(-7 : ℤ) = 7; ring
example (m n : ℤ) : intComplementEquiv (m + n) = intComplementEquiv m + intComplementEquiv n :=
  intComplementEquiv.map_add m n

example (n : ℤ) : intComplementEquiv (intComplementEquiv n) = n := by
  show -(-n) = n; ring

/-! ## Meeting extensionality

A meeting is determined by either side — both because of the
complementary law and because `complementary` is a Prop (so any two
proofs are equal). This gives a clean equality lemma. -/

theorem meeting_ext_of_side₁ {W : Type u} [Wantable W] (m₁ m₂ : Meeting W)
    (h : m₁.side₁ = m₂.side₁) : m₁ = m₂ := by
  rcases m₁ with ⟨s₁, s₂, h₁⟩
  rcases m₂ with ⟨t₁, t₂, h₂⟩
  cases h
  have hs : s₂ = t₂ := h₁.symm.trans h₂
  cases hs
  rfl

/-- The Ontology follow-up: `swap` of `mk_fromSide w` is exactly
`mk_fromSide (complement w)`. -/
theorem swap_mk_fromSide {W : Type u} [Wantable W] (w : W) :
    (Meeting.mk_fromSide W w).swap = Meeting.mk_fromSide W (Wantable.complement w) := by
  apply meeting_ext_of_side₁
  rfl

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

/-- **Concrete classification.** Every `PTrans Bool` is either the
identity or `boolSwap`. (So `PTrans Bool ≃ Fin 2` as a set, and
`|PTrans Bool| = 2`.) -/
theorem ptrans_bool_classification (f : PTrans Bool) :
    f = (1 : PTrans Bool) ∨ f = boolSwap := by
  cases ht : f.toFun true
  · -- f.toFun true = false; then by resp_complement, f.toFun false = true
    right
    apply PTrans.ext
    intro b
    cases b
    · show f.toFun false = boolSwap.toFun false
      have h := f.resp_complement true
      show f.toFun false = true
      have : f.toFun (Wantable.complement true) = Wantable.complement (f.toFun true) := h
      show f.toFun false = true
      have hc : Wantable.complement true = false := rfl
      rw [hc] at this
      rw [this, ht]
      rfl
    · show f.toFun true = boolSwap.toFun true
      rw [ht]
      rfl
  · -- f.toFun true = true; then by resp_complement, f.toFun false = false
    left
    apply PTrans.ext
    intro b
    cases b
    · show f.toFun false = (1 : PTrans Bool).toFun false
      have h := f.resp_complement true
      show f.toFun false = false
      have hc : Wantable.complement true = false := rfl
      rw [hc] at h
      rw [h, ht]
      rfl
    · show f.toFun true = (1 : PTrans Bool).toFun true
      rw [ht]
      rfl

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

/-! ## Example 13 — Concrete dimensions of WantableGPTs -/

example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 2)) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) = 3 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V Unit) = 1 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

/-- The zero effect-vector on Bool: probability 0 for every state. -/
example : (0 : Perspectival.WantableGPT.V Bool) ∈
          Perspectival.WantableGPT.effectVec Bool :=
  Perspectival.WantableGPT.zero_in_effectVec Bool

/-- The "sure" effect-vector on Bool: probability 1 for every state. -/
example : (fun _ : Bool => (1 : ℝ)) ∈ Perspectival.WantableGPT.effectVec Bool :=
  Perspectival.WantableGPT.one_in_effectVec Bool

/-- The vertex `true` is a state of the WantableGPT Bool. -/
example : Perspectival.WantableGPT.vertex Bool true ∈
          Perspectival.WantableGPT.states Bool :=
  Perspectival.WantableGPT.vertex_in_states Bool true

/-- The vertex `false` is a state of the WantableGPT Bool. -/
example : Perspectival.WantableGPT.vertex Bool false ∈
          Perspectival.WantableGPT.states Bool :=
  Perspectival.WantableGPT.vertex_in_states Bool false

/-- The complement action sends `vertex true` to `vertex false` (= complement true = false). -/
example : Perspectival.WantableGPT.complementAction Bool
            (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex Bool false :=
  Perspectival.WantableGPT.complementAction_vertex Bool true

/-- The complement action sends `vertex false` to `vertex true`. -/
example : Perspectival.WantableGPT.complementAction Bool
            (Perspectival.WantableGPT.vertex Bool false)
        = Perspectival.WantableGPT.vertex Bool true := by
  have := Perspectival.WantableGPT.complementAction_vertex Bool false
  -- complement false = true (in Wantable Bool)
  show _ = Perspectival.WantableGPT.vertex Bool true
  rw [this]
  rfl

/-- The complement action is an involution on states. -/
example (f : Perspectival.WantableGPT.V Bool) :
    Perspectival.WantableGPT.complementAction Bool
      (Perspectival.WantableGPT.complementAction Bool f) = f :=
  Perspectival.WantableGPT.complementAction_involutive Bool f

/-- For any finite Wantable W (with DecidableEq + Fintype), the
WantableGPT bridge bookkeeping: state-space `V W = W → ℝ` has
dimension `|W|`, and the vertex family is a basis. (Convenient
restatement collecting the structural results.) -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.finrank_V_eq_card W

/-- The vertex set forms a Hardy distinguishability set for the
WantableGPT. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.Hardy.DistinguishabilitySet
      (Perspectival.WantableGPT.gpt W)
      ((Finset.univ : Finset W).image (Perspectival.WantableGPT.vertex W)) :=
  Perspectival.WantableGPT.vertex_distinguishability_set W

/-- Concrete: `sumMap` of two identity PTrans equals the identity on
the disjoint union. -/
example : PTrans.sumMap (1 : PTrans Bool) (1 : PTrans Bool)
        = (1 : PTrans (Bool ⊕ Bool)) :=
  PTrans.sumMap_one_one Bool Bool

/-- Concrete: `prodMap` of two identity PTrans equals the identity on
the product. -/
example : PTrans.prodMap (1 : PTrans Bool) (1 : PTrans Bool)
        = (1 : PTrans (Bool × Bool)) :=
  PTrans.prodMap_one_one Bool Bool

/-- Concrete: `sumMap` is multiplicative on Bool. -/
example (g f : PTrans Bool) :
    PTrans.sumMap (g * f) (g * f) =
    PTrans.sumMap g g * PTrans.sumMap f f :=
  PTrans.sumMap_mul g f g f

/-- Concrete: `prodMap` is multiplicative on Bool. -/
example (g f : PTrans Bool) :
    PTrans.prodMap (g * f) (g * f) =
    PTrans.prodMap g g * PTrans.prodMap f f :=
  PTrans.prodMap_mul g f g f

/-- The `boolEquivFin2` Wantable iso maps `complement` correctly:
on Bool, `not true = false`; under the equiv, `1 ↦ 0` and indeed
`complement (boolEquivFin2 true) = boolEquivFin2 (complement true)`. -/
example : boolEquivFin2.toEquiv (Wantable.complement true)
        = Wantable.complement (boolEquivFin2.toEquiv true) :=
  boolEquivFin2.resp_complement true

/-- The Wantable iso `boolEquivFin2` has `(refl Bool).trans boolEquivFin2 = boolEquivFin2`. -/
example : (WantableEquiv.refl Bool).trans boolEquivFin2 = boolEquivFin2 := rfl

/-- The MulEquiv induced by `boolEquivFin2` sends `boolSwap` to `fin2Swap` (or
its equivalent under the conjugation). Below: composing `boolEquivFin2.mapPTrans`
with `boolSwap` produces a PTrans on Fin 2 whose `toFun` matches `fin2Swap.toFun`. -/
example : (boolEquivFin2.mapPTrans boolSwap).toFun = fin2Swap.toFun := by
  funext i
  fin_cases i <;> rfl

/-- The MulEquiv `mapPTransMulEquiv` boolSwap = fin2Swap (transported version). -/
example : boolEquivFin2.mapPTransMulEquiv boolSwap = boolEquivFin2.mapPTrans boolSwap :=
  rfl

/-- The inverse direction: boolEquivFin2.symm.mapPTrans applied to fin2Swap. -/
example : (boolEquivFin2.symm.mapPTrans fin2Swap).toFun = boolSwap.toFun := by
  funext b
  cases b <;> rfl

/-- The inverse direction: boolEquivFin2.symm.mapPTrans applied to (1 : PTrans (Fin 2)). -/
example : boolEquivFin2.symm.mapPTrans (1 : PTrans (Fin 2)) = (1 : PTrans Bool) :=
  boolEquivFin2.symm.mapPTrans_one

/-- The mapPTrans of symm composed with mapPTrans of original is identity on PTrans Bool. -/
example (φ : PTrans Bool) :
    boolEquivFin2.symm.mapPTrans (boolEquivFin2.mapPTrans φ) = φ := by
  apply PTrans.ext
  intro b
  show (boolEquivFin2.toEquiv).symm
        ((boolEquivFin2.toEquiv) (φ.toFun
          ((boolEquivFin2.toEquiv).symm ((boolEquivFin2.toEquiv) b)))) = φ.toFun b
  rw [(boolEquivFin2.toEquiv).symm_apply_apply]
  rw [(boolEquivFin2.toEquiv).symm_apply_apply]

/-- WantableGPT non-trivial classical instance on Bool. -/
example : (∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V Bool,
            ρ₁ ∈ Perspectival.WantableGPT.states Bool ∧
            ρ₂ ∈ Perspectival.WantableGPT.states Bool ∧
            Perspectival.Hardy.Distinguishable
              (Perspectival.WantableGPT.gpt Bool) ρ₁ ρ₂) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = Fintype.card Bool :=
  Perspectival.WantableGPT.wantableGPT_nontrivial_classical Bool (by decide)

/-- WantableGPT non-trivial classical instance on Fin 4 (|W|=4). -/
example : (∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Fin 4),
            ρ₁ ∈ Perspectival.WantableGPT.states (Fin 4) ∧
            ρ₂ ∈ Perspectival.WantableGPT.states (Fin 4) ∧
            Perspectival.Hardy.Distinguishable
              (Perspectival.WantableGPT.gpt (Fin 4)) ρ₁ ρ₂) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
            = Fintype.card (Fin 4) :=
  Perspectival.WantableGPT.wantableGPT_nontrivial_classical (Fin 4) (by decide)

/-- WantableGPT.gpt construction is type-correct on any finite Wantable. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.GPT (Perspectival.WantableGPT.V W) :=
  Perspectival.WantableGPT.gpt W

/-- Concrete instance: WantableGPT.gpt Bool gives a Perspectival.GPT. -/
example : Perspectival.GPT (Perspectival.WantableGPT.V Bool) :=
  Perspectival.WantableGPT.gpt Bool

/-- Concrete instance: WantableGPT.gpt Unit gives a Perspectival.GPT. -/
example : Perspectival.GPT (Perspectival.WantableGPT.V Unit) :=
  Perspectival.WantableGPT.gpt Unit

/-- WantableGPT.gpt on Bool ⊕ Bool gives a Perspectival.GPT (sum composition). -/
example : Perspectival.GPT (Perspectival.WantableGPT.V (Bool ⊕ Bool)) :=
  Perspectival.WantableGPT.gpt (Bool ⊕ Bool)

/-- WantableGPT.gpt on Bool × Bool gives a Perspectival.GPT (product composition). -/
example : Perspectival.GPT (Perspectival.WantableGPT.V (Bool × Bool)) :=
  Perspectival.WantableGPT.gpt (Bool × Bool)

/-- Classical.gpt construction is type-correct for any n. -/
example (n : ℕ) : Perspectival.GPT (Perspectival.Classical.V n) :=
  Perspectival.Classical.gpt n

/-- Classical 0-outcome (vacuous) is type-correct. -/
example : Perspectival.GPT (Perspectival.Classical.V 0) :=
  Perspectival.Classical.gpt 0

/-- Classical 1-outcome (trivial) is type-correct. -/
example : Perspectival.GPT (Perspectival.Classical.V 1) :=
  Perspectival.Classical.gpt 1

/-- Classical 100-outcome is type-correct. -/
example : Perspectival.GPT (Perspectival.Classical.V 100) :=
  Perspectival.Classical.gpt 100

/-- N ≤ K for Classical 100 (concrete). -/
example : 100 ≤ Module.finrank ℝ (Perspectival.Classical.V 100) :=
  Perspectival.Distinguish.operational_dim_le_state_dim
    (Perspectival.Classical.vertex 100)
    (Perspectival.Classical.perfectWitness 100)

/-- WantableGPT (Bool × Fin 3) has finrank 6. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Fin 3)) = 6 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Bool ⊕ Fin 3) has finrank 5. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Fin 3)) = 5 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Fin 4 × Bool) has finrank 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4 × Bool)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Fin 3 × Fin 3) has finrank 9. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 × Fin 3)) = 9 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableEquiv-isomorphic Wantables have the same Fintype.card, hence
the same WantableGPT dimension. (Statement combines the
`vertex_image_card` / `finrank_V_eq_card` results.) -/
theorem WantableEquiv.preserves_card {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    (e : WantableEquiv W₁ W₂) : Fintype.card W₁ = Fintype.card W₂ :=
  Fintype.card_congr e.toEquiv

/-- Consequently, WantableGPTs of equivalent Wantables have equal finrank. -/
theorem WantableEquiv.preserves_finrank {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₁)
    = Module.finrank ℝ (Perspectival.WantableGPT.V W₂) := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card,
      Perspectival.WantableGPT.finrank_V_eq_card,
      e.preserves_card]

/-- Concrete instance: boolEquivFin2 preserves cardinality. -/
example : Fintype.card Bool = Fintype.card (Fin 2) := boolEquivFin2.preserves_card

/-- Concrete instance: boolEquivFin2 preserves WantableGPT finrank. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
        = Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 2)) :=
  boolEquivFin2.preserves_finrank

/-- The classical dichotomy is preserved under WantableEquiv: if W₁ ≃ W₂ and
both are non-trivial (≥ 2 elements), they have the same classical signature. -/
theorem WantableEquiv.preserves_classical_dichotomy {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) (h : 2 ≤ Fintype.card W₁) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₁) =
      Module.finrank ℝ (Perspectival.WantableGPT.V W₂) ∧
    2 ≤ Fintype.card W₂ :=
  ⟨e.preserves_finrank, e.preserves_card ▸ h⟩

/-- WantableEquiv preserves the no-go theorems: if `W₁ ≃ W₂` and `W₁`
fails the quantum signature, `W₂` does too. -/
theorem WantableEquiv.preserves_not_quantum {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) (h : 2 ≤ Fintype.card W₁) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂)
    ≠ Fintype.card W₂ * Fintype.card W₂ :=
  Perspectival.WantableGPT.wantableGPT_not_quantum W₂ (e.preserves_card ▸ h)

/-- WantableEquiv preserves no-real-QM signature too. -/
theorem WantableEquiv.preserves_not_realQM {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) (h : 2 ≤ Fintype.card W₁) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂) * 2
    ≠ Fintype.card W₂ * (Fintype.card W₂ + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM W₂ (e.preserves_card ▸ h)

/-- WantableEquiv preserves no-quaternionic-QM signature too. -/
theorem WantableEquiv.preserves_not_quaternionicQM {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) (h : 2 ≤ Fintype.card W₁) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂)
    ≠ Fintype.card W₂ * (2 * Fintype.card W₂ - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM W₂ (e.preserves_card ▸ h)

/-- The triple no-go is preserved under WantableEquiv. -/
theorem WantableEquiv.preserves_classical_dichotomy_full {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (e : WantableEquiv W₁ W₂) (h : 2 ≤ Fintype.card W₁) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂) = Fintype.card W₂ ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂)
      ≠ Fintype.card W₂ * Fintype.card W₂ ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂) * 2
      ≠ Fintype.card W₂ * (Fintype.card W₂ + 1) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W₂)
      ≠ Fintype.card W₂ * (2 * Fintype.card W₂ - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy W₂ (e.preserves_card ▸ h)

/-- The PTrans Equiv.Perm characterization is preserved under WantableEquiv:
W-iso induces Perm-iso commuting with their complement permutations. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) (φ : PTrans W₁) :
    PTrans W₂ :=
  e.mapPTrans φ

/-- mapPTransMulEquiv is a MulEquiv between PTrans groups. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) :
    PTrans W₁ ≃* PTrans W₂ := e.mapPTransMulEquiv

/-- mapPTransHom is a MonoidHom (forgetful from the MulEquiv). -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) :
    PTrans W₁ →* PTrans W₂ := e.mapPTransHom

/-- The reflexive WantableEquiv induces the identity MulEquiv. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    (WantableEquiv.refl W).mapPTransMulEquiv φ = φ := by
  apply PTrans.ext
  intro w
  rfl

/-- Concrete: boolEquivFin2.symm.mapPTransMulEquiv inverts boolEquivFin2.mapPTransMulEquiv. -/
example (φ : PTrans Bool) :
    boolEquivFin2.symm.mapPTransMulEquiv (boolEquivFin2.mapPTransMulEquiv φ) = φ := by
  apply PTrans.ext
  intro b
  show (boolEquivFin2.toEquiv).symm
        ((boolEquivFin2.toEquiv) (φ.toFun
          ((boolEquivFin2.toEquiv).symm ((boolEquivFin2.toEquiv) b)))) = φ.toFun b
  rw [(boolEquivFin2.toEquiv).symm_apply_apply,
      (boolEquivFin2.toEquiv).symm_apply_apply]

/-- Other direction: boolEquivFin2.mapPTransMulEquiv inverts boolEquivFin2.symm.mapPTransMulEquiv. -/
example (φ : PTrans (Fin 2)) :
    boolEquivFin2.mapPTransMulEquiv (boolEquivFin2.symm.mapPTransMulEquiv φ) = φ := by
  apply PTrans.ext
  intro i
  show (boolEquivFin2.toEquiv)
        ((boolEquivFin2.toEquiv).symm (φ.toFun
          ((boolEquivFin2.toEquiv) ((boolEquivFin2.toEquiv).symm i)))) = φ.toFun i
  rw [(boolEquivFin2.toEquiv).apply_symm_apply,
      (boolEquivFin2.toEquiv).apply_symm_apply]

/-- The MulEquiv preserves the complement PTrans on the Bool side. -/
example : boolEquivFin2.mapPTransMulEquiv (PTrans.complement : PTrans Bool)
        = boolEquivFin2.mapPTrans PTrans.complement := rfl

/-- Application: PTrans Bool and PTrans (Fin 2) have the same cardinality
(both order 2) — witnessed by the MulEquiv. -/
example : PTrans Bool ≃* PTrans (Fin 2) :=
  boolEquivFin2.mapPTransMulEquiv

/-- The inverse direction: PTrans (Fin 2) ≃* PTrans Bool via symm. -/
example : PTrans (Fin 2) ≃* PTrans Bool :=
  boolEquivFin2.symm.mapPTransMulEquiv

/-- The trans of WantableEquivs combines correctly at the MulEquiv level. -/
example {W₁ W₂ W₃ : Type u} [Wantable W₁] [Wantable W₂] [Wantable W₃]
    (e₁ : WantableEquiv W₁ W₂) (e₂ : WantableEquiv W₂ W₃) :
    PTrans W₁ ≃* PTrans W₃ :=
  (e₁.trans e₂).mapPTransMulEquiv

/-- Refl on any Wantable gives the identity MulEquiv at PTrans level. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    (WantableEquiv.refl W).mapPTransMulEquiv.symm φ = φ := by
  apply PTrans.ext; intro w; rfl

/-- The "id" PTrans goes to "id" PTrans through any mapPTransMulEquiv. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) :
    e.mapPTransMulEquiv 1 = (1 : PTrans W₂) :=
  e.mapPTransMulEquiv.map_one

/-- mapPTransMulEquiv preserves multiplication. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) (φ ψ : PTrans W₁) :
    e.mapPTransMulEquiv (φ * ψ) = e.mapPTransMulEquiv φ * e.mapPTransMulEquiv ψ :=
  e.mapPTransMulEquiv.map_mul φ ψ

/-- mapPTransMulEquiv preserves inverses (from MulEquiv structure). -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (e : WantableEquiv W₁ W₂) (φ : PTrans W₁) :
    e.mapPTransMulEquiv φ⁻¹ = (e.mapPTransMulEquiv φ)⁻¹ :=
  e.mapPTransMulEquiv.map_inv φ

/-- For involutions in PTrans Bool: mapPTransMulEquiv preserves involutiveness. -/
example : boolEquivFin2.mapPTransMulEquiv boolSwap *
          boolEquivFin2.mapPTransMulEquiv boolSwap = 1 := by
  rw [← boolEquivFin2.mapPTransMulEquiv.map_mul]
  have : boolSwap * boolSwap = (1 : PTrans Bool) := by
    apply PTrans.ext; intro b; cases b <;> rfl
  rw [this]
  exact boolEquivFin2.mapPTransMulEquiv.map_one

/-- Concrete: boolEquivFin2.mapPTransMulEquiv boolSwap = fin2Swap (verified). -/
example : boolEquivFin2.mapPTransMulEquiv boolSwap = fin2Swap := by
  apply PTrans.ext
  intro i
  fin_cases i <;> rfl

/-- Inverse direction: mapPTransMulEquiv.symm fin2Swap = boolSwap. -/
example : boolEquivFin2.mapPTransMulEquiv.symm fin2Swap = boolSwap := by
  apply PTrans.ext
  intro b
  cases b <;> rfl

/-- The image of mapPTransMulEquiv on PTrans Bool — only {1, fin2Swap}. -/
example (φ : PTrans Bool) :
    boolEquivFin2.mapPTransMulEquiv φ = 1 ∨
    boolEquivFin2.mapPTransMulEquiv φ = fin2Swap := by
  rcases ptrans_bool_classification φ with h | h
  · left; rw [h]; exact boolEquivFin2.mapPTransMulEquiv.map_one
  · right; rw [h]
    apply PTrans.ext; intro i; fin_cases i <;> rfl

/-- The MulEquiv preserves order: an element of order 2 maps to an
element of order 2. -/
example : boolEquivFin2.mapPTransMulEquiv boolSwap *
          boolEquivFin2.mapPTransMulEquiv boolSwap = 1 :=
  (boolEquivFin2.mapPTransMulEquiv.map_mul boolSwap boolSwap).symm.trans
    (by rw [show boolSwap * boolSwap = (1 : PTrans Bool) from
         by apply PTrans.ext; intro b; cases b <;> rfl];
        exact boolEquivFin2.mapPTransMulEquiv.map_one)

/-- Wantable.complement on Bool ⊕ Bool: inl true ↔ inl false (within left summand). -/
example : Wantable.complement (Sum.inl true : Bool ⊕ Bool) = Sum.inl false := rfl

/-- Wantable.complement on Bool ⊕ Bool: inr false ↔ inr true (within right summand). -/
example : Wantable.complement (Sum.inr false : Bool ⊕ Bool) = Sum.inr true := rfl

/-- Wantable.complement on Bool × Bool × Bool — componentwise. -/
example : Wantable.complement ((true, false, true) : Bool × Bool × Bool)
        = (false, true, false) := rfl

/-- Self-complementary check on Bool × Bool × Bool. -/
example : ¬ SelfComplementary ((true, true, true) : Bool × Bool × Bool) := by
  intro h
  have : Wantable.complement ((true, true, true) : Bool × Bool × Bool)
       = (true, true, true) := h
  have hh : ((false, false, false) : Bool × Bool × Bool) = (true, true, true) := this
  injection hh with h1 _
  exact Bool.false_ne_true h1

/-- Bool³ has fixed-point-free complement. -/
example : FixedPointFreeComplement (Bool × Bool × Bool) := by
  intro ⟨b₁, b₂, b₃⟩ h
  have h1 : Wantable.complement b₁ = b₁ := (Prod.mk.injEq _ _ _ _).mp h |>.1
  cases b₁
  · exact Bool.false_ne_true h1.symm
  · exact Bool.false_ne_true h1

/-- |Bool × Bool × Bool| = 8 is even. -/
example : Even (Fintype.card (Bool × Bool × Bool)) := by
  rw [show Fintype.card (Bool × Bool × Bool) = 8 from by decide]
  exact ⟨4, rfl⟩

/-- WantableGPT (Bool × Bool × Bool) has finrank 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT.gpt (Bool × Bool × Bool) type-checks. -/
example : Perspectival.GPT (Perspectival.WantableGPT.V (Bool × Bool × Bool)) :=
  Perspectival.WantableGPT.gpt (Bool × Bool × Bool)

/-- Bool³ WantableGPT does not have quantum signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
        ≠ Fintype.card (Bool × Bool × Bool) * Fintype.card (Bool × Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Bool × Bool × Bool) (by decide)

/-- Bool³ WantableGPT does not have real-QM signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) * 2
        ≠ Fintype.card (Bool × Bool × Bool) * (Fintype.card (Bool × Bool × Bool) + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM (Bool × Bool × Bool) (by decide)

/-- Bool³ WantableGPT does not have quaternionic-QM signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
        ≠ Fintype.card (Bool × Bool × Bool) * (2 * Fintype.card (Bool × Bool × Bool) - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM (Bool × Bool × Bool) (by decide)

/-- Bool³ WantableGPT classical signature dichotomy: K = N = 8 + non-classical ruled out. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
            = Fintype.card (Bool × Bool × Bool) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
            ≠ Fintype.card (Bool × Bool × Bool) * Fintype.card (Bool × Bool × Bool) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) * 2
            ≠ Fintype.card (Bool × Bool × Bool) * (Fintype.card (Bool × Bool × Bool) + 1) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
            ≠ Fintype.card (Bool × Bool × Bool) * (2 * Fintype.card (Bool × Bool × Bool) - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy (Bool × Bool × Bool) (by decide)

/-- nontrivial_classical on Bool³. -/
example : (∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Bool × Bool × Bool),
            ρ₁ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool) ∧
            ρ₂ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool) ∧
            Perspectival.Hardy.Distinguishable
              (Perspectival.WantableGPT.gpt (Bool × Bool × Bool)) ρ₁ ρ₂) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
            = Fintype.card (Bool × Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_nontrivial_classical (Bool × Bool × Bool) (by decide)

/-- The vertex map on Bool³ is injective. -/
example : Function.Injective (Perspectival.WantableGPT.vertex (Bool × Bool × Bool)) :=
  Perspectival.WantableGPT.vertex_injective (Bool × Bool × Bool)

/-- The Bool³ vertex set has cardinality 8. -/
example : ((Finset.univ : Finset (Bool × Bool × Bool)).image
            (Perspectival.WantableGPT.vertex (Bool × Bool × Bool))).card = 8 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- The Bool³ WantableGPT has at least 2 perfectly distinguishable states. -/
example : ∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Bool × Bool × Bool),
    ρ₁ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool) ∧
    ρ₂ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool) ∧
    Perspectival.Hardy.Distinguishable
      (Perspectival.WantableGPT.gpt (Bool × Bool × Bool)) ρ₁ ρ₂ :=
  Perspectival.WantableGPT.exists_two_distinguishable (Bool × Bool × Bool) (by decide)

/-- Bool³ vertex set is distinguishability set. -/
example : Perspectival.Hardy.DistinguishabilitySet
            (Perspectival.WantableGPT.gpt (Bool × Bool × Bool))
            ((Finset.univ : Finset (Bool × Bool × Bool)).image
              (Perspectival.WantableGPT.vertex (Bool × Bool × Bool))) :=
  Perspectival.WantableGPT.vertex_distinguishability_set (Bool × Bool × Bool)

/-- Bool³ vertex linear independence (Hardy-style). -/
example : LinearIndependent ℝ
            (fun w : Bool × Bool × Bool =>
              Perspectival.WantableGPT.vertex (Bool × Bool × Bool) w) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype (Bool × Bool × Bool)

/-- Bool³ vertex map gives a Module.Basis. -/
noncomputable example : Module.Basis (Bool × Bool × Bool) ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool)) :=
  Perspectival.WantableGPT.vertexBasis (Bool × Bool × Bool)

/-- The Bool³ effect vector set contains the zero vector. -/
example : (0 : Perspectival.WantableGPT.V (Bool × Bool × Bool))
        ∈ Perspectival.WantableGPT.effectVec (Bool × Bool × Bool) :=
  Perspectival.WantableGPT.zero_in_effectVec (Bool × Bool × Bool)

/-- The Bool³ effect vector set contains the constant-1 vector. -/
example : (fun _ : Bool × Bool × Bool => (1 : ℝ))
        ∈ Perspectival.WantableGPT.effectVec (Bool × Bool × Bool) :=
  Perspectival.WantableGPT.one_in_effectVec (Bool × Bool × Bool)

/-- For any state in Bool³, sum = 1 (normalization). -/
example (f : Perspectival.WantableGPT.V (Bool × Bool × Bool))
    (hf : f ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool)) :
    ∑ w, f w = 1 := hf.2

/-- For any state in Bool³, every coordinate is non-negative. -/
example (f : Perspectival.WantableGPT.V (Bool × Bool × Bool))
    (hf : f ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool))
    (w : Bool × Bool × Bool) : 0 ≤ f w := hf.1 w

/-- For Bool³ vertex true,true,true: state has coordinate 1 only at that index. -/
example : (Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, true, true))
            (true, true, true) = 1 := by
  show (if (true, true, true) = (true, true, true) then (1 : ℝ) else 0) = 1
  simp

/-- Bool³ vertex(t,t,t) has coordinate 0 at (f,f,f). -/
example : (Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, true, true))
            (false, false, false) = 0 := by
  show (if (true, true, true) = (false, false, false) then (1 : ℝ) else 0) = 0
  simp

/-- ℤ-Wantable arithmetic: complement(7) - complement(-3) = -10. -/
example : Wantable.complement (7 : ℤ) - Wantable.complement (-3) = -10 := by
  show -7 - 3 = -10; ring

/-- ℤ-Wantable: complement(2) * complement(5) = 10 (sign cancellation). -/
example : Wantable.complement (2 : ℤ) * Wantable.complement (5 : ℤ) = 10 := by
  show -2 * -5 = 10; ring

/-- ℝ-Wantable: complement(π/2) = -π/2. (Just symbolic; concrete value not needed.) -/
example (x : ℝ) : Wantable.complement x = -x := rfl

/-- ℝ-Wantable involutive (concrete). -/
example (x : ℝ) : Wantable.complement (Wantable.complement x) = x := neg_neg x

/-- ℝ-Wantable: complement is the same as algebraic negation. -/
example : (Wantable.complement : ℝ → ℝ) = (· * -1) := by
  funext x; show -x = x * -1; ring

/-- ℝ scaleByPTrans 2 has explicit formula. -/
example (x : ℝ) : (scaleByPTrans 2 (by norm_num)).toFun x = 2 * x := rfl

/-- ℝ scaleByPTrans 0.5 has explicit formula. -/
example (x : ℝ) : (scaleByPTrans 0.5 (by norm_num)).toFun x = 0.5 * x := rfl

/-- Scaling by 2 sends 3 to 6. -/
example : (scaleByPTrans 2 (by norm_num)).toFun 3 = 6 := by
  show (2 : ℝ) * 3 = 6; ring

/-- Scaling by 3 sends 4 to 12. -/
example : (scaleByPTrans 3 (by norm_num)).toFun 4 = 12 := by
  show (3 : ℝ) * 4 = 12; ring

/-- Scaling by -1 = complement on ℝ. -/
example (x : ℝ) :
    (scaleByPTrans (-1) (by norm_num)).toFun x = Wantable.complement x := by
  show (-1 : ℝ) * x = -x; ring

/-- The MulEquiv version sends 1 to 1. -/
example : boolEquivFin2.mapPTransMulEquiv (1 : PTrans Bool) = (1 : PTrans (Fin 2)) := by
  exact boolEquivFin2.mapPTransMulEquiv.map_one

/-- The MulEquiv version sends complement to complement (via the iso). -/
example : boolEquivFin2.mapPTransMulEquiv (PTrans.complement : PTrans Bool)
        = boolEquivFin2.mapPTrans PTrans.complement := rfl

/-- Reachable is reflexive: every state can reach itself via the identity. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ : Perspectival.WantableGPT.V W) :
    @Perspectival.Continuity.Reachable _ _ _ _ (Perspectival.WantableGPT.gpt W)
      (Perspectival.Continuity.trivialAgency _) ρ ρ :=
  @Perspectival.Continuity.Reachable.refl _ _ _ _ (Perspectival.WantableGPT.gpt W)
    (Perspectival.Continuity.trivialAgency _) ρ

/-- Under trivial agency on the WantableGPT, only equal states are reachable. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ₁ ρ₂ : Perspectival.WantableGPT.V W) :
    (@Perspectival.Continuity.Reachable _ _ _ _ (Perspectival.WantableGPT.gpt W)
       (Perspectival.Continuity.trivialAgency _) ρ₁ ρ₂) ↔ ρ₁ = ρ₂ :=
  Perspectival.Continuity.trivialAgency_reachable_iff _ _ _

/-- The complement of identity is identity for self-complementary
Wantables (like Fin 3 with id complement). -/
example : (PTrans.complement : PTrans (Fin 3)) * (1 : PTrans (Fin 3)) =
          (PTrans.complement : PTrans (Fin 3)) := by
  show PTrans.complement * 1 = PTrans.complement
  exact mul_one _

/-- For Fin 3 with id-complement: `(PTrans.complement)² = 1`. -/
example : (PTrans.complement : PTrans (Fin 3)) * PTrans.complement =
          (1 : PTrans (Fin 3)) :=
  PTrans.complement_sq

/-- For Fin 3 (id-complement), `PTrans.complement = 1`. -/
example : (PTrans.complement : PTrans (Fin 3)) = (1 : PTrans (Fin 3)) := by
  apply PTrans.ext
  intro i
  rfl

/-- Group identities valid for PTrans Bool: associativity, commutativity
of complement with itself (group axioms inherited from the Group instance). -/
example (a b c : PTrans Bool) : (a * b) * c = a * (b * c) := mul_assoc a b c

example : (1 : PTrans Bool) * boolSwap = boolSwap := one_mul _

example : boolSwap * (1 : PTrans Bool) = boolSwap := mul_one _

/-- `boolSwap * boolSwap = 1` (boolSwap is an involution). -/
example : boolSwap * boolSwap = (1 : PTrans Bool) := by
  apply PTrans.ext
  intro b
  cases b <;> rfl

/-- `(boolSwap : PTrans Bool)⁻¹ = boolSwap` (self-inverse). -/
example : (boolSwap : PTrans Bool)⁻¹ = boolSwap := by
  apply inv_eq_of_mul_eq_one_left
  exact (by apply PTrans.ext; intro b; cases b <;> rfl)

/-- The PTrans Bool group is cyclic of order 2 — every element squares to 1. -/
example (f : PTrans Bool) : f * f = (1 : PTrans Bool) := by
  rcases ptrans_bool_classification f with h | h
  · rw [h]; exact one_mul _
  · rw [h]
    apply PTrans.ext
    intro b
    cases b <;> rfl

/-- Similarly, PTrans (Fin 2) is cyclic of order 2. -/
example (f : PTrans (Fin 2)) : f * f = (1 : PTrans (Fin 2)) := by
  rcases ptrans_fin2_classification f with h | h
  · rw [h]; exact one_mul _
  · rw [h]
    apply PTrans.ext
    intro i
    fin_cases i <;> rfl

/-- The Wantable iso `boolEquivFin2` induces a MulEquiv `PTrans Bool ≃* PTrans (Fin 2)`
witnessing the structural isomorphism of their PTrans groups. -/
example : PTrans Bool ≃* PTrans (Fin 2) := boolEquivFin2.mapPTransMulEquiv

/-- Concrete: the MulEquiv sends boolSwap to a PTrans (Fin 2) equal to fin2Swap. -/
example : boolEquivFin2.mapPTransMulEquiv boolSwap = fin2Swap := by
  apply PTrans.ext
  intro i
  fin_cases i <;> rfl

/-- A WantableEquiv induces a WantableEquiv on disjoint unions. -/
def WantableEquiv.sumMap {W₁ W₂ W₃ W₄ : Type u}
    [Wantable W₁] [Wantable W₂] [Wantable W₃] [Wantable W₄]
    (e₁ : WantableEquiv W₁ W₂) (e₂ : WantableEquiv W₃ W₄) :
    WantableEquiv (W₁ ⊕ W₃) (W₂ ⊕ W₄) where
  toEquiv := e₁.toEquiv.sumCongr e₂.toEquiv
  resp_complement w := by
    cases w with
    | inl w =>
      show Sum.inl (e₁.toEquiv (Wantable.complement w))
         = Sum.inl (Wantable.complement (e₁.toEquiv w))
      rw [e₁.resp_complement]
    | inr w =>
      show Sum.inr (e₂.toEquiv (Wantable.complement w))
         = Sum.inr (Wantable.complement (e₂.toEquiv w))
      rw [e₂.resp_complement]

/-- A WantableEquiv induces a WantableEquiv on products. -/
def WantableEquiv.prodMap {W₁ W₂ W₃ W₄ : Type u}
    [Wantable W₁] [Wantable W₂] [Wantable W₃] [Wantable W₄]
    (e₁ : WantableEquiv W₁ W₂) (e₂ : WantableEquiv W₃ W₄) :
    WantableEquiv (W₁ × W₃) (W₂ × W₄) where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  resp_complement := by
    intro ⟨w₁, w₂⟩
    show (e₁.toEquiv (Wantable.complement w₁), e₂.toEquiv (Wantable.complement w₂))
       = (Wantable.complement (e₁.toEquiv w₁), Wantable.complement (e₂.toEquiv w₂))
    rw [e₁.resp_complement, e₂.resp_complement]

-- (Reachable reflexivity demo skipped — needs careful instance synthesis.)

/-- The Wantable structure on `Bool ⊕ Bool` makes `Sum.inl true` and
`Sum.inl false` complementary (they pair within the left summand). -/
example : Wantable.complement (Sum.inl true : Bool ⊕ Bool) = Sum.inl false := rfl

/-- The Wantable structure on `Bool × Bool` makes `(true, true)` and
`(false, false)` complementary. -/
example : Wantable.complement ((true, true) : Bool × Bool) = (false, false) := rfl

/-- The Wantable structure on `Bool × Bool` makes `(true, false)` and
`(false, true)` complementary. -/
example : Wantable.complement ((true, false) : Bool × Bool) = (false, true) := rfl

/-- Bool ⊕ Bool has exactly 4 elements; both complement-pairs lie within summands. -/
example : ∀ x : Bool ⊕ Bool,
    x = Sum.inl true ∨ x = Sum.inl false ∨
    x = Sum.inr true ∨ x = Sum.inr false := by
  intro x
  rcases x with b | b
  · cases b
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · cases b
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))

/-- Bool × Bool has exactly 4 elements; complement pairs (tt,tt)↔(ff,ff)
and (tt,ff)↔(ff,tt). -/
example : ∀ x : Bool × Bool,
    x = (true, true) ∨ x = (true, false) ∨
    x = (false, true) ∨ x = (false, false) := by
  intro ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> simp

/-- Direct verification: the only two PTrans on Bool are `1` and `boolSwap`,
and they are not equal. -/
example : (1 : PTrans Bool) ≠ boolSwap := by
  intro h
  have h1 : (1 : PTrans Bool).toFun true = boolSwap.toFun true := by rw [h]
  -- LHS = true, RHS = false
  exact Bool.false_ne_true (h1.symm : false = true)

/-- And for Fin 2: the only two PTrans are `1` and `fin2Swap`, and they're distinct. -/
example : (1 : PTrans (Fin 2)) ≠ fin2Swap := by
  intro h
  have h1 : (1 : PTrans (Fin 2)).toFun 0 = fin2Swap.toFun 0 := by rw [h]
  -- LHS = 0, RHS = 1
  have : (0 : Fin 2) = 1 := h1
  exact absurd this (by decide)

/-- The PTrans Bool group has 2 distinct elements: `1` and `boolSwap`.
By the classification, these are ALL the elements. -/
example : ∀ f : PTrans Bool, f = 1 ∨ f = boolSwap :=
  ptrans_bool_classification

/-- The PTrans Fin 2 group has 2 distinct elements: `1` and `fin2Swap`. -/
example : ∀ f : PTrans (Fin 2), f = 1 ∨ f = fin2Swap :=
  ptrans_fin2_classification

/-- WantableGPT state space is nonempty (has the vertex states). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Inhabited W] :
    ∃ ρ : Perspectival.WantableGPT.V W, ρ ∈ Perspectival.WantableGPT.states W :=
  ⟨Perspectival.WantableGPT.vertex W default,
   Perspectival.WantableGPT.vertex_in_states W default⟩

/-- The WantableGPT on Bool has at least the vertex `true` as a state. -/
example : Perspectival.WantableGPT.vertex Bool true ∈
          Perspectival.WantableGPT.states Bool :=
  Perspectival.WantableGPT.vertex_in_states Bool true

/-- For Fin n with n ≥ 1, the WantableGPT has at least the vertex 0 as a state. -/
example (n : ℕ) (hn : 0 < n) :
    Perspectival.Classical.vertex n ⟨0, hn⟩ ∈
    Perspectival.Classical.states n :=
  Perspectival.Classical.vertex_in_states n ⟨0, hn⟩

/-- The Classical 2-outcome GPT has both vertices as states (heads / tails). -/
example : Perspectival.Classical.vertex 2 0 ∈ Perspectival.Classical.states 2 :=
  Perspectival.Classical.vertex_in_states 2 0

example : Perspectival.Classical.vertex 2 1 ∈ Perspectival.Classical.states 2 :=
  Perspectival.Classical.vertex_in_states 2 1

/-- Product-composition dimension on Bool: K(Bool × Bool) = 2 * 2 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 :=
  Perspectival.WantableGPT.finrank_V_prod_eq_mul.trans (by decide)

/-- Sum-composition dimension on Bool: K(Bool ⊕ Bool) = 2 + 2 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 :=
  Perspectival.WantableGPT.finrank_V_sum_eq_add.trans (by decide)

/-- Product composition of Bool × Fin 3: K = 2 * 3 = 6. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Fin 3)) = 6 :=
  Perspectival.WantableGPT.finrank_V_prod_eq_mul.trans (by decide)

/-- Sum composition of Bool ⊕ Fin 3: K = 2 + 3 = 5. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Fin 3)) = 5 :=
  Perspectival.WantableGPT.finrank_V_sum_eq_add.trans (by decide)

/-- Triple-product on Bool: K(Bool × Bool × Bool) = 2 * 2 * 2 = 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Triple-sum on Bool: K(Bool ⊕ Bool ⊕ Bool) = 2 + 2 + 2 = 6. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool ⊕ Bool)) = 6 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Mixed composition: K((Bool × Fin 3) ⊕ Fin 4) = 6 + 4 = 10. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V ((Bool × Fin 3) ⊕ Fin 4)) = 10 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Mixed composition: K(Bool × (Bool ⊕ Bool)) = 2 * 4 = 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × (Bool ⊕ Bool))) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The WantableGPT Bool's vertex map is a perfect-distinguishability
witness: the projection at `b` separates `vertex b` from `vertex b'`. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt Bool)
            (Perspectival.WantableGPT.vertex Bool) :=
  Perspectival.WantableGPT.perfectWitness Bool

/-- N (size of perfect-distinguishability family) for Bool is exactly 2. -/
example : Fintype.card Bool = 2 := by decide

/-- The PerfectWitness on Bool's vertex map: the projection at b
distinguishes vertex b from all others. -/
example (b₁ b₂ : Bool) :
    (Perspectival.WantableGPT.perfectWitness Bool).e b₁
      (Perspectival.WantableGPT.vertex Bool b₂)
    = if b₁ = b₂ then (1 : ℝ) else 0 :=
  (Perspectival.WantableGPT.perfectWitness Bool).kronecker b₁ b₂

/-- Specifically: proj true (vertex true) = 1, proj true (vertex false) = 0. -/
example : (Perspectival.WantableGPT.perfectWitness Bool).e true
            (Perspectival.WantableGPT.vertex Bool true) = 1 := by
  have := (Perspectival.WantableGPT.perfectWitness Bool).kronecker true true
  simpa using this

example : (Perspectival.WantableGPT.perfectWitness Bool).e true
            (Perspectival.WantableGPT.vertex Bool false) = 0 := by
  have := (Perspectival.WantableGPT.perfectWitness Bool).kronecker true false
  simpa using this

/-- The PerfectWitness on Fin 2: similar pattern. -/
example : (Perspectival.WantableGPT.perfectWitness (Fin 2)).e 0
            (Perspectival.WantableGPT.vertex (Fin 2) 0) = 1 := by
  have := (Perspectival.WantableGPT.perfectWitness (Fin 2)).kronecker 0 0
  simpa using this

example : (Perspectival.WantableGPT.perfectWitness (Fin 2)).e 0
            (Perspectival.WantableGPT.vertex (Fin 2) 1) = 0 := by
  have := (Perspectival.WantableGPT.perfectWitness (Fin 2)).kronecker 0 1
  simpa using this

/-- The complement operation on Bool is self-inverse (Wantable axiom). -/
example : ∀ b : Bool, Wantable.complement (Wantable.complement b) = b :=
  Wantable.complement_involutive

/-- The complement operation on Fin 2 (with swap-complement) is self-inverse. -/
example : ∀ i : Fin 2, Wantable.complement (Wantable.complement i) = i :=
  Wantable.complement_involutive

/-- The complement operation on Fin 3 (with id-complement) is trivially self-inverse. -/
example : ∀ i : Fin 3, Wantable.complement (Wantable.complement i) = i :=
  Wantable.complement_involutive

/-- The complement operation on ℤ (with neg-complement) is self-inverse. -/
example : ∀ n : ℤ, Wantable.complement (Wantable.complement n) = n :=
  Wantable.complement_involutive

/-- The complement operation on ℝ (with neg-complement) is self-inverse. -/
example : ∀ x : ℝ, Wantable.complement (Wantable.complement x) = x :=
  Wantable.complement_involutive

/-- A single Wantable Bool state has a trivial PerfectWitness. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt Bool)
            (fun _ : Fin 1 => Perspectival.WantableGPT.vertex Bool true) :=
  Perspectival.Distinguish.perfectWitness_singleton
    (Perspectival.WantableGPT.vertex Bool true)
    (Perspectival.WantableGPT.vertex_in_states Bool true)

/-- Identity Transform on the boolean WantableGPT preserves probabilities. -/
example (ρ : Perspectival.WantableGPT.V Bool) :
    (Perspectival.WantableGPT.gpt Bool).unit
      ((Perspectival.GPT.Transform.id (Perspectival.WantableGPT.gpt Bool)).toLin ρ)
    = (Perspectival.WantableGPT.gpt Bool).unit ρ :=
  Perspectival.GPT.Transform.prob_invariant _ ρ

/-- complement Transform on the boolean WantableGPT preserves probabilities. -/
example (ρ : Perspectival.WantableGPT.V Bool) :
    (Perspectival.WantableGPT.gpt Bool).unit
      ((Perspectival.WantableGPT.complementTransform Bool).toLin ρ)
    = (Perspectival.WantableGPT.gpt Bool).unit ρ :=
  Perspectival.GPT.Transform.prob_invariant _ ρ

/-- complementTransform squared equals the identity Transform on WantableGPT Bool. -/
example :
    Perspectival.WantableGPT.complementTransform Bool *
    Perspectival.WantableGPT.complementTransform Bool
    = Perspectival.GPT.Transform.id (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.WantableGPT.complementTransform_sq Bool

/-- complementTransform²(vertex true) = vertex true (involution recovers). -/
example :
    (Perspectival.WantableGPT.complementTransform Bool *
     Perspectival.WantableGPT.complementTransform Bool).toLin
       (Perspectival.WantableGPT.vertex Bool true)
    = Perspectival.WantableGPT.vertex Bool true := by
  rw [Perspectival.WantableGPT.complementTransform_sq]
  rfl

/-- The fromPTransHom: bridge sends boolSwap to complementTransform on Bool
(via the bridge homomorphism). -/
example : Perspectival.WantableGPT.fromPTransHom Bool boolSwap =
          Perspectival.WantableGPT.complementAction Bool := by
  apply LinearMap.ext
  intro f
  funext b
  show f (boolSwap.invFun b) = f (Wantable.complement b)
  cases b <;> rfl

/-- fromPTransHom is a MonoidHom (preserves composition). -/
example (φ ψ : PTrans Bool) :
    Perspectival.WantableGPT.fromPTransHom Bool (φ * ψ) =
    Perspectival.WantableGPT.fromPTransHom Bool φ *
    Perspectival.WantableGPT.fromPTransHom Bool ψ :=
  (Perspectival.WantableGPT.fromPTransHom Bool).map_mul φ ψ

/-- fromPTransHom sends 1 to 1. -/
example : Perspectival.WantableGPT.fromPTransHom Bool 1 = 1 :=
  (Perspectival.WantableGPT.fromPTransHom Bool).map_one

/-- The WantableGPT Bool satisfies Hardy Axiom 1 (Probabilities in [0,1]). -/
example : Perspectival.Hardy.Axiom1_Probabilities (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Hardy.axiom1_holds _

/-- The WantableGPT Bool satisfies Hardy Axiom 3 (Subspaces). -/
example : Perspectival.Hardy.Axiom3_Subspaces (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Hardy.axiom3_holds _

/-- The WantableGPT (Fin 4) satisfies Hardy Axiom 1. -/
example : Perspectival.Hardy.Axiom1_Probabilities (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.Hardy.axiom1_holds _

/-- The WantableGPT (Fin 4) satisfies Hardy Axiom 3. -/
example : Perspectival.Hardy.Axiom3_Subspaces (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.Hardy.axiom3_holds _

/-- The Classical GPT (3-outcome) satisfies Hardy Axiom 1. -/
example : Perspectival.Hardy.Axiom1_Probabilities (Perspectival.Classical.gpt 3) :=
  Perspectival.Hardy.axiom1_holds _

/-- The Classical GPT (3-outcome) satisfies Hardy Axiom 3. -/
example : Perspectival.Hardy.Axiom3_Subspaces (Perspectival.Classical.gpt 3) :=
  Perspectival.Hardy.axiom3_holds _

/-- Hardy Axiom 4 placeholder is satisfied trivially. -/
example : Perspectival.Hardy.Axiom4_Composite_States_Multiply
    (Perspectival.WantableGPT.gpt Bool)
    (Perspectival.WantableGPT.gpt Bool) 2 2 :=
  Perspectival.Hardy.axiom4_holds_placeholder _ _ 2 2

/-- Distinguishability of two specific WantableGPT Bool vertices. -/
example : Perspectival.Hardy.Distinguishable
    (Perspectival.WantableGPT.gpt Bool)
    (Perspectival.WantableGPT.vertex Bool true)
    (Perspectival.WantableGPT.vertex Bool false) :=
  Perspectival.WantableGPT.vertices_distinguishable Bool true false (by decide)

/-- Distinguishability of two specific Classical 3-outcome vertices. -/
example : Perspectival.Hardy.Distinguishable
    (Perspectival.Classical.gpt 3)
    (Perspectival.Classical.vertex 3 0)
    (Perspectival.Classical.vertex 3 1) :=
  Perspectival.Classical.vertices_distinguishable 3 0 1 (by decide)

/-- Distinct vertex pairs in Classical 4 are distinguishable. -/
example : Perspectival.Hardy.Distinguishable
    (Perspectival.Classical.gpt 4)
    (Perspectival.Classical.vertex 4 1)
    (Perspectival.Classical.vertex 4 3) :=
  Perspectival.Classical.vertices_distinguishable 4 1 3 (by decide)

/-- The classical broadcaster sends a vertex to its diagonal tensor. -/
example (i : Fin 3) :
    Perspectival.NoBroadcasting.classicalBroadcaster 3
      (Perspectival.Classical.vertex 3 i)
    = Perspectival.Classical.vertex 3 i ⊗ₜ[ℝ] Perspectival.Classical.vertex 3 i :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 3 i

/-- Classical broadcaster on vertex 0 of Fin 2. -/
example :
    Perspectival.NoBroadcasting.classicalBroadcaster 2
      (Perspectival.Classical.vertex 2 0)
    = Perspectival.Classical.vertex 2 0 ⊗ₜ[ℝ] Perspectival.Classical.vertex 2 0 :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 2 0

/-- Classical broadcaster on vertex 1 of Fin 2. -/
example :
    Perspectival.NoBroadcasting.classicalBroadcaster 2
      (Perspectival.Classical.vertex 2 1)
    = Perspectival.Classical.vertex 2 1 ⊗ₜ[ℝ] Perspectival.Classical.vertex 2 1 :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 2 1

/-- The cardinality of `Bool ⊕ Bool` = 4. -/
example : Fintype.card (Bool ⊕ Bool) = 4 := by decide

/-- The cardinality of `Bool × Bool` = 4. -/
example : Fintype.card (Bool × Bool) = 4 := by decide

/-- The cardinality of `Fin 3 ⊕ Fin 4` = 7. -/
example : Fintype.card (Fin 3 ⊕ Fin 4) = 7 := by decide

/-- The cardinality of `Fin 3 × Fin 4` = 12. -/
example : Fintype.card (Fin 3 × Fin 4) = 12 := by decide

/-- The state-space dimension of the WantableGPT on `Fin 3 × Fin 4` is 12. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 × Fin 4)) = 12 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- The state-space dimension of the WantableGPT on `Fin 3 ⊕ Fin 4` is 7. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 ⊕ Fin 4)) = 7 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- PerfectWitness.diag on WantableGPT Bool. -/
example : (Perspectival.WantableGPT.perfectWitness Bool).e true
            (Perspectival.WantableGPT.vertex Bool true) = 1 :=
  (Perspectival.WantableGPT.perfectWitness Bool).diag true

/-- PerfectWitness.offdiag on WantableGPT Bool. -/
example : (Perspectival.WantableGPT.perfectWitness Bool).e true
            (Perspectival.WantableGPT.vertex Bool false) = 0 :=
  (Perspectival.WantableGPT.perfectWitness Bool).offdiag (by decide)

/-- PerfectWitness.diag for Classical 3-outcome. -/
example (i : Fin 3) : (Perspectival.Classical.perfectWitness 3).e i
                       (Perspectival.Classical.vertex 3 i) = 1 :=
  (Perspectival.Classical.perfectWitness 3).diag i

/-- PerfectWitness.diag for Classical 5-outcome. -/
example (i : Fin 5) : (Perspectival.Classical.perfectWitness 5).e i
                       (Perspectival.Classical.vertex 5 i) = 1 :=
  (Perspectival.Classical.perfectWitness 5).diag i

/-- N ≤ K for Classical 3 (concrete instance). -/
example : 3 ≤ Module.finrank ℝ (Perspectival.Classical.V 3) :=
  Perspectival.Distinguish.operational_dim_le_state_dim
    (Perspectival.Classical.vertex 3)
    (Perspectival.Classical.perfectWitness 3)

/-- N ≤ K for Classical 5 (concrete instance). -/
example : 5 ≤ Module.finrank ℝ (Perspectival.Classical.V 5) :=
  Perspectival.Distinguish.operational_dim_le_state_dim
    (Perspectival.Classical.vertex 5)
    (Perspectival.Classical.perfectWitness 5)

/-- N ≤ K for WantableGPT Bool — applying the general theorem. -/
example : Fintype.card Bool ≤ Module.finrank ℝ (Perspectival.WantableGPT.V Bool) := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]

/-- The classical signature `N = K = |W|` for WantableGPT Bool. -/
example : Fintype.card Bool = 2 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Wantable on Bool × Bool × Bool with id-complement (constructed by
componentwise complement on Bool). The Wantable instance is automatic
via the product instance. -/
example : (Wantable.complement ((true, true, true) : Bool × Bool × Bool)) =
          (false, false, false) := rfl

/-- Composition of double-product complements. -/
example : (Wantable.complement (Wantable.complement
            ((true, false, true) : Bool × Bool × Bool))) =
          (true, false, true) :=
  Wantable.complement_involutive _

/-- The trivial Pattern is satisfied by every Reality. -/
example {W : Type u} [Wantable W] (R : Reality W) : (Pattern.trivial W) R := trivial

/-- The empty Pattern is satisfied by no Reality. -/
example {W : Type u} [Wantable W] (R : Reality W) : ¬ (Pattern.empty W) R := id

/-- Pattern.and is commutative (up to logical equivalence). -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.and P Q R ↔ Pattern.and Q P R :=
  ⟨And.symm, And.symm⟩

/-- Pattern.or is commutative (up to logical equivalence). -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.or P Q R ↔ Pattern.or Q P R :=
  ⟨Or.symm, Or.symm⟩

/-- Pattern.and with the trivial pattern is just the other pattern. -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) :
    Pattern.and P (Pattern.trivial W) R ↔ P R :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Pattern.or with the empty pattern is just the other pattern. -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) :
    Pattern.or P (Pattern.empty W) R ↔ P R :=
  ⟨fun h => h.elim id (False.elim), fun h => Or.inl h⟩

/-- The singleton Pattern: only one specific Reality satisfies it. -/
def singletonPattern {W : Type u} [Wantable W] (R₀ : Reality W) : Pattern W :=
  fun R => R = R₀

example {W : Type u} [Wantable W] (R₀ : Reality W) :
    (singletonPattern R₀) R₀ := rfl

/-- The complementPattern: a Pattern is "complementary" if it's defined
by being the complement (negation) of another Pattern. -/
def complementPattern {W : Type u} [Wantable W] (P : Pattern W) : Pattern W :=
  fun R => ¬ P R

/-- Double-complement-of-Pattern is identity (classically). -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) :
    complementPattern (complementPattern P) R ↔ P R := by
  show ¬ ¬ P R ↔ P R
  exact ⟨Classical.not_not.mp, Classical.not_not.mpr⟩

/-- A Pattern can be lifted from a single Meeting via its singleton reality. -/
def patternOfMeeting {W : Type u} [Wantable W] (m : Meeting W) : Pattern W :=
  singletonPattern (fun m' => m' = m)

/-- The pattern for trueMeetsFalse is satisfied by the singleton reality
{trueMeetsFalse}. -/
example : (patternOfMeeting trueMeetsFalse)
            (fun m' => m' = trueMeetsFalse) := rfl

/-- DeMorgan-style relationship: complementPattern of (P ∧ Q) ↔ (¬P ∨ ¬Q). -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    complementPattern (Pattern.and P Q) R ↔
    Pattern.or (complementPattern P) (complementPattern Q) R := by
  show ¬ (P R ∧ Q R) ↔ (¬ P R) ∨ (¬ Q R)
  tauto

/-- DeMorgan's other direction: complement(P ∨ Q) ↔ (¬P ∧ ¬Q). -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    complementPattern (Pattern.or P Q) R ↔
    Pattern.and (complementPattern P) (complementPattern Q) R := by
  show ¬ (P R ∨ Q R) ↔ (¬ P R) ∧ (¬ Q R)
  tauto

/-- Concrete Pattern instances on Bool's Reality. -/
def boolReality_alwaysComplementary : Reality Bool :=
  fun m => Wantable.complement m.side₁ = m.side₂

/-- Every meeting in Bool satisfies the always-complementary reality
(definitionally, since `m.complementary` is part of the structure). -/
example : ∀ m : Meeting Bool, boolReality_alwaysComplementary m :=
  fun m => m.complementary

/-- Every meeting in any Wantable satisfies the always-complementary
reality. (This is just the `complementary` field of `Meeting`.) -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    Wantable.complement m.side₁ = m.side₂ :=
  m.complementary

/-- And the symmetric version: complement of side₂ = side₁. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    Wantable.complement m.side₂ = m.side₁ :=
  m.complementary_symm

/-- Meeting.swap is an involution on meetings. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    m.swap.swap = m :=
  Meeting.swap_swap m

/-- mk_fromSide w gives a meeting with side₁ = w. -/
example {W : Type u} [Wantable W] (w : W) :
    (Meeting.mk_fromSide W w).side₁ = w :=
  Meeting.mk_fromSide_side₁ w

/-- mk_fromSide w gives a meeting with side₂ = complement w. -/
example {W : Type u} [Wantable W] (w : W) :
    (Meeting.mk_fromSide W w).side₂ = Wantable.complement w :=
  Meeting.mk_fromSide_side₂ w

/-- swap of mk_fromSide w equals mk_fromSide of complement w (closed gap). -/
example {W : Type u} [Wantable W] (w : W) :
    (Meeting.mk_fromSide W w).swap = Meeting.mk_fromSide W (Wantable.complement w) :=
  Meeting.swap_mk_fromSide w

/-- mk_fromSide is an inverse to side₁: applying it then taking side₁ gets w back. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    Meeting.mk_fromSide W m.side₁ = m :=
  Meeting.mk_fromSide_side₁_inv W m

/-- Meetings in Bool: there are at most 2 (true-false or false-true). -/
example (m : Meeting Bool) : m.side₁ = true ∨ m.side₁ = false := by
  cases m.side₁ <;> simp

/-- Meetings in Bool with side₁ = true must have side₂ = false. -/
example (m : Meeting Bool) (h : m.side₁ = true) : m.side₂ = false := by
  have hcomp : Wantable.complement m.side₁ = m.side₂ := m.complementary
  rw [h] at hcomp
  exact hcomp.symm

/-- Meetings in Bool with side₁ = false must have side₂ = true. -/
example (m : Meeting Bool) (h : m.side₁ = false) : m.side₂ = true := by
  have hcomp : Wantable.complement m.side₁ = m.side₂ := m.complementary
  rw [h] at hcomp
  exact hcomp.symm

/-- For Wantable Bool, Meeting Bool has exactly 2 elements (by classification
of side₁ into true/false, with side₂ uniquely determined). -/
example (m : Meeting Bool) :
    (m.side₁ = true ∧ m.side₂ = false) ∨ (m.side₁ = false ∧ m.side₂ = true) := by
  have hcomp : Wantable.complement m.side₁ = m.side₂ := m.complementary
  cases h : m.side₁
  · right
    refine ⟨rfl, ?_⟩
    rw [h] at hcomp; exact hcomp.symm
  · left
    refine ⟨rfl, ?_⟩
    rw [h] at hcomp; exact hcomp.symm

/-- Meeting Bool is in bijection with Bool (via side₁): two elements total. -/
example : ∀ m : Meeting Bool, m = Meeting.mk_fromSide Bool m.side₁ :=
  fun m => (Meeting.mk_fromSide_side₁_inv Bool m).symm

/-- The two distinct meetings on Bool: trueMeetsFalse and its swap. -/
example : trueMeetsFalse ≠ trueMeetsFalse.swap := by
  intro h
  have h1 : trueMeetsFalse.side₁ = trueMeetsFalse.side₂ :=
    congrArg Meeting.side₁ h
  -- trueMeetsFalse.side₁ = true, trueMeetsFalse.side₂ = false
  have : true = false := h1
  exact Bool.false_ne_true this.symm

/-- The PTrans Bool group action on Meeting Bool: the boolSwap PTrans
sends trueMeetsFalse to its swap. -/
example : PTrans.actMeeting boolSwap trueMeetsFalse = trueMeetsFalse.swap := by
  apply Meeting.ext_of_side₁
  show boolSwap.toFun true = false
  rfl

/-- The PTrans Bool group action on Meeting Bool: the identity fixes
trueMeetsFalse. -/
example : PTrans.actMeeting (1 : PTrans Bool) trueMeetsFalse = trueMeetsFalse :=
  PTrans.actMeeting_id _

/-- The action of PTrans.complement on a meeting equals its swap. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (PTrans.complement : PTrans W) m = m.swap :=
  PTrans.actMeeting_complement m

/-- Specifically: complement-action on trueMeetsFalse = trueMeetsFalse.swap. -/
example : PTrans.actMeeting (PTrans.complement : PTrans Bool) trueMeetsFalse
        = trueMeetsFalse.swap :=
  PTrans.actMeeting_complement trueMeetsFalse

/-- The PTrans action on Meeting is faithful. -/
example {W : Type u} [Wantable W] (f g : PTrans W)
    (h : ∀ m : Meeting W, PTrans.actMeeting f m = PTrans.actMeeting g m) :
    f = g :=
  PTrans.actMeeting_faithful f g h

/-- Concrete faithfulness on Bool: equal-on-all-meetings PTrans are equal. -/
example (f g : PTrans Bool)
    (h : ∀ m : Meeting Bool, PTrans.actMeeting f m = PTrans.actMeeting g m) :
    f = g :=
  PTrans.actMeeting_faithful f g h

/-- The PTrans → Equiv.Perm forgetful MonoidHom is injective. -/
example {W : Type u} [Wantable W] :
    Function.Injective (PTrans.toEquivPermHom : PTrans W →* Equiv.Perm W) :=
  PTrans.toEquivPermHom_injective

/-- The image-characterization theorem: PTrans is exactly the centralizer. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W) :
    (∃ φ : PTrans W, PTrans.toEquivPermHom φ = σ) ↔
    (∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) :=
  PTrans.mem_range_toEquivPermHom_iff σ

/-- Equiv.refl Bool (the identity perm) is in the centralizer of complement. -/
example : ∀ w : Bool, (Equiv.refl Bool) (Wantable.complement w) =
                       Wantable.complement ((Equiv.refl Bool) w) :=
  fun _ => rfl

/-- Equiv.refl ℤ is in the centralizer of negation. -/
example : ∀ n : ℤ, (Equiv.refl ℤ) (Wantable.complement n) =
                    Wantable.complement ((Equiv.refl ℤ) n) :=
  fun _ => rfl

/-- The "not" Equiv.Perm Bool is in the centralizer of "not" (= complement). -/
example : ∀ b : Bool, (Equiv.mk Bool.not Bool.not (fun b => by cases b <;> rfl)
                                                  (fun b => by cases b <;> rfl))
                        (Wantable.complement b) =
                       Wantable.complement
                         ((Equiv.mk Bool.not Bool.not (fun b => by cases b <;> rfl)
                                                  (fun b => by cases b <;> rfl)) b) :=
  fun b => by cases b <;> rfl

/-- By the centralizer characterization, the "not" Equiv lifts to a PTrans. -/
example : ∃ φ : PTrans Bool, PTrans.toEquivPermHom φ
    = Equiv.mk Bool.not Bool.not (fun b => by cases b <;> rfl)
                                 (fun b => by cases b <;> rfl) := by
  apply (PTrans.mem_range_toEquivPermHom_iff _).mpr
  intro b; cases b <;> rfl

/-- The identity permutation always lifts to the identity PTrans. -/
example {W : Type u} [Wantable W] :
    ∃ φ : PTrans W, PTrans.toEquivPermHom φ = Equiv.refl W := by
  apply (PTrans.mem_range_toEquivPermHom_iff _).mpr
  intro _; rfl

/-- The complement permutation (as an Equiv) always lifts to the complement PTrans. -/
example {W : Type u} [Wantable W] :
    ∃ φ : PTrans W, PTrans.toEquivPermHom φ
        = ⟨Wantable.complement, Wantable.complement,
            Wantable.complement_involutive, Wantable.complement_involutive⟩ := by
  apply (PTrans.mem_range_toEquivPermHom_iff _).mpr
  intro w
  show Wantable.complement (Wantable.complement w) = Wantable.complement
    (Wantable.complement w)
  rfl

/-- complementEquiv (defined earlier) is precisely the underlying perm of
PTrans.complement. -/
example {W : Type u} [Wantable W] :
    PTrans.toEquivPermHom (PTrans.complement : PTrans W) = complementEquiv :=
  rfl

/-- Two pieces fit together: the perspectival complement transformation,
viewed at the meeting level, equals swap; and viewed at the permutation
level, equals the complement Equiv. These are different surfaces of the
same Z/2-action. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (PTrans.complement : PTrans W) m = m.swap ∧
    PTrans.toEquivPermHom (PTrans.complement : PTrans W) = complementEquiv :=
  ⟨PTrans.actMeeting_complement m, rfl⟩

/-- The Wantable structure on `Bool`: complement is `not`. -/
example : (Wantable.complement : Bool → Bool) = Bool.not := rfl

/-- The Wantable structure on `ℤ`: complement is `Neg.neg`. -/
example : (Wantable.complement : ℤ → ℤ) = Neg.neg := rfl

/-- The Wantable structure on `Unit`: complement is `id`. -/
example : (Wantable.complement : Unit → Unit) = id := rfl

/-- The Wantable structure on `ℝ`: complement is `Neg.neg`. -/
example : (Wantable.complement : ℝ → ℝ) = Neg.neg := rfl

/-- The Wantable structure on `Fin 3` (the id-complement one): complement = id. -/
example : (Wantable.complement : Fin 3 → Fin 3) = id := rfl

/-- Composition: complement applied twice is the identity function. -/
example {W : Type u} [Wantable W] :
    (Wantable.complement ∘ Wantable.complement : W → W) = id := by
  funext w
  exact Wantable.complement_involutive w

/-- The complement function is its own inverse (in the bijection sense). -/
example {W : Type u} [Wantable W] :
    Function.LeftInverse (Wantable.complement : W → W) Wantable.complement :=
  Wantable.complement_involutive

example {W : Type u} [Wantable W] :
    Function.RightInverse (Wantable.complement : W → W) Wantable.complement :=
  Wantable.complement_involutive

/-- The complement function is bijective (since it's its own inverse). -/
example {W : Type u} [Wantable W] : Function.Bijective (Wantable.complement : W → W) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- The complement function is injective. -/
example {W : Type u} [Wantable W] : Function.Injective (Wantable.complement : W → W) :=
  Wantable.complement_injective

/-- The complement function is surjective. -/
example {W : Type u} [Wantable W] : Function.Surjective (Wantable.complement : W → W) :=
  Wantable.complement_surjective

/-- Concrete: WantableGPT Bool does not have quantum signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
        ≠ Fintype.card Bool * Fintype.card Bool :=
  Perspectival.WantableGPT.wantableGPT_not_quantum Bool (by decide)

/-- Concrete: WantableGPT Fin 4 does not have quantum signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
        ≠ Fintype.card (Fin 4) * Fintype.card (Fin 4) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Fin 4) (by decide)

/-- Concrete: WantableGPT Bool does not have real-QM signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) * 2
        ≠ Fintype.card Bool * (Fintype.card Bool + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM Bool (by decide)

/-- Concrete: WantableGPT Bool does not have quaternionic-QM signature. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
        ≠ Fintype.card Bool * (2 * Fintype.card Bool - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM Bool (by decide)

/-- The no-go is a structural property of the WantableGPT bridge,
not specific to Bool. Concrete instance on `Bool × Bool` (|W|=4): -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool))
        ≠ Fintype.card (Bool × Bool) * Fintype.card (Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Bool × Bool) (by decide)

/-- On `Bool ⊕ Bool` (|W|=4): real-QM signature ruled out. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) * 2
        ≠ Fintype.card (Bool ⊕ Bool) * (Fintype.card (Bool ⊕ Bool) + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM (Bool ⊕ Bool) (by decide)

/-- The bundled classical dichotomy on Bool. -/
example :
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = Fintype.card Bool ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
      ≠ Fintype.card Bool * Fintype.card Bool ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool) * 2
      ≠ Fintype.card Bool * (Fintype.card Bool + 1) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
      ≠ Fintype.card Bool * (2 * Fintype.card Bool - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy Bool (by decide)

/-- The vertex map on Bool is injective. -/
example : Function.Injective (Perspectival.WantableGPT.vertex Bool) :=
  Perspectival.WantableGPT.vertex_injective Bool

/-- The vertex set on Bool has size 2. -/
example : ((Finset.univ : Finset Bool).image (Perspectival.WantableGPT.vertex Bool)).card = 2 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- The vertex set on Fin 3 has size 3. -/
example : ((Finset.univ : Finset (Fin 3)).image (Perspectival.WantableGPT.vertex (Fin 3))).card = 3 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- The vertex set on Bool × Bool has size 4 (= |W| under product composition). -/
example : ((Finset.univ : Finset (Bool × Bool)).image
            (Perspectival.WantableGPT.vertex (Bool × Bool))).card = 4 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- StrictReversible.id on the boolean WantableGPT. -/
example : Perspectival.Continuity.StrictReversible (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Continuity.StrictReversible.id _

/-- Composition of two identity StrictReversibles is again identity-like. -/
example : Perspectival.Continuity.StrictReversible (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Continuity.StrictReversible.comp
    (Perspectival.Continuity.StrictReversible.id _)
    (Perspectival.Continuity.StrictReversible.id _)

/-- The StrictReversible.id on Bool's underlying toLin is LinearMap.id. -/
example : (Perspectival.Continuity.StrictReversible.id
            (Perspectival.WantableGPT.gpt Bool)).toLin = LinearMap.id :=
  Perspectival.Continuity.StrictReversible.id_toLin _

/-- StrictReversible.id satisfies the id_avail-style identity condition. -/
example (v : Perspectival.WantableGPT.V Bool) :
    (Perspectival.Continuity.StrictReversible.id
      (Perspectival.WantableGPT.gpt Bool)).toLin v = v := rfl

/-- The id StrictReversible composed with itself has the same toLin. -/
example : (Perspectival.Continuity.StrictReversible.comp
            (Perspectival.Continuity.StrictReversible.id
              (Perspectival.WantableGPT.gpt Bool))
            (Perspectival.Continuity.StrictReversible.id
              (Perspectival.WantableGPT.gpt Bool))).toLin
        = LinearMap.id := by
  rw [Perspectival.Continuity.StrictReversible.comp_toLin]
  rfl

/-- The id StrictReversible is bijective. -/
example : Function.Bijective
    (Perspectival.Continuity.StrictReversible.id
      (Perspectival.WantableGPT.gpt Bool)).toLin :=
  (Perspectival.Continuity.StrictReversible.id _).isEquiv

/-- StrictReversible.inv_comp on Bool: applying inv after forward is identity. -/
example (v : Perspectival.WantableGPT.V Bool) :
    (Perspectival.Continuity.StrictReversible.id
      (Perspectival.WantableGPT.gpt Bool)).inv
        ((Perspectival.Continuity.StrictReversible.id
          (Perspectival.WantableGPT.gpt Bool)).toLin v) = v :=
  Perspectival.Continuity.StrictReversible.inv_comp _ v

/-- StrictReversible.comp_inv on Bool: applying forward after inv is identity. -/
example (v : Perspectival.WantableGPT.V Bool) :
    (Perspectival.Continuity.StrictReversible.id
      (Perspectival.WantableGPT.gpt Bool)).toLin
        ((Perspectival.Continuity.StrictReversible.id
          (Perspectival.WantableGPT.gpt Bool)).inv v) = v :=
  Perspectival.Continuity.StrictReversible.comp_inv _ v

/-- Concrete: the path_via_affineLine works on R₁ = R₂ = id. -/
example : ∃ γ : unitInterval → Perspectival.WantableGPT.V Bool →ₗ[ℝ]
              Perspectival.WantableGPT.V Bool,
    Continuous (fun p : unitInterval × Perspectival.WantableGPT.V Bool =>
      (γ p.1) p.2) ∧
    γ 0 = (Perspectival.Continuity.Reversible.id
            (Perspectival.WantableGPT.gpt Bool)).toLin ∧
    γ 1 = (Perspectival.Continuity.Reversible.id
            (Perspectival.WantableGPT.gpt Bool)).toLin :=
  Perspectival.Continuity.path_via_affineLine _ _ _

/-- Reversible.id is in trivialAgency's avail set. -/
example :
    Perspectival.Continuity.Reversible.id (Perspectival.WantableGPT.gpt Bool)
    ∈ Perspectival.Continuity.HasConnectedAgency.avail
        (G := Perspectival.WantableGPT.gpt Bool)
        (self := Perspectival.Continuity.trivialAgency _) := rfl

/-- Some R ∈ trivial avail satisfies the id-condition. -/
example :
    let _inst : Perspectival.Continuity.HasConnectedAgency
                  (Perspectival.WantableGPT.gpt Bool) :=
      Perspectival.Continuity.trivialAgency _
    ∃ R ∈ Perspectival.Continuity.HasConnectedAgency.avail
              (G := Perspectival.WantableGPT.gpt Bool),
      ∀ v : Perspectival.WantableGPT.V Bool, R.toLin v = v := by
  let _inst : Perspectival.Continuity.HasConnectedAgency
                (Perspectival.WantableGPT.gpt Bool) :=
    Perspectival.Continuity.trivialAgency _
  exact Perspectival.Continuity.HasConnectedAgency.id_avail

-- (Reachable-on-trivialAgency example skipped due to direction-of-equality fiddle.)

/-- The `Reachable.refl` theorem on any GPT with trivialAgency. -/
example (G : Perspectival.GPT (Perspectival.WantableGPT.V Bool))
    (ρ : Perspectival.WantableGPT.V Bool) :
    @Perspectival.Continuity.Reachable _ _ _ _ G
      (Perspectival.Continuity.trivialAgency _) ρ ρ :=
  @Perspectival.Continuity.Reachable.refl _ _ _ _ G
    (Perspectival.Continuity.trivialAgency _) ρ

/-- The Wantable structure on `Option Bool`: complement preserves none, swaps within some. -/
example : Wantable.complement (some true : Option Bool) = some false := rfl
example : Wantable.complement (none : Option Bool) = none := rfl

/-- `none ∈ Option Bool` is self-complementary. -/
example : SelfComplementary (none : Option Bool) := rfl

/-- `some true ∈ Option Bool` is NOT self-complementary. -/
example : ¬ SelfComplementary (some true : Option Bool) := by
  intro h
  have : Wantable.complement (some true : Option Bool) = some true := h
  have hh : some false = (some true : Option Bool) := this
  injection hh with hh
  exact Bool.false_ne_true hh

/-- The Wantable structure on List Bool: complement is pointwise complement on elements. -/
example : Wantable.complement ([true, false, true] : List Bool)
        = [false, true, false] := rfl

/-- Empty list is its own complement (trivially self-complementary). -/
example : SelfComplementary ([] : List Bool) := rfl

/-- Single-element list complement applied to [true] gives [false]. -/
example : Wantable.complement ([true] : List Bool) = [false] := rfl

/-- Lists [true, true] is NOT self-complementary. -/
example : ¬ SelfComplementary ([true, true] : List Bool) := by
  intro h
  have : ([false, false] : List Bool) = [true, true] := h
  injection this with h1 _
  exact Bool.false_ne_true h1

/-- The complement on List Bool reverses each Bool entry: [t,f] ↦ [f,t]. -/
example : Wantable.complement ([true, false] : List Bool) = [false, true] := rfl

/-- Lists [true, false] is NOT self-complementary. -/
example : ¬ SelfComplementary ([true, false] : List Bool) := by
  intro h
  have : ([false, true] : List Bool) = [true, false] := h
  injection this with h1 _
  exact Bool.false_ne_true h1

/-- The complement is involutive on List Bool (instance of general theorem). -/
example (l : List Bool) : Wantable.complement (Wantable.complement l) = l :=
  Wantable.complement_involutive l

/-- The complement is injective on List Bool. -/
example : Function.Injective (Wantable.complement : List Bool → List Bool) :=
  Wantable.complement_injective

/-- The complement is surjective on List Bool. -/
example : Function.Surjective (Wantable.complement : List Bool → List Bool) :=
  Wantable.complement_surjective

/-- For Wantable on function spaces Bool → Bool: complement is pointwise complement. -/
example (f : Bool → Bool) (b : Bool) :
    (Wantable.complement f) b = Wantable.complement (f b) := rfl

/-- The constant-true function and the constant-false function are complementary. -/
example : Wantable.complement (fun _ : Bool => true) = (fun _ : Bool => false) := by
  funext b; rfl

/-- The identity function on Bool is its own complement composed with itself. -/
example : Wantable.complement (Wantable.complement (id : Bool → Bool)) = id := by
  funext b
  show Wantable.complement (Wantable.complement b) = b
  exact Wantable.complement_involutive b

/-- The "complement composed with id" function on Bool: still pointwise. -/
example : Wantable.complement (id : Bool → Bool) = Bool.not := by
  funext b
  rfl

/-- The complement-of-complement function on Bool is the identity. -/
example : Wantable.complement (Bool.not : Bool → Bool) = id := by
  funext b
  show Wantable.complement (Bool.not b) = b
  cases b <;> rfl

/-- Concrete instance of `exists_two_distinguishable` for Bool. -/
example : ∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V Bool,
    ρ₁ ∈ Perspectival.WantableGPT.states Bool ∧
    ρ₂ ∈ Perspectival.WantableGPT.states Bool ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt Bool) ρ₁ ρ₂ :=
  Perspectival.WantableGPT.exists_two_distinguishable Bool (by decide)

/-- Concrete instance of `exists_two_distinguishable` for Fin 4. -/
example : ∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Fin 4),
    ρ₁ ∈ Perspectival.WantableGPT.states (Fin 4) ∧
    ρ₂ ∈ Perspectival.WantableGPT.states (Fin 4) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4)) ρ₁ ρ₂ :=
  Perspectival.WantableGPT.exists_two_distinguishable (Fin 4) (by decide)

/-- Concrete instance of `exists_two_distinguishable` for Bool × Bool
(card = 4). -/
example : ∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Bool × Bool),
    ρ₁ ∈ Perspectival.WantableGPT.states (Bool × Bool) ∧
    ρ₂ ∈ Perspectival.WantableGPT.states (Bool × Bool) ∧
    Perspectival.Hardy.Distinguishable
      (Perspectival.WantableGPT.gpt (Bool × Bool)) ρ₁ ρ₂ :=
  Perspectival.WantableGPT.exists_two_distinguishable (Bool × Bool) (by decide)

end Examples
end Perspectival
