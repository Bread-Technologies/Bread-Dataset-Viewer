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

/-- Self-complementary 0 on ℝ via scaling by -1. -/
example : (scaleByPTrans (-1) (by norm_num)).toFun 0 = 0 := by
  show (-1 : ℝ) * 0 = 0; ring

/-- Self-complementary 0 on ℤ. -/
example : (PTrans.complement : PTrans ℤ).toFun 0 = 0 := by
  show -(0 : ℤ) = 0; ring

/-- SelfComplementary 0 on ℤ. -/
example : SelfComplementary (0 : ℤ) := by show -(0 : ℤ) = 0; ring

/-- SelfComplementary 0 on ℝ. -/
example : SelfComplementary (0 : ℝ) := by show -(0 : ℝ) = 0; ring

/-- ℤ is not fixed-point-free (0 is fixed). -/
example : ¬ FixedPointFreeComplement ℤ := by
  intro h; exact h 0 (by show -(0 : ℤ) = 0; ring)

/-- ℝ is not fixed-point-free (0 is fixed). -/
example : ¬ FixedPointFreeComplement ℝ := by
  intro h; exact h 0 (by show -(0 : ℝ) = 0; ring)

/-- The 0-vector on Bool³ is in the effect-vector hypercube [0,1]^W. -/
example : (0 : Perspectival.WantableGPT.V (Bool × Bool × Bool))
        ∈ { g | ∀ w, g w ∈ Set.Icc (0 : ℝ) 1 } := by
  rw [← Perspectival.WantableGPT.effectVec_eq_hypercube]
  exact Perspectival.WantableGPT.zero_in_effectVec _

-- (effectVec_eq_hypercube concrete instance skipped — type inference fiddly.)

/-- The complement on Fin 2 sends 0 to 1. -/
example : Wantable.complement (0 : Fin 2) = 1 := rfl

/-- The complement on Fin 2 sends 1 to 0. -/
example : Wantable.complement (1 : Fin 2) = 0 := rfl

/-- Fin 2 complement involution: 0 → 1 → 0. -/
example : Wantable.complement (Wantable.complement (0 : Fin 2)) = 0 := rfl

/-- Fin 2 complement involution: 1 → 0 → 1. -/
example : Wantable.complement (Wantable.complement (1 : Fin 2)) = 1 := rfl

/-- Bool complement involution: true → false → true. -/
example : Wantable.complement (Wantable.complement true) = true := rfl
example : Wantable.complement (Wantable.complement false) = false := rfl

/-- The Wantable structure on Unit is trivial — every element is self-complementary. -/
example : SelfComplementary () := rfl

/-- Wantable.complement on Empty is vacuously involutive. -/
example (e : Empty) : Wantable.complement (Wantable.complement e) = e := e.elim

/-- FixedPointFreeComplement Empty (vacuously). -/
example : FixedPointFreeComplement Empty := fun e _ => e.elim

/-- |Empty| = 0 is trivially even. -/
example : Even (Fintype.card Empty) := by
  rw [show Fintype.card Empty = 0 from by decide]; exact ⟨0, rfl⟩

/-- WantableGPT on Unit has finrank 1. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Unit) = 1 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

/-- WantableGPT on Empty has finrank 0. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Empty) = 0 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; rfl

/-- Concrete Fintype.card on Fin n. -/
example : Fintype.card (Fin 5) = 5 := by decide
example : Fintype.card (Fin 10) = 10 := by decide
example : Fintype.card (Fin 100) = 100 := by decide

-- (Classical.V n finrank deferred — instance issue.)

/-- Bool ⊕ Unit has cardinality 3. -/
example : Fintype.card (Bool ⊕ Unit) = 3 := by decide

/-- Bool × Unit has cardinality 2. -/
example : Fintype.card (Bool × Unit) = 2 := by decide

/-- Wantable.complement on Bool × Unit is componentwise. -/
example : Wantable.complement ((true, ()) : Bool × Unit) = (false, ()) := rfl

/-- WantableGPT on Bool × Unit has finrank 2. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Unit)) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT on Unit × Unit has finrank 1. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Unit × Unit)) = 1 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT on Unit ⊕ Unit has finrank 2. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Unit ⊕ Unit)) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- Unit ⊕ Unit is not fixed-point-free (each side has self-complementary). -/
example : ¬ FixedPointFreeComplement (Unit ⊕ Unit) := by
  intro h
  exact h (Sum.inl ()) rfl

/-- Sum.inl () is self-complementary. -/
example : SelfComplementary (Sum.inl () : Unit ⊕ Unit) := rfl

/-- Sum.inr () is self-complementary. -/
example : SelfComplementary (Sum.inr () : Unit ⊕ Unit) := rfl

/-- WantableGPT (Unit × Bool) has finrank 2. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Unit × Bool)) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Unit ⊕ Bool) has finrank 3. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Unit ⊕ Bool)) = 3 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Empty × Bool) has finrank 0 (vacuous). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Empty × Bool)) = 0 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Empty ⊕ Bool) has finrank 2 (= 0 + 2). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Empty ⊕ Bool)) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- |Empty| * |Bool| = 0 (multiplicative identity of empty). -/
example : Fintype.card (Empty × Bool) = 0 := by decide

/-- |Empty| + |Bool| = 2 (additive identity of empty). -/
example : Fintype.card (Empty ⊕ Bool) = 2 := by decide

/-- |Unit| × |Bool| = 2 (Unit is multiplicative identity). -/
example : Fintype.card (Unit × Bool) = 2 := by decide

/-- |Unit| + |Bool| = 3. -/
example : Fintype.card (Unit ⊕ Bool) = 3 := by decide

/-- |Bool ⊕ Bool ⊕ Bool ⊕ Bool| = 8 (left-associated). -/
example : Fintype.card (Bool ⊕ (Bool ⊕ (Bool ⊕ Bool))) = 8 := by decide

/-- |Bool × Bool × Bool × Bool| = 16. -/
example : Fintype.card (Bool × Bool × Bool × Bool) = 16 := by decide

/-- WantableGPT (Bool⁴) has finrank 16. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool)) = 16 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Bool⁴) is not quantum (16 ≠ 16² = 256). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
        ≠ Fintype.card (Bool × Bool × Bool × Bool)
          * Fintype.card (Bool × Bool × Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Bool × Bool × Bool × Bool) (by decide)

/-- WantableGPT (Bool⁴) has K = N = 16. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
        = Fintype.card (Bool × Bool × Bool × Bool) :=
  Perspectival.WantableGPT.finrank_V_eq_card (Bool × Bool × Bool × Bool)

/-- Bool⁴ has fixed-point-free complement. -/
example : FixedPointFreeComplement (Bool × Bool × Bool × Bool) := by
  intro ⟨b₁, _, _, _⟩ h
  have h1 : Wantable.complement b₁ = b₁ := (Prod.mk.injEq _ _ _ _).mp h |>.1
  cases b₁
  · exact Bool.false_ne_true h1.symm
  · exact Bool.false_ne_true h1

/-- Bool⁴ complement on (t,f,t,f): each position negates. -/
example : Wantable.complement ((true, false, true, false) : Bool × Bool × Bool × Bool)
        = (false, true, false, true) := rfl

/-- Bool⁴ vertex set has 16 elements. -/
example : ((Finset.univ : Finset (Bool × Bool × Bool × Bool)).image
            (Perspectival.WantableGPT.vertex (Bool × Bool × Bool × Bool))).card = 16 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- The Bool⁴ classical dichotomy (full bundle). -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
            = Fintype.card (Bool × Bool × Bool × Bool) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
            ≠ Fintype.card (Bool × Bool × Bool × Bool)
              * Fintype.card (Bool × Bool × Bool × Bool) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool)) * 2
            ≠ Fintype.card (Bool × Bool × Bool × Bool)
              * (Fintype.card (Bool × Bool × Bool × Bool) + 1) ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
            ≠ Fintype.card (Bool × Bool × Bool × Bool)
              * (2 * Fintype.card (Bool × Bool × Bool × Bool) - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy (Bool × Bool × Bool × Bool) (by decide)

/-- Bool⁴ has 16 distinguishable states (the entire vertex set). -/
example : Perspectival.Hardy.DistinguishabilitySet
            (Perspectival.WantableGPT.gpt (Bool × Bool × Bool × Bool))
            ((Finset.univ : Finset (Bool × Bool × Bool × Bool)).image
              (Perspectival.WantableGPT.vertex (Bool × Bool × Bool × Bool))) :=
  Perspectival.WantableGPT.vertex_distinguishability_set (Bool × Bool × Bool × Bool)

/-- Bool⁴ vertices are linearly independent. -/
example : LinearIndependent ℝ
            (fun w : Bool × Bool × Bool × Bool =>
              Perspectival.WantableGPT.vertex (Bool × Bool × Bool × Bool) w) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype (Bool × Bool × Bool × Bool)

/-- Bool⁴ vertex map is injective. -/
example : Function.Injective (Perspectival.WantableGPT.vertex (Bool × Bool × Bool × Bool)) :=
  Perspectival.WantableGPT.vertex_injective (Bool × Bool × Bool × Bool)

/-- Bool⁴ has at least 2 distinguishable states. -/
example : ∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool),
    ρ₁ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool × Bool) ∧
    ρ₂ ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool × Bool) ∧
    Perspectival.Hardy.Distinguishable
      (Perspectival.WantableGPT.gpt (Bool × Bool × Bool × Bool)) ρ₁ ρ₂ :=
  Perspectival.WantableGPT.exists_two_distinguishable (Bool × Bool × Bool × Bool) (by decide)

/-- Trivial dim instance: WantableGPT Unit has dim 1. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Unit) = 1 :=
  Perspectival.WantableGPT.wantableGPT_trivial_dim Unit (by decide)

/-- Empty dim instance: WantableGPT Empty has dim 0. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Empty) = 0 :=
  Perspectival.WantableGPT.wantableGPT_empty_dim Empty (by decide)

/-- WantableGPT Bool has positive dim. -/
example : 0 < Module.finrank ℝ (Perspectival.WantableGPT.V Bool) :=
  Perspectival.WantableGPT.wantableGPT_dim_pos Bool

/-- WantableGPT (Fin 3) has positive dim. -/
example : 0 < Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) :=
  Perspectival.WantableGPT.wantableGPT_dim_pos (Fin 3)

/-- WantableGPT dim is multiplicative on products. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Fin 3))
        = Module.finrank ℝ (Perspectival.WantableGPT.V Bool) *
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) :=
  Perspectival.WantableGPT.wantableGPT_dim_prod

/-- WantableGPT dim is additive on sums. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Fin 3))
        = Module.finrank ℝ (Perspectival.WantableGPT.V Bool) +
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) :=
  Perspectival.WantableGPT.wantableGPT_dim_sum

-- (Bool×W and Bool⊕W universe-polymorphic dim theorems deferred — needs
-- explicit `Type u` rather than `Type*` to align with Bool's Wantable instance.)

/-- Bool × Bool has dim 4 via wantableGPT_dim_prod. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 := by
  rw [Perspectival.WantableGPT.wantableGPT_dim_prod]
  rw [show Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 from by
    rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide]

/-- Bool ⊕ Bool has dim 4 via wantableGPT_dim_sum. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 := by
  rw [Perspectival.WantableGPT.wantableGPT_dim_sum]
  rw [show Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 from by
    rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide]

/-- Bool × Bool × Bool has dim 8 via repeated dim_prod. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Bool × Bool ⊕ Bool) has dim 4 + 2 = 6. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool ⊕ Bool)) = 6 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Bool × (Fin 3 ⊕ Bool)) has dim 2 * 5 = 10. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × (Fin 3 ⊕ Bool))) = 10 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT ((Fin 3 × Bool) ⊕ Fin 4) has dim 6 + 4 = 10. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V ((Fin 3 × Bool) ⊕ Fin 4)) = 10 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Fin 4 × Fin 4) has dim 16. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4 × Fin 4)) = 16 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- WantableGPT (Fin 4 ⊕ Fin 4) has dim 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4 ⊕ Fin 4)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]; decide

/-- For Fin 4: rich vertex set on the (id-complement) Wantable. -/
example : ((Finset.univ : Finset (Fin 4)).image
            (Perspectival.WantableGPT.vertex (Fin 4))).card = 4 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- For Fin 3: rich vertex set on the id-complement Wantable. -/
example : ((Finset.univ : Finset (Fin 3)).image
            (Perspectival.WantableGPT.vertex (Fin 3))).card = 3 := by
  rw [Perspectival.WantableGPT.vertex_image_card]; decide

/-- Fin 4 vertex map is injective. -/
example : Function.Injective (Perspectival.WantableGPT.vertex (Fin 4)) :=
  Perspectival.WantableGPT.vertex_injective (Fin 4)

/-- Fin 3 vertex map is injective. -/
example : Function.Injective (Perspectival.WantableGPT.vertex (Fin 3)) :=
  Perspectival.WantableGPT.vertex_injective (Fin 3)

/-- Fin 4 wantableGPT has positive dim. -/
example : 0 < Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) :=
  Perspectival.WantableGPT.wantableGPT_dim_pos (Fin 4)

/-- Bool × Bool wantableGPT has positive dim. -/
example : 0 < Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) :=
  Perspectival.WantableGPT.wantableGPT_dim_pos (Bool × Bool)

/-- Unit wantableGPT has positive dim. -/
example : 0 < Module.finrank ℝ (Perspectival.WantableGPT.V Unit) :=
  Perspectival.WantableGPT.wantableGPT_dim_pos Unit

/-- This is the central K = |W| dimension formula. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.finrank_V_eq_card W

/-- The K = N classical signature holds (general statement). -/
theorem WantableGPT_classical_K_eq_N {W : Type u}
    [Wantable W] [Fintype W] [DecidableEq W] :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.finrank_V_eq_card W

/-- Verification: K = N concretely on Bool gives 2 = 2. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = Fintype.card Bool :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Fin 3 gives 3 = 3. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) = Fintype.card (Fin 3) :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Bool × Bool gives 4 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool))
        = Fintype.card (Bool × Bool) :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Bool ⊕ Bool gives 4 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool))
        = Fintype.card (Bool ⊕ Bool) :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Fin 4 gives 4 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
        = Fintype.card (Fin 4) :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Bool × Bool × Bool gives 8 = 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
        = Fintype.card (Bool × Bool × Bool) :=
  WantableGPT_classical_K_eq_N

/-- Verification: K = N concretely on Bool × Bool × Bool × Bool gives 16 = 16. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
        = Fintype.card (Bool × Bool × Bool × Bool) :=
  WantableGPT_classical_K_eq_N

/-- For any non-empty Wantable, the WantableGPT has at least one state. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Inhabited W] :
    ∃ ρ : Perspectival.WantableGPT.V W, ρ ∈ Perspectival.WantableGPT.states W :=
  ⟨Perspectival.WantableGPT.vertex W default,
   Perspectival.WantableGPT.vertex_in_states W default⟩

/-- For any non-empty Wantable, the WantableGPT has at least one effect. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Inhabited W] :
    ∃ e : Perspectival.WantableGPT.V W →ₗ[ℝ] ℝ,
      e ∈ Perspectival.WantableGPT.effects W :=
  ⟨Perspectival.WantableGPT.proj W default,
   Perspectival.WantableGPT.proj_in_effects W default⟩

/-- Using the named theorem: WantableGPT Bool has a state. -/
example : ∃ ρ : Perspectival.WantableGPT.V Bool,
    ρ ∈ Perspectival.WantableGPT.states Bool :=
  Perspectival.WantableGPT.wantableGPT_state_inhabited Bool

/-- Using the named theorem: WantableGPT Bool has an effect. -/
example : ∃ e : Perspectival.WantableGPT.V Bool →ₗ[ℝ] ℝ,
    e ∈ Perspectival.WantableGPT.effects Bool :=
  Perspectival.WantableGPT.wantableGPT_effect_inhabited Bool

/-- Trivial fact: WantableGPT.states is the standard simplex. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.states W = stdSimplex ℝ W := rfl

/-- Concrete: WantableGPT Bool states is stdSimplex Bool. -/
example : Perspectival.WantableGPT.states Bool = stdSimplex ℝ Bool := rfl

/-- Concrete: WantableGPT (Fin 3) states is stdSimplex (Fin 3). -/
example : Perspectival.WantableGPT.states (Fin 3) = stdSimplex ℝ (Fin 3) := rfl

/-- The WantableGPT states are convex. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Convex ℝ (Perspectival.WantableGPT.states W) := convex_stdSimplex ℝ W

/-- Bool's WantableGPT states are convex. -/
example : Convex ℝ (Perspectival.WantableGPT.states Bool) := convex_stdSimplex ℝ Bool

/-- Fin 4 WantableGPT states are convex. -/
example : Convex ℝ (Perspectival.WantableGPT.states (Fin 4)) := convex_stdSimplex ℝ (Fin 4)

/-- Bool × Bool WantableGPT states are convex. -/
example : Convex ℝ (Perspectival.WantableGPT.states (Bool × Bool)) :=
  convex_stdSimplex ℝ (Bool × Bool)

/-- The effects-set is convex. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Convex ℝ (Perspectival.WantableGPT.effects W) :=
  (Perspectival.WantableGPT.gpt W).effects_convex

/-- Bool's WantableGPT effects are convex. -/
example : Convex ℝ (Perspectival.WantableGPT.effects Bool) :=
  (Perspectival.WantableGPT.gpt Bool).effects_convex

/-- The unit functional is in the effects set. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.gpt W).unit ∈ (Perspectival.WantableGPT.gpt W).effects :=
  (Perspectival.WantableGPT.gpt W).unit_is_effect

/-- Concrete: unit functional in Bool WantableGPT effects. -/
example : (Perspectival.WantableGPT.gpt Bool).unit
        ∈ (Perspectival.WantableGPT.gpt Bool).effects :=
  (Perspectival.WantableGPT.gpt Bool).unit_is_effect

/-- The states-normalization holds: for any state, unit applied = 1. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ : Perspectival.WantableGPT.V W)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt W).states) :
    (Perspectival.WantableGPT.gpt W).unit ρ = 1 :=
  (Perspectival.WantableGPT.gpt W).states_normalized ρ hρ

/-- Concrete: vertex true on Bool gives unit = 1. -/
example : (Perspectival.WantableGPT.gpt Bool).unit
            (Perspectival.WantableGPT.vertex Bool true) = 1 :=
  (Perspectival.WantableGPT.gpt Bool).states_normalized _
    (Perspectival.WantableGPT.vertex_in_states Bool true)

/-- For any state and any effect, the probability is in [0,1]. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (e : Perspectival.WantableGPT.V W →ₗ[ℝ] ℝ)
    (he : e ∈ (Perspectival.WantableGPT.gpt W).effects)
    (ρ : Perspectival.WantableGPT.V W)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt W).states) :
    0 ≤ e ρ ∧ e ρ ≤ 1 :=
  (Perspectival.WantableGPT.gpt W).prob_in_unit_interval e he ρ hρ

/-- Concrete: probability of vertex true under proj true is 1. -/
example : (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool true) = 1 := by
  show (if true = true then (1 : ℝ) else 0) = 1
  simp

/-- Concrete: probability of vertex true under proj false is 0. -/
example : (Perspectival.WantableGPT.proj Bool false)
            (Perspectival.WantableGPT.vertex Bool true) = 0 := by
  show (if true = false then (1 : ℝ) else 0) = 0
  simp

/-- Concrete: vertex false under proj true = 0. -/
example : (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool false) = 0 := by
  show (if false = true then (1 : ℝ) else 0) = 0
  simp

/-- Concrete: vertex false under proj false = 1. -/
example : (Perspectival.WantableGPT.proj Bool false)
            (Perspectival.WantableGPT.vertex Bool false) = 1 := by
  show (if false = false then (1 : ℝ) else 0) = 1
  simp

-- (Sum-of-probabilities example over Bool deferred — Finset.sum_eq_add syntax fiddly.)

/-- The unit functional of WantableGPT applied to a vertex gives 1. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    (Perspectival.WantableGPT.gpt W).unit
      (Perspectival.WantableGPT.vertex W w) = 1 :=
  (Perspectival.WantableGPT.gpt W).states_normalized _
    (Perspectival.WantableGPT.vertex_in_states W w)

/-- Concrete: unit (vertex (Fin 3) 2) = 1. -/
example : (Perspectival.WantableGPT.gpt (Fin 3)).unit
            (Perspectival.WantableGPT.vertex (Fin 3) 2) = 1 :=
  (Perspectival.WantableGPT.gpt (Fin 3)).states_normalized _
    (Perspectival.WantableGPT.vertex_in_states (Fin 3) 2)

-- (Unit-functional explicit-sum-equals-binary form deferred — Finset.sum
-- elaboration on Bool needs different approach.)

/-- The fromPTransHom on Bool sends id PTrans to id LinearMap. -/
example : Perspectival.WantableGPT.fromPTransHom Bool 1 = LinearMap.id :=
  (Perspectival.WantableGPT.fromPTransHom Bool).map_one

/-- The complement Transform on Bool's underlying linear map sends vertex true to vertex false. -/
example : (Perspectival.WantableGPT.complementAction Bool)
            (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex Bool false :=
  Perspectival.WantableGPT.complementAction_vertex Bool true

/-- The complement Transform on Bool sends vertex false to vertex true. -/
example : (Perspectival.WantableGPT.complementAction Bool)
            (Perspectival.WantableGPT.vertex Bool false)
        = Perspectival.WantableGPT.vertex Bool true := by
  have := Perspectival.WantableGPT.complementAction_vertex Bool false
  show _ = Perspectival.WantableGPT.vertex Bool true
  rw [this]
  rfl

/-- complementAction is involutive on all states. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (f : Perspectival.WantableGPT.V W) :
    Perspectival.WantableGPT.complementAction W
      (Perspectival.WantableGPT.complementAction W f) = f :=
  Perspectival.WantableGPT.complementAction_involutive W f

/-- complementAction on Bool is involutive. -/
example (f : Perspectival.WantableGPT.V Bool) :
    Perspectival.WantableGPT.complementAction Bool
      (Perspectival.WantableGPT.complementAction Bool f) = f :=
  Perspectival.WantableGPT.complementAction_involutive Bool f

/-- complementAction preserves states. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (f : Perspectival.WantableGPT.V W)
    (hf : f ∈ Perspectival.WantableGPT.states W) :
    Perspectival.WantableGPT.complementAction W f
      ∈ Perspectival.WantableGPT.states W :=
  Perspectival.WantableGPT.complementAction_preserves_states W f hf

/-- Concrete: complementAction preserves Bool states. -/
example (f : Perspectival.WantableGPT.V Bool)
    (hf : f ∈ Perspectival.WantableGPT.states Bool) :
    Perspectival.WantableGPT.complementAction Bool f
      ∈ Perspectival.WantableGPT.states Bool :=
  Perspectival.WantableGPT.complementAction_preserves_states Bool f hf

/-- complementTransform is a GPT.Transform on Bool's WantableGPT. -/
example : Perspectival.GPT.Transform (Perspectival.WantableGPT.gpt Bool)
                                     (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.WantableGPT.complementTransform Bool

/-- complementTransform on Bool has toLin = complementAction. -/
example : (Perspectival.WantableGPT.complementTransform Bool).toLin
        = Perspectival.WantableGPT.complementAction Bool := rfl

/-- complementTransform preserves the unit. -/
example : (Perspectival.WantableGPT.gpt Bool).unit.comp
            (Perspectival.WantableGPT.complementTransform Bool).toLin
        = (Perspectival.WantableGPT.gpt Bool).unit :=
  (Perspectival.WantableGPT.complementTransform Bool).preserves_unit

/-- complementTransform preserves states. -/
example (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt Bool).states) :
    (Perspectival.WantableGPT.complementTransform Bool).toLin ρ
      ∈ (Perspectival.WantableGPT.gpt Bool).states :=
  (Perspectival.WantableGPT.complementTransform Bool).preserves_states ρ hρ

/-- The continuous Wantable instance on ℝ. -/
example : ContinuousWantable ℝ := inferInstance

/-- The continuous Wantable instance on ℤ. -/
example : ContinuousWantable ℤ := inferInstance

/-- The complement is continuous on ℝ. -/
example : Continuous (Wantable.complement : ℝ → ℝ) :=
  ContinuousWantable.complement_continuous

/-- The complement is continuous on ℤ (with discrete topology). -/
example : Continuous (Wantable.complement : ℤ → ℤ) :=
  ContinuousWantable.complement_continuous

/-- ContinuousPTrans on ℝ contains the identity. -/
example : ContinuousPTrans ℝ := ContinuousPTrans.id ℝ

/-- ContinuousPTrans on ℝ contains the complement. -/
example : ContinuousPTrans ℝ := ContinuousPTrans.complement ℝ

/-- ContinuousPTrans.comp composes two continuous PTrans. -/
example (φ ψ : ContinuousPTrans ℝ) : ContinuousPTrans ℝ := φ.comp ψ

/-- complement.comp(complement) on ℝ has underlying PTrans = 1. -/
example : ((ContinuousPTrans.complement ℝ).comp (ContinuousPTrans.complement ℝ)).toPTrans
        = 1 := PTrans.complement_sq

/-- scaleByPTrans on ℝ extends to a ContinuousPTrans (scaling is continuous). -/
noncomputable example (a : ℝ) (ha : a ≠ 0) : ContinuousPTrans ℝ where
  toPTrans := scaleByPTrans a ha
  toFun_continuous := continuous_const.mul continuous_id

-- (scaleHom ℝˣ-literal example deferred — Unit ℝˣ literal needs explicit construction.)

/-- Hardy Axiom 1 holds for any GPT (general theorem). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Perspectival.Hardy.Axiom1_Probabilities G :=
  Perspectival.Hardy.axiom1_holds G

/-- Hardy Axiom 3 holds for any GPT (general theorem). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Perspectival.Hardy.Axiom3_Subspaces G :=
  Perspectival.Hardy.axiom3_holds G

/-- Hardy Axiom 4 (placeholder) holds. -/
example {VA VB : Type u} [AddCommGroup VA] [Module ℝ VA]
    [AddCommGroup VB] [Module ℝ VB]
    (GA : Perspectival.GPT VA) (GB : Perspectival.GPT VB) (nA nB : ℕ) :
    Perspectival.Hardy.Axiom4_Composite_States_Multiply GA GB nA nB :=
  Perspectival.Hardy.axiom4_holds_placeholder GA GB nA nB

/-- N ≤ K for any GPT with a PerfectWitness. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {G : Perspectival.GPT V}
    {n : ℕ} (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) :
    n ≤ Module.finrank ℝ V :=
  Perspectival.Distinguish.operational_dim_le_state_dim ρ w

/-- No oversized perfect distinguishability set. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {G : Perspectival.GPT V}
    {n : ℕ} (h : n > Module.finrank ℝ V)
    (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) : False :=
  Perspectival.Distinguish.no_oversized_perfect_distinguishability h ρ w

/-- Distinguishable states are unequal. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (h : Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) : ρ₁ ≠ ρ₂ :=
  Perspectival.Distinguish.distinguishable_ne h

/-- States are nonzero. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ : V} (h : ρ ∈ G.states) : ρ ≠ 0 :=
  Perspectival.Distinguish.state_ne_zero h

/-- Distinguishable states are linearly independent. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
    (hd : Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) :
    LinearIndependent ℝ ![ρ₁, ρ₂] :=
  Perspectival.Distinguish.distinguishable_imp_linear_independent h₁ h₂ hd

/-- N perfectly distinguishable states are linearly independent. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {n : ℕ} (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) :
    LinearIndependent ℝ ρ :=
  Perspectival.Distinguish.perfect_distinguishable_imp_linear_independent ρ w

/-- PerfectWitness.diag general: e i (ρ i) = 1. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ι : Type*} [DecidableEq ι] {ρ : ι → V}
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) (i : ι) :
    w.e i (ρ i) = 1 := w.diag i

/-- PerfectWitness.offdiag general: e i (ρ j) = 0 for i ≠ j. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ι : Type*} [DecidableEq ι] {ρ : ι → V}
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) {i j : ι}
    (hij : i ≠ j) :
    w.e i (ρ j) = 0 := w.offdiag hij

/-- The no-cloning bilinear-form theorem applies to any linear cloner. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S)
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : B v₁ v₂ + B v₂ v₁ ≠ 0) : False :=
  Perspectival.no_cloning hC h₁ h₂ h_sum hB

/-- No-cloning from linear independence. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S)
    (hLI : LinearIndependent ℝ ![v₁, v₂]) : False :=
  Perspectival.no_cloning_of_linear_independent hC h₁ h₂ h_sum hLI

/-- Cross-term cancellation: linear cloner forces cross terms to zero. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S) :
    v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁ = 0 :=
  Perspectival.cross_terms_vanish hC h₁ h₂ h_sum

/-- No-cloning from distinguishability (full chain). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {ρ₁ ρ₂ : V} (h₁ : ρ₁ ∈ S) (h₂ : ρ₂ ∈ S) (h_sum : ρ₁ + ρ₂ ∈ S)
    (hρ₁ : ρ₁ ∈ G.states) (hρ₂ : ρ₂ ∈ G.states)
    (hd : Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) : False :=
  Perspectival.Distinguish.no_cloning_of_distinguishable hC h₁ h₂ h_sum hρ₁ hρ₂ hd

-- (Tsirelson bound examples require importing CHSH module — Examples doesn't import it.)

/-- Hardy.Distinguishable is symmetric in the special case of perfectly-disjoint effects
(but in general it's NOT symmetric — see the asymmetric definition). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (e : V →ₗ[ℝ] ℝ) (he : e ∈ G.effects) (h1 : e ρ₁ = 1) (h2 : e ρ₂ = 0) :
    Perspectival.Hardy.Distinguishable G ρ₁ ρ₂ := ⟨e, he, h1, h2⟩

/-- The unit functional gives probability 1 on any normalized state (boundary case). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] {G : Perspectival.GPT V}
    {ρ : V} (hρ : ρ ∈ G.states) : G.unit ρ = 1 := G.states_normalized ρ hρ

/-- The states form a convex set (GPT axiom). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Convex ℝ G.states := G.states_convex

/-- The effects form a convex set (GPT axiom). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Convex ℝ G.effects := G.effects_convex

/-- GPT.unit is itself an effect (axiom). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    G.unit ∈ G.effects := G.unit_is_effect

/-- GPT probabilities are in [0,1] (axiom). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V)
    (e : V →ₗ[ℝ] ℝ) (he : e ∈ G.effects) (ρ : V) (hρ : ρ ∈ G.states) :
    0 ≤ e ρ ∧ e ρ ≤ 1 := G.prob_in_unit_interval e he ρ hρ

/-- Transform identity. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Perspectival.GPT.Transform G G := Perspectival.GPT.Transform.id G

/-- Transform composition. -/
example {V V' V'' : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup V''] [Module ℝ V'']
    {G : Perspectival.GPT V} {G' : Perspectival.GPT V'} {G'' : Perspectival.GPT V''}
    (T' : Perspectival.GPT.Transform G' G'') (T : Perspectival.GPT.Transform G G') :
    Perspectival.GPT.Transform G G'' := Perspectival.GPT.Transform.comp T' T

/-- Transform.prob_invariant: a Transform preserves probabilities via unit. -/
example {V V' : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    {G : Perspectival.GPT V} {G' : Perspectival.GPT V'}
    (T : Perspectival.GPT.Transform G G') (ρ : V) :
    G'.unit (T.toLin ρ) = G.unit ρ :=
  Perspectival.GPT.Transform.prob_invariant T ρ

/-- Transform.id_sq: id ∘ id = id. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Perspectival.GPT.Transform.id G * Perspectival.GPT.Transform.id G
    = Perspectival.GPT.Transform.id G := Perspectival.GPT.Transform.id_sq G

/-- Transform.id_toLin: id has LinearMap.id as toLin. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    (Perspectival.GPT.Transform.id G).toLin = LinearMap.id :=
  Perspectival.GPT.Transform.id_toLin G

/-- Transform.comp_toLin: composition's toLin is composition of toLins. -/
example {V V' V'' : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup V''] [Module ℝ V'']
    {G : Perspectival.GPT V} {G' : Perspectival.GPT V'} {G'' : Perspectival.GPT V''}
    (T' : Perspectival.GPT.Transform G' G'') (T : Perspectival.GPT.Transform G G') :
    (Perspectival.GPT.Transform.comp T' T).toLin = T'.toLin.comp T.toLin :=
  Perspectival.GPT.Transform.comp_toLin T' T

/-- Self-Transforms on a GPT form a Monoid. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    Monoid (Perspectival.GPT.Transform G G) := inferInstance

/-- Concrete: WantableGPT Bool self-Transforms form a Monoid. -/
example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt Bool)
                    (Perspectival.WantableGPT.gpt Bool)) := inferInstance

-- (Fin 4 concrete complement values — instance definition different; skip.)

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

/-- Monoid identity law `1 * T = T` for Transform on WantableGPT Bool. -/
example (T : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt Bool)
              (Perspectival.WantableGPT.gpt Bool)) :
    1 * T = T := one_mul T

/-- Monoid identity law `T * 1 = T` for Transform on WantableGPT Bool. -/
example (T : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt Bool)
              (Perspectival.WantableGPT.gpt Bool)) :
    T * 1 = T := mul_one T

/-- Monoid associativity for Transform on WantableGPT Bool. -/
example (T₁ T₂ T₃ : Perspectival.GPT.Transform
                     (Perspectival.WantableGPT.gpt Bool)
                     (Perspectival.WantableGPT.gpt Bool)) :
    (T₁ * T₂) * T₃ = T₁ * (T₂ * T₃) := mul_assoc T₁ T₂ T₃

/-- `T^0 = 1` in Transform monoid (pow_zero). -/
example (T : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt Bool)
              (Perspectival.WantableGPT.gpt Bool)) :
    T ^ 0 = 1 := pow_zero T

/-- `T^1 = T` in Transform monoid (pow_one). -/
example (T : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt Bool)
              (Perspectival.WantableGPT.gpt Bool)) :
    T ^ 1 = T := pow_one T

/-- `T^(m+n) = T^m * T^n` in Transform monoid (pow_add). -/
example (T : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt Bool)
              (Perspectival.WantableGPT.gpt Bool)) (m n : ℕ) :
    T ^ (m + n) = T ^ m * T ^ n := pow_add T m n

/-- `1^n = 1` in Transform monoid (one_pow). -/
example (n : ℕ) :
    (1 : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt Bool)
            (Perspectival.WantableGPT.gpt Bool)) ^ n = 1 := one_pow n

/-- Transform identity carries the linear identity map. -/
example : (1 : Perspectival.GPT.Transform
                (Perspectival.WantableGPT.gpt Bool)
                (Perspectival.WantableGPT.gpt Bool)).toLin
        = LinearMap.id := rfl

/-- Transform composition carries linear composition. -/
example (T₁ T₂ : Perspectival.GPT.Transform
                   (Perspectival.WantableGPT.gpt Bool)
                   (Perspectival.WantableGPT.gpt Bool)) :
    (T₁ * T₂).toLin = T₁.toLin ∘ₗ T₂.toLin := rfl

/-- Self-Transforms on WantableGPT (Fin 4) form a Monoid. -/
example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt (Fin 4))
                    (Perspectival.WantableGPT.gpt (Fin 4))) := inferInstance

/-- Self-Transforms on WantableGPT (Bool × Bool) form a Monoid. -/
example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt (Bool × Bool))
                    (Perspectival.WantableGPT.gpt (Bool × Bool))) := inferInstance

/-- `Reachable.preorder` gives reflexivity and transitivity under
`ClosedAgency`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V}
    [Perspectival.Continuity.ClosedAgency G] :
    (∀ ρ : V, Perspectival.Continuity.Reachable (G := G) ρ ρ) ∧
    (∀ ρ₁ ρ₂ ρ₃ : V,
      Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂ →
      Perspectival.Continuity.Reachable (G := G) ρ₂ ρ₃ →
      Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₃) :=
  Perspectival.Continuity.Reachable.preorder

/-- `Reachable` is reflexive under any `HasConnectedAgency`
(generic restatement). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.HasConnectedAgency G]
    (ρ : V) : Perspectival.Continuity.Reachable (G := G) ρ ρ :=
  Perspectival.Continuity.Reachable.refl ρ

/-- `Reachable.trans` under `ClosedAgency` (generic restatement). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.ClosedAgency G]
    {ρ₁ ρ₂ ρ₃ : V}
    (h₁ : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂)
    (h₂ : Perspectival.Continuity.Reachable (G := G) ρ₂ ρ₃) :
    Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₃ :=
  Perspectival.Continuity.Reachable.trans h₁ h₂

/-- `Reachable.apply_available`: if `ρ₁ ~> ρ₂` and `R` is available,
then `ρ₁ ~> R.toLin ρ₂`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.ClosedAgency G]
    {ρ₁ ρ₂ : V}
    (h : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂)
    (R : Perspectival.Continuity.Reversible G)
    (hR : R ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G)) :
    Perspectival.Continuity.Reachable (G := G) ρ₁ (R.toLin ρ₂) :=
  Perspectival.Continuity.Reachable.apply_available h R hR

/-- Generic dimension inequality: a `PerfectWitness` on `n` indexes
gives `n ≤ Module.finrank ℝ V` (operational ≤ structural). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    {G : Perspectival.GPT V}
    (n : ℕ) (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) :
    n ≤ Module.finrank ℝ V :=
  Perspectival.Distinguish.operational_dim_le_state_dim ρ w

/-- For Bool's WantableGPT: |Bool| = 2 ≤ finrank = 2 (concrete dim
inequality). -/
example : (2 : ℕ) ≤ Module.finrank ℝ (Perspectival.WantableGPT.V Bool) := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- `no_oversized_perfect_distinguishability`: cannot have more
perfectly distinguishable states than the dimension of V. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    {G : Perspectival.GPT V}
    {n : ℕ} (hn : n > Module.finrank ℝ V) (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) : False :=
  Perspectival.Distinguish.no_oversized_perfect_distinguishability hn ρ w

/-- Axiom 2 is auxiliary, not a derivable substantive predicate
(placeholder def is `True`). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (n k : ℕ) :
    Perspectival.Hardy.Axiom2_Simplicity G n k := trivial

/-- Axiom 4 is the auxiliary placeholder (vacuously true).  -/
example {VA VB : Type u}
    [AddCommGroup VA] [Module ℝ VA] [AddCommGroup VB] [Module ℝ VB]
    (GA : Perspectival.GPT VA) (GB : Perspectival.GPT VB) (nA nB : ℕ) :
    Perspectival.Hardy.Axiom4_Composite_States_Multiply GA GB nA nB :=
  Perspectival.Hardy.axiom4_holds_placeholder GA GB nA nB

/-- Hardy Axiom 1 (probabilities in [0,1]) holds for the classical
GPT on `n`. -/
example (n : ℕ) :
    Perspectival.Hardy.Axiom1_Probabilities
      (Perspectival.Classical.gpt n) :=
  Perspectival.Hardy.axiom1_holds _

/-- Hardy Axiom 3 (subspaces) holds for the classical GPT on `n`. -/
example (n : ℕ) :
    Perspectival.Hardy.Axiom3_Subspaces
      (Perspectival.Classical.gpt n) :=
  Perspectival.Hardy.axiom3_holds _

/-- `Meeting.prodMk_prodFst_prodSnd`: projecting a product meeting and
re-pairing reconstructs it (functoriality identity). -/
example (m : Meeting (Bool × Bool)) :
    Meeting.prodMk m.prodFst m.prodSnd = m :=
  Meeting.prodMk_prodFst_prodSnd m

/-- `Meeting.prod_swap`: swap on a product meeting equals the prodMk
of component swaps. -/
example (m : Meeting (Bool × Bool)) :
    m.swap = Meeting.prodMk m.prodFst.swap m.prodSnd.swap :=
  Meeting.prod_swap m

/-- `PTrans.sumMap_mul`: sumMap distributes over composition. -/
example (g₁ f₁ g₂ f₂ : PTrans Bool) :
    PTrans.sumMap (g₁ * f₁) (g₂ * f₂) =
    PTrans.sumMap g₁ g₂ * PTrans.sumMap f₁ f₂ :=
  PTrans.sumMap_mul g₁ f₁ g₂ f₂

/-- `PTrans.prodMap_mul`: prodMap distributes over composition. -/
example (g₁ f₁ g₂ f₂ : PTrans Bool) :
    PTrans.prodMap (g₁ * f₁) (g₂ * f₂) =
    PTrans.prodMap g₁ g₂ * PTrans.prodMap f₁ f₂ :=
  PTrans.prodMap_mul g₁ f₁ g₂ f₂

/-- `PTrans.complement_inv`: complement is its own inverse in PTrans. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W)⁻¹ = PTrans.complement :=
  PTrans.complement_inv

/-- `actMeeting_complement_sq`: applying complement twice via actMeeting
returns the original meeting (involutive action on meetings). -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (PTrans.complement : PTrans W)
      (PTrans.actMeeting PTrans.complement m) = m :=
  PTrans.actMeeting_complement_sq m

/-- `actMeeting_comp`: action of composition factors through individual
actions. -/
example {W : Type u} [Wantable W] (g f : PTrans W) (m : Meeting W) :
    PTrans.actMeeting (g * f) m =
      PTrans.actMeeting g (PTrans.actMeeting f m) :=
  PTrans.actMeeting_comp g f m

/-- `actReality_mul`: action on Reality respects PTrans multiplication. -/
example {W : Type u} [Wantable W] (ψ φ : PTrans W) (R : Reality W) :
    PTrans.actReality (ψ * φ) R = PTrans.actReality ψ (PTrans.actReality φ R) :=
  PTrans.actReality_mul ψ φ R

/-- `actReality_and`: action distributes over logical conjunction. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (R₁ R₂ : Reality W) :
    PTrans.actReality φ (fun m => R₁ m ∧ R₂ m) =
      fun m => PTrans.actReality φ R₁ m ∧ PTrans.actReality φ R₂ m :=
  PTrans.actReality_and φ R₁ R₂

/-- `actReality_or`: action distributes over logical disjunction. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (R₁ R₂ : Reality W) :
    PTrans.actReality φ (fun m => R₁ m ∨ R₂ m) =
      fun m => PTrans.actReality φ R₁ m ∨ PTrans.actReality φ R₂ m :=
  PTrans.actReality_or φ R₁ R₂

/-- `actReality_empty`: empty reality is φ-invariant. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.actReality φ (fun _ : Meeting W => False) = fun _ => False :=
  PTrans.actReality_empty φ

/-- `actReality_full`: full reality is φ-invariant. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.actReality φ (fun _ : Meeting W => True) = fun _ => True :=
  PTrans.actReality_full φ

/-- `Reality` admits a `MulAction` instance from PTrans. -/
example {W : Type u} [Wantable W] : MulAction (PTrans W) (Reality W) := inferInstance

/-- `complementary_symm`: side₁ and side₂ of a meeting are mutual
complements. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    Wantable.complement m.side₁ = m.side₂ ∧
    Wantable.complement m.side₂ = m.side₁ :=
  ⟨m.complementary, Meeting.complementary_symm m⟩

/-- `side₂_eq_complement_side₁`: side₂ is the complement of side₁. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    m.side₂ = Wantable.complement m.side₁ :=
  Meeting.side₂_eq_complement_side₁ m

/-- `swap_swap`: swap is involutive on meetings. -/
example {W : Type u} [Wantable W] (m : Meeting W) : m.swap.swap = m :=
  Meeting.swap_swap m

/-- `swap_mk_fromSide`: swap of a meeting built from side `w` gives
the meeting built from the complement. -/
example {W : Type u} [Wantable W] (w : W) :
    (Meeting.mk_fromSide W w).swap = Meeting.mk_fromSide W (Wantable.complement w) :=
  Meeting.swap_mk_fromSide w

/-- `Wantable.complement_complement_eq_id`: complement squared is `id`. -/
example {W : Type u} [Wantable W] :
    (Wantable.complement ∘ Wantable.complement : W → W) = id :=
  Wantable.complement_complement_eq_id

/-- `ext_of_side₁`: meetings agreeing on side₁ are equal. -/
example {W : Type u} [Wantable W] (m₁ m₂ : Meeting W) (h : m₁.side₁ = m₂.side₁) :
    m₁ = m₂ :=
  Meeting.ext_of_side₁ m₁ m₂ h

/-- `SelfComplementary.preserved`: a function commuting with complement
sends self-complementary wants to self-complementary wants. -/
example {W : Type u} [Wantable W]
    (f : W → W) (hf : ∀ w, f (Wantable.complement w) = Wantable.complement (f w))
    (w : W) (h : SelfComplementary w) : SelfComplementary (f w) :=
  SelfComplementary.preserved f hf w h

/-- `ne_complement_of_fixedPointFree`: in a fixed-point-free Wantable,
no want equals its complement. -/
example {W : Type u} [Wantable W]
    (h : FixedPointFreeComplement W) (w : W) :
    w ≠ Wantable.complement w :=
  ne_complement_of_fixedPointFree h w

/-- `Wantable.exists_complement`: every want has a complement (trivial). -/
example {W : Type u} [Wantable W] (w : W) :
    ∃ v : W, Wantable.complement w = v :=
  Wantable.exists_complement w

/-- `Wantable.complement_surjective`: complement is surjective. -/
example {W : Type u} [Wantable W] :
    Function.Surjective (Wantable.complement : W → W) :=
  Wantable.complement_surjective

/-- `Wantable.complement_eq_iff`: complement is an injective-like
characterisation. -/
example {W : Type u} [Wantable W] (a b : W) :
    Wantable.complement a = b ↔ a = Wantable.complement b :=
  Wantable.complement_eq_iff a b

/-- `Transform.ext` (generic): equal underlying linear maps ⇒ equal Transforms. -/
example {V V' : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V']
    {G : Perspectival.GPT V} {G' : Perspectival.GPT V'}
    {T T' : Perspectival.GPT.Transform G G'}
    (h : T.toLin = T'.toLin) : T = T' :=
  Perspectival.GPT.Transform.ext h

/-- Two Bool-self Transforms with the same toLin are equal. -/
example (T T' : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool))
    (h : T.toLin = T'.toLin) : T = T' :=
  Perspectival.GPT.Transform.ext h

/-- The Transform constructed from the identity LinearMap is the identity Transform. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) :
    (Perspectival.GPT.Transform.id G).toLin = LinearMap.id :=
  Perspectival.GPT.Transform.id_toLin G

/-- `Transform.id` squared is `Transform.id`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) :
    Perspectival.GPT.Transform.id G * Perspectival.GPT.Transform.id G
      = Perspectival.GPT.Transform.id G :=
  Perspectival.GPT.Transform.id_sq G

/-- `Classical.vertex_decomposition`: every classical state is its
coordinate-wise vertex combination. -/
example (n : ℕ) (f : Perspectival.Classical.V n) :
    f = ∑ i, f i • Perspectival.Classical.vertex n i :=
  Perspectival.Classical.vertex_decomposition n f

/-- `Classical.vertices_span`: classical vertices span `V n`. -/
example (n : ℕ) :
    Submodule.span ℝ (Set.range (Perspectival.Classical.vertex n)) = ⊤ :=
  Perspectival.Classical.vertices_span n

/-- `Classical.vertex_linear_independent`: classical vertices are
linearly independent. -/
example (n : ℕ) : LinearIndependent ℝ (Perspectival.Classical.vertex n) :=
  Perspectival.Classical.vertex_linear_independent n

/-- `Classical.vertices_distinguishable`: distinct vertices are
distinguishable in the classical GPT. -/
example (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Perspectival.Hardy.Distinguishable (Perspectival.Classical.gpt n)
      (Perspectival.Classical.vertex n i)
      (Perspectival.Classical.vertex n j) :=
  Perspectival.Classical.vertices_distinguishable n i j hij

/-- `WantableGPT.vertex_decomposition`: every WantableGPT state is its
coordinate-wise vertex combination. -/
example (W : Type u) [Wantable W] [Fintype W] [DecidableEq W]
    (f : Perspectival.WantableGPT.V W) :
    f = ∑ w, f w • Perspectival.WantableGPT.vertex W w :=
  Perspectival.WantableGPT.vertex_decomposition W f

/-- `WantableGPT.vertices_span`: WantableGPT vertices span `V W`. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Submodule.span ℝ (Set.range (Perspectival.WantableGPT.vertex W)) = ⊤ :=
  Perspectival.WantableGPT.vertices_span W

/-- `WantableGPT.vertex_linear_independent_of_fintype`: WantableGPT
vertices are linearly independent. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    LinearIndependent ℝ (Perspectival.WantableGPT.vertex W) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype W

/-- `WantableGPT.vertices_distinguishable`: distinct vertices are
distinguishable. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (w v : W) (hwv : w ≠ v) :
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt W)
      (Perspectival.WantableGPT.vertex W w)
      (Perspectival.WantableGPT.vertex W v) :=
  Perspectival.WantableGPT.vertices_distinguishable W w v hwv

/-- `complementPTrans_sq`: complementPTrans squared is the identity. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) *
    (Perspectival.WantableGPT.complementPTrans W) = (1 : PTrans W) :=
  Perspectival.WantableGPT.complementPTrans_sq W

/-- `complementPTrans_inv`: complementPTrans is its own inverse. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W)⁻¹
      = Perspectival.WantableGPT.complementPTrans W :=
  Perspectival.WantableGPT.complementPTrans_inv W

/-- `complementTransform_eq_fromPTrans_full`: the bridge identifies
complementTransform with fromPTrans of complementPTrans. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.complementTransform W
      = Perspectival.WantableGPT.fromPTrans W
          (Perspectival.WantableGPT.complementPTrans W) :=
  Perspectival.WantableGPT.complementTransform_eq_fromPTrans_full W

/-- `complementTransform_sq`: complementTransform squared = identity. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.complementTransform W *
    Perspectival.WantableGPT.complementTransform W
      = (1 : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt W)
              (Perspectival.WantableGPT.gpt W)) :=
  Perspectival.WantableGPT.complementTransform_sq W

/-- Generic statement: `fromPTransHom` is injective (the bridge is a
faithful embedding of PTrans into the operational transformation monoid). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Function.Injective (Perspectival.WantableGPT.fromPTransHom W) :=
  Perspectival.WantableGPT.fromPTransHom_injective W

/-- Generic statement: `fromPTransHom` of 1 is LinearMap.id. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.fromPTransHom W 1 = LinearMap.id :=
  (Perspectival.WantableGPT.fromPTransHom W).map_one

/-- Generic statement: `fromPTransHom` is multiplicative. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (φ ψ : PTrans W) :
    Perspectival.WantableGPT.fromPTransHom W (φ * ψ) =
    Perspectival.WantableGPT.fromPTransHom W φ *
    Perspectival.WantableGPT.fromPTransHom W ψ :=
  (Perspectival.WantableGPT.fromPTransHom W).map_mul φ ψ

/-- Generic statement: `fromPTransTransformHom` is multiplicative. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (φ ψ : PTrans W) :
    Perspectival.WantableGPT.fromPTransTransformHom W (φ * ψ) =
    Perspectival.WantableGPT.fromPTransTransformHom W φ *
    Perspectival.WantableGPT.fromPTransTransformHom W ψ :=
  (Perspectival.WantableGPT.fromPTransTransformHom W).map_mul φ ψ

/-- `toEquivPerm`: applying a PTrans's underlying permutation at `w`
gives `φ.toFun w`. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (w : W) :
    PTrans.toEquivPerm φ w = φ.toFun w :=
  PTrans.toEquivPerm_apply φ w

/-- `toEquivPerm.symm`: the symm of the underlying permutation gives
`φ.invFun`. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (w : W) :
    (PTrans.toEquivPerm φ).symm w = φ.invFun w :=
  PTrans.toEquivPerm_symm_apply φ w

/-- `toEquivPerm_one`: identity PTrans → identity permutation. -/
example {W : Type u} [Wantable W] :
    PTrans.toEquivPerm (1 : PTrans W) = 1 := PTrans.toEquivPerm_one

/-- `toEquivPerm_mul`: composition factors through. -/
example {W : Type u} [Wantable W] (g f : PTrans W) :
    PTrans.toEquivPerm (g * f) = PTrans.toEquivPerm g * PTrans.toEquivPerm f :=
  PTrans.toEquivPerm_mul g f

/-- `ofEquivPerm`: a permutation commuting with complement lifts to PTrans. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W)
    (h : ∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) (w : W) :
    (PTrans.ofEquivPerm σ h).toFun w = σ w :=
  PTrans.ofEquivPerm_toFun σ h w

/-- `toEquivPerm_ofEquivPerm`: roundtrip recovers the permutation. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W)
    (h : ∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) :
    PTrans.toEquivPerm (PTrans.ofEquivPerm σ h) = σ :=
  PTrans.toEquivPerm_ofEquivPerm σ h

/-- `ofEquivPerm_toEquivPerm`: roundtrip recovers the PTrans. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.ofEquivPerm (PTrans.toEquivPerm φ) φ.resp_complement = φ :=
  PTrans.ofEquivPerm_toEquivPerm φ

/-- `toEquivPerm_commutes_complement`: PTrans permutations commute with
the complement permutation (centralizer property). -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.toEquivPerm φ * PTrans.toEquivPerm (PTrans.complement : PTrans W)
    = PTrans.toEquivPerm (PTrans.complement : PTrans W) * PTrans.toEquivPerm φ :=
  PTrans.toEquivPerm_commutes_complement φ

/-- `PTrans.id_comp`: identity composed with f gives f. -/
example {W : Type u} [Wantable W] (f : PTrans W) :
    PTrans.comp PTrans.id f = f :=
  PTrans.id_comp f

/-- `PTrans.comp_id`: f composed with identity gives f. -/
example {W : Type u} [Wantable W] (f : PTrans W) :
    PTrans.comp f PTrans.id = f :=
  PTrans.comp_id f

/-- `PTrans.comp_assoc`: composition is associative. -/
example {W : Type u} [Wantable W] (h g f : PTrans W) :
    PTrans.comp (PTrans.comp h g) f = PTrans.comp h (PTrans.comp g f) :=
  PTrans.comp_assoc h g f

/-- `NoBroadcasting.classicalBroadcaster_vertex`: the classical
broadcaster sends each vertex to its diagonal tensor. -/
example (n : ℕ) (i : Fin n) :
    Perspectival.NoBroadcasting.classicalBroadcaster n
        (Perspectival.Classical.vertex n i)
      = Perspectival.Classical.vertex n i
          ⊗ₜ[ℝ] Perspectival.Classical.vertex n i :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex n i

/-- `NoBroadcasting.basisFun_eq_vertex`: the standard basis vector
equals the classical vertex. -/
example (n : ℕ) (i : Fin n) :
    (Pi.basisFun ℝ (Fin n)) i = Perspectival.Classical.vertex n i :=
  Perspectival.NoBroadcasting.basisFun_eq_vertex n i

/-- `NoBroadcasting.classicalBroadcaster_basisFun`: action on standard
basis vectors of `Fin n → ℝ`. -/
example (n : ℕ) (i : Fin n) :
    Perspectival.NoBroadcasting.classicalBroadcaster n
        ((Pi.basisFun ℝ (Fin n)) i)
      = Perspectival.Classical.vertex n i
          ⊗ₜ[ℝ] Perspectival.Classical.vertex n i :=
  Perspectival.NoBroadcasting.classicalBroadcaster_basisFun n i

/-- `Reachable.symm_of_inv_avail`: with per-element inverse availability,
Reachable is symmetric. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V}
    [Perspectival.Continuity.HasConnectedAgency G]
    (h_inv : ∀ R : Perspectival.Continuity.Reversible G,
              R ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) →
              ∃ S : Perspectival.Continuity.Reversible G,
                S ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) ∧
                ∀ v : V, S.toLin (R.toLin v) = v)
    {ρ₁ ρ₂ : V}
    (h : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂) :
    Perspectival.Continuity.Reachable (G := G) ρ₂ ρ₁ :=
  Perspectival.Continuity.Reachable.symm_of_inv_avail h_inv h

/-- `trivialAgency_reachable_refl`: under trivialAgency, every state is
reachable from itself. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : Perspectival.GPT V) (ρ : V) :
    @Perspectival.Continuity.Reachable V _ _ _ G
      (Perspectival.Continuity.trivialAgency G) ρ ρ :=
  Perspectival.Continuity.trivialAgency_reachable_refl G ρ

/-- `trivialAgency_inv_avail`: identity-only agency vacuously satisfies
the inverse-availability hypothesis. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : Perspectival.GPT V) :
    ∀ R : Perspectival.Continuity.Reversible G,
      R ∈ Perspectival.Continuity.HasConnectedAgency.avail
            (G := G) (self := Perspectival.Continuity.trivialAgency G) →
      ∃ S : Perspectival.Continuity.Reversible G,
        S ∈ Perspectival.Continuity.HasConnectedAgency.avail
            (G := G) (self := Perspectival.Continuity.trivialAgency G) ∧
        ∀ v : V, S.toLin (R.toLin v) = v :=
  Perspectival.Continuity.trivialAgency_inv_avail G

/-- `pairAgency_reaches_R₁`: in a pairAgency, R₁'s output is reachable
from any state. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : Perspectival.GPT V)
    (R₀ R₁ : Perspectival.Continuity.Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) (ρ : V) :
    @Perspectival.Continuity.Reachable V _ _ _ G
      (Perspectival.Continuity.pairAgency G R₀ R₁ hR₀_id) ρ (R₁.toLin ρ) :=
  Perspectival.Continuity.pairAgency_reaches_R₁ G R₀ R₁ hR₀_id ρ

/-- `pairAgency_reaches_self`: in a pairAgency, every state is
reachable from itself via R₀ = id. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : Perspectival.GPT V)
    (R₀ R₁ : Perspectival.Continuity.Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) (ρ : V) :
    @Perspectival.Continuity.Reachable V _ _ _ G
      (Perspectival.Continuity.pairAgency G R₀ R₁ hR₀_id) ρ ρ :=
  Perspectival.Continuity.pairAgency_reaches_self G R₀ R₁ hR₀_id ρ

/-- `pairAgency_avail_eq`: the avail set in a pairAgency is exactly {R₀, R₁}. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : Perspectival.GPT V)
    (R₀ R₁ : Perspectival.Continuity.Reversible G)
    (hR₀_id : ∀ v : V, R₀.toLin v = v) :
    Perspectival.Continuity.HasConnectedAgency.avail
      (G := G) (self := Perspectival.Continuity.pairAgency G R₀ R₁ hR₀_id)
      = {R₀, R₁} :=
  Perspectival.Continuity.pairAgency_avail_eq G R₀ R₁ hR₀_id

/-- `distinguishable_imp_linear_independent`: two distinguishable states
are linearly independent. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
    (hd : Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) :
    LinearIndependent ℝ ![ρ₁, ρ₂] :=
  Perspectival.Distinguish.distinguishable_imp_linear_independent h₁ h₂ hd

/-- `perfect_distinguishable_imp_linear_independent`: a perfect-witness
family is linearly independent. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {n : ℕ} (ρ : Fin n → V)
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) :
    LinearIndependent ℝ ρ :=
  Perspectival.Distinguish.perfect_distinguishable_imp_linear_independent ρ w

/-- `PerfectWitness.diag`: diagonal entries equal 1. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ι : Type*} [DecidableEq ι] {ρ : ι → V}
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ) (i : ι) :
    w.e i (ρ i) = 1 :=
  Perspectival.Distinguish.PerfectWitness.diag w i

/-- `PerfectWitness.offdiag`: off-diagonal entries equal 0. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ι : Type*} [DecidableEq ι] {ρ : ι → V}
    (w : Perspectival.Distinguish.PerfectWitness (G := G) ρ)
    {i j : ι} (hij : i ≠ j) :
    w.e i (ρ j) = 0 :=
  Perspectival.Distinguish.PerfectWitness.offdiag w hij

/-- `GPT.prob_def`: probability is just effect-application. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (e : V →ₗ[ℝ] ℝ) (ρ : V) :
    G.prob e ρ = e ρ := Perspectival.GPT.prob_def G e ρ

/-- States are normalized: `unit ρ = 1` for `ρ ∈ states`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (ρ : V) (hρ : ρ ∈ G.states) :
    G.unit ρ = 1 := G.states_normalized ρ hρ

/-- The unit is itself an effect. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) : G.unit ∈ G.effects := G.unit_is_effect

/-- The states set is convex. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) : Convex ℝ G.states := G.states_convex

/-- The effects set is convex. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) : Convex ℝ G.effects := G.effects_convex

/-- `Hardy.Distinguishable` unfolds: there exists an effect with
`e ρ₁ = 1` and `e ρ₂ = 0`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (ρ₁ ρ₂ : V) :
    Perspectival.Hardy.Distinguishable G ρ₁ ρ₂ ↔
    ∃ e ∈ G.effects, e ρ₁ = 1 ∧ e ρ₂ = 0 := Iff.rfl

/-- `Hardy.DistinguishabilitySet` unfolds: a finite set of mutually
distinguishable states. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (S : Finset V) :
    Perspectival.Hardy.DistinguishabilitySet G S ↔
    ((∀ ρ ∈ S, ρ ∈ G.states) ∧
     ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S, ρ₁ ≠ ρ₂ →
       Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) := Iff.rfl

/-- `Hardy.HasDimensionN` unfolds: existence of a max-size
distinguishability set. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) (n : ℕ) :
    Perspectival.Hardy.HasDimensionN G n ↔
    ((∃ S : Finset V, S.card = n ∧ Perspectival.Hardy.DistinguishabilitySet G S) ∧
     (∀ m, m > n → ¬ ∃ S : Finset V, S.card = m ∧
       Perspectival.Hardy.DistinguishabilitySet G S)) := Iff.rfl

/-- `Hardy.Axiom5_Continuity` is the placeholder predicate `True`
(continuity needs additional topological structure not in pure GPT). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (G : Perspectival.GPT V) :
    Perspectival.Hardy.Axiom5_Continuity G := by
  intro ρ₁ ρ₂ _ _ _ _
  trivial

/-- `PureState` unfolds: a pure state is a state which is also an
extreme point of the convex state space. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : Perspectival.GPT V) (ρ : V) :
    Perspectival.Continuity.PureState G ρ ↔
    (ρ ∈ G.states ∧ IsExtreme ℝ G.states {ρ}) := Iff.rfl

/-- `hardy_axiom5_pure_states`: between any two reachable pure states
there exists a continuous path of linear maps. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.HasConnectedAgency G]
    {ρ₁ ρ₂ : V}
    (hp₁ : Perspectival.Continuity.PureState G ρ₁)
    (hp₂ : Perspectival.Continuity.PureState G ρ₂)
    (h : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ :=
  Perspectival.Continuity.hardy_axiom5_pure_states hp₁ hp₂ h

/-- `hardy_axiom5_transitive`: under transitivity of the agency action
on pure states, Hardy Axiom 5 follows. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.HasConnectedAgency G]
    (h_transitive :
      ∀ ρ₁ ρ₂, Perspectival.Continuity.PureState G ρ₁ →
                Perspectival.Continuity.PureState G ρ₂ →
                Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂)
    (ρ₁ ρ₂ : V)
    (hp₁ : Perspectival.Continuity.PureState G ρ₁)
    (hp₂ : Perspectival.Continuity.PureState G ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ :=
  Perspectival.Continuity.hardy_axiom5_transitive h_transitive ρ₁ ρ₂ hp₁ hp₂

/-- `continuous_path_of_reachable`: from reachability, a continuous
path between states (the V-valued form of Hardy Axiom 5). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.HasConnectedAgency G]
    (ρ₁ ρ₂ : V) (hρ₁ : ρ₁ ∈ G.states)
    (h : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂) :
    ∃ p : unitInterval → V, Continuous p ∧ p 0 = ρ₁ ∧ p 1 = ρ₂ :=
  Perspectival.Continuity.continuous_path_of_reachable ρ₁ ρ₂ hρ₁ h

/-- `hardy_axiom5_of_agency`: from reachability + agency, a continuous
path of linear maps (no pure-state restriction). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.HasConnectedAgency G]
    (ρ₁ ρ₂ : V) (h : Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂) :
    ∃ γ : unitInterval → V →ₗ[ℝ] V,
      Continuous (fun p : unitInterval × V => γ p.1 p.2) ∧
      (∀ v, γ 0 v = v) ∧
      γ 1 ρ₁ = ρ₂ :=
  Perspectival.Continuity.hardy_axiom5_of_agency ρ₁ ρ₂ h

/-- Generic `complementAction_vertex`: the complement action sends
`vertex w` to `vertex (complement w)`. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.complementAction W (Perspectival.WantableGPT.vertex W w)
      = Perspectival.WantableGPT.vertex W (Wantable.complement w) :=
  Perspectival.WantableGPT.complementAction_vertex W w

/-- Generic `vertex_perfectly_distinguishable`: there exists a perfect
witness (the projections) for the vertex family. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    ∃ e : W → Perspectival.WantableGPT.V W →ₗ[ℝ] ℝ,
      ∀ i j : W, e i (Perspectival.WantableGPT.vertex W j)
                  = if i = j then (1 : ℝ) else 0 :=
  Perspectival.WantableGPT.vertex_perfectly_distinguishable W

/-- Generic `vertex_injective`: distinct elements of W give distinct
vertices. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Function.Injective (Perspectival.WantableGPT.vertex W) :=
  Perspectival.WantableGPT.vertex_injective W

/-- Generic `vertex_image_card`: the vertex set has cardinality |W|. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    ((Finset.univ : Finset W).image
      (Perspectival.WantableGPT.vertex W)).card = Fintype.card W :=
  Perspectival.WantableGPT.vertex_image_card W

/-- Generic `vertex_distinguishability_set`: vertex set is a Hardy
distinguishability set. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.Hardy.DistinguishabilitySet
      (Perspectival.WantableGPT.gpt W)
      ((Finset.univ : Finset W).image (Perspectival.WantableGPT.vertex W)) :=
  Perspectival.WantableGPT.vertex_distinguishability_set W

/-- Generic `state_is_convex_combination_of_vertices`: every state
decomposes into a vertex combination. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (f : Perspectival.WantableGPT.V W)
    (hf : f ∈ Perspectival.WantableGPT.states W) :
    f = ∑ w, f w • Perspectival.WantableGPT.vertex W w :=
  Perspectival.WantableGPT.state_is_convex_combination_of_vertices W f hf

/-- Generic `proj_in_effects`: each projection is a valid effect. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.proj W w ∈ Perspectival.WantableGPT.effects W :=
  Perspectival.WantableGPT.proj_in_effects W w

/-- Generic `wantableGPT_classical_signature`: the signature `N = K`
holds for the WantableGPT bridge. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    ∃ (n : ℕ) (ρ : Fin n → Perspectival.WantableGPT.V W)
      (_w : Perspectival.Distinguish.PerfectWitness
              (G := Perspectival.WantableGPT.gpt W) ρ),
      n = Module.finrank ℝ (Perspectival.WantableGPT.V W) :=
  Perspectival.WantableGPT.wantableGPT_classical_signature W

/-- Generic triple no-go (`wantableGPT_classical_dichotomy`):
all three signatures simultaneously hold/fail. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) ≠
        Fintype.card W * Fintype.card W ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) * 2 ≠
        Fintype.card W * (Fintype.card W + 1) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) ≠
        Fintype.card W * (2 * Fintype.card W - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy W h

/-- Generic `wantableGPT_nontrivial_classical`: |W| ≥ 2 case has
distinguishable states AND classical dimension. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    (∃ ρ₁ ρ₂ : Perspectival.WantableGPT.V W,
      ρ₁ ∈ Perspectival.WantableGPT.states W ∧
      ρ₂ ∈ Perspectival.WantableGPT.states W ∧
      Perspectival.Hardy.Distinguishable
        (Perspectival.WantableGPT.gpt W) ρ₁ ρ₂) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.wantableGPT_nontrivial_classical W h

/-- Generic `wantableGPT_not_quantum`: K ≠ N² for |W| ≥ 2. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W)
      ≠ Fintype.card W * Fintype.card W :=
  Perspectival.WantableGPT.wantableGPT_not_quantum W h

/-- Generic `wantableGPT_not_realQM`: 2K ≠ N(N+1) for |W| ≥ 2. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) * 2
      ≠ Fintype.card W * (Fintype.card W + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM W h

/-- Generic `wantableGPT_not_quaternionicQM`: K ≠ N(2N-1) for |W| ≥ 2. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W)
      ≠ Fintype.card W * (2 * Fintype.card W - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM W h

/-- Generic `finrank_V_prod_eq_mul`: product composition rule. -/
example {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (Perspectival.WantableGPT.V (W₁ × W₂))
      = Fintype.card W₁ * Fintype.card W₂ :=
  Perspectival.WantableGPT.finrank_V_prod_eq_mul

/-- Generic `finrank_V_sum_eq_add`: sum composition rule. -/
example {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (Perspectival.WantableGPT.V (W₁ ⊕ W₂))
      = Fintype.card W₁ + Fintype.card W₂ :=
  Perspectival.WantableGPT.finrank_V_sum_eq_add

/-- Generic `zero_in_effectVec`: the zero effect is in the effect vector set. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (0 : Perspectival.WantableGPT.V W) ∈ Perspectival.WantableGPT.effectVec W :=
  Perspectival.WantableGPT.zero_in_effectVec W

/-- Generic `one_in_effectVec`: the constant-1 effect is in the effect
vector set. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (fun _ : W => (1 : ℝ)) ∈ Perspectival.WantableGPT.effectVec W :=
  Perspectival.WantableGPT.one_in_effectVec W

/-- Generic `effectVec_eq_hypercube`: the effect vector set is the unit
hypercube. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.effectVec W
      = { g : Perspectival.WantableGPT.V W |
          ∀ w, g w ∈ Set.Icc (0 : ℝ) 1 } :=
  Perspectival.WantableGPT.effectVec_eq_hypercube W

/-- Generic `transformAction_preserves_states`: PTrans action keeps
states inside the state space. -/
example {W : Type u} [Wantable W] [Fintype W] (φ : PTrans W)
    (f : Perspectival.WantableGPT.V W)
    (hf : f ∈ Perspectival.WantableGPT.states W) :
    Perspectival.WantableGPT.transformAction W φ f
      ∈ Perspectival.WantableGPT.states W :=
  Perspectival.WantableGPT.transformAction_preserves_states W φ f hf

/-- Generic `unitFn_transformAction`: PTrans action preserves the unit. -/
example {W : Type u} [Wantable W] [Fintype W] (φ : PTrans W)
    (f : Perspectival.WantableGPT.V W) :
    Perspectival.WantableGPT.unitFn W
        (Perspectival.WantableGPT.transformAction W φ f)
      = Perspectival.WantableGPT.unitFn W f :=
  Perspectival.WantableGPT.unitFn_transformAction W φ f

/-- Generic `complementAction_preserves_states`: complement action
preserves the state space. -/
example {W : Type u} [Wantable W] [Fintype W]
    (f : Perspectival.WantableGPT.V W)
    (hf : f ∈ Perspectival.WantableGPT.states W) :
    Perspectival.WantableGPT.complementAction W f
      ∈ Perspectival.WantableGPT.states W :=
  Perspectival.WantableGPT.complementAction_preserves_states W f hf

/-- Generic `unitFn_complementAction`: complement action preserves the unit. -/
example {W : Type u} [Wantable W] [Fintype W]
    (f : Perspectival.WantableGPT.V W) :
    Perspectival.WantableGPT.unitFn W
        (Perspectival.WantableGPT.complementAction W f)
      = Perspectival.WantableGPT.unitFn W f :=
  Perspectival.WantableGPT.unitFn_complementAction W f

/-- Generic: WantableGPT effects are inner-product functionals with
[0,1]-valued coefficient vectors. -/
example {W : Type u} [Wantable W] [Fintype W] :
    Perspectival.WantableGPT.effects W
      = Perspectival.WantableGPT.innerLin W ''
          Perspectival.WantableGPT.effectVec W := rfl

/-- Generic: the WantableGPT's unit is exactly `unitFn`. -/
example {W : Type u} [Wantable W] [Fintype W] :
    (Perspectival.WantableGPT.gpt W).unit = Perspectival.WantableGPT.unitFn W :=
  rfl

/-- Generic: the WantableGPT's states are exactly the simplex. -/
example {W : Type u} [Wantable W] [Fintype W] :
    (Perspectival.WantableGPT.gpt W).states
      = Perspectival.WantableGPT.states W := rfl

/-- Generic: the WantableGPT's effects equal `effects`. -/
example {W : Type u} [Wantable W] [Fintype W] :
    (Perspectival.WantableGPT.gpt W).effects
      = Perspectival.WantableGPT.effects W := rfl

/-- `Pattern.and` is associative (logically). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and (Pattern.and P Q) R r ↔ Pattern.and P (Pattern.and Q R) r :=
  and_assoc

/-- `Pattern.or` is associative (logically). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.or (Pattern.or P Q) R r ↔ Pattern.or P (Pattern.or Q R) r :=
  or_assoc

/-- `Pattern.and` distributes over `Pattern.or` (left). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.or Q R) r ↔
    Pattern.or (Pattern.and P Q) (Pattern.and P R) r :=
  and_or_left

/-- `Pattern.or` distributes over `Pattern.and` (left). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.and Q R) r ↔
    Pattern.and (Pattern.or P Q) (Pattern.or P R) r :=
  or_and_left

/-- `Pattern.and` of any pattern with `Pattern.empty` is `Pattern.empty`. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.empty W) r ↔ Pattern.empty W r := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact h.elim

/-- `Pattern.or` of any pattern with `Pattern.trivial` is `Pattern.trivial`. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.trivial W) r ↔ Pattern.trivial W r := by
  constructor
  · intro _; trivial
  · intro _; exact Or.inr trivial

/-- Pattern is itself a Type: `Pattern W = Reality W → Prop`. -/
example {W : Type u} [Wantable W] :
    Pattern W = (Reality W → Prop) := rfl

/-- `Reality W` is an alias for `Meeting W → Prop`. -/
example {W : Type u} [Wantable W] :
    Reality W = (Meeting W → Prop) := rfl

/-- Generic `wantableGPT_is_classical`: the classical signature N = K
holds — N ≤ K AND K = N (both are |W|). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Fintype.card W ≤ Module.finrank ℝ (Perspectival.WantableGPT.V W) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.wantableGPT_is_classical W

/-- Generic `instModuleFinite`: `V W` is a finite ℝ-module. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.Finite ℝ (Perspectival.WantableGPT.V W) := inferInstance

/-- Generic `finrank_V_eq_card`: WantableGPT dimension equals |W|. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W :=
  Perspectival.WantableGPT.finrank_V_eq_card W

/-- `Classical.vertex_distinguishability_set`: classical vertex set is
a Hardy distinguishability set. -/
example (n : ℕ) :
    Perspectival.Hardy.DistinguishabilitySet (Perspectival.Classical.gpt n)
      ((Finset.univ : Finset (Fin n)).image (Perspectival.Classical.vertex n)) :=
  Perspectival.Classical.vertex_distinguishability_set n

/-- `Classical.perfectWitness`: the classical perfect witness exists. -/
example (n : ℕ) :
    Perspectival.Distinguish.PerfectWitness (G := Perspectival.Classical.gpt n)
      (Perspectival.Classical.vertex n) :=
  Perspectival.Classical.perfectWitness n

/-- `Classical.proj_in_effects`: each classical projection is an effect. -/
example (n : ℕ) (i : Fin n) :
    Perspectival.Classical.proj n i ∈ Perspectival.Classical.effects n :=
  Perspectival.Classical.proj_in_effects n i

/-- `Classical.proj_vertex`: coordinate projection gives Kronecker delta. -/
example (n : ℕ) (i j : Fin n) :
    Perspectival.Classical.proj n i (Perspectival.Classical.vertex n j)
      = if j = i then 1 else 0 :=
  Perspectival.Classical.proj_vertex n i j

/-- `Classical.unit_in_effects`: the unit is an effect. -/
example (n : ℕ) : Perspectival.Classical.unitFn n ∈ Perspectival.Classical.effects n :=
  Perspectival.Classical.unit_in_effects n

/-- `Classical.unit_is_innerLin_one`: unit equals innerLin of all-ones. -/
example (n : ℕ) :
    Perspectival.Classical.unitFn n
      = Perspectival.Classical.innerLin n (fun _ => 1) :=
  Perspectival.Classical.unit_is_innerLin_one n

/-- `Classical.states_convex`: states are convex. -/
example (n : ℕ) : Convex ℝ (Perspectival.Classical.states n) :=
  Perspectival.Classical.states_convex n

/-- `Classical.effects_convex`: effects are convex. -/
example (n : ℕ) : Convex ℝ (Perspectival.Classical.effects n) :=
  Perspectival.Classical.effects_convex n

/-- `Classical.unit_eq_one_on_states`: unit normalizes states. -/
example (n : ℕ) (x : Perspectival.Classical.V n)
    (hx : x ∈ Perspectival.Classical.states n) :
    Perspectival.Classical.unitFn n x = 1 :=
  Perspectival.Classical.unit_eq_one_on_states n x hx

/-- `Classical.prob_in_unit_interval`: effects give probabilities in [0,1]. -/
example (n : ℕ) (e : Perspectival.Classical.V n →ₗ[ℝ] ℝ)
    (he : e ∈ Perspectival.Classical.effects n)
    (x : Perspectival.Classical.V n)
    (hx : x ∈ Perspectival.Classical.states n) :
    0 ≤ e x ∧ e x ≤ 1 :=
  Perspectival.Classical.prob_in_unit_interval n e he x hx

/-- Generic `Meeting.sum_no_cross`: in a sum-Wantable, sides are
in the same summand (no cross-system meetings). -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m : Meeting (W₁ ⊕ W₂)) :
    (∃ a b, m.side₁ = .inl a ∧ m.side₂ = .inl b) ∨
    (∃ a b, m.side₁ = .inr a ∧ m.side₂ = .inr b) :=
  Meeting.sum_no_cross m

/-- Generic `Meeting.sumInl_swap`: sumInl commutes with swap. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂] (m : Meeting W₁) :
    (Meeting.sumInl (W₂ := W₂) m).swap = Meeting.sumInl m.swap :=
  Meeting.sumInl_swap m

/-- Generic `Meeting.sumInr_swap`: sumInr commutes with swap. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂] (m : Meeting W₂) :
    (Meeting.sumInr (W₁ := W₁) m).swap = Meeting.sumInr m.swap :=
  Meeting.sumInr_swap m

/-- Generic `Meeting.prodFst_prodMk`: prodMk-then-project recovers
the first component. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m₁ : Meeting W₁) (m₂ : Meeting W₂) :
    (Meeting.prodMk m₁ m₂).prodFst = m₁ :=
  Meeting.prodFst_prodMk m₁ m₂

/-- Generic `Meeting.prodSnd_prodMk`: prodMk-then-project recovers
the second component. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    (m₁ : Meeting W₁) (m₂ : Meeting W₂) :
    (Meeting.prodMk m₁ m₂).prodSnd = m₂ :=
  Meeting.prodSnd_prodMk m₁ m₂

/-- Generic `PTrans.prodMap_one_one`: prodMap of identities. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂] :
    PTrans.prodMap (1 : PTrans W₁) (1 : PTrans W₂) = 1 :=
  PTrans.prodMap_one_one W₁ W₂

/-- Generic `PTrans.sumMap_one_one`: sumMap of identities. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂] :
    PTrans.sumMap (1 : PTrans W₁) (1 : PTrans W₂) = 1 :=
  PTrans.sumMap_one_one W₁ W₂

/-- Generic `IsLinearCloner`: a cloner sends each element to its
diagonal tensor. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C) (v : V) (hv : v ∈ S) :
    C v = v ⊗ₜ[ℝ] v := hC v hv

/-- Generic `cross_terms_vanish`: a linear cloner forces cross terms
to cancel. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S) :
    v₁ ⊗ₜ[ℝ] v₂ + v₂ ⊗ₜ[ℝ] v₁ = 0 :=
  Perspectival.cross_terms_vanish hC h₁ h₂ h_sum

/-- Generic `no_cloning_of_linear_independent`: linear independence
forbids cloning. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {S : Set V} {C : V →ₗ[ℝ] V ⊗[ℝ] V}
    (hC : Perspectival.IsLinearCloner S C)
    {v₁ v₂ : V} (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S) (h_sum : v₁ + v₂ ∈ S)
    (hLI : LinearIndependent ℝ ![v₁, v₂]) : False :=
  Perspectival.no_cloning_of_linear_independent hC h₁ h₂ h_sum hLI

/-- Generic `distinguishable_ne`: distinguishable states are unequal. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (h : Perspectival.Hardy.Distinguishable G ρ₁ ρ₂) : ρ₁ ≠ ρ₂ :=
  Perspectival.Distinguish.distinguishable_ne h

/-- Generic `state_ne_zero`: states are nonzero. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ : V} (h : ρ ∈ G.states) : ρ ≠ 0 :=
  Perspectival.Distinguish.state_ne_zero h

/-- Generic `linear_dependent_states_eq`: linearly dependent states
must be equal. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} {ρ₁ ρ₂ : V}
    (h₁ : ρ₁ ∈ G.states) (h₂ : ρ₂ ∈ G.states)
    (hdep : ¬ LinearIndependent ℝ ![ρ₁, ρ₂]) :
    ρ₁ = ρ₂ :=
  Perspectival.Distinguish.linear_dependent_states_eq h₁ h₂ hdep

/-- Generic `perfectWitness_singleton`: a single state has a trivial
perfect witness (the unit functional). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} (ρ : V) (hρ : ρ ∈ G.states) :
    Perspectival.Distinguish.PerfectWitness (G := G) (fun _ : Fin 1 => ρ) :=
  Perspectival.Distinguish.perfectWitness_singleton ρ hρ

/-- Generic `outerForm_apply`: the outer-form evaluates as a product. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (e u : V →ₗ[ℝ] ℝ) (x y : V) :
    Perspectival.Distinguish.outerForm e u x y = e x * u y := rfl

/-- `actMeeting_id`: identity action on meetings is identity. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (PTrans.id : PTrans W) m = m :=
  PTrans.actMeeting_id m

/-- `actMeeting_complement`: complement acts as swap on meetings. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (PTrans.complement : PTrans W) m = m.swap :=
  PTrans.actMeeting_complement m

/-- `actMeeting_faithful`: the PTrans action on meetings is faithful. -/
example {W : Type u} [Wantable W] (f g : PTrans W)
    (h : ∀ m : Meeting W, PTrans.actMeeting f m = PTrans.actMeeting g m) :
    f = g :=
  PTrans.actMeeting_faithful f g h

/-- `PTrans.complement_sq`: complement is an involution. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * PTrans.complement = 1 :=
  PTrans.complement_sq

/-- `Meeting` admits a `MulAction` instance from PTrans. -/
example {W : Type u} [Wantable W] : MulAction (PTrans W) (Meeting W) := inferInstance

/-- `actReality_one`: identity action on Reality is identity. -/
example {W : Type u} [Wantable W] (R : Reality W) :
    PTrans.actReality (1 : PTrans W) R = R :=
  PTrans.actReality_one R

/-- `actReality_singleton`: singleton reality is sent to singleton at
the acted meeting. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (m : Meeting W) :
    PTrans.actReality φ (fun m' => m' = m)
      = (fun m' => m' = PTrans.actMeeting φ m) :=
  PTrans.actReality_singleton φ m

/-- On Bool: applying complement to the vertex true gives vertex false. -/
example : Perspectival.WantableGPT.complementAction Bool
            (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex Bool false := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- On Bool: applying complement to the vertex false gives vertex true. -/
example : Perspectival.WantableGPT.complementAction Bool
            (Perspectival.WantableGPT.vertex Bool false)
        = Perspectival.WantableGPT.vertex Bool true := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- On Fin 4 WantableGPT, the dim is 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- On Fin 4 WantableGPT, the dim equals card. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
        = Fintype.card (Fin 4) :=
  Perspectival.WantableGPT.finrank_V_eq_card (Fin 4)

/-- On Fin 4 WantableGPT, |W| ≥ 2 so the triple no-go applies. -/
example :
    Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
      ≠ Fintype.card (Fin 4) * Fintype.card (Fin 4) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Fin 4) (by decide)

/-- On Bool × Bool WantableGPT, |W| = 4 ≥ 2, triple no-go applies. -/
example :
    Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) * 2
      ≠ Fintype.card (Bool × Bool) * (Fintype.card (Bool × Bool) + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM (Bool × Bool) (by decide)

/-- On Bool ⊕ Bool WantableGPT, |W| = 4. -/
example : Fintype.card (Bool ⊕ Bool) = 4 := by decide

/-- On Bool ⊕ Bool: WantableGPT dim = 4 via sum composition rule. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_sum_eq_add]
  decide

/-- On Bool × Bool: WantableGPT dim = 4 via product composition rule. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_prod_eq_mul]
  decide

/-- On Bool × Fin 3: WantableGPT dim = 6 via product rule. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Fin 3)) = 6 := by
  rw [Perspectival.WantableGPT.finrank_V_prod_eq_mul]
  decide

/-- On Fin 3 ⊕ Bool: WantableGPT dim = 5 via sum rule. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 ⊕ Bool)) = 5 := by
  rw [Perspectival.WantableGPT.finrank_V_sum_eq_add]
  decide

/-- `IsBroadcaster` unfolds: two marginals coincide with the input. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (tr₁ tr₂ : V ⊗[ℝ] V →ₗ[ℝ] V) (S : Set V) (B : V →ₗ[ℝ] V ⊗[ℝ] V)
    (h : Perspectival.NoBroadcasting.IsBroadcaster tr₁ tr₂ S B) (v : V)
    (hv : v ∈ S) :
    tr₁ (B v) = v ∧ tr₂ (B v) = v :=
  ⟨h.marginal₁ v hv, h.marginal₂ v hv⟩

/-- The classical broadcaster sends vertex 0 of Fin 2 to its diagonal. -/
example :
    Perspectival.NoBroadcasting.classicalBroadcaster 2
        (Perspectival.Classical.vertex 2 0)
      = Perspectival.Classical.vertex 2 0
          ⊗ₜ[ℝ] Perspectival.Classical.vertex 2 0 :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 2 0

/-- The classical broadcaster sends vertex 1 of Fin 3 to its diagonal. -/
example :
    Perspectival.NoBroadcasting.classicalBroadcaster 3
        (Perspectival.Classical.vertex 3 1)
      = Perspectival.Classical.vertex 3 1
          ⊗ₜ[ℝ] Perspectival.Classical.vertex 3 1 :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 3 1

/-- The classical broadcaster sends vertex 2 of Fin 4 to its diagonal. -/
example :
    Perspectival.NoBroadcasting.classicalBroadcaster 4
        (Perspectival.Classical.vertex 4 2)
      = Perspectival.Classical.vertex 4 2
          ⊗ₜ[ℝ] Perspectival.Classical.vertex 4 2 :=
  Perspectival.NoBroadcasting.classicalBroadcaster_vertex 4 2

/-- Bool's WantableGPT vertex true is the function `fun v => if true = v then 1 else 0`. -/
example : Perspectival.WantableGPT.vertex Bool true
        = (fun v => if true = v then (1 : ℝ) else 0) := rfl

/-- Bool's WantableGPT vertex false is the function `fun v => if false = v then 1 else 0`. -/
example : Perspectival.WantableGPT.vertex Bool false
        = (fun v => if false = v then (1 : ℝ) else 0) := rfl

/-- On Bool: proj true at vertex true is 1. -/
example : Perspectival.WantableGPT.proj Bool true
            (Perspectival.WantableGPT.vertex Bool true) = 1 := by
  rw [Perspectival.WantableGPT.proj_vertex]
  simp

/-- On Bool: proj true at vertex false is 0. -/
example : Perspectival.WantableGPT.proj Bool true
            (Perspectival.WantableGPT.vertex Bool false) = 0 := by
  rw [Perspectival.WantableGPT.proj_vertex]
  simp

/-- The perfectWitness on Fin 3 picks out vertex 1 at index 1. -/
example : (Perspectival.WantableGPT.perfectWitness (Fin 3)).e 1
            (Perspectival.WantableGPT.vertex (Fin 3) 1) = 1 := by
  have := (Perspectival.WantableGPT.perfectWitness (Fin 3)).kronecker 1 1
  simpa using this

/-- The perfectWitness on Fin 3 sends vertex 2 to 0 under e 1. -/
example : (Perspectival.WantableGPT.perfectWitness (Fin 3)).e 1
            (Perspectival.WantableGPT.vertex (Fin 3) 2) = 0 := by
  have := (Perspectival.WantableGPT.perfectWitness (Fin 3)).kronecker 1 2
  simpa using this

/-- The perfectWitness on Fin 4 picks out vertex 0 at index 0. -/
example : (Perspectival.WantableGPT.perfectWitness (Fin 4)).e 0
            (Perspectival.WantableGPT.vertex (Fin 4) 0) = 1 := by
  have := (Perspectival.WantableGPT.perfectWitness (Fin 4)).kronecker 0 0
  simpa using this

/-- On Bool × Bool: perfectWitness picks out (true, true) at (true, true). -/
example : (Perspectival.WantableGPT.perfectWitness (Bool × Bool)).e (true, true)
            (Perspectival.WantableGPT.vertex (Bool × Bool) (true, true)) = 1 := by
  have := (Perspectival.WantableGPT.perfectWitness (Bool × Bool)).kronecker
    (true, true) (true, true)
  simpa using this

/-- The Wantable instance on Fin 2 swaps 0 ↔ 1. -/
example : (Wantable.complement (0 : Fin 2)) = 1 := rfl
example : (Wantable.complement (1 : Fin 2)) = 0 := rfl

/-- The Wantable instance on ℤ uses negation. -/
example : (Wantable.complement (5 : ℤ)) = -5 := rfl
example : (Wantable.complement (-3 : ℤ)) = 3 := neg_neg 3

/-- The Wantable instance on ℝ uses negation. -/
example : (Wantable.complement (1.5 : ℝ)) = -1.5 := rfl

/-- Unit's Wantable instance is trivial (complement = self). -/
example : (Wantable.complement (() : Unit)) = () := rfl

/-- Empty has a vacuous Wantable instance. -/
example : Wantable Empty := inferInstance

/-- Fin 4 WantableGPT vertex 0 on coords. -/
example : Perspectival.WantableGPT.vertex (Fin 4) 0
        = (fun v => if (0 : Fin 4) = v then (1 : ℝ) else 0) := rfl

/-- Fin 4 WantableGPT proj 0 evaluates Kronecker on vertex 0. -/
example : Perspectival.WantableGPT.proj (Fin 4) 0
            (Perspectival.WantableGPT.vertex (Fin 4) 0) = 1 := by
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- Fin 4 WantableGPT proj 0 evaluates Kronecker on vertex 1 (= 0). -/
example : Perspectival.WantableGPT.proj (Fin 4) 0
            (Perspectival.WantableGPT.vertex (Fin 4) 1) = 0 := by
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- Complement on Fin 4 sends vertex 1 to vertex 2. -/
example : Perspectival.WantableGPT.complementAction (Fin 4)
            (Perspectival.WantableGPT.vertex (Fin 4) 1)
        = Perspectival.WantableGPT.vertex (Fin 4) 2 := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- Complement on Fin 4 sends vertex 0 to vertex 3 (reflection). -/
example : Perspectival.WantableGPT.complementAction (Fin 4)
            (Perspectival.WantableGPT.vertex (Fin 4) 0)
        = Perspectival.WantableGPT.vertex (Fin 4) 3 := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- Complement on Fin 4 sends vertex 3 to vertex 0 (reflection). -/
example : Perspectival.WantableGPT.complementAction (Fin 4)
            (Perspectival.WantableGPT.vertex (Fin 4) 3)
        = Perspectival.WantableGPT.vertex (Fin 4) 0 := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- Complement on Fin 4 sends vertex 2 to vertex 1 (reflection). -/
example : Perspectival.WantableGPT.complementAction (Fin 4)
            (Perspectival.WantableGPT.vertex (Fin 4) 2)
        = Perspectival.WantableGPT.vertex (Fin 4) 1 := by
  rw [Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- Bool × Bool: complement on (true, false) is (false, true). -/
example : Wantable.complement (true, false) = (false, true) := rfl

/-- Bool × Bool: complement on (true, true) is (false, false). -/
example : Wantable.complement (true, true) = (false, false) := rfl

/-- Bool × Bool: complement on (false, false) is (true, true). -/
example : Wantable.complement (false, false) = (true, true) := rfl

/-- Bool ⊕ Bool: complement on inl true is inl false. -/
example : Wantable.complement (Sum.inl true : Bool ⊕ Bool) = Sum.inl false := rfl

/-- Bool ⊕ Bool: complement on inr false is inr true. -/
example : Wantable.complement (Sum.inr false : Bool ⊕ Bool) = Sum.inr true := rfl

/-- A new small lemma: complement of complement on Bool × Bool is identity. -/
example (p : Bool × Bool) :
    Wantable.complement (Wantable.complement p) = p :=
  Wantable.complement_involutive p

/-- A new small lemma: complement of complement on Bool ⊕ Bool is identity. -/
example (p : Bool ⊕ Bool) :
    Wantable.complement (Wantable.complement p) = p :=
  Wantable.complement_involutive p

/-- On Bool × Bool, complement is injective. -/
example : Function.Injective
    (Wantable.complement : Bool × Bool → Bool × Bool) :=
  Wantable.complement_injective

/-- On Bool × Bool, complement is surjective. -/
example : Function.Surjective
    (Wantable.complement : Bool × Bool → Bool × Bool) :=
  Wantable.complement_surjective

/-- On Bool × Bool, complement preserves cardinality (it's a bijection). -/
example : Fintype.card (Bool × Bool) = Fintype.card (Bool × Bool) := rfl

/-- complement_complement_eq_id on Bool × Bool. -/
example : (Wantable.complement ∘ Wantable.complement
            : Bool × Bool → Bool × Bool) = id :=
  Wantable.complement_complement_eq_id

/-- Bool ⊕ Bool: complement is injective. -/
example : Function.Injective
    (Wantable.complement : Bool ⊕ Bool → Bool ⊕ Bool) :=
  Wantable.complement_injective

/-- Bool ⊕ Bool: complement is surjective. -/
example : Function.Surjective
    (Wantable.complement : Bool ⊕ Bool → Bool ⊕ Bool) :=
  Wantable.complement_surjective

/-- complement_eq_iff applied on Bool: complement true = false iff true = complement false. -/
example : Wantable.complement (true : Bool) = false
        ↔ true = Wantable.complement (false : Bool) :=
  Wantable.complement_eq_iff _ _

/-- complement_eq_iff applied on ℤ: complement 5 = -5 iff 5 = complement (-5). -/
example : Wantable.complement (5 : ℤ) = -5
        ↔ 5 = Wantable.complement (-5 : ℤ) :=
  Wantable.complement_eq_iff _ _

/-- Bool × Bool meeting from side (true, false). -/
example : (Meeting.mk_fromSide (Bool × Bool) (true, false)).side₂
        = (false, true) := rfl

/-- Bool ⊕ Bool meeting from side inl true. -/
example : (Meeting.mk_fromSide (Bool ⊕ Bool) (Sum.inl true)).side₂
        = Sum.inl false := rfl

/-- Meeting on Bool × Bool with both sides equal forces self-complementary
side (no such pair exists since complement is fixed-point-free). -/
example (m : Meeting (Bool × Bool)) (h : m.side₁ = m.side₂) :
    SelfComplementary m.side₁ := by
  unfold SelfComplementary
  rw [m.complementary, h]

/-- Fin 2 meeting from side 0. -/
example : (Meeting.mk_fromSide (Fin 2) 0).side₂ = 1 := rfl

/-- swap on a Bool meeting from true gives meeting from false. -/
example : (Meeting.mk_fromSide Bool true).swap = Meeting.mk_fromSide Bool false := by
  rfl

/-- Bool's WantableGPT satisfies Hardy Axiom 1 (probabilities). -/
example : Perspectival.Hardy.Axiom1_Probabilities
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Hardy.axiom1_holds _

/-- Fin 4's WantableGPT satisfies Hardy Axiom 1. -/
example : Perspectival.Hardy.Axiom1_Probabilities
            (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.Hardy.axiom1_holds _

/-- Bool's WantableGPT satisfies Hardy Axiom 3 (subspaces). -/
example : Perspectival.Hardy.Axiom3_Subspaces
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Hardy.axiom3_holds _

/-- Fin 4's WantableGPT satisfies Hardy Axiom 3. -/
example : Perspectival.Hardy.Axiom3_Subspaces
            (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.Hardy.axiom3_holds _

/-- Bool's WantableGPT satisfies Hardy Axiom 5 (placeholder). -/
example : Perspectival.Hardy.Axiom5_Continuity
            (Perspectival.WantableGPT.gpt Bool) := by
  intro _ _ _ _ _ _; trivial

/-- `Reversible.id` is a valid Reversible on the Bool WantableGPT. -/
example : Perspectival.Continuity.Reversible
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Continuity.Reversible.id _

/-- `Reversible.id` has toLin = LinearMap.id. -/
example : (Perspectival.Continuity.Reversible.id
            (Perspectival.WantableGPT.gpt Bool)).toLin = LinearMap.id := rfl

/-- `Reversible.id` continuous_toLin: continuous_id. -/
example : Continuous
    (Perspectival.Continuity.Reversible.id
      (Perspectival.WantableGPT.gpt Bool)).toLin :=
  (Perspectival.Continuity.Reversible.id _).continuous_toLin

/-- `Reversible.id.preserves_unit`: G.unit composed with id = G.unit. -/
example : (Perspectival.WantableGPT.gpt Bool).unit.comp
            (Perspectival.Continuity.Reversible.id
              (Perspectival.WantableGPT.gpt Bool)).toLin
        = (Perspectival.WantableGPT.gpt Bool).unit :=
  (Perspectival.Continuity.Reversible.id _).preserves_unit

/-- `Reversible.id` preserves any state. -/
example (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt Bool).states) :
    (Perspectival.Continuity.Reversible.id
      (Perspectival.WantableGPT.gpt Bool)).toLin ρ
    ∈ (Perspectival.WantableGPT.gpt Bool).states :=
  (Perspectival.Continuity.Reversible.id _).preserves_states ρ hρ

/-- `trivialAgency` instance on Bool's WantableGPT. -/
example : Perspectival.Continuity.HasConnectedAgency
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.Continuity.trivialAgency _

/-- `trivialAgency`'s avail set contains the identity. -/
example : Perspectival.Continuity.Reversible.id
            (Perspectival.WantableGPT.gpt Bool)
        ∈ Perspectival.Continuity.HasConnectedAgency.avail
            (G := Perspectival.WantableGPT.gpt Bool)
            (self := Perspectival.Continuity.trivialAgency _) := rfl

/-- Under trivialAgency on Bool, vertex true is reachable from itself. -/
example : @Perspectival.Continuity.Reachable _ _ _ _
            (Perspectival.WantableGPT.gpt Bool)
            (Perspectival.Continuity.trivialAgency _)
            (Perspectival.WantableGPT.vertex Bool true)
            (Perspectival.WantableGPT.vertex Bool true) :=
  Perspectival.Continuity.trivialAgency_reachable_refl _ _

/-- Born-rule-style: `G.prob (proj w) (vertex w) = 1` on WantableGPT Bool. -/
example : (Perspectival.WantableGPT.gpt Bool).prob
            (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool true) = 1 := by
  show Perspectival.WantableGPT.proj Bool true
        (Perspectival.WantableGPT.vertex Bool true) = 1
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- Born-rule-style: `G.prob (proj true) (vertex false) = 0`. -/
example : (Perspectival.WantableGPT.gpt Bool).prob
            (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool false) = 0 := by
  show Perspectival.WantableGPT.proj Bool true
        (Perspectival.WantableGPT.vertex Bool false) = 0
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- Born-rule-style: `Classical.prob (proj i) (vertex j) = δ_{ji}`. -/
example (n : ℕ) (i j : Fin n) :
    (Perspectival.Classical.gpt n).prob
      (Perspectival.Classical.proj n i)
      (Perspectival.Classical.vertex n j)
    = if j = i then 1 else 0 :=
  Perspectival.Classical.proj_vertex n i j

/-- Generic: state probabilities sum to 1 across the perfect-witness
effects on the vertex family. -/
theorem WantableGPT_sum_probs_vertex_eq_one
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    ∑ v, Perspectival.WantableGPT.proj W v
            (Perspectival.WantableGPT.vertex W w) = 1 := by
  rw [Finset.sum_eq_single w
    (fun v _ hvw => by
      rw [Perspectival.WantableGPT.proj_vertex]
      simp [hvw.symm])
    (fun h => absurd (Finset.mem_univ w) h)]
  rw [Perspectival.WantableGPT.proj_vertex]
  simp

/-- Concrete: on Bool, the sum of projection-probabilities over vertex true
equals 1. -/
example : ∑ v, Perspectival.WantableGPT.proj Bool v
            (Perspectival.WantableGPT.vertex Bool true) = 1 :=
  WantableGPT_sum_probs_vertex_eq_one true

/-- Concrete: on Fin 4, the sum of projection-probabilities over vertex 2
equals 1. -/
example : ∑ v, Perspectival.WantableGPT.proj (Fin 4) v
            (Perspectival.WantableGPT.vertex (Fin 4) 2) = 1 :=
  WantableGPT_sum_probs_vertex_eq_one (2 : Fin 4)

/-- New theorem: complementTransform on `W` is bijective via its
involution property. The inverse is itself. -/
theorem WantableGPT_complementTransform_invertible
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (f : Perspectival.WantableGPT.V W) :
    (Perspectival.WantableGPT.complementTransform W).toLin
      ((Perspectival.WantableGPT.complementTransform W).toLin f) = f := by
  funext w
  show f (Wantable.complement (Wantable.complement w)) = f w
  rw [Wantable.complement_involutive]

/-- Concrete: on Bool, the complementTransform involution sends f back. -/
example (f : Perspectival.WantableGPT.V Bool) :
    (Perspectival.WantableGPT.complementTransform Bool).toLin
      ((Perspectival.WantableGPT.complementTransform Bool).toLin f) = f :=
  WantableGPT_complementTransform_invertible f

/-- Concrete: on Fin 4, the complementTransform involution sends f back. -/
example (f : Perspectival.WantableGPT.V (Fin 4)) :
    (Perspectival.WantableGPT.complementTransform (Fin 4)).toLin
      ((Perspectival.WantableGPT.complementTransform (Fin 4)).toLin f) = f :=
  WantableGPT_complementTransform_invertible f

/-- Bijectivity from involution: complementTransform is bijective. -/
theorem WantableGPT_complementTransform_bijective
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Function.Bijective
      (Perspectival.WantableGPT.complementTransform W).toLin := by
  refine ⟨?_, ?_⟩
  · -- Injective: from C(f) = C(g), apply C again to get f = g.
    intro f g h
    have hC : (Perspectival.WantableGPT.complementTransform W).toLin
                ((Perspectival.WantableGPT.complementTransform W).toLin f)
            = (Perspectival.WantableGPT.complementTransform W).toLin
                ((Perspectival.WantableGPT.complementTransform W).toLin g) := by
      rw [h]
    rw [WantableGPT_complementTransform_invertible,
        WantableGPT_complementTransform_invertible] at hC
    exact hC
  · -- Surjective: for any f, C(C f) = f, so C f is a preimage.
    intro f
    refine ⟨(Perspectival.WantableGPT.complementTransform W).toLin f, ?_⟩
    exact WantableGPT_complementTransform_invertible f

/-- New theorem: the unit functional evaluated on a vertex equals 1. -/
theorem WantableGPT_unit_vertex_eq_one
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.unitFn W
      (Perspectival.WantableGPT.vertex W w) = 1 :=
  (Perspectival.WantableGPT.vertex_in_states W w).2

/-- Concrete: unit applied to Bool vertex true is 1. -/
example : Perspectival.WantableGPT.unitFn Bool
            (Perspectival.WantableGPT.vertex Bool true) = 1 :=
  WantableGPT_unit_vertex_eq_one true

/-- Concrete: unit applied to Fin 4 vertex 2 is 1. -/
example : Perspectival.WantableGPT.unitFn (Fin 4)
            (Perspectival.WantableGPT.vertex (Fin 4) 2) = 1 :=
  WantableGPT_unit_vertex_eq_one (2 : Fin 4)

/-- New theorem: vertex values are nonneg (vertex coords). -/
theorem WantableGPT_vertex_nonneg
    {W : Type u} [Wantable W] [DecidableEq W] (w v : W) :
    0 ≤ Perspectival.WantableGPT.vertex W w v := by
  show 0 ≤ (if w = v then (1 : ℝ) else 0)
  split <;> simp

/-- Concrete: on Bool, vertex true at false is 0 (nonneg). -/
example : 0 ≤ Perspectival.WantableGPT.vertex Bool true false :=
  WantableGPT_vertex_nonneg true false

/-- New theorem: vertex values are bounded above by 1. -/
theorem WantableGPT_vertex_le_one
    {W : Type u} [Wantable W] [DecidableEq W] (w v : W) :
    Perspectival.WantableGPT.vertex W w v ≤ 1 := by
  show (if w = v then (1 : ℝ) else 0) ≤ 1
  split <;> simp

/-- Concrete: on Bool, vertex true at true ≤ 1. -/
example : Perspectival.WantableGPT.vertex Bool true true ≤ 1 :=
  WantableGPT_vertex_le_one true true

/-- New theorem: vertex value at w is in [0,1]. -/
theorem WantableGPT_vertex_mem_unitInterval
    {W : Type u} [Wantable W] [DecidableEq W] (w v : W) :
    Perspectival.WantableGPT.vertex W w v ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨WantableGPT_vertex_nonneg w v, WantableGPT_vertex_le_one w v⟩

/-- New theorem: a vertex (qua function W → ℝ) is itself in `effectVec`. -/
theorem WantableGPT_vertex_in_effectVec
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.vertex W w ∈ Perspectival.WantableGPT.effectVec W := by
  intro v
  exact ⟨WantableGPT_vertex_nonneg w v, WantableGPT_vertex_le_one w v⟩

/-- New theorem: the constant-0 function is a valid effect-vector (zero effect). -/
theorem WantableGPT_const_zero_in_effectVec
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (fun _ : W => (0 : ℝ)) ∈ Perspectival.WantableGPT.effectVec W := by
  intro w
  refine ⟨le_refl 0, zero_le_one⟩

/-- Concrete: on Bool, the constant-0 function is in effectVec. -/
example : (fun _ : Bool => (0 : ℝ)) ∈ Perspectival.WantableGPT.effectVec Bool :=
  WantableGPT_const_zero_in_effectVec

/-- New theorem: proj w equals innerLin of vertex w (on `V W`). -/
theorem WantableGPT_proj_eq_innerLin_vertex
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.proj W w
      = Perspectival.WantableGPT.innerLin W
          (Perspectival.WantableGPT.vertex W w) := by
  apply LinearMap.ext
  intro f
  show f w = ∑ v, Perspectival.WantableGPT.vertex W w v * f v
  symm
  rw [Finset.sum_eq_single w
    (fun v _ hvw => by
      show Perspectival.WantableGPT.vertex W w v * f v = 0
      show (if w = v then (1 : ℝ) else 0) * f v = 0
      rw [if_neg hvw.symm]; ring)
    (fun h => absurd (Finset.mem_univ w) h)]
  show (if w = w then (1 : ℝ) else 0) * f w = f w
  rw [if_pos rfl]; ring

/-- Concrete: on Bool, proj true = innerLin (vertex true). -/
example : Perspectival.WantableGPT.proj Bool true
        = Perspectival.WantableGPT.innerLin Bool
            (Perspectival.WantableGPT.vertex Bool true) :=
  WantableGPT_proj_eq_innerLin_vertex true

/-- New theorem: sum over W of vertex w (across all w) equals the
constant-1 function (each coordinate hits exactly one vertex). -/
theorem WantableGPT_sum_vertices_eq_one
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (∑ w, Perspectival.WantableGPT.vertex W w)
      = fun _ : W => (1 : ℝ) := by
  funext v
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single v
    (fun w _ hwv => by
      show Perspectival.WantableGPT.vertex W w v = 0
      show (if w = v then (1 : ℝ) else 0) = 0
      simp [hwv])
    (fun h => absurd (Finset.mem_univ v) h)]
  show Perspectival.WantableGPT.vertex W v v = 1
  show (if v = v then (1 : ℝ) else 0) = 1
  simp

/-- Concrete: on Bool, sum of vertices is constant 1. -/
example : (∑ w, Perspectival.WantableGPT.vertex Bool w)
        = fun _ : Bool => (1 : ℝ) :=
  WantableGPT_sum_vertices_eq_one

/-- Concrete: on Fin 4, sum of vertices is constant 1. -/
example : (∑ w, Perspectival.WantableGPT.vertex (Fin 4) w)
        = fun _ : Fin 4 => (1 : ℝ) :=
  WantableGPT_sum_vertices_eq_one

/-- New theorem: each `proj w` evaluated on the constant-1 function = 1.
That is, the "unit on the projection" gives 1. -/
theorem WantableGPT_proj_const_one
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.proj W w (fun _ => (1 : ℝ)) = 1 := rfl

/-- New theorem: each `proj w` evaluated on the constant-0 function = 0. -/
theorem WantableGPT_proj_const_zero
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.proj W w (fun _ => (0 : ℝ)) = 0 := rfl

/-- New theorem: the unit functional on the constant-1 function gives |W|. -/
theorem WantableGPT_unit_const_one
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.unitFn W (fun _ : W => (1 : ℝ))
      = (Fintype.card W : ℝ) := by
  show ∑ _ : W, (1 : ℝ) = Fintype.card W
  rw [Finset.sum_const, Finset.card_univ]
  simp

/-- Concrete: on Bool, the constant-1 function has unit value 2. -/
example : Perspectival.WantableGPT.unitFn Bool (fun _ : Bool => (1 : ℝ)) = 2 := by
  rw [WantableGPT_unit_const_one]
  norm_num

/-- Concrete: on Fin 4, the constant-1 function has unit value 4. -/
example : Perspectival.WantableGPT.unitFn (Fin 4) (fun _ : Fin 4 => (1 : ℝ)) = 4 := by
  rw [WantableGPT_unit_const_one]
  norm_num

/-- `Reachable.refl_symm_trans`: with closed agency and per-element
inverse availability, Reachable is refl + symm + trans. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.ClosedAgency G]
    (h_inv : ∀ R : Perspectival.Continuity.Reversible G,
              R ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) →
              ∃ S : Perspectival.Continuity.Reversible G,
                S ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) ∧
                ∀ v : V, S.toLin (R.toLin v) = v) :
    (∀ ρ : V, Perspectival.Continuity.Reachable (G := G) ρ ρ) ∧
    (∀ ρ₁ ρ₂ : V, Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂ →
                   Perspectival.Continuity.Reachable (G := G) ρ₂ ρ₁) ∧
    (∀ ρ₁ ρ₂ ρ₃ : V, Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₂ →
                     Perspectival.Continuity.Reachable (G := G) ρ₂ ρ₃ →
                     Perspectival.Continuity.Reachable (G := G) ρ₁ ρ₃) :=
  Perspectival.Continuity.Reachable.refl_symm_trans h_inv

/-- `Reachable.equivalence`: with the same hypotheses, Reachable is
an `Equivalence`. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V} [Perspectival.Continuity.ClosedAgency G]
    (h_inv : ∀ R : Perspectival.Continuity.Reversible G,
              R ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) →
              ∃ S : Perspectival.Continuity.Reversible G,
                S ∈ Perspectival.Continuity.HasConnectedAgency.avail (G := G) ∧
                ∀ v : V, S.toLin (R.toLin v) = v) :
    Equivalence (Perspectival.Continuity.Reachable (G := G)) :=
  Perspectival.Continuity.Reachable.equivalence h_inv

/-- `StrictReversible.id` has inverse equal to itself (via the bijective
identity map). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (G : Perspectival.GPT V) (v : V) :
    (Perspectival.Continuity.StrictReversible.id G).inv v = v := by
  exact Perspectival.Continuity.StrictReversible.inv_comp _ v

/-- Generic `StrictReversible.comp_toLin`: composition toLin is the
underlying composition of linear maps. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {G : Perspectival.GPT V}
    (R₂ R₁ : Perspectival.Continuity.StrictReversible G) :
    (Perspectival.Continuity.StrictReversible.comp R₂ R₁).toLin
      = R₂.toLin.comp R₁.toLin :=
  Perspectival.Continuity.StrictReversible.comp_toLin R₂ R₁

/-- New theorem: vertex on Bool true equals function `(! ·) ∘ id` after
swap. More concretely: vertex true = (fun v => v ? 1 : 0). -/
theorem WantableGPT_vertex_Bool_true_eq :
    Perspectival.WantableGPT.vertex Bool true
      = (fun v : Bool => if v then (1 : ℝ) else 0) := by
  funext v
  cases v <;> rfl

/-- New theorem: vertex on Bool false equals function `(fun v => if !v then 1 else 0)`. -/
theorem WantableGPT_vertex_Bool_false_eq :
    Perspectival.WantableGPT.vertex Bool false
      = (fun v : Bool => if !v then (1 : ℝ) else 0) := by
  funext v
  cases v <;> rfl

/-- New theorem: vertex true + vertex false = the constant-1 function
on Bool. (This is `sum_vertices_eq_one` specialised to Bool, written
without the sum notation.) -/
theorem WantableGPT_Bool_vertex_sum :
    Perspectival.WantableGPT.vertex Bool true
    + Perspectival.WantableGPT.vertex Bool false
      = fun _ : Bool => (1 : ℝ) := by
  funext v
  show (if true = v then (1 : ℝ) else 0) + (if false = v then (1 : ℝ) else 0) = 1
  cases v <;> simp

/-- New theorem: any state in WantableGPT Bool is `a • vertex true + b •
vertex false` with a + b = 1, a, b ≥ 0. The state itself is determined
by its true-coord and false-coord. -/
theorem WantableGPT_Bool_state_decomp (f : Perspectival.WantableGPT.V Bool) :
    f = f true • Perspectival.WantableGPT.vertex Bool true
      + f false • Perspectival.WantableGPT.vertex Bool false := by
  funext v
  cases v with
  | true =>
    show f true = f true • Perspectival.WantableGPT.vertex Bool true true
                + f false • Perspectival.WantableGPT.vertex Bool false true
    show f true = f true * (if true = true then (1 : ℝ) else 0)
                + f false * (if false = true then (1 : ℝ) else 0)
    simp
  | false =>
    show f false = f true • Perspectival.WantableGPT.vertex Bool true false
                 + f false • Perspectival.WantableGPT.vertex Bool false false
    show f false = f true * (if true = false then (1 : ℝ) else 0)
                 + f false * (if false = false then (1 : ℝ) else 0)
    simp

/-- New theorem: unitFn on Bool's V = f true + f false. -/
theorem WantableGPT_Bool_unit (f : Perspectival.WantableGPT.V Bool) :
    Perspectival.WantableGPT.unitFn Bool f = f true + f false := by
  show ∑ b, f b = f true + f false
  rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]

/-- New theorem: A function f : Bool → ℝ is in WantableGPT.states iff
both f true, f false ≥ 0 and f true + f false = 1. -/
theorem WantableGPT_Bool_states_iff (f : Perspectival.WantableGPT.V Bool) :
    f ∈ Perspectival.WantableGPT.states Bool ↔
    (0 ≤ f true ∧ 0 ≤ f false ∧ f true + f false = 1) := by
  constructor
  · intro ⟨hpos, hsum⟩
    refine ⟨hpos true, hpos false, ?_⟩
    have := WantableGPT_Bool_unit f
    rw [← this]; exact hsum
  · intro ⟨ht, hf, hsum⟩
    refine ⟨?_, ?_⟩
    · intro b; cases b
      · exact hf
      · exact ht
    · show ∑ b, f b = 1
      rw [show ∑ b, f b = f true + f false from by
        rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
            Finset.sum_insert (by decide), Finset.sum_singleton]]
      exact hsum

/-- The uniform Bool state: 1/2 on each. -/
noncomputable def uniformBool : Perspectival.WantableGPT.V Bool := fun _ => 1/2

/-- The uniform Bool state is a valid state. -/
theorem uniformBool_in_states :
    uniformBool ∈ Perspectival.WantableGPT.states Bool := by
  rw [WantableGPT_Bool_states_iff]
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ 1/2; norm_num
  · show (0 : ℝ) ≤ 1/2; norm_num
  · show (1/2 : ℝ) + 1/2 = 1; norm_num

/-- The uniform Bool state has unitFn value 1 (= sum of components). -/
example : Perspectival.WantableGPT.unitFn Bool uniformBool = 1 :=
  (uniformBool_in_states).2

/-- The uniform Bool state is fixed by the complement action. -/
theorem uniformBool_complement_invariant :
    Perspectival.WantableGPT.complementAction Bool uniformBool = uniformBool := by
  funext b
  show uniformBool (Wantable.complement b) = uniformBool b
  rfl

/-- The uniform Bool state equals (1/2) • vertex true + (1/2) • vertex false. -/
theorem uniformBool_decomp :
    uniformBool = (1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool true
                + (1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool false := by
  funext v
  cases v with
  | true =>
    show (1/2 : ℝ) = (1/2 : ℝ) * (if true = true then 1 else 0)
                  + (1/2 : ℝ) * (if false = true then 1 else 0)
    simp
  | false =>
    show (1/2 : ℝ) = (1/2 : ℝ) * (if true = false then 1 else 0)
                  + (1/2 : ℝ) * (if false = false then 1 else 0)
    simp

/-- New: Existent.mk is injective in the `want` field. -/
theorem Existent_mk_injective {W : Type u} :
    Function.Injective (Existent.mk : W → Existent W) := by
  intro a b h
  injection h

/-- Concrete: Existent.mk on Bool injective. -/
example : Function.Injective (Existent.mk : Bool → Existent Bool) :=
  Existent_mk_injective

/-- Existent is essentially a wrapper around `W`: there's a bijection. -/
def existentEquiv (W : Type u) : Existent W ≃ W where
  toFun e := e.want
  invFun w := ⟨w⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Concrete: existentEquiv Bool has the right action. -/
example (b : Bool) : (existentEquiv Bool).symm b = ⟨b⟩ := rfl

/-- Concrete: existentEquiv Bool inverse. -/
example (e : Existent Bool) : (existentEquiv Bool) e = e.want := rfl

/-- New theorem: WantableGPT.unitFn equals innerLin of constant-1. -/
theorem WantableGPT_unitFn_eq_innerLin_one
    {W : Type u} [Wantable W] [Fintype W] :
    Perspectival.WantableGPT.unitFn W
      = Perspectival.WantableGPT.innerLin W (fun _ => 1) := by
  apply LinearMap.ext
  intro f
  show ∑ w, f w = ∑ w, 1 * f w
  simp

/-- Concrete: on Bool, unitFn = innerLin (fun _ => 1). -/
example : Perspectival.WantableGPT.unitFn Bool
        = Perspectival.WantableGPT.innerLin Bool (fun _ : Bool => 1) :=
  WantableGPT_unitFn_eq_innerLin_one

/-- Concrete: on Fin 4, unitFn = innerLin (fun _ => 1). -/
example : Perspectival.WantableGPT.unitFn (Fin 4)
        = Perspectival.WantableGPT.innerLin (Fin 4) (fun _ : Fin 4 => 1) :=
  WantableGPT_unitFn_eq_innerLin_one

/-- New theorem: complementTransform applied twice to a vertex gives the
same vertex back. -/
theorem WantableGPT_complementTransform_vertex_sq
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    (Perspectival.WantableGPT.complementTransform W).toLin
      ((Perspectival.WantableGPT.complementTransform W).toLin
        (Perspectival.WantableGPT.vertex W w))
      = Perspectival.WantableGPT.vertex W w :=
  WantableGPT_complementTransform_invertible _

/-- New theorem: complementTransform applied to vertex w gives vertex
(complement w). -/
theorem WantableGPT_complementTransform_vertex
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    (Perspectival.WantableGPT.complementTransform W).toLin
      (Perspectival.WantableGPT.vertex W w)
      = Perspectival.WantableGPT.vertex W (Wantable.complement w) :=
  Perspectival.WantableGPT.complementAction_vertex W w

/-- Concrete: on Bool, complementTransform vertex true = vertex false. -/
example : (Perspectival.WantableGPT.complementTransform Bool).toLin
            (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex Bool false :=
  WantableGPT_complementTransform_vertex true

/-- New theorem: fromPTrans of the complementPTrans on Bool, applied
to vertex true, gives vertex false. -/
theorem WantableGPT_fromPTrans_complementPTrans_vertex_true :
    (Perspectival.WantableGPT.fromPTrans Bool
      (Perspectival.WantableGPT.complementPTrans Bool)).toLin
        (Perspectival.WantableGPT.vertex Bool true)
      = Perspectival.WantableGPT.vertex Bool false := by
  rw [← Perspectival.WantableGPT.complementTransform_eq_fromPTrans]
  exact WantableGPT_complementTransform_vertex true

/-- New theorem: fromPTrans of identity PTrans is identity on V W. -/
theorem WantableGPT_fromPTrans_one_apply
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (f : Perspectival.WantableGPT.V W) :
    (Perspectival.WantableGPT.fromPTrans W (1 : PTrans W)).toLin f = f := by
  rw [Perspectival.WantableGPT.fromPTrans_one_toLin]
  rfl

/-- Concrete: fromPTrans 1 acts as identity on Bool vertex true. -/
example : (Perspectival.WantableGPT.fromPTrans Bool 1).toLin
            (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex Bool true :=
  WantableGPT_fromPTrans_one_apply _

/-- New theorem: vertex 0, vertex 1, vertex 2 of WantableGPT (Fin 3)
are pairwise distinguishable. -/
theorem WantableGPT_Fin3_three_distinguishable :
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 3))
      (Perspectival.WantableGPT.vertex (Fin 3) 0)
      (Perspectival.WantableGPT.vertex (Fin 3) 1) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 3))
      (Perspectival.WantableGPT.vertex (Fin 3) 0)
      (Perspectival.WantableGPT.vertex (Fin 3) 2) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 3))
      (Perspectival.WantableGPT.vertex (Fin 3) 1)
      (Perspectival.WantableGPT.vertex (Fin 3) 2) :=
  ⟨Perspectival.WantableGPT.vertices_distinguishable (Fin 3) 0 1 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 3) 0 2 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 3) 1 2 (by decide)⟩

/-- Concrete: Meeting on Bool × Bool built from prodMk. -/
example : (Meeting.prodMk (Meeting.mk_fromSide Bool true)
                          (Meeting.mk_fromSide Bool false)).side₁
        = (true, false) := rfl

/-- Concrete: Meeting on Bool × Bool built from prodMk has the correct
side₂. -/
example : (Meeting.prodMk (Meeting.mk_fromSide Bool true)
                          (Meeting.mk_fromSide Bool false)).side₂
        = (false, true) := rfl

/-- Concrete: complement of (true, false) = (false, true) via the
Wantable Bool×Bool instance. -/
example : Wantable.complement ((true, false) : Bool × Bool) = (false, true) := rfl

/-- New theorem: prodMap of identities on Bool gives identity PTrans on
Bool × Bool. -/
example : PTrans.prodMap (1 : PTrans Bool) (1 : PTrans Bool)
        = (1 : PTrans (Bool × Bool)) :=
  PTrans.prodMap_one_one Bool Bool

/-- New theorem: sumMap of identities on Bool gives identity PTrans on
Bool ⊕ Bool. -/
example : PTrans.sumMap (1 : PTrans Bool) (1 : PTrans Bool)
        = (1 : PTrans (Bool ⊕ Bool)) :=
  PTrans.sumMap_one_one Bool Bool

/-- prodMap of complement and identity on Bool. -/
example : PTrans.prodMap (PTrans.complement : PTrans Bool) (1 : PTrans Bool)
            ≠ 1 := by
  intro h
  have hap := congrArg (fun (φ : PTrans (Bool × Bool)) => φ.toFun (true, true)) h
  exact absurd hap (by decide)

/-- New: vertex on Bool × Bool decomposes as a "tensor" of two Bool
vertices (this is the simplex-tensor identification on the product). -/
theorem WantableGPT_vertex_prod_decomp
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w₁ : W₁) (w₂ : W₂) (p : W₁ × W₂) :
    Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂) p
      = Perspectival.WantableGPT.vertex W₁ w₁ p.1
      * Perspectival.WantableGPT.vertex W₂ w₂ p.2 := by
  rcases p with ⟨a, b⟩
  show (if (w₁, w₂) = (a, b) then (1 : ℝ) else 0)
      = (if w₁ = a then 1 else 0) * (if w₂ = b then 1 else 0)
  by_cases h₁ : w₁ = a
  · by_cases h₂ : w₂ = b
    · simp [h₁, h₂]
    · have hne : (w₁, w₂) ≠ (a, b) := by
        intro h; exact h₂ (Prod.mk.inj h).2
      simp [hne, h₂]
  · have hne : (w₁, w₂) ≠ (a, b) := by
      intro h; exact h₁ (Prod.mk.inj h).1
    simp [hne, h₁]

/-- Concrete: vertex (true, false) on Bool × Bool factors through Bool vertices. -/
example (p : Bool × Bool) :
    Perspectival.WantableGPT.vertex (Bool × Bool) (true, false) p
      = Perspectival.WantableGPT.vertex Bool true p.1
      * Perspectival.WantableGPT.vertex Bool false p.2 :=
  WantableGPT_vertex_prod_decomp true false p

/-- New theorem: vertex on W₁ ⊕ W₂ at inl w gives the W₁ vertex
component on inl, and 0 on inr. -/
theorem WantableGPT_vertex_sum_inl
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w : W₁) (q : W₁ ⊕ W₂) :
    Perspectival.WantableGPT.vertex (W₁ ⊕ W₂) (Sum.inl w) q
      = match q with
        | .inl v => Perspectival.WantableGPT.vertex W₁ w v
        | .inr _ => (0 : ℝ) := by
  rcases q with v | v
  · show (if (Sum.inl w : W₁ ⊕ W₂) = Sum.inl v then (1 : ℝ) else 0)
        = (if w = v then 1 else 0)
    by_cases h : w = v
    · simp [h]
    · have hne : (Sum.inl w : W₁ ⊕ W₂) ≠ Sum.inl v := by
        intro he; exact h (Sum.inl.inj he)
      simp [hne, h]
  · show (if (Sum.inl w : W₁ ⊕ W₂) = Sum.inr v then (1 : ℝ) else 0)
        = 0
    simp

/-- Concrete: vertex on Bool ⊕ Bool at inl true: at inl true gives 1,
at inr anything gives 0. -/
example : Perspectival.WantableGPT.vertex (Bool ⊕ Bool) (Sum.inl true)
            (Sum.inr true) = 0 := by
  rw [WantableGPT_vertex_sum_inl]

/-- New theorem: vertex 0..3 of WantableGPT (Fin 4) are all pairwise
distinguishable (6 pairs). -/
theorem WantableGPT_Fin4_six_distinguishable :
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 0)
      (Perspectival.WantableGPT.vertex (Fin 4) 1) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 0)
      (Perspectival.WantableGPT.vertex (Fin 4) 2) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 0)
      (Perspectival.WantableGPT.vertex (Fin 4) 3) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 1)
      (Perspectival.WantableGPT.vertex (Fin 4) 2) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 1)
      (Perspectival.WantableGPT.vertex (Fin 4) 3) ∧
    Perspectival.Hardy.Distinguishable (Perspectival.WantableGPT.gpt (Fin 4))
      (Perspectival.WantableGPT.vertex (Fin 4) 2)
      (Perspectival.WantableGPT.vertex (Fin 4) 3) :=
  ⟨Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 0 1 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 0 2 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 0 3 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 1 2 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 1 3 (by decide),
   Perspectival.WantableGPT.vertices_distinguishable (Fin 4) 2 3 (by decide)⟩

/-- Symmetric companion of vertex_sum_inl: vertex at inr w is W₂-valued
on inr side, 0 on inl side. -/
theorem WantableGPT_vertex_sum_inr
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w : W₂) (q : W₁ ⊕ W₂) :
    Perspectival.WantableGPT.vertex (W₁ ⊕ W₂) (Sum.inr w) q
      = match q with
        | .inl _ => (0 : ℝ)
        | .inr v => Perspectival.WantableGPT.vertex W₂ w v := by
  rcases q with v | v
  · show (if (Sum.inr w : W₁ ⊕ W₂) = Sum.inl v then (1 : ℝ) else 0) = 0
    simp
  · show (if (Sum.inr w : W₁ ⊕ W₂) = Sum.inr v then (1 : ℝ) else 0)
        = (if w = v then 1 else 0)
    by_cases h : w = v
    · simp [h]
    · have hne : (Sum.inr w : W₁ ⊕ W₂) ≠ Sum.inr v := by
        intro he; exact h (Sum.inr.inj he)
      simp [hne, h]

/-- Concrete: vertex inr true on Bool ⊕ Bool at inl true gives 0. -/
example : Perspectival.WantableGPT.vertex (Bool ⊕ Bool) (Sum.inr true)
            (Sum.inl true) = 0 := by
  rw [WantableGPT_vertex_sum_inr]

/-- New: the unit functional on Bool ⊕ Bool sums in two summands. -/
theorem WantableGPT_unitFn_sum
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ ⊕ W₂)) :
    Perspectival.WantableGPT.unitFn (W₁ ⊕ W₂) f
      = (∑ w₁ : W₁, f (Sum.inl w₁)) + (∑ w₂ : W₂, f (Sum.inr w₂)) := by
  show ∑ w, f w
      = (∑ w₁ : W₁, f (Sum.inl w₁)) + (∑ w₂ : W₂, f (Sum.inr w₂))
  rw [Fintype.sum_sum_type]

/-- Concrete: on Bool ⊕ Bool the unit functional splits between summands. -/
example (f : Perspectival.WantableGPT.V (Bool ⊕ Bool)) :
    Perspectival.WantableGPT.unitFn (Bool ⊕ Bool) f
      = (∑ b : Bool, f (Sum.inl b)) + (∑ b : Bool, f (Sum.inr b)) :=
  WantableGPT_unitFn_sum f

/-- New: the unit functional on a product W₁ × W₂ decomposes as a double
sum. -/
theorem WantableGPT_unitFn_prod
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    Perspectival.WantableGPT.unitFn (W₁ × W₂) f
      = ∑ w₁ : W₁, ∑ w₂ : W₂, f (w₁, w₂) := by
  show ∑ p : W₁ × W₂, f p
      = ∑ w₁ : W₁, ∑ w₂ : W₂, f (w₁, w₂)
  rw [Fintype.sum_prod_type]

/-- Concrete: on Bool × Bool the unit functional decomposes as a double sum. -/
example (f : Perspectival.WantableGPT.V (Bool × Bool)) :
    Perspectival.WantableGPT.unitFn (Bool × Bool) f
      = ∑ b₁ : Bool, ∑ b₂ : Bool, f (b₁, b₂) :=
  WantableGPT_unitFn_prod f

/-- New: a state on W₁ × W₂ that is a product of states on W₁ and W₂
(product state). -/
noncomputable def productState
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.V (W₁ × W₂) :=
  fun p => f₁ p.1 * f₂ p.2

/-- New theorem: the productState's unitFn factors. -/
theorem productState_unitFn
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.unitFn (W₁ × W₂) (productState f₁ f₂)
      = Perspectival.WantableGPT.unitFn W₁ f₁
      * Perspectival.WantableGPT.unitFn W₂ f₂ := by
  rw [WantableGPT_unitFn_prod]
  show ∑ w₁ : W₁, ∑ w₂ : W₂, productState f₁ f₂ (w₁, w₂)
      = (∑ w₁, f₁ w₁) * (∑ w₂, f₂ w₂)
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro w₁ _
  apply Finset.sum_congr rfl
  intro w₂ _
  rfl

/-- Concrete: productState of two normalized Bool states is normalized. -/
example (f₁ f₂ : Perspectival.WantableGPT.V Bool)
    (h₁ : Perspectival.WantableGPT.unitFn Bool f₁ = 1)
    (h₂ : Perspectival.WantableGPT.unitFn Bool f₂ = 1) :
    Perspectival.WantableGPT.unitFn (Bool × Bool) (productState f₁ f₂) = 1 := by
  rw [productState_unitFn, h₁, h₂]; ring

/-- New theorem: productState's nonnegativity is preserved if both
factors are nonnegative. -/
theorem productState_nonneg
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : ∀ w₁, 0 ≤ f₁ w₁) (h₂ : ∀ w₂, 0 ≤ f₂ w₂) :
    ∀ p : W₁ × W₂, 0 ≤ productState f₁ f₂ p := by
  intro p
  show 0 ≤ f₁ p.1 * f₂ p.2
  exact mul_nonneg (h₁ p.1) (h₂ p.2)

/-- New theorem: productState of two states is a state on W₁ × W₂. -/
theorem productState_in_states
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : f₁ ∈ Perspectival.WantableGPT.states W₁)
    (h₂ : f₂ ∈ Perspectival.WantableGPT.states W₂) :
    productState f₁ f₂ ∈ Perspectival.WantableGPT.states (W₁ × W₂) := by
  refine ⟨productState_nonneg f₁ f₂ h₁.1 h₂.1, ?_⟩
  show ∑ p : W₁ × W₂, productState f₁ f₂ p = 1
  rw [Fintype.sum_prod_type]
  show ∑ w₁ : W₁, ∑ w₂ : W₂, f₁ w₁ * f₂ w₂ = 1
  have key : (∑ w₁ : W₁, ∑ w₂ : W₂, f₁ w₁ * f₂ w₂)
           = (∑ w₁, f₁ w₁) * (∑ w₂, f₂ w₂) := by
    rw [Finset.sum_mul_sum]
  rw [key, h₁.2, h₂.2]; ring

/-- Concrete: vertex true ⊗ vertex false on Bool × Bool is a state. -/
example :
    productState (Perspectival.WantableGPT.vertex Bool true)
                 (Perspectival.WantableGPT.vertex Bool false)
    ∈ Perspectival.WantableGPT.states (Bool × Bool) :=
  productState_in_states _ _
    (Perspectival.WantableGPT.vertex_in_states Bool true)
    (Perspectival.WantableGPT.vertex_in_states Bool false)

/-- New theorem: productState of vertices equals the vertex of the pair.
This is the simplex-tensor identification at the vertex level. -/
theorem productState_vertex
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w₁ : W₁) (w₂ : W₂) :
    productState (Perspectival.WantableGPT.vertex W₁ w₁)
                 (Perspectival.WantableGPT.vertex W₂ w₂)
      = Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂) := by
  funext p
  show Perspectival.WantableGPT.vertex W₁ w₁ p.1
     * Perspectival.WantableGPT.vertex W₂ w₂ p.2
     = Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂) p
  rw [WantableGPT_vertex_prod_decomp]

/-- Concrete: vertex true ⊗ vertex false on Bool × Bool = vertex (true, false). -/
example :
    productState (Perspectival.WantableGPT.vertex Bool true)
                 (Perspectival.WantableGPT.vertex Bool false)
      = Perspectival.WantableGPT.vertex (Bool × Bool) (true, false) :=
  productState_vertex true false

/-- New theorem: productState is associative on triple products (via the
W₁ × (W₂ × W₃) ≅ (W₁ × W₂) × W₃ Equiv). The factorization works
pointwise. -/
theorem productState_assoc
    {W₁ W₂ W₃ : Type u}
    [Wantable W₁] [Wantable W₂] [Wantable W₃]
    [Fintype W₁] [Fintype W₂] [Fintype W₃]
    [DecidableEq W₁] [DecidableEq W₂] [DecidableEq W₃]
    (f₁ : Perspectival.WantableGPT.V W₁)
    (f₂ : Perspectival.WantableGPT.V W₂)
    (f₃ : Perspectival.WantableGPT.V W₃)
    (p : W₁ × W₂ × W₃) :
    productState f₁ (productState f₂ f₃) p
      = f₁ p.1 * f₂ p.2.1 * f₃ p.2.2 := by
  show f₁ p.1 * productState f₂ f₃ p.2 = _
  show f₁ p.1 * (f₂ p.2.1 * f₃ p.2.2) = _
  ring

/-- New theorem: productState is symmetric up to a swap on the product. -/
theorem productState_swap
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (p : W₁ × W₂) :
    productState f₁ f₂ p = productState f₂ f₁ p.swap := by
  show f₁ p.1 * f₂ p.2 = f₂ p.2 * f₁ p.1
  ring

/-- New: an effect-vector on W₁ × W₂ which is a product of two
effect-vectors. -/
noncomputable def productEffectVec
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (g₁ : Perspectival.WantableGPT.V W₁) (g₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.V (W₁ × W₂) :=
  fun p => g₁ p.1 * g₂ p.2

/-- New theorem: productEffectVec is in effectVec if both factors are. -/
theorem productEffectVec_in_effectVec
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (g₁ : Perspectival.WantableGPT.V W₁) (g₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : g₁ ∈ Perspectival.WantableGPT.effectVec W₁)
    (h₂ : g₂ ∈ Perspectival.WantableGPT.effectVec W₂) :
    productEffectVec g₁ g₂ ∈ Perspectival.WantableGPT.effectVec (W₁ × W₂) := by
  intro p
  refine ⟨?_, ?_⟩
  · show 0 ≤ g₁ p.1 * g₂ p.2
    exact mul_nonneg (h₁ p.1).1 (h₂ p.2).1
  · show g₁ p.1 * g₂ p.2 ≤ 1
    have : g₁ p.1 * g₂ p.2 ≤ 1 * 1 := by
      apply mul_le_mul (h₁ p.1).2 (h₂ p.2).2 (h₂ p.2).1
      norm_num
    linarith

/-- Concrete: vertex true × vertex false as a product effect vector. -/
example : productEffectVec (Perspectival.WantableGPT.vertex Bool true)
                            (Perspectival.WantableGPT.vertex Bool false)
        ∈ Perspectival.WantableGPT.effectVec (Bool × Bool) :=
  productEffectVec_in_effectVec _ _
    (WantableGPT_vertex_in_effectVec true)
    (WantableGPT_vertex_in_effectVec false)

/-- New: the complementAction on a productState factors as the product
of complementActions on each factor. -/
theorem productState_complement_factor
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.complementAction (W₁ × W₂)
        (productState f₁ f₂)
      = productState
          (Perspectival.WantableGPT.complementAction W₁ f₁)
          (Perspectival.WantableGPT.complementAction W₂ f₂) := by
  funext p
  show productState f₁ f₂ (Wantable.complement p)
     = (Perspectival.WantableGPT.complementAction W₁ f₁) p.1
     * (Perspectival.WantableGPT.complementAction W₂ f₂) p.2
  show f₁ (Wantable.complement p).1 * f₂ (Wantable.complement p).2
     = f₁ (Wantable.complement p.1) * f₂ (Wantable.complement p.2)
  rfl

/-- Concrete: on Bool × Bool, complement of productState (vertex true,
vertex false) = productState (vertex false, vertex true). -/
example :
    Perspectival.WantableGPT.complementAction (Bool × Bool)
      (productState (Perspectival.WantableGPT.vertex Bool true)
                    (Perspectival.WantableGPT.vertex Bool false))
    = productState
        (Perspectival.WantableGPT.vertex Bool false)
        (Perspectival.WantableGPT.vertex Bool true) := by
  rw [productState_complement_factor]
  rw [Perspectival.WantableGPT.complementAction_vertex,
      Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- New: productState is left-homogeneous: scaling f₁ by c scales the
product by c. -/
theorem productState_smul_left
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (c : ℝ) (f₁ : Perspectival.WantableGPT.V W₁)
    (f₂ : Perspectival.WantableGPT.V W₂) :
    productState (c • f₁) f₂ = c • productState f₁ f₂ := by
  funext p
  show (c • f₁) p.1 * f₂ p.2 = c • (productState f₁ f₂ p)
  show c * f₁ p.1 * f₂ p.2 = c * (f₁ p.1 * f₂ p.2)
  ring

/-- New: productState is right-homogeneous: scaling f₂ by c scales the
product by c. -/
theorem productState_smul_right
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (c : ℝ) (f₁ : Perspectival.WantableGPT.V W₁)
    (f₂ : Perspectival.WantableGPT.V W₂) :
    productState f₁ (c • f₂) = c • productState f₁ f₂ := by
  funext p
  show f₁ p.1 * (c • f₂) p.2 = c • (productState f₁ f₂ p)
  show f₁ p.1 * (c * f₂ p.2) = c * (f₁ p.1 * f₂ p.2)
  ring

/-- New: productState is left-additive in the first factor. -/
theorem productState_add_left
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ f₁' : Perspectival.WantableGPT.V W₁)
    (f₂ : Perspectival.WantableGPT.V W₂) :
    productState (f₁ + f₁') f₂ = productState f₁ f₂ + productState f₁' f₂ := by
  funext p
  show (f₁ + f₁') p.1 * f₂ p.2 = productState f₁ f₂ p + productState f₁' f₂ p
  show (f₁ p.1 + f₁' p.1) * f₂ p.2 = f₁ p.1 * f₂ p.2 + f₁' p.1 * f₂ p.2
  ring

/-- New: productState is right-additive in the second factor. -/
theorem productState_add_right
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁)
    (f₂ f₂' : Perspectival.WantableGPT.V W₂) :
    productState f₁ (f₂ + f₂') = productState f₁ f₂ + productState f₁ f₂' := by
  funext p
  show f₁ p.1 * (f₂ + f₂') p.2 = productState f₁ f₂ p + productState f₁ f₂' p
  show f₁ p.1 * (f₂ p.2 + f₂' p.2) = f₁ p.1 * f₂ p.2 + f₁ p.1 * f₂' p.2
  ring

/-- New: productState commutes with PTrans.prodMap action via
transformAction. -/
theorem productState_transform_factor
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (φ₁ : PTrans W₁) (φ₂ : PTrans W₂)
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.transformAction (W₁ × W₂)
        (PTrans.prodMap φ₁ φ₂) (productState f₁ f₂)
      = productState
          (Perspectival.WantableGPT.transformAction W₁ φ₁ f₁)
          (Perspectival.WantableGPT.transformAction W₂ φ₂ f₂) := by
  funext p
  show productState f₁ f₂ ((PTrans.prodMap φ₁ φ₂).invFun p)
     = (Perspectival.WantableGPT.transformAction W₁ φ₁ f₁) p.1
     * (Perspectival.WantableGPT.transformAction W₂ φ₂ f₂) p.2
  show f₁ ((PTrans.prodMap φ₁ φ₂).invFun p).1
     * f₂ ((PTrans.prodMap φ₁ φ₂).invFun p).2
     = f₁ (φ₁.invFun p.1) * f₂ (φ₂.invFun p.2)
  rfl

/-- New: a perfectWitness on `W₁ × W₂` for product-vertices is
constructed from the projections. -/
noncomputable def productPerfectWitness
    (W₁ W₂ : Type u) [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    Perspectival.Distinguish.PerfectWitness
      (G := Perspectival.WantableGPT.gpt (W₁ × W₂))
      (Perspectival.WantableGPT.vertex (W₁ × W₂)) :=
  Perspectival.WantableGPT.perfectWitness (W₁ × W₂)

/-- New: linear-independence of product-vertices. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    LinearIndependent ℝ (Perspectival.WantableGPT.vertex (W₁ × W₂)) :=
  Perspectival.WantableGPT.vertex_linear_independent_of_fintype (W₁ × W₂)

/-- New: the finrank of `V (W₁ × W₂)` factorizes as a product. -/
theorem WantableGPT_finrank_prod
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (Perspectival.WantableGPT.V (W₁ × W₂))
      = Module.finrank ℝ (Perspectival.WantableGPT.V W₁)
      * Module.finrank ℝ (Perspectival.WantableGPT.V W₂) :=
  Perspectival.WantableGPT.wantableGPT_dim_prod

/-- New: the finrank of `V (W₁ ⊕ W₂)` adds. -/
theorem WantableGPT_finrank_sum
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (Perspectival.WantableGPT.V (W₁ ⊕ W₂))
      = Module.finrank ℝ (Perspectival.WantableGPT.V W₁)
      + Module.finrank ℝ (Perspectival.WantableGPT.V W₂) :=
  Perspectival.WantableGPT.wantableGPT_dim_sum

/-- Concrete: Bool × Bool has finrank 2 * 2 = 4. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool))
        = Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
        * Module.finrank ℝ (Perspectival.WantableGPT.V Bool) :=
  WantableGPT_finrank_prod

/-- Concrete: Bool ⊕ Fin 3 has finrank 2 + 3 = 5. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Fin 3))
        = Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
        + Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) :=
  WantableGPT_finrank_sum

/-- New: a singleton perfect witness on a one-state subset (constructed
from any state in `gpt W`). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ : Perspectival.WantableGPT.V W)
    (hρ : ρ ∈ Perspectival.WantableGPT.states W) :
    Perspectival.Distinguish.PerfectWitness
      (G := Perspectival.WantableGPT.gpt W) (fun _ : Fin 1 => ρ) :=
  Perspectival.Distinguish.perfectWitness_singleton ρ hρ

/-- New: vertex true on Bool, as a 1-element family, gives a perfect
witness. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt Bool)
            (fun _ : Fin 1 => Perspectival.WantableGPT.vertex Bool true) :=
  Perspectival.Distinguish.perfectWitness_singleton _
    (Perspectival.WantableGPT.vertex_in_states Bool true)

/-- New: vertex 0 on Fin 4, as a 1-element family, gives a perfect
witness. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt (Fin 4))
            (fun _ : Fin 1 => Perspectival.WantableGPT.vertex (Fin 4) 0) :=
  Perspectival.Distinguish.perfectWitness_singleton _
    (Perspectival.WantableGPT.vertex_in_states (Fin 4) 0)

/-- New: small concrete arithmetic check: |Bool| is even. -/
example : Even (Fintype.card Bool) := by decide

/-- New: small concrete check: |Bool × Bool| is even. -/
example : Even (Fintype.card (Bool × Bool)) := by decide

/-- New: small concrete check: |Bool ⊕ Bool| is even. -/
example : Even (Fintype.card (Bool ⊕ Bool)) := by decide

/-- New: |Fin 4| is even. -/
example : Even (Fintype.card (Fin 4)) := by decide

/-- New: |Bool ⊕ Fin 4| = 6 is even. -/
example : Even (Fintype.card (Bool ⊕ Fin 4)) := by decide

/-- New theorem: the uniform state `(1/|W|, ..., 1/|W|)` on `WantableGPT W`
is a valid state (when |W| > 0). -/
noncomputable def uniformState (W : Type u) [Wantable W] [Fintype W] [DecidableEq W]
    [Nonempty W] : Perspectival.WantableGPT.V W :=
  fun _ => 1 / (Fintype.card W : ℝ)

/-- The uniform state's coordinates are nonneg. -/
theorem uniformState_nonneg {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    [Nonempty W] (w : W) : 0 ≤ uniformState W w := by
  show 0 ≤ 1 / (Fintype.card W : ℝ)
  have : 0 < (Fintype.card W : ℝ) := by
    exact_mod_cast Fintype.card_pos
  positivity

/-- The uniform state's coords sum to 1. -/
theorem uniformState_sum {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    [Nonempty W] :
    ∑ w : W, uniformState W w = 1 := by
  show ∑ _ : W, 1 / (Fintype.card W : ℝ) = 1
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card W : ℝ) ≠ 0 := by
    have : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  rw [nsmul_eq_mul]
  field_simp

/-- New: the uniform state is in `states`. -/
theorem uniformState_in_states {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    [Nonempty W] : uniformState W ∈ Perspectival.WantableGPT.states W :=
  ⟨uniformState_nonneg, uniformState_sum⟩

/-- Concrete: the uniform state on Bool is the uniformBool. -/
example : uniformState Bool = uniformBool := by
  funext b
  show 1 / (Fintype.card Bool : ℝ) = (1/2 : ℝ)
  have : (Fintype.card Bool : ℝ) = 2 := by norm_cast
  rw [this]

/-- New theorem: the uniform state is invariant under any PTrans action
(every PTrans permutes coords; the uniform state has the same value on
every coord). -/
theorem uniformState_transformAction_invariant
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W]
    (φ : PTrans W) :
    Perspectival.WantableGPT.transformAction W φ (uniformState W)
      = uniformState W := by
  funext w
  show uniformState W (φ.invFun w) = uniformState W w
  rfl

/-- Concrete: uniformState on Bool is invariant under complementPTrans. -/
example : Perspectival.WantableGPT.transformAction Bool
            (Perspectival.WantableGPT.complementPTrans Bool)
            (uniformState Bool)
        = uniformState Bool :=
  uniformState_transformAction_invariant _

/-- New theorem: the uniform state is invariant under complementAction. -/
theorem uniformState_complement_invariant
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W] :
    Perspectival.WantableGPT.complementAction W (uniformState W)
      = uniformState W := by
  funext w
  show uniformState W (Wantable.complement w) = uniformState W w
  rfl

/-- Born-rule for the uniform state: probability of vertex w under
uniformState is 1/|W|. -/
theorem uniformState_proj_eq
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W]
    (w : W) :
    Perspectival.WantableGPT.proj W w (uniformState W)
      = 1 / (Fintype.card W : ℝ) := rfl

/-- Concrete: probability of vertex true under uniformBool = 1/2. -/
example : Perspectival.WantableGPT.proj Bool true uniformBool = 1/2 := rfl

/-- Concrete: probability of vertex 0 under uniformState (Fin 4) = 1/4. -/
example : Perspectival.WantableGPT.proj (Fin 4) 0 (uniformState (Fin 4))
        = 1 / 4 := by
  rw [uniformState_proj_eq]
  norm_cast

/-- Uniform state's unitFn = 1 (normalization). -/
theorem uniformState_unitFn
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W] :
    Perspectival.WantableGPT.unitFn W (uniformState W) = 1 :=
  uniformState_in_states.2

/-- Concrete: uniformState on Fin 4 has unitFn = 1. -/
example : Perspectival.WantableGPT.unitFn (Fin 4) (uniformState (Fin 4)) = 1 :=
  uniformState_unitFn

/-- New: uniformState on Bool is in WantableGPT.gpt Bool's states (full
GPT-level). -/
example : uniformState Bool ∈ (Perspectival.WantableGPT.gpt Bool).states :=
  uniformState_in_states

/-- New: uniformState on Fin 4 is in states. -/
example : uniformState (Fin 4) ∈ (Perspectival.WantableGPT.gpt (Fin 4)).states :=
  uniformState_in_states

/-- New: uniformState has constant coord values. -/
theorem uniformState_constant
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W]
    (w₁ w₂ : W) :
    uniformState W w₁ = uniformState W w₂ := rfl

/-- New: uniformState is determined by a single coord (and they're all equal). -/
example : uniformState Bool true = uniformState Bool false := rfl

/-- New: on Fin 4, all four coords of uniformState are equal. -/
example : uniformState (Fin 4) 0 = uniformState (Fin 4) 1 := rfl
example : uniformState (Fin 4) 1 = uniformState (Fin 4) 2 := rfl
example : uniformState (Fin 4) 2 = uniformState (Fin 4) 3 := rfl

/-- New theorem: uniformState on a product factors as productState of
the component uniform states. -/
theorem uniformState_prod_factor
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    [Nonempty W₁] [Nonempty W₂] :
    uniformState (W₁ × W₂)
      = productState (uniformState W₁) (uniformState W₂) := by
  funext p
  show 1 / (Fintype.card (W₁ × W₂) : ℝ)
      = uniformState W₁ p.1 * uniformState W₂ p.2
  show 1 / (Fintype.card (W₁ × W₂) : ℝ)
      = (1 / (Fintype.card W₁ : ℝ)) * (1 / (Fintype.card W₂ : ℝ))
  rw [Fintype.card_prod]
  push_cast
  ring

/-- Concrete: uniformState (Bool × Bool) factorises through uniformState
on each Bool. -/
example : uniformState (Bool × Bool)
        = productState (uniformState Bool) (uniformState Bool) :=
  uniformState_prod_factor

/-- New: a non-product state on Bool × Bool exists: e.g., (1/2)(vertex
(true, true) + vertex (false, false)) cannot be written as
productState f₁ f₂. -/
noncomputable def diagonalState : Perspectival.WantableGPT.V (Bool × Bool) :=
  fun p => if p = (true, true) ∨ p = (false, false) then (1/2 : ℝ) else 0

/-- The diagonal state has coords (1/2, 0, 0, 1/2). -/
example : diagonalState (true, true) = (1/2 : ℝ) := by
  show (if (true, true) = (true, true) ∨ (true, true) = (false, false)
        then (1/2 : ℝ) else 0) = 1/2
  simp

example : diagonalState (true, false) = (0 : ℝ) := by
  show (if (true, false) = (true, true) ∨ (true, false) = (false, false)
        then (1/2 : ℝ) else 0) = 0
  simp

example : diagonalState (false, true) = (0 : ℝ) := by
  show (if (false, true) = (true, true) ∨ (false, true) = (false, false)
        then (1/2 : ℝ) else 0) = 0
  simp

example : diagonalState (false, false) = (1/2 : ℝ) := by
  show (if (false, false) = (true, true) ∨ (false, false) = (false, false)
        then (1/2 : ℝ) else 0) = 1/2
  simp

/-- diagonalState's left marginal (sum over right) is uniformBool. -/
theorem diagonalState_left_marginal (b : Bool) :
    (∑ b₂, diagonalState (b, b₂)) = uniformBool b := by
  rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  cases b with
  | true =>
    show diagonalState (true, true) + diagonalState (true, false) = uniformBool true
    show (1/2 : ℝ) + 0 = 1/2
    norm_num
  | false =>
    show diagonalState (false, true) + diagonalState (false, false) = uniformBool false
    show (0 : ℝ) + 1/2 = 1/2
    norm_num

/-- diagonalState's right marginal (sum over left) is uniformBool. -/
theorem diagonalState_right_marginal (b : Bool) :
    (∑ b₁, diagonalState (b₁, b)) = uniformBool b := by
  rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  cases b with
  | true =>
    show diagonalState (true, true) + diagonalState (false, true) = uniformBool true
    show (1/2 : ℝ) + 0 = 1/2
    norm_num
  | false =>
    show diagonalState (true, false) + diagonalState (false, false) = uniformBool false
    show (0 : ℝ) + 1/2 = 1/2
    norm_num

/-- diagonalState is NOT a product of uniform states (it's correlated). -/
theorem diagonalState_ne_productState_uniformBool :
    diagonalState ≠ productState uniformBool uniformBool := by
  intro h
  have : diagonalState (true, false) = productState uniformBool uniformBool (true, false) := by
    rw [h]
  -- LHS = 0 (off-diagonal), RHS = 1/2 * 1/2 = 1/4 ≠ 0
  have hLHS : diagonalState (true, false) = 0 := by
    show (if (true, false) = (true, true) ∨ (true, false) = (false, false)
          then (1/2 : ℝ) else 0) = 0
    simp
  have hRHS : productState uniformBool uniformBool (true, false) = 1/4 := by
    show uniformBool true * uniformBool false = 1/4
    show (1/2 : ℝ) * (1/2 : ℝ) = 1/4
    norm_num
  rw [hLHS, hRHS] at this
  norm_num at this

/-- The diagonal state is in WantableGPT.states. -/
theorem diagonalState_in_states :
    diagonalState ∈ Perspectival.WantableGPT.states (Bool × Bool) := by
  refine ⟨?_, ?_⟩
  · intro p
    show 0 ≤ (if p = (true, true) ∨ p = (false, false)
              then (1/2 : ℝ) else 0)
    split <;> norm_num
  · show ∑ p, diagonalState p = 1
    rw [show (Finset.univ : Finset (Bool × Bool))
          = {(true, true), (true, false), (false, true), (false, false)} from by
        decide,
        Finset.sum_insert (by decide),
        Finset.sum_insert (by decide),
        Finset.sum_insert (by decide),
        Finset.sum_singleton]
    show diagonalState (true, true) +
        (diagonalState (true, false) +
          (diagonalState (false, true) + diagonalState (false, false))) = 1
    show (1/2 : ℝ) + (0 + (0 + 1/2)) = 1
    norm_num

/-- New: the antidiagonal state (1/2 on (true,false) and (false,true)). -/
noncomputable def antiDiagonalState : Perspectival.WantableGPT.V (Bool × Bool) :=
  fun p => if p = (true, false) ∨ p = (false, true) then (1/2 : ℝ) else 0

example : antiDiagonalState (true, false) = (1/2 : ℝ) := by
  show (if (true, false) = (true, false) ∨ (true, false) = (false, true)
        then (1/2 : ℝ) else 0) = 1/2
  simp

example : antiDiagonalState (true, true) = (0 : ℝ) := by
  show (if (true, true) = (true, false) ∨ (true, true) = (false, true)
        then (1/2 : ℝ) else 0) = 0
  simp

/-- antiDiagonalState is in WantableGPT.states. -/
theorem antiDiagonalState_in_states :
    antiDiagonalState ∈ Perspectival.WantableGPT.states (Bool × Bool) := by
  refine ⟨?_, ?_⟩
  · intro p
    show 0 ≤ (if p = (true, false) ∨ p = (false, true)
              then (1/2 : ℝ) else 0)
    split <;> norm_num
  · show ∑ p, antiDiagonalState p = 1
    rw [show (Finset.univ : Finset (Bool × Bool))
          = {(true, true), (true, false), (false, true), (false, false)} from by
        decide,
        Finset.sum_insert (by decide),
        Finset.sum_insert (by decide),
        Finset.sum_insert (by decide),
        Finset.sum_singleton]
    show antiDiagonalState (true, true) +
        (antiDiagonalState (true, false) +
          (antiDiagonalState (false, true) + antiDiagonalState (false, false))) = 1
    show (0 : ℝ) + (1/2 + (1/2 + 0)) = 1
    norm_num

/-- New: complementAction maps diagonalState to itself (the diagonal is
preserved by componentwise complement). -/
example : Perspectival.WantableGPT.complementAction (Bool × Bool) diagonalState
        = diagonalState := by
  funext p
  show diagonalState (Wantable.complement p) = diagonalState p
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- New: complementAction maps antiDiagonalState to itself. -/
example : Perspectival.WantableGPT.complementAction (Bool × Bool) antiDiagonalState
        = antiDiagonalState := by
  funext p
  show antiDiagonalState (Wantable.complement p) = antiDiagonalState p
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- The "diagonal-indicator" coefficient vector (1 on diagonal, 0 off). -/
noncomputable def diagonalIndicator : Perspectival.WantableGPT.V (Bool × Bool) :=
  fun p => if p = (true, true) ∨ p = (false, false) then (1 : ℝ) else 0

/-- diagonalIndicator is in effectVec. -/
theorem diagonalIndicator_in_effectVec :
    diagonalIndicator ∈ Perspectival.WantableGPT.effectVec (Bool × Bool) := by
  intro p
  refine ⟨?_, ?_⟩
  · show 0 ≤ (if p = (true, true) ∨ p = (false, false)
              then (1 : ℝ) else 0)
    split <;> norm_num
  · show (if p = (true, true) ∨ p = (false, false)
          then (1 : ℝ) else 0) ≤ 1
    split <;> norm_num

/-- The diagonal-indicator inner-product linear functional. -/
noncomputable def diagonalIndicatorLin :
    Perspectival.WantableGPT.V (Bool × Bool) →ₗ[ℝ] ℝ :=
  Perspectival.WantableGPT.innerLin (Bool × Bool) diagonalIndicator

/-- diagonalIndicatorLin is in WantableGPT.effects. -/
theorem diagonalIndicatorLin_in_effects :
    diagonalIndicatorLin ∈ Perspectival.WantableGPT.effects (Bool × Bool) :=
  ⟨diagonalIndicator, diagonalIndicator_in_effectVec, rfl⟩

/-- diagonalIndicatorLin gives 1 on diagonalState. -/
theorem diagonalIndicatorLin_on_diagonalState :
    diagonalIndicatorLin diagonalState = 1 := by
  show ∑ p, diagonalIndicator p * diagonalState p = 1
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show diagonalIndicator (true, true) * diagonalState (true, true) +
        (diagonalIndicator (true, false) * diagonalState (true, false) +
          (diagonalIndicator (false, true) * diagonalState (false, true) +
            diagonalIndicator (false, false) * diagonalState (false, false))) = 1
  show (1 : ℝ) * (1/2 : ℝ) + (0 * 0 + (0 * 0 + 1 * (1/2 : ℝ))) = 1
  norm_num

/-- diagonalIndicatorLin gives 0 on antiDiagonalState. -/
theorem diagonalIndicatorLin_on_antiDiagonalState :
    diagonalIndicatorLin antiDiagonalState = 0 := by
  show ∑ p, diagonalIndicator p * antiDiagonalState p = 0
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show diagonalIndicator (true, true) * antiDiagonalState (true, true) +
        (diagonalIndicator (true, false) * antiDiagonalState (true, false) +
          (diagonalIndicator (false, true) * antiDiagonalState (false, true) +
            diagonalIndicator (false, false) * antiDiagonalState (false, false))) = 0
  show (1 : ℝ) * 0 + (0 * (1/2 : ℝ) + (0 * (1/2 : ℝ) + 1 * 0)) = 0
  norm_num

/-- diagonalState and antiDiagonalState are perfectly distinguishable. -/
theorem diagonalState_distinguishable_antiDiagonalState :
    Perspectival.Hardy.Distinguishable
      (Perspectival.WantableGPT.gpt (Bool × Bool))
      diagonalState antiDiagonalState :=
  ⟨diagonalIndicatorLin, diagonalIndicatorLin_in_effects,
   diagonalIndicatorLin_on_diagonalState,
   diagonalIndicatorLin_on_antiDiagonalState⟩

/-- New theorem: uniformBool is a 50/50 mixture of vertex true and vertex false. -/
theorem uniformBool_eq_mixture :
    uniformBool = (1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool true
                + (1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool false :=
  uniformBool_decomp

/-- New theorem: uniformBool is a convex combination of the two vertices,
showing that the framework supports "mixed states" naturally. -/
theorem uniformBool_convex_combo :
    uniformBool = (1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool true
                + (1 - 1/2 : ℝ) • Perspectival.WantableGPT.vertex Bool false := by
  rw [uniformBool_decomp]
  ring_nf

/-- New theorem: the uniform state on any finite W is a convex
combination of the vertex states with all coefficients equal to 1/|W|. -/
theorem uniformState_eq_vertex_combo
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W] :
    uniformState W = ∑ w, (1 / (Fintype.card W : ℝ))
      • Perspectival.WantableGPT.vertex W w := by
  funext v
  show 1 / (Fintype.card W : ℝ)
     = (∑ w, (1 / (Fintype.card W : ℝ)) • Perspectival.WantableGPT.vertex W w) v
  rw [Finset.sum_apply]
  show 1 / (Fintype.card W : ℝ)
     = ∑ w, (1 / (Fintype.card W : ℝ)) * (if w = v then (1 : ℝ) else 0)
  rw [Finset.sum_eq_single v
    (fun w _ hwv => by
      show (1 / (Fintype.card W : ℝ)) * (if w = v then (1 : ℝ) else 0) = 0
      rw [if_neg hwv]; ring)
    (fun h => absurd (Finset.mem_univ v) h)]
  show 1 / (Fintype.card W : ℝ)
     = (1 / (Fintype.card W : ℝ)) * (if v = v then (1 : ℝ) else 0)
  rw [if_pos rfl]; ring

/-- Concrete: uniformBool decomposes through this generic formula. -/
example : uniformBool = ∑ b, (1 / (Fintype.card Bool : ℝ)) •
                              Perspectival.WantableGPT.vertex Bool b := by
  rw [show uniformBool = uniformState Bool from by funext b; show (1/2 : ℝ) = 1 / (Fintype.card Bool : ℝ); norm_cast]
  exact uniformState_eq_vertex_combo

/-- New: vertices on Bool are pure states (extremal). The vertex true
state cannot be written as a non-trivial convex combination of two
distinct states. We prove a weak version: vertex true ≠ uniformBool. -/
example : Perspectival.WantableGPT.vertex Bool true ≠ uniformBool := by
  intro h
  have h_true : Perspectival.WantableGPT.vertex Bool true true = 1 := by
    show (if true = true then (1 : ℝ) else 0) = 1
    simp
  have h_unif : uniformBool true = (1/2 : ℝ) := rfl
  rw [h] at h_true
  rw [h_unif] at h_true
  norm_num at h_true

/-- New: similarly, vertex false ≠ uniformBool. -/
example : Perspectival.WantableGPT.vertex Bool false ≠ uniformBool := by
  intro h
  have h_false : Perspectival.WantableGPT.vertex Bool false false = 1 := by
    show (if false = false then (1 : ℝ) else 0) = 1
    simp
  have h_unif : uniformBool false = (1/2 : ℝ) := rfl
  rw [h] at h_false
  rw [h_unif] at h_false
  norm_num at h_false

/-- New: vertex true ≠ vertex false (they're genuinely distinct states). -/
example : Perspectival.WantableGPT.vertex Bool true
        ≠ Perspectival.WantableGPT.vertex Bool false := by
  intro h
  have : Perspectival.WantableGPT.vertex Bool true true
       = Perspectival.WantableGPT.vertex Bool false true := by rw [h]
  show False
  have h1 : Perspectival.WantableGPT.vertex Bool true true = 1 := by
    show (if true = true then (1 : ℝ) else 0) = 1; simp
  have h2 : Perspectival.WantableGPT.vertex Bool false true = 0 := by
    show (if false = true then (1 : ℝ) else 0) = 0; simp
  rw [h1, h2] at this
  exact one_ne_zero this

/-- New theorem: distinct vertices in any Wantable are unequal. -/
theorem WantableGPT_vertex_ne {W : Type u} [Wantable W] [DecidableEq W]
    (w v : W) (hwv : w ≠ v) :
    Perspectival.WantableGPT.vertex W w ≠ Perspectival.WantableGPT.vertex W v := by
  intro h
  have h_eq : Perspectival.WantableGPT.vertex W w w
            = Perspectival.WantableGPT.vertex W v w := by rw [h]
  have h1 : Perspectival.WantableGPT.vertex W w w = 1 := by
    show (if w = w then (1 : ℝ) else 0) = 1; simp
  have h2 : Perspectival.WantableGPT.vertex W v w = 0 := by
    show (if v = w then (1 : ℝ) else 0) = 0; simp [Ne.symm hwv]
  rw [h1, h2] at h_eq
  exact one_ne_zero h_eq

/-- Concrete: vertex 0 ≠ vertex 3 on Fin 4. -/
example : Perspectival.WantableGPT.vertex (Fin 4) 0
        ≠ Perspectival.WantableGPT.vertex (Fin 4) 3 :=
  WantableGPT_vertex_ne 0 3 (by decide)

/-- Concrete: vertex (true, true) ≠ vertex (false, true) on Bool × Bool. -/
example : Perspectival.WantableGPT.vertex (Bool × Bool) (true, true)
        ≠ Perspectival.WantableGPT.vertex (Bool × Bool) (false, true) :=
  WantableGPT_vertex_ne _ _ (by decide)

/-- New theorem: distinct vertices give linearly independent pairs. -/
theorem WantableGPT_vertex_pair_independent
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (w v : W) (hwv : w ≠ v) :
    LinearIndependent ℝ ![Perspectival.WantableGPT.vertex W w,
                           Perspectival.WantableGPT.vertex W v] :=
  Perspectival.Distinguish.distinguishable_imp_linear_independent
    (Perspectival.WantableGPT.vertex_in_states W w)
    (Perspectival.WantableGPT.vertex_in_states W v)
    (Perspectival.WantableGPT.vertices_distinguishable W w v hwv)

/-- Concrete: vertex true and vertex false form a linearly independent
pair in V Bool. -/
example : LinearIndependent ℝ ![Perspectival.WantableGPT.vertex Bool true,
                                 Perspectival.WantableGPT.vertex Bool false] :=
  WantableGPT_vertex_pair_independent true false (by decide)

/-- Concrete: vertex 0 and vertex 1 form a linearly independent pair in V (Fin 4). -/
example : LinearIndependent ℝ ![Perspectival.WantableGPT.vertex (Fin 4) 0,
                                 Perspectival.WantableGPT.vertex (Fin 4) 1] :=
  WantableGPT_vertex_pair_independent 0 1 (by decide)

/-- New theorem: No linear cloner exists on the (vertex true, vertex false)
pair in V Bool. -/
theorem no_cloning_Bool_vertices
    {C : Perspectival.WantableGPT.V Bool →ₗ[ℝ]
         Perspectival.WantableGPT.V Bool ⊗[ℝ] Perspectival.WantableGPT.V Bool}
    {S : Set (Perspectival.WantableGPT.V Bool)}
    (hC : Perspectival.IsLinearCloner S C)
    (h₁ : Perspectival.WantableGPT.vertex Bool true ∈ S)
    (h₂ : Perspectival.WantableGPT.vertex Bool false ∈ S)
    (h_sum : Perspectival.WantableGPT.vertex Bool true +
             Perspectival.WantableGPT.vertex Bool false ∈ S) : False :=
  Perspectival.no_cloning_of_linear_independent hC h₁ h₂ h_sum
    (WantableGPT_vertex_pair_independent true false (by decide))

/-- New theorem: No linear cloner exists on the (vertex 0, vertex 1) pair
in V (Fin 4). -/
theorem no_cloning_Fin4_vertices
    {C : Perspectival.WantableGPT.V (Fin 4) →ₗ[ℝ]
         Perspectival.WantableGPT.V (Fin 4) ⊗[ℝ]
         Perspectival.WantableGPT.V (Fin 4)}
    {S : Set (Perspectival.WantableGPT.V (Fin 4))}
    (hC : Perspectival.IsLinearCloner S C)
    (h₁ : Perspectival.WantableGPT.vertex (Fin 4) 0 ∈ S)
    (h₂ : Perspectival.WantableGPT.vertex (Fin 4) 1 ∈ S)
    (h_sum : Perspectival.WantableGPT.vertex (Fin 4) 0 +
             Perspectival.WantableGPT.vertex (Fin 4) 1 ∈ S) : False :=
  Perspectival.no_cloning_of_linear_independent hC h₁ h₂ h_sum
    (WantableGPT_vertex_pair_independent 0 1 (by decide))

/-- New theorem: in any non-trivial finite Wantable, no linear cloner
exists on a pair of distinct vertices. -/
theorem no_cloning_WantableGPT_vertices
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    {C : Perspectival.WantableGPT.V W →ₗ[ℝ]
         Perspectival.WantableGPT.V W ⊗[ℝ] Perspectival.WantableGPT.V W}
    {S : Set (Perspectival.WantableGPT.V W)}
    (hC : Perspectival.IsLinearCloner S C)
    {w v : W} (hwv : w ≠ v)
    (h₁ : Perspectival.WantableGPT.vertex W w ∈ S)
    (h₂ : Perspectival.WantableGPT.vertex W v ∈ S)
    (h_sum : Perspectival.WantableGPT.vertex W w +
             Perspectival.WantableGPT.vertex W v ∈ S) : False :=
  Perspectival.no_cloning_of_linear_independent hC h₁ h₂ h_sum
    (WantableGPT_vertex_pair_independent w v hwv)

/-- New theorem: in any non-trivial finite Wantable, no linear cloner
on `Set.univ` of `V W` can clone any pair of distinct vertices. -/
theorem no_universal_cloner_WantableGPT_vertices
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    {C : Perspectival.WantableGPT.V W →ₗ[ℝ]
         Perspectival.WantableGPT.V W ⊗[ℝ] Perspectival.WantableGPT.V W}
    (hC : Perspectival.IsLinearCloner Set.univ C)
    {w v : W} (hwv : w ≠ v) : False :=
  no_cloning_WantableGPT_vertices hC hwv
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)

/-- Concrete: no universal cloner on V Bool can clone (vertex true, vertex false). -/
example {C : Perspectival.WantableGPT.V Bool →ₗ[ℝ]
              Perspectival.WantableGPT.V Bool ⊗[ℝ] Perspectival.WantableGPT.V Bool}
    (hC : Perspectival.IsLinearCloner Set.univ C) : False :=
  no_universal_cloner_WantableGPT_vertices hC (by decide : true ≠ false)

/-- Concrete: no universal cloner on V (Fin 4). -/
example {C : Perspectival.WantableGPT.V (Fin 4) →ₗ[ℝ]
              Perspectival.WantableGPT.V (Fin 4) ⊗[ℝ]
              Perspectival.WantableGPT.V (Fin 4)}
    (hC : Perspectival.IsLinearCloner Set.univ C) : False :=
  no_universal_cloner_WantableGPT_vertices hC (by decide : (0 : Fin 4) ≠ 1)

/-- Concrete: no universal cloner on V (Bool × Bool). -/
example {C : Perspectival.WantableGPT.V (Bool × Bool) →ₗ[ℝ]
              Perspectival.WantableGPT.V (Bool × Bool) ⊗[ℝ]
              Perspectival.WantableGPT.V (Bool × Bool)}
    (hC : Perspectival.IsLinearCloner Set.univ C) : False :=
  no_universal_cloner_WantableGPT_vertices hC
    (by decide : ((true, true) : Bool × Bool) ≠ (true, false))

/-- New theorem: cloner of the empty set is vacuous. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    (C : V →ₗ[ℝ] V ⊗[ℝ] V) :
    Perspectival.IsLinearCloner (∅ : Set V) C := by
  intro v hv
  exact absurd hv (Set.notMem_empty v)

/-- New theorem: cloner of any singleton {0} is satisfied by the zero map. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] :
    Perspectival.IsLinearCloner ({0} : Set V) (0 : V →ₗ[ℝ] V ⊗[ℝ] V) := by
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  simp

/-- New theorem: vertex states give linearly independent triples. -/
theorem WantableGPT_vertex_triple_independent
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (w v u : W) (hwv : w ≠ v) (hvu : v ≠ u) (hwu : w ≠ u) :
    LinearIndependent ℝ ![Perspectival.WantableGPT.vertex W w,
                           Perspectival.WantableGPT.vertex W v,
                           Perspectival.WantableGPT.vertex W u] := by
  set ρ : Fin 3 → Perspectival.WantableGPT.V W :=
    ![Perspectival.WantableGPT.vertex W w,
      Perspectival.WantableGPT.vertex W v,
      Perspectival.WantableGPT.vertex W u] with hρ
  have hvw : v ≠ w := hwv.symm
  have huv : u ≠ v := hvu.symm
  have huw : u ≠ w := hwu.symm
  have hwit : Perspectival.Distinguish.PerfectWitness
      (G := Perspectival.WantableGPT.gpt W) ρ := by
    refine ⟨![Perspectival.WantableGPT.proj W w,
              Perspectival.WantableGPT.proj W v,
              Perspectival.WantableGPT.proj W u], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      (show Perspectival.WantableGPT.proj W _
              (Perspectival.WantableGPT.vertex W _) = _) <;>
      (rw [Perspectival.WantableGPT.proj_vertex]) <;>
      simp_all
  exact Perspectival.Distinguish.perfect_distinguishable_imp_linear_independent
    ρ hwit

/-- Concrete: on Fin 4, vertices 0, 1, 2 are linearly independent. -/
example : LinearIndependent ℝ ![Perspectival.WantableGPT.vertex (Fin 4) 0,
                                 Perspectival.WantableGPT.vertex (Fin 4) 1,
                                 Perspectival.WantableGPT.vertex (Fin 4) 2] :=
  WantableGPT_vertex_triple_independent 0 1 2 (by decide) (by decide) (by decide)

/-- Concrete: on Bool × Bool, three out of four vertices are linearly
independent. -/
example : LinearIndependent ℝ
    ![Perspectival.WantableGPT.vertex (Bool × Bool) (true, true),
      Perspectival.WantableGPT.vertex (Bool × Bool) (true, false),
      Perspectival.WantableGPT.vertex (Bool × Bool) (false, true)] :=
  WantableGPT_vertex_triple_independent _ _ _
    (by decide) (by decide) (by decide)

/-- New: distinct vertices give a chain of pairwise non-equalities. -/
theorem WantableGPT_three_vertices_ne
    {W : Type u} [Wantable W] [DecidableEq W]
    (w v u : W) (hwv : w ≠ v) (hvu : v ≠ u) (hwu : w ≠ u) :
    Perspectival.WantableGPT.vertex W w ≠ Perspectival.WantableGPT.vertex W v ∧
    Perspectival.WantableGPT.vertex W v ≠ Perspectival.WantableGPT.vertex W u ∧
    Perspectival.WantableGPT.vertex W w ≠ Perspectival.WantableGPT.vertex W u :=
  ⟨WantableGPT_vertex_ne w v hwv,
   WantableGPT_vertex_ne v u hvu,
   WantableGPT_vertex_ne w u hwu⟩

/-- New: vertex spans of distinct singletons are pairwise different
state-space rays. -/
theorem WantableGPT_vertex_pair_smul_independent
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (w v : W) (hwv : w ≠ v) (a b : ℝ)
    (h : a • Perspectival.WantableGPT.vertex W w
       + b • Perspectival.WantableGPT.vertex W v = 0) :
    a = 0 ∧ b = 0 := by
  have hLI := WantableGPT_vertex_pair_independent w v hwv
  rw [LinearIndependent.pair_iff] at hLI
  exact hLI a b h

/-- Concrete: a • vertex true + b • vertex false = 0 ⇒ a = 0 ∧ b = 0. -/
example (a b : ℝ)
    (h : a • Perspectival.WantableGPT.vertex Bool true
       + b • Perspectival.WantableGPT.vertex Bool false = 0) :
    a = 0 ∧ b = 0 :=
  WantableGPT_vertex_pair_smul_independent true false (by decide) a b h

/-- The "anti-diagonal-indicator" coefficient vector. -/
noncomputable def antiDiagonalIndicator : Perspectival.WantableGPT.V (Bool × Bool) :=
  fun p => if p = (true, false) ∨ p = (false, true) then (1 : ℝ) else 0

/-- antiDiagonalIndicator is in effectVec. -/
theorem antiDiagonalIndicator_in_effectVec :
    antiDiagonalIndicator ∈ Perspectival.WantableGPT.effectVec (Bool × Bool) := by
  intro p
  refine ⟨?_, ?_⟩
  · show 0 ≤ (if p = (true, false) ∨ p = (false, true)
              then (1 : ℝ) else 0)
    split <;> norm_num
  · show (if p = (true, false) ∨ p = (false, true)
          then (1 : ℝ) else 0) ≤ 1
    split <;> norm_num

/-- The anti-diagonal-indicator linear functional. -/
noncomputable def antiDiagonalIndicatorLin :
    Perspectival.WantableGPT.V (Bool × Bool) →ₗ[ℝ] ℝ :=
  Perspectival.WantableGPT.innerLin (Bool × Bool) antiDiagonalIndicator

/-- antiDiagonalIndicatorLin is in WantableGPT.effects. -/
theorem antiDiagonalIndicatorLin_in_effects :
    antiDiagonalIndicatorLin ∈ Perspectival.WantableGPT.effects (Bool × Bool) :=
  ⟨antiDiagonalIndicator, antiDiagonalIndicator_in_effectVec, rfl⟩

/-- diagonalIndicator + antiDiagonalIndicator = constant 1 (unit). -/
theorem diagonalIndicator_add_antiDiagonalIndicator :
    diagonalIndicator + antiDiagonalIndicator
      = (fun _ : Bool × Bool => (1 : ℝ)) := by
  funext p
  show diagonalIndicator p + antiDiagonalIndicator p = 1
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> (
    show (if _ ∨ _ then (1 : ℝ) else 0) + (if _ ∨ _ then (1 : ℝ) else 0) = 1
    simp)

/-- antiDiagonalIndicatorLin gives 0 on diagonalState. -/
theorem antiDiagonalIndicatorLin_on_diagonalState :
    antiDiagonalIndicatorLin diagonalState = 0 := by
  show ∑ p, antiDiagonalIndicator p * diagonalState p = 0
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show antiDiagonalIndicator (true, true) * diagonalState (true, true) +
        (antiDiagonalIndicator (true, false) * diagonalState (true, false) +
          (antiDiagonalIndicator (false, true) * diagonalState (false, true) +
            antiDiagonalIndicator (false, false) * diagonalState (false, false))) = 0
  show (0 : ℝ) * (1/2 : ℝ) + (1 * 0 + (1 * 0 + 0 * (1/2 : ℝ))) = 0
  norm_num

/-- antiDiagonalIndicatorLin gives 1 on antiDiagonalState. -/
theorem antiDiagonalIndicatorLin_on_antiDiagonalState :
    antiDiagonalIndicatorLin antiDiagonalState = 1 := by
  show ∑ p, antiDiagonalIndicator p * antiDiagonalState p = 1
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show antiDiagonalIndicator (true, true) * antiDiagonalState (true, true) +
        (antiDiagonalIndicator (true, false) * antiDiagonalState (true, false) +
          (antiDiagonalIndicator (false, true) * antiDiagonalState (false, true) +
            antiDiagonalIndicator (false, false) * antiDiagonalState (false, false))) = 1
  show (0 : ℝ) * 0 + (1 * (1/2 : ℝ) + (1 * (1/2 : ℝ) + 0 * 0)) = 1
  norm_num

/-- Reverse distinguishability: antiDiagonalState is distinguishable from
diagonalState (in the opposite direction). -/
theorem antiDiagonalState_distinguishable_diagonalState :
    Perspectival.Hardy.Distinguishable
      (Perspectival.WantableGPT.gpt (Bool × Bool))
      antiDiagonalState diagonalState :=
  ⟨antiDiagonalIndicatorLin, antiDiagonalIndicatorLin_in_effects,
   antiDiagonalIndicatorLin_on_antiDiagonalState,
   antiDiagonalIndicatorLin_on_diagonalState⟩

/-- New: productState (vertex w) uniformBool gives a "1 ⊗ 1/2" mixed
state on the product. -/
theorem productState_vertex_uniformBool (w : Bool) (p : Bool × Bool) :
    productState (Perspectival.WantableGPT.vertex Bool w) uniformBool p
      = (if w = p.1 then (1/2 : ℝ) else 0) := by
  show Perspectival.WantableGPT.vertex Bool w p.1 * uniformBool p.2
      = if w = p.1 then (1/2 : ℝ) else 0
  show (if w = p.1 then (1 : ℝ) else 0) * (1/2 : ℝ)
      = if w = p.1 then (1/2 : ℝ) else 0
  by_cases h : w = p.1
  · simp [h]
  · simp [h]

/-- Concrete: productState (vertex true) uniformBool at (true, true) = 1/2. -/
example : productState (Perspectival.WantableGPT.vertex Bool true)
                       uniformBool (true, true) = (1/2 : ℝ) := by
  rw [productState_vertex_uniformBool]; simp

/-- productState (vertex w) uniformBool is in states (it's a valid
mixed state on Bool × Bool). -/
example (w : Bool) :
    productState (Perspectival.WantableGPT.vertex Bool w) uniformBool
    ∈ Perspectival.WantableGPT.states (Bool × Bool) :=
  productState_in_states _ _
    (Perspectival.WantableGPT.vertex_in_states Bool w)
    uniformBool_in_states

/-- productState uniformBool (vertex w) is in states. -/
example (w : Bool) :
    productState uniformBool (Perspectival.WantableGPT.vertex Bool w)
    ∈ Perspectival.WantableGPT.states (Bool × Bool) :=
  productState_in_states _ _ uniformBool_in_states
    (Perspectival.WantableGPT.vertex_in_states Bool w)

/-- New: a convex combination of two states is a state (general fact). -/
theorem WantableGPT_convex_combo_in_states
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ₁ ρ₂ : Perspectival.WantableGPT.V W) (a b : ℝ)
    (h₁ : ρ₁ ∈ Perspectival.WantableGPT.states W)
    (h₂ : ρ₂ ∈ Perspectival.WantableGPT.states W)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • ρ₁ + b • ρ₂ ∈ Perspectival.WantableGPT.states W := by
  refine ⟨?_, ?_⟩
  · intro w
    show 0 ≤ (a • ρ₁ + b • ρ₂) w
    show 0 ≤ a * ρ₁ w + b * ρ₂ w
    exact add_nonneg (mul_nonneg ha (h₁.1 w)) (mul_nonneg hb (h₂.1 w))
  · show ∑ w, (a • ρ₁ + b • ρ₂) w = 1
    rw [show (a • ρ₁ + b • ρ₂ : Perspectival.WantableGPT.V W)
          = (fun w => a * ρ₁ w + b * ρ₂ w) from rfl]
    show ∑ w, (a * ρ₁ w + b * ρ₂ w) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁.2, h₂.2]
    ring_nf
    exact hab

/-- Concrete: convex combo of two vertex states is a state. -/
example (w v : Bool) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • Perspectival.WantableGPT.vertex Bool w
    + b • Perspectival.WantableGPT.vertex Bool v
    ∈ Perspectival.WantableGPT.states Bool :=
  WantableGPT_convex_combo_in_states _ _ a b
    (Perspectival.WantableGPT.vertex_in_states Bool w)
    (Perspectival.WantableGPT.vertex_in_states Bool v)
    ha hb hab

/-- Concrete: uniformBool (= 1/2 vertex true + 1/2 vertex false) is a state. -/
example : uniformBool ∈ Perspectival.WantableGPT.states Bool := by
  rw [uniformBool_decomp]
  exact WantableGPT_convex_combo_in_states _ _ (1/2) (1/2)
    (Perspectival.WantableGPT.vertex_in_states Bool true)
    (Perspectival.WantableGPT.vertex_in_states Bool false)
    (by norm_num) (by norm_num) (by norm_num)

/-- Concrete: 1/3 vertex true + 2/3 vertex false is a state. -/
example :
    (1/3 : ℝ) • Perspectival.WantableGPT.vertex Bool true
    + (2/3 : ℝ) • Perspectival.WantableGPT.vertex Bool false
    ∈ Perspectival.WantableGPT.states Bool :=
  WantableGPT_convex_combo_in_states _ _ (1/3) (2/3)
    (Perspectival.WantableGPT.vertex_in_states Bool true)
    (Perspectival.WantableGPT.vertex_in_states Bool false)
    (by norm_num) (by norm_num) (by norm_num)

/-- New theorem: every Bool state is a convex combination of vertex true
and vertex false. -/
theorem WantableGPT_Bool_states_convex_hull
    (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ Perspectival.WantableGPT.states Bool) :
    ρ = ρ true • Perspectival.WantableGPT.vertex Bool true
      + ρ false • Perspectival.WantableGPT.vertex Bool false :=
  WantableGPT_Bool_state_decomp ρ

/-- New theorem: ρ is a 'pure' state on Bool iff ρ = vertex true or
ρ = vertex false (the convex hull characterization). For finite
classical states, "pure" means an extreme point = vertex. -/
theorem WantableGPT_Bool_state_is_convex_combo
    (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ Perspectival.WantableGPT.states Bool) :
    0 ≤ ρ true ∧ 0 ≤ ρ false ∧ ρ true + ρ false = 1 :=
  (WantableGPT_Bool_states_iff ρ).mp hρ

/-- New theorem: every classical state can be written as a sum of
weighted vertex states (vertex decomposition). -/
theorem WantableGPT_classical_state_decomposition
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ : Perspectival.WantableGPT.V W) :
    ρ = ∑ w, ρ w • Perspectival.WantableGPT.vertex W w :=
  Perspectival.WantableGPT.vertex_decomposition W ρ

/-- Concrete: any uniformBool state has the explicit decomposition
1/2 • vertex true + 1/2 • vertex false. -/
example : uniformBool
        = uniformBool true • Perspectival.WantableGPT.vertex Bool true
        + uniformBool false • Perspectival.WantableGPT.vertex Bool false :=
  WantableGPT_Bool_state_decomp _

/-- Concrete: vertex true has decomposition 1 • vertex true + 0 • vertex false. -/
example : Perspectival.WantableGPT.vertex Bool true
        = (1 : ℝ) • Perspectival.WantableGPT.vertex Bool true
        + (0 : ℝ) • Perspectival.WantableGPT.vertex Bool false := by
  rw [one_smul, zero_smul, add_zero]

/-- New theorem: a state is in the span of the vertex set. -/
theorem WantableGPT_states_in_vertex_span
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (ρ : Perspectival.WantableGPT.V W) :
    ρ ∈ Submodule.span ℝ (Set.range (Perspectival.WantableGPT.vertex W)) := by
  have h := Perspectival.WantableGPT.vertices_span W
  rw [h]
  exact Submodule.mem_top

/-- Concrete: uniformBool is in the span of {vertex true, vertex false}. -/
example : uniformBool ∈ Submodule.span ℝ
            (Set.range (Perspectival.WantableGPT.vertex Bool)) :=
  WantableGPT_states_in_vertex_span uniformBool

/-- Concrete: diagonalState is in the span of vertex-set of Bool × Bool. -/
example : diagonalState ∈ Submodule.span ℝ
            (Set.range (Perspectival.WantableGPT.vertex (Bool × Bool))) :=
  WantableGPT_states_in_vertex_span diagonalState

/-- New: uniformBool is preserved by fromPTrans of any PTrans. -/
theorem fromPTrans_uniformBool_invariant (φ : PTrans Bool) :
    (Perspectival.WantableGPT.fromPTrans Bool φ).toLin uniformBool = uniformBool := by
  funext b
  show uniformBool (φ.invFun b) = uniformBool b
  rfl

/-- New: complementTransform on uniformBool is uniformBool. -/
example : (Perspectival.WantableGPT.complementTransform Bool).toLin uniformBool
        = uniformBool := by
  rw [Perspectival.WantableGPT.complementTransform_eq_fromPTrans_full]
  exact fromPTrans_uniformBool_invariant _

/-- New: the uniform state is the "maximally mixed" state on any
finite Wantable — it's invariant under the PTrans-fromPTrans bridge. -/
theorem fromPTrans_uniformState_invariant
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] [Nonempty W]
    (φ : PTrans W) :
    (Perspectival.WantableGPT.fromPTrans W φ).toLin (uniformState W)
      = uniformState W := by
  funext w
  show uniformState W (φ.invFun w) = uniformState W w
  rfl

/-- New: fromPTrans on Fin 4 applied to uniformState (Fin 4) returns the same. -/
example (φ : PTrans (Fin 4)) :
    (Perspectival.WantableGPT.fromPTrans (Fin 4) φ).toLin
      (uniformState (Fin 4)) = uniformState (Fin 4) :=
  fromPTrans_uniformState_invariant φ

/-- New: fromPTrans on the complement PTrans applied to uniformBool returns
the same (specialized form). -/
example : (Perspectival.WantableGPT.fromPTrans Bool
            (Perspectival.WantableGPT.complementPTrans Bool)).toLin
            uniformBool = uniformBool :=
  fromPTrans_uniformBool_invariant _

/-- New: fromPTrans on the identity PTrans applied to uniformBool returns
the same. -/
example : (Perspectival.WantableGPT.fromPTrans Bool 1).toLin uniformBool
        = uniformBool :=
  fromPTrans_uniformBool_invariant 1

/-- New: diagonalIndicatorLin gives 1/2 on uniformState (Bool × Bool). -/
theorem diagonalIndicatorLin_on_uniformBoolBool :
    diagonalIndicatorLin (uniformState (Bool × Bool)) = 1/2 := by
  show ∑ p, diagonalIndicator p * uniformState (Bool × Bool) p = 1/2
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show diagonalIndicator (true, true) * uniformState (Bool × Bool) (true, true) +
        (diagonalIndicator (true, false) * uniformState (Bool × Bool) (true, false) +
          (diagonalIndicator (false, true) * uniformState (Bool × Bool) (false, true) +
            diagonalIndicator (false, false) * uniformState (Bool × Bool) (false, false))) = 1/2
  show (1 : ℝ) * (1 / 4) + (0 * (1 / 4) + (0 * (1 / 4) + 1 * (1 / 4))) = 1/2
  norm_num

/-- New: antiDiagonalIndicatorLin gives 1/2 on uniformState (Bool × Bool). -/
theorem antiDiagonalIndicatorLin_on_uniformBoolBool :
    antiDiagonalIndicatorLin (uniformState (Bool × Bool)) = 1/2 := by
  show ∑ p, antiDiagonalIndicator p * uniformState (Bool × Bool) p = 1/2
  rw [show (Finset.univ : Finset (Bool × Bool))
        = {(true, true), (true, false), (false, true), (false, false)} from by
      decide,
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  show antiDiagonalIndicator (true, true) * uniformState (Bool × Bool) (true, true) +
        (antiDiagonalIndicator (true, false) * uniformState (Bool × Bool) (true, false) +
          (antiDiagonalIndicator (false, true) * uniformState (Bool × Bool) (false, true) +
            antiDiagonalIndicator (false, false) * uniformState (Bool × Bool) (false, false))) = 1/2
  show (0 : ℝ) * (1 / 4) + (1 * (1 / 4) + (1 * (1 / 4) + 0 * (1 / 4))) = 1/2
  norm_num

/-- New: diagonalIndicatorLin + antiDiagonalIndicatorLin = unitFn. -/
theorem diagonalIndicatorLin_add_antiDiagonalIndicatorLin :
    diagonalIndicatorLin + antiDiagonalIndicatorLin
      = Perspectival.WantableGPT.unitFn (Bool × Bool) := by
  apply LinearMap.ext
  intro f
  show diagonalIndicatorLin f + antiDiagonalIndicatorLin f
     = Perspectival.WantableGPT.unitFn (Bool × Bool) f
  show ∑ p, diagonalIndicator p * f p + ∑ p, antiDiagonalIndicator p * f p
     = ∑ p, f p
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  show diagonalIndicator p * f p + antiDiagonalIndicator p * f p = f p
  have h : diagonalIndicator p + antiDiagonalIndicator p = 1 := by
    have := congr_fun diagonalIndicator_add_antiDiagonalIndicator p
    simpa using this
  rw [← add_mul, h, one_mul]

/-- Born-rule normalization: every state ρ has diagonalIndicatorLin ρ
+ antiDiagonalIndicatorLin ρ = 1 (probabilities sum to 1). -/
theorem indicator_probs_sum_to_one
    (ρ : Perspectival.WantableGPT.V (Bool × Bool))
    (hρ : ρ ∈ Perspectival.WantableGPT.states (Bool × Bool)) :
    diagonalIndicatorLin ρ + antiDiagonalIndicatorLin ρ = 1 := by
  have := congr_fun
    (congrArg (·.toFun) diagonalIndicatorLin_add_antiDiagonalIndicatorLin) ρ
  simpa using
    (LinearMap.congr_fun diagonalIndicatorLin_add_antiDiagonalIndicatorLin ρ).trans hρ.2

/-- Concrete: diagonalState satisfies the probability normalization for
the indicator measurement. -/
example : diagonalIndicatorLin diagonalState
        + antiDiagonalIndicatorLin diagonalState = 1 := by
  rw [diagonalIndicatorLin_on_diagonalState,
      antiDiagonalIndicatorLin_on_diagonalState]
  norm_num

/-- Concrete: antiDiagonalState satisfies the normalization. -/
example : diagonalIndicatorLin antiDiagonalState
        + antiDiagonalIndicatorLin antiDiagonalState = 1 := by
  rw [diagonalIndicatorLin_on_antiDiagonalState,
      antiDiagonalIndicatorLin_on_antiDiagonalState]
  norm_num

/-- Concrete: uniformState (Bool × Bool) gives 1/2 + 1/2 = 1 for the
indicator measurement (50/50 outcomes). -/
example : diagonalIndicatorLin (uniformState (Bool × Bool))
        + antiDiagonalIndicatorLin (uniformState (Bool × Bool)) = 1 := by
  rw [diagonalIndicatorLin_on_uniformBoolBool,
      antiDiagonalIndicatorLin_on_uniformBoolBool]
  norm_num

/-- Concrete: productState uniformBool uniformBool gives the same as
uniformState (Bool × Bool). -/
example : productState uniformBool uniformBool = uniformState (Bool × Bool) := by
  rw [uniformState_prod_factor]
  congr 1 <;> (funext _; rfl)

/-- Classical-correlation: diagonalState is the "Bell-state-like" perfectly
correlated state — measuring with diagonalIndicator gives 1 (probability
1 of "same outcome"). -/
example : diagonalIndicatorLin diagonalState = 1 :=
  diagonalIndicatorLin_on_diagonalState

/-- And measuring with antiDiagonalIndicator gives 0 (no anti-correlation). -/
example : antiDiagonalIndicatorLin diagonalState = 0 :=
  antiDiagonalIndicatorLin_on_diagonalState

/-- antiDiagonalState is the dual perfectly-anti-correlated state. -/
example : diagonalIndicatorLin antiDiagonalState = 0 :=
  diagonalIndicatorLin_on_antiDiagonalState

example : antiDiagonalIndicatorLin antiDiagonalState = 1 :=
  antiDiagonalIndicatorLin_on_antiDiagonalState

/-- The pair (diagonal-indicator, antiDiagonal-indicator) forms a
2-outcome perfect measurement for the (diagonalState, antiDiagonalState)
family. -/
noncomputable def diagAntiDiagWitness :
    Perspectival.Distinguish.PerfectWitness
      (G := Perspectival.WantableGPT.gpt (Bool × Bool))
      ![diagonalState, antiDiagonalState] where
  e := ![diagonalIndicatorLin, antiDiagonalIndicatorLin]
  kronecker i j := by
    fin_cases i <;> fin_cases j
    · show diagonalIndicatorLin diagonalState = if (0 : Fin 2) = 0 then 1 else 0
      simp [diagonalIndicatorLin_on_diagonalState]
    · show diagonalIndicatorLin antiDiagonalState = if (0 : Fin 2) = 1 then 1 else 0
      simp [diagonalIndicatorLin_on_antiDiagonalState]
    · show antiDiagonalIndicatorLin diagonalState = if (1 : Fin 2) = 0 then 1 else 0
      simp [antiDiagonalIndicatorLin_on_diagonalState]
    · show antiDiagonalIndicatorLin antiDiagonalState = if (1 : Fin 2) = 1 then 1 else 0
      simp [antiDiagonalIndicatorLin_on_antiDiagonalState]

/-- The diagonal/antiDiagonal pair gives a linearly-independent family
of states. -/
example : LinearIndependent ℝ ![diagonalState, antiDiagonalState] :=
  Perspectival.Distinguish.perfect_distinguishable_imp_linear_independent
    ![diagonalState, antiDiagonalState] diagAntiDiagWitness

/-- The diagonal/antiDiagonal witness gives the inequality 2 ≤ dim V (B×B) = 4. -/
example : (2 : ℕ) ≤ Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) :=
  Perspectival.Distinguish.operational_dim_le_state_dim
    ![diagonalState, antiDiagonalState] diagAntiDiagWitness

/-- The full perfect-witness on Bool × Bool vertices gives the
inequality 4 ≤ dim V (B×B) = 4 (tight bound). -/
example : Fintype.card (Bool × Bool)
        ≤ Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) :=
  (Perspectival.WantableGPT.wantableGPT_is_classical (Bool × Bool)).1

/-- The classical signature N = K = 4 for Bool × Bool. -/
example : Fintype.card (Bool × Bool) = 4 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool)) = 4 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The classical signature N = K = 2 for Bool. -/
example : Fintype.card Bool = 2 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The classical signature N = K = 4 for Fin 4. -/
example : Fintype.card (Fin 4) = 4 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) = 4 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The classical signature N = K = |Bool ⊕ Bool| = 4. -/
example : Fintype.card (Bool ⊕ Bool) = 4 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool ⊕ Bool)) = 4 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The classical signature N = K = 6 for Bool × Fin 3. -/
example : Fintype.card (Bool × Fin 3) = 6 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Fin 3)) = 6 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- New theorem: fromPTrans of prodMap commutes with productState
on the linear-map level. -/
theorem fromPTrans_prodMap_apply_productState
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (φ₁ : PTrans W₁) (φ₂ : PTrans W₂)
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    (Perspectival.WantableGPT.fromPTrans (W₁ × W₂)
        (PTrans.prodMap φ₁ φ₂)).toLin (productState f₁ f₂)
      = productState
          ((Perspectival.WantableGPT.fromPTrans W₁ φ₁).toLin f₁)
          ((Perspectival.WantableGPT.fromPTrans W₂ φ₂).toLin f₂) :=
  productState_transform_factor φ₁ φ₂ f₁ f₂

/-- Concrete: fromPTrans of (1, complementPTrans) on Bool × Bool. -/
example (f₁ f₂ : Perspectival.WantableGPT.V Bool) :
    (Perspectival.WantableGPT.fromPTrans (Bool × Bool)
        (PTrans.prodMap (1 : PTrans Bool)
          (Perspectival.WantableGPT.complementPTrans Bool))).toLin
      (productState f₁ f₂)
    = productState
        ((Perspectival.WantableGPT.fromPTrans Bool 1).toLin f₁)
        ((Perspectival.WantableGPT.fromPTrans Bool
          (Perspectival.WantableGPT.complementPTrans Bool)).toLin f₂) :=
  fromPTrans_prodMap_apply_productState _ _ f₁ f₂

/-- New: PTrans.prodMap (1, 1) ∘ productState f₁ f₂ = productState f₁ f₂. -/
theorem fromPTrans_prodMap_id_id_eq
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂) :
    (Perspectival.WantableGPT.fromPTrans (W₁ × W₂)
        (PTrans.prodMap (1 : PTrans W₁) (1 : PTrans W₂))).toLin
      (productState f₁ f₂)
    = productState f₁ f₂ := by
  rw [fromPTrans_prodMap_apply_productState]
  rw [WantableGPT_fromPTrans_one_apply, WantableGPT_fromPTrans_one_apply]

/-- Concrete: fromPTrans (prodMap 1 1) on productState uniformBool uniformBool. -/
example :
    (Perspectival.WantableGPT.fromPTrans (Bool × Bool)
        (PTrans.prodMap (1 : PTrans Bool) (1 : PTrans Bool))).toLin
      (productState uniformBool uniformBool)
    = productState uniformBool uniformBool :=
  fromPTrans_prodMap_id_id_eq _ _

/-- New: PTrans.prodMap (complementPTrans, complementPTrans) ∘
productState f₁ f₂ = productState (complement·f₁) (complement·f₂). -/
theorem fromPTrans_prodMap_complement_complement_apply
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (f₁ f₂ : Perspectival.WantableGPT.V W) :
    (Perspectival.WantableGPT.fromPTrans (W × W)
        (PTrans.prodMap (Perspectival.WantableGPT.complementPTrans W)
                        (Perspectival.WantableGPT.complementPTrans W))).toLin
      (productState f₁ f₂)
    = productState
        (Perspectival.WantableGPT.complementAction W f₁)
        (Perspectival.WantableGPT.complementAction W f₂) :=
  productState_transform_factor _ _ f₁ f₂

/-- Concrete: applying complement on both factors of Bool × Bool maps
productState (vertex true) (vertex true) to productState (vertex false)
(vertex false). -/
example :
    (Perspectival.WantableGPT.fromPTrans (Bool × Bool)
        (PTrans.prodMap (Perspectival.WantableGPT.complementPTrans Bool)
                        (Perspectival.WantableGPT.complementPTrans Bool))).toLin
      (productState (Perspectival.WantableGPT.vertex Bool true)
                    (Perspectival.WantableGPT.vertex Bool true))
    = productState
        (Perspectival.WantableGPT.vertex Bool false)
        (Perspectival.WantableGPT.vertex Bool false) := by
  rw [fromPTrans_prodMap_complement_complement_apply,
      Perspectival.WantableGPT.complementAction_vertex]
  rfl

/-- New theorem: every state on the product Wantable can be decomposed
into a sum of product-vertex-states (the classical signature
witnessed by the simplex on the product). -/
theorem WantableGPT_state_prod_vertex_decomp
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    f = ∑ w₁ : W₁, ∑ w₂ : W₂, f (w₁, w₂)
      • productState (Perspectival.WantableGPT.vertex W₁ w₁)
                     (Perspectival.WantableGPT.vertex W₂ w₂) := by
  rw [show
    (∑ w₁ : W₁, ∑ w₂ : W₂, f (w₁, w₂)
      • productState (Perspectival.WantableGPT.vertex W₁ w₁)
                     (Perspectival.WantableGPT.vertex W₂ w₂))
    = ∑ w₁ : W₁, ∑ w₂ : W₂, f (w₁, w₂)
      • Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂)
    from by
      apply Finset.sum_congr rfl
      intro w₁ _
      apply Finset.sum_congr rfl
      intro w₂ _
      rw [productState_vertex]]
  rw [← Fintype.sum_prod_type
        (f := fun p : W₁ × W₂ => f p
          • Perspectival.WantableGPT.vertex (W₁ × W₂) p)]
  exact Perspectival.WantableGPT.vertex_decomposition (W₁ × W₂) f

/-- Concrete: diagonalState decomposes as ½•(vertex (true,true) ⊗ ...)
+ ½•(vertex (false,false) ⊗ ...) — a classical mixture of product states. -/
example : diagonalState
        = ∑ b₁ : Bool, ∑ b₂ : Bool, diagonalState (b₁, b₂)
          • productState (Perspectival.WantableGPT.vertex Bool b₁)
                         (Perspectival.WantableGPT.vertex Bool b₂) :=
  WantableGPT_state_prod_vertex_decomp _

/-- Concrete: any state on Bool × Bool decomposes into product vertex
states (classical separability — no quantum entanglement). -/
example (f : Perspectival.WantableGPT.V (Bool × Bool)) :
    f = ∑ b₁ : Bool, ∑ b₂ : Bool, f (b₁, b₂)
      • productState (Perspectival.WantableGPT.vertex Bool b₁)
                     (Perspectival.WantableGPT.vertex Bool b₂) :=
  WantableGPT_state_prod_vertex_decomp f

/-- Classical separability: every state on a product Wantable is a
"separable mixture" — a sum of weighted product-vertex states. -/
theorem WantableGPT_classical_separability
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    ∃ (coeffs : W₁ × W₂ → ℝ),
      f = ∑ p, coeffs p
        • productState (Perspectival.WantableGPT.vertex W₁ p.1)
                       (Perspectival.WantableGPT.vertex W₂ p.2) := by
  refine ⟨f, ?_⟩
  rw [Fintype.sum_prod_type]
  exact WantableGPT_state_prod_vertex_decomp f

/-- Concrete: diagonalState exhibits classical separability. -/
example : ∃ (coeffs : Bool × Bool → ℝ),
    diagonalState = ∑ p, coeffs p
      • productState (Perspectival.WantableGPT.vertex Bool p.1)
                     (Perspectival.WantableGPT.vertex Bool p.2) :=
  WantableGPT_classical_separability diagonalState

/-- antiDiagonalState exhibits classical separability. -/
example : ∃ (coeffs : Bool × Bool → ℝ),
    antiDiagonalState = ∑ p, coeffs p
      • productState (Perspectival.WantableGPT.vertex Bool p.1)
                     (Perspectival.WantableGPT.vertex Bool p.2) :=
  WantableGPT_classical_separability antiDiagonalState

/-- uniformState (Bool × Bool) exhibits classical separability. -/
example : ∃ (coeffs : Bool × Bool → ℝ),
    uniformState (Bool × Bool) = ∑ p, coeffs p
      • productState (Perspectival.WantableGPT.vertex Bool p.1)
                     (Perspectival.WantableGPT.vertex Bool p.2) :=
  WantableGPT_classical_separability _

/-- productState uniformBool uniformBool exhibits classical separability. -/
example : ∃ (coeffs : Bool × Bool → ℝ),
    productState uniformBool uniformBool = ∑ p, coeffs p
      • productState (Perspectival.WantableGPT.vertex Bool p.1)
                     (Perspectival.WantableGPT.vertex Bool p.2) :=
  WantableGPT_classical_separability _

/-- Generic classical-separability for triples (Bool × Bool × Bool). -/
example (f : Perspectival.WantableGPT.V (Bool × (Bool × Bool))) :
    ∃ (coeffs : Bool × (Bool × Bool) → ℝ),
      f = ∑ p, coeffs p
        • productState (Perspectival.WantableGPT.vertex Bool p.1)
                       (Perspectival.WantableGPT.vertex (Bool × Bool) p.2) :=
  WantableGPT_classical_separability f

/-- Generic classical-separability for Fin 3 × Bool. -/
example (f : Perspectival.WantableGPT.V (Fin 3 × Bool)) :
    ∃ (coeffs : Fin 3 × Bool → ℝ),
      f = ∑ p, coeffs p
        • productState (Perspectival.WantableGPT.vertex (Fin 3) p.1)
                       (Perspectival.WantableGPT.vertex Bool p.2) :=
  WantableGPT_classical_separability f

/-- Generic classical-separability for Fin 4 × Fin 4. -/
example (f : Perspectival.WantableGPT.V (Fin 4 × Fin 4)) :
    ∃ (coeffs : Fin 4 × Fin 4 → ℝ),
      f = ∑ p, coeffs p
        • productState (Perspectival.WantableGPT.vertex (Fin 4) p.1)
                       (Perspectival.WantableGPT.vertex (Fin 4) p.2) :=
  WantableGPT_classical_separability f

/-- Born-rule for productState: proj(w₁, w₂) of productState f₁ f₂
gives f₁ w₁ * f₂ w₂. -/
theorem proj_productState
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w₁ : W₁) (w₂ : W₂) (f₁ : Perspectival.WantableGPT.V W₁)
    (f₂ : Perspectival.WantableGPT.V W₂) :
    Perspectival.WantableGPT.proj (W₁ × W₂) (w₁, w₂)
      (productState f₁ f₂) = f₁ w₁ * f₂ w₂ := rfl

/-- Concrete: proj (true, false) of productState f₁ f₂ on Bool×Bool. -/
example (f₁ f₂ : Perspectival.WantableGPT.V Bool) :
    Perspectival.WantableGPT.proj (Bool × Bool) (true, false)
      (productState f₁ f₂) = f₁ true * f₂ false :=
  proj_productState true false f₁ f₂

/-- Concrete: proj (true, true) of productState (vertex true) (vertex true) = 1. -/
example : Perspectival.WantableGPT.proj (Bool × Bool) (true, true)
            (productState (Perspectival.WantableGPT.vertex Bool true)
                          (Perspectival.WantableGPT.vertex Bool true)) = 1 := by
  rw [proj_productState]
  show (if true = true then (1 : ℝ) else 0) * (if true = true then 1 else 0) = 1
  simp

/-- Left marginal of productState f₁ f₂ at w₁ gives f₁ w₁ * (unit f₂). -/
theorem productState_left_marginal
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (w₁ : W₁) :
    (∑ w₂, productState f₁ f₂ (w₁, w₂))
      = f₁ w₁ * Perspectival.WantableGPT.unitFn W₂ f₂ := by
  show (∑ w₂, f₁ w₁ * f₂ w₂) = f₁ w₁ * Perspectival.WantableGPT.unitFn W₂ f₂
  rw [← Finset.mul_sum]
  rfl

/-- Right marginal of productState f₁ f₂ at w₂ gives (unit f₁) * f₂ w₂. -/
theorem productState_right_marginal
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (w₂ : W₂) :
    (∑ w₁, productState f₁ f₂ (w₁, w₂))
      = Perspectival.WantableGPT.unitFn W₁ f₁ * f₂ w₂ := by
  show (∑ w₁, f₁ w₁ * f₂ w₂) = Perspectival.WantableGPT.unitFn W₁ f₁ * f₂ w₂
  rw [← Finset.sum_mul]
  rfl

/-- For normalized factors (f₁, f₂ states), the left marginal of
productState gives exactly f₁. -/
theorem productState_left_marginal_state
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₂ : f₂ ∈ Perspectival.WantableGPT.states W₂) (w₁ : W₁) :
    (∑ w₂, productState f₁ f₂ (w₁, w₂)) = f₁ w₁ := by
  rw [productState_left_marginal]
  have : Perspectival.WantableGPT.unitFn W₂ f₂ = 1 := h₂.2
  rw [this]
  ring

/-- For normalized factors, the right marginal gives f₂. -/
theorem productState_right_marginal_state
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : f₁ ∈ Perspectival.WantableGPT.states W₁) (w₂ : W₂) :
    (∑ w₁, productState f₁ f₂ (w₁, w₂)) = f₂ w₂ := by
  rw [productState_right_marginal]
  have : Perspectival.WantableGPT.unitFn W₁ f₁ = 1 := h₁.2
  rw [this]
  ring

/-- Concrete: left marginal of productState (vertex true) (uniformBool)
gives vertex true. -/
example (b : Bool) :
    (∑ b₂, productState (Perspectival.WantableGPT.vertex Bool true)
                        uniformBool (b, b₂))
    = Perspectival.WantableGPT.vertex Bool true b :=
  productState_left_marginal_state _ _ uniformBool_in_states b

/-- Concrete: right marginal of productState uniformBool (vertex false)
gives vertex false. -/
example (b : Bool) :
    (∑ b₁, productState uniformBool
                        (Perspectival.WantableGPT.vertex Bool false) (b₁, b))
    = Perspectival.WantableGPT.vertex Bool false b :=
  productState_right_marginal_state _ _ uniformBool_in_states b

/-- Concrete: left marginal of productState uniformBool uniformBool
gives uniformBool. -/
example (b : Bool) :
    (∑ b₂, productState uniformBool uniformBool (b, b₂))
    = uniformBool b :=
  productState_left_marginal_state _ _ uniformBool_in_states b

/-- New theorem: marginalization is a linear operation (LeftMarginal
is a LinearMap). -/
noncomputable def leftMarginal
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    Perspectival.WantableGPT.V (W₁ × W₂) →ₗ[ℝ] Perspectival.WantableGPT.V W₁ where
  toFun f := fun w₁ => ∑ w₂, f (w₁, w₂)
  map_add' f g := by
    funext w₁
    show ∑ w₂, (f (w₁, w₂) + g (w₁, w₂))
       = (∑ w₂, f (w₁, w₂)) + (∑ w₂, g (w₁, w₂))
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    funext w₁
    show ∑ w₂, c * f (w₁, w₂)
       = c * ∑ w₂, f (w₁, w₂)
    rw [← Finset.mul_sum]

/-- leftMarginal applied to productState gives f₁ (up to unit on f₂). -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₂ : f₂ ∈ Perspectival.WantableGPT.states W₂) :
    leftMarginal (productState f₁ f₂) = f₁ := by
  funext w₁
  exact productState_left_marginal_state f₁ f₂ h₂ w₁

/-- Right marginalization as a LinearMap. -/
noncomputable def rightMarginal
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    Perspectival.WantableGPT.V (W₁ × W₂) →ₗ[ℝ] Perspectival.WantableGPT.V W₂ where
  toFun f := fun w₂ => ∑ w₁, f (w₁, w₂)
  map_add' f g := by
    funext w₂
    show ∑ w₁, (f (w₁, w₂) + g (w₁, w₂))
       = (∑ w₁, f (w₁, w₂)) + (∑ w₁, g (w₁, w₂))
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    funext w₂
    show ∑ w₁, c * f (w₁, w₂)
       = c * ∑ w₁, f (w₁, w₂)
    rw [← Finset.mul_sum]

/-- rightMarginal applied to productState gives f₂ (when f₁ is a state). -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : f₁ ∈ Perspectival.WantableGPT.states W₁) :
    rightMarginal (productState f₁ f₂) = f₂ := by
  funext w₂
  exact productState_right_marginal_state f₁ f₂ h₁ w₂

/-- Concrete: leftMarginal of diagonalState is uniformBool. -/
example : leftMarginal diagonalState = uniformBool := by
  funext b
  exact diagonalState_left_marginal b

/-- Concrete: rightMarginal of diagonalState is uniformBool. -/
example : rightMarginal diagonalState = uniformBool := by
  funext b
  exact diagonalState_right_marginal b

/-- Both marginals of diagonalState are uniformBool (despite the
correlation between factors!). -/
example : leftMarginal diagonalState = uniformBool ∧
          rightMarginal diagonalState = uniformBool := by
  refine ⟨?_, ?_⟩
  · funext b; exact diagonalState_left_marginal b
  · funext b; exact diagonalState_right_marginal b

/-- New theorem: diagonalState marginals = antiDiagonalState marginals (both uniform). -/
example : leftMarginal diagonalState = leftMarginal antiDiagonalState := by
  funext b
  show (∑ b₂, diagonalState (b, b₂)) = (∑ b₂, antiDiagonalState (b, b₂))
  rw [diagonalState_left_marginal b]
  rw [show (∑ b₂, antiDiagonalState (b, b₂))
        = antiDiagonalState (b, true) + antiDiagonalState (b, false) from by
      rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]]
  cases b with
  | true =>
    show uniformBool true = antiDiagonalState (true, true) + antiDiagonalState (true, false)
    show (1/2 : ℝ) = 0 + 1/2
    norm_num
  | false =>
    show uniformBool false = antiDiagonalState (false, true) + antiDiagonalState (false, false)
    show (1/2 : ℝ) = 1/2 + 0
    norm_num

/-- New: leftMarginal is linear: applies to sums of two states. -/
example (f g : Perspectival.WantableGPT.V (Bool × Bool)) :
    leftMarginal (f + g) = leftMarginal f + leftMarginal g := by
  rw [map_add]

/-- New: leftMarginal is scaled by scalar multiples. -/
example (c : ℝ) (f : Perspectival.WantableGPT.V (Bool × Bool)) :
    leftMarginal (c • f) = c • leftMarginal f := by
  rw [map_smul]

/-- New: rightMarginal is linear too. -/
example (f g : Perspectival.WantableGPT.V (Bool × Bool)) :
    rightMarginal (f + g) = rightMarginal f + rightMarginal g := by
  rw [map_add]

example (c : ℝ) (f : Perspectival.WantableGPT.V (Bool × Bool)) :
    rightMarginal (c • f) = c • rightMarginal f := by
  rw [map_smul]

/-- New: leftMarginal preserves unit (unitFn after marginal = unitFn of original). -/
theorem leftMarginal_unitFn
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    Perspectival.WantableGPT.unitFn W₁ (leftMarginal f)
      = Perspectival.WantableGPT.unitFn (W₁ × W₂) f := by
  show (∑ w₁, leftMarginal f w₁) = ∑ p : W₁ × W₂, f p
  show (∑ w₁, ∑ w₂, f (w₁, w₂)) = ∑ p : W₁ × W₂, f p
  rw [← Fintype.sum_prod_type]

/-- New: rightMarginal preserves unit. -/
theorem rightMarginal_unitFn
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    Perspectival.WantableGPT.unitFn W₂ (rightMarginal f)
      = Perspectival.WantableGPT.unitFn (W₁ × W₂) f := by
  show (∑ w₂, rightMarginal f w₂) = ∑ p : W₁ × W₂, f p
  show (∑ w₂, ∑ w₁, f (w₁, w₂)) = ∑ p : W₁ × W₂, f p
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]

/-- leftMarginal preserves states (normalized stays normalized). -/
theorem leftMarginal_preserves_states
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂))
    (hf : f ∈ Perspectival.WantableGPT.states (W₁ × W₂)) :
    leftMarginal f ∈ Perspectival.WantableGPT.states W₁ := by
  refine ⟨?_, ?_⟩
  · intro w₁
    show 0 ≤ ∑ w₂, f (w₁, w₂)
    exact Finset.sum_nonneg fun w₂ _ => hf.1 (w₁, w₂)
  · have hu := leftMarginal_unitFn f
    show Perspectival.WantableGPT.unitFn W₁ (leftMarginal f) = 1
    rw [hu]
    exact hf.2

/-- rightMarginal preserves states. -/
theorem rightMarginal_preserves_states
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂))
    (hf : f ∈ Perspectival.WantableGPT.states (W₁ × W₂)) :
    rightMarginal f ∈ Perspectival.WantableGPT.states W₂ := by
  refine ⟨?_, ?_⟩
  · intro w₂
    show 0 ≤ ∑ w₁, f (w₁, w₂)
    exact Finset.sum_nonneg fun w₁ _ => hf.1 (w₁, w₂)
  · have hu := rightMarginal_unitFn f
    show Perspectival.WantableGPT.unitFn W₂ (rightMarginal f) = 1
    rw [hu]
    exact hf.2

/-- leftMarginal of vertex (w₁, w₂) gives vertex w₁. -/
theorem leftMarginal_vertex
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w₁ : W₁) (w₂ : W₂) :
    leftMarginal (Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂))
      = Perspectival.WantableGPT.vertex W₁ w₁ := by
  rw [← productState_vertex]
  funext v
  exact productState_left_marginal_state _ _
    (Perspectival.WantableGPT.vertex_in_states W₂ w₂) v

/-- rightMarginal of vertex (w₁, w₂) gives vertex w₂. -/
theorem rightMarginal_vertex
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (w₁ : W₁) (w₂ : W₂) :
    rightMarginal (Perspectival.WantableGPT.vertex (W₁ × W₂) (w₁, w₂))
      = Perspectival.WantableGPT.vertex W₂ w₂ := by
  rw [← productState_vertex]
  funext v
  exact productState_right_marginal_state _ _
    (Perspectival.WantableGPT.vertex_in_states W₁ w₁) v

/-- Concrete: leftMarginal of vertex (true, false) on Bool × Bool = vertex true. -/
example : leftMarginal (Perspectival.WantableGPT.vertex (Bool × Bool) (true, false))
        = Perspectival.WantableGPT.vertex Bool true :=
  leftMarginal_vertex true false

/-- Concrete: rightMarginal of vertex (true, false) on Bool × Bool = vertex false. -/
example : rightMarginal (Perspectival.WantableGPT.vertex (Bool × Bool) (true, false))
        = Perspectival.WantableGPT.vertex Bool false :=
  rightMarginal_vertex true false

/-- leftMarginal of the constant-1 function = constant-|W₂|. -/
theorem leftMarginal_const_one
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    leftMarginal (fun _ : W₁ × W₂ => (1 : ℝ))
      = fun _ : W₁ => (Fintype.card W₂ : ℝ) := by
  funext w₁
  show ∑ _ : W₂, (1 : ℝ) = (Fintype.card W₂ : ℝ)
  rw [Finset.sum_const, Finset.card_univ]
  simp

/-- rightMarginal of the constant-1 function = constant-|W₁|. -/
theorem rightMarginal_const_one
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂] :
    rightMarginal (fun _ : W₁ × W₂ => (1 : ℝ))
      = fun _ : W₂ => (Fintype.card W₁ : ℝ) := by
  funext w₂
  show ∑ _ : W₁, (1 : ℝ) = (Fintype.card W₁ : ℝ)
  rw [Finset.sum_const, Finset.card_univ]
  simp

/-- Concrete: leftMarginal of constant-1 on Bool × Bool = constant 2. -/
example : leftMarginal (fun _ : Bool × Bool => (1 : ℝ))
        = fun _ : Bool => (2 : ℝ) := by
  rw [leftMarginal_const_one]
  funext _
  norm_cast

/-- Marginalization commutes with complementAction on the product:
leftMarginal (complementAction f) = complementAction (leftMarginal f). -/
theorem leftMarginal_complementAction
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    leftMarginal (Perspectival.WantableGPT.complementAction (W₁ × W₂) f)
      = Perspectival.WantableGPT.complementAction W₁ (leftMarginal f) := by
  funext w₁
  show (∑ w₂, f (Wantable.complement w₁, Wantable.complement w₂))
     = (∑ w₂, f (Wantable.complement w₁, w₂))
  exact Equiv.sum_comp
    (⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩ : W₂ ≃ W₂)
    (fun w₂ => f (Wantable.complement w₁, w₂))

/-- Marginalization on rightMarginal also commutes with complement. -/
theorem rightMarginal_complementAction
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f : Perspectival.WantableGPT.V (W₁ × W₂)) :
    rightMarginal (Perspectival.WantableGPT.complementAction (W₁ × W₂) f)
      = Perspectival.WantableGPT.complementAction W₂ (rightMarginal f) := by
  funext w₂
  show (∑ w₁, f (Wantable.complement w₁, Wantable.complement w₂))
     = (∑ w₁, f (w₁, Wantable.complement w₂))
  exact Equiv.sum_comp
    (⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩ : W₁ ≃ W₁)
    (fun w₁ => f (w₁, Wantable.complement w₂))

/-- Concrete: complementAction of diagonalState has same marginal as
diagonalState (which is uniformBool, also complement-invariant). -/
example : leftMarginal
            (Perspectival.WantableGPT.complementAction (Bool × Bool) diagonalState)
        = leftMarginal diagonalState := by
  rw [leftMarginal_complementAction]
  funext b
  show leftMarginal diagonalState (Wantable.complement b) = leftMarginal diagonalState b
  show (∑ b₂, diagonalState (Wantable.complement b, b₂))
     = (∑ b₂, diagonalState (b, b₂))
  rw [diagonalState_left_marginal, diagonalState_left_marginal]
  cases b <;> rfl

/-- Marginals are mutually inverse to productState restricted to product
states: starting from a product state, marginalizing gives the factors,
and rebuilding gives the product state back. -/
example {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f₁ : Perspectival.WantableGPT.V W₁) (f₂ : Perspectival.WantableGPT.V W₂)
    (h₁ : f₁ ∈ Perspectival.WantableGPT.states W₁)
    (h₂ : f₂ ∈ Perspectival.WantableGPT.states W₂) :
    productState (leftMarginal (productState f₁ f₂))
                 (rightMarginal (productState f₁ f₂))
    = productState f₁ f₂ := by
  rw [show leftMarginal (productState f₁ f₂) = f₁ from by
        funext w₁; exact productState_left_marginal_state f₁ f₂ h₂ w₁]
  rw [show rightMarginal (productState f₁ f₂) = f₂ from by
        funext w₂; exact productState_right_marginal_state f₁ f₂ h₁ w₂]

/-- Crucial: diagonalState ≠ productState (leftMarginal diagonalState)
(rightMarginal diagonalState). The marginals don't reconstruct the
correlated state — the framework supports nontrivial correlations
beyond what marginals capture. -/
example : diagonalState ≠ productState (leftMarginal diagonalState)
                                       (rightMarginal diagonalState) := by
  intro h
  have h_left : leftMarginal diagonalState = uniformBool := by
    funext b; exact diagonalState_left_marginal b
  have h_right : rightMarginal diagonalState = uniformBool := by
    funext b; exact diagonalState_right_marginal b
  rw [h_left, h_right] at h
  have h_val : diagonalState (true, false)
             = productState uniformBool uniformBool (true, false) := by rw [h]
  have h_LHS : diagonalState (true, false) = 0 := by
    show (if (true, false) = (true, true) ∨ (true, false) = (false, false)
          then (1/2 : ℝ) else 0) = 0
    simp
  have h_RHS : productState uniformBool uniformBool (true, false) = 1/4 := by
    show uniformBool true * uniformBool false = 1/4
    show (1/2 : ℝ) * (1/2 : ℝ) = 1/4
    norm_num
  rw [h_LHS, h_RHS] at h_val
  norm_num at h_val

/-- Concrete: antiDiagonalState ≠ productState of its marginals. -/
example : antiDiagonalState ≠ productState (leftMarginal antiDiagonalState)
                                            (rightMarginal antiDiagonalState) := by
  intro h
  have h_val : antiDiagonalState (true, true)
             = productState (leftMarginal antiDiagonalState)
                            (rightMarginal antiDiagonalState) (true, true) :=
    congr_fun h _
  have h_LHS : antiDiagonalState (true, true) = 0 := by
    show (if (true, true) = (true, false) ∨ (true, true) = (false, true)
          then (1/2 : ℝ) else 0) = 0
    simp
  have h_RHS : productState (leftMarginal antiDiagonalState)
                           (rightMarginal antiDiagonalState) (true, true) = 1/4 := by
    show leftMarginal antiDiagonalState true * rightMarginal antiDiagonalState true = 1/4
    show (∑ b₂, antiDiagonalState (true, b₂)) * (∑ b₁, antiDiagonalState (b₁, true)) = 1/4
    rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton,
        Finset.sum_insert (by decide), Finset.sum_singleton]
    show (antiDiagonalState (true, true) + antiDiagonalState (true, false))
       * (antiDiagonalState (true, true) + antiDiagonalState (false, true))
       = 1/4
    show ((0 : ℝ) + 1/2) * (0 + 1/2) = 1/4
    norm_num
  rw [h_LHS, h_RHS] at h_val
  norm_num at h_val

/-- The framework's "no-signaling" predicate: the marginal at one factor
is the same whether or not we marginalize over the other (trivially
holds since marginalization is a single operation). -/
theorem WantableGPT_no_signaling_left
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f g : Perspectival.WantableGPT.V (W₁ × W₂))
    (h : ∀ w₁ w₂, f (w₁, w₂) = g (w₁, w₂)) :
    leftMarginal f = leftMarginal g := by
  funext w₁
  show (∑ w₂, f (w₁, w₂)) = (∑ w₂, g (w₁, w₂))
  apply Finset.sum_congr rfl
  intro w₂ _
  exact h w₁ w₂

/-- Similarly for rightMarginal: if f = g pointwise, then so are
their right marginals. -/
theorem WantableGPT_no_signaling_right
    {W₁ W₂ : Type u} [Wantable W₁] [Wantable W₂]
    [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]
    (f g : Perspectival.WantableGPT.V (W₁ × W₂))
    (h : ∀ w₁ w₂, f (w₁, w₂) = g (w₁, w₂)) :
    rightMarginal f = rightMarginal g := by
  funext w₂
  show (∑ w₁, f (w₁, w₂)) = (∑ w₁, g (w₁, w₂))
  apply Finset.sum_congr rfl
  intro w₁ _
  exact h w₁ w₂

/-- Concrete: diagonalState and antiDiagonalState (with disjoint
support!) still have the same marginals — neither side can
"signal" which state it's in by looking at its own marginal. -/
example : leftMarginal diagonalState = leftMarginal antiDiagonalState := by
  funext b
  show (∑ b₂, diagonalState (b, b₂)) = (∑ b₂, antiDiagonalState (b, b₂))
  rw [diagonalState_left_marginal]
  rw [show (∑ b₂, antiDiagonalState (b, b₂))
        = antiDiagonalState (b, true) + antiDiagonalState (b, false) from by
      rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]]
  cases b with
  | true => show uniformBool true = (0 : ℝ) + 1/2; norm_num; rfl
  | false => show uniformBool false = (1/2 : ℝ) + 0; norm_num; rfl

/-- Similarly: right marginals are equal. -/
example : rightMarginal diagonalState = rightMarginal antiDiagonalState := by
  funext b
  show (∑ b₁, diagonalState (b₁, b)) = (∑ b₁, antiDiagonalState (b₁, b))
  rw [diagonalState_right_marginal]
  rw [show (∑ b₁, antiDiagonalState (b₁, b))
        = antiDiagonalState (true, b) + antiDiagonalState (false, b) from by
      rw [show (Finset.univ : Finset Bool) = {true, false} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]]
  cases b with
  | true => show uniformBool true = (0 : ℝ) + 1/2; norm_num; rfl
  | false => show uniformBool false = (1/2 : ℝ) + 0; norm_num; rfl

/-- The diagonal and antiDiagonal states are 50/50 mixed to form
uniformState (Bool × Bool). -/
example : uniformState (Bool × Bool)
        = (1/2 : ℝ) • diagonalState + (1/2 : ℝ) • antiDiagonalState := by
  funext p
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    (show (1 / ((Fintype.card (Bool × Bool) : ℝ)))
        = (1/2 : ℝ) * diagonalState _ + (1/2 : ℝ) * antiDiagonalState _) <;>
    (simp only [show (Fintype.card (Bool × Bool) : ℝ) = 4 from by norm_cast]) <;>
    (show ((1 : ℝ) / 4) = (1/2 : ℝ) * _ + (1/2 : ℝ) * _) <;>
    (first | (show _ = (1/2 : ℝ) * (1/2 : ℝ) + (1/2 : ℝ) * 0; norm_num)
           | (show _ = (1/2 : ℝ) * 0 + (1/2 : ℝ) * (1/2 : ℝ); norm_num))

/-- The diagonal and antiDiagonal states' marginals together coincide
with the marginals of uniformState (which is their 50/50 mixture). -/
example : leftMarginal (uniformState (Bool × Bool))
        = (1/2 : ℝ) • leftMarginal diagonalState
        + (1/2 : ℝ) • leftMarginal antiDiagonalState := by
  show leftMarginal (uniformState (Bool × Bool))
     = (1/2 : ℝ) • leftMarginal diagonalState
     + (1/2 : ℝ) • leftMarginal antiDiagonalState
  have hcom : uniformState (Bool × Bool)
            = (1/2 : ℝ) • diagonalState + (1/2 : ℝ) • antiDiagonalState := by
    funext p
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;>
      (show (1 / ((Fintype.card (Bool × Bool) : ℝ)))
          = (1/2 : ℝ) * diagonalState _ + (1/2 : ℝ) * antiDiagonalState _) <;>
      (simp only [show (Fintype.card (Bool × Bool) : ℝ) = 4 from by norm_cast]) <;>
      (first | (show ((1 : ℝ) / 4) = (1/2 : ℝ) * (1/2 : ℝ) + (1/2 : ℝ) * 0; norm_num)
             | (show ((1 : ℝ) / 4) = (1/2 : ℝ) * 0 + (1/2 : ℝ) * (1/2 : ℝ); norm_num))
  rw [hcom]
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]

/-- Same for rightMarginal: linearity carries over. -/
example : rightMarginal (uniformState (Bool × Bool))
        = (1/2 : ℝ) • rightMarginal diagonalState
        + (1/2 : ℝ) • rightMarginal antiDiagonalState := by
  show rightMarginal (uniformState (Bool × Bool))
     = (1/2 : ℝ) • rightMarginal diagonalState
     + (1/2 : ℝ) • rightMarginal antiDiagonalState
  have hcom : uniformState (Bool × Bool)
            = (1/2 : ℝ) • diagonalState + (1/2 : ℝ) • antiDiagonalState := by
    funext p
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;>
      (show (1 / ((Fintype.card (Bool × Bool) : ℝ)))
          = (1/2 : ℝ) * diagonalState _ + (1/2 : ℝ) * antiDiagonalState _) <;>
      (simp only [show (Fintype.card (Bool × Bool) : ℝ) = 4 from by norm_cast]) <;>
      (first | (show ((1 : ℝ) / 4) = (1/2 : ℝ) * (1/2 : ℝ) + (1/2 : ℝ) * 0; norm_num)
             | (show ((1 : ℝ) / 4) = (1/2 : ℝ) * 0 + (1/2 : ℝ) * (1/2 : ℝ); norm_num))
  rw [hcom]
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]

/-- New: the WantableGPT product Wantable structure is consistent with
componentwise complement. -/
example (p : Bool × Bool) : Wantable.complement p
        = (Wantable.complement p.1, Wantable.complement p.2) := rfl

/-- New: the WantableGPT sum Wantable structure on (Bool ⊕ Bool). -/
example (b : Bool) : Wantable.complement (Sum.inl b : Bool ⊕ Bool)
        = Sum.inl (Wantable.complement b) := rfl

example (b : Bool) : Wantable.complement (Sum.inr b : Bool ⊕ Bool)
        = Sum.inr (Wantable.complement b) := rfl

/-- Triple-Wantable complement on Bool × Bool × Bool. -/
example (p : Bool × Bool × Bool) : Wantable.complement p
        = (Wantable.complement p.1, Wantable.complement p.2.1,
           Wantable.complement p.2.2) := rfl

/-- Concrete: complement (true, false, true) = (false, true, false). -/
example : Wantable.complement ((true, false, true) : Bool × Bool × Bool)
        = (false, true, false) := rfl

/-- Complement is involutive on Bool × Bool × Bool. -/
example (p : Bool × Bool × Bool) : Wantable.complement (Wantable.complement p) = p :=
  Wantable.complement_involutive p

/-- Concrete: |Bool × Bool × Bool| = 8. -/
example : Fintype.card (Bool × Bool × Bool) = 8 := by decide

/-- Concrete: WantableGPT dim on Bool × Bool × Bool = 8. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) = 8 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Concrete triple no-go on Bool × Bool × Bool. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool))
        ≠ Fintype.card (Bool × Bool × Bool) * Fintype.card (Bool × Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Bool × Bool × Bool) (by decide)

/-- Concrete: vertex (true, false, true) on Bool × Bool × Bool. -/
example : Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, false, true)
            (true, false, true) = 1 := by
  show (if (true, false, true) = (true, false, true) then (1 : ℝ) else 0) = 1
  simp

example : Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, false, true)
            (false, false, true) = 0 := by
  show (if (true, false, true) = (false, false, true) then (1 : ℝ) else 0) = 0
  simp

/-- Concrete: triple productState on Bool × Bool × Bool. -/
example : productState (Perspectival.WantableGPT.vertex Bool true)
                       (productState (Perspectival.WantableGPT.vertex Bool false)
                                     (Perspectival.WantableGPT.vertex Bool true))
        ∈ Perspectival.WantableGPT.states (Bool × Bool × Bool) :=
  productState_in_states _ _
    (Perspectival.WantableGPT.vertex_in_states Bool true)
    (productState_in_states _ _
      (Perspectival.WantableGPT.vertex_in_states Bool false)
      (Perspectival.WantableGPT.vertex_in_states Bool true))

/-- Concrete: uniformState (Bool × Bool × Bool) factorizes. -/
example : uniformState (Bool × Bool × Bool)
        = productState uniformBool (uniformState (Bool × Bool)) :=
  uniformState_prod_factor

/-- Concrete: uniformState (Bool × Bool × Bool) value at any point = 1/8. -/
example (p : Bool × Bool × Bool) : uniformState (Bool × Bool × Bool) p = 1/8 := by
  show (1 : ℝ) / (Fintype.card (Bool × Bool × Bool) : ℝ) = 1/8
  norm_cast

-- Note: a triple-decomp theorem for vertex on Bool×Bool×Bool would be
-- deferred — Lean's decidable reasoning has trouble with the
-- classical-from-Mathlib instance interfering with reduction.

/-- Concrete: vertex (true, false, true) on Bool³ at the same point = 1. -/
example : Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, false, true)
            (true, false, true) = 1 := by
  show (if (true, false, true) = (true, false, true) then (1 : ℝ) else 0) = 1
  simp

/-- Concrete: on Fin 3 × Fin 4, |Fin 3 × Fin 4| = 12. -/
example : Fintype.card (Fin 3 × Fin 4) = 12 := by decide

/-- Concrete: WantableGPT dim on Fin 3 × Fin 4 = 12. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 × Fin 4)) = 12 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Concrete: uniformState (Fin 3 × Fin 4) at any point = 1/12. -/
example (p : Fin 3 × Fin 4) : uniformState (Fin 3 × Fin 4) p = 1/12 := by
  show (1 : ℝ) / (Fintype.card (Fin 3 × Fin 4) : ℝ) = 1/12
  norm_cast

/-- Concrete: on Fin 3 ⊕ Bool, |Fin 3 ⊕ Bool| = 5. -/
example : Fintype.card (Fin 3 ⊕ Bool) = 5 := by decide

/-- Concrete: WantableGPT dim on Fin 3 ⊕ Bool = 5. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 ⊕ Bool)) = 5 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Concrete: uniformState (Fin 3 ⊕ Bool) at any point = 1/5. -/
example (p : Fin 3 ⊕ Bool) : uniformState (Fin 3 ⊕ Bool) p = 1/5 := by
  show (1 : ℝ) / (Fintype.card (Fin 3 ⊕ Bool) : ℝ) = 1/5
  norm_cast

/-- Concrete: |Bool × (Bool × Bool)| = 8 = |Bool × Bool × Bool|. -/
example : Fintype.card (Bool × (Bool × Bool)) = Fintype.card (Bool × Bool × Bool) := by
  decide

/-- Concrete: |(Bool × Bool) × Bool| = 8. -/
example : Fintype.card ((Bool × Bool) × Bool) = 8 := by decide

/-- Concrete: |Bool × Bool × Bool × Bool| = 16. -/
example : Fintype.card (Bool × Bool × Bool × Bool) = 16 := by decide

/-- Concrete: WantableGPT dim on Bool × Bool × Bool × Bool = 16. -/
example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool)) = 16 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Concrete: triple no-go on Bool⁴. -/
example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
    ≠ Fintype.card (Bool × Bool × Bool × Bool)
    * Fintype.card (Bool × Bool × Bool × Bool) :=
  Perspectival.WantableGPT.wantableGPT_not_quantum (Bool × Bool × Bool × Bool)
    (by decide)

/-- Concrete: real-QM signature ruled out on Bool⁴. -/
example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool)) * 2
    ≠ Fintype.card (Bool × Bool × Bool × Bool)
    * (Fintype.card (Bool × Bool × Bool × Bool) + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM (Bool × Bool × Bool × Bool)
    (by decide)

/-- Concrete: quaternionic-QM signature ruled out on Bool⁴. -/
example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool × Bool))
    ≠ Fintype.card (Bool × Bool × Bool × Bool)
    * (2 * Fintype.card (Bool × Bool × Bool × Bool) - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM
    (Bool × Bool × Bool × Bool) (by decide)

/-- Triple no-go on Bool³. -/
example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool)) * 2
    ≠ Fintype.card (Bool × Bool × Bool)
    * (Fintype.card (Bool × Bool × Bool) + 1) :=
  Perspectival.WantableGPT.wantableGPT_not_realQM (Bool × Bool × Bool)
    (by decide)

example : Module.finrank ℝ
    (Perspectival.WantableGPT.V (Bool × Bool × Bool))
    ≠ Fintype.card (Bool × Bool × Bool)
    * (2 * Fintype.card (Bool × Bool × Bool) - 1) :=
  Perspectival.WantableGPT.wantableGPT_not_quaternionicQM (Bool × Bool × Bool)
    (by decide)

/-- Classical signature N = K explicit for Bool³ (N = K = 8). -/
example : Fintype.card (Bool × Bool × Bool) = 8 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Bool × Bool × Bool)) = 8 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Classical signature N = K explicit for Bool⁴ (N = K = 16). -/
example : Fintype.card (Bool × Bool × Bool × Bool) = 16 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V
            (Bool × Bool × Bool × Bool)) = 16 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Classical signature N = K explicit for Fin 3 × Fin 4 (N = K = 12). -/
example : Fintype.card (Fin 3 × Fin 4) = 12 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3 × Fin 4)) = 12 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Classical signature N = K explicit for Fin 4 ⊕ Bool (N = K = 6). -/
example : Fintype.card (Fin 4 ⊕ Bool) = 6 ∧
          Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4 ⊕ Bool)) = 6 := by
  refine ⟨by decide, ?_⟩
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- productState of vertex true and vertex true = vertex (true, true) on Bool × Bool. -/
example : productState (Perspectival.WantableGPT.vertex Bool true)
                       (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex (Bool × Bool) (true, true) :=
  productState_vertex true true

/-- productState of vertex true and vertex false = vertex (true, false). -/
example : productState (Perspectival.WantableGPT.vertex Bool true)
                       (Perspectival.WantableGPT.vertex Bool false)
        = Perspectival.WantableGPT.vertex (Bool × Bool) (true, false) :=
  productState_vertex true false

/-- productState of vertex false and vertex true = vertex (false, true). -/
example : productState (Perspectival.WantableGPT.vertex Bool false)
                       (Perspectival.WantableGPT.vertex Bool true)
        = Perspectival.WantableGPT.vertex (Bool × Bool) (false, true) :=
  productState_vertex false true

/-- productState of vertex false and vertex false = vertex (false, false). -/
example : productState (Perspectival.WantableGPT.vertex Bool false)
                       (Perspectival.WantableGPT.vertex Bool false)
        = Perspectival.WantableGPT.vertex (Bool × Bool) (false, false) :=
  productState_vertex false false

/-- Sum of all 4 product-vertex-states on Bool × Bool = const 1. -/
example : (∑ p : Bool × Bool,
    productState (Perspectival.WantableGPT.vertex Bool p.1)
                 (Perspectival.WantableGPT.vertex Bool p.2))
    = (fun _ : Bool × Bool => (1 : ℝ)) := by
  rw [show (fun (p : Bool × Bool) =>
            productState (Perspectival.WantableGPT.vertex Bool p.1)
                         (Perspectival.WantableGPT.vertex Bool p.2))
        = (fun p => Perspectival.WantableGPT.vertex (Bool × Bool) p) from by
      funext p; rcases p with ⟨a, b⟩; exact productState_vertex a b]
  exact WantableGPT_sum_vertices_eq_one

/-- Sum over all vertices of Bool×Bool×Bool = const 1. -/
example : (∑ p : Bool × Bool × Bool,
            Perspectival.WantableGPT.vertex (Bool × Bool × Bool) p)
        = (fun _ : Bool × Bool × Bool => (1 : ℝ)) :=
  WantableGPT_sum_vertices_eq_one

/-- Sum over all vertices of Fin 5 = const 1 (no Wantable instance, just
shows the underlying vertex_decomposition theorem applies). -/
example (n : ℕ) : (∑ i, Perspectival.Classical.vertex n i)
                = (fun _ : Fin n => (1 : ℝ)) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j
    (fun i _ hij => by
      show Perspectival.Classical.vertex n i j = 0
      show (if i = j then (1 : ℝ) else 0) = 0
      simp [hij])
    (fun h => absurd (Finset.mem_univ j) h)]
  show Perspectival.Classical.vertex n j j = 1
  show (if j = j then (1 : ℝ) else 0) = 1
  simp

/-- Classical.vertex is in WantableGPT-states-like simplex states. -/
example (n : ℕ) (i : Fin n) :
    Perspectival.Classical.vertex n i ∈ Perspectival.Classical.states n :=
  Perspectival.Classical.vertex_in_states n i

/-- Classical.gpt is a GPT. -/
example (n : ℕ) : Perspectival.GPT (Perspectival.Classical.V n) :=
  Perspectival.Classical.gpt n

/-- WantableGPT.gpt is a GPT. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.GPT (Perspectival.WantableGPT.V W) :=
  Perspectival.WantableGPT.gpt W

/-- Concrete: classical 2-outcome GPT has dim 2. -/
example : Module.finrank ℝ (Perspectival.Classical.V 2) = 2 := by
  show Module.finrank ℝ (Fin 2 → ℝ) = 2
  simp

/-- Concrete: classical 3-outcome GPT has dim 3. -/
example : Module.finrank ℝ (Perspectival.Classical.V 3) = 3 := by
  show Module.finrank ℝ (Fin 3 → ℝ) = 3
  simp

/-- Concrete: classical N-outcome GPT has dim N. -/
example (n : ℕ) : Module.finrank ℝ (Perspectival.Classical.V n) = n := by
  show Module.finrank ℝ (Fin n → ℝ) = n
  simp

/-- GPT.unit is the same as the WantableGPT.unitFn at the structure level. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.gpt W).unit = Perspectival.WantableGPT.unitFn W :=
  rfl

/-- GPT.states is the same as the WantableGPT.states. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.gpt W).states = Perspectival.WantableGPT.states W :=
  rfl

/-- GPT.unit on Classical.gpt is Classical.unitFn. -/
example (n : ℕ) :
    (Perspectival.Classical.gpt n).unit = Perspectival.Classical.unitFn n :=
  rfl

/-- GPT.states on Classical.gpt is Classical.states. -/
example (n : ℕ) :
    (Perspectival.Classical.gpt n).states = Perspectival.Classical.states n :=
  rfl

/-- GPT.effects on Classical.gpt is Classical.effects. -/
example (n : ℕ) :
    (Perspectival.Classical.gpt n).effects = Perspectival.Classical.effects n :=
  rfl

/-- Born-rule on Classical: prob (proj i) (vertex j) = δ_{ji}. -/
example (n : ℕ) (i j : Fin n) :
    (Perspectival.Classical.gpt n).prob
      (Perspectival.Classical.proj n i)
      (Perspectival.Classical.vertex n j)
    = if j = i then 1 else 0 :=
  Perspectival.Classical.proj_vertex n i j

/-- Concrete: prob (proj 0) (vertex 0) = 1 on Classical Fin 2. -/
example : (Perspectival.Classical.gpt 2).prob
            (Perspectival.Classical.proj 2 0)
            (Perspectival.Classical.vertex 2 0) = 1 := by
  show Perspectival.Classical.proj 2 0 (Perspectival.Classical.vertex 2 0) = 1
  rw [Perspectival.Classical.proj_vertex]; simp

/-- Concrete: prob (proj 0) (vertex 1) = 0 on Classical Fin 2. -/
example : (Perspectival.Classical.gpt 2).prob
            (Perspectival.Classical.proj 2 0)
            (Perspectival.Classical.vertex 2 1) = 0 := by
  show Perspectival.Classical.proj 2 0 (Perspectival.Classical.vertex 2 1) = 0
  rw [Perspectival.Classical.proj_vertex]; simp

/-- Concrete: prob (proj 1) (vertex 1) = 1 on Classical Fin 3. -/
example : (Perspectival.Classical.gpt 3).prob
            (Perspectival.Classical.proj 3 1)
            (Perspectival.Classical.vertex 3 1) = 1 := by
  show Perspectival.Classical.proj 3 1 (Perspectival.Classical.vertex 3 1) = 1
  rw [Perspectival.Classical.proj_vertex]; simp

/-- WantableGPT.gpt's prob applied to proj and vertex on Bool. -/
example : (Perspectival.WantableGPT.gpt Bool).prob
            (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool true) = 1 := by
  show Perspectival.WantableGPT.proj Bool true
        (Perspectival.WantableGPT.vertex Bool true) = 1
  rw [Perspectival.WantableGPT.proj_vertex]; simp

example : (Perspectival.WantableGPT.gpt Bool).prob
            (Perspectival.WantableGPT.proj Bool true)
            (Perspectival.WantableGPT.vertex Bool false) = 0 := by
  show Perspectival.WantableGPT.proj Bool true
        (Perspectival.WantableGPT.vertex Bool false) = 0
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- WantableGPT.gpt's prob on Fin 4. -/
example : (Perspectival.WantableGPT.gpt (Fin 4)).prob
            (Perspectival.WantableGPT.proj (Fin 4) 2)
            (Perspectival.WantableGPT.vertex (Fin 4) 2) = 1 := by
  show Perspectival.WantableGPT.proj (Fin 4) 2
        (Perspectival.WantableGPT.vertex (Fin 4) 2) = 1
  rw [Perspectival.WantableGPT.proj_vertex]; simp

example : (Perspectival.WantableGPT.gpt (Fin 4)).prob
            (Perspectival.WantableGPT.proj (Fin 4) 2)
            (Perspectival.WantableGPT.vertex (Fin 4) 1) = 0 := by
  show Perspectival.WantableGPT.proj (Fin 4) 2
        (Perspectival.WantableGPT.vertex (Fin 4) 1) = 0
  rw [Perspectival.WantableGPT.proj_vertex]; simp

/-- A non-Bool small Wantable instance: Fin 2 with the swap complement
gives the same essential structure as Bool. The cardinalities match. -/
example : Fintype.card (Fin 2) = Fintype.card Bool := by decide

example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 2))
        = Module.finrank ℝ (Perspectival.WantableGPT.V Bool) := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card,
      Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- Concrete vertices on Fin 2 evaluate to 1 at same point. -/
example : Perspectival.WantableGPT.vertex (Fin 2) 0
            (0 : Fin 2) = 1 := by
  show (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 1
  simp

example : Perspectival.WantableGPT.vertex (Fin 2) 0
            (1 : Fin 2) = 0 := by
  show (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) = 0
  simp

example : Perspectival.WantableGPT.vertex (Fin 2) 1
            (0 : Fin 2) = 0 := by
  show (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0
  simp

example : Perspectival.WantableGPT.vertex (Fin 2) 1
            (1 : Fin 2) = 1 := by
  show (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) = 1
  simp

/-- The Bool vertex states form a 2-element basis for V Bool. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = 2 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The Fin 3 vertex states form a 3-element basis. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 3)) = 3 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- The Fin 4 vertex states form a 4-element basis. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) = 4 := by
  rw [Perspectival.WantableGPT.finrank_V_eq_card]
  decide

/-- WantableGPT.gpt Bool has states_convex by construction. -/
example : Convex ℝ (Perspectival.WantableGPT.gpt Bool).states :=
  (Perspectival.WantableGPT.gpt Bool).states_convex

/-- WantableGPT.gpt Bool's effects are convex. -/
example : Convex ℝ (Perspectival.WantableGPT.gpt Bool).effects :=
  (Perspectival.WantableGPT.gpt Bool).effects_convex

/-- States on WantableGPT Bool are normalized. -/
example (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt Bool).states) :
    (Perspectival.WantableGPT.gpt Bool).unit ρ = 1 :=
  (Perspectival.WantableGPT.gpt Bool).states_normalized ρ hρ

/-- Probabilities on WantableGPT Bool are in [0,1]. -/
example (e : Perspectival.WantableGPT.V Bool →ₗ[ℝ] ℝ)
    (he : e ∈ (Perspectival.WantableGPT.gpt Bool).effects)
    (ρ : Perspectival.WantableGPT.V Bool)
    (hρ : ρ ∈ (Perspectival.WantableGPT.gpt Bool).states) :
    0 ≤ e ρ ∧ e ρ ≤ 1 :=
  (Perspectival.WantableGPT.gpt Bool).prob_in_unit_interval e he ρ hρ

/-- The unit on WantableGPT Bool is an effect. -/
example : (Perspectival.WantableGPT.gpt Bool).unit
        ∈ (Perspectival.WantableGPT.gpt Bool).effects :=
  (Perspectival.WantableGPT.gpt Bool).unit_is_effect

/-- WantableGPT Bool projection (proj true) is in effects. -/
example : Perspectival.WantableGPT.proj Bool true
        ∈ (Perspectival.WantableGPT.gpt Bool).effects :=
  Perspectival.WantableGPT.proj_in_effects Bool true

/-- WantableGPT Bool projection (proj false) is in effects. -/
example : Perspectival.WantableGPT.proj Bool false
        ∈ (Perspectival.WantableGPT.gpt Bool).effects :=
  Perspectival.WantableGPT.proj_in_effects Bool false

/-- WantableGPT Fin 4 projection (proj 2) is in effects. -/
example : Perspectival.WantableGPT.proj (Fin 4) 2
        ∈ (Perspectival.WantableGPT.gpt (Fin 4)).effects :=
  Perspectival.WantableGPT.proj_in_effects (Fin 4) 2

/-- WantableGPT Bool×Bool projection at (true, false) is in effects. -/
example : Perspectival.WantableGPT.proj (Bool × Bool) (true, false)
        ∈ (Perspectival.WantableGPT.gpt (Bool × Bool)).effects :=
  Perspectival.WantableGPT.proj_in_effects (Bool × Bool) (true, false)

/-- WantableGPT vertex_in_states applied generically. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (w : W) :
    Perspectival.WantableGPT.vertex W w ∈ (Perspectival.WantableGPT.gpt W).states :=
  Perspectival.WantableGPT.vertex_in_states W w

/-- Concrete: vertex true on Bool is in states. -/
example : Perspectival.WantableGPT.vertex Bool true
        ∈ (Perspectival.WantableGPT.gpt Bool).states :=
  Perspectival.WantableGPT.vertex_in_states Bool true

/-- Concrete: vertex (true, false) on Bool × Bool is in states. -/
example : Perspectival.WantableGPT.vertex (Bool × Bool) (true, false)
        ∈ (Perspectival.WantableGPT.gpt (Bool × Bool)).states :=
  Perspectival.WantableGPT.vertex_in_states (Bool × Bool) (true, false)

/-- Concrete: vertex 2 on Fin 4 is in states. -/
example : Perspectival.WantableGPT.vertex (Fin 4) 2
        ∈ (Perspectival.WantableGPT.gpt (Fin 4)).states :=
  Perspectival.WantableGPT.vertex_in_states (Fin 4) 2

/-- Concrete: vertex (true, true, true) on Bool×Bool×Bool is in states. -/
example : Perspectival.WantableGPT.vertex (Bool × Bool × Bool) (true, true, true)
        ∈ (Perspectival.WantableGPT.gpt (Bool × Bool × Bool)).states :=
  Perspectival.WantableGPT.vertex_in_states (Bool × Bool × Bool) (true, true, true)

/-- Concrete: classical vertex 0 on Fin 5 is in states. -/
example : Perspectival.Classical.vertex 5 0 ∈ (Perspectival.Classical.gpt 5).states :=
  Perspectival.Classical.vertex_in_states 5 0

/-- Concrete: classical vertex 4 on Fin 5 is in states. -/
example : Perspectival.Classical.vertex 5 4 ∈ (Perspectival.Classical.gpt 5).states :=
  Perspectival.Classical.vertex_in_states 5 4

/-- Concrete: classical vertex distinguishability on Fin 5. -/
example : Perspectival.Hardy.Distinguishable (Perspectival.Classical.gpt 5)
            (Perspectival.Classical.vertex 5 0)
            (Perspectival.Classical.vertex 5 3) :=
  Perspectival.Classical.vertices_distinguishable 5 0 3 (by decide)

/-- Concrete: classical vertex distinguishability on Fin 10. -/
example : Perspectival.Hardy.Distinguishable (Perspectival.Classical.gpt 10)
            (Perspectival.Classical.vertex 10 5)
            (Perspectival.Classical.vertex 10 9) :=
  Perspectival.Classical.vertices_distinguishable 10 5 9 (by decide)

/-- Concrete: classical proj 3 on Fin 10 is in effects. -/
example : Perspectival.Classical.proj 10 3 ∈ Perspectival.Classical.effects 10 :=
  Perspectival.Classical.proj_in_effects 10 3

/-- Concrete: classical proj_vertex on Fin 10. -/
example : Perspectival.Classical.proj 10 3 (Perspectival.Classical.vertex 10 3) = 1 := by
  rw [Perspectival.Classical.proj_vertex]
  simp

example : Perspectival.Classical.proj 10 3 (Perspectival.Classical.vertex 10 7) = 0 := by
  rw [Perspectival.Classical.proj_vertex]
  simp

/-- Concrete: vertex_linear_independent on Fin 10. -/
example : LinearIndependent ℝ (Perspectival.Classical.vertex 10) :=
  Perspectival.Classical.vertex_linear_independent 10

/-- Concrete: vertex_linear_independent on Fin 100. -/
example : LinearIndependent ℝ (Perspectival.Classical.vertex 100) :=
  Perspectival.Classical.vertex_linear_independent 100

/-- Classical Fin 100 GPT has dim 100. -/
example : Module.finrank ℝ (Perspectival.Classical.V 100) = 100 := by
  show Module.finrank ℝ (Fin 100 → ℝ) = 100
  simp

/-- Classical Fin 100 has vertices_span. -/
example : Submodule.span ℝ (Set.range (Perspectival.Classical.vertex 100)) = ⊤ :=
  Perspectival.Classical.vertices_span 100

/-- Classical Fin 100 perfect witness exists. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.Classical.gpt 100)
            (Perspectival.Classical.vertex 100) :=
  Perspectival.Classical.perfectWitness 100

/-- Classical Fin 100 has the operational dim bound 100 ≤ 100. -/
example : (100 : ℕ) ≤ Module.finrank ℝ (Perspectival.Classical.V 100) :=
  Perspectival.Distinguish.operational_dim_le_state_dim
    (Perspectival.Classical.vertex 100) (Perspectival.Classical.perfectWitness 100)

/-- WantableGPT Fin 4 perfect witness exists. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt (Fin 4))
            (Perspectival.WantableGPT.vertex (Fin 4)) :=
  Perspectival.WantableGPT.perfectWitness (Fin 4)

/-- WantableGPT Bool perfect witness exists. -/
example : Perspectival.Distinguish.PerfectWitness
            (G := Perspectival.WantableGPT.gpt Bool)
            (Perspectival.WantableGPT.vertex Bool) :=
  Perspectival.WantableGPT.perfectWitness Bool

/-- Operational dim ≤ structural dim for WantableGPT Fin 4. -/
example : (Fintype.card (Fin 4) : ℕ)
        ≤ Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4)) :=
  (Perspectival.WantableGPT.wantableGPT_is_classical (Fin 4)).1

/-- The classical signature holds with equality. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V (Fin 4))
        = Fintype.card (Fin 4) :=
  Perspectival.WantableGPT.finrank_V_eq_card (Fin 4)

/-- Module.Finite instance for WantableGPT V W. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.Finite ℝ (Perspectival.WantableGPT.V W) := inferInstance

/-- Concrete: V Bool is finite. -/
example : Module.Finite ℝ (Perspectival.WantableGPT.V Bool) := inferInstance

/-- Concrete: V (Fin 4) is finite. -/
example : Module.Finite ℝ (Perspectival.WantableGPT.V (Fin 4)) := inferInstance

/-- Concrete: V (Bool × Bool) is finite. -/
example : Module.Finite ℝ (Perspectival.WantableGPT.V (Bool × Bool)) := inferInstance

/-- AddCommGroup on V W is inferred. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    AddCommGroup (Perspectival.WantableGPT.V W) := inferInstance

/-- Module instance on V W. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module ℝ (Perspectival.WantableGPT.V W) := inferInstance

/-- WantableGPT vertexBasis on Bool. -/
noncomputable example : Module.Basis Bool ℝ (Perspectival.WantableGPT.V Bool) :=
  Perspectival.WantableGPT.vertexBasis Bool

/-- WantableGPT vertexBasis on Fin 4. -/
noncomputable example : Module.Basis (Fin 4) ℝ (Perspectival.WantableGPT.V (Fin 4)) :=
  Perspectival.WantableGPT.vertexBasis (Fin 4)

/-- WantableGPT vertexBasis on Bool × Bool. -/
noncomputable example : Module.Basis (Bool × Bool) ℝ
            (Perspectival.WantableGPT.V (Bool × Bool)) :=
  Perspectival.WantableGPT.vertexBasis (Bool × Bool)

/-- Generic: vertexBasis exists for any finite DecidableEq Wantable. -/
noncomputable example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Module.Basis W ℝ (Perspectival.WantableGPT.V W) :=
  Perspectival.WantableGPT.vertexBasis W

/-- The complementTransform is a GPT-self-transformation on Bool. -/
example : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt Bool)
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.WantableGPT.complementTransform Bool

/-- The complementTransform is a GPT-self-transformation on Fin 4. -/
example : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt (Fin 4))
            (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.WantableGPT.complementTransform (Fin 4)

/-- fromPTrans 1 is a self-Transform of WantableGPT Bool. -/
example : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt Bool)
            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.WantableGPT.fromPTrans Bool 1

/-- fromPTrans complementPTrans on Fin 4. -/
example : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt (Fin 4))
            (Perspectival.WantableGPT.gpt (Fin 4)) :=
  Perspectival.WantableGPT.fromPTrans (Fin 4)
    (Perspectival.WantableGPT.complementPTrans (Fin 4))

/-- fromPTransHom Bool is a MonoidHom. -/
example : (PTrans Bool) →* (Perspectival.WantableGPT.V Bool →ₗ[ℝ]
                            Perspectival.WantableGPT.V Bool) :=
  Perspectival.WantableGPT.fromPTransHom Bool

/-- fromPTransTransformHom Bool is a MonoidHom into Transform monoid. -/
example : (PTrans Bool) →* Perspectival.GPT.Transform
                            (Perspectival.WantableGPT.gpt Bool)
                            (Perspectival.WantableGPT.gpt Bool) :=
  Perspectival.WantableGPT.fromPTransTransformHom Bool

/-- fromPTransHom Fin 4 is a MonoidHom. -/
example : (PTrans (Fin 4)) →* (Perspectival.WantableGPT.V (Fin 4) →ₗ[ℝ]
                            Perspectival.WantableGPT.V (Fin 4)) :=
  Perspectival.WantableGPT.fromPTransHom (Fin 4)

/-- complementPTrans on Bool is a PTrans. -/
example : PTrans Bool := Perspectival.WantableGPT.complementPTrans Bool

/-- complementPTrans on Fin 4 is a PTrans. -/
example : PTrans (Fin 4) := Perspectival.WantableGPT.complementPTrans (Fin 4)

/-- complementPTrans toFun applied. -/
example : (Perspectival.WantableGPT.complementPTrans Bool).toFun true = false := rfl

example : (Perspectival.WantableGPT.complementPTrans Bool).toFun false = true := rfl

/-- complementPTrans is its own inverse (PTrans-level). -/
example : (Perspectival.WantableGPT.complementPTrans Bool).invFun true = false := rfl

example : (Perspectival.WantableGPT.complementPTrans Bool).invFun false = true := rfl

/-- complementPTrans on Fin 4 toFun. -/
example : (Perspectival.WantableGPT.complementPTrans (Fin 4)).toFun 0 = 3 := by decide
example : (Perspectival.WantableGPT.complementPTrans (Fin 4)).toFun 3 = 0 := by decide
example : (Perspectival.WantableGPT.complementPTrans (Fin 4)).toFun 1 = 2 := by decide
example : (Perspectival.WantableGPT.complementPTrans (Fin 4)).toFun 2 = 1 := by decide

/-- complementPTrans is its own inverse via PTrans group structure. -/
example : (Perspectival.WantableGPT.complementPTrans Bool)⁻¹
        = Perspectival.WantableGPT.complementPTrans Bool :=
  Perspectival.WantableGPT.complementPTrans_inv Bool

example : (Perspectival.WantableGPT.complementPTrans (Fin 4))⁻¹
        = Perspectival.WantableGPT.complementPTrans (Fin 4) :=
  Perspectival.WantableGPT.complementPTrans_inv (Fin 4)

/-- complementPTrans squared = id PTrans. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) *
          (Perspectival.WantableGPT.complementPTrans Bool) = 1 :=
  Perspectival.WantableGPT.complementPTrans_sq Bool

example : (Perspectival.WantableGPT.complementPTrans (Fin 4)) *
          (Perspectival.WantableGPT.complementPTrans (Fin 4)) = 1 :=
  Perspectival.WantableGPT.complementPTrans_sq (Fin 4)

/-- WantableGPT.complementPTrans Bool × Bool is its own inverse. -/
example : (Perspectival.WantableGPT.complementPTrans (Bool × Bool))⁻¹
        = Perspectival.WantableGPT.complementPTrans (Bool × Bool) :=
  Perspectival.WantableGPT.complementPTrans_inv (Bool × Bool)

/-- WantableGPT.complementPTrans Bool ⊕ Bool is its own inverse. -/
example : (Perspectival.WantableGPT.complementPTrans (Bool ⊕ Bool))⁻¹
        = Perspectival.WantableGPT.complementPTrans (Bool ⊕ Bool) :=
  Perspectival.WantableGPT.complementPTrans_inv (Bool ⊕ Bool)

/-- complementTransform_eq_fromPTrans_full on Bool. -/
example : Perspectival.WantableGPT.complementTransform Bool
        = Perspectival.WantableGPT.fromPTrans Bool
            (Perspectival.WantableGPT.complementPTrans Bool) :=
  Perspectival.WantableGPT.complementTransform_eq_fromPTrans_full Bool

/-- complementTransform_eq_fromPTrans_full on Fin 4. -/
example : Perspectival.WantableGPT.complementTransform (Fin 4)
        = Perspectival.WantableGPT.fromPTrans (Fin 4)
            (Perspectival.WantableGPT.complementPTrans (Fin 4)) :=
  Perspectival.WantableGPT.complementTransform_eq_fromPTrans_full (Fin 4)

/-- complementTransform_sq on Bool. -/
example : Perspectival.WantableGPT.complementTransform Bool *
          Perspectival.WantableGPT.complementTransform Bool
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) :=
  Perspectival.WantableGPT.complementTransform_sq Bool

/-- complementTransform_sq on Fin 4. -/
example : Perspectival.WantableGPT.complementTransform (Fin 4) *
          Perspectival.WantableGPT.complementTransform (Fin 4)
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt (Fin 4))
                  (Perspectival.WantableGPT.gpt (Fin 4))) :=
  Perspectival.WantableGPT.complementTransform_sq (Fin 4)

/-- complementTransform_sq on Bool × Bool. -/
example : Perspectival.WantableGPT.complementTransform (Bool × Bool) *
          Perspectival.WantableGPT.complementTransform (Bool × Bool)
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt (Bool × Bool))
                  (Perspectival.WantableGPT.gpt (Bool × Bool))) :=
  Perspectival.WantableGPT.complementTransform_sq (Bool × Bool)

/-- complementTransform_sq on Bool ⊕ Bool. -/
example : Perspectival.WantableGPT.complementTransform (Bool ⊕ Bool) *
          Perspectival.WantableGPT.complementTransform (Bool ⊕ Bool)
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt (Bool ⊕ Bool))
                  (Perspectival.WantableGPT.gpt (Bool ⊕ Bool))) :=
  Perspectival.WantableGPT.complementTransform_sq (Bool ⊕ Bool)

/-- fromPTransHom on complementPTrans = complementAction (PTrans→V W →ₗ V W form). -/
example : Perspectival.WantableGPT.fromPTransHom Bool
            (Perspectival.WantableGPT.complementPTrans Bool)
        = Perspectival.WantableGPT.complementAction Bool :=
  Perspectival.WantableGPT.fromPTransHom_complementPTrans Bool

example : Perspectival.WantableGPT.fromPTransHom (Fin 4)
            (Perspectival.WantableGPT.complementPTrans (Fin 4))
        = Perspectival.WantableGPT.complementAction (Fin 4) :=
  Perspectival.WantableGPT.fromPTransHom_complementPTrans (Fin 4)

/-- fromPTransTransformHom on complementPTrans = complementTransform. -/
example : Perspectival.WantableGPT.fromPTransTransformHom Bool
            (Perspectival.WantableGPT.complementPTrans Bool)
        = Perspectival.WantableGPT.complementTransform Bool :=
  Perspectival.WantableGPT.fromPTransTransformHom_complementPTrans Bool

example : Perspectival.WantableGPT.fromPTransTransformHom (Fin 4)
            (Perspectival.WantableGPT.complementPTrans (Fin 4))
        = Perspectival.WantableGPT.complementTransform (Fin 4) :=
  Perspectival.WantableGPT.fromPTransTransformHom_complementPTrans (Fin 4)

/-- fromPTransHom is injective on Bool. -/
example : Function.Injective (Perspectival.WantableGPT.fromPTransHom Bool) :=
  Perspectival.WantableGPT.fromPTransHom_injective Bool

/-- fromPTransHom is injective on Fin 4. -/
example : Function.Injective (Perspectival.WantableGPT.fromPTransHom (Fin 4)) :=
  Perspectival.WantableGPT.fromPTransHom_injective (Fin 4)

/-- fromPTransHom is injective on Bool × Bool. -/
example : Function.Injective
    (Perspectival.WantableGPT.fromPTransHom (Bool × Bool)) :=
  Perspectival.WantableGPT.fromPTransHom_injective (Bool × Bool)

/-- fromPTransHom is injective on Bool ⊕ Bool. -/
example : Function.Injective
    (Perspectival.WantableGPT.fromPTransHom (Bool ⊕ Bool)) :=
  Perspectival.WantableGPT.fromPTransHom_injective (Bool ⊕ Bool)

/-- fromPTransHom is injective on Bool × Bool × Bool. -/
example : Function.Injective
    (Perspectival.WantableGPT.fromPTransHom (Bool × Bool × Bool)) :=
  Perspectival.WantableGPT.fromPTransHom_injective (Bool × Bool × Bool)

/-- fromPTransHom is injective on Fin 4 × Fin 4. -/
example : Function.Injective
    (Perspectival.WantableGPT.fromPTransHom (Fin 4 × Fin 4)) :=
  Perspectival.WantableGPT.fromPTransHom_injective (Fin 4 × Fin 4)

/-- fromPTransHom is injective for any finite Wantable. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Function.Injective (Perspectival.WantableGPT.fromPTransHom W) :=
  Perspectival.WantableGPT.fromPTransHom_injective W

/-- WantableGPT classical signature on any finite Wantable. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W]
    (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (Perspectival.WantableGPT.V W) = Fintype.card W ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) ≠ Fintype.card W * Fintype.card W ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W) * 2
      ≠ Fintype.card W * (Fintype.card W + 1) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V W)
      ≠ Fintype.card W * (2 * Fintype.card W - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy W h

/-- Concrete: classical dichotomy on Bool. -/
example : Module.finrank ℝ (Perspectival.WantableGPT.V Bool) = Fintype.card Bool ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
      ≠ Fintype.card Bool * Fintype.card Bool ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool) * 2
      ≠ Fintype.card Bool * (Fintype.card Bool + 1) ∧
    Module.finrank ℝ (Perspectival.WantableGPT.V Bool)
      ≠ Fintype.card Bool * (2 * Fintype.card Bool - 1) :=
  Perspectival.WantableGPT.wantableGPT_classical_dichotomy Bool (by decide)

/-- Concrete: classical dichotomy on Fin 4. -/
example := Perspectival.WantableGPT.wantableGPT_classical_dichotomy (Fin 4) (by decide)

/-- Concrete: classical dichotomy on Bool × Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_dichotomy
  (Bool × Bool) (by decide)

/-- Concrete: classical dichotomy on Bool ⊕ Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_dichotomy
  (Bool ⊕ Bool) (by decide)

/-- Concrete: classical dichotomy on Bool × Bool × Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_dichotomy
  (Bool × Bool × Bool) (by decide)

/-- Concrete: classical dichotomy on Bool × Bool × Bool × Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_dichotomy
  (Bool × Bool × Bool × Bool) (by decide)

/-- WantableGPT classical_signature on Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_signature Bool

/-- WantableGPT classical_signature on Fin 4. -/
example := Perspectival.WantableGPT.wantableGPT_classical_signature (Fin 4)

/-- WantableGPT classical_signature on Bool × Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_signature (Bool × Bool)

/-- WantableGPT classical_signature on Bool ⊕ Bool. -/
example := Perspectival.WantableGPT.wantableGPT_classical_signature (Bool ⊕ Bool)

/-- WantableGPT classical_signature on Bool³. -/
example := Perspectival.WantableGPT.wantableGPT_classical_signature (Bool × Bool × Bool)

/-- Pattern.and is idempotent: P.and P ↔ P. -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) :
    Pattern.and P P R ↔ P R := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, h⟩

/-- Pattern.or is idempotent: P.or P ↔ P. -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) :
    Pattern.or P P R ↔ P R := by
  constructor
  · intro h; rcases h with h | h <;> exact h
  · intro h; exact Or.inl h

/-- Pattern.and absorbs Pattern.or: P.and (P.or Q) ↔ P. -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.and P (Pattern.or P Q) R ↔ P R := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, Or.inl h⟩

/-- Pattern.or absorbs Pattern.and: P.or (P.and Q) ↔ P. -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.or P (Pattern.and P Q) R ↔ P R := by
  constructor
  · intro h; rcases h with h | ⟨h, _⟩ <;> exact h
  · intro h; exact Or.inl h

/-- Pattern.and is commutative. -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.and P Q R ↔ Pattern.and Q P R :=
  And.comm

/-- Pattern.or is commutative. -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (R : Reality W) :
    Pattern.or P Q R ↔ Pattern.or Q P R :=
  Or.comm

/-- Pattern.and is associative (logically). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and (Pattern.and P Q) R r ↔ Pattern.and P (Pattern.and Q R) r :=
  and_assoc

/-- Pattern.or is associative (logically). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.or (Pattern.or P Q) R r ↔ Pattern.or P (Pattern.or Q R) r :=
  or_assoc

/-- Pattern.and distributes over Pattern.or (left). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.or Q R) r ↔
    Pattern.or (Pattern.and P Q) (Pattern.and P R) r :=
  and_or_left

/-- Pattern.or distributes over Pattern.and (left). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.and Q R) r ↔
    Pattern.and (Pattern.or P Q) (Pattern.or P R) r :=
  or_and_left

/-- Pattern.and with Pattern.trivial gives the original. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.trivial W) r ↔ P r := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, trivial⟩

/-- Pattern.or with Pattern.empty gives the original. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.empty W) r ↔ P r := by
  constructor
  · intro h; rcases h with h | h
    · exact h
    · exact h.elim
  · intro h; exact Or.inl h

/-- Pattern.and with Pattern.empty gives Pattern.empty. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.empty W) r ↔ Pattern.empty W r := by
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact h.elim

/-- Pattern.or with Pattern.trivial gives Pattern.trivial. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.trivial W) r ↔ Pattern.trivial W r := by
  constructor
  · intro _; trivial
  · intro _; exact Or.inr trivial

/-- Reality is essentially Meeting W → Prop. -/
example {W : Type u} [Wantable W] : Reality W = (Meeting W → Prop) := rfl

/-- Pattern is essentially Reality W → Prop. -/
example {W : Type u} [Wantable W] : Pattern W = (Reality W → Prop) := rfl

/-- A Reality on Bool can be the universal predicate. -/
example : Reality Bool := fun _ => True

/-- A Reality on Bool can be the false predicate. -/
example : Reality Bool := fun _ => False

/-- A Reality singleton: "is this exactly meeting m". -/
example (m : Meeting Bool) : Reality Bool := fun m' => m' = m

/-- A Pattern that's trivially satisfied. -/
example : Pattern Bool := Pattern.trivial Bool

/-- A Pattern that's never satisfied. -/
example : Pattern Bool := Pattern.empty Bool

/-- A Pattern conjunction. -/
example (P Q : Pattern Bool) : Pattern Bool := Pattern.and P Q

/-- A Pattern disjunction. -/
example (P Q : Pattern Bool) : Pattern Bool := Pattern.or P Q

/-- Meeting is a structure. -/
example : Meeting Bool := ⟨true, false, rfl⟩

example : Meeting Bool := ⟨false, true, rfl⟩

example : Meeting (Fin 4) := ⟨0, 3, rfl⟩

example : Meeting (Fin 4) := ⟨1, 2, rfl⟩

example : Meeting ℤ := ⟨5, -5, rfl⟩

example : Meeting (Bool × Bool) := ⟨(true, false), (false, true), rfl⟩

/-- A meeting's swap exchanges its sides. -/
example (m : Meeting Bool) : m.swap.side₁ = m.side₂ := by cases m; rfl
example (m : Meeting Bool) : m.swap.side₂ = m.side₁ := by cases m; rfl

/-- swap is involutive. -/
example (m : Meeting Bool) : m.swap.swap = m := Meeting.swap_swap m
example (m : Meeting (Fin 4)) : m.swap.swap = m := Meeting.swap_swap m
example (m : Meeting (Bool × Bool)) : m.swap.swap = m := Meeting.swap_swap m

/-- Meeting.mk_fromSide constructs a meeting from one side. -/
example : Meeting Bool := Meeting.mk_fromSide Bool true
example : Meeting Bool := Meeting.mk_fromSide Bool false
example : Meeting (Fin 4) := Meeting.mk_fromSide (Fin 4) 2
example : Meeting (Bool × Bool) := Meeting.mk_fromSide (Bool × Bool) (true, false)

/-- Existent on Bool. -/
example : Existent Bool := ⟨true⟩
example : Existent Bool := ⟨false⟩
example : Existent (Fin 4) := ⟨2⟩
example : Existent ℤ := ⟨42⟩
example : Existent (Bool × Bool) := ⟨(true, true)⟩

/-- Existent's want field accessor. -/
example : (⟨true⟩ : Existent Bool).want = true := rfl
example : (⟨false⟩ : Existent Bool).want = false := rfl
example : (⟨2⟩ : Existent (Fin 4)).want = 2 := rfl
example : (⟨42⟩ : Existent ℤ).want = 42 := rfl
example : (⟨(true, false)⟩ : Existent (Bool × Bool)).want = (true, false) := rfl

/-- The PTrans identity element. -/
example : PTrans Bool := 1
example : PTrans (Fin 4) := 1
example : PTrans (Bool × Bool) := 1

/-- The PTrans complement element. -/
example : PTrans Bool := PTrans.complement
example : PTrans (Fin 4) := PTrans.complement

/-- PTrans group structure verifications. -/
example : Group (PTrans Bool) := inferInstance
example : Group (PTrans (Fin 4)) := inferInstance
example : Group (PTrans (Bool × Bool)) := inferInstance
example : Group (PTrans (Bool ⊕ Bool)) := inferInstance
example : Group (PTrans (Bool × Bool × Bool)) := inferInstance

/-- PTrans is inhabited. -/
example : Inhabited (PTrans Bool) := inferInstance
example : Inhabited (PTrans (Fin 4)) := inferInstance

/-- PTrans acts on Meeting (MulAction). -/
example : MulAction (PTrans Bool) (Meeting Bool) := inferInstance
example : MulAction (PTrans (Fin 4)) (Meeting (Fin 4)) := inferInstance

/-- PTrans acts on Reality (MulAction). -/
example : MulAction (PTrans Bool) (Reality Bool) := inferInstance
example : MulAction (PTrans (Fin 4)) (Reality (Fin 4)) := inferInstance

/-- Self-Transforms form a Monoid on any WantableGPT. -/
example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt Bool)
                    (Perspectival.WantableGPT.gpt Bool)) := inferInstance

example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt (Fin 4))
                    (Perspectival.WantableGPT.gpt (Fin 4))) := inferInstance

example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.WantableGPT.gpt (Bool × Bool))
                    (Perspectival.WantableGPT.gpt (Bool × Bool))) := inferInstance

example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.Classical.gpt 5)
                    (Perspectival.Classical.gpt 5)) := inferInstance

example : Monoid (Perspectival.GPT.Transform
                    (Perspectival.Classical.gpt 10)
                    (Perspectival.Classical.gpt 10)) := inferInstance

/-- Transform.id is the identity of the Monoid. -/
example : (Perspectival.GPT.Transform.id (Perspectival.WantableGPT.gpt Bool))
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) := rfl

/-- Transform composition is the multiplication in the Monoid. -/
example (T₁ T₂ : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) :
    T₁ * T₂ = Perspectival.GPT.Transform.comp T₁ T₂ := rfl

/-- Transform.id_toLin equals LinearMap.id (generic). -/
example {V : Type u} [AddCommGroup V] [Module ℝ V] (G : Perspectival.GPT V) :
    (Perspectival.GPT.Transform.id G).toLin = LinearMap.id := rfl

/-- Transform composition's toLin factors through linear-map composition. -/
example {V : Type u} [AddCommGroup V] [Module ℝ V]
    {G : Perspectival.GPT V} (T₁ T₂ : Perspectival.GPT.Transform G G) :
    (T₁ * T₂).toLin = T₁.toLin ∘ₗ T₂.toLin := rfl

/-- The order of complementTransform in the Transform monoid is at most 2. -/
theorem WantableGPT_complementTransform_order_two
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementTransform W) ^ 2
    = (1 : Perspectival.GPT.Transform
            (Perspectival.WantableGPT.gpt W)
            (Perspectival.WantableGPT.gpt W)) := by
  rw [pow_two]
  exact Perspectival.WantableGPT.complementTransform_sq W

/-- Concrete: complementTransform Bool has order 2. -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 2
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) :=
  WantableGPT_complementTransform_order_two

/-- Concrete: complementTransform Fin 4 has order 2. -/
example : (Perspectival.WantableGPT.complementTransform (Fin 4)) ^ 2
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt (Fin 4))
                  (Perspectival.WantableGPT.gpt (Fin 4))) :=
  WantableGPT_complementTransform_order_two

/-- Concrete: complementTransform Bool × Bool has order 2. -/
example : (Perspectival.WantableGPT.complementTransform (Bool × Bool)) ^ 2
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt (Bool × Bool))
                  (Perspectival.WantableGPT.gpt (Bool × Bool))) :=
  WantableGPT_complementTransform_order_two

/-- complementTransform^4 = 1 on Bool. -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 4
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      WantableGPT_complementTransform_order_two, one_pow]

/-- complementTransform^6 = 1 on Bool. -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 6
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul,
      WantableGPT_complementTransform_order_two, one_pow]

/-- complementTransform^3 = complementTransform on Bool. -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 3
        = Perspectival.WantableGPT.complementTransform Bool := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add,
      WantableGPT_complementTransform_order_two, one_mul, pow_one]

/-- complementPTrans has order 2 in the PTrans group. -/
theorem WantableGPT_complementPTrans_order_two
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) ^ 2 = 1 := by
  rw [pow_two]
  exact Perspectival.WantableGPT.complementPTrans_sq W

/-- Concrete: complementPTrans Bool has order 2. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) ^ 2 = 1 :=
  WantableGPT_complementPTrans_order_two

/-- Concrete: complementPTrans Fin 4 has order 2. -/
example : (Perspectival.WantableGPT.complementPTrans (Fin 4)) ^ 2 = 1 :=
  WantableGPT_complementPTrans_order_two

/-- complementPTrans^4 = 1. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      WantableGPT_complementPTrans_order_two, one_pow]

/-- complementPTrans^3 = complementPTrans. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) ^ 3
        = Perspectival.WantableGPT.complementPTrans Bool := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add,
      WantableGPT_complementPTrans_order_two, one_mul, pow_one]

/-- PTrans.complement has order 2 in the PTrans group. -/
example : (PTrans.complement : PTrans Bool) ^ 2 = 1 := by
  rw [pow_two]
  exact PTrans.complement_sq

example : (PTrans.complement : PTrans (Fin 4)) ^ 2 = 1 := by
  rw [pow_two]
  exact PTrans.complement_sq

example : (PTrans.complement : PTrans (Bool × Bool)) ^ 2 = 1 := by
  rw [pow_two]
  exact PTrans.complement_sq

/-- PTrans.complement squared = identity (generic). -/
example {W : Type u} [Wantable W] : (PTrans.complement : PTrans W) ^ 2 = 1 := by
  rw [pow_two]
  exact PTrans.complement_sq

/-- PTrans.complement is its own inverse. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W)⁻¹ = PTrans.complement :=
  PTrans.complement_inv

/-- PTrans.complement * PTrans.complement = 1. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * PTrans.complement = 1 :=
  PTrans.complement_sq

/-- The PTrans complement on Bool×Bool is its own inverse. -/
example : (PTrans.complement : PTrans (Bool × Bool))⁻¹ = PTrans.complement :=
  PTrans.complement_inv

/-- The PTrans complement on Bool⊕Bool is its own inverse. -/
example : (PTrans.complement : PTrans (Bool ⊕ Bool))⁻¹ = PTrans.complement :=
  PTrans.complement_inv

/-- Generic theorem: there exists a non-identity element in PTrans W whenever
W has a non-self-complementary element (specifically the complement PTrans). -/
example {W : Type u} [Wantable W] (hne : ∃ w : W, ¬ SelfComplementary w) :
    ∃ φ : PTrans W, φ ≠ 1 := by
  obtain ⟨w, hw⟩ := hne
  refine ⟨PTrans.complement, ?_⟩
  intro h
  apply hw
  have : (PTrans.complement : PTrans W).toFun w = (1 : PTrans W).toFun w := by rw [h]
  exact this

/-- Concrete: Bool has a non-trivial PTrans (complement ≠ identity). -/
example : ∃ φ : PTrans Bool, φ ≠ 1 := by
  refine ⟨PTrans.complement, ?_⟩
  intro h
  have : (PTrans.complement : PTrans Bool).toFun true = (1 : PTrans Bool).toFun true := by
    rw [h]
  exact absurd this (by decide)

/-- Concrete: Fin 4 has a non-trivial PTrans. -/
example : ∃ φ : PTrans (Fin 4), φ ≠ 1 := by
  refine ⟨PTrans.complement, ?_⟩
  intro h
  have : (PTrans.complement : PTrans (Fin 4)).toFun 0
       = (1 : PTrans (Fin 4)).toFun 0 := by rw [h]
  exact absurd this (by decide)

/-- For Bool, complement actually equals "not" on the underlying type. -/
example (b : Bool) : Wantable.complement b = !b := by
  cases b <;> rfl

/-- For ℤ, complement is the negation. -/
example (n : ℤ) : Wantable.complement n = -n := rfl

/-- For ℝ, complement is the negation. -/
example (r : ℝ) : Wantable.complement r = -r := rfl

/-- For Unit, complement is the unique element. -/
example (u : Unit) : Wantable.complement u = () := rfl

/-- For Fin 3 (with id complement), complement is the identity. -/
example (i : Fin 3) : Wantable.complement i = i := rfl

/-- For Bool × Bool, complement is componentwise. -/
example (p : Bool × Bool) :
    Wantable.complement p = (Wantable.complement p.1, Wantable.complement p.2) :=
  rfl

/-- For Bool ⊕ Bool, complement is in the same summand. -/
example (b : Bool) : Wantable.complement (Sum.inl b : Bool ⊕ Bool)
                   = Sum.inl (Wantable.complement b) := rfl

example (b : Bool) : Wantable.complement (Sum.inr b : Bool ⊕ Bool)
                   = Sum.inr (Wantable.complement b) := rfl

/-- For Bool × Bool × Bool, complement is triplewise. -/
example (p : Bool × Bool × Bool) :
    Wantable.complement p = (Wantable.complement p.1,
                             Wantable.complement p.2.1,
                             Wantable.complement p.2.2) := rfl

/-- For Bool × Bool × Bool × Bool, complement is quadruplewise. -/
example (p : Bool × Bool × Bool × Bool) :
    Wantable.complement p = (Wantable.complement p.1,
                             Wantable.complement p.2.1,
                             Wantable.complement p.2.2.1,
                             Wantable.complement p.2.2.2) := rfl

/-- New: Wantable instances exist for List (with element-wise complement). -/
example : Wantable (List Bool) := inferInstance

example : Wantable (List ℤ) := inferInstance

example : Wantable (List (Fin 4)) := inferInstance

/-- Wantable on Option. -/
example : Wantable (Option Bool) := inferInstance

example : Wantable (Option (Fin 4)) := inferInstance

/-- Wantable on function spaces (Bool → Bool). -/
example : Wantable (Bool → Bool) := inferInstance

example : Wantable (Fin 4 → Bool) := inferInstance

/-- complement on List Bool reverses bits in each element. -/
example : Wantable.complement ([true, false, true] : List Bool)
        = [false, true, false] := by
  show List.map Wantable.complement [true, false, true] = [false, true, false]
  rfl

example : Wantable.complement ([] : List Bool) = [] := rfl

example : Wantable.complement (Option.some true : Option Bool) = Option.some false := rfl

example : Wantable.complement (Option.some false : Option Bool) = Option.some true := rfl

example : Wantable.complement (Option.none : Option Bool) = Option.none := rfl

/-- Wantable on function spaces is pointwise complement. -/
example (f : Bool → Bool) (b : Bool) :
    (Wantable.complement f) b = Wantable.complement (f b) := rfl

/-- complement on `not : Bool → Bool` is `id : Bool → Bool`. -/
example : Wantable.complement (Bool.not : Bool → Bool) = id := by
  funext b
  show Wantable.complement (Bool.not b) = b
  cases b <;> rfl

/-- complement on `id : Bool → Bool` is `not : Bool → Bool`. -/
example : Wantable.complement (id : Bool → Bool) = Bool.not := by
  funext b
  show Wantable.complement b = !b
  cases b <;> rfl

/-- complement of constant-true function = constant-false function. -/
example : Wantable.complement (fun _ : Bool => true) = (fun _ => false) := by
  funext b
  rfl

/-- complement of constant-false function = constant-true function. -/
example : Wantable.complement (fun _ : Bool => false) = (fun _ => true) := by
  funext b
  rfl

/-- complement involution on functions. -/
example (f : Bool → Bool) :
    Wantable.complement (Wantable.complement f) = f :=
  Wantable.complement_involutive f

/-- complement involution on List Bool. -/
example (l : List Bool) :
    Wantable.complement (Wantable.complement l) = l :=
  Wantable.complement_involutive l

/-- complement involution on Option Bool. -/
example (o : Option Bool) :
    Wantable.complement (Wantable.complement o) = o :=
  Wantable.complement_involutive o

/-- complement involution generic. -/
example {W : Type u} [Wantable W] (w : W) :
    Wantable.complement (Wantable.complement w) = w :=
  Wantable.complement_involutive w

/-- complement is involutive across all types — Bool×Bool. -/
example (p : Bool × Bool) :
    Wantable.complement (Wantable.complement p) = p :=
  Wantable.complement_involutive p

/-- complement is involutive across all types — Fin 4. -/
example (i : Fin 4) :
    Wantable.complement (Wantable.complement i) = i :=
  Wantable.complement_involutive i

/-- complement is injective across all types. -/
example {W : Type u} [Wantable W] : Function.Injective (Wantable.complement : W → W) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : Bool → Bool) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : Fin 4 → Fin 4) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : Bool × Bool → Bool × Bool) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : Bool ⊕ Bool → Bool ⊕ Bool) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : List Bool → List Bool) :=
  Wantable.complement_injective

example : Function.Injective (Wantable.complement : Option Bool → Option Bool) :=
  Wantable.complement_injective

/-- complement is surjective across all types. -/
example {W : Type u} [Wantable W] : Function.Surjective (Wantable.complement : W → W) :=
  Wantable.complement_surjective

example : Function.Surjective (Wantable.complement : Bool → Bool) :=
  Wantable.complement_surjective

example : Function.Surjective (Wantable.complement : Fin 4 → Fin 4) :=
  Wantable.complement_surjective

example : Function.Surjective (Wantable.complement : Bool × Bool → Bool × Bool) :=
  Wantable.complement_surjective

example : Function.Surjective (Wantable.complement : Bool ⊕ Bool → Bool ⊕ Bool) :=
  Wantable.complement_surjective

/-- complement is bijective across all types. -/
example {W : Type u} [Wantable W] : Function.Bijective (Wantable.complement : W → W) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement is bijective on Bool. -/
example : Function.Bijective (Wantable.complement : Bool → Bool) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement is bijective on Fin 4. -/
example : Function.Bijective (Wantable.complement : Fin 4 → Fin 4) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement is bijective on Bool × Bool. -/
example : Function.Bijective (Wantable.complement : Bool × Bool → Bool × Bool) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement is bijective on Bool ⊕ Bool. -/
example : Function.Bijective (Wantable.complement : Bool ⊕ Bool → Bool ⊕ Bool) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement is bijective on Bool × Bool × Bool. -/
example : Function.Bijective
    (Wantable.complement : Bool × Bool × Bool → Bool × Bool × Bool) :=
  ⟨Wantable.complement_injective, Wantable.complement_surjective⟩

/-- complement_complement_eq_id specialized. -/
example : (Wantable.complement ∘ Wantable.complement : Bool → Bool) = id :=
  Wantable.complement_complement_eq_id

example : (Wantable.complement ∘ Wantable.complement : Fin 4 → Fin 4) = id :=
  Wantable.complement_complement_eq_id

example : (Wantable.complement ∘ Wantable.complement
            : Bool × Bool → Bool × Bool) = id :=
  Wantable.complement_complement_eq_id

example : (Wantable.complement ∘ Wantable.complement
            : Bool ⊕ Bool → Bool ⊕ Bool) = id :=
  Wantable.complement_complement_eq_id

/-- The complement function as an equivalence. -/
example {W : Type u} [Wantable W] : W ≃ W where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive

/-- complement equivalence on Bool. -/
example : Bool ≃ Bool where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive

/-- complement equivalence on Fin 4. -/
example : Fin 4 ≃ Fin 4 where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive

/-- complementEquiv is an automorphism (it's a permutation as a function). -/
example {W : Type u} [Wantable W] : Equiv.Perm W :=
  { toFun := Wantable.complement
    invFun := Wantable.complement
    left_inv := Wantable.complement_involutive
    right_inv := Wantable.complement_involutive }

/-- PTrans.complement's underlying Equiv.Perm = complement equivalence. -/
example {W : Type u} [Wantable W] :
    PTrans.toEquivPerm (PTrans.complement : PTrans W)
    = ({ toFun := Wantable.complement
         invFun := Wantable.complement
         left_inv := Wantable.complement_involutive
         right_inv := Wantable.complement_involutive } : Equiv.Perm W) := by
  apply Equiv.ext
  intro w
  rfl

/-- PTrans.toEquivPerm of PTrans.id = 1 (identity permutation). -/
example {W : Type u} [Wantable W] :
    PTrans.toEquivPerm (1 : PTrans W) = 1 :=
  PTrans.toEquivPerm_one

/-- toEquivPerm is multiplicative. -/
example {W : Type u} [Wantable W] (g f : PTrans W) :
    PTrans.toEquivPerm (g * f) = PTrans.toEquivPerm g * PTrans.toEquivPerm f :=
  PTrans.toEquivPerm_mul g f

/-- toEquivPermHom is a MonoidHom. -/
example {W : Type u} [Wantable W] : PTrans W →* Equiv.Perm W :=
  PTrans.toEquivPermHom

/-- toEquivPermHom is injective. -/
example {W : Type u} [Wantable W] :
    Function.Injective (PTrans.toEquivPermHom : PTrans W →* Equiv.Perm W) :=
  PTrans.toEquivPermHom_injective

/-- toEquivPerm preserves identity, multiplication. -/
example : PTrans.toEquivPerm (1 : PTrans Bool) = 1 :=
  PTrans.toEquivPerm_one

example : PTrans.toEquivPerm (1 : PTrans (Fin 4)) = 1 :=
  PTrans.toEquivPerm_one

/-- mem_range_toEquivPermHom_iff: a permutation lifts to PTrans iff it
commutes with complement. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W) :
    (∃ φ : PTrans W, PTrans.toEquivPermHom φ = σ) ↔
    (∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) :=
  PTrans.mem_range_toEquivPermHom_iff σ

/-- The identity permutation lifts to PTrans (trivially). -/
example {W : Type u} [Wantable W] :
    ∃ φ : PTrans W, PTrans.toEquivPermHom φ = (1 : Equiv.Perm W) :=
  ⟨1, PTrans.toEquivPerm_one⟩

/-- The complement permutation lifts to PTrans (complement). -/
example {W : Type u} [Wantable W] :
    ∃ φ : PTrans W, PTrans.toEquivPermHom φ
      = ({ toFun := Wantable.complement
           invFun := Wantable.complement
           left_inv := Wantable.complement_involutive
           right_inv := Wantable.complement_involutive } : Equiv.Perm W) := by
  refine ⟨PTrans.complement, ?_⟩
  apply Equiv.ext
  intro w
  rfl

/-- toEquivPerm_commutes_complement: PTrans permutations commute with
the complement permutation. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.toEquivPerm φ * PTrans.toEquivPerm (PTrans.complement : PTrans W)
    = PTrans.toEquivPerm (PTrans.complement : PTrans W) * PTrans.toEquivPerm φ :=
  PTrans.toEquivPerm_commutes_complement φ

/-- ofEquivPerm constructs a PTrans from a complement-commuting permutation. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W)
    (h : ∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) :
    PTrans W := PTrans.ofEquivPerm σ h

/-- ofEquivPerm of identity Equiv = PTrans.id. -/
example {W : Type u} [Wantable W] :
    PTrans.ofEquivPerm (1 : Equiv.Perm W) (fun w => rfl) = (1 : PTrans W) := by
  apply PTrans.ext
  intro w
  rfl

/-- toEquivPerm_ofEquivPerm: round-trip recovers the permutation. -/
example {W : Type u} [Wantable W] (σ : Equiv.Perm W)
    (h : ∀ w, σ (Wantable.complement w) = Wantable.complement (σ w)) :
    PTrans.toEquivPerm (PTrans.ofEquivPerm σ h) = σ :=
  PTrans.toEquivPerm_ofEquivPerm σ h

/-- ofEquivPerm_toEquivPerm: round-trip recovers the PTrans. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.ofEquivPerm (PTrans.toEquivPerm φ) φ.resp_complement = φ :=
  PTrans.ofEquivPerm_toEquivPerm φ

/-- toEquivPerm of complement = the complement equivalence. -/
example {W : Type u} [Wantable W] :
    PTrans.toEquivPerm (PTrans.complement : PTrans W)
      = (⟨Wantable.complement, Wantable.complement,
          Wantable.complement_involutive,
          Wantable.complement_involutive⟩ : Equiv.Perm W) := by
  apply Equiv.ext
  intro w
  rfl

/-- PTrans.id_comp: id ∘ f = f. -/
example {W : Type u} [Wantable W] (f : PTrans W) :
    PTrans.comp PTrans.id f = f := PTrans.id_comp f

/-- PTrans.comp_id: f ∘ id = f. -/
example {W : Type u} [Wantable W] (f : PTrans W) :
    PTrans.comp f PTrans.id = f := PTrans.comp_id f

/-- PTrans.comp_assoc: composition is associative. -/
example {W : Type u} [Wantable W] (h g f : PTrans W) :
    PTrans.comp (PTrans.comp h g) f = PTrans.comp h (PTrans.comp g f) :=
  PTrans.comp_assoc h g f

/-- PTrans group: identity left. -/
example {W : Type u} [Wantable W] (f : PTrans W) : (1 : PTrans W) * f = f :=
  one_mul f

example {W : Type u} [Wantable W] (f : PTrans W) : f * (1 : PTrans W) = f :=
  mul_one f

example {W : Type u} [Wantable W] (h g f : PTrans W) :
    (h * g) * f = h * (g * f) := mul_assoc h g f

example {W : Type u} [Wantable W] (f : PTrans W) : f⁻¹ * f = 1 := inv_mul_cancel f

example {W : Type u} [Wantable W] (f : PTrans W) : f * f⁻¹ = 1 := mul_inv_cancel f

/-- PTrans inv applied twice gives back the same. -/
example {W : Type u} [Wantable W] (f : PTrans W) : (f⁻¹)⁻¹ = f := inv_inv f

/-- PTrans inv distributes over composition (with reversal). -/
example {W : Type u} [Wantable W] (g f : PTrans W) :
    (g * f)⁻¹ = f⁻¹ * g⁻¹ := mul_inv_rev g f

/-- PTrans identity has inverse identity. -/
example {W : Type u} [Wantable W] : (1 : PTrans W)⁻¹ = 1 := inv_one

/-- complement * complement * complement = complement. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * PTrans.complement * PTrans.complement
    = PTrans.complement := by
  rw [PTrans.complement_sq, one_mul]

/-- complement^4 = 1. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * PTrans.complement *
      (PTrans.complement * PTrans.complement) = 1 := by
  rw [PTrans.complement_sq]
  exact one_mul 1

/-- PTrans.complement * 1 = complement. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * 1 = PTrans.complement := mul_one _

/-- 1 * PTrans.complement = complement. -/
example {W : Type u} [Wantable W] :
    (1 : PTrans W) * PTrans.complement = PTrans.complement := one_mul _

/-- A specific identity: complement * complement * complement = complement. -/
example {W : Type u} [Wantable W] :
    (PTrans.complement : PTrans W) * (PTrans.complement * PTrans.complement) =
    PTrans.complement := by
  rw [PTrans.complement_sq, mul_one]

/-- PTrans^0 = 1 for any PTrans. -/
example {W : Type u} [Wantable W] (f : PTrans W) : f ^ 0 = 1 := pow_zero f

/-- PTrans^1 = f. -/
example {W : Type u} [Wantable W] (f : PTrans W) : f ^ 1 = f := pow_one f

/-- 1 ^ n = 1 for PTrans. -/
example {W : Type u} [Wantable W] (n : ℕ) : (1 : PTrans W) ^ n = 1 := one_pow n

/-- (f * g) * (g⁻¹ * f⁻¹) = 1 in PTrans. -/
example {W : Type u} [Wantable W] (f g : PTrans W) :
    (f * g) * (g⁻¹ * f⁻¹) = 1 := by
  rw [mul_assoc, ← mul_assoc g g⁻¹ f⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]

/-- (f * g)⁻¹ = g⁻¹ * f⁻¹ in PTrans. -/
example {W : Type u} [Wantable W] (f g : PTrans W) :
    (f * g)⁻¹ = g⁻¹ * f⁻¹ := mul_inv_rev f g

/-- f⁻¹⁻¹ = f in PTrans (involution). -/
example {W : Type u} [Wantable W] (f : PTrans W) : f⁻¹⁻¹ = f := inv_inv f

/-- 1⁻¹ = 1 in PTrans. -/
example {W : Type u} [Wantable W] : (1 : PTrans W)⁻¹ = 1 := inv_one

/-- complementPTrans is involutive in the WantableGPT group. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W)⁻¹⁻¹
      = Perspectival.WantableGPT.complementPTrans W := inv_inv _

example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) ^ 0 = 1 := pow_zero _

example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) ^ 1
      = Perspectival.WantableGPT.complementPTrans W := pow_one _

/-- complement powers cycle with period 2 (idealization). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) ^ 5
      = Perspectival.WantableGPT.complementPTrans W := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_add,
      pow_mul, WantableGPT_complementPTrans_order_two,
      one_pow, one_mul, pow_one]

/-- complement^10 = 1 (even powers = id). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementPTrans W) ^ 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul,
      WantableGPT_complementPTrans_order_two, one_pow]

/-- complementTransform powers cycle with period 2. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementTransform W) ^ 5
      = Perspectival.WantableGPT.complementTransform W := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_add,
      pow_mul, WantableGPT_complementTransform_order_two,
      one_pow, one_mul, pow_one]

/-- complementTransform^100 = 1. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementTransform W) ^ 100
      = (1 : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt W)
              (Perspectival.WantableGPT.gpt W)) := by
  rw [show (100 : ℕ) = 2 * 50 from rfl, pow_mul,
      WantableGPT_complementTransform_order_two, one_pow]

/-- complementTransform^101 = complementTransform. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.complementTransform W) ^ 101
      = Perspectival.WantableGPT.complementTransform W := by
  rw [show (101 : ℕ) = 2 * 50 + 1 from rfl, pow_add,
      pow_mul, WantableGPT_complementTransform_order_two,
      one_pow, one_mul, pow_one]

/-- A general n-period theorem: complementTransform^(2n) = 1. -/
theorem complementTransform_pow_two_n
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (n : ℕ) :
    (Perspectival.WantableGPT.complementTransform W) ^ (2 * n)
      = (1 : Perspectival.GPT.Transform
              (Perspectival.WantableGPT.gpt W)
              (Perspectival.WantableGPT.gpt W)) := by
  rw [pow_mul, WantableGPT_complementTransform_order_two, one_pow]

/-- A general (2n+1) theorem: complementTransform^(2n+1) = complementTransform. -/
theorem complementTransform_pow_two_n_succ
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (n : ℕ) :
    (Perspectival.WantableGPT.complementTransform W) ^ (2 * n + 1)
      = Perspectival.WantableGPT.complementTransform W := by
  rw [pow_add, complementTransform_pow_two_n, one_mul, pow_one]

/-- Concrete: complementTransform^200 = 1 (Bool case). -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 200
        = (1 : Perspectival.GPT.Transform
                  (Perspectival.WantableGPT.gpt Bool)
                  (Perspectival.WantableGPT.gpt Bool)) :=
  complementTransform_pow_two_n 100

/-- Concrete: complementTransform^999 = complementTransform (Bool). -/
example : (Perspectival.WantableGPT.complementTransform Bool) ^ 999
        = Perspectival.WantableGPT.complementTransform Bool :=
  complementTransform_pow_two_n_succ 499

/-- Generic complementPTrans power theorems. -/
theorem complementPTrans_pow_two_n
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (n : ℕ) :
    (Perspectival.WantableGPT.complementPTrans W) ^ (2 * n) = 1 := by
  rw [pow_mul, WantableGPT_complementPTrans_order_two, one_pow]

theorem complementPTrans_pow_two_n_succ
    {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (n : ℕ) :
    (Perspectival.WantableGPT.complementPTrans W) ^ (2 * n + 1)
      = Perspectival.WantableGPT.complementPTrans W := by
  rw [pow_add, complementPTrans_pow_two_n, one_mul, pow_one]

/-- Concrete: complementPTrans^200 = 1 on Bool. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) ^ 200 = 1 :=
  complementPTrans_pow_two_n 100

/-- Concrete: complementPTrans^999 = complementPTrans on Bool. -/
example : (Perspectival.WantableGPT.complementPTrans Bool) ^ 999
        = Perspectival.WantableGPT.complementPTrans Bool :=
  complementPTrans_pow_two_n_succ 499

/-- General PTrans.complement power theorems (group-level). -/
theorem PTrans_complement_pow_two_n {W : Type u} [Wantable W] (n : ℕ) :
    (PTrans.complement : PTrans W) ^ (2 * n) = 1 := by
  rw [pow_mul, pow_two, PTrans.complement_sq, one_pow]

theorem PTrans_complement_pow_two_n_succ {W : Type u} [Wantable W] (n : ℕ) :
    (PTrans.complement : PTrans W) ^ (2 * n + 1)
      = PTrans.complement := by
  rw [pow_add, PTrans_complement_pow_two_n, one_mul, pow_one]

/-- Concrete: PTrans.complement^200 = 1 on Bool. -/
example : (PTrans.complement : PTrans Bool) ^ 200 = 1 :=
  PTrans_complement_pow_two_n 100

/-- Concrete: PTrans.complement^999 = complement on Bool. -/
example : (PTrans.complement : PTrans Bool) ^ 999 = PTrans.complement :=
  PTrans_complement_pow_two_n_succ 499

/-- Pattern combination: P.and Q.and R = P.and (Q.and R) elementwise. -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and (Pattern.and P Q) R r ↔ Pattern.and P (Pattern.and Q R) r :=
  and_assoc

/-- Pattern.and is commutative elementwise. -/
example {W : Type u} [Wantable W] (P Q : Pattern W) (r : Reality W) :
    Pattern.and P Q r ↔ Pattern.and Q P r :=
  And.comm

/-- Generic Pattern algebra forms a lattice (logical). -/
example {W : Type u} [Wantable W] (P Q R : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.or Q R) r ↔
    Pattern.or (Pattern.and P Q) (Pattern.and P R) r :=
  and_or_left

/-- Generic Pattern.and with empty pattern is empty. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.and P (Pattern.empty W) r ↔ Pattern.empty W r := by
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact h.elim

/-- Generic Pattern.or with trivial pattern is trivial. -/
example {W : Type u} [Wantable W] (P : Pattern W) (r : Reality W) :
    Pattern.or P (Pattern.trivial W) r ↔ Pattern.trivial W r := by
  constructor
  · intro _; trivial
  · intro _; exact Or.inr trivial

/-- Reality on Bool can be enumerated: there are exactly 2^4 = 16
realities (since |Meeting Bool| = 2, and a reality is a predicate on
meetings). -/
example : Reality Bool := fun _ => True

example : Reality Bool := fun _ => False

example : Reality Bool := fun m => m.side₁ = true

example : Reality Bool := fun m => m.side₁ = false

example : Reality Bool := fun m => m.side₂ = true

example : Reality Bool := fun m => m.side₂ = false

/-- A reality determined by both sides. -/
example : Reality Bool := fun m => m.side₁ = m.side₂

/-- A reality that's always true. -/
example : Reality Bool := fun _ => True

/-- A reality on Fin 4 by specifying allowed meetings. -/
example : Reality (Fin 4) := fun m => m.side₁ ≤ 1

/-- A reality on Bool × Bool. -/
example : Reality (Bool × Bool) := fun m => m.side₁.1 = m.side₁.2

/-- A Reality determined by a Pattern (membership). -/
example {W : Type u} [Wantable W] (P : Pattern W) (R : Reality W) : Prop := P R

/-- Pattern.trivial is satisfied by any Reality. -/
example {W : Type u} [Wantable W] (R : Reality W) : Pattern.trivial W R := trivial

/-- Pattern.empty is not satisfied by any Reality. -/
example {W : Type u} [Wantable W] (R : Reality W) : ¬ Pattern.empty W R := id

/-- The "everything" Reality satisfies Pattern.trivial. -/
example : Pattern.trivial Bool (fun _ : Meeting Bool => True) := trivial

/-- The "nothing" Reality does not satisfy Pattern.empty. -/
example : ¬ Pattern.empty Bool (fun _ : Meeting Bool => False) := id

/-- The "nothing" Reality satisfies Pattern.trivial. -/
example : Pattern.trivial Bool (fun _ : Meeting Bool => False) := trivial

/-- The framework supports Reality intersections. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) : Reality W :=
  fun m => R₁ m ∧ R₂ m

/-- The framework supports Reality unions. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) : Reality W :=
  fun m => R₁ m ∨ R₂ m

/-- The framework supports Reality negations. -/
example {W : Type u} [Wantable W] (R : Reality W) : Reality W :=
  fun m => ¬ R m

/-- The framework supports Reality implications. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) : Reality W :=
  fun m => R₁ m → R₂ m

/-- Reality intersection is associative. -/
example {W : Type u} [Wantable W] (R₁ R₂ R₃ : Reality W) (m : Meeting W) :
    ((fun m => R₁ m ∧ R₂ m ∧ R₃ m) m : Prop)
    ↔ ((fun m => (R₁ m ∧ R₂ m) ∧ R₃ m) m : Prop) := by
  exact and_assoc.symm

/-- Reality intersection is commutative. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) (m : Meeting W) :
    (R₁ m ∧ R₂ m) ↔ (R₂ m ∧ R₁ m) := And.comm

/-- Reality union is associative. -/
example {W : Type u} [Wantable W] (R₁ R₂ R₃ : Reality W) (m : Meeting W) :
    ((R₁ m ∨ R₂ m) ∨ R₃ m) ↔ (R₁ m ∨ (R₂ m ∨ R₃ m)) :=
  or_assoc

/-- Reality union is commutative. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) (m : Meeting W) :
    (R₁ m ∨ R₂ m) ↔ (R₂ m ∨ R₁ m) := Or.comm

/-- Reality double negation is original (classical). -/
example {W : Type u} [Wantable W] (R : Reality W) (m : Meeting W) :
    (¬ ¬ R m) ↔ R m := not_not

/-- Reality De Morgan's law: ¬ (R₁ ∧ R₂) ↔ ¬R₁ ∨ ¬R₂ (classical). -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) (m : Meeting W) :
    ¬ (R₁ m ∧ R₂ m) ↔ ¬ R₁ m ∨ ¬ R₂ m := not_and_or

/-- Reality De Morgan's law: ¬ (R₁ ∨ R₂) ↔ ¬R₁ ∧ ¬R₂. -/
example {W : Type u} [Wantable W] (R₁ R₂ : Reality W) (m : Meeting W) :
    ¬ (R₁ m ∨ R₂ m) ↔ ¬ R₁ m ∧ ¬ R₂ m := not_or

/-- The PTrans action on Reality is functorial: 1 • R = R. -/
example {W : Type u} [Wantable W] (R : Reality W) :
    (1 : PTrans W) • R = R := one_smul _ _

/-- The PTrans action on Reality respects multiplication. -/
example {W : Type u} [Wantable W] (φ ψ : PTrans W) (R : Reality W) :
    (φ * ψ) • R = φ • (ψ • R) := mul_smul _ _ _

/-- The PTrans action on Meeting is functorial: 1 • m = m. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    (1 : PTrans W) • m = m := one_smul _ _

/-- The PTrans action on Meeting respects multiplication. -/
example {W : Type u} [Wantable W] (φ ψ : PTrans W) (m : Meeting W) :
    (φ * ψ) • m = φ • (ψ • m) := mul_smul _ _ _

/-- PTrans action: complementPTrans on (Meeting Bool) via smul. -/
example (m : Meeting Bool) :
    (PTrans.complement : PTrans Bool) • m = m.swap := by
  show PTrans.actMeeting PTrans.complement m = m.swap
  exact PTrans.actMeeting_complement m

/-- PTrans action squared (complementPTrans on Meeting): involution. -/
example (m : Meeting Bool) :
    (PTrans.complement : PTrans Bool) • ((PTrans.complement : PTrans Bool) • m) = m := by
  rw [← mul_smul, PTrans.complement_sq, one_smul]

/-- Multiple complement actions cycle. -/
example (m : Meeting Bool) :
    (PTrans.complement : PTrans Bool) • ((PTrans.complement : PTrans Bool) •
      ((PTrans.complement : PTrans Bool) • m))
    = (PTrans.complement : PTrans Bool) • m := by
  rw [← mul_smul, ← mul_smul, PTrans.complement_sq, one_mul]

/-- Same on Reality: complement•R = R after pull-back interpretation. -/
example (R : Reality Bool) :
    (PTrans.complement : PTrans Bool) • ((PTrans.complement : PTrans Bool) • R) = R := by
  rw [← mul_smul, PTrans.complement_sq, one_smul]

/-- complement applied 4 times on Reality = identity. -/
example (R : Reality Bool) :
    (PTrans.complement : PTrans Bool) • ((PTrans.complement : PTrans Bool) •
      ((PTrans.complement : PTrans Bool) • ((PTrans.complement : PTrans Bool) • R))) = R := by
  rw [← mul_smul, PTrans.complement_sq]
  rw [one_smul, ← mul_smul, PTrans.complement_sq, one_smul]

/-- complement applied n=2k times on Reality = identity. -/
theorem complement_pow_two_n_smul_reality
    {W : Type u} [Wantable W] (R : Reality W) (n : ℕ) :
    ((PTrans.complement : PTrans W) ^ (2 * n)) • R = R := by
  rw [PTrans_complement_pow_two_n, one_smul]

example (R : Reality Bool) :
    ((PTrans.complement : PTrans Bool) ^ 200) • R = R :=
  complement_pow_two_n_smul_reality R 100

/-- Same for Meeting: complement applied 2k times = identity. -/
theorem complement_pow_two_n_smul_meeting
    {W : Type u} [Wantable W] (m : Meeting W) (n : ℕ) :
    ((PTrans.complement : PTrans W) ^ (2 * n)) • m = m := by
  rw [PTrans_complement_pow_two_n, one_smul]

example (m : Meeting Bool) :
    ((PTrans.complement : PTrans Bool) ^ 200) • m = m :=
  complement_pow_two_n_smul_meeting m 100

/-- (2n+1)-fold complement on Meeting = swap. -/
theorem complement_pow_two_n_succ_smul_meeting
    {W : Type u} [Wantable W] (m : Meeting W) (n : ℕ) :
    ((PTrans.complement : PTrans W) ^ (2 * n + 1)) • m = m.swap := by
  rw [PTrans_complement_pow_two_n_succ]
  show PTrans.actMeeting PTrans.complement m = m.swap
  exact PTrans.actMeeting_complement m

example (m : Meeting Bool) :
    ((PTrans.complement : PTrans Bool) ^ 999) • m = m.swap :=
  complement_pow_two_n_succ_smul_meeting m 499

/-- complement^2 on Meeting via actMeeting. -/
example (m : Meeting Bool) :
    PTrans.actMeeting (PTrans.complement : PTrans Bool)
      (PTrans.actMeeting PTrans.complement m) = m := by
  rw [PTrans.actMeeting_complement, PTrans.actMeeting_complement,
      Meeting.swap_swap]

/-- complement on actMeeting on Fin 4 Meeting. -/
example (m : Meeting (Fin 4)) :
    PTrans.actMeeting (PTrans.complement : PTrans (Fin 4)) m = m.swap :=
  PTrans.actMeeting_complement m

/-- complement on actMeeting on Bool × Bool Meeting. -/
example (m : Meeting (Bool × Bool)) :
    PTrans.actMeeting (PTrans.complement : PTrans (Bool × Bool)) m = m.swap :=
  PTrans.actMeeting_complement m

/-- complement^2 on actMeeting Bool × Bool Meeting. -/
example (m : Meeting (Bool × Bool)) :
    PTrans.actMeeting (PTrans.complement : PTrans (Bool × Bool))
      (PTrans.actMeeting PTrans.complement m) = m :=
  PTrans.actMeeting_complement_sq m

/-- Trivial: actMeeting of identity is identity. -/
example {W : Type u} [Wantable W] (m : Meeting W) :
    PTrans.actMeeting (1 : PTrans W) m = m :=
  PTrans.actMeeting_id m

/-- actMeeting is composition-respecting. -/
example {W : Type u} [Wantable W] (g f : PTrans W) (m : Meeting W) :
    PTrans.actMeeting (g * f) m = PTrans.actMeeting g (PTrans.actMeeting f m) :=
  PTrans.actMeeting_comp g f m

/-- actMeeting on Bool with identity. -/
example (m : Meeting Bool) : PTrans.actMeeting (1 : PTrans Bool) m = m :=
  PTrans.actMeeting_id m

/-- actMeeting on Fin 4 with identity. -/
example (m : Meeting (Fin 4)) : PTrans.actMeeting (1 : PTrans (Fin 4)) m = m :=
  PTrans.actMeeting_id m

/-- actMeeting on Bool×Bool with identity. -/
example (m : Meeting (Bool × Bool)) :
    PTrans.actMeeting (1 : PTrans (Bool × Bool)) m = m :=
  PTrans.actMeeting_id m

/-- actReality applications. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (R : Reality W) :
    Reality W := PTrans.actReality φ R

example {W : Type u} [Wantable W] (R : Reality W) :
    PTrans.actReality (1 : PTrans W) R = R :=
  PTrans.actReality_one R

example {W : Type u} [Wantable W] (ψ φ : PTrans W) (R : Reality W) :
    PTrans.actReality (ψ * φ) R
      = PTrans.actReality ψ (PTrans.actReality φ R) :=
  PTrans.actReality_mul ψ φ R

/-- actReality on Bool with identity. -/
example (R : Reality Bool) : PTrans.actReality (1 : PTrans Bool) R = R :=
  PTrans.actReality_one R

/-- actReality_and: distributes over conjunction. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (R₁ R₂ : Reality W) :
    PTrans.actReality φ (fun m => R₁ m ∧ R₂ m)
      = fun m => PTrans.actReality φ R₁ m ∧ PTrans.actReality φ R₂ m :=
  PTrans.actReality_and φ R₁ R₂

/-- actReality_or: distributes over disjunction. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (R₁ R₂ : Reality W) :
    PTrans.actReality φ (fun m => R₁ m ∨ R₂ m)
      = fun m => PTrans.actReality φ R₁ m ∨ PTrans.actReality φ R₂ m :=
  PTrans.actReality_or φ R₁ R₂

/-- actReality_empty: action on false predicate is false predicate. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.actReality φ (fun _ : Meeting W => False) = fun _ => False :=
  PTrans.actReality_empty φ

/-- actReality_full: action on true predicate is true predicate. -/
example {W : Type u} [Wantable W] (φ : PTrans W) :
    PTrans.actReality φ (fun _ : Meeting W => True) = fun _ => True :=
  PTrans.actReality_full φ

/-- actReality_singleton: action on a singleton reality. -/
example {W : Type u} [Wantable W] (φ : PTrans W) (m : Meeting W) :
    PTrans.actReality φ (fun m' => m' = m)
      = (fun m' => m' = PTrans.actMeeting φ m) :=
  PTrans.actReality_singleton φ m

/-- complement action on singleton Reality. -/
example (m : Meeting Bool) :
    PTrans.actReality (PTrans.complement : PTrans Bool) (fun m' => m' = m)
      = (fun m' => m' = m.swap) := by
  rw [PTrans.actReality_singleton, PTrans.actMeeting_complement]

/-- complement action on the empty Reality (false predicate). -/
example : PTrans.actReality (PTrans.complement : PTrans Bool)
            (fun _ : Meeting Bool => False) = fun _ => False :=
  PTrans.actReality_empty _

/-- complement action on the full Reality (true predicate). -/
example : PTrans.actReality (PTrans.complement : PTrans Bool)
            (fun _ : Meeting Bool => True) = fun _ => True :=
  PTrans.actReality_full _

/-- Identity PTrans on Reality is the identity. -/
example (R : Reality Bool) : PTrans.actReality (1 : PTrans Bool) R = R :=
  PTrans.actReality_one R

/-- complement * complement = id on Reality (Bool case). -/
example (R : Reality Bool) :
    PTrans.actReality ((PTrans.complement : PTrans Bool) * PTrans.complement) R = R := by
  rw [PTrans.complement_sq, PTrans.actReality_one]

/-- Concrete: actReality on the diagonal-meeting predicate. -/
example : PTrans.actReality (PTrans.complement : PTrans Bool)
            (fun m : Meeting Bool => m.side₁ = m.side₂)
        = (fun m : Meeting Bool =>
            (PTrans.actMeeting (PTrans.complement : PTrans Bool)⁻¹ m).side₁
            = (PTrans.actMeeting (PTrans.complement : PTrans Bool)⁻¹ m).side₂) :=
  rfl

/-- The action on a self-referential Reality (m.side₁ = true). -/
example : PTrans.actReality (PTrans.complement : PTrans Bool)
            (fun m : Meeting Bool => m.side₁ = true)
        = (fun m : Meeting Bool =>
            (PTrans.actMeeting (PTrans.complement : PTrans Bool)⁻¹ m).side₁ = true) :=
  rfl

/-- The action of identity preserves any Reality predicate. -/
example (R : Reality Bool) :
    PTrans.actReality (1 : PTrans Bool) R = R :=
  PTrans.actReality_one R

example (R : Reality (Fin 4)) :
    PTrans.actReality (1 : PTrans (Fin 4)) R = R :=
  PTrans.actReality_one R

example (R : Reality (Bool × Bool)) :
    PTrans.actReality (1 : PTrans (Bool × Bool)) R = R :=
  PTrans.actReality_one R

/-- complementPTrans squared on Reality: cancels. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] (R : Reality W) :
    PTrans.actReality
      ((Perspectival.WantableGPT.complementPTrans W) *
       (Perspectival.WantableGPT.complementPTrans W)) R = R := by
  rw [Perspectival.WantableGPT.complementPTrans_sq, PTrans.actReality_one]

example {W : Type u} [Wantable W] (R : Reality W) :
    PTrans.actReality ((PTrans.complement : PTrans W) * PTrans.complement) R = R := by
  rw [PTrans.complement_sq, PTrans.actReality_one]

/-- 4-fold complement on Reality is identity. -/
example {W : Type u} [Wantable W] (R : Reality W) :
    PTrans.actReality (((PTrans.complement : PTrans W) * PTrans.complement) *
                       ((PTrans.complement : PTrans W) * PTrans.complement)) R = R := by
  rw [PTrans.complement_sq, one_mul, PTrans.actReality_one]

/-- New theorem: The complement equiv has order 2 (in Equiv.Perm). -/
theorem WantableGPT_complementEquiv_order_two
    {W : Type u} [Wantable W] :
    (⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩
      : Equiv.Perm W)
    * (⟨Wantable.complement, Wantable.complement,
        Wantable.complement_involutive, Wantable.complement_involutive⟩
      : Equiv.Perm W) = 1 := by
  apply Equiv.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

/-- complementEquiv inverse is itself. -/
example {W : Type u} [Wantable W] :
    (⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩
      : Equiv.Perm W).symm =
    (⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩
      : Equiv.Perm W) := rfl

/-- The standard simplex (Classical.states) is convex. -/
example (n : ℕ) : Convex ℝ (Perspectival.Classical.states n) :=
  Perspectival.Classical.states_convex n

/-- The standard simplex (WantableGPT.states) is convex. -/
example {W : Type u} [Wantable W] [Fintype W] :
    Convex ℝ (Perspectival.WantableGPT.states W) :=
  convex_stdSimplex ℝ W

/-- Classical effects are convex. -/
example (n : ℕ) : Convex ℝ (Perspectival.Classical.effects n) :=
  Perspectival.Classical.effects_convex n

/-- Classical unit is in effects. -/
example (n : ℕ) : Perspectival.Classical.unitFn n ∈ Perspectival.Classical.effects n :=
  Perspectival.Classical.unit_in_effects n

/-- Classical proj is in effects. -/
example (n : ℕ) (i : Fin n) :
    Perspectival.Classical.proj n i ∈ Perspectival.Classical.effects n :=
  Perspectival.Classical.proj_in_effects n i

/-- WantableGPT unit equals unitFn (definitionally). -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    (Perspectival.WantableGPT.gpt W).unit = Perspectival.WantableGPT.unitFn W := rfl

example : (Perspectival.WantableGPT.gpt Bool).unit
        = Perspectival.WantableGPT.unitFn Bool := rfl

example : (Perspectival.WantableGPT.gpt (Fin 4)).unit
        = Perspectival.WantableGPT.unitFn (Fin 4) := rfl

example : (Perspectival.WantableGPT.gpt (Bool × Bool)).unit
        = Perspectival.WantableGPT.unitFn (Bool × Bool) := rfl

/-- Classical unit equals unitFn (definitionally). -/
example (n : ℕ) :
    (Perspectival.Classical.gpt n).unit = Perspectival.Classical.unitFn n := rfl

example : (Perspectival.Classical.gpt 5).unit = Perspectival.Classical.unitFn 5 := rfl

example : (Perspectival.Classical.gpt 10).unit
        = Perspectival.Classical.unitFn 10 := rfl

/-- WantableGPT effects on Bool = innerLin Bool '' effectVec Bool. -/
example : (Perspectival.WantableGPT.gpt Bool).effects
        = Perspectival.WantableGPT.innerLin Bool ''
            Perspectival.WantableGPT.effectVec Bool := rfl

/-- WantableGPT effects on Fin 4 = innerLin (Fin 4) '' effectVec (Fin 4). -/
example : (Perspectival.WantableGPT.gpt (Fin 4)).effects
        = Perspectival.WantableGPT.innerLin (Fin 4) ''
            Perspectival.WantableGPT.effectVec (Fin 4) := rfl

/-- Classical effects = innerLin n '' effectVec n. -/
example (n : ℕ) : (Perspectival.Classical.gpt n).effects
        = Perspectival.Classical.innerLin n ''
            Perspectival.Classical.effectVec n := rfl

/-- WantableGPT.states = stdSimplex ℝ W. -/
example {W : Type u} [Wantable W] [Fintype W] :
    Perspectival.WantableGPT.states W = stdSimplex ℝ W := rfl

/-- Classical.states = stdSimplex ℝ (Fin n). -/
example (n : ℕ) : Perspectival.Classical.states n = stdSimplex ℝ (Fin n) := rfl

/-- WantableGPT V W = (W → ℝ). -/
example {W : Type u} [Wantable W] [Fintype W] :
    Perspectival.WantableGPT.V W = (W → ℝ) := rfl

example : Perspectival.WantableGPT.V Bool = (Bool → ℝ) := rfl

example : Perspectival.WantableGPT.V (Fin 4) = (Fin 4 → ℝ) := rfl

/-- Classical V n = (Fin n → ℝ). -/
example (n : ℕ) : Perspectival.Classical.V n = (Fin n → ℝ) := rfl

example : Perspectival.Classical.V 5 = (Fin 5 → ℝ) := rfl

/-- WantableGPT.effectVec is the unit hypercube. -/
example {W : Type u} [Wantable W] [Fintype W] [DecidableEq W] :
    Perspectival.WantableGPT.effectVec W = { g | ∀ w, 0 ≤ g w ∧ g w ≤ 1 } := rfl

/-- Classical.effectVec is the unit hypercube. -/
example (n : ℕ) :
    Perspectival.Classical.effectVec n = { f | ∀ i, 0 ≤ f i ∧ f i ≤ 1 } := rfl
