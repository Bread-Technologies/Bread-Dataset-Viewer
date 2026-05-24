/-
Perspectival Physics — Wantable → GPT (partial bridge)
========================================================

The framework's central technical claim is that operational
probabilistic structure (`GPT`) *emerges* from the metaphysical
perspective-wanting structure (`Wantable`). The full bridge is open;
this module provides a *partial* construction.

Given a *finite* Wantable `W`, we construct:
  - `V W := W → ℝ` (functions on outcomes).
  - The "WantableGPT" with states = probability distributions on `W`
    (states are convex; this is just the standard simplex on `W`).
  - The complement involution on `W` induces a linear involution on
    `V W` that *preserves* the state space.

This is a real connection: the complement structure on `W` *acts* on
the GPT's state space. It does NOT yet show the GPT structure *emerges*
from `W` alone — the convex/normalized states are imposed, not derived.

Status:
  ✓ The Wantable-complement action on `V W` is a well-defined linear
    involution.
  ✓ It preserves the state space (since complement is a bijection on W).
  ▲ Whether this gives the "right" GPT in a framework-distinctive
    sense is open. The construction is one of many possible bridges.

Honest qualification: this is the *thinnest* possible connection, not
a derivation. It shows the metaphysical level can *act* on the
operational level but does not show one produces the other.
-/

import Perspectival.Ontology
import Perspectival.Transformations
import Perspectival.GPT
import Perspectival.Hardy
import Perspectival.Distinguish
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Real.Basic

namespace Perspectival
namespace WantableGPT

variable (W : Type u) [Wantable W] [Fintype W]
-- DecidableEq W is needed only for `effects` and `gpt`; specific
-- theorems may not require it. We bring it in locally where needed.

/-- The carrier vector space of the Wantable-induced GPT. -/
abbrev V := W → ℝ

/-- The complement action on `V W`: pull back by `Wantable.complement`. -/
def complementAction : V W →ₗ[ℝ] V W where
  toFun f := fun w => f (Wantable.complement w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complement action is an involution. -/
theorem complementAction_involutive (f : V W) :
    complementAction W (complementAction W f) = f := by
  funext w
  show f (Wantable.complement (Wantable.complement w)) = f w
  rw [Wantable.complement_involutive]

/-- The states (probability distributions on `W`). -/
def states : Set (V W) := stdSimplex ℝ W

/-- Complement action sends states to states (it permutes outcome
probabilities). -/
theorem complementAction_preserves_states (f : V W) (hf : f ∈ states W) :
    complementAction W f ∈ states W := by
  refine ⟨?_, ?_⟩
  · intro w
    show 0 ≤ f (Wantable.complement w)
    exact hf.1 _
  · -- ∑ w, f (complement w) = ∑ w, f w = 1
    show ∑ w, f (Wantable.complement w) = 1
    rw [← hf.2]
    -- Reindex via the complement involution
    refine Equiv.sum_comp ⟨Wantable.complement, Wantable.complement,
        Wantable.complement_involutive, Wantable.complement_involutive⟩ f

/-- The Wantable-induced GPT: states are probability distributions on W,
effects are bounded inner-product functionals with the standard basis. -/
def unitFn : V W →ₗ[ℝ] ℝ where
  toFun f := ∑ w, f w
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- Inner-product functional: a coefficient vector `g` defines
`f ↦ ∑ w, g w * f w`. -/
def innerLin (g : V W) : V W →ₗ[ℝ] ℝ where
  toFun f := ∑ w, g w * f w
  map_add' f₁ f₂ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

/-- Coefficient vectors representing valid effects: components in [0,1]. -/
def effectVec : Set (V W) := { g | ∀ w, 0 ≤ g w ∧ g w ≤ 1 }

/-- The effects of the WantableGPT: inner-product functionals with
coefficient vectors in [0,1]^W. -/
def effects : Set (V W →ₗ[ℝ] ℝ) := innerLin W '' effectVec W

/-- The Wantable-induced GPT. (Mirrors `Classical.gpt` but with the
ambient outcome set being a Wantable rather than `Fin n`. The
complement structure acts on the state space via
`complementAction`.) -/
def gpt : Perspectival.GPT (V W) where
  unit := unitFn W
  states := states W
  effects := effects W
  states_convex := convex_stdSimplex ℝ W
  effects_convex := by
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩ a b ha hb hab
    refine ⟨a • g₁ + b • g₂, ?_, ?_⟩
    · intro w
      refine ⟨?_, ?_⟩
      · have := add_nonneg (mul_nonneg ha (hg₁ w).1) (mul_nonneg hb (hg₂ w).1)
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
      · have h1 : a * g₁ w ≤ a * 1 := mul_le_mul_of_nonneg_left (hg₁ w).2 ha
        have h2 : b * g₂ w ≤ b * 1 := mul_le_mul_of_nonneg_left (hg₂ w).2 hb
        have : a * g₁ w + b * g₂ w ≤ a + b := by linarith
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hab] using this.trans hab.le
    · apply LinearMap.ext
      intro f
      show ∑ w, (a • g₁ + b • g₂) w * f w = a * (∑ w, g₁ w * f w) + b * (∑ w, g₂ w * f w)
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
            Finset.mul_sum, mul_assoc]
  states_normalized := fun _ hρ => hρ.2
  prob_in_unit_interval := by
    rintro _ ⟨g, hg, rfl⟩ ρ ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∑ w, g w * ρ w
      exact Finset.sum_nonneg fun w _ => mul_nonneg (hg w).1 (hpos w)
    · show ∑ w, g w * ρ w ≤ 1
      calc ∑ w, g w * ρ w
          ≤ ∑ w, 1 * ρ w := Finset.sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_right (hg w).2 (hpos w)
        _ = ∑ w, ρ w := by simp
        _ = 1 := hsum
  unit_is_effect := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro w; exact ⟨zero_le_one, le_refl _⟩
    · apply LinearMap.ext
      intro f
      show (innerLin W fun _ => 1) f = (unitFn W) f
      show ∑ w, 1 * f w = ∑ w, f w
      simp

/-- The unit functional is preserved by the complement action. -/
theorem unitFn_complementAction (f : V W) :
    unitFn W (complementAction W f) = unitFn W f := by
  show ∑ w, f (Wantable.complement w) = ∑ w, f w
  exact Equiv.sum_comp ⟨Wantable.complement, Wantable.complement,
      Wantable.complement_involutive, Wantable.complement_involutive⟩ f

/-- The Wantable-complement action is a structure-preserving GPT
transformation: a Transform from `gpt W` to itself. -/
def complementTransform : Perspectival.GPT.Transform (gpt W) (gpt W) where
  toLin := complementAction W
  preserves_states := complementAction_preserves_states W
  preserves_unit := by
    apply LinearMap.ext
    intro f
    show unitFn W (complementAction W f) = unitFn W f
    exact unitFn_complementAction W f

/-! ## Bridge: every PTrans induces a GPT automorphism -/

/-- The action of a perspectival transformation `φ : PTrans W` on the
state space `V W`, by pullback: `(φ · f)(w) := f(φ⁻¹ w)`. -/
def transformAction (φ : PTrans W) : V W →ₗ[ℝ] V W where
  toFun f := fun w => f (φ.invFun w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The transform-action of `φ` preserves the state space (permutes
outcome probabilities, sum unchanged). -/
theorem transformAction_preserves_states (φ : PTrans W) (f : V W)
    (hf : f ∈ states W) : transformAction W φ f ∈ states W := by
  refine ⟨?_, ?_⟩
  · intro w
    show 0 ≤ f (φ.invFun w)
    exact hf.1 _
  · show ∑ w, f (φ.invFun w) = 1
    rw [← hf.2]
    exact Equiv.sum_comp ⟨φ.invFun, φ.toFun, φ.right_inv, φ.left_inv⟩ f

/-- The transform-action preserves the unit functional. -/
theorem unitFn_transformAction (φ : PTrans W) (f : V W) :
    unitFn W (transformAction W φ f) = unitFn W f := by
  show ∑ w, f (φ.invFun w) = ∑ w, f w
  exact Equiv.sum_comp ⟨φ.invFun, φ.toFun, φ.right_inv, φ.left_inv⟩ f

/-- **Every `PTrans W` induces a structure-preserving GPT
automorphism on `gpt W`.**

This is a concrete realization of Axiom IV's "perspectival
transformations cohere across the structure": the metaphysical group
of perspectival transformations *is* a group of operational
GPT-transformations. -/
def fromPTrans (φ : PTrans W) : Perspectival.GPT.Transform (gpt W) (gpt W) where
  toLin := transformAction W φ
  preserves_states := transformAction_preserves_states W φ
  preserves_unit := by
    apply LinearMap.ext
    intro f
    show unitFn W (transformAction W φ f) = unitFn W f
    exact unitFn_transformAction W φ f

/-- `fromPTrans` sends the identity perspectival transformation to
the identity GPT-transformation (at the level of underlying linear
maps). -/
theorem fromPTrans_one_toLin :
    (fromPTrans W (1 : PTrans W)).toLin = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext w
  show f ((1 : PTrans W).invFun w) = f w
  rfl

/-- `fromPTrans` is multiplicative: composing two perspectival
transformations and then sending to GPT-transformations equals
composing the corresponding GPT-transformations.

(This is the group-homomorphism property `fromPTrans (ψ * φ) = ψ.fromPTrans ∘ φ.fromPTrans`.) -/
theorem fromPTrans_mul_toLin (ψ φ : PTrans W) :
    (fromPTrans W (ψ * φ)).toLin =
      (fromPTrans W ψ).toLin.comp (fromPTrans W φ).toLin := by
  apply LinearMap.ext
  intro f
  funext w
  show f ((ψ * φ).invFun w) = f (φ.invFun (ψ.invFun w))
  -- (ψ * φ).invFun w = φ.invFun (ψ.invFun w) by definition of comp
  rfl

/-- The linear-map underlying `fromPTrans` is a monoid homomorphism
from `PTrans W` to `V W →ₗ[ℝ] V W` (under linear-map composition).

This is the framework's "group of metaphysical transformations maps
into the group of operational transformations" claim, made precise. -/
def fromPTransHom : PTrans W →* (V W →ₗ[ℝ] V W) where
  toFun φ := (fromPTrans W φ).toLin
  map_one' := fromPTrans_one_toLin W
  map_mul' := fromPTrans_mul_toLin W

/-- The full Transform-valued monoid homomorphism: `PTrans W` maps
into the Monoid of GPT-self-transformations of `gpt W`. -/
def fromPTransTransformHom :
    PTrans W →* Perspectival.GPT.Transform (gpt W) (gpt W) where
  toFun := fromPTrans W
  map_one' := Perspectival.GPT.Transform.ext (fromPTrans_one_toLin W)
  map_mul' ψ φ := Perspectival.GPT.Transform.ext (fromPTrans_mul_toLin W ψ φ)

-- Injectivity is proven below, after `vertex` is defined.

/-! ## Vertices: pure states corresponding to each element of `W` -/

variable [DecidableEq W]

/-- The "vertex" state at `w` ∈ W: probability mass 1 at `w`, 0
elsewhere. -/
def vertex (w : W) : V W := fun v => if w = v then 1 else 0

/-- The vertex at `w` is a valid state. -/
theorem vertex_in_states (w : W) : vertex W w ∈ states W := by
  refine ⟨?_, ?_⟩
  · intro v
    show 0 ≤ (if w = v then (1 : ℝ) else 0)
    split <;> simp
  · show ∑ v, (if w = v then (1 : ℝ) else 0) = 1
    rw [Finset.sum_eq_single w (fun v _ hvw => by simp [if_neg hvw.symm])
        (by intro h; exact absurd (Finset.mem_univ w) h)]
    simp

/-- The Wantable-complement action sends `vertex w` to `vertex (complement w)`. -/
theorem complementAction_vertex (w : W) :
    complementAction W (vertex W w) = vertex W (Wantable.complement w) := by
  funext v
  show vertex W w (Wantable.complement v) = vertex W (Wantable.complement w) v
  show (if w = Wantable.complement v then (1 : ℝ) else 0)
       = (if Wantable.complement w = v then (1 : ℝ) else 0)
  by_cases h : w = Wantable.complement v
  · have : Wantable.complement w = v := by
      rw [h, Wantable.complement_involutive]
    simp [h, this]
  · have : Wantable.complement w ≠ v := by
      intro h'
      apply h
      rw [← h', Wantable.complement_involutive]
    simp [h, this]

/-- The coordinate projection at `w`. -/
def proj (w : W) : V W →ₗ[ℝ] ℝ where
  toFun f := f w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem proj_vertex (w v : W) :
    proj W w (vertex W v) = if v = w then (1 : ℝ) else 0 := by
  show (if v = w then (1 : ℝ) else 0) = if v = w then 1 else 0
  rfl

/-- The projection `proj w` is a valid effect (witness: vertex coefficient). -/
theorem proj_in_effects (w : W) : proj W w ∈ effects W := by
  refine ⟨vertex W w, ?_, ?_⟩
  · intro v
    show 0 ≤ (if w = v then (1 : ℝ) else 0) ∧ (if w = v then (1 : ℝ) else 0) ≤ 1
    split <;> simp
  · apply LinearMap.ext
    intro f
    show ∑ v, vertex W w v * f v = f w
    rw [Finset.sum_eq_single w (fun v _ hvw => by
        show vertex W w v * f v = 0
        rw [show vertex W w v = 0 from if_neg hvw.symm]; ring)
        (by intro h; exact absurd (Finset.mem_univ w) h)]
    show vertex W w w * f w = f w
    rw [show vertex W w w = 1 from if_pos rfl]
    ring

/-- Vertices of the WantableGPT are pairwise distinguishable. -/
theorem vertices_distinguishable (w v : W) (hwv : w ≠ v) :
    Perspectival.Hardy.Distinguishable (gpt W) (vertex W w) (vertex W v) := by
  refine ⟨proj W w, proj_in_effects W w, ?_, ?_⟩
  · show proj W w (vertex W w) = 1
    rw [proj_vertex]
    simp
  · show proj W w (vertex W v) = 0
    rw [proj_vertex]
    simp [Ne.symm hwv]

/-- The perfect-witness for vertices: each vertex `v` is picked out
by the projection `proj v`. -/
def perfectWitness : Perspectival.Distinguish.PerfectWitness (G := gpt W) (vertex W) where
  e := proj W
  kronecker i j := by
    show proj W i (vertex W j) = if i = j then (1 : ℝ) else 0
    rw [proj_vertex]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]

/-- The vertex set forms a Hardy-style distinguishability set. -/
theorem vertex_distinguishability_set :
    Perspectival.Hardy.DistinguishabilitySet (gpt W)
      ((Finset.univ : Finset W).image (vertex W)) := by
  constructor
  · intro ρ hρ
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hρ
    exact vertex_in_states W w
  · intro ρ₁ hρ₁ ρ₂ hρ₂ hne
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hρ₁
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hρ₂
    exact vertices_distinguishable W w v (fun h => hne (by rw [h]))

/-- **Vertices of the WantableGPT are linearly independent**, derived
from the perfect-distinguishability witness. -/
theorem vertex_linear_independent_of_fintype [Fintype W] :
    LinearIndependent ℝ (fun w : W => vertex W w) := by
  -- Reindex via an equivalence to Fin (Fintype.card W) and use the
  -- perfect-distinguishability theorem.
  exact LinearIndependent.of_pairwise_dual_eq_zero_one (vertex W) (proj W)
    (fun {i j} hij => by
      show proj W i (vertex W j) = 0
      rw [proj_vertex]; simp [Ne.symm hij])
    (fun i => by
      show proj W i (vertex W i) = 1
      rw [proj_vertex]; simp)

/-- `fromPTransHom` is INJECTIVE: distinct perspectival transformations
give distinct linear maps on the state space.

Proof sketch: from `(fromPTrans φ).toLin = (fromPTrans ψ).toLin`,
evaluate at each `vertex w₀` and at each `w'` to deduce
`φ.invFun w' = ψ.invFun w'`. Since `toFun` is determined by `invFun`
(as its two-sided inverse), `φ = ψ`. -/
theorem fromPTransHom_injective :
    Function.Injective (fromPTransHom W) := by
  intro φ ψ h
  apply PTrans.ext
  intro w
  have h_inv : ∀ w', φ.invFun w' = ψ.invFun w' := by
    intro w'
    have hap := LinearMap.congr_fun h (vertex W (φ.invFun w'))
    have heq : (vertex W (φ.invFun w')) (φ.invFun w') =
               (vertex W (φ.invFun w')) (ψ.invFun w') := by
      have := congr_fun hap w'
      exact this
    rw [show (vertex W (φ.invFun w')) (φ.invFun w') = 1 from by
        show (if φ.invFun w' = φ.invFun w' then (1 : ℝ) else 0) = 1
        simp] at heq
    by_contra hne
    rw [show (vertex W (φ.invFun w')) (ψ.invFun w') = 0 from by
        show (if φ.invFun w' = ψ.invFun w' then (1 : ℝ) else 0) = 0
        simp [hne]] at heq
    exact one_ne_zero heq
  -- Use h_inv: φ.toFun w = x means φ.invFun x = w. Apply h_inv: ψ.invFun x = w. Hence ψ.toFun w = x.
  set x := φ.toFun w with hx
  have hφ : φ.invFun x = w := by rw [hx]; exact φ.left_inv w
  have hψ : ψ.invFun x = w := by rw [← h_inv x]; exact hφ
  have hψtoFun : ψ.toFun w = x := by
    have hr : ψ.toFun (ψ.invFun x) = x := ψ.right_inv x
    rw [hψ] at hr
    exact hr
  rw [hψtoFun]

/-! ## Bridge back: the complement function as PTrans -/

/-- The complement function on `W`, packaged as a PTrans. -/
def complementPTrans : PTrans W where
  toFun := Wantable.complement
  invFun := Wantable.complement
  left_inv := Wantable.complement_involutive
  right_inv := Wantable.complement_involutive
  resp_complement := fun _ => rfl

/-- The complement-action GPT-transformation is the image of the
complement-as-PTrans under `fromPTrans` (at the level of underlying
linear maps). The two routes to "Wantable complement acts on the GPT"
coincide. -/
theorem complementTransform_eq_fromPTrans :
    (complementTransform W).toLin = (fromPTrans W (complementPTrans W)).toLin := by
  apply LinearMap.ext
  intro f
  funext w
  show f (Wantable.complement w) = f ((complementPTrans W).invFun w)
  rfl

/-- The full-Transform version: `complementTransform W = fromPTrans W
(complementPTrans W)` as GPT-transformations. -/
theorem complementTransform_eq_fromPTrans_full :
    complementTransform W = fromPTrans W (complementPTrans W) :=
  Perspectival.GPT.Transform.ext (complementTransform_eq_fromPTrans W)

end WantableGPT
end Perspectival
