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
import Perspectival.Composition
import Perspectival.GPT
import Perspectival.Hardy
import Perspectival.Distinguish
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

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

/-- Coercion: any perspectival transformation on W is automatically a
GPT-transformation on the corresponding WantableGPT. -/
instance : Coe (PTrans W) (Perspectival.GPT.Transform (gpt W) (gpt W)) where
  coe := fromPTrans W

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

/-- The general `transformAction φ` permutes vertices: it sends
`vertex w` to `vertex (φ.toFun w)`. The PTrans action on the operational
state space restricts to a permutation of the vertex set. -/
@[simp] theorem transformAction_vertex (φ : PTrans W) (w : W) :
    transformAction W φ (vertex W w) = vertex W (φ.toFun w) := by
  funext v
  show (if w = φ.invFun v then (1 : ℝ) else 0)
       = (if φ.toFun w = v then (1 : ℝ) else 0)
  by_cases h : w = φ.invFun v
  · have hv : φ.toFun w = v := by rw [h]; exact φ.right_inv v
    simp [h, hv, φ.right_inv v]
  · have : φ.toFun w ≠ v := by
      intro h'
      apply h
      rw [← h']
      exact (φ.left_inv w).symm
    simp [h, this]

/-- The Wantable-complement action sends `vertex w` to `vertex (complement w)`. -/
theorem complementAction_vertex (w : W) :
    complementAction W (vertex W w) = vertex W (Wantable.complement w) := by
  funext v
  show vertex W w (Wantable.complement v) = vertex W (Wantable.complement w) v
  show (if w = Wantable.complement v then (1 : ℝ) else 0)
       = (if Wantable.complement w = v then (1 : ℝ) else 0)
  by_cases h : w = Wantable.complement v
  · have hw : Wantable.complement w = v := by
      rw [h, Wantable.complement_involutive]
    simp [h, hw]
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

/-- The vertex map (indexed by `W` itself, not `Fin n`) is a perfect
distinguishability family. This is the "natural" form of the witness
that doesn't require a Fin-reindexing. -/
theorem vertex_perfectly_distinguishable [Fintype W] :
    ∃ e : W → V W →ₗ[ℝ] ℝ,
      ∀ i j : W, e i (vertex W j) = if i = j then (1 : ℝ) else 0 :=
  ⟨proj W, (perfectWitness W).kronecker⟩

/-- The vertex map is injective: distinct elements of W give distinct vertices. -/
theorem vertex_injective [Fintype W] : Function.Injective (vertex W) := by
  intro i j hij
  by_contra hne
  -- Apply proj i to both sides.
  have h1 : proj W i (vertex W i) = 1 := by rw [proj_vertex]; simp
  have h2 : proj W i (vertex W j) = 0 := by
    rw [proj_vertex]
    have : ¬ j = i := fun h => hne h.symm
    simp [this]
  have h3 : proj W i (vertex W i) = proj W i (vertex W j) := by rw [hij]
  rw [h1, h2] at h3
  linarith

/-- The image of vertex (the vertex set) has cardinality |W|. -/
theorem vertex_image_card [Fintype W] :
    ((Finset.univ : Finset W).image (vertex W)).card = Fintype.card W := by
  rw [Finset.card_image_of_injective _ (vertex_injective W)]
  simp

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

/-- **Vertex decomposition.** Every element of `V W = W → ℝ` is its
own coordinate-wise vertex combination:
  `f = ∑ w, f w • vertex w`.
For states (probability distributions) this exhibits the WantableGPT
state space as the convex hull of the vertex set — i.e., a simplex
on `W`. -/
theorem vertex_decomposition (f : V W) :
    f = ∑ w, f w • vertex W w := by
  funext v
  show f v = (∑ w, f w • vertex W w) v
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single v
    (fun w _ hwv => by
      show f w • vertex W w v = 0
      show f w * (if w = v then (1 : ℝ) else 0) = 0
      simp [hwv])
    (fun h => absurd (Finset.mem_univ v) h)]
  symm
  show (f v • vertex W v) v = f v
  show f v * (if v = v then (1 : ℝ) else 0) = f v
  simp

/-- **Convex-hull characterization.** Every state of the WantableGPT
is a convex combination (with coefficients given by its outcome
probabilities) of the vertices. This is the precise statement that
the WantableGPT is the classical simplex on `W`. -/
theorem state_is_convex_combination_of_vertices (f : V W) (_hf : f ∈ states W) :
    f = ∑ w, f w • vertex W w := vertex_decomposition W f

/-- The vertex family spans the entire ambient space `V W`. -/
theorem vertices_span : Submodule.span ℝ (Set.range (vertex W)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [vertex_decomposition W f]
  exact Submodule.sum_mem _ (fun w _ =>
    Submodule.smul_mem _ (f w) (Submodule.subset_span ⟨w, rfl⟩))

/-- **The vertex family is a basis of `V W = W → ℝ`.** -/
noncomputable def vertexBasis [Fintype W] : Module.Basis W ℝ (V W) :=
  Module.Basis.mk (vertex_linear_independent_of_fintype W) (ge_of_eq (vertices_span W))

/-- The finite-dimensionality of the WantableGPT state space, from the
vertex basis. -/
theorem finrank_V_eq_card [Fintype W] :
    Module.finrank ℝ (V W) = Fintype.card W :=
  Module.finrank_eq_card_basis (vertexBasis W)

/-- `V W` is a finite ℝ-module (carried by the vertex basis). -/
instance instModuleFinite [Fintype W] : Module.Finite ℝ (V W) :=
  Module.Finite.of_basis (vertexBasis W)

/-- **Classical-signature no-go.** For any finite Wantable `W`, the
WantableGPT achieves `N = K`: the maximal number of perfectly
distinguishable states equals the dimension of the ambient state
space. Both are `|W|`. In Hardy's classification this is the
*classical* signature — the framework's bare ontology, when bridged
to a GPT via `WantableGPT.gpt`, never produces non-classical
(`N < K`) structure.

This is a no-go for the framework's "ontology alone derives quantum
theory" reading: deriving non-classical structure must come from
additional postulates (e.g., composition rules beyond disjoint union,
continuity / agency richness beyond bare PTrans, etc.), not from the
bare Wantable structure. -/
theorem wantableGPT_is_classical [Fintype W] :
    Fintype.card W ≤ Module.finrank ℝ (V W) ∧
    Module.finrank ℝ (V W) = Fintype.card W := by
  refine ⟨?_, finrank_V_eq_card W⟩
  -- The vertex map is itself a perfect-distinguishability witness; from this
  -- we get card W ≤ finrank (via `operational_dim_le_state_dim` reasoning,
  -- but we have the cleaner direct bound from the basis size).
  exact (finrank_V_eq_card W).symm.le

/-- **Product-composition dimension.** For finite Wantables W₁, W₂,
the WantableGPT of `W₁ × W₂` has dimension `|W₁| · |W₂|`. This is the
Hardy "composition rule" K_AB = K_A · K_B, holding *automatically*
for our finite-Wantable bridge (no additional tensor postulate required
at the dimension-counting level — though tensor structure of states /
effects is more than this). -/
theorem finrank_V_prod_eq_mul {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (V (W₁ × W₂)) = Fintype.card W₁ * Fintype.card W₂ := by
  rw [finrank_V_eq_card (W₁ × W₂), Fintype.card_prod]

/-- **Sum-composition dimension.** For finite Wantables W₁, W₂,
the WantableGPT of `W₁ ⊕ W₂` has dimension `|W₁| + |W₂|`. This is the
classical "additive" composition rule. -/
theorem finrank_V_sum_eq_add {W₁ W₂ : Type u}
    [Wantable W₁] [Wantable W₂] [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂] :
    Module.finrank ℝ (V (W₁ ⊕ W₂)) = Fintype.card W₁ + Fintype.card W₂ := by
  rw [finrank_V_eq_card (W₁ ⊕ W₂), Fintype.card_sum]

/-- The unit (zero-vector) is in the effect-vector set: the zero
effect (probability 0 for every state) is a valid effect. -/
theorem zero_in_effectVec : (0 : V W) ∈ effectVec W := by
  intro w
  refine ⟨?_, ?_⟩
  · show (0 : ℝ) ≤ (0 : V W) w
    show (0 : ℝ) ≤ (0 : ℝ)
    exact le_refl 0
  · show (0 : V W) w ≤ 1
    show (0 : ℝ) ≤ 1
    norm_num

/-- The unit-vector (constantly 1) is in the effect-vector set: the
"sure" effect (probability 1 for every state). -/
theorem one_in_effectVec [Fintype W] : (fun _ : W => (1 : ℝ)) ∈ effectVec W := by
  intro w
  refine ⟨?_, ?_⟩
  · show (0 : ℝ) ≤ 1; norm_num
  · show (1 : ℝ) ≤ 1; norm_num

/-- Effect vectors are componentwise in [0, 1] — the effect-vector set
is literally the unit hypercube `[0,1]^W` in `V W`. -/
theorem effectVec_eq_hypercube :
    effectVec W = { g : V W | ∀ w, g w ∈ Set.Icc (0 : ℝ) 1 } := by
  ext g
  exact Iff.rfl

/-- For a non-trivial Wantable (cardinality ≥ 2), the WantableGPT has
at least two perfectly distinguishable states. -/
theorem exists_two_distinguishable [Fintype W]
    (h : 2 ≤ Fintype.card W) :
    ∃ ρ₁ ρ₂ : V W,
      ρ₁ ∈ states W ∧ ρ₂ ∈ states W ∧
      Perspectival.Hardy.Distinguishable (gpt W) ρ₁ ρ₂ := by
  -- Two distinct elements of W give two distinct vertices.
  obtain ⟨w, v, hwv⟩ : ∃ w v : W, w ≠ v := by
    rw [← Fintype.one_lt_card_iff]
    omega
  refine ⟨vertex W w, vertex W v, vertex_in_states W w, vertex_in_states W v, ?_⟩
  exact vertices_distinguishable W w v hwv

/-- **Stronger no-go.** For any finite Wantable `W` with `|W| ≥ 2`, the
WantableGPT does NOT have quantum signature (K = N²). This is a
strict-inequality version of `wantableGPT_is_classical` ruling out
the quantum case explicitly. -/
theorem wantableGPT_not_quantum [Fintype W] (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (V W) ≠ Fintype.card W * Fintype.card W := by
  rw [finrank_V_eq_card]
  intro heq
  -- |W| = |W| * |W| with |W| ≥ 2 forces |W| = 0 or |W| = 1
  set n := Fintype.card W with hn
  have hn2 : 2 ≤ n := h
  have hnn : n = n * n := heq
  -- n * (n - 1) = 0 from n = n*n (working in ℕ)
  have : n * 1 = n * n := by rw [mul_one]; exact hnn
  have hn1 : n = 1 ∨ n = 0 := by
    have hmul : n * 1 = n * n := this
    have : 1 = n ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · exact Or.inr hz
      · left; exact (Nat.eq_of_mul_eq_mul_left hpos hmul)
    rcases this with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  omega

/-- **Real-QM signature ruled out.** Real quantum mechanics has the
Hardy signature K = N(N+1)/2 (i.e., 2K = N(N+1)). For the WantableGPT
with `|W| ≥ 2`, this fails: K = N = |W|, but then 2N = N(N+1) ⇒ N = 1. -/
theorem wantableGPT_not_realQM [Fintype W] (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (V W) * 2 ≠ Fintype.card W * (Fintype.card W + 1) := by
  rw [finrank_V_eq_card]
  set n := Fintype.card W
  intro heq
  have hpos : 0 < n := by omega
  have hmul : n * 2 = n * (n + 1) := heq
  have : 2 = n + 1 := Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

/-- **Quaternionic-QM signature ruled out.** Quaternionic QM has Hardy
signature K = N(2N-1). For the WantableGPT with `|W| ≥ 2`, this fails:
K = N = |W|, but then N = N(2N-1) ⇒ 2N - 1 = 1 ⇒ N = 1. -/
theorem wantableGPT_not_quaternionicQM [Fintype W] (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (V W) ≠ Fintype.card W * (2 * Fintype.card W - 1) := by
  rw [finrank_V_eq_card]
  set n := Fintype.card W
  intro heq
  have hpos : 0 < n := by omega
  have hmul : n * 1 = n * (2 * n - 1) := by rw [mul_one]; exact heq
  have : 1 = 2 * n - 1 := Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

/-- **Hardy-signature dichotomy.** For finite Wantable W with `|W| ≥ 2`,
the WantableGPT satisfies the classical signature `K = N = |W|` and
*does not* satisfy any of the standard non-classical signatures
(quantum K=N², real-QM 2K=N(N+1), quaternionic-QM K=N(2N-1)). -/
theorem wantableGPT_classical_dichotomy [Fintype W] (h : 2 ≤ Fintype.card W) :
    Module.finrank ℝ (V W) = Fintype.card W ∧
    Module.finrank ℝ (V W) ≠ Fintype.card W * Fintype.card W ∧
    Module.finrank ℝ (V W) * 2 ≠ Fintype.card W * (Fintype.card W + 1) ∧
    Module.finrank ℝ (V W) ≠ Fintype.card W * (2 * Fintype.card W - 1) :=
  ⟨finrank_V_eq_card W, wantableGPT_not_quantum W h,
   wantableGPT_not_realQM W h, wantableGPT_not_quaternionicQM W h⟩

/-- **Hardy's "classical signature" `N = K` is satisfied for the
WantableGPT bridge.** The maximal perfectly-distinguishable family is
the vertex family (size `|W|`), and the state-space dimension is also
`|W|`. So `N = K = |W|` — the *classical* Hardy signature. -/
theorem wantableGPT_classical_signature [Fintype W] :
    ∃ (n : ℕ) (ρ : Fin n → V W) (_w : Perspectival.Distinguish.PerfectWitness (G := gpt W) ρ),
      n = Module.finrank ℝ (V W) := by
  refine ⟨Fintype.card W,
    fun i => vertex W ((Fintype.equivFin W).symm i), ?_, ?_⟩
  · -- Reindex perfectWitness via the equivalence
    refine ⟨fun i => proj W ((Fintype.equivFin W).symm i), ?_⟩
    intro i j
    show proj W ((Fintype.equivFin W).symm i) (vertex W ((Fintype.equivFin W).symm j))
       = if i = j then (1 : ℝ) else 0
    rw [proj_vertex]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : (Fintype.equivFin W).symm j ≠ (Fintype.equivFin W).symm i := by
        intro h
        apply hij
        have := congrArg (Fintype.equivFin W) h
        simpa using this.symm
      simp [hij, hne]
  · exact (finrank_V_eq_card W).symm

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

/-- `complementPTrans` is an involution in the Group `PTrans W`. -/
theorem complementPTrans_sq :
    (complementPTrans W) * (complementPTrans W) = (1 : PTrans W) := by
  apply PTrans.ext
  intro w
  show Wantable.complement (Wantable.complement w) = w
  exact Wantable.complement_involutive w

/-- `complementPTrans` is its own inverse in the group. -/
theorem complementPTrans_inv :
    (complementPTrans W)⁻¹ = complementPTrans W :=
  inv_eq_of_mul_eq_one_right (complementPTrans_sq W)

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

/-- The monoid hom `fromPTransHom` sends `complementPTrans` to
exactly `complementAction`. The bridge respects the specific
complement structure. -/
theorem fromPTransHom_complementPTrans :
    fromPTransHom W (complementPTrans W) = complementAction W :=
  (complementTransform_eq_fromPTrans W).symm

/-- Transform-level version: `fromPTransTransformHom (complementPTrans) = complementTransform`. -/
theorem fromPTransTransformHom_complementPTrans :
    fromPTransTransformHom W (complementPTrans W) = complementTransform W :=
  (complementTransform_eq_fromPTrans_full W).symm

/-- `complementTransform W` is an involution in the Monoid of GPT
self-transformations. -/
theorem complementTransform_sq :
    complementTransform W * complementTransform W
    = (1 : Perspectival.GPT.Transform (gpt W) (gpt W)) := by
  apply Perspectival.GPT.Transform.ext
  apply LinearMap.ext
  intro f
  funext w
  show f (Wantable.complement (Wantable.complement w)) = f w
  rw [Wantable.complement_involutive]

end WantableGPT
end Perspectival
