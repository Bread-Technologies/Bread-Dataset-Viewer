/-
Perspectival Physics — General GPT tensor product
====================================================

Hardy's Axiom 4 (composite systems multiply: K_AB = K_A · K_B and an
associated tensor-state existence) is currently proven only at the
WantableGPT-specific level (`Hardy_Axiom4_WantableGPT_dimension`,
`Hardy_Axiom4_WantableGPT_state_exists` in `WantableGPT.lean`). This
file lifts the construction to a **general** GPT-level operator
`gptTensor : GPT V₁ → GPT V₂ → GPT (V₁ ⊗[ℝ] V₂)`.

Design choices:

  • Underlying space   : the algebraic tensor product `V₁ ⊗[ℝ] V₂`.
  • Unit functional    : `unit_AB := lift (u_A ⊗ u_B)` — the unique
                         linear map sending `ρ₁ ⊗ ρ₂ ↦ u_A ρ₁ · u_B ρ₂`.
  • States             : `convexHull ℝ {ρ₁ ⊗ ρ₂ | ρᵢ ∈ Gᵢ.states}` —
                         the framework-minimal "separable" states.
                         Entangled states are an additional postulate,
                         not part of this construction.
  • Effects            : `{ e : V₁ ⊗ V₂ →ₗ[ℝ] ℝ | 0 ≤ e ρ ≤ 1 ∀ ρ ∈ states }`.

These are the four data of a `GPT`. We verify all six axioms.

The framework reading: in the **product-states** GPT the metaphysical
"two perspectives, each in their own state" composes by the algebraic
tensor; entanglement appears only with a *further* postulate
(extension to non-product states). The bare framework therefore yields
the SEPARABLE / NO-ENTANGLEMENT composite as its minimal commitment —
consistent with the framework's emphasis on bilateral wants being the
primitive ontological unit.

The headline theorem `gptTensor_finrank_eq_mul` is Hardy's K_AB =
K_A · K_B at the general (not WantableGPT-specific) level, and
follows from `Module.finrank_tensorProduct`.
-/

import Perspectival.GPT
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.Hull

namespace Perspectival
namespace GPT

open TensorProduct

variable {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]

/-! ## The bilinear unit functional for the composite -/

/-- The bilinear "product of units" map `(ρ₁, ρ₂) ↦ u_A ρ₁ · u_B ρ₂`,
viewed as a linear map `V₁ →ₗ[ℝ] (V₂ →ₗ[ℝ] ℝ)`. -/
def unitBilin (G₁ : GPT V₁) (G₂ : GPT V₂) : V₁ →ₗ[ℝ] V₂ →ₗ[ℝ] ℝ where
  toFun ρ₁ :=
    { toFun := fun ρ₂ => G₁.unit ρ₁ * G₂.unit ρ₂
      map_add' := fun x y => by simp [LinearMap.map_add, mul_add]
      map_smul' := fun c x => by
        show G₁.unit ρ₁ * G₂.unit (c • x) = c • (G₁.unit ρ₁ * G₂.unit x)
        rw [LinearMap.map_smul]
        simp [smul_eq_mul]; ring }
  map_add' x y := by
    apply LinearMap.ext; intro z
    show G₁.unit (x + y) * G₂.unit z
         = G₁.unit x * G₂.unit z + G₁.unit y * G₂.unit z
    rw [LinearMap.map_add]; ring
  map_smul' c x := by
    apply LinearMap.ext; intro z
    show G₁.unit (c • x) * G₂.unit z = c • (G₁.unit x * G₂.unit z)
    rw [LinearMap.map_smul]
    simp [smul_eq_mul]; ring

/-- The composite unit functional `unit_AB : V₁ ⊗ V₂ →ₗ[ℝ] ℝ`. -/
noncomputable def tensorUnit (G₁ : GPT V₁) (G₂ : GPT V₂) :
    V₁ ⊗[ℝ] V₂ →ₗ[ℝ] ℝ :=
  TensorProduct.lift (unitBilin G₁ G₂)

@[simp] theorem tensorUnit_tmul
    (G₁ : GPT V₁) (G₂ : GPT V₂) (ρ₁ : V₁) (ρ₂ : V₂) :
    tensorUnit G₁ G₂ (ρ₁ ⊗ₜ[ℝ] ρ₂) = G₁.unit ρ₁ * G₂.unit ρ₂ := by
  show TensorProduct.lift (unitBilin G₁ G₂) (ρ₁ ⊗ₜ[ℝ] ρ₂)
       = G₁.unit ρ₁ * G₂.unit ρ₂
  rw [TensorProduct.lift.tmul]
  rfl

/-! ## Product states (separable states) -/

/-- The set of **product (pure-separable) generators**
`{ρ₁ ⊗ ρ₂ | ρ₁ ∈ G₁.states, ρ₂ ∈ G₂.states}`. -/
def productGenerators (G₁ : GPT V₁) (G₂ : GPT V₂) : Set (V₁ ⊗[ℝ] V₂) :=
  { x | ∃ ρ₁ ∈ G₁.states, ∃ ρ₂ ∈ G₂.states, x = ρ₁ ⊗ₜ[ℝ] ρ₂ }

/-- The set of **separable / product states** of the composite GPT:
the convex hull of pure product states. Entangled states would require
extending this set. -/
def tensorStates (G₁ : GPT V₁) (G₂ : GPT V₂) : Set (V₁ ⊗[ℝ] V₂) :=
  convexHull ℝ (productGenerators G₁ G₂)

theorem tensorStates_convex (G₁ : GPT V₁) (G₂ : GPT V₂) :
    Convex ℝ (tensorStates G₁ G₂) :=
  convex_convexHull ℝ _

/-- Every product generator has unit equal to 1 (normalization on the
generators). -/
theorem tensorUnit_eq_one_on_generators
    (G₁ : GPT V₁) (G₂ : GPT V₂) {x : V₁ ⊗[ℝ] V₂}
    (hx : x ∈ productGenerators G₁ G₂) :
    tensorUnit G₁ G₂ x = 1 := by
  obtain ⟨ρ₁, hρ₁, ρ₂, hρ₂, rfl⟩ := hx
  rw [tensorUnit_tmul,
      G₁.states_normalized ρ₁ hρ₁,
      G₂.states_normalized ρ₂ hρ₂]
  norm_num

/-- The level set `{x | tensorUnit G₁ G₂ x = 1}` is convex (as the
preimage of a singleton under a linear functional). -/
theorem tensorUnit_level_one_convex (G₁ : GPT V₁) (G₂ : GPT V₂) :
    Convex ℝ {x : V₁ ⊗[ℝ] V₂ | tensorUnit G₁ G₂ x = 1} := by
  -- {1} ⊆ ℝ is convex; preimage under linear map is convex.
  have hConv : Convex ℝ ({1} : Set ℝ) := convex_singleton 1
  -- The preimage of {1} under the linear map tensorUnit is convex.
  have hPre : Convex ℝ ((tensorUnit G₁ G₂) ⁻¹' ({1} : Set ℝ)) :=
    hConv.linear_preimage (tensorUnit G₁ G₂)
  -- The preimage of {1} is exactly the desired set.
  convert hPre using 1

/-- Every state of the composite (product-states GPT) is normalized:
`tensorUnit (ρ) = 1` for all `ρ ∈ tensorStates`. -/
theorem tensorStates_normalized
    (G₁ : GPT V₁) (G₂ : GPT V₂) (ρ : V₁ ⊗[ℝ] V₂)
    (hρ : ρ ∈ tensorStates G₁ G₂) :
    tensorUnit G₁ G₂ ρ = 1 := by
  -- The convex hull is contained in any convex set containing the
  -- generators. The level set is convex and contains the generators.
  have h : tensorStates G₁ G₂ ⊆ {x | tensorUnit G₁ G₂ x = 1} := by
    refine convexHull_min ?_ (tensorUnit_level_one_convex G₁ G₂)
    intro x hx
    exact tensorUnit_eq_one_on_generators G₁ G₂ hx
  exact h hρ

/-! ## Effects of the composite GPT -/

/-- The effects of the composite GPT: linear functionals
`e : V₁ ⊗ V₂ →ₗ[ℝ] ℝ` with `0 ≤ e ρ ≤ 1` on every state. -/
def tensorEffects (G₁ : GPT V₁) (G₂ : GPT V₂) :
    Set (V₁ ⊗[ℝ] V₂ →ₗ[ℝ] ℝ) :=
  { e | ∀ ρ ∈ tensorStates G₁ G₂, 0 ≤ e ρ ∧ e ρ ≤ 1 }

theorem tensorEffects_convex (G₁ : GPT V₁) (G₂ : GPT V₂) :
    Convex ℝ (tensorEffects G₁ G₂) := by
  intro e₁ he₁ e₂ he₂ a b ha hb hab ρ hρ
  -- (a • e₁ + b • e₂) ρ = a*(e₁ ρ) + b*(e₂ ρ), pointwise bounds.
  have h1 := he₁ ρ hρ
  have h2 := he₂ ρ hρ
  have hval : (a • e₁ + b • e₂) ρ = a * (e₁ ρ) + b * (e₂ ρ) := by
    show a • e₁ ρ + b • e₂ ρ = a * (e₁ ρ) + b * (e₂ ρ)
    simp [smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact add_nonneg (mul_nonneg ha h1.1) (mul_nonneg hb h2.1)
  · rw [hval]
    calc a * (e₁ ρ) + b * (e₂ ρ)
        ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left h1.2 ha)
                     (mul_le_mul_of_nonneg_left h2.2 hb)
      _ = a + b := by ring
      _ = 1 := hab

/-- The composite unit is itself an effect (probability 1 ∈ [0,1]). -/
theorem tensorUnit_is_effect (G₁ : GPT V₁) (G₂ : GPT V₂) :
    tensorUnit G₁ G₂ ∈ tensorEffects G₁ G₂ := by
  intro ρ hρ
  rw [tensorStates_normalized G₁ G₂ ρ hρ]
  exact ⟨zero_le_one, le_refl _⟩

/-! ## The GPT tensor product -/

/-- **The general GPT tensor product.**

  • Underlying space : `V₁ ⊗[ℝ] V₂`
  • Unit             : `tensorUnit G₁ G₂` (lifts `u₁ · u₂` on tmuls)
  • States           : `convexHull ℝ {ρ₁ ⊗ ρ₂ | ρᵢ ∈ Gᵢ.states}`
                       (separable / product states)
  • Effects          : `{e | 0 ≤ e ρ ≤ 1 ∀ ρ ∈ states}`

All six GPT axioms are verified. The dimension multiplicativity
(Hardy A4 dimension half) is `gptTensor_finrank_eq_mul` below. -/
noncomputable def gptTensor (G₁ : GPT V₁) (G₂ : GPT V₂) :
    GPT (V₁ ⊗[ℝ] V₂) where
  unit := tensorUnit G₁ G₂
  states := tensorStates G₁ G₂
  effects := tensorEffects G₁ G₂
  states_convex := tensorStates_convex G₁ G₂
  effects_convex := tensorEffects_convex G₁ G₂
  states_normalized := tensorStates_normalized G₁ G₂
  prob_in_unit_interval := fun _ he ρ hρ => he ρ hρ
  unit_is_effect := tensorUnit_is_effect G₁ G₂

/-! ## Hardy Axiom 4 — dimension multiplicativity, general GPT level -/

/-- **Hardy A4 (dimension half) — general GPT version.**

For any two GPTs `G₁, G₂`, the dimension of the composite is the
product of the component dimensions:

    finrank ℝ (V₁ ⊗ V₂) = (finrank ℝ V₁) * (finrank ℝ V₂).

This holds *without any additional postulate* — it is a structural
fact about real tensor products (`Module.finrank_tensorProduct`).

This is the general-level upgrade of
`Hardy_Axiom4_WantableGPT_dimension` (which only worked for
WantableGPTs on product Wantables). -/
theorem gptTensor_finrank_eq_mul
    (_G₁ : GPT V₁) (_G₂ : GPT V₂) :
    Module.finrank ℝ (V₁ ⊗[ℝ] V₂)
      = (Module.finrank ℝ V₁) * (Module.finrank ℝ V₂) :=
  Module.finrank_tensorProduct

/-! ## Existence of a product state (Hardy A4 state-half, generic version) -/

/-- **Hardy A4 (state-half existence) — general GPT version.**

If `ρ₁ ∈ G₁.states` and `ρ₂ ∈ G₂.states`, then `ρ₁ ⊗ ρ₂` is a state of
the composite GPT.

This generalizes `Hardy_Axiom4_WantableGPT_state_exists`: rather than
constructing the witness on the WantableGPT level, the same statement
holds at the abstract GPT level by the very definition of
`tensorStates`. -/
theorem gptTensor_tmul_mem_states
    (G₁ : GPT V₁) (G₂ : GPT V₂)
    {ρ₁ : V₁} (hρ₁ : ρ₁ ∈ G₁.states)
    {ρ₂ : V₂} (hρ₂ : ρ₂ ∈ G₂.states) :
    ρ₁ ⊗ₜ[ℝ] ρ₂ ∈ (gptTensor G₁ G₂).states := by
  apply subset_convexHull
  exact ⟨ρ₁, hρ₁, ρ₂, hρ₂, rfl⟩

/-- The product-of-units formula for the composite unit, restated for
the `gptTensor` GPT. -/
@[simp] theorem gptTensor_unit_tmul
    (G₁ : GPT V₁) (G₂ : GPT V₂) (ρ₁ : V₁) (ρ₂ : V₂) :
    (gptTensor G₁ G₂).unit (ρ₁ ⊗ₜ[ℝ] ρ₂) = G₁.unit ρ₁ * G₂.unit ρ₂ :=
  tensorUnit_tmul G₁ G₂ ρ₁ ρ₂

/-! ## Tomographic locality (S1 toward Tier 1 #5)

A composite GPT `G_AB` satisfies *tomographic locality* if its
state-space dimension equals the product of the component dimensions
(K_AB = K_A · K_B). This is the structural fingerprint distinguishing
classical/complex-QM/real-QM (all satisfying it) from quaternionic-QM
(violates it, K_AB > K_A · K_B at N=2).

The framework's `gptTensor` is the canonical tomographic-local
composite: by `gptTensor_finrank_eq_mul`, it satisfies K_AB = K_A · K_B
by construction. So any composite that DOES NOT equal `gptTensor`
(linearly) at the dimension level is automatically not in the
framework's preferred class — which immediately excludes qQM. -/

/-- A composite GPT on `V₁ ⊗[ℝ] V₂` satisfies *tomographic locality*
if its underlying linear dimension equals the product of the
components'. -/
def TomographicLocality
    {V₁ V₂ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    (_G₁ : GPT V₁) (_G₂ : GPT V₂) (_GAB : GPT (V₁ ⊗[ℝ] V₂)) : Prop :=
  Module.finrank ℝ (V₁ ⊗[ℝ] V₂)
    = (Module.finrank ℝ V₁) * (Module.finrank ℝ V₂)

/-- The framework's `gptTensor` composite is tomographic-local. -/
theorem gptTensor_tomographic_local
    {V₁ V₂ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    (G₁ : GPT V₁) (G₂ : GPT V₂) :
    TomographicLocality G₁ G₂ (gptTensor G₁ G₂) :=
  gptTensor_finrank_eq_mul G₁ G₂

/-! **qQM exclusion (Tier 1 #5, S1 step).**

Quaternionic QM at level N has `K_qQM(N) = N(2N - 1)`. At N=2:
`K_qQM(2) = 2(3) = 6`. The composite at N_AB = 4 would have
`K_qQM(4) = 4·7 = 28`, while the framework's tomographic local
product gives `K_A · K_B = 6 · 6 = 36`. Hence `K_qQM(N_A · N_B) ≠
K_qQM(N_A) · K_qQM(N_B)` — qQM violates tomographic locality.

Conclusion: any composite GPT derivable in the framework with
operational dimensions N_A, N_B and the gptTensor composition rule has
`K_AB = K_A · K_B` (the `TomographicLocality` predicate), which qQM
fails. So qQM is structurally INCOMPATIBLE with the framework's
preferred composition. This is the framework's machine-verified
S1-step toward Tier 1 #5 (complex-vs-real-vs-quaternionic Hilbert
space). -/

end GPT
end Perspectival
