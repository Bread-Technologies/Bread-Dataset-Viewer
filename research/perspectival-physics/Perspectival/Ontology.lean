/-
Perspectival Physics — Ontology Scaffold
========================================

Encoding of Axioms I–IV as a Lean 4 ontology. This is Tier 1, Step 1
of the research program.

Honest scope of this file:
  - Defines types. Proves the trivial structural lemmas that follow
    from those definitions (complement involution, meeting swap).
  - Does NOT derive any physics. Encoding a philosophical axiom as a
    type signature is not a derivation; it is a fixing of referents.
  - The bridge from this scaffold to operational probability,
    Hilbert space, or gauge structure requires additional postulates
    that are not entailed by I–IV. Where such postulates are added
    later, they — not the perspective/wanting vocabulary — will
    carry the technical load. That gap is the actual research problem.
-/

namespace Perspectival

/-! ## Axiom II: wants are intrinsically relational

Every want has a complement; complementation is an involution. We do
NOT here require complement to be fixed-point-free; whether `w =
complement w` is permissible is a design choice deferred to refinement.
-/

universe u

class Wantable (W : Type u) where
  complement : W → W
  complement_involutive : ∀ w, complement (complement w) = w

namespace Wantable
attribute [simp] complement_involutive
end Wantable

/-! ## Axiom I: to exist is to instantiate a perspective with directedness

An existent is identified by its directedness (its want). The
philosophical claim "perspective IS what existence consists in" is
honored by refusing any substrate field other than the want itself.
-/

structure Existent (W : Type u) where
  want : W

instance {W : Type u} [Inhabited W] : Inhabited (Existent W) := ⟨⟨default⟩⟩

/-- `complement` is injective. -/
theorem Wantable.complement_injective {W : Type u} [Wantable W] :
    ∀ a b : W, Wantable.complement a = Wantable.complement b → a = b := by
  intro a b h
  have : Wantable.complement (Wantable.complement a) = Wantable.complement (Wantable.complement b) :=
    congrArg Wantable.complement h
  rw [Wantable.complement_involutive, Wantable.complement_involutive] at this
  exact this

/-- `complement` is surjective. -/
theorem Wantable.complement_surjective {W : Type u} [Wantable W] :
    ∀ w : W, ∃ v, Wantable.complement v = w :=
  fun w => ⟨Wantable.complement w, Wantable.complement_involutive w⟩

/-- Alias: `complement_complement` is `complement_involutive`. -/
theorem Wantable.complement_complement {W : Type u} [Wantable W] (w : W) :
    Wantable.complement (Wantable.complement w) = w :=
  Wantable.complement_involutive w

-- NOTE: Wantable.complement is a self-bijection (an Equiv). The
-- Equiv type lives in Mathlib; not imported here to keep Ontology
-- pure. See Examples.lean for an Equiv.Perm instance.

/-- For any Wantable, every want has at least one complement (namely
the standard complement). -/
theorem Wantable.exists_complement {W : Type u} [Wantable W] (w : W) :
    ∃ v, Wantable.complement w = v :=
  ⟨Wantable.complement w, rfl⟩

/-- Two wants are complementary iff one is the complement of the other. -/
theorem Wantable.complement_eq_iff {W : Type u} [Wantable W] (a b : W) :
    Wantable.complement a = b ↔ a = Wantable.complement b := by
  constructor
  · intro h
    have : Wantable.complement b = Wantable.complement (Wantable.complement a) :=
      congrArg Wantable.complement h.symm
    rw [Wantable.complement_involutive] at this
    exact this.symm
  · intro h
    have : Wantable.complement a = Wantable.complement (Wantable.complement b) :=
      congrArg Wantable.complement h
    rw [Wantable.complement_involutive] at this
    exact this

/-- Complement is self-inverse as a function. -/
theorem Wantable.complement_complement_eq_id {W : Type u} [Wantable W] :
    Wantable.complement ∘ Wantable.complement = (id : W → W) := by
  funext w
  exact Wantable.complement_involutive w

/-! ## Axiom III: reality is the structure of meetings

A meeting is a pair of complementary wants. Reality is a collection
of such meetings — explicitly nothing else. -/

structure Meeting (W : Type u) [Wantable W] where
  side₁ : W
  side₂ : W
  complementary : Wantable.complement side₁ = side₂

namespace Meeting

variable {W : Type u} [Wantable W]

/-- A meeting viewed from its other side. -/
def swap (m : Meeting W) : Meeting W where
  side₁ := m.side₂
  side₂ := m.side₁
  complementary := by
    have h := m.complementary
    calc Wantable.complement m.side₂
        = Wantable.complement (Wantable.complement m.side₁) := by rw [h]
      _ = m.side₁ := Wantable.complement_involutive _

@[simp] theorem swap_swap (m : Meeting W) : m.swap.swap = m := by
  cases m; rfl

/-- The two sides of a meeting are mutually complementary. -/
theorem complementary_symm (m : Meeting W) :
    Wantable.complement m.side₂ = m.side₁ := by
  have h := m.complementary
  rw [← h, Wantable.complement_involutive]

/-- `side₂` is determined by `side₁`: it's its complement. -/
theorem side₂_eq_complement_side₁ (m : Meeting W) :
    m.side₂ = Wantable.complement m.side₁ := m.complementary.symm

/-- Construct a meeting from just one side (the other is determined). -/
def mk_fromSide (W : Type u) [Wantable W] (w : W) : Meeting W where
  side₁ := w
  side₂ := Wantable.complement w
  complementary := rfl

@[simp] theorem mk_fromSide_side₁ {W : Type u} [Wantable W] (w : W) :
    (mk_fromSide W w).side₁ = w := rfl

@[simp] theorem mk_fromSide_side₂ {W : Type u} [Wantable W] (w : W) :
    (mk_fromSide W w).side₂ = Wantable.complement w := rfl

/-- `mk_fromSide` and `side₁` exhibit a bijection `W ≃ Meeting W`.
This formalizes the observation that meetings are no more (and no less)
than wants — every want induces a unique meeting (with its complement),
and every meeting is determined by either side. -/
theorem mk_fromSide_side₁_inv (W : Type u) [Wantable W] (m : Meeting W) :
    mk_fromSide W m.side₁ = m := by
  rcases m with ⟨s₁, s₂, h⟩
  show Meeting.mk s₁ (Wantable.complement s₁) rfl = ⟨s₁, s₂, h⟩
  -- s₂ = complement s₁ by h.symm
  have : s₂ = Wantable.complement s₁ := h.symm
  subst this
  rfl

/-- A meeting is determined by `side₁`: two meetings are equal iff
their first sides are equal. (The second side is forced by
`complementary`, and the proof itself is propositional.) -/
theorem ext_of_side₁ (m₁ m₂ : Meeting W) (h : m₁.side₁ = m₂.side₁) :
    m₁ = m₂ := by
  rcases m₁ with ⟨s₁, s₂, h₁⟩
  rcases m₂ with ⟨t₁, t₂, h₂⟩
  cases h
  have hs : s₂ = t₂ := h₁.symm.trans h₂
  cases hs
  rfl

/-- Swap of `mk_fromSide w` is exactly `mk_fromSide (complement w)`. -/
@[simp] theorem swap_mk_fromSide (w : W) :
    (mk_fromSide W w).swap = mk_fromSide W (Wantable.complement w) :=
  ext_of_side₁ _ _ rfl

end Meeting

/-- A *self-complementary* want is one that is its own complement.
The framework's Axiom II requires complement to be involutive but
does *not* forbid such fixed points; whether self-complementary wants
are admissible is a refinement question. -/
def SelfComplementary {W : Type u} [Wantable W] (w : W) : Prop :=
  Wantable.complement w = w

/-- If `w` is self-complementary, then a meeting with `w` on both sides
exists (a degenerate "monad-meeting"). -/
def Meeting.of_selfComplementary {W : Type u} [Wantable W]
    {w : W} (h : SelfComplementary w) : Meeting W :=
  ⟨w, w, h⟩

/-- The *complement-fixed-point predicate* is invariant under PTrans-like
operations that respect complement: if `f` commutes with complement,
then `f` maps fixed points to fixed points. (Statement at the function
level; the PTrans-specific version lives in `Transformations`.) -/
theorem SelfComplementary.preserved {W : Type u} [Wantable W]
    (f : W → W) (hf : ∀ w, f (Wantable.complement w) = Wantable.complement (f w))
    (w : W) (h : SelfComplementary w) : SelfComplementary (f w) := by
  show Wantable.complement (f w) = f w
  rw [← hf, h]

/-- A Wantable is *fixed-point-free* if no want is its own complement. -/
def FixedPointFreeComplement (W : Type u) [Wantable W] : Prop :=
  ∀ w : W, ¬ SelfComplementary w

/-- If complement is fixed-point-free, then `w ≠ complement w` for all `w`. -/
theorem ne_complement_of_fixedPointFree {W : Type u} [Wantable W]
    (h : FixedPointFreeComplement W) (w : W) : w ≠ Wantable.complement w := by
  intro hw
  exact h w hw.symm

-- NOTE (OPEN): a natural conjecture is that for finite Wantable W with
-- fixed-point-free complement, |W| is even (complement is a free Z/2
-- action; orbits all have size 2). The proof can be given via
-- `Equiv.Perm.cycleType` machinery; left for follow-up.

-- The actual proof that fixed-point-free + finite → even cardinality
-- requires Mathlib (LinearOrder, Fintype, Finset). It is given in
-- `Perspectival/Examples.lean` as `card_even_of_fixedPointFree`.

/-- Collective form of Axiom III: reality is a set (= predicate) of meetings. -/
abbrev Reality (W : Type u) [Wantable W] := Meeting W → Prop

/-! ## Axiom IV: particulars are stable patterns

A pattern is meant to be a substructure of Reality stable under some
notion of evolution. We have not yet introduced evolution, so this is
left as a placeholder predicate. Replacing it with a genuine
dynamical/categorical notion is itself open work. -/

def Pattern (W : Type u) [Wantable W] : Type _ := Reality W → Prop

/-- The trivially-true Pattern: every Reality satisfies it. -/
def Pattern.trivial (W : Type u) [Wantable W] : Pattern W := fun _ => True

/-- The trivially-false Pattern: no Reality satisfies it. -/
def Pattern.empty (W : Type u) [Wantable W] : Pattern W := fun _ => False

/-- Patterns close under conjunction (intersection of satisfied Realities). -/
def Pattern.and {W : Type u} [Wantable W] (P Q : Pattern W) : Pattern W :=
  fun R => P R ∧ Q R

/-- Patterns close under disjunction. -/
def Pattern.or {W : Type u} [Wantable W] (P Q : Pattern W) : Pattern W :=
  fun R => P R ∨ Q R

/-! ## Axiom IV refinement: PatternStableWantable

The framework's Axiom IV says "particulars are stable patterns within
meetings, not substances behind them." A bare `Wantable W` does not
itself express the stability requirement. `PatternStableWantable`
strengthens `Wantable` with an explicit `Stable : W → Prop` predicate.

Per `PATTERN_STABLE_WANTABLE.md`, formulation (a) — informational
sufficiency, à la Friston's Markov blanket — recommends:
  `Stable w` iff there exists a finite-information predicate
  determining `w` up to perspectival transformations.

This file provides the minimal scaffold; the choice of Stable
predicate is left open for downstream refinement modules.

This is the framework's axiom-refinement per the user-authorized
"metaphysics-fixed, axioms-adjustable" methodology. The metaphysical
commitment (Axiom IV) is fixed; this is one concrete formalization. -/

/-- A `PatternStableWantable W` is a `Wantable W` with an explicit
predicate `Stable : W → Prop` marking which wants represent stable
patterns. Constraints: (1) complement preserves stability — if `w` is
a stable pattern, so is its complement (because complement is
involutive and stability is a structural property of wants). (2) the
stable subclass is non-empty — there is at least one stable pattern
(otherwise no existents). -/
class PatternStableWantable (W : Type u) extends Wantable W where
  Stable : W → Prop
  stable_complement : ∀ w, Stable w → Stable (Wantable.complement w)
  stable_nonempty : ∃ w, Stable w

namespace PatternStableWantable
attribute [simp] stable_complement
end PatternStableWantable

/-- For any `Wantable W` where the "everything is stable" predicate is
non-trivially inhabited, there is a `PatternStableWantable` instance
with `Stable := fun _ => True`. This is the maximal-stability degenerate
case; non-trivial formulations restrict `Stable` further. -/
@[reducible]
def PatternStableWantable.trivialOfNonempty (W : Type u) [Wantable W]
    [Nonempty W] : PatternStableWantable W where
  toWantable := inferInstance
  Stable := fun _ => True
  stable_complement := fun _ _ => trivial
  stable_nonempty := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact ⟨w, trivial⟩

end Perspectival
