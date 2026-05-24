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

end Meeting

/-- Collective form of Axiom III: reality is a set (= predicate) of meetings. -/
abbrev Reality (W : Type u) [Wantable W] := Meeting W → Prop

/-! ## Axiom IV: particulars are stable patterns

A pattern is meant to be a substructure of Reality stable under some
notion of evolution. We have not yet introduced evolution, so this is
left as a placeholder predicate. Replacing it with a genuine
dynamical/categorical notion is itself open work. -/

def Pattern (W : Type u) [Wantable W] : Type _ := Reality W → Prop

end Perspectival
