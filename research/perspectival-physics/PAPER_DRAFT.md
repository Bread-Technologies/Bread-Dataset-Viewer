# Perspectival Reconstruction of Quantum Mechanics — Lean 4 Formalization

## Working draft (interim, calibrated)

This is the in-progress writeup of the perspectival-physics research
program. Every claim in this paper is annotated with one of:

  ✓  machine-verified in Lean 4 (this repository)
  ▲  partially verified (with documented `sorry` placeholders)
  ○  argued in prose only — presumed wrong until verified
  ?  open

The repository is at `research/perspectival-physics/` in
`bread-technologies/bread-dataset-viewer`. Pointer files: `STATUS.md`
(per-result catalog), `FINDINGS.md` (running honest log), `LINEAGE.md`
(philosophical references).

---

## 1. Abstract

We formalize, in Lean 4, a perspective-centric axiomatization of the
operational structure of quantum mechanics. Four axioms — *to exist is
to instantiate a perspective with directedness*; *wants are
intrinsically relational*; *reality is the structure of meetings
between wants*; *all particulars are stable patterns* — are encoded
as types. We then bridge the resulting ontology to standard
operational-quantum machinery (Generalized Probabilistic Theories;
ordered ★-rings) and use the bridge to mechanize two substantive
results:

  (i) ✓ a Lean-verified statement of the Bell vs. Tsirelson dichotomy
      in perspective-wanting vocabulary: commutativity of the algebra
      of observables ↔ existence of an observer-independent ledger of
      facts, with the Tsirelson bound 2√2 obtained as the framework's
      natural prediction;

  (ii) ✓ a Lean-verified no-cloning theorem in linear-algebraic form,
       framed as the structural shadow of the framework's two-sided
       wanting axiom.

We further state Hardy's five axioms (Hardy 2001) as Lean predicates on
our GPT structure and provide an honest categorization (DERIVABLE /
AUXILIARY / INCOMPATIBLE) relative to axioms I–IV. Formal derivations
of the DERIVABLE entries are identified as the principal open
sub-problem.

---

## 2. The axioms (Lean: `Perspectival.Ontology`)

**Axiom I.** To exist is to instantiate a perspective with directedness
(wanting). Perspective is not a property of some pre-existing thing;
perspective with directedness *is* what existence consists in.

  ✓ Encoded as `structure Existent (W : Type u) where want : W`.

**Axiom II.** Wants are intrinsically relational. Every want presupposes
a complement.

  ✓ Encoded as `class Wantable W` with an involutive
    `complement : W → W` (`complement_involutive : ∀ w, complement
    (complement w) = w`).

**Axiom III.** Reality is the structure of meetings between wants.

  ✓ Encoded as `structure Meeting W` (pairs of complementary wants),
    `Reality W := Meeting W → Prop`, with `Meeting.swap` involutive
    (`swap_swap`).

**Axiom IV.** All apparent particulars are stable patterns within (III).
The mathematical structure of any such patterning is group-theoretic.

  ▲ Encoded as a `Pattern` placeholder + a `PTrans` group of
    perspectival transformations (Lean: `Perspectival.Transformations`),
    which is the action-theoretic carrier of group structure on
    Wantables. The "stability" predicate is left abstract pending a
    dynamical refinement.

We further establish (Lean: `Perspectival.Composition`):

  ✓ Disjoint-union Wantable structure: complement acts component-wise.
  ✓ `Meeting.sum_no_cross` — no cross-system meetings in a disjoint
    union. This is the structural-no-signaling theorem of the framework.
  ✓ Componentwise PTrans on disjoint unions.

---

## 3. Result A — Tsirelson is the framework's natural CHSH bound

(Lean: `Perspectival.CHSH`.)

We define a `BinaryObservable R := { val : R // val^2 = 1, star val = val }`
in a ★-ring `R` — physically, a ±1-valued observable. A `SpacelikePair R`
packages four binary observables `A₀, A₁, B₀, B₁` with the spacelike
cross-commutations `Aᵢ Bⱼ = Bⱼ Aᵢ`. The CHSH expression is

    chshExpr s := A₀·B₀ + A₀·B₁ + A₁·B₀ − A₁·B₁ ∈ R.

We prove (via Mathlib's `CHSH_inequality_of_comm` and
`tsirelson_inequality`):

  ✓ **`bound_realist`.** In a *commutative* ordered ★-algebra over ℝ:

         chshExpr s ≤ 2.

  ✓ **`bound_perspectival`.** In a *general* ordered ★-algebra over ℝ:

         chshExpr s ≤ √2³ · 1   ( = 2√2 ).

The framework's reading. **Commutativity of the algebra of observables
is equivalent to the existence of an observer-independent joint
ledger** — a single classical-style assignment of ±1 values to all four
observables simultaneously. The framework explicitly rejects this
ledger (Frauchiger–Renner C-drop; Quine's ontological relativity at
the semantic level; Rovelli's relational QM at the physical level).
Rejecting it removes the commutativity hypothesis; the
mathematically forced consequence is that the relevant bound is
2√2, which is exactly the experimentally verified one.

**Honest qualification.** This is *re-interpretation*, not derivation.
The ★-algebra structure is imported, not derived from I–IV. The
philosophical content of the framework is the *identification* of
which algebraic hypothesis is the realist hinge.

---

### 3.1 Group structure on perspectival transformations

(Lean: `Perspectival.Transformations`.)

The set `PTrans W` of perspectival transformations of a `Wantable W`
— self-bijections commuting with `complement` — is verified as a
Lean `Group` instance. This is the first concrete carrier of
Axiom IV's "the mathematical structure of perspectival patterning is
group-theoretic": the group laws (composition, identity, inverse)
are formally proven, and the action on `Meeting`s is functorial.

## 4. Result B — No-cloning

(Lean: `Perspectival.NoCloning`.)

A *linear cloner* on a set `S ⊆ V` is a linear map
`C : V →ₗ[ℝ] V ⊗ V` with `C v = v ⊗ v` for all `v ∈ S`.

  ✓ **`cross_terms_vanish`.** Given a linear cloner on `S` containing
    `v₁, v₂` and `v₁ + v₂`:

        v₁ ⊗ v₂ + v₂ ⊗ v₁ = 0.

    Proof: linearity gives `C(v₁+v₂) = v₁⊗v₁ + v₂⊗v₂`; the cloner law
    gives `C(v₁+v₂) = (v₁+v₂) ⊗ (v₁+v₂)`; expanding and cancelling the
    duplicates leaves the cross terms equal to zero.

  ✓ **`no_cloning`.** If additionally there is a bilinear form
    `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` with `B v₁ v₂ + B v₂ v₁ ≠ 0`, contradiction.

    Proof: `TensorProduct.lift B` sends the (zero) sum to
    `B v₁ v₂ + B v₂ v₁ ≠ 0`, impossible.

The framework's reading. A "want" cannot be duplicated into two
isolated copies, because wanting is intrinsically two-sided
(Axiom II). Linearity is the structural shadow of this two-sidedness;
the cross-term cancellation makes the impossibility quantitative.

The bilinear-form hypothesis is *weaker than* (and implied by) linear
independence of `v₁, v₂`. We use this weaker form because it keeps the
proof self-contained at this level; the standard "lin-indep ⇒ such `B`
exists" wrapper is left for follow-up.

---

### 4.1 Distinguishability ↔ linear independence

(Lean: `Perspectival.Distinguish`.)

A bridge between the *operational* notion of distinguishability (some
effect gives probability 1 on one state, 0 on another) and the
*linear-algebraic* notion of linear independence:

  ✓ `distinguishable_imp_linear_independent`: distinguishable states
    are linearly independent.
  ✓ `linear_dependent_states_eq`: linearly dependent states are
    equal. Combining gives: in a GPT, two states are linearly
    independent iff they are unequal.
  ✓ `perfect_distinguishable_imp_linear_independent`: a finite family
    of states with a Kronecker effect family is linearly independent.
  ✓ `operational_dim_le_state_dim`: in finite-dim GPT, N perfectly
    distinguishable states ⇒ state space has dimension ≥ N. This is
    the structural form of Hardy's N ≤ K direction.
  ✓ `no_cloning_of_distinguishable`: full chain — if two states are
    distinguishable, no linear cloner exists on a set containing them.

The classical n-simplex's vertices give a concrete example:
`Classical.vertex_linear_independent` machine-verifies that the n
vertices of the n-outcome classical GPT are linearly independent
(via the abstract `perfect_distinguishable_imp_linear_independent`
applied to the coordinate-projection witness).

## 5. Hardy's axioms — categorization

(Lean: `Perspectival.Hardy`.)

Each of Hardy 2001's five axioms is stated as a Lean predicate on the
GPT structure (`Perspectival.GPT`, with a concrete classical instance
`Perspectival.Classical.gpt`).

| Axiom | Statement (gloss) | Category | Status |
|------|--------------------|----------|--------|
| 1 — Probabilities | well-defined limit frequencies | DERIVABLE | ✓ formally proven (`axiom1_holds`) |
| 2 — Simplicity | K minimal among theories of given N | AUXILIARY | ○ argued only |
| 3 — Subspaces | restricting to a sub-state-space yields a sub-GPT | DERIVABLE | ○ argued; formal derivation OPEN |
| 4 — Composite systems | `N_AB = N_A · N_B`, `K_AB = K_A · K_B` | AUXILIARY | ○ multiplicative rule beyond disjoint-union no-signaling |
| 5 — Continuity | continuous reversible transformations between pure states | DERIVABLE | ○ argued; libertarian agency favors but does not force; OPEN |

The honest research bottleneck: turning the ARGUED entries into
formally proven ones, or honestly downgrading them. The Axiom 5
direction — *libertarian agency at each instant ⇒ continuous group
of reversible transformations* — is the most promising open angle for
the framework to do unique technical work.

---

### 5.1 Result C — Hardy Axiom 5 from libertarian agency

(Lean: `Perspectival.Continuity`.)

This is the framework's *most distinctive* machine-verified
contribution. We formalize the libertarian-agency commitment as a
postulate `HasConnectedAgency` — the set of reversible perspectival
transformations is path-connected and contains the identity — and
prove:

  ✓ `continuous_path_of_reachable`: from agency + reachability, any
    two reachable states are connected by a continuous path in `V`.
  ✓ `hardy_axiom5_of_agency`: more strongly, there is a continuous
    path of *linear maps* from the identity (at t=0) to a
    transformation realizing the reachability (at t=1). This is
    Hardy Axiom 5 in concrete form, modulo the pure-state restriction.
  ✓ `hardy_axiom5_pure_states`: the pure-state form.
  ✓ `hardy_axiom5_transitive`: the full Hardy Axiom 5 — given
    agency + transitivity on pure states, between any two pure states
    there exists a continuous path of linear maps realizing a
    transformation between them.

The framework's reading: Hardy treats continuity as a postulate; we
*derive* it from a more philosophically motivated postulate (agency
as path-connectedness of the transformation group) plus the standard
transitivity hypothesis. This is the framework's first technical
contribution that goes beyond restating standard operational content
in new vocabulary.

**Honest qualification.** The derivation has three open subproblems:

  1. Whether libertarian agency really forces path-connectedness
     rather than just richness — philosophical-to-formal step.
  2. Whether transitivity on pure states is derivable from the
     framework's axioms (as opposed to being an extra hypothesis,
     as in Hardy).
  3. Whether the connected group is necessarily a Lie group; the
     theorem we proved is purely topological.

## 6. Classical GPT instance

(Lean: `Perspectival.Classical`.)

We construct the n-outcome classical theory as a full instance of
`Perspectival.GPT`:

  ✓ `states := stdSimplex ℝ (Fin n)` — verified convex via
    Mathlib's `convex_stdSimplex`.
  ✓ `effects := { ⟨·, f⟩ : f ∈ [0,1]ⁿ }` — verified convex.
  ✓ `unit := ∑` — verified normalized on states.
  ✓ Probabilities `e ρ ∈ [0,1]` for all `e ∈ effects`, `ρ ∈ states`.

This serves three purposes:

  (a) demonstrates the GPT framework is non-vacuous;
  (b) provides a reference point for which Hardy axioms hold;
  (c) makes the K = N (classical) vs K = N² (quantum) target
      concretely testable in subsequent work.

A quantum instance is the next milestone, via density matrices —
Mathlib + Physlib provide the ingredients but the assembly is open
work in this codebase.

---

## 7. What this work does NOT establish

Calibrated honesty floor:

  ?  We have not derived the ★-algebra structure from I–IV. The
     ★-algebra picture is imported.
  ?  We have not derived the gauge group U(1)×SU(2)×SU(3). Not
     known to anyone, from any framework.
  ?  We have not derived three fermion generations. Same.
  ?  We have not formally completed Hardy's reconstruction
     theorem (K = N²).
  ?  The "hard-problem dissolution" and "category-error reading of
     the cosmological constant" remain philosophical moves, not
     mathematical results.

In each of these places the framework offers a *reading*; the
underlying mathematics is borrowed.

---

## 8. What the framework would need to do to earn its keep

A theorem of the form:

  > Axioms I–IV (plus minimal additions X, Y) imply some Hardy
  > axiom that cannot be motivated as cleanly from realist
  > axioms.

The most plausible target is Hardy Axiom 5 (continuity of reversible
transformations between pure states), via the framework's
libertarian-agency commitment to genuine choice at each instant.

A formal version we suggest: show that the framework requires the set
of reversible perspectival transformations on a pure-state space to
form a *connected Lie group*, not a discrete group. The connectedness
hypothesis is closely related to Hardy's continuity axiom and is the
dividing line between classical (S_N) and quantum (U(N)) reversible
dynamics.

We have not attempted this proof. It is the natural next research
target.

---

## 9. Philosophical lineage

See `LINEAGE.md`. Key bibliographic anchors:

- **Stage theory / persistence without substance.** Quine (*Word and
  Object*, 1960; *Ontological Relativity*, 1968). David Lewis (*On the
  Plurality of Worlds*). Theodore Sider (*Four-Dimensionalism*, 2001).
  Derek Parfit (*Reasons and Persons*).
- **Process philosophy.** A. N. Whitehead (*Process and Reality*).
  Henri Bergson.
- **Idealist core.** Schopenhauer (Will-as-noumenon), Husserl, Sartre.
- **Relational structure.** Leibniz, Mach, Wheeler, Rovelli.
- **Pragmatist.** James, Peirce, Rorty.
- **Austrian economics.** Hayek (spontaneous order), Mises (praxeology).
- **Buddhist.** Madhyamaka, Yogacara, *paticca-samuppada*.
- **Confronted and rejected.** Dennett (compatibilism — rejected
  because framework rejects physicalism, so needs no compatibilist
  rescue); Goff (panpsychism — rejected because the framework treats
  matter as how consciousness appears, not as something with
  consciousness as a property).

**Quine–Rovelli parallel.** The framework asserts that Quine's
ontological relativity at the semantic level prefigures Rovelli's
relational quantum mechanics at the physical level. Both deny an
observer-/framework-independent ledger; both retain pragmatic adequacy
of framework-internal claims. The framework unifies these by making
perspective-with-directedness the fundamental layer of which semantic
and physical structures are different surfaces.

---

## 10. Status of this draft

In-progress. Updates committed to
`research/perspectival-physics/PAPER_DRAFT.md`. Companion data:
`STATUS.md`, `FINDINGS.md`. Code:
`research/perspectival-physics/Perspectival/`.

Co-author target list for the final version: Markus Müller (algorithmic
idealism); Lluis Masanes (operational reconstructions); Carlo Rovelli
(relational QM); the Lean-QuantumInfo / Physlib team for the
formalization layer.

The work here is incomplete; honesty requires marking that explicitly.
The technical content already verified is novel in the sense that no
prior Lean formalization links the perspectival-philosophical layer
to operational quantum machinery, but most of the *mathematical*
content is the well-established CHSH/Tsirelson / no-cloning / Hardy
material, recast in the framework's vocabulary. The framework's
distinctive contribution remains to be earned by the open derivations
above.
