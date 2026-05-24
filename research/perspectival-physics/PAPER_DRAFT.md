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

**Structural identification (`mem_range_toEquivPermHom_iff`).** A
verified theorem now establishes that `PTrans W` is *exactly* the
centralizer of the `complement` permutation inside the full
permutation group `Equiv.Perm W`. That is: for any permutation
`σ : Equiv.Perm W`,

> `σ ∈ image(PTrans → Perm)  ⟺  σ ∘ complement = complement ∘ σ`.

This is an unexciting but clarifying result: perspectival
transformations are *not* a novel structure beyond Mathlib's
permutation group — they are the Z/2-equivariant permutations. The
ontology's mathematical content lives in the *compatibility* with
complement, not in the perspective vocabulary itself. Per Quine's
ontological deflation, this is precisely what we should expect:
"perspective" is a way of speaking about an algebraic invariant
already in the analytic toolkit. The research question is whether
adding *further* postulates on top of I–IV picks out specifically
quantum mathematics; the bare ontology, as the theorem makes
explicit, does not.

**Concrete classification (`ptrans_bool_classification`,
Examples).** For `W = Bool` (the smallest non-trivial Wantable),
`PTrans Bool = {1, boolSwap}` — exactly the two-element centralizer.
This is the smallest non-trivial verified instance of the general
structural fact.

**Vertex action (`transformAction_vertex`).** Under the bridge
`fromPTrans : PTrans W → Transform(gpt W)`, the induced action on the
state space permutes the vertices according to the underlying
permutation: `transformAction φ (vertex w) = vertex (φ.toFun w)`. The
PTrans group acts on the *operational* state space (the `|W|`-simplex)
the same way it acts on the *abstract* outcome set `W`.

**Vertex decomposition (`vertex_decomposition`).** Every state of
the WantableGPT decomposes as `f = ∑ w, f(w) • vertex w` — i.e.,
the WantableGPT-from-finite-Wantable construction *is* the classical
simplex on `W`, no more, no less. Combined with the structural
identification above, this completes a deflation: the ontology
of finite Wantables, when bridged via `WantableGPT`, picks out
classical simplices with Z/2-equivariant automorphism subgroup.

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

---

### 5.2 Result D — R6 Birkhoff disconnect for Classical n = 2

(Lean: `Perspectival.Classical`,
theorem `classical_n2_strict_reversible_path_id_swap_empty`.)

The libertarian-agency derivation of Hardy Axiom 5 (Section 5.1) is
cheap when the path requirement is weak — `path_via_affineLine` shows
that any two linear maps on a topological `V` are connected by an
affine path, and so the bare `HasConnectedAgency` postulate is
generically satisfiable. The substantive question is whether the
strengthened path notion — paths that remain *bijective* and *state-
preserving at every intermediate point* — is also generically
satisfiable. Section 5.1 leaves this open.

This subsection records the *first* verified result that closes the
question in the direction the framework wants: for the Classical
n = 2 GPT, the strengthened agency postulate cannot connect the
identity to the non-trivial swap.

**The strict-path hierarchy.** `Continuity.lean` introduces three
nested path notions:

  ✓ `StatePreservingPath G R₁ R₂` — a continuous path `γ : [0,1] →
    (V →ₗ V)` with `γ 0 = R₁`, `γ 1 = R₂`, jointly continuous in
    `(t, v)`, and `γ t ρ ∈ G.states` for every `t` and every
    state `ρ`.
  ✓ `ReversiblePath G R₁ R₂` — strengthens `StatePreservingPath`
    to a path of *Reversibles* (state-and-unit-preserving linear
    maps).
  ✓ `StrictReversiblePath G R₁ R₂` — strengthens `ReversiblePath`
    further by requiring `γ t` to be *bijective* at every `t`.

The corresponding agency postulates are `StatePreservingAgency`,
`ReversibleAgency`, `StrictConnectedAgency`. The framework's
*genuine* path-connectedness commitment — perspectives evolving
continuously through admissible (i.e., reversible *and* state-
preserving *and* bijective) transformations — is `StrictConnectedAgency`.
This is the strengthening that R6 of `ROADMAP.md` asks for.

**The Birkhoff disconnect.** On the Classical n = 2 GPT
(`Classical.gpt 2`, state space the 2-simplex in `ℝ²`), the
bijective state-preserving linear maps are exactly the 2 × 2
doubly-stochastic matrices with non-zero determinant. Parametrising
such a matrix as `[[a, b], [1−a, 1−b]]` with `a, b ∈ [0,1]`, the
bijectivity locus is `{(a, b) ∈ [0,1]² : a ≠ b}`. This set has
exactly two connected components:

  - `{a > b}`, containing `id` (`a = 1, b = 0`),
  - `{a < b}`, containing `swap` (`a = 0, b = 1`),

separated by the singular line `a = b`. Any continuous path from
`id` to `swap` must cross this line — at which point bijectivity
fails. Formally:

  ✓ `classical_n2_strict_reversible_path_id_swap_empty` — there is
    no `StrictReversiblePath` from the identity to the swap on
    `Classical.gpt 2`. Proof: the *first-column determinant*
    `n2_disc_det R := R(vertex 0) 0 − R(vertex 1) 0` is `+1` at `id`
    and `−1` at `swap`; joint continuity of the path pushes
    `n2_disc_det` to a continuous map `[0,1] → ℝ`; the Intermediate
    Value Theorem produces a `t*` with `n2_disc_det (γ t*) = 0`; but
    `n2_disc_det = 0` together with state-preservation forces
    `γ t*` to send `vertex 0` and `vertex 1` to the same vector,
    contradicting bijectivity.

  ✓ `classical_n2_no_two_element_strict_agency` — corollary: there
    is no `StrictConnectedAgency` on `Classical.gpt 2` whose
    availability set contains both `id` and `swap`.

  ✓ `classical_n2_det_one_eq_id` — the n = 2 enumeration: every
    bijective state-preserving linear map `R : V 2 → V 2` with
    `n2_disc_det R = 1` is exactly the identity, and (by symmetric
    argument) every such map with `n2_disc_det R = −1` is exactly
    `swap`. Combined with the disconnect, the bijective state-
    preserving linear maps on `V 2` are *exactly* `{id, swap} =
    S_2`.

**Framework reading.** The n = 2 Birkhoff disconnect is the
framework's first formally verified instance of the structural
divergence between classical and quantum reversible dynamics. The
classical reversible group `S_N` is *discrete* — its bijective
state-preserving stratum decomposes into `N!` connected components,
one per permutation — whereas the quantum reversible group `U(N)`
is *connected*. The agency commitment, formalized as
`StrictConnectedAgency`, is therefore *vacuously trivial* (only the
single-element trivial agency exists) over a classical GPT but
*non-vacuously substantive* over a quantum-like GPT.

This is the first machine-verified result in the codebase that
shows the framework *picks out* quantum-like structure: any GPT in
which the libertarian-agency postulate is genuinely instantiated
(rather than reduced to triviality) cannot be the Classical n = 2
simplex. The result generalizes in principle to all `n ≥ 2`: the
Birkhoff polytope's bijection locus has `n!` connected components
(sign of permutation as topological invariant), so the same
disconnect argument applies; only the n = 2 case is currently
machine-verified.

**Honest qualifications.**

  ?  The full `n ≥ 3` generalization needs the `n × n` determinant
     and a finer matrix-analytic argument; it is sketched but not
     proven in `Classical.lean`.
  ?  The result rules out *classical* GPTs as carriers of strict
     agency; it does not yet positively *construct* a non-classical
     GPT in which strict agency is satisfied. That construction —
     plausibly via complex-amplitude or qubit-like Wantable
     refinements — is the natural Tier 1 follow-up.
  ?  The "agency forces strict connectedness" half — i.e., the
     philosophical-to-formal half of R6 — remains an input, not a
     theorem.

What the result does *positively* accomplish: it converts R6 from a
heuristic ("the agency postulate should be substantive, not vacuous")
into a verified non-trivial constraint ("on classical GPTs the
postulate has only the trivial witness, hence selects against
classical realizations of agency"). This is, together with the
agency → Hardy Axiom 5 derivation of 5.1, the framework's most
distinctive machine-verified content.

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

### 6.1 No-go: the finite-Wantable bridge stays classical

(Lean: `WantableGPT.lean :: wantableGPT_is_classical`.)

A verified theorem now establishes that the WantableGPT bridge from
*any* finite Wantable `W` to a GPT *always* produces the classical
signature `N = K = |W|`. The composition theorems further pin down
the rule:
`K(W₁ × W₂) = |W₁| · |W₂|` and `K(W₁ ⊕ W₂) = |W₁| + |W₂|`.

This is a *positive* no-go: it sharply delimits what the bare
axioms I–IV plus `WantableGPT.gpt` can deliver — only classical GPT
structure. To derive non-classical structure, one must add at least
one of:
- A richer composition rule (Hardy Axiom 4 in tensor-product form),
- Additional postulates on the agency / continuity structure
  (Continuity.lean's `HasConnectedAgency`, or a stronger refinement),
- A different bridge construction (e.g., complex-valued or
  infinite-dimensional Wantable).

**Triple no-go (verified).** Three of the four candidate Hardy
signatures are formally ruled out for `WantableGPT.gpt W` when
`|W| ≥ 2`:
- Quantum (K = N²): `wantableGPT_not_quantum`.
- Real-QM (2K = N(N+1)): `wantableGPT_not_realQM`.
- Quaternionic-QM (K = N(2N-1)): `wantableGPT_not_quaternionicQM`.

The remaining (and verified-realized) signature is the classical one,
K = N = |W|. This delimitation is itself a research contribution: it
tells the program *exactly where* the next bet must be placed.

### 6.2 Continuous setting (toward Lie-group refinement)

(Lean: `Examples.lean :: ContinuousWantable, ContinuousPTrans,
scaleByPTrans, scaleHom, scaleHom_injective`.)

The `ContinuousWantable` / `ContinuousPTrans` infrastructure
extends the framework to topological-space Wantables (e.g., `ℝ`
with `complement := Neg.neg`). In this setting:

- A verified `MonoidHom` `scaleHom : ℝˣ →* PTrans ℝ` is injective
  (`scaleHom_injective`), embedding the 1-dimensional Lie group
  `ℝˣ` as a subgroup of `PTrans ℝ`.

- The full `PTrans ℝ` is much larger (includes every odd bijection
  of ℝ, e.g., `x ↦ x³`). The scalings are the *linear* odd
  bijections; the connected-identity component naturally has a Lie
  group structure.

- Translations `x ↦ x + c` do *not* respect complement on ℝ — they
  are excluded by Z/2-equivariance. PTrans is therefore a *strict*
  subgroup of the homeomorphism group.

This is the natural mathematical home for the ROADMAP R6/R7 program:
in continuous Wantable settings, the Lie group structure on PTrans
is available "for free", and the agency postulate's
path-connectedness condition becomes a natural topological
constraint rather than an additional postulate.

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

### 9.1 Comparison to existing reconstruction programs

The framework is one of several programs aiming to *derive* (rather
than *postulate*) quantum-mechanical structure from a smaller set of
operationally or philosophically motivated axioms. A precise
comparison is required if the claim "the framework adds value over
the existing literature" is to be defensible.

**Hardy 2001 (template).** Lucien Hardy's five-axiom reconstruction
— Probabilities, Simplicity, Subspaces, Composite Systems, Continuity
— is the *template* of operational reconstructions: GPTs as the
genus, quantum mechanics as the differentia picked out by Axiom 5
(continuous reversible transformations between pure states). The
present framework adopts Hardy's GPT scaffolding wholesale
(`Perspectival.GPT`, `Perspectival.Hardy`) and our principal positive
contribution at the operational level is the *derivation* of
Hardy's Axiom 5 from a more basic libertarian-agency postulate
(`hardy_axiom5_transitive`, Section 5.1) plus the disconnect
witness for the classical case (`classical_n2_strict_reversible_
path_id_swap_empty`, Section 5.2). Hardy treats continuity as a
postulate; we re-derive it from agency and document the
*classical*-side incompatibility. Where Hardy leaves Axiom 1 and
Axiom 3 as inputs in his original paper, our codebase has formally
proved them (`axiom1_holds`, `axiom3_holds`).

  ✓ verified: our derivation of Axioms 1, 3, 5; Hardy's full
    quantum reconstruction theorem remains, in our framework,
    DERIVABLE-but-not-derived (`Hardy.lean` predicates).
  ○ argued: that libertarian-agency is a stronger philosophical
    motivation than continuity-as-postulate.

**Clifton, Bub, Halvorson 2003 ("CBH"; no-broadcasting).** CBH derive
the qualitative quantum features (no-cloning, no-broadcasting,
no-bit-commitment) from C*-algebraic information-theoretic
constraints. The framework's no-cloning chain (`Distinguish.lean ::
no_cloning_of_distinguishable`, `no_cloning_of_linear_independent`)
recovers the no-cloning half operationally. We do *not* attempt
no-broadcasting in this codebase — `NoBroadcasting.lean` is a
placeholder. The CBH-style derivation imports the C*-algebraic
structure; our derivation imports only linear-algebraic structure.
This is logically weaker (CBH's reading via C* is stronger evidence
for "quantum mechanics is information theory") but is genuinely
performed in our setting without the C*-axioms.

  ✓ verified: no-cloning from distinguishability and from linear
    independence.
  ?  open: no-broadcasting; the C*-algebraic vs. linear-algebraic
    comparison would need its own writeup.

**Markus Müller (algorithmic idealism).** Müller's "algorithmic
idealism" — the universe is the structure of computational
processes, observers as algorithmic agents, physical structure as
the structural shadow of Solomonoff-style induction — is the
*closest* sibling program to ours. We share: ontological priority
of perspective (Müller's observer-centric formalism), rejection of
substance-realism (Müller's third-person ontology only as a
derivative), and the methodological commitment to derive rather than
postulate. We diverge: Müller's foundation is *algorithmic*
(Kolmogorov-complexity-style induction); ours is *libertarian-
agentic* (genuine indeterministic choice, formalized as path-
connectedness of the strict-reversible group, Section 5.2). The
algorithmic foundation is naturally deterministic at the Solomonoff
level; ours is naturally indeterministic. Whether the two foundations
yield equivalent operational predictions is an open
*meta-comparison* question we do not resolve.

  ○ argued: the libertarian-agency divergence from Müller's
    algorithmic foundation; whether this divergence is empirically
    consequential is open.
  ?  open: a formal mapping between Müller's third-person
    derivation and our Wantable bridge would be a valuable target.

**Renou et al. 2021 (real-QM rule-out).** Renou and collaborators
showed experimentally that real-amplitude QM is incompatible with
quantum-network correlations: certain three-source network Bell
scenarios cannot be reproduced by any real-Hilbert-space model
with the standard tensor rule. This is an *empirical* falsification
*within the assumed quantum framework*. Our framework's
corresponding target (TIER1_5_HILBERT.md, Tier 1 #5) is a
*structural* falsification: starting from axioms I–IV strengthened
by `StrictConnectedAgency` and local tomography, real-QM should
fail to be a model. The two results would be complementary:
*nature* is not real-QM (Renou); *the framework's axioms* cannot
be realized by real-QM (our hoped-for extension). At present, our
codebase has the *trivial* triple-no-go (`wantableGPT_not_realQM`,
`wantableGPT_not_quaternionicQM`, `wantableGPT_not_quantum`)
which rules out *all three* non-classical signatures because the
bare `WantableGPT` bridge always lands classical. The non-trivial
content — ruling out real-QM and quaternionic-QM for the
*strengthened* bridge — is open and is the principal Tier 1
follow-up.

  ✓ verified: the trivial no-go for the bare bridge.
  ?  open: the non-trivial structural rule-out parallel to
    Renou's empirical one.

**Other sibling programs (brief).** Masanes–Müller 2011
(reconstructive axioms from invariance), Chiribella–D'Ariano–
Perinotti 2011 ("Informational derivation of QM" via Purification),
Hardy's later "Causaloid" framework, Wilce's Jordan-algebraic
reconstruction, the Brukner–Zeilinger information-theoretic
foundations — each isolates a different operational axiom as the
quantum-distinctive one. The present framework's distinctive
contribution is not the operational axiom (we recover Hardy's
Axiom 5) but the *philosophical reading* of that axiom:
libertarian agency as the substantive content of path-
connectedness, and the corresponding disconnect-on-classical-GPTs
as the formal witness that the reading does technical work.

---

## 10. Predictions

A calibrated catalog of empirical predictions flowing from the
framework is maintained in `PREDICTIONS.md`. We summarize here and
highlight the prediction with the most distinctive testable content.

**Calibration legend** (consistent with `PREDICTIONS.md`):
D = Derived; C = Consistent; S = Suggested; X = Speculative.

| # | Prediction | Status | Comment |
|---|------------|--------|---------|
| P1 | Tsirelson saturation, not Bell saturation | D | Verified experimentally; framework's contribution is the realist-ledger reading (`bound_perspectival`). |
| P2 | No-cloning of distinguishable states | D | Framework-agnostic (`no_cloning_of_distinguishable`). |
| P3 | Continuous reversible transformations between pure states | D, conditional | Conditional on the agency postulate (`hardy_axiom5_transitive`). |
| P4 | N ≤ K (operational dim ≤ state-space dim) | D | `operational_dim_le_state_dim`. |
| P5 | Dark matter is multi-species (multi-sector) | S | Qualitative only; *most distinctive* framework prediction. |
| P6 | Λ as relational artifact | X | Interpretive only. |
| P7 | Fine-tuning as coherence-forcing | X | No quantitative path. |
| P8 | Hard-problem dissolution | D conceptually | Philosophical dissolution, not derivation. |
| P9 | Partial panexperientialism | X | Whitehead-style. |
| P10 | Sharper Bell-style inequalities from observer plurality | S | Frauchiger–Renner-style; testable in principle. |

**The distinctive prediction (P5).** The framework's
`Composition.lean :: Meeting.sum_no_cross` theorem shows that
disjoint-union Wantables admit *no cross-system meetings*:
independent perspectival sectors are *structurally* prohibited from
non-gravitational interactions. If gravity is geometric (acting on
all sectors uniformly as part of the universal patterning of
Axiom IV) but other forces are sector-internal connections (as
Axiom IV reads "forces are connections"), then dark matter should
consist of *multiple* Wantable sectors, distinguished from
baryonic matter by incompatible complement structures.

Concrete experimental signatures (from `PREDICTIONS.md`):

  - **Halo substructure.** Multi-sector dark matter with different
    self-interaction cross-sections per sector produces distinct
    small-scale clustering features (cusp-vs-core morphology;
    satellite-galaxy abundance) that single-species cold dark
    matter cannot mimic.
  - **Cluster kinematics.** Sectors with different
    temperatures/dissipation timescales yield distinct velocity
    dispersions in galaxy-cluster environments.
  - **Power-spectrum scale dependence.** Multi-sector composition
    can give a clustering signal whose scale-dependence diverges
    from the ΛCDM single-fluid prediction.

  S  **Honest qualification.** The prediction is *qualitative* —
     the framework picks out *plurality* of dark sectors as
     natural; quantitative cross-sections, mass ratios, or sector
     count are *not* derived. Sharpening to a quantitative
     prediction would require either an N-sector model
     parametrized by composition data (Axiom III with multiple
     disjoint Wantables) or a Lagrangian-level specification —
     neither present in this codebase. Even so, the *qualitative*
     claim "dark matter is plural, not singular" is a structural
     framework prediction that ΛCDM does not make, and any null
     observation in favor of single-species CDM would constitute
     evidence against the framework.

The remaining predictions P1–P4 are recoverable (or framework-
agnostic) under any reconstruction; the suggestive predictions
P6–P10 are honest interpretive moves rather than derivations. The
program's quantitative honesty is concentrated in P1–P4 and its
philosophical distinctiveness in P5–P10.

---

## 11. Open problems

A catalog of the principal open problems, organised by Tier per
`ORIGINAL_PROMPT.md` and `ROADMAP.md`. Each is annotated with the
codebase artifact most relevant to its closure.

**Tier 1 — Foundational reconstruction.**

  ?  **O.T1.a** Hardy reconstruction in full (`K = N²` selection).
     The remaining cQM-vs-rQM-vs-qQM uniqueness theorem requires
     local-tomography for a genuine GPT tensor (`gptTensor`, not
     yet constructed) plus a connected-reversibles argument that
     rules out the disconnected `O(N)` reversible group of rQM.
     `TIER1_5_HILBERT.md` sketches the chain in detail.
  ?  **O.T1.b** Generalize the n = 2 Birkhoff disconnect (Section
     5.2) to `n ≥ 3`. The structural argument is the same — n!
     connected components in the Birkhoff bijection locus — but
     the Lean formalization requires the `n × n` determinant and
     its sign-of-permutation invariant.
  ?  **O.T1.c** Construct a non-classical GPT in which
     `StrictConnectedAgency` is *non-vacuously* satisfied. The
     natural candidate is a complex-amplitude or qubit Wantable
     refinement; the bare finite-Wantable bridge always lands
     classical (`wantableGPT_classical_dichotomy`).
  ?  **O.T1.d** Derive the ★-algebra picture from axioms I–IV.
     CHSH/Tsirelson is currently imported from Mathlib.
  ?  **O.T1.e** Formalize no-broadcasting in the framework's
     vocabulary. `NoBroadcasting.lean` is a placeholder.

**Tier 2 — Standard-model structure.**

  ?  **O.T2.a** Gauge group `U(1) × SU(2) × SU(3)`. The
     `TIER2_GAUGE_SCOPING.md` note identifies the *one tractable
     step*: a `u(1)`-valued connection one-form on the trivial
     bundle, on the `ContinuousWantable W = ℝ` case where
     `scaleHom : ℝˣ ↪ PTrans ℝ` already embeds the abelian Lie
     subgroup. The non-abelian factors and the specific factor
     count remain open in any axiomatic framework.
  ?  **O.T2.b** Three fermion generations. Open under any known
     framework.
  ?  **O.T2.c** Particle representations (chirality, hypercharge
     assignments, the 16 of `SO(10)`). Open under any known
     framework.
  ?  **O.T2.d** Promote `Meeting W` from a *global* to a *local*
     (sheaf/bundle) structure — the formal home for "meetings
     happen at places."

**Tier 3 — Cosmology.**

  ?  **O.T3.a** Quantitative form of P5 (multi-sector dark
     matter). Currently qualitative only.
  ?  **O.T3.b** Cosmological-constant value. The
     "vacuum-as-absence-of-meetings" reading (P6) gives no
     quantitative path.
  ?  **O.T3.c** Fine-tuning forcing (P7). No quantitative path.
  ?  **O.T3.d** QM/GR unification. The framework provides a
     setting; no technical fix is offered.

**Tier 4 — Foundations of consciousness.**

  ?  **O.T4.a** Formal counterpart to the hard-problem
     dissolution. The reading (matter is how consciousness appears
     under perspectivization) is philosophical, not derivational.
  ?  **O.T4.b** A formal statement of Whitehead-style partial
     panexperientialism (P9).

**Cross-tier.**

  ?  **O.X.a** Move A.H1 entries of `FINDINGS.md` (Hardy axioms 2,
     3, 4 categorizations) from ARGUED to verified or honestly
     downgrade.
  ?  **O.X.b** Move A.P1 (Quine–Rovelli parallel) toward a formal
     category-theoretic statement (e.g., a universal property
     identifying the semantic-relativity and the relational-QM
     limits).
  ?  **O.X.c** Address `WantableGPT` uniqueness: does the
     operational structure *uniquely determine* the GPT given a
     Wantable, or does it admit a family of consistent GPTs?

The critical path to "earning the keep" — per Section 8 — runs
through O.T1.a–c. The framework's *philosophically distinctive*
content is concentrated in P5 and O.T3.a; the framework's
*technically distinctive* current content is the agency → Hardy
Axiom 5 derivation (Section 5.1) together with the Birkhoff
disconnect (Section 5.2).

---

## 12. Status of this draft

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

---

## Appendix A — Latest verified results (session log)

This appendix records, in compact form, the substantive Lean
contributions added in the most recent working sessions. Each entry
is keyed to a Lean theorem name; all are machine-verified (✓) unless
otherwise marked.

**A.1 Strict-agency hierarchy** (`Continuity.lean`).
The three nested path notions referenced in Section 5.2 are now
formal Lean structures:

  ✓ `StatePreservingPath G R₁ R₂` — continuous linear-map path
    with state preservation at every intermediate `t`.
  ✓ `ReversiblePath G R₁ R₂` — path of `Reversible`s.
  ✓ `StrictReversiblePath G R₁ R₂` — path of bijective
    `StrictReversible`s.
  ✓ `StatePreservingAgency`, `ReversibleAgency`,
    `StrictConnectedAgency` — agency classes parametrised by
    each path notion.
  ✓ `HasConnectedAgency.ofStatePreservingAgency` — instance:
    StatePreservingAgency implies the weaker HasConnectedAgency.
  ✓ `continuous_state_preserving_path` — under
    `StatePreservingAgency`, the continuous path stays inside the
    state space the whole time (the R6 improvement over Hardy's
    original Axiom 5).

**A.2 R6 Birkhoff disconnect for Classical n = 2**
(`Classical.lean`). Section 5.2 of the main text; theorems:

  ✓ `n2_disc_det` — the first-column determinant on `V 2 →ₗ V 2`.
  ✓ `n2_disc_det_id = 1`, `n2_disc_det_swap = −1`.
  ✓ `ivt_path_one_to_neg_one` — IVT specialization
    `[0,1] → ℝ` with endpoints `+1` and `−1`.
  ✓ `n2_no_continuous_path_id_to_swap_through_bijections` — the
    IVT-pushed root of `n2_disc_det ∘ γ` on any path id → swap.
  ✓ `n2_disc_det_zero_implies_not_injective` — the bridge from
    `n2_disc_det = 0` to failure of injectivity (using state
    preservation).
  ✓ `classical_n2_no_strict_path_id_to_swap` — combined
    contradiction lemma for any state-preserving bijective
    continuous path from id to swap.
  ✓ `n2_disc_det_path_continuous` — joint continuity of the
    StrictReversiblePath's `γ` pushes through `n2_disc_det`.
  ✓ `classical_n2_strict_reversible_path_id_swap_empty` — the
    main result: no `StrictReversiblePath` from id to swap exists
    on Classical n = 2.
  ✓ `classical_n2_strict_reversible_path_id_swap_nonempty_false`
    — contrapositive form (Nonempty negation).
  ✓ `classical_n2_strict_reversible_path_swap_id_nonempty_false`
    — symmetric direction via path-reversal.
  ✓ `classical_n2_no_two_element_strict_agency` — no
    `StrictConnectedAgency` contains both id and swap.

**A.3 n = 2 enumeration** (`Classical.lean`). Every bijective
state-preserving linear map on `V 2` is exactly id or swap:

  ✓ `classical_n2_bijection_image_vertex0_form` — image of
    vertex 0 is determined by its coordinates.
  ✓ `classical_n2_bijection_image_vertex1_form` — same for
    vertex 1.
  ✓ `classical_n2_det_one_eq_id` — det = +1 forces R = id.
  ✓ (symmetric corollary) — det = −1 forces R = swap.
  ✓ `classical_n2_no_bijective_state_pres_joint_path` — cleaner
    form of the disconnect using only joint continuity at the
    linear-map level.

**A.4 Product-state structure and classical correlation** (`Examples.lean`).
The `productState` construction on Bool × Bool, together with the
`diagonalState` and `antiDiagonalState` examples, makes the
classical-side composition structure concrete:

  ✓ `productState f₁ f₂` — product of two single-system states
    as a state on the product Wantable.
  ✓ `productState_unitFn` — unit of product = product of units.
  ✓ `productState_nonneg`, `productState_in_states` —
    state-axioms preserved.
  ✓ `productState_vertex` — products of vertices = pair vertex.
  ✓ `diagonalState` — uniform on the diagonal of Bool × Bool;
    `diagonalState_left_marginal`, `diagonalState_right_marginal`
    — both marginals are uniform.
  ✓ `diagonalState_ne_productState_uniformBool` — **the
    diagonal state is NOT a product state**: a classical
    correlation that cannot factorise into independent marginals.
    This is the framework's smallest verified instance of
    correlation-without-factorisation, and it sets up the
    contrast with quantum entanglement (which would require a
    further non-classical structure).
  ✓ `diagonalState_in_states` — `diagonalState` is a valid GPT
    state.
  ✓ `diagonalIndicatorLin_on_diagonalState = 1`,
    `antiDiagonalIndicatorLin_on_diagonalState = 0`,
    `diagonalState_distinguishable_antiDiagonalState` — the
    diagonal and antidiagonal classical correlations are
    perfectly distinguishable.

**A.5 Complement subgroup is central** (`Examples.lean`).

  ✓ `complementSubgroup W` — the subgroup of `PTrans W`
    generated by `complement`.
  ✓ Centrality (`example` form, `Examples.lean`):
    `complementSubgroup W ≤ Subgroup.center (PTrans W)`. The
    complement involution commutes with every perspectival
    transformation. This is the formal expression of the fact
    that `complement` is *not* a representative of agency — it is
    a *structural symmetry of every agent*, central in the PTrans
    group, and therefore appears uniformly in every Z/2-
    equivariant perspectival dynamics.

**A.6 Cumulative count.** The codebase as of this appendix has
~140+ machine-verified theorems (cf. `STATUS.md`), no `sorry`s in
the main proof line, and SIX philosophically motivated structural
results that go beyond restating standard GPT content:

  ✓ Hardy Axiom 5 from libertarian agency (Section 5.1).
  ✓ R6 Birkhoff disconnect: classical-side incompatibility with
    strict agency for n=2 (Section 5.2). Formally hypothesis-free.
  ✓ R6 n=3 sign-of-det invariant: even/odd permutation discrimination
    via the 6-term Leibniz formula `n3_disc_det`, with `n3_disc_det_id = 1`,
    `n3_disc_det_swap01 = -1`, and IVT zero-crossing along any
    continuous path. Conditional disconnect via
    `classical_n3_no_strict_path_id_to_swap01_conditional`. (Closure
    needs the `det = 0 ⇒ not injective` lemma.)
  ✓ Triple no-go: bare WantableGPT bridge always lands classical
    (Section 6.1).
  ✓ Vertex-decomposition + structural identification of
    PTrans as Z/2-equivariant permutations (Section 3.1).
  ✓ PatternStableWantable axiom refinement (Ontology.lean):
    typeclass-level expression of Axiom IV's pattern-stability
    commitment, with discriminating `Stable_nontrivial` predicate
    that distinguishes Bool/Bool×Bool/Bool³ (have non-trivial
    pattern stability) from Fin 3 with id-complement (does not).
    Connected to PTrans non-triviality via
    `stable_nontrivial_implies_complement_ne_one`.

These six together form the framework's current load-bearing
formal content. Every other verified theorem is either an
infrastructural lemma or a recasting of standard material.

**A.7 Tier 1 #5 progress (Hardy A4 BOTH halves).**
`Hardy_Axiom4_WantableGPT_dimension` proves dimensions multiply
(`finrank V(W₁ × W₂) = (finrank V W₁) × (finrank V W₂)`).
`Hardy_Axiom4_WantableGPT_state_exists` proves the state-half
existence claim (for any pair of states, a composite state
exists with multiplicatively-factoring unit). Together: Hardy
Axiom 4 is fully *derivable* (not auxiliary) for the WantableGPT
bridge. The bilinear-map packaging is `productStateBilin`.

**A.8 Tier 2 #6 u(1) toy.** The smallest non-trivial Lie-group
gauge instance is now formalized: `gaugeFamily`, `combinedFamily`,
`rescale` in `Examples.lean` realize the "position-dependent
rescaling compensated by a u(1) connection" picture from
`TIER2_GAUGE_SCOPING.md` §7. Reuses the existing `scaleHom`
infrastructure. Does NOT establish anything about non-abelian
factors or specific gauge group selection.

**A.9 R7 algebraic scaffold.** `GroupClosedReversiblePath` and
`GroupClosedAgency` in `Continuity.lean` provide the algebraic
precursor to the Lie-group reversible-dynamics target.
`trivialGroupClosedAgency` shows the structure is non-vacuous.
Full Lie-group bridge (smooth paths, Lie algebra) deferred to
future work with Mathlib `LieGroup` infrastructure.
