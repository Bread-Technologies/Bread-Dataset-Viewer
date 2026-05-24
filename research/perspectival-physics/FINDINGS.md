# Findings — Honest Research Log

A running, calibrated record. Read alongside `STATUS.md` (per-file)
and `PAPER_DRAFT.md` (writeup form).

## Verified results (no `sorry`)

### Ontology & structure

- **F.O1** `Wantable` involution structure; `Meeting` swap involution;
  `Perspective`/`Existent` as types. (`Ontology.lean`)
- **F.O2** `PTrans` is a verified `Group` instance: identity,
  composition, inverses, all laws including `inv_mul_cancel`.
  (`Transformations.lean`)
- **F.O3** `PTrans` acts functorially on `Meeting`.
  (`Transformations.lean`)
- **F.O4** Disjoint-union `Wantable`; structural no-cross-system
  meetings (`Meeting.sum_no_cross`). (`Composition.lean`)
- **F.O5** Component-wise `PTrans` on disjoint unions.
  (`Composition.lean`)

### CHSH / Tsirelson bridge

- **F.C1** `bound_realist`: in a commutative ordered *-algebra over ℝ,
  the CHSH expression is ≤ 2. (`CHSH.lean` via Mathlib's
  `CHSH_inequality_of_comm`.)
- **F.C2** `bound_perspectival`: in a general ordered *-algebra over ℝ,
  the CHSH expression is ≤ 2√2. (`CHSH.lean` via Mathlib's
  `tsirelson_inequality`.)
- **F.C3** Identification of the philosophical hinge: commutativity ↔
  observer-independent joint ledger of facts. Rejecting the latter
  forces the Tsirelson bound.

### No-cloning

- **F.N1** `cross_terms_vanish`: a linear cloner forces the cross
  terms `v₁⊗v₂ + v₂⊗v₁` to be zero. (`NoCloning.lean`)
- **F.N2** `no_cloning`: contradicted by any bilinear form `B` with
  `B v₁ v₂ + B v₂ v₁ ≠ 0`. (`NoCloning.lean`)
- **F.N3** `outerForm`: outer product of two functionals as a bilinear
  form. (`Distinguish.lean`)
- **F.N4** `no_cloning_of_distinguishable`: full operational chain —
  if two states in `S` are perfectly distinguishable by some effect,
  no linear cloner can exist on `S`. (`Distinguish.lean`)

### GPT framework and Hardy axioms

- **F.G1** GPT data structure (`GPT.lean`); classical n-outcome
  instance fully constructed (`Classical.lean`).
- **F.G2** `axiom1_holds`: Hardy Axiom 1 (Probabilities) is
  DERIVABLE and machine-verified. (`Hardy.lean`)
- **F.G3** Vertices of the n-simplex as concrete pure states with
  coordinate-projection witnesses. (`Classical.lean`)
- **F.G4** `vertex_linear_independent`: concrete classical instance
  of the abstract `perfect_distinguishable_imp_linear_independent`.

### Distinguishability ↔ linear-algebraic structure

- **F.D1** `distinguishable_ne`: distinguishable ⇒ unequal.
- **F.D2** `state_ne_zero`: states are nonzero.
- **F.D3** `distinguishable_imp_linear_independent`: pairwise
  distinguishability ⇒ linear independence.
- **F.D4** `linear_dependent_states_eq`: converse — linearly
  dependent states are equal. Together with D3, gives:
  *in a GPT, two states are linearly independent iff they are unequal*.
- **F.D5** `perfect_distinguishable_imp_linear_independent`: a finite
  family of states with a Kronecker effect family is linearly
  independent.
- **F.D6** `operational_dim_le_state_dim`: in finite-dim GPT,
  N perfectly distinguishable states ⇒ state space has dimension ≥ N.

### Libertarian agency → Hardy Axiom 5

- **F.A1** `HasConnectedAgency`: formalization of the libertarian-
  agency postulate as a Lean class.
- **F.A2** `continuous_path_of_reachable`: continuous path between
  reachable states. (`Continuity.lean`)
- **F.A3** `hardy_axiom5_of_agency`: from agency + reachability,
  recover Hardy Axiom 5 in concrete form (continuous path of linear
  maps from identity to transformation realizing the reachability).
- **F.A4** `hardy_axiom5_pure_states`: pure-state restriction.
- **F.A5** `hardy_axiom5_transitive`: full Hardy Axiom 5 from
  agency + transitivity on pure states.

## Argued (prose) — presumed wrong until verified

- **A.H1** Hardy Axioms 2, 3, 4 categorizations (auxiliary, derivable,
  auxiliary respectively) — prose only.
- **A.P1** The Quine–Rovelli parallel (semantic ↔ physical ontological
  relativity) — philosophical, not derivational.
- **A.P2** Hard-problem dissolution; Λ-as-category-error; partial
  panexperientialism — interpretive moves in `LINEAGE.md` and
  `PREDICTIONS.md`.

## Open (not attempted, or stuck)

- **O1** Deriving the *-algebra picture from I–IV. The CHSH bridge
  imports it.
- **O2** Deriving complex (vs real/quaternionic) Hilbert space.
- **O3** Deriving the multi-sector dark-matter prediction at
  *quantitative* level. Qualitative form is argued in `PREDICTIONS.md`.
- **O4** Cosmological constant value, fine-tuning forcing — likely
  not achievable from these axioms alone.
- **O5** Gauge group U(1)×SU(2)×SU(3); three fermion generations.
  Open in any axiomatic framework.
- **~~O6~~** ✓ **CLOSED.** Lin-indep wrapper for `no_cloning` is
  now `no_cloning_of_linear_independent` in `NoCloning.lean`. The
  standard formulation (linear independence ⇒ no cloner) is verified
  via dual-functional extraction.

## The metaphysical→operational bridge (significant progress)

The `WantableGPT.lean` module formalizes a bridge between the two
structural levels. **The bridge is no longer just a partial action —
it's a verified injective MonoidHom.**

Specifically:

  ✓ Given a finite Wantable W, `gpt W` constructs a full GPT.
  ✓ `complementAction W` is a verified linear involution on the
    state space.
  ✓ `complementTransform`: the complement-action lifts to a full
    GPT.Transform automorphism.
  ✓ `fromPTrans φ`: every PTrans (metaphysical transformation)
    induces a GPT.Transform (operational transformation).
  ✓ `fromPTransHom`: the lifted map PTrans W → (V W →ₗ V W) is a
    Mathlib MonoidHom (identity preserved, multiplication preserved).
  ✓ `fromPTransHom_injective`: the MonoidHom is injective; distinct
    metaphysical transformations give distinct operational ones.

Together these show: **the metaphysical group PTrans W is faithfully
embedded in the operational monoid of linear maps on the state space.**
The metaphysical structure is not just *connected to* the operational
structure but *fully recoverable from it* via the injection.

This closes a substantial portion of the framework's central
technical claim. The remaining gap: showing the operational structure
*uniquely determines* the choice of GPT (rather than admitting many
GPTs consistent with a given Wantable), which is the OPEN question
about determinism vs. permissiveness of the bridge.

## The framework's two levels — and the gap between them (qualified)

The codebase has *two structurally distinct levels* that the framework
claims should be unified:

**Metaphysical level** (`Ontology`, `Transformations`, `Composition`).
Types describing perspective, wanting, meeting. Group-theoretic
transformation structure. Carrier: `Wantable W` for some `W`.

**Operational level** (`GPT`, `Hardy`, `Distinguish`, `Continuity`,
`Classical`, `NoCloning`, `NoBroadcasting`). Probabilistic structure
with convex state spaces, linear algebra, effects. Carrier: `GPT V`
for a real vector space `V`.

These two levels are *independently coherent* — each is internally
consistent and has its own verified theorems. They share the
`Ontology` foundation (the `Wantable` axioms motivate the operational
notions in prose), and the CHSH module imports both Mathlib's
operator-algebra side and our `Wantable`-derived `BinaryObservable`,
but the **bridge in the strong sense** — showing that the operational
structure *emerges* from the metaphysical — is not formalized.

What would such a bridge look like? A construction that, given a
`Wantable W` (possibly with additional postulates), *produces* a
concrete `GPT V` whose states correspond to some natural notion of
"perspective" on `W`, whose effects come from `W`'s complement
structure, etc. This is the framework's central technical claim
(Axiom IV: matter is patterning of perspectival transformations);
formalizing it is the natural Tier 1+ research target.

This gap is the framework's honest structural limitation. Both levels
do real work; they don't yet *unify*. ROADMAP R6 and R7 are the path
toward closing this gap.

### Bridge now built; bridge now also delimited

**Update.** `WantableGPT` (verified) provides a concrete bridge: for
any finite Wantable `W`, the construction `WantableGPT.gpt W` is a
machine-verified GPT instance whose vertices, distinguishability set,
and PTrans-induced automorphisms are all formally derived. So the
"strong-bridge" question has *partial* affirmative resolution.

But the same module now also contains a **triple no-go theorem**
(`wantableGPT_classical_dichotomy`): the bridge always lands on
classical structure — `N = K = |W|`, with `K = K_A · K_B` for product
composition and `K = K_A + K_B` for sum composition; and the three
canonical non-classical Hardy signatures (quantum `K=N²`, real-QM
`2K=N(N+1)`, quaternionic-QM `K=N(2N-1)`) are *each* formally ruled
out for `|W| ≥ 2`. So the bridge exists, but it cannot, by itself,
deliver any non-classical structure.

The ROADMAP R6/R7 program — strengthening the agency postulate to
force quantum-like path-connectedness — is the next bet *precisely
because* the bare ontology has been shown to be insufficient.
Furthermore, `path_via_affineLine` reveals that "path-connectedness"
in `HasConnectedAgency` is cheap (always satisfiable for topological
V); the substantive content of R6 is the *availability set* (which
transformations are admissible), not the connectedness itself.

## Structural deflations (clarifying)

Two clarifying deflations have been formally proven:

- `Meeting W ≃ W` via `mk_fromSide` (Ontology). A "meeting" is not
  a richer thing than a "want"; the two are in canonical bijection.
- `PTrans W` is *exactly* the centralizer of the `complement`
  involution inside `Equiv.Perm W` (Transformations). The PTrans
  group is not a novel algebraic structure beyond Mathlib's
  permutation group; it is the standard Z/2-equivariant subgroup.

These are not weaknesses but clarifications: the framework's
vocabulary picks out a specific, well-understood mathematical object.
The interesting research question is whether *additional* postulates
on top of I–IV can pick out non-classical mathematics; the bare
ontology, as the no-go and the deflations together establish, cannot.

## Continuous setting (path toward R6/R7)

The `ContinuousWantable` / `ContinuousPTrans` refinement (Examples.lean,
verified) packages Wantable on a topological space with continuous
complement, and the corresponding PTrans whose `toFun` is continuous.

A concrete observation in this setting: `Wantable ℝ` (with
`complement := Neg.neg`) admits not just `{1, complement}` but also
all scaling maps `x ↦ a*x` for `a ≠ 0` as elements of `PTrans ℝ`
(verified: `scaleByPTrans`). The PTrans group on ℝ contains
`ℝˣ` (the multiplicative group of nonzero reals — a 1-dimensional Lie
group). This is the first concrete realization in the codebase that
*infinite / topological Wantables naturally support Lie-group
structure on PTrans*, where finite Wantables only support finite
(discrete) subgroup structure.

This is the natural setting in which to attempt R6/R7 — strengthening
agency to force path-connectedness — because path-connectedness
is automatic in continuous Lie groups, whereas it must be added as
a postulate over finite/discrete carriers.

## Clarifications and limitations

### L1. Scope of `no_cloning`

`no_cloning` and `no_cloning_of_distinguishable` require the set `S`
to contain `v₁`, `v₂`, AND `v₁ + v₂`. For normalized state spaces
(simplices, density-matrix spaces) this is generically false:
`v₁ + v₂` has unit-functional value 2, not 1, so it's not a state.

The theorems should therefore be read as facts about **linear-algebra
cloners on the linear span of states**, not about cloners restricted
to the normalized state space. The standard quantum no-cloning
theorem (Wootters–Zurek) uses unitarity + ancilla and is a different
statement; the framework currently formalizes only the underlying
linear-algebra impossibility, which is logically weaker.

This is the kind of subtlety honest calibration is for. The Lean
result is what it is; the framework's *reading* (two-sided wanting
forbids isolation) is metaphorically apt but the literal theorem is
the pure-linearity one.

### L2. Tsirelson bound — interpretation vs. derivation

`bound_perspectival` uses `Mathlib.Algebra.Star.CHSH`'s
`tsirelson_inequality`. The mathematical content is Mathlib's; the
framework's contribution is the *identification* of which algebraic
hypothesis is the realist hinge (commutativity ↔ joint ledger). We
do not derive the *-algebra picture from I–IV; we import it.

### L3. Hardy Axiom 5 derivation — easy direction only

`hardy_axiom5_of_agency` proves: from agency (formalized as path-
connectedness of the transformation group), Hardy Axiom 5 follows
by direct construction. The HARD direction — that libertarian
agency forces path-connectedness, not mere richness — is not in this
codebase. The agency postulate `HasConnectedAgency` is the input,
not a theorem.

## Meta-assessment

**What is technically distinctive about the framework, given the
verified results.** The cleanest distinctive contribution is the
*agency → continuity* derivation (F.A1–F.A5). It shows that the
framework's philosophical commitment to libertarian agency, when
formalized as path-connectedness of the reversible-transformation
group, yields Hardy Axiom 5 by direct construction. This is the
framework's first machine-verified result that goes beyond restating
standard operational content.

**What is technically NOT distinctive.** The CHSH/Tsirelson bridge,
no-cloning, and the dimension inequality F.D6 are framework-agnostic
in their proofs — any reconstruction can claim them. The framework
provides interpretation (commutativity ↔ joint ledger; two-sided
wanting ↔ no-cloning; perfect distinguishability ↔ linear
independence), not unique proof power.

**The honest research bottleneck going forward.**

1. Move A.H1 entries → verified, by proving Hardy Axioms 3, 5
   derivable from I–IV in the same way F.A5 derived Axiom 5 from
   agency.
2. Move O5 from "not pursued here" to "tractable target" by
   identifying any new constraint the framework forces. Currently
   none is known.
3. Move A.P1 toward a formal theorem connecting Quinean ontological
   relativity to Rovelli's relational QM at the level of category-
   theoretic universal properties (speculative).

The verified-results scoreboard is real and growing. The
philosophically distinctive predictions remain mostly in the
Suggested/Speculative columns (see `PREDICTIONS.md`). That is the
honest current state.
