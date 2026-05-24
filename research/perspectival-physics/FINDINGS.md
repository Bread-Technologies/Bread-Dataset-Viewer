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
- **O6** Lin-indep wrapper for `no_cloning` (bridge from
  `LinearIndependent ℝ ![v₁, v₂]` to the bilinear-form hypothesis).
  Technical, uses `LinearMap.exists_leftInverse_of_injective`; not
  pursued in this codebase to avoid bookkeeping.

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
