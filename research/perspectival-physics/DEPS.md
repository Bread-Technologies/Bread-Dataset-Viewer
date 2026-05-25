# Module Dependency Map

How the 12 Lean modules in `Perspectival/` depend on each other and
what each contributes.

## Dependency graph (text)

```
Ontology.lean       ← foundation (axioms I-IV as types)
   ↑
   ├── Transformations.lean    (PTrans as Group, MulAction on Meeting)
   │       ↑
   │       └── Composition.lean (disjoint-union Wantable, no-cross-system)
   │
   └── (used everywhere)

CHSH.lean           ← Mathlib's CHSH/Tsirelson
   ↑
   └── (independent — depends only on Ontology + Mathlib.Algebra.Star.CHSH)

GPT.lean            ← convex state spaces, effects
   ↑
   ├── Hardy.lean       (Axioms 1-5 as predicates; axiom1_holds, axiom3_holds)
   │     ↑
   │     └── Continuity.lean (Hardy Axiom 5 from libertarian agency)
   │
   ├── Distinguish.lean (distinguishability ↔ linear independence)
   │     ↑
   │     └── (Hardy, NoCloning, GPT)
   │
   └── Classical.lean   (concrete n-outcome instance)
         ↑
         ├── Examples.lean        (worked end-to-end demos)
         └── NoBroadcasting.lean  (classical broadcaster, quantum gap)

NoCloning.lean      ← linear-algebra no-cloning (TensorProduct + linearity)
   ↑
   └── Distinguish.lean (chains to no_cloning_of_distinguishable)
```

## What each module contributes

### Foundation layer

**`Ontology.lean`** (50 LOC)
Axioms I–IV as Lean types:
- `Wantable W` — Axiom II: involutive complement.
- `Existent W`, `Meeting W` — Axioms I, III.
- `Reality W` — collective form of Axiom III.
- `Pattern W` — placeholder for Axiom IV (stability requires dynamics).
- `Meeting.swap`, `swap_swap`, `complementary_symm`.

**`Transformations.lean`** (100 LOC)
Axiom IV's group-theoretic carrier:
- `PTrans W` — perspectival transformations (complement-respecting
  self-bijections).
- Group laws: `id`, `comp`, `inv`, all unit/assoc/cancel laws.
- `Group (PTrans W)` instance.
- `MulAction (PTrans W) (Meeting W)` instance.

**`Composition.lean`** (95 LOC)
Disjoint-union composition:
- `instWantableSum` — complement acts component-wise.
- `Meeting.sum_no_cross` — structural no-signaling.
- `PTrans.sumMap` — component-wise transformations.

### CHSH/Tsirelson bridge

**`CHSH.lean`** (135 LOC)
Bridge to Mathlib's CHSH module:
- `BinaryObservable` — self-adjoint involution in a *-ring.
- `SpacelikePair` — four binary observables with cross-commutations.
- `bound_realist` — commutative case ≤ 2.
- `bound_perspectival` — general case ≤ 2√2 (Tsirelson).

### Generalized Probabilistic Theory

**`GPT.lean`** (75 LOC)
GPT data structure (states, effects, unit, probabilities).

**`Hardy.lean`** (190 LOC)
Hardy 2001's five axioms as predicates on GPTs:
- `Axiom1_Probabilities` — `axiom1_holds` (✓ derived).
- `Axiom3_Subspaces` — `axiom3_holds` (✓ derived).
- `Axiom2_Simplicity`, `Axiom4_Composite`, `Axiom5_Continuity` — stated.
- `Distinguishable`, `DistinguishabilitySet`, `HasDimensionN`.

**`Distinguish.lean`** (175 LOC)
Distinguishability ↔ linear independence:
- `distinguishable_ne`, `state_ne_zero`.
- `linear_dependent_states_eq` (converse).
- `distinguishable_imp_linear_independent`.
- `outerForm` (bilinear forms from functionals).
- `no_cloning_of_distinguishable`.
- `PerfectWitness`, `perfect_distinguishable_imp_linear_independent`.
- `operational_dim_le_state_dim` (N ≤ K).

**`Continuity.lean`** (170 LOC)
Libertarian agency → Hardy Axiom 5:
- `Reversible`, `HasConnectedAgency`, `Reachable`.
- `continuous_path_of_reachable`.
- `hardy_axiom5_of_agency`, `hardy_axiom5_pure_states`,
  `hardy_axiom5_transitive`.
- `PureState`.

### Concrete instances and applications

**`Classical.lean`** (175 LOC)
The n-outcome classical GPT instance:
- `Classical.V n`, `unitFn`, `states`, `effects`.
- `states_convex`, `effects_convex`, `prob_in_unit_interval`.
- `Classical.gpt n` — full GPT instance.
- `vertex`, `proj`, `vertex_in_states`, `perfectWitness`,
  `vertex_linear_independent`.

**`NoCloning.lean`** (80 LOC)
Linear-algebra no-cloning:
- `IsLinearCloner`, `cross_terms_vanish`, `no_cloning`.

**`NoBroadcasting.lean`** (85 LOC)
Classical broadcaster + quantum gap:
- `IsBroadcaster`, `classicalBroadcaster`,
  `basisFun_eq_vertex`, `classicalBroadcaster_basisFun`.

**`Examples.lean`** (110 LOC)
End-to-end demonstrations:
- Boolean Wantable, classical 2-outcome GPT, 3-simplex
  linear independence, no-cross-system meetings, `boolSwap`.

## Recent additions (post-bridge)

Since the initial bridge (WantableGPT.lean), several modules have been
deepened:

- `Ontology.lean` now contains `SelfComplementary`,
  `FixedPointFreeComplement` predicates, `Meeting.ext_of_side₁` (closing
  a documented gap), `Meeting.swap_mk_fromSide`.
- `Transformations.lean` adds `toEquivPermHom` (`PTrans W →* Equiv.Perm W`),
  `mem_range_toEquivPermHom_iff` (the *characterization*: PTrans =
  Centralizer of complement), `actMeeting_complement = swap`,
  `actMeeting_faithful`, `actReality` (PTrans action on Reality with full
  lattice-operation preservation).
- `WantableGPT.lean` adds the **triple no-go theorem**
  (`wantableGPT_is_classical`, `wantableGPT_not_quantum`,
  `wantableGPT_not_realQM`, `wantableGPT_not_quaternionicQM`, bundled
  as `wantableGPT_classical_dichotomy`); `vertexBasis`,
  `finrank_V_eq_card`, composition-dimension theorems
  `finrank_V_prod_eq_mul` and `finrank_V_sum_eq_add`;
  `exists_two_distinguishable`, `wantableGPT_classical_signature`,
  `vertex_perfectly_distinguishable`, `vertex_injective`,
  `vertex_image_card`, `zero_in_effectVec`, `one_in_effectVec`,
  `effectVec_eq_hypercube`.
- `Continuity.lean` adds `Reversible.comp`, `ClosedAgency` (closure
  refinement), `Reachable.trans`, `Reachable.apply_available`,
  `path_via_affineLine`, `singletonAgency`/`pairAgency`,
  `StrictReversible` (with `.id`, `.inv`, `.comp`, `inv_comp`,
  `comp_inv`, `comp_toLin`), `Reachable.symm_of_inv_avail`,
  `Reachable.equivalence`, `trivialAgency_inv_avail`.
- `Classical.lean` adds `vertex_decomposition`, `vertices_span`.
- `Examples.lean` adds `WantableEquiv` (Wantable iso, with refl/symm/trans
  groupoid structure), `mapPTransMulEquiv` (PTrans iso induced from
  WantableEquiv), concrete classifications
  `ptrans_bool_classification`, `ptrans_fin2_classification`,
  `ptrans_unit_classification`, `ptrans_empty_classification`,
  `card_even_of_fixedPointFree` (even-cardinality theorem),
  `ContinuousWantable`/`ContinuousPTrans` (topological refinement, with
  ℝ instance).

## v2 architecture modules

The v2 architectural correction (Tier A + Tier B) introduced new
modules that constitute the framework's two-tier formalization:

- `TierA.lean` (~700 lines) — Want, Existent, Meeting, MeetingStatus,
  Reality, RealitySuccessor, ActualizationMap, past/future,
  no_return_to_potential, WBT_structural_shadow. The Tier A
  irreversible foundation.

- `TierB.lean` (~1700 lines) — BracketedTransition, AtSeam,
  DefiniteConfig + permutation action, TrajectoryStep dichotomy,
  measurement_is_actualization, RealityChain + RealityChain'
  (plain + strict chains), full count algebra
  (actualizationCount, bracketedCount, length), chain monoid laws,
  iff theorems (`ne_iff_pos_count`, `eq_iff_zero_count`).

- `Decoherence.lean` (~2400 lines) — Seam 4 formal correlate.
  Trajectory algebra (actualizationRate, trajectoryComplexity),
  regime characterizations, monoid morphism content,
  DecoherenceEquivalent + congruence, loop submonoid algebra,
  coherent-kernel characterization, anti-realism witnesses,
  Boltzmann brain dissolution shadow, super-certificate.
  Depends on TierA + TierB.

- `Dichotomy.lean` (~1100 lines) — v2-classical-vs-quantum dichotomy
  certificate, framework_v2_certificate, framework_v2_extended_certificate,
  R7 instance evidence.

- `Continuity.lean` (~1500 lines) — agency hierarchy, OneParameterFamily,
  MultiAxisAgency, SmoothConnectedAgency scaffold, R7_Conjecture,
  Hardy A5 derivation pipeline.

## Reading order

For a first pass:
1. `Ontology.lean` — see the axioms.
2. `CHSH.lean` — see the Tsirelson bridge.
3. `Continuity.lean` — see the framework's distinctive contribution.
4. `Classical.lean` — see a concrete instance.
5. `Examples.lean` — see them combine.

Documentation order:
1. `README.md` — orientation.
2. `STATUS.md` — verified-results scoreboard.
3. `FINDINGS.md` — honest commentary.
4. `CONCLUSIONS.md` — external-reader summary.
5. `PREDICTIONS.md` — empirical content.
6. `LINEAGE.md` — philosophical anchors.
7. `PAPER_DRAFT.md` — publication-target writeup.
