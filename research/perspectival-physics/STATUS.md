# Perspectival Physics — Status Catalog

Live, calibrated record of the research program. Every claim falls into
exactly one of:

- **✓ VERIFIED** — Lean 4 type-checks; proof contains no `sorry`.
- **▲ PARTIAL** — Lean 4 type-checks; proof contains `sorry` placeholders.
  The `sorry` location is documented.
- **○ ARGUED** — informal argument in prose, no formal verification.
  Presumed wrong until verified.
- **✗ STUCK** — attempted and failed; failure mode documented.
- **? OPEN** — not attempted; open in the program.

## Axioms (the inputs)

These are inputs, not results. See `Perspectival/Ontology.lean`.

| Axiom | Encoded | Notes |
|------:|---------|-------|
| I — existence = perspective with directedness | `Existent` structure | Minimal: a perspective is its want; no substrate |
| II — wants are intrinsically relational | `Wantable` class with involutive `complement` | Self-complement (fixed points) not yet excluded |
| III — reality is the structure of meetings | `Meeting`, `Reality := Meeting → Prop` | Bare set; no measure, no probability yet |
| IV — particulars are stable patterns | `Pattern` placeholder | "Stable" requires evolution; not yet defined |

## Verified results so far

| Result | Location | Status |
|-------:|----------|--------|
| Complement is an involution | `Ontology.lean :: Wantable` | ✓ axiomatic |
| Meeting.swap is involutive | `Ontology.lean :: Meeting.swap_swap` | ✓ |
| Complementary symmetry of meeting sides | `Ontology.lean :: complementary_symm` | ✓ |
| Perspectival transformations form a monoid (id, comp, assoc, unit laws) | `Transformations.lean :: PTrans` | ✓ |
| invFun uniqueness from toFun | `Transformations.lean :: invFun_unique` | ✓ |
| PTrans extensionality | `Transformations.lean :: ext` | ✓ |
| Action of PTrans on Meeting is functorial | `Transformations.lean :: actMeeting_id, actMeeting_comp` | ✓ |
| `actMeeting PTrans.complement = Meeting.swap` (PTrans/swap identification) | `Transformations.lean :: actMeeting_complement` | ✓ |
| PTrans action on Meeting is faithful | `Transformations.lean :: actMeeting_faithful` | ✓ |
| Forgetful injective MonoidHom `PTrans W →* Equiv.Perm W` | `Transformations.lean :: toEquivPermHom, toEquivPermHom_injective` | ✓ |
| **Characterization**: `PTrans W` is *exactly* the centralizer of `complement` in `Equiv.Perm W` | `Transformations.lean :: mem_range_toEquivPermHom_iff` | ✓ |
| Disjoint-union Wantable structure (no cross-system meetings) | `Composition.lean :: instWantableSum, Meeting.sum_no_cross` | ✓ |
| Componentwise PTrans on disjoint unions | `Composition.lean :: PTrans.sumMap` | ✓ |
| Spacelike pair of binary perspectival observables → CHSH tuple | `CHSH.lean :: SpacelikePair, toCHSHTuple` | ✓ |
| **Realist case** (commutative *-algebra) ⇒ CHSH expression ≤ 2 | `CHSH.lean :: bound_realist` | ✓ via Mathlib |
| **Perspectival/Tsirelson case** ⇒ CHSH expression ≤ 2√2 | `CHSH.lean :: bound_perspectival` | ✓ via Mathlib |
| GPT data structure (states, effects, unit, probabilities) | `GPT.lean :: GPT` | ✓ |
| Hardy Axiom 1 (Probabilities) — DERIVABLE, formally proved | `Hardy.lean :: axiom1_holds` | ✓ |
| Hardy Axiom 3 (Subspaces) — DERIVABLE, formally proved (weak form) | `Hardy.lean :: axiom3_holds` | ✓ |
| Hardy Axiom 5 (Continuity) — DERIVABLE from agency, formally proved | `Continuity.lean :: hardy_axiom5_transitive` | ✓ |
| Hardy Axioms 2, 4 stated as Lean predicates (AUXILIARY) | `Hardy.lean` | ✓ statement; argued auxiliary |
| **No-cloning theorem** — cross-term vanishing from linearity | `NoCloning.lean :: cross_terms_vanish` | ✓ |
| **No-cloning theorem** — contradiction with distinguishing bilinear form | `NoCloning.lean :: no_cloning` | ✓ |
| **No-cloning from linear independence** (standard formulation) | `NoCloning.lean :: no_cloning_of_linear_independent` | ✓ |
| `fromPTransHom` MonoidHom into LinearMap monoid | `WantableGPT.lean :: fromPTransHom` | ✓ |
| `transformAction φ` permutes vertices: `vertex w ↦ vertex (φ.toFun w)` | `WantableGPT.lean :: transformAction_vertex` | ✓ |
| `fromPTransTransformHom` MonoidHom into Transform monoid | `WantableGPT.lean :: fromPTransTransformHom` | ✓ |
| `fromPTransHom` is injective | `WantableGPT.lean :: fromPTransHom_injective` | ✓ |
| `complementPTrans` is an involution | `WantableGPT.lean :: complementPTrans_sq` | ✓ |
| Bridge respects complement: `fromPTrans complementPTrans = complementAction` | `WantableGPT.lean :: fromPTransHom_complementPTrans` | ✓ |
| Coe instance: PTrans → Transform | `WantableGPT.lean` | ✓ |
| WantableGPT vertices linearly independent | `WantableGPT.lean :: vertex_linear_independent_of_fintype` | ✓ |
| WantableGPT vertex decomposition: `f = ∑ w, f w • vertex w` | `WantableGPT.lean :: vertex_decomposition` | ✓ |
| WantableGPT is the classical simplex on `W` (convex-hull characterization) | `WantableGPT.lean :: state_is_convex_combination_of_vertices` | ✓ |
| WantableGPT vertices form a basis; `finrank (V W) = |W|` | `WantableGPT.lean :: vertexBasis, finrank_V_eq_card` | ✓ |
| **No-go: WantableGPT-from-finite-Wantable is always classical** (`N = K`) | `WantableGPT.lean :: wantableGPT_is_classical` | ✓ |
| **Classical signature explicit**: PerfectWitness family of size `|W|` with `n = finrank V W` | `WantableGPT.lean :: wantableGPT_classical_signature` | ✓ |
| **Quantum signature ruled out**: K ≠ N² for `|W|≥2` | `WantableGPT.lean :: wantableGPT_not_quantum` | ✓ |
| **Real-QM signature ruled out**: 2K ≠ N(N+1) for `|W|≥2` | `WantableGPT.lean :: wantableGPT_not_realQM` | ✓ |
| **Quaternionic-QM signature ruled out**: K ≠ N(2N-1) for `|W|≥2` | `WantableGPT.lean :: wantableGPT_not_quaternionicQM` | ✓ |
| **Classical dichotomy (bundled)**: K = N AND all non-classical Hardy signatures fail | `WantableGPT.lean :: wantableGPT_classical_dichotomy` | ✓ |
| WantableGPT product-composition dimension: `K(W₁ × W₂) = |W₁| · |W₂|` | `WantableGPT.lean :: finrank_V_prod_eq_mul` | ✓ |
| WantableGPT sum-composition dimension: `K(W₁ ⊕ W₂) = |W₁| + |W₂|` | `WantableGPT.lean :: finrank_V_sum_eq_add` | ✓ |
| Concrete classification `PTrans Bool = {1, boolSwap}` | `Examples.lean :: ptrans_bool_classification` | ✓ |
| `SelfComplementary`, `FixedPointFreeComplement` predicates | `Ontology.lean` | ✓ |
| **Even-cardinality theorem**: fixed-point-free complement + finite + linear order ⇒ `|W|` even | `Examples.lean :: card_even_of_fixedPointFree` | ✓ |
| `WantableEquiv W₁ W₂` structure (Wantable isomorphism) | `Examples.lean :: WantableEquiv` | ✓ |
| `WantableEquiv` induces MulEquiv `PTrans W₁ ≃* PTrans W₂` (functoriality) | `Examples.lean :: WantableEquiv.mapPTransMulEquiv` | ✓ |
| Concrete classifications: `PTrans Unit = {1}`, `PTrans Empty = {1}`, `PTrans (Fin 2) = {1, fin2Swap}` | `Examples.lean :: ptrans_unit_classification`, etc. | ✓ |
| `ClosedAgency` class (composition closure refinement of `HasConnectedAgency`) | `Continuity.lean :: ClosedAgency` | ✓ |
| `Reachable` is transitive under `ClosedAgency` | `Continuity.lean :: Reachable.trans` | ✓ |
| `Reversible.comp` (composition of reversible transformations) | `Continuity.lean :: Reversible.comp` | ✓ |
| `path_via_affineLine` — generic affine interpolation path | `Continuity.lean :: path_via_affineLine` | ✓ |
| `singletonAgency` / `pairAgency` — generic builders for `HasConnectedAgency` | `Continuity.lean` | ✓ |
| `StrictReversible` (Reversible + bijective toLin) with `.inv`, `.comp`, identity | `Continuity.lean :: StrictReversible.{id, inv, comp}` | ✓ |
| `Reachable.symm_of_inv_avail` — symmetric Reachable from per-element inverse availability | `Continuity.lean` | ✓ |
| `Reachable.equivalence` — `Reachable` is an `Equivalence` under ClosedAgency + inverse availability | `Continuity.lean` | ✓ |
| `ContinuousWantable` class (Wantable on a topological space with continuous complement) | `Examples.lean :: ContinuousWantable` | ✓ |
| `ContinuousPTrans` structure (PTrans with continuous toFun); id, complement, comp | `Examples.lean :: ContinuousPTrans` | ✓ |
| Wantable instances on ℝ (Wantable + ContinuousWantable) | `Examples.lean` | ✓ |
| `WantableEquiv` is a groupoid (refl/symm/trans, identity laws) | `Examples.lean :: WantableEquiv.{refl, symm, trans, refl_trans, trans_refl}` | ✓ |
| `WantableEquiv` preserves `Fintype.card` and WantableGPT finrank | `Examples.lean :: WantableEquiv.preserves_card, preserves_finrank` | ✓ |
| `scaleByPTrans` — scalings on ℝ as PTrans (commute with negation) | `Examples.lean :: scaleByPTrans` | ✓ |
| **Lie-group embedding** `ℝˣ ↪ PTrans ℝ` as MonoidHom (injective) | `Examples.lean :: scaleHom, scaleHom_injective` | ✓ |
| Linear ℝ → ℝ classification: every injective linear map is `x ↦ a*x` | `Examples.lean` | ✓ |
| `FixedPointFreeComplement (Bool ⊕ Bool)` (sum) and `(Bool × Bool)` (product) | `Examples.lean` | ✓ |
| Self-Transforms form a Monoid | `GPT.lean (instance)` | ✓ |
| Transform composition (`Transform.comp`) | `GPT.lean :: Transform.comp` | ✓ |
| Reachable is reflexive | `Continuity.lean :: Reachable.refl` | ✓ |
| Trivial HasConnectedAgency instance | `Continuity.lean :: trivialAgency` | ✓ |
| Product Wantable structure | `Composition.lean :: instWantableProd` | ✓ |
| Meeting.prodFst / prodSnd / prodMk for product Wantable | `Composition.lean` | ✓ |
| Product Meeting bijection lemmas (`prodFst_prodMk`, `prodSnd_prodMk`) | `Composition.lean` | ✓ |
| Wantable instances on Bool, ℤ, Fin 2, Unit, Empty, Fin 3, Fin 4, products, sums, Option, List, function spaces | `Examples.lean` | ✓ |
| complementTransform squared = id (Transform level) | `WantableGPT.lean :: complementTransform_sq` | ✓ |
| `Wantable.complement` is injective and surjective | `Ontology.lean :: complement_injective, complement_surjective` | ✓ |
| `mk_fromSide` constructor for meetings | `Ontology.lean :: mk_fromSide` | ✓ |
| Meeting W ≃ W via mk_fromSide | `Ontology.lean :: mk_fromSide_side₁_inv` | ✓ |
| Meeting extensionality via side₁ | `Ontology.lean :: Meeting.ext_of_side₁` | ✓ |
| `swap (mk_fromSide w) = mk_fromSide (complement w)` (closed gap) | `Ontology.lean :: Meeting.swap_mk_fromSide` | ✓ |
| Classical n-outcome GPT — full construction | `Classical.lean :: gpt` | ✓ |
| Classical GPT — convex states (std simplex) | `Classical.lean :: states_convex` | ✓ |
| Classical GPT — convex effects | `Classical.lean :: effects_convex` | ✓ |
| Classical GPT — probabilities in [0,1] | `Classical.lean :: prob_in_unit_interval` | ✓ |
| Classical vertices form a distinguishability set | `Classical.lean :: vertex_distinguishability_set` | ✓ |
| Coordinate projections are valid effects | `Classical.lean :: proj_in_effects` | ✓ |
| Vertices pairwise distinguishable via projections | `Classical.lean :: vertices_distinguishable` | ✓ |
| **WantableGPT bridge — full GPT from finite Wantable** | `WantableGPT.lean :: gpt` | ✓ |
| Wantable-complement action on state space | `WantableGPT.lean :: complementAction` | ✓ |
| Complement action preserves states | `WantableGPT.lean :: complementAction_preserves_states` | ✓ |
| Complement action is GPT automorphism | `WantableGPT.lean :: complementTransform` | ✓ |
| GPT transformations preserve unit value | `GPT.lean :: Transform.prob_invariant` | ✓ |
| Trivial HasConnectedAgency instance | `Continuity.lean :: trivialAgency` | ✓ |
| Reversible.id (identity reversible transformation) | `Continuity.lean :: Reversible.id` | ✓ |
| HasConnectedAgency postulate (libertarian agency formalized) | `Continuity.lean :: HasConnectedAgency` | ✓ |
| **Agency ⇒ continuous-path between reachable states** | `Continuity.lean :: continuous_path_of_reachable` | ✓ |
| **Agency ⇒ Hardy Axiom 5 (concrete form)** | `Continuity.lean :: hardy_axiom5_of_agency` | ✓ |
| Distinguishable states are unequal | `Distinguish.lean :: distinguishable_ne` | ✓ |
| States are nonzero | `Distinguish.lean :: state_ne_zero` | ✓ |
| **Distinguishable states are linearly independent** | `Distinguish.lean :: distinguishable_imp_linear_independent` | ✓ |
| Outer-product bilinear form | `Distinguish.lean :: outerForm` | ✓ |
| **No-cloning from distinguishability** (full chain) | `Distinguish.lean :: no_cloning_of_distinguishable` | ✓ |
| **N perfectly distinguishable states ⇒ linear independence** | `Distinguish.lean :: perfect_distinguishable_imp_linear_independent` | ✓ |
| **N ≤ K (operational dim ≤ state space dim)** in finite-dim GPT | `Distinguish.lean :: operational_dim_le_state_dim` | ✓ |

## What is NOT YET done — honest open list

| Target | Tier | Status | Bottleneck |
|--------|------|--------|------------|
| Hardy reconstruction in this language | 1 | ? OPEN | Needs GPT (convex state spaces) — Mathlib has the pieces |
| Tsirelson 2√2 from axioms | 1 | ▲ PARTIAL | Bound is verified given the *-ring picture (`bound_perspectival`). DERIVING the *-ring picture from I–IV remains open |
| No-cloning / no-broadcasting | 1 | ? OPEN | Needs operational composition structure |
| Complex Hilbert space (vs real/quaternionic) | 1 | ? OPEN | Renou-style; needs tensor products in GPT |
| Gauge group U(1)×SU(2)×SU(3) | 2 | ? OPEN | Unknown to anyone from any axiomatic framework |
| Three fermion generations | 2 | ? OPEN | Unknown to anyone |
| Specific particle representations | 2 | ? OPEN | Wigner gives the form; specific reps are empirical |
| Mass hierarchies | 2 | ? OPEN | Empirical input in all known approaches |
| Cosmological constant value | 3 | ? OPEN | Open problem; "category error" claim ARGUED only |
| Dark matter multi-sector prediction | 3 | ? OPEN | Sharp prediction; experimental test pending |
| Fine-tuning forcing | 3 | ? OPEN | Argued; not derived |
| QM/GR unification | 3 | ? OPEN | Framework provides setting; no technical fix yet |
| Hard problem dissolution | 4 | ○ ARGUED | Philosophical move; no formal counterpart |

## Honest meta-assessment

**Strength of the framework so far (this codebase):** the encoded ontology
is mathematically thin. It captures involutive complement + meetings +
group actions on meetings. None of that is uniquely "perspectival" —
it's the formal structure of any relational symmetry. **The philosophical
load is not yet doing technical work.** That gap is the actual research
problem and must be confronted head-on.

**Structural identifications now formalized.** The framework's
ostensibly novel structures reduce to well-known mathematics: `Meeting W`
is in canonical bijection with `W` (`mk_fromSide` is an Equiv); `PTrans W`
is *exactly* the centralizer of the complement involution inside the
permutation group `Equiv.Perm W` (`mem_range_toEquivPermHom_iff`); the
PTrans-level complement, acting on meetings, is identically the swap
(`actMeeting_complement = Meeting.swap`). These are clarifying
deflations: the perspectival vocabulary picks out no new mathematics
beyond Z/2-equivariant permutations. The research question is whether
*additional* postulates beyond I–IV can pick out specifically quantum
mathematics, not whether the bare ontology already does so.

**No-go for the bare ontology (`wantableGPT_is_classical`).** The
WantableGPT-from-finite-Wantable construction always satisfies
`N = K = |W|` — the Hardy *classical* signature. There is therefore
*no path* to non-classical / quantum structure that goes purely
through Wantable + WantableGPT.gpt. Any derivation of quantum
structure must come from additional postulates: continuous reversible
agency (Continuity.lean's `HasConnectedAgency`), composition rules
beyond disjoint union (Hardy Axiom 4 in non-placeholder form), or
infinite-dimensional / non-finite Wantable structure. This narrows
the research target sharply.

**What would constitute the framework "earning its keep":**
- A theorem of the form: *axioms I–IV (+ minimal compositional postulates)
  imply some Hardy axiom*, derived non-trivially.
- A toy model where the perspective-wanting vocabulary picks out a
  specific GPT (e.g., qubit) that realist axioms don't.
- A sharp testable prediction not derivable from existing reconstructions.

**Until one of those lands, the program has not yet justified itself
technically.** That is the honest position and the working target.
