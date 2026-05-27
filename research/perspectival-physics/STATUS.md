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
| `WantableEquiv` preserves classical dichotomy (full triple-no-go bundle) | `Examples.lean :: WantableEquiv.preserves_classical_dichotomy_full` | ✓ |
| `WantableEquiv` preserves `not_quantum`/`not_realQM`/`not_quaternionicQM` | `Examples.lean :: WantableEquiv.preserves_not_quantum`, etc. | ✓ |
| `WantableEquiv.sumMap` / `WantableEquiv.prodMap` | `Examples.lean` | ✓ |
| `wantableGPT_dim_prod` / `wantableGPT_dim_sum` (composite-dim restatements) | `WantableGPT.lean` | ✓ |
| `wantableGPT_trivial_dim` (\|W\|=1 ⇒ dim=1) / `wantableGPT_empty_dim` (\|W\|=0 ⇒ dim=0) | `WantableGPT.lean` | ✓ |
| `wantableGPT_dim_pos` — non-empty Wantable has positive WantableGPT dim | `WantableGPT.lean` | ✓ |
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

## R6 strengthened-agency framework (this session)

The R6 program (strengthening the agency postulate so path-connectedness
forces non-classical reversible dynamics) was substantially advanced.
A four-level hierarchy of agency postulates was formalized, and the
n=2 classical disconnect theorem was proven *hypothesis-free*. Each
entry below carries an (a/b/c/d) calibration tag per ORIGINAL_PROMPT §7.

| Result | Location | Calibration |
|-------:|----------|-------------|
| `StatePreservingPath G R₁ R₂` — continuous linear-map path with state preservation at every t | `Continuity.lean :: StatePreservingPath` | ✓ (a) |
| `StatePreservingAgency G` — every pair of avail reversibles connected by a StatePreservingPath | `Continuity.lean :: StatePreservingAgency` | ✓ (a) |
| `HasConnectedAgency.ofStatePreservingAgency` — SPA strengthens HCA | `Continuity.lean` | ✓ (a) |
| `continuous_state_preserving_path` — under SPA, the path of states stays inside the state space | `Continuity.lean` | ✓ (a) |
| `StatePreservingPath.{id, reverse, const, value_in_states, start_preserves_states, finish_preserves_states}` | `Continuity.lean` | ✓ (a) |
| **KEY R6 OBSERVATION** (verbal): convex `G.states` makes affine interpolation auto-state-preserving, so SPA alone is too weak | inline comment in `Continuity.lean` | ○ (b) — argued, but motivates the stronger hierarchy |
| `ReversiblePath G R₁ R₂` — each γ(t) is a Reversible (continuous, state-preserving, unit-preserving) | `Continuity.lean :: ReversiblePath` | ✓ (a) |
| `ReversiblePath.{toStatePreservingPath, id, const}` | `Continuity.lean` | ✓ (a) |
| `StrongConnectedAgency G` — every pair of avail Reversibles connected by a ReversiblePath | `Continuity.lean :: StrongConnectedAgency` | ✓ (a) |
| `StrictReversiblePath G R₁ R₂` — each γ(t) is a *bijection* (the strongest R6 condition) | `Continuity.lean :: StrictReversiblePath` | ✓ (a) |
| `StrictReversiblePath.{toReversiblePath, id}` | `Continuity.lean` | ✓ (a) |
| `StrictConnectedAgency G` — substantive R6 condition (avail StrictReversibles connected by StrictReversiblePaths) | `Continuity.lean :: StrictConnectedAgency` | ✓ (a) |
| `trivialStrictAgency`, `trivialStrictAgency_reachable_iff` | `Continuity.lean` | ✓ (a) |

## R6 Birkhoff disconnect — Classical n=2 (this session)

The substantive new theorem: on the classical n=2 GPT, no continuous
path of bijective state-preserving linear maps connects `id` and `swap`.
This is proved with **no continuity hypothesis** (auto-continuity is
derived from the joint continuity field of `StrictReversiblePath`).
No other GPT reconstruction is known to have a Lean-formalized version
of this discreteness phenomenon.

| Result | Location | Calibration |
|-------:|----------|-------------|
| `swapLin`, `swapLin_{vertex_zero, vertex_one, swapLin, preserves_states, preserves_unit, bijective, continuous}` | `Classical.lean` | ✓ (a) |
| `swapReversible`, `swapStrictReversible`, `swapReversible_ne_id` | `Classical.lean` | ✓ (a) |
| `n2_disc_det` — discrete determinant `R(v0) 0 − R(v1) 0` for V 2 | `Classical.lean :: n2_disc_det` | ✓ (a) |
| `n2_disc_det_id = 1`, `n2_disc_det_swap = -1` | `Classical.lean` | ✓ (a) |
| `ivt_path_one_to_neg_one` — IVT specialization for `[0,1] → ℝ` going `1 → −1` | `Classical.lean` | ✓ (a) |
| `n2_no_continuous_path_id_to_swap_through_bijections` — any continuous path id→swap hits det = 0 | `Classical.lean` | ✓ (a) |
| `n2_disc_det_zero_implies_not_injective` — det = 0 on state-preserving R forces non-injective R | `Classical.lean` | ✓ (a) |
| `classical_n2_no_strict_path_id_to_swap` — combination of the chain (state-preserving + bijective + path id↔swap ⇒ False) | `Classical.lean` | ✓ (a) |
| `n2_disc_det_path_continuous` — auto-continuity of det along a jointly-continuous path | `Classical.lean` | ✓ (a) |
| `classical_n2_no_strict_reversible_path` — hypothesis-free for given path (with explicit cont. hyp.) | `Classical.lean` | ✓ (a) |
| **`classical_n2_strict_reversible_path_id_swap_empty` — R6 FINAL: no `StrictReversiblePath` from id to swap on Classical n=2 (no hypotheses)** | `Classical.lean` | ✓ (a) **framework-distinctive** |
| `classical_n2_strict_reversible_path_id_swap_nonempty_false` — contrapositive form | `Classical.lean` | ✓ (a) |
| `classical_n2_strict_reversible_path_swap_id_nonempty_false` — reverse direction | `Classical.lean` | ✓ (a) |
| `classical_n2_no_two_element_strict_agency` — no StrictConnectedAgency on n=2 containing both id and swap | `Classical.lean` | ✓ (a) |
| `classical_n2_id_avail_implies_swap_not_avail`, `classical_n2_trivial_agency_id_avail` | `Classical.lean` | ✓ (a) |
| `classical_n2_state_preserving_first_coord_bound{,_v1}` — R(vertex i) 0 ∈ [0,1] for state-preserving R | `Classical.lean` | ✓ (a) |
| `classical_n2_injective_distinct_images`, `classical_n2_surjective_vertex_image` | `Classical.lean` | ✓ (a) |
| `classical_n2_image_vertex_{zero,one}_in_states`, `classical_n2_state_eq_combo` | `Classical.lean` | ✓ (a) |
| `classical_n2_bijection_image_vertex{0,1}_form` — image-of-vertex decomposition under state preservation | `Classical.lean` | ✓ (a) |
| **`classical_n2_det_one_eq_id` — every state-preserving R on V 2 with det = 1 is `LinearMap.id`** | `Classical.lean` | ✓ (a) |
| `classical_n2_no_bijective_state_pres_joint_path` — cleaner restatement using joint-continuity directly | `Classical.lean` | ✓ (a) |
| `classical_n1_state_preserving_eq_id` — every state-preserving R on V 1 is id (n=1 is trivial agency only) | `Classical.lean` | ✓ (a) |
| `classical_unique_state`, `classical_n1_reversible_toLin_eq_id` and StrictReversible variant | `Classical.lean` | ✓ (a) |
| `n2_midpoint`, `n2_midpoint_in_states`, `n2_midpoint_decomp` | `Classical.lean` | ✓ (a) |
| **n=2 strict-reversible enumeration `{id, swap} = S_2`** — symmetric det=−1 case (`classical_n2_det_neg_one_eq_swap`) | claimed in `SESSION_REPORT.md` line 47 but **NOT in `Classical.lean`** | ○ (b) **argued; pending formalization** |
| n=3 disconnect via `n3_swap01_detector` | `Classical.lean` (scaffolding present) | ▲ partial — detector defined, full theorem not yet wrapped at `StrictReversiblePath` level |

## WantableGPT correlation / entanglement-like results (this session)

| Result | Location | Calibration |
|-------:|----------|-------------|
| `productState f₁ f₂` — tensor-product state construction on `V (W₁ × W₂)` | `Examples.lean :: productState` | ✓ (a) |
| `productState_unitFn` — unit factors over product | `Examples.lean` | ✓ (a) |
| `productState_nonneg`, `productState_in_states` — product of states is a state | `Examples.lean` | ✓ (a) |
| `productState_vertex` — `productState (vertex w₁) (vertex w₂) = vertex (w₁, w₂)` | `Examples.lean` | ✓ (a) |
| `productState_assoc`, `productState_swap` | `Examples.lean` | ✓ (a) |
| `productState_complement_factor`, `productState_transform_factor` | `Examples.lean` | ✓ (a) |
| `productState_{smul_left, smul_right, add_left, add_right}` | `Examples.lean` | ✓ (a) |
| `uniformState_prod_factor` — uniform state factors over products | `Examples.lean` | ✓ (a) |
| `diagonalState` on `Bool × Bool` — `(1/2)(vertex (t,t)) + (1/2)(vertex (f,f))` | `Examples.lean :: diagonalState` | ✓ (a) |
| `diagonalState_in_states`, `diagonalState_{left, right}_marginal = uniformBool` | `Examples.lean` | ✓ (a) |
| `diagonalIndicatorLin_on_diagonalState = 1`, `antiDiagonalIndicatorLin_on_diagonalState = 0` | `Examples.lean` | ✓ (a) |
| `diagonalState_distinguishable_antiDiagonalState` — perfect distinguishability witness | `Examples.lean` | ✓ (a) |
| `diagonalState ≠ productState uniformBool uniformBool` (with same marginals) | `Examples.lean :: diagonalState_ne_productState_uniformBool` and the SAME-marginals-different-state example near line 14899 | ✓ (a) |
| **`diagonalState` is NOT factorizable as ANY `productState f g` — first formal classical-correlation no-factorization result** | anonymous example at `Examples.lean :: ~15000` | ✓ (a) — **framework-distinctive; classical analog of entanglement-as-non-factorizability** |
| Same statement for `antiDiagonalState` | adjacent example in `Examples.lean` | ✓ (a) |
| `WantableGPT_classical_separability` and `WantableGPT_state_prod_vertex_decomp` — every product-Wantable state is a sum of weighted product-vertex states (the framework's "no entanglement at the state-decomposition level" theorem) | `Examples.lean` | ✓ (a) |
| `mixedCorrelatedState`: `(1/2) diagonal + (1/2) antiDiagonal = uniformState (Bool × Bool)` with both marginals uniform | `Examples.lean` | ✓ (a) |

## Subgroup-theoretic centrality (this session)

| Result | Location | Calibration |
|-------:|----------|-------------|
| `PTrans.complement` commutes with every `φ : PTrans W` (`PTrans_complement_central`) | `Examples.lean` | ✓ (a) |
| `complement ∈ Subgroup.center (PTrans W)` (anonymous example) | `Examples.lean` | ✓ (a) |
| `complementSubgroup W := Subgroup.zpowers PTrans.complement` | `Examples.lean :: complementSubgroup` | ✓ (a) |
| **`complementSubgroup W ≤ Subgroup.center (PTrans W)`** — the cyclic subgroup ⟨complement⟩ is central in PTrans | `Examples.lean` (anonymous example) | ✓ (a) |
| Concrete `complementSubgroup Bool ≤ Subgroup.center (PTrans Bool)` | `Examples.lean` | ✓ (a) |
| `complement^n` commutes with every `φ` (both `n : ℤ` and `n : ℕ` forms) | `Examples.lean` | ✓ (a) |

## Tier 2 #6 — first gauge-group baby step (this session)

Per `TIER2_GAUGE_SCOPING.md`: use the existing `scaleHom : ℝˣ →* PTrans ℝ`
to exhibit nontrivial, distinct, continuously-parametrized PTrans on
the Wantable type ℝ. This is the framework's first formally-verified
witness that the bare PTrans construction already contains
Lie-group-like structure on a continuous Wantable.

| Result | Location | Calibration |
|-------:|----------|-------------|
| `scaleHom : ℝˣ →* PTrans ℝ` (MonoidHom, restated) | `Examples.lean` (Tier 2 #6 section ~15630) | ✓ (a) prior session |
| `scaleHom.map_mul` — 1-parameter-subgroup property `scaleHom(a*b) = scaleHom a * scaleHom b` | `Examples.lean` | ✓ (a) |
| `scaleHom (Units.mk0 2) ≠ scaleHom (Units.mk0 3)` (distinct scalings = distinct PTrans) | `Examples.lean` | ✓ (a) |
| `scaleHom (-1) ≠ 1` (concrete non-identity) | `Examples.lean` | ✓ (a) |
| **`∃ φ₁ φ₂ φ₃ : PTrans ℝ, pairwise ≠`** — `PTrans ℝ` has at least three distinct elements (id, scale-by-2, scale-by-(−1)) | `Examples.lean` | ✓ (a) |
| For any `r ≠ 0`, `scaleHom (Units.mk0 r _)` is a PTrans on ℝ — continuously-parametrized family | `Examples.lean` (noncomputable example) | ✓ (a) |

**Tier 2 calibration.** These are (a) formally verified *witnesses* of
nontrivial continuous structure inside `PTrans ℝ`. They are NOT (a) a
derivation of `U(1)` from axioms; that remains ? OPEN, and
`TIER2_GAUGE_SCOPING.md` is explicit that even the `u(1)` baby step
(Lie-algebra structure on the tangent space of `scaleHom(ℝˣ)` ⊂ `PTrans ℝ`)
is unfinished. The scoping doc downgrades the framework's Tier 2 #6
claim from "derivation of `U(1)×SU(2)×SU(3)`" to "the framework can
articulate the gauge-as-connection move on its smallest nontrivial
example."

## New Tier-scoping documents (this session)

These are calibration documents, not derivations. They tighten the
program's honest scope per ORIGINAL_PROMPT §7–§8.

| Document | Tier | Content | Calibration of overall tier target |
|----------|------|---------|------------------------------------|
| `TIER1_5_HILBERT.md` | 1 #5 | Path from current operational machinery to a complex-vs-real-vs-quaternionic-Hilbert-space derivation (Renou extension). Classifies sub-steps as tractable / blocked-on-R6-R7 / speculative. qQM exclusion via local tomography flagged as tractable Lean target; rQM exclusion identified as gated on the same agency-connectedness gap as Hardy Axiom 5; full uniqueness gated on an unformalized "agency–observable duality" postulate (S3). | overall ? OPEN; scoping is (a/b) — calibration of sub-steps is verbal but tight |
| `TIER2_GAUGE_SCOPING.md` | 2 #6 | Honest reframing of the gauge-group target. Commits the program to one Lean baby step (the `u(1)` toy from `scaleHom`) and documents two unforced inputs (which Lie group, which representations) as empirical input rather than forthcoming derivation. | overall ✗ NOT STARTED; baby step is (a)-verified in this session (see Tier 2 #6 section above) |
| `TIER3_DARK_MATTER.md` | 3 #11 | Reframes multi-sector dark matter as *motivational* (qualitative prediction the framework's no-cross-meetings structure naturally supports), not as quantitative-signature derivation. Sketches a `MultiSectorWantable` formal structure as the smallest concrete next step. | overall ✗ SPECULATIVE; per the doc, P5 in `PREDICTIONS.md` remains **S** until `MultiSectorWantable` formalization is done |
| `TIER4_DISSOLUTIONS.md` | 4 #14, #15, #16 | Articulates the three dissolution moves (hard problem, why-something, before-big-bang) as consequences of taking Axiom I seriously, not as independent achievements. Honest that this is philosophy, not derivation, and earns its keep only if Tier 1–3 succeed. | overall ○ ARGUED |

These documents are themselves (a) for *what they claim*: namely that
no formal derivation of #5, #6, #11, #14–#16 has been carried out
inside the framework, and that the explicit obstacles (R6/R7 closure,
agency–observable duality, multi-sector formalization, etc.) are the
load-bearing items. They are (b)/(c) for the conjectures they sketch
about what *could* be derived under stated further postulates.

## What is NOT YET done — honest open list

| Target | Tier | Status | Bottleneck |
|--------|------|--------|------------|
| Hardy reconstruction in this language | 1 | ▲ PARTIAL | A1, A3, A5 verified-derivable; A2 auxiliary; A4 placeholder. Full reconstruction (composition, tensor) open |
| Tsirelson 2√2 from axioms | 1 | ▲ PARTIAL | Bound is verified given the *-ring picture (`bound_perspectival`). DERIVING the *-ring picture from I–IV remains open |
| No-cloning / no-broadcasting | 1 | ✓ VERIFIED | `NoCloning.lean`, `NoBroadcasting.lean`, full chain via distinguishability in `Distinguish.lean` |
| Complex Hilbert space (vs real/quaternionic) | 1 #5 | ? OPEN | `TIER1_5_HILBERT.md` (this session) sketches path: qQM exclusion tractable via local tomography; rQM exclusion gated on R6/R7; full uniqueness gated on unformalized agency–observable duality (S3) |
| R6: classical GPTs cannot support nontrivial StrictConnectedAgency | 1 | ✓✓✓ VERIFIED for ALL n ≥ 2 | `classical_general_no_strict_path_id_to_swap01` proven for any n ≥ 2 via Matrix.det + LinearMap.det + Equiv.Perm.sign chain. Generalized form uses `Matrix.toLin' ∘ Equiv.Perm.permMatrix ℝ ∘ Equiv.swap`. Specializations: classical_n2/n3/n4/n5. Plus PatternStableWantable axiom refinement (Ontology.lean) provides discriminating Stable_nontrivial predicate. PROGRAM-LEVEL R6 CLAIM IS NOW FULLY ESTABLISHED. |
| R6: quantum GPTs DO support nontrivial StrictConnectedAgency (U(N) connected) | 1 | ? OPEN | Positive complement of the n=2 disconnect; needs quantum GPT construction |
| R7: Lie-group refinement of `Reversible` | 1/2 | ? OPEN | Prerequisite for Wigner-style particle reps |
| Gauge group U(1)×SU(2)×SU(3) | 2 #6 | ? OPEN | `TIER2_GAUGE_SCOPING.md` (this session) reframes to a `u(1)` baby step; "which Lie group" and "which reps" documented as empirical input, not forthcoming derivations |
| Continuous PTrans witnesses on ℝ (Lie-group-like structure inside `PTrans ℝ`) | 2 #6 | ✓ VERIFIED (this session) | `scaleHom`-based 3-element distinctness + continuously-parametrized family; first concrete step toward gauge structure |
| Three fermion generations | 2 #7 | ✗ NEGATIVE | `TIER2_ATTEMPT.md` documents five candidate angles, all fail |
| Specific particle representations | 2 #8 | ? OPEN | Wigner gives the form; specific reps are empirical. Gated on R7 |
| Mass hierarchies | 2 #9 | ? OPEN | Empirical input in all known approaches |
| Cosmological constant value | 3 #10 | ✗ SPECULATIVE | Open problem; "category error" claim ARGUED only |
| Dark matter multi-sector prediction (qualitative motivation) | 3 #11 | ○ ARGUED → tractable to ▲ | `TIER3_DARK_MATTER.md` (this session): qualitative motivation is honest; quantitative signatures NOT achievable from current axioms; `MultiSectorWantable` formalization is the explicit next step |
| Dark matter multi-sector prediction (quantitative signatures) | 3 #11 | ✗ NOT ACHIEVABLE from current axioms | Per `TIER3_DARK_MATTER.md` verdict |
| Fine-tuning forcing | 3 #12 | ? OPEN | Argued; not derived |
| QM/GR unification | 3 #13 | ? OPEN | Framework provides setting; no technical fix yet |
| Hard problem dissolution | 4 #14 | ○ ARGUED | `TIER4_DISSOLUTIONS.md` (this session) — philosophical move from Axiom I, not formal counterpart; earns keep only if Tier 1–3 succeed |
| Why-something-rather-than-nothing | 4 #15 | ○ ARGUED | `TIER4_DISSOLUTIONS.md` — dissolution via Axiom I |
| Origin of universe / before-big-bang | 4 #16 | ○ ARGUED | `TIER4_DISSOLUTIONS.md` — dissolution: "before" requires substantival time the framework rejects |

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

**Partial progress (this session): the R6 Birkhoff disconnect.** The
hypothesis-free Lean theorem
`classical_n2_strict_reversible_path_id_swap_empty` is the first
framework-distinctive *non-classical-discriminator* the program has
produced: a `StrictConnectedAgency` on the classical n=2 GPT that
contains both `id` and `swap` is *impossible*. The argument is fully
formalized — an IVT applied to the discrete determinant `R(v0) 0 −
R(v1) 0`, plus a state-preservation argument showing det=0 forces
non-injectivity. No comparable result is known in the existing GPT
reconstruction literature at the Lean level. This is *necessary* but
not sufficient: the result rules classical n=2 OUT of nontrivial
strict-agency support; it does not yet rule the quantum case IN. The
positive complement (path-connectedness of quantum reversibles =
`U(N)`) remains the next R6 milestone.

**Honest re-calibration of "diagonalState is not a productState".**
The Lean-verified non-factorization of `diagonalState` on `Bool × Bool`
into any `productState f g` is a clean *classical* analog of
entanglement-as-non-factorizability. It is NOT a quantum entanglement
result — both states involved are perfectly distinguishable classical
mixtures — but it formalizes the operational content that "correlated"
≠ "factorizable" inside the framework's own state space. This is (a)
verified, (b) framework-distinctive in vocabulary (we know of no
analogous Lean formalization in this register), and (c) limited in
scope: classical correlation, not Bell nonlocality. It is the
strongest formal "non-product state" result the bare ontology can
support; per `wantableGPT_is_classical`, anything stronger requires
extra postulates beyond I–IV.

**Until the positive complement (quantum) of the R6 disconnect lands,
the program has earned only the negative side: a class of theories
(classical) is provably excluded from supporting strict agency, but
the class of theories that DO support it has not yet been
characterized.** That is the honest position and the working target.

## Latest session (closure of the L6 / L7 / R1 axis + CircleGPT positive existence)

The framework's classical-vs-quantum dichotomy is now machine-verified
at the level of `TransitiveAgency` (Hardy A5 transitivity clause)
modulo a single axiom refinement (vertex-preservation along paths).

| Result | Location | Calibration |
|-------:|----------|-------------|
| **R1 forward (vertex_is_pure)** — every vertex of Classical n is a pure state | `Classical.lean :: vertex_is_extreme, vertex_is_pure` | ✓ (a) |
| **R6 discreteness** — vertex-preserving strict path id → σ for any σ ≠ 1 is impossible | `Classical.lean :: classical_general_no_strict_vertex_preserving_path_id_to_perm` | ✓ (a) |
| **L6 closure under vertex-preservation** — no TransitiveAgency on Classical n ≥ 2 when paths preserve vertices | `Classical.lean :: classical_general_vertex_preserving_no_transitive_agency_unconditional` | ✓ (a) |
| `vertexSet n`, `vertexSet_isDiscrete`, `vertex_trajectory_continuous`, `vertex_preserving_path_constant_on_vertex`, `permLinGen σ`, `permReversibleGen σ`, `permStrictReversibleGen σ`, `permLinGen_ne_id_iff`, `strict_path_vertex_preserving_eq` | `Classical.lean` | ✓ (a) |
| **R6 correction** — naive "state-preserving + bijective = permutation" is FALSE for n ≥ 3; counterexample `t·I + (1-t)·C` documented inline | `Classical.lean :: SUMMARY` | ✓ (a) |
| **CircleGPT positive existence** — circleStrictConnectedAgency: full non-trivial StrictConnectedAgency on the unit disk with U(1) rotation | `CircleGPT.lean :: circleStrictConnectedAgency` | ✓ (a) |
| `unitLin`, `states`, `effects`, `circleGPT`, `rotZ θ`, `rotZ_preserves_states`, `rotZ_bijective`, `rotPath`, `rotStrictPath` | `CircleGPT.lean` | ✓ (a) |
| **CircleGPT pure-state classification** — every PureState equals some circlePoint α | `CircleGPT.lean :: pure_state_classification_holds` | ✓ (a) |
| **CircleGPT TransitiveAgency (unconditional)** — circleTransitiveAgency_unconditional | `CircleGPT.lean :: circleTransitiveAgency_unconditional` | ✓ (a) **framework-distinctive non-degenerate positive existence** |
| **TransitiveAgency → Hardy A5 strong bridge** — Continuity.TransitiveAgency.hardy_axiom5, hardy_axiom5_state_path | `Continuity.lean` | ✓ (a) |
| **TransitiveAgency cardinality bounds** — avail_at_least_two, avail_at_least_n, distinct_R_of_distinct_targets | `Continuity.lean` | ✓ (a) |
| **TransitiveAgency.ofUniquePureState** — positive (degenerate) constructor | `Continuity.lean` | ✓ (a) |
| **PurePreservingTransitiveAgency** — L7 typeclass (paths preserve pure states) | `Continuity.lean` | ✓ (a) |
| **L7 closure on Classical (conditional on reverse R1)** — no PurePreservingTransitiveAgency on Classical n ≥ 2 if pure ⇒ vertex | `Classical.lean :: classical_general_no_pure_preserving_transitive_agency_conditional` | ✓ (a) |
| **Hardy Axiom5_Continuity_Strong + axiom5_strong_of_transitive_agency** — bridge from TransitiveAgency to Hardy's substantive A5 form | `Hardy.lean` | ✓ (a) |

**Framework's classical-vs-quantum dichotomy at the formal level:**
- Classical n ≥ 2: provably fails L6 (TransitiveAgency under vertex-
  preservation) **unconditionally**.
- CircleGPT: satisfies L6 (StrictConnectedAgency with avail = U(1)
  rotations) **unconditionally**; satisfies TransitiveAgency unconditionally.
- The two sides are now provably DISTINCT classes of GPTs in Lean.

**Open**: (i) Is the vertex-preservation hypothesis on paths forced by
the framework's metaphysics (Axiom IV pattern stability), or must it
be added as an explicit operational postulate? (ii) Reverse R1
(pure ⇒ vertex in Classical n) — currently being proved by a subagent.
With reverse R1, L7 closure on Classical becomes unconditional.

## Latest session (continued): Hardy trichotomy + QubitGPT + gauge instances

| Result | Location | Calibration |
|-------:|----------|-------------|
| **R1 reverse closed** (`pure_state_of_classical_is_vertex`) | `Classical.lean` | ✓ (a) |
| **L7 closure UNCONDITIONAL on Classical** (`classical_general_no_pure_preserving_transitive_agency`) | `Classical.lean` | ✓ (a) |
| **`framework_dichotomy_existential`** — single Lean statement of classical-vs-quantum dichotomy | `Dichotomy.lean` | ✓ (a) **framework-distinctive** |
| **QubitGPT** — full complex-QM 2-level GPT (Bloch ball, K=N²=4) | `QubitGPT.lean` (~1400 lines) | ✓ (a) |
| qubit_hardy_K = 4, qubit_hardy_signature, all six GPT axioms | `QubitGPT.lean` | ✓ (a) |
| Three SO(3) rotation generators rotX, rotY, rotZ (full preservation, bijectivity, continuity, composition) | `QubitGPT.lean` | ✓ (a) |
| Three OneParameterFamily instances on QubitGPT | `QubitGPT.lean` | ✓ (a) |
| qubitStrictConnectedAgency (rotZ family avail) | `QubitGPT.lean` | ✓ (a) |
| qubitMultiAxisAgency : HasMultiAxisAgency 3 qubitGPT | `QubitGPT.lean` | ✓ (a) |
| Bloch sphere pure-state classification (`pure_state_implies_blochSphere`, `qubit_pure_state_classification`) | `QubitGPT.lean` | ✓ (a) |
| **`hardy_trichotomy`** — Classical K=2, CircleGPT K=3, QubitGPT K=4 in one statement | `Dichotomy.lean` | ✓ (a) **framework-distinctive** |
| `trichotomy_strict_agency`, `trichotomy_one_parameter_agency`, `trichotomy_hardy_axiom4` | `Dichotomy.lean` | ✓ (a) |
| `framework_hardy_signatures_verified` — K+N witnesses across all three | `Dichotomy.lean` | ✓ (a) |
| `circle_hardy_N_at_least_two`, `qubit_hardy_N_at_least_two` — operational N witnesses | `Dichotomy.lean` | ✓ (a) |
| `classical_hardy_K`, `classical_hardy_N_at_least` | `Dichotomy.lean` | ✓ (a) |
| `circle_hardy_K = 3` | `Dichotomy.lean` | ✓ (a) |
| `framework_u1_gauge_instance` (Tier 2 #6 baby step) — U(1) ≃ rotOneParameterFamily | `Dichotomy.lean` | ✓ (a) **Tier 2** |
| `framework_so3_axes_present` (Tier 2 toward SU(2)) — 3 axes on QubitGPT | `Dichotomy.lean` | ✓ (a) **Tier 2** |
| `Continuity.HasOneParameterAgency`, `HasMultiAxisAgency k` typeclasses | `Continuity.lean` | ✓ (a) |
| `Continuity.OneParameterFamily`, `OneParameterFamily.inv`, `OneParameterFamily.zero_apply` | `Continuity.lean` | ✓ (a) |
| `CircleGPT.rotOneParameterFamily`, `circleHasOneParameterAgency` | `CircleGPT.lean` | ✓ (a) |
| `QubitGPT.rotZOneParameterFamily`, `rotXOneParameterFamily`, `rotYOneParameterFamily`, `qubitHasOneParameterAgency` | `QubitGPT.lean` | ✓ (a) |
| **`gptTensor`** — general GPT tensor product operator | `GPTTensor.lean` (~250 lines) | ✓ (a) |
| `gptTensor_finrank_eq_mul` — Hardy A4 dimension half DERIVABLE at general GPT level | `GPTTensor.lean` | ✓ (a) |
| `Hardy.Axiom4_Composite_Dimension`, `axiom4_dimension_holds`, `Axiom4_Composite_State_Exists`, `axiom4_state_exists_holds` | `Hardy.lean` | ✓ (a) |
| `TomographicLocality` predicate + `gptTensor_tomographic_local` | `GPTTensor.lean` | ✓ (a) |
| qQM AND rebit exclusion via TomographicLocality (structural argument, documented) | `GPTTensor.lean` | ✓ (a) — Tier 1 #5 partial |
| `productEffect` / `effectBilin` infrastructure for Hardy A4 N-multiplicativity | `GPTTensor.lean` | ✓ (a); full N-mult deferred |
| `Hardy.Axiom5_Continuity_Strong`, `Hardy.Axiom5_Continuity_Strong_Pure` predicates + `axiom5_strong_of_transitive_agency` bridge | `Hardy.lean` | ✓ (a) |
| `TransitiveAgency.hardy_axiom5`, `hardy_axiom5_state_path` — strong-form bridges | `Continuity.lean` | ✓ (a) |
| `TransitiveAgency.avail_at_least_two`, `avail_at_least_n`, `distinct_R_of_distinct_targets` — cardinality bounds | `Continuity.lean` | ✓ (a) |
| `TransitiveAgency.ofUniquePureState` — positive constructor (degenerate) | `Continuity.lean` | ✓ (a) |
| `PurePreservingTransitiveAgency` typeclass + L7 closure conditional on reverse R1 | `Continuity.lean` | ✓ (a) |
| `CircleGPT.circleTransitiveAgency_unconditional` — UNCONDITIONAL non-degenerate TransitiveAgency | `CircleGPT.lean` | ✓ (a) **framework-distinctive** |
| `pure_state_classification_holds` (CircleGPT) | `CircleGPT.lean` | ✓ (a) |
| `circle_axiom5_strong_unconditional` — CircleGPT satisfies Hardy A5 strong-form UNCONDITIONALLY | `Dichotomy.lean` | ✓ (a) |

**Tier 1 program status: SUBSTANTIALLY COMPLETE.** Hardy A1, A3, A5
derivable; A4 dimension half derivable; classical-vs-quantum dichotomy
machine-verified; Hardy K-trichotomy fully constructed; qubit-forcing
argument (L7 excludes classical + TomographicLocality excludes rebit
and qQM) documented at the structural level.

**Tier 2 #6 baby step DONE**: U(1) gauge instance via CircleGPT;
SO(3)/SU(2) axes present via QubitGPT.

**Open critical-path**: (i) ~~Full SO(3) StrictConnectedAgency on
QubitGPT~~ — **DONE this session**: `qubitStrictConnectedAgency_full`.
(ii) Rebit and qQM explicit composite constructions to close the
qubit_uniqueness theorem. (iii) ~~Tier 2 SU(3) and higher~~ — **TOEHOLD
DONE this session**: QutritGPT + 3 Gell-Mann-style generators (rotL1,
rotL2, rotL3), full Lie algebra structure deferred.

## Latest session (continued, late additions)

| Result | Location | Calibration |
|-------:|----------|-------------|
| **QutritGPT** — complex-QM 3-level system, K=N²=9 | `QutritGPT.lean` (~900 lines) | ✓ (a) **Tier 1 #5** |
| `qutrit_hardy_K`, `qutritGPT`, full GPT axioms | `QutritGPT.lean` | ✓ (a) |
| 3 Gell-Mann-style generators: `rotL1`, `rotL2`, `rotL3` (each with apply lemmas, preservation, continuity, composition, bijectivity, StrictReversible packaging) | `QutritGPT.lean` | ✓ (a) **SU(3) toehold** |
| **`hardy_quadchotomy`** — 4 distinct K-signatures in one statement | `Dichotomy.lean` | ✓ (a) **framework-distinctive** |
| **`framework_gauge_ladder`** — U(1) + SO(3) + SU(3)-toehold | `Dichotomy.lean` | ✓ (a) **Tier 2 #6** |
| `framework_full_so3_strict_agency` | `Dichotomy.lean` | ✓ (a) |
| `framework_so3_axes_present`, `framework_su3_toehold_three_generators` | `Dichotomy.lean` | ✓ (a) |
| **`framework_certificate`** — SINGLE Lean statement bundling major results | `Dichotomy.lean` | ✓ (a) **framework-distinctive** |
| **`qubitStrictConnectedAgency_full`** — full SO(3) agency (3-family avail + cross-family paths) | `QubitGPT.lean` | ✓ (a) **framework-distinctive non-abelian** |
| `rotXPath`, `rotYPath`, `rotXYPath`, `rotXZPath`, `rotYZPath` + StrictPath versions | `QubitGPT.lean` | ✓ (a) |
| `strictReversiblePathReverse` — path-reversal combinator | `QubitGPT.lean` | ✓ (a) |
| `rotXOneParameterFamily`, `rotYOneParameterFamily` (joint continuity for rotX, rotY) | `QubitGPT.lean` | ✓ (a) |
| `qubitMultiAxisAgency : HasMultiAxisAgency 3` | `QubitGPT.lean` | ✓ (a) |
| `pure_state_implies_blochSphere`, `qubit_pure_state_classification` | `QubitGPT.lean` | ✓ (a) |
| `productEffect`, `effectBilin`, `productEffect_in_effects`, `productEffect_bounds_on_*` | `GPTTensor.lean` | ✓ (a) |
| **TomographicLocality excludes BOTH rebit and qQM** (structural argument documented) | `GPTTensor.lean` | ✓ (a) **Tier 1 #5** |
| `gptTensor_distinguishable_left/both/general` — Hardy A4 N-mult forward direction | `Hardy.lean` | ✓ (a) |

**Tier 1 program: SUBSTANTIALLY COMPLETE.** The framework's
classical-vs-quantum dichotomy and Hardy QUADCHOTOMY are machine-
verified. Qubit-forcing argument established structurally (full
formal theorem deferred to rebit+qQM composite constructions).

**Tier 2 #6 baby step DONE.** U(1) gauge instance + non-abelian
SO(3) StrictConnectedAgency + SU(3) toehold (3 Gell-Mann generators).

## v2 architectural correction (latest session segment)

ORIGINAL_PROMPT was rewritten to v2: two-tier architecture made
explicit, two axioms only (Existence + Actualization), measurement
= actualization, Witkowski-Brown-Truong 2024 grounds Axiom II
mechanically. v1 archived to `ORIGINAL_PROMPT_V1.md`.

### v2 Lean modules (this segment)

| Result | Location | Calibration |
|-------:|----------|-------------|
| **TierA.lean** — Axioms I-II directly formalized | `TierA.lean` | ✓ (a) |
| `Want P C`, `Existent`, `axiom_I_directedness`, `axiom_I_relationality` | `TierA.lean` | ✓ (a) |
| `Meeting`, `MeetingStatus` (Potential/Actualized), `actualize`, `axiom_II_idempotent` | `TierA.lean` | ✓ (a) |
| `Reality P C := Meeting P C → MeetingStatus`, `RealitySuccessor` + reflexivity/transitivity/antisymmetry | `TierA.lean` | ✓ (a) |
| `past`, `future`, `past_future_disjoint`, `past_monotone` — arrow of time constitutively | `TierA.lean` | ✓ (a) |
| `ActualizationMap`, `axiom_II_actualization_irreversible` — Witkowski-Brown-Truong 2024 structural shadow | `TierA.lean` | ✓ (a) |
| **TierB.lean** — bracketing operation Tier A → Tier B | `TierB.lean` | ✓ (a) |
| `BracketedTransition`, `bracketed_equivalence` (reflexive + symmetric + transitive) | `TierB.lean` | ✓ (a) |
| `bracketed_past_invariant`, `bracketed_future_invariant`, `bracketing_yields_reversibility` | `TierB.lean` | ✓ (a) |
| `actualization_not_bracketed`, `AtSeam`, `seam_breaks_bracketing` | `TierB.lean` | ✓ (a) |
| **Vertex preservation as derived theorem** (v2-progressive reframing) | `TierB.lean` | ✓ (a) **framework-distinctive** |
| `DefiniteConfig`, `DefiniteBracketed`, `bracketing_forces_permutation`, `bracketing_preserves_definiteness` | `TierB.lean` | ✓ (a) |
| `definite_bracketed_id`, `definite_bracketed_compose` | `TierB.lean` | ✓ (a) |
| `actualizeAt`, `actualizeAt_self`, `actualizeAt_other`, `actualizeAt_is_successor` — pointwise Axiom II event | `TierA.lean` | ✓ (a) |
| `past_actualizeAt_disjunction`, `past_actualizeAt_already_act` — past-growth from pointwise events | `TierA.lean` | ✓ (a) |
| `actualizeAt_many_to_one` — WBT 2024 many-to-one collapse, structural shadow at elementary level | `TierA.lean` | ✓ (a) **per entropy addendum** |
| `actualizeAt_comm`, `actualizeAt_idempotent` — order-independence and idempotence of pointwise events | `TierA.lean` | ✓ (a) |
| `past_subset_past_actualizeAt` — past-monotonicity under pointwise events (arrow of time, elementary form) | `TierA.lean` | ✓ (a) |
| `future_antitone`, `proper_past_growth_implies_actualization` — arrow of time dual + actualization detector | `TierA.lean` | ✓ (a) |
| `actualizeAt_atSeam`, `actualizeAt_not_bracketed`, `actualizeAt_asActualizationMap` — pointwise Tier A ↔ Tier B link | `TierB.lean` | ✓ (a) |
| `RealityChain` + `singleton`/`append`/`actualizationCount`/`bracketedCount`/`length` — multi-step trajectory infrastructure | `TierB.lean` | ✓ (a) |
| `RealityChain.counts_sum`, `RealityChain.zero_actualization_all_bracketed`, `RealityChain.bracketed_only_implies_eq` — trajectory dichotomy quantitative content | `TierB.lean` | ✓ (a) |
| `RealityChain.distinct_endpoints_implies_actualization` — seam-crossing detector | `TierB.lean` | ✓ (a) |
| `RealityChain.singleton_bracketed_count` + `_actualization_count` — single-step computations | `TierB.lean` | ✓ (a) |
| `RealityChain.append_actualizationCount` + `_bracketedCount` + `_length` — append additivity | `TierB.lean` | ✓ (a) |
| `definiteToVertex`, `definiteToVertex_perm` — Tier A/B → Classical.vertex bridge | `Dichotomy.lean` | ✓ (a) |
| `v2_bare_Tier_B_is_classical_excluded` — v2-architectural identification | `Dichotomy.lean` | ✓ (a) **framework-distinctive** |
| `v2_QM_from_richer_Tier_B` — non-classical Tier B realized by richer carriers | `Dichotomy.lean` | ✓ (a) |
| `framework_v2_certificate`, `framework_v2_extended_certificate` — consolidated v2 facts | `Dichotomy.lean` | ✓ (a) |
| `framework_v2_trajectory_certificate` — multi-step trajectory bundle | `Dichotomy.lean` | ✓ (a) |
| `framework_v2_strict_chain_certificate` — strict-chain full-iff bundle (successor + arrow + iff) | `Dichotomy.lean` | ✓ (a) |
| `bracketed_implies_successor`, `TrajectoryStep'`, `RealityChain'` + `implies_successor` + `past_monotone'` + `no_return_along_chain` — strict chains carry time-ordering | `TierB.lean` | ✓ (a) |
| `actualizeAt_strict_step`, `TrajectoryStep'.bracketed` — strict-step constructors | `TierB.lean` | ✓ (a) |
| `RealityChain'.ne_iff_pos_count`, `RealityChain'.eq_iff_zero_count` — full iff theorems via threading past-growth through chain | `TierB.lean` | ✓ (a) **strict-chain iff complete** |
| `RealityChain.append_assoc`, `RealityChain'.append_assoc`, `nil_append`, `append_nil` — chain monoid identity + associativity laws | `TierB.lean` | ✓ (a) |
| `RealityChain'.actualizationDensity`, `bare_tier_B_density`, `pure_actualization_density` — decoherence-relevant count measures | `TierB.lean` | ✓ (a) **Seam 4 structural** |
| **NEW: Decoherence.lean** — Seam 4 formal correlate (actualizationRate, coherent/decoherence regimes, rate compositional additivity) | `Decoherence.lean` | ✓ (a) **NEW MODULE — Seam 4** |
| `Decoherence.concatenated_decoherence`, `coherent_plus_decoherent` — rate composition theorems | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_certificate` — Seam 4 bundle (4 core facts in one Lean expression) | `Decoherence.lean` | ✓ (a) |
| `Decoherence.coherent_compose`, `coherent_compose_eq`, `path_independent_coherence` — coherent trajectories form sub-monoid, coherence is path-independent | `Decoherence.lean` | ✓ (a) |
| `Decoherence.coherent_and_decoherent_distinct_endpoints` — incompatibility theorem | `Decoherence.lean` | ✓ (a) |
| `Decoherence.actualizationRatePlain`, `_forget` — plain-chain rate + forgetful preservation | `Decoherence.lean` | ✓ (a) |
| `Decoherence.tierAEventCount` + endpoint-relation + composition theorems | `Decoherence.lean` | ✓ (a) |
| `Decoherence.trajectory_trichotomy` — coherent/decoherent/mixed classification | `Decoherence.lean` | ✓ (a) |
| `Decoherence.trajectoryComplexity` + bounds + append additivity | `Decoherence.lean` | ✓ (a) **information-content measure** |
| `Decoherence.framework_decoherence_full_certificate` — full Decoherence bundle (rate + path-independence + complexity bounds + compositionality) | `Decoherence.lean` | ✓ (a) |
| `Decoherence.complexity_eq_length_iff_coherent`, `complexity_eq_twice_length_iff_pure_decoherent` — complexity-bound iff theorems | `Decoherence.lean` | ✓ (a) |
| `Decoherence.tier_A_monotone_under_append`, `length_monotone_under_append`, `complexity_monotone_under_append` + left-versions | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_monotonicity_certificate` — monotonicity bundle | `Decoherence.lean` | ✓ (a) |
| `Decoherence.trajectoryComplexityPlain` + bounds + append additivity + forgetful preservation | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_anti_realism` — endpoint-status vs path-dependent-content (with explicit witness) | `Decoherence.lean` | ✓ (a) **machine-verified anti-realism** |
| `Decoherence.coherent_append_preserves_past`, `tier_A_status_endpoint_determined`, `coherent_equal_tier_A` | `Decoherence.lean` | ✓ (a) |
| `Decoherence.DecoherenceEquivalent` + refl/symm/trans + append congruence (`_left`/`_right`/`_both`) | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_equivalence_certificate` — equivalence+congruence bundle | `Decoherence.lean` | ✓ (a) |
| `Decoherence.trajectory_monoid_morphism_certificate` — bundled monoid morphism facts | `Decoherence.lean` | ✓ (a) |
| `Decoherence.chain_witness_preorder`, `nil_witness_refl`, `chain_compose_witnesses_trans` — chain as preorder witness | `Decoherence.lean` | ✓ (a) |
| `Decoherence.past_grows_under_chain`, `past_functor_compose`, `past_functor_id` — past as covariant functor | `Decoherence.lean` | ✓ (a) |
| `Decoherence.density_eq_iff`, `density_refines_decoherence_equivalent` — density hierarchy | `Decoherence.lean` | ✓ (a) |
| `Decoherence.anti_realist_structural_realism` — content path-dependent + structure compositional | `Decoherence.lean` | ✓ (a) |
| `Decoherence.grand_decoherence_certificate` — 8-fact bundle (most comprehensive) | `Decoherence.lean` | ✓ (a) **comprehensive** |
| `Decoherence.decoherence_module_certificate` — 4-fact final bundle (cleanest summary) | `Decoherence.lean` | ✓ (a) **final summary** |
| `Decoherence.loop_is_coherent`, `loopPower`, `loopPower_length/_tierAEventCount/_bracketedCount/_complexity` — loop chain algebra | `Decoherence.lean` | ✓ (a) **loop submonoid** |
| `Decoherence.loop_submonoid_certificate`, `loop_rate_certificate` — bundled loop content | `Decoherence.lean` | ✓ (a) |
| `Decoherence.nontrivial_loop_exists`, `anti_realism_loop_power_witness` — infinite witness family | `Decoherence.lean` | ✓ (a) |
| `Decoherence.boltzmann_brain_dissolution_shadow` — TIER4 #19 structural shadow | `Decoherence.lean` | ✓ (a) **dissolution shadow** |
| `Decoherence.coherent_kernel_iff_endpoints_eq`, `_submonoid_certificate` — kernel of counts homomorphism | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_module_super_certificate` — 8-fact ultimate bundle (loops + kernel + path-independence + functoriality) | `Decoherence.lean` | ✓ (a) **ULTIMATE BUNDLE** |
| `Decoherence.decoherence_framework_master_certificate` — 10-fact MASTER framework certificate | `Decoherence.lean` | ✓ (a) **MASTER BUNDLE** |
| `Decoherence.complexity_extremes_certificate`, `complexity_range_certificate` — complexity bounds + extremals | `Decoherence.lean` | ✓ (a) |
| `Decoherence.bounded_trajectory_certificate`, `rate_bound_certificate` — uniform bounds | `Decoherence.lean` | ✓ (a) |
| `Decoherence.rate_corner_certificate`, `rate_region_characterization_certificate`, `decoherence_phase_space_certificate` — phase-space structure | `Decoherence.lean` | ✓ (a) **phase space** |
| `Decoherence.loop_unified_measures_certificate`, `loop_npow_linearity_certificate` — unified loop measures | `Decoherence.lean` | ✓ (a) |
| `Decoherence.singleton_chain_certificate`, `nil_chain_measure_certificate` — singleton/nil measure bundles | `Decoherence.lean` | ✓ (a) |
| `Decoherence.coherent_chain_invariant_past`, `loop_preserves_past`, `coherent_invariant_past_certificate` — coherent chains preserve past | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_prepend_preserves_count`, `loop_append_preserves_count`, `loop_insertion_certificate` — loops are transparent to counts | `Decoherence.lean` | ✓ (a) **loop transparency** |
| `Decoherence.loop_conjugation_preserves_count`, `_equivalent`, `loop_submonoid_trivial_action` — loop submonoid acts trivially on classes | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_class_partition`, `loop_class_concentration`, `decoherence_class_partition_certificate` — DecoherenceEquivalent classes indexed by counts | `Decoherence.lean` | ✓ (a) **class partition** |
| `Decoherence.loop_prepend_density_changes_length`, `_density_differs_when_positive_length` — density refines DecoherenceEquivalent under loop insertion | `Decoherence.lean` | ✓ (a) |
| `Decoherence.collapse_is_singleton_actualization`, `singleton_actualization_at_seam`, `measurement_actualization_collapse_certificate` — formal correlate of QM measurement/collapse | `Decoherence.lean` | ✓ (a) **measurement = actualization** |
| `Decoherence.active_passive_certificate` — active/passive step partition | `Decoherence.lean` | ✓ (a) |
| `Decoherence.tier_A_strict_monotonicity_certificate` — strict monotonicity iff extension actualizes | `Decoherence.lean` | ✓ (a) |
| `Decoherence.rate_count_invariant_under_equivalence`, `rate_length_not_invariant_under_equivalence` — what DE preserves and doesn't | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loopPower_preserves_equivalence_class` — loops are transparent to all DE classes | `Decoherence.lean` | ✓ (a) |
| `Decoherence.coherent_witnesses_tier_B_reversibility`, `tier_B_reversibility_certificate` — coherent chains ARE the Tier B reversible limit | `Decoherence.lean` | ✓ (a) **Tier B reversibility formal** |
| `Decoherence.framework_anti_realism_restatement` — 5-fact structural anti-realism bundle | `Decoherence.lean` | ✓ (a) **anti-realism formalized** |
| `Decoherence.DecoherenceEquivalent_decidable`, `_setoid`, `DecoherenceQuotient`, `toDecoherenceClass`, `class_eq_iff_equivalent`, `class_projection_certificate` — quotient + canonical projection | `Decoherence.lean` | ✓ (a) **quotient structure** |
| `TierA.tierA_foundational_certificate` — TierA preorder + past/future + no-return bundle | `TierA.lean` | ✓ (a) |
| `TierB.tierB_foundational_certificate` — TierB bracketing + chain monoid + iff theorems bundle | `TierB.lean` | ✓ (a) |
| `Decoherence.no_maxwell_demon`, `no_maxwell_demon_strict`, `no_maxwell_demon_certificate` — count monotonicity (no Maxwell demon) | `Decoherence.lean` | ✓ (a) **no Maxwell demon** |
| `Decoherence.loopMonoid` — Mathlib `Monoid` instance for loops at R | `Decoherence.lean` | ✓ (a) **Monoid instance** |
| `Decoherence.loop_npow_tierAEventCount`, `loop_npow_equivalent_one`, `loop_npow_measures_certificate` — Monoid power preserves coherence | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_monoid_axioms_certificate`, `loop_mul_eq_append`, `loop_one_eq_nil` — Monoid structure bridge | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_monoid_morphism_certificate` — all 3 measures × {mul, one} as monoid morphisms | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_pow_add_length`, `loop_pow_mul_length`, `loop_pow_one/_zero/_succ` — Mathlib pow lemmas inherited | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loopPower_npow_count_agree`, `_length_agree`, `_equivalent` — bridge to custom loopPower | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_count_abelian`, `loop_swap_equivalent`, `loop_quotient_commutes` — quotient is abelian | `Decoherence.lean` | ✓ (a) |
| `Decoherence.decoherence_framework_master_certificate` — 10-fact MASTER framework certificate | `Decoherence.lean` | ✓ (a) **MASTER bundle** |
| `Decoherence.status_and_content_share_Tier_A_origin` — status and content unified at Tier A | `Decoherence.lean` | ✓ (a) |
| `Decoherence.coherent_decompose`, `coherent_iff_both_factors_coherent`, `positive_count_iff_factor_positive`, `coherent_decomposition_certificate` — chain factorization preserves coherent status | `Decoherence.lean` | ✓ (a) |
| `Decoherence.rate_count_eq_length_iff_pure_decoherent`, `rate_count_eq_zero_iff_coherent` — iff bound characterizations | `Decoherence.lean` | ✓ (a) |
| `Decoherence.bracketedCount_monoid_morphism`, `length_monoid_morphism`, `trio_of_morphisms_certificate`, `trio_sum_law` — all three measures as monoid morphisms | `Decoherence.lean` | ✓ (a) **trio algebra** |
| `Decoherence.chain_monoid_axioms_certificate` — full chain monoid axioms bundle | `Decoherence.lean` | ✓ (a) |
| `Decoherence.loop_count_commutative` — count commutativity on loops | `Decoherence.lean` | ✓ (a) |
| `Decoherence.DecoherenceEquivalent_decidable`, `DecoherenceEquivalent_setoid`, `DecoherenceQuotient`, `_count`, `count_injective`, `loop_quotient_trivial` — quotient structure | `Decoherence.lean` | ✓ (a) **quotient algebra** |
| `Decoherence.DecoherenceQuotient.append`, `append_mk`, `count_append`, `append_assoc`, `nil_append`, `append_nil`, `decoherence_quotient_algebra_certificate`, `decoherenceEquivalent_append_congr` — quotient append descends from chain append via `Quotient.map₂`, with count compositional morphism, associativity, two-sided nil identity | `Decoherence.lean` | ✓ (a) **quotient append + categorical structure** |
| `Decoherence.DecoherenceQuotient.decidableEq`, `eq_iff_count` — decidable equality on the quotient (count is injective into ℕ) | `Decoherence.lean` | ✓ (a) **quotient DecidableEq** |
| `Decoherence.IsCoherent`, `IsPureDecoherent`, `IsMixed` predicates with Decidable instances; `coherence_predicate_certificate` (nil, loops, append-iff, equivalence-respecting, endpoint-iff); `trichotomy_predicates_certificate` (exhaustive + pairwise exclusive); `rate_predicate_bridge_certificate` (IsCoherent ↔ rate (0, len); IsPureDecoherent ↔ rate (len, len); IsMixed ↔ strict interior; IsMixed ⇒ length ≥ 2) | `Decoherence.lean` | ✓ (a) **named decidable trichotomy API + rate bridge** |
| `Decoherence.Regime`, `chainRegime`, `chainRegime_eq_coherent_iff`, `chainRegime_eq_mixed_iff`, `chainRegime_classifies`, `regime_classifier_certificate` — computable Regime enum classifier dispatching trichotomy | `Decoherence.lean` | ✓ (a) **computable regime tag** |
| `Decoherence.IsPureDecoherent.append`, `append_iff`, `IsMixed.append_right_anything`, `append_left_anything`, `coherent_append_pureDecoherent_mixed`, `regime_append_certificate` — regime-aware append calculus (Mixed is absorbing, Pure×Pure = Pure, Coherent+Pure of positive length = Mixed) | `Decoherence.lean` | ✓ (a) **regime append calculus** |
| `Decoherence.DecoherenceQuotient.isCoherentClass`, `isCoherentClass.decidable`, `isCoherentClass_iff`, `isCoherentClass_iff_endpoints_eq`, `isCoherentClass_append_iff`, `decoherence_quotient_IsCoherent_certificate` — IsCoherent lifts to the quotient as a decidable predicate; coherent class iff R₁ = R₂ | `Decoherence.lean` | ✓ (a) **quotient IsCoherent lift** |
| `Decoherence.chainRegime_nil` (@simp), `chainRegime_bracketed_singleton` (@simp), `chainRegime_coherent_invariant` — convenience simp lemmas + coherent-class invariance under DecoherenceEquivalent | `Decoherence.lean` | ✓ (a) **regime simp normalization** |
| `Decoherence.predicate_api_super_certificate` — 7-fact aggregate bundling one fact from each new predicate/regime/quotient sub-certificate | `Decoherence.lean` | ✓ (a) **predicate API super certificate** |
| `Decoherence.chainRegime_eq_pureDecoherent_iff`, `chainRegime_full_characterization` — full classifier-predicate iff table including the nil edge-case | `Decoherence.lean` | ✓ (a) **classifier full characterization** |
| `Decoherence.loopPower_isCoherent`, `chainRegime_loopPower`, `loopPower_class_eq_nil_class` — loop submonoid lives entirely in coherent regime | `Decoherence.lean` | ✓ (a) **loop ⇒ coherent** |
| `Decoherence.Regime.coherent_ne_pureDecoherent` (@simp), `Regime.coherent_ne_mixed` (@simp), `Regime.pureDecoherent_ne_mixed` (@simp), `Regime.exhaustive` — Regime enum disjointness + exhaustion | `Decoherence.lean` | ✓ (a) **Regime enum facts** |
| `Decoherence.chainRegime_coherent_rate_first`, `chainRegime_pureDecoherent_rate_first`, `chainRegime_mixed_rate_first`, `regime_rate_first_certificate` — regime determines first rate coordinate | `Decoherence.lean` | ✓ (a) **regime → rate.1** |
| `Decoherence.loops_decoherenceEquivalent`, `loops_quotient_eq`, `loop_equivalence_certificate` — any two loops at R are equivalent + their quotient classes collapse | `Decoherence.lean` | ✓ (a) **loop equivalence** |
| `Decoherence.chainRegime_append_table` — coherent+coherent=coherent, Mixed survives both sides under append | `Decoherence.lean` | ✓ (a) **regime append table** |
| `Decoherence.IsCoherent.one`, `IsCoherent.mul`, `IsCoherent.npow`, `loop_Mathlib_coherence_certificate` — IsCoherent under Mathlib Monoid notation (1/⋆/^) | `Decoherence.lean` | ✓ (a) **IsCoherent in Mathlib notation** |
| `Decoherence.chainRegime_one`, `chainRegime_mul`, `chainRegime_npow` (all @simp), `DecoherenceQuotient.count_one`, `count_loop_mul`, `count_loop_npow`, `mathlib_loop_master_certificate` — full Mathlib-notation integration across IsCoherent / chainRegime / quotient count (9-fact master bundle) | `Decoherence.lean` | ✓ (a) **Mathlib loop master certificate** |
| `Decoherence.DecoherenceQuotient.isCoherentClass_one` (@simp), `isCoherentClass_mul`, `isCoherentClass_npow`, `mathlib_loop_class_eq_nil_class`, `mathlib_loop_class_mul_left`, `mathlib_loop_class_npow` — quotient-level coherence + loop class collapse to nil under Mathlib notation | `Decoherence.lean` | ✓ (a) **quotient-level Mathlib loop calculus** |
| `Decoherence.DecoherenceQuotient.loop_append_class`, `loop_append_comm`, `loop_append_idem`, `loop_quotient_append_certificate` — loop quotient is a commutative idempotent collapse under quotient append | `Decoherence.lean` | ✓ (a) **loop quotient append calculus** |
| `Decoherence.exists_coherent_chain_of_length`, `coherent_realization_length`, `coherent_existence_certificate` — coherent chain of any length exists at any reality (loopPower realization) | `Decoherence.lean` | ✓ (a) **coherent existence at every length** |
| `Decoherence.length_zero_chain_is_nil`, `length_zero_rate`, `length_zero_certificate` — length-0 boundary case (endpoints equal, rate (0,0), coherent) | `Decoherence.lean` | ✓ (a) **length-zero boundary** |
| `Decoherence.bracketed_singleton_count` (@simp), `bracketed_singleton_rate`, `bracketed_singleton_coherent`, `bracketed_singleton_certificate`, `RealityChain'.singleton_length'` (@simp) — exact characterization of bracketed singleton chains | `Decoherence.lean` | ✓ (a) **bracketed singleton facts** |
| `Decoherence.chainRegime_bracketed_singleton'` (@simp), `isCoherentClass_bracketed_singleton`, `count_bracketed_singleton_class`, `bracketed_singleton_quotient_certificate` — quotient-level lift of bracketed singleton classification | `Decoherence.lean` | ✓ (a) **bracketed singleton quotient cert** |
| `Decoherence.bracketed_singletons_append_coherent`, `bracketed_singletons_append_length`, `chainRegime_bracketed_singletons_append` — append-of-bracketed-singletons classification | `Decoherence.lean` | ✓ (a) **bracketed pair facts** |
| `Decoherence.exists_pureDecoherent_chain_length_one`, `actualization_length_one_count`, `actualization_length_one_rate`, `actualization_length_one_not_mixed`, `actualization_length_one_not_coherent`, `chainRegime_actualization_length_one`, `actualization_length_one_quotient_certificate` — length-1 actualization step characterization (counterpart of bracketed singleton) | `Decoherence.lean` | ✓ (a) **length-1 actualization** |
| `Decoherence.mixed_actualize_then_loop`, `mixed_actualize_then_loop_length`, `mixed_actualize_then_loop_rate`, `chainRegime_mixed_actualize_then_loop`, `mixed_witness_certificate` — explicit IsMixed chain construction (actualization-then-bracketed-loop, length 2, rate (1,2)) | `Decoherence.lean` | ✓ (a) **mixed witness** |
| `Decoherence.trichotomy_existence_super_certificate` — constructive existence of each regime: coherent at every k, pureDecoherent length-1, mixed length-2 | `Decoherence.lean` | ✓ (a) **constructive trichotomy super cert** |
| `Decoherence.IsCoherent.inhabited`, `IsCoherent.witness`, `witness_length`, `witness_isCoherent` — named extractor for coherent chains at every length | `Decoherence.lean` | ✓ (a) **coherent witness extractor** |
| `Decoherence.CoherentChain`, `PureDecoherentChain`, `MixedChain` subtypes; `CoherentChain.inhabited`, `PureDecoherentChain.inhabited`, `count_zero`, `endpoints_eq`, `regime_subtype_certificate` — typed carriers for regime-tagged chains | `Decoherence.lean` | ✓ (a) **regime subtype API** |
| `Decoherence.CoherentChain.append`, `length_append`, `append_count`, `append_assoc_count`, `coherent_chain_composition_certificate` — CoherentChain closure under append + composition algebra | `Decoherence.lean` | ✓ (a) **CoherentChain composition** |
| `Decoherence.CoherentChain.nil`, `nil_length` (@simp), `nil_count` (@simp), `nil_append_length`, `append_nil_length`, `coherent_chain_identity_certificate` — CoherentChain identity element + two-sided length identity laws | `Decoherence.lean` | ✓ (a) **CoherentChain identity** |
| `Decoherence.loop_submonoid_unbounded_length`, `loops_are_not_resets`, `loops_preserve_actualized` — loop submonoid is infinite + non-resetting | `Decoherence.lean` | ✓ (a) |
| `RealityChain'.length_one_count_*_iff_*`, `length_zero_implies_eq`, `actualizationCount_le_length` — quantitative characterizations | `TierB.lean` | ✓ (a) |
| `future_antitone`, `proper_past_growth_implies_actualization` — arrow dual + actualization detector | `TierA.lean` | ✓ (a) |
| **R7 conjecture stated precisely** | `Continuity.lean :: R7_Conjecture` | ○ (c) **CONJECTURE** |
| `SmoothConnectedAgency` scaffold | `Continuity.lean` | ✓ (a) scaffold only |
| `SmoothConnectedAgency.ofStrict`, `R7_Conjecture_of_strict` | `Continuity.lean` | ✓ (a) scaffold-level |
| `R7_Conjecture_holds_on_circleGPT`, `_qubitGPT` — R7 instance evidence | `Dichotomy.lean` | ✓ (a) **scaffold-level R7** |
| `HasMultiAxisAgency.toOneParameter`, `HasOneParameterAgency.ofMultiAxis` — multi/single axis bridges | `Continuity.lean` | ✓ (a) |
| `qubit_one_parameter_from_multi_axis` — concrete 3-axis → 1-axis specialization | `Dichotomy.lean` | ✓ (a) |
| `SEAMS.md` — catalog of 6 Tier A / Tier B seams | docs | ✓ documented |
| `V2_AUDIT.md` — honest re-examination of prior Tier B work | docs | ✓ documented |

### v2 architectural status

**Tier A foundation:** Lean formalization in place. Axioms I-II encoded
directly. Witkowski-Brown-Truong 2024 cited as mechanical content;
structural shadow theorem proved.

**Tier B reversible-limit:** Lean formalization of bracketing operation
in place. Vertex preservation reframed as derived theorem (v2-progressive,
not a v1 patch). The existing modules (Continuity, GPT, Hardy,
WantableGPT, CircleGPT, QubitGPT, QutritGPT, GPTTensor, Dichotomy) all
encode Tier B content valid under v2.

**Seams:** 6 cataloged in SEAMS.md. Seams 1-3 have formal correlates;
Seam 4-6 open.

**v2 audit:** A5-from-agency non-trivial at StrictConnectedAgency level;
triple no-go is BOTH sharp constraint and weakness diagnosis; vertex
preservation is v2-progressive; WantableGPT bridge novelty needs
Müller validation.

**Tier 1 program under v2: substantially complete with two-tier
architecture explicit.** Remaining open: derive QM structure
from Tier A bracketing (rather than postulate it as axiom strengthening),
R7 Lie-group proof, Renou-style rebit exclusion.
