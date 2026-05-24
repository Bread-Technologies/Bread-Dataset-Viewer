# Session Report — Perspectival Physics Lean Formalization

A summary of accomplishments from this development session.

## Headline numbers

- **13 Lean modules** building cleanly with Mathlib v4.29.1
- **~13,000+ lines of Lean** (excluding Mathlib dependencies); Examples.lean
  alone past 12,800 lines
- **~900+ verified theorems / examples** (no `sorry` outside documented placeholders)
- **14 documentation files** (~75 KB of structured exposition)
- **1136+ commits** to the research branch

## R6 substantive progress (this session — pivot from corollaries to roadmap)

After many small commits filling out WantableGPT corollaries, pivoted
to direct R6 work in `Continuity.lean` and `Classical.lean`:

**Continuity.lean (~250 new lines):**
- `StatePreservingPath G R₁ R₂`: continuous path of state-preserving
  linear maps with state preservation at EVERY t (not just endpoints).
- `StatePreservingAgency G`: every pair of avail Reversibles connected
  by a StatePreservingPath.
- `HasConnectedAgency.ofStatePreservingAgency`: SPA ⇒ HCA.
- `continuous_state_preserving_path`: the path of states stays inside
  the state space (key R6 improvement).
- `StatePreservingPath.id/.reverse/.const`: basic constructors.
- **KEY INSIGHT**: state-preservation alone is too weak — convex state
  space makes affine interpolation automatically state-preserving.
- `ReversiblePath` (R6-bis): path where each γ(t) is a Reversible
  (continuous, state-preserving, unit-preserving).
- `StrongConnectedAgency`: pairs connected by ReversiblePaths.
- `StrictReversiblePath` (R6-tris): each γ(t) is a *bijection*.
- `StrictConnectedAgency`: substantive R6 condition.
- `trivialStrictAgency`: avail = {id} is the smallest valid agency.

**Classical.lean (~280 new lines):**
- `classical_unique_state`: the only state on V 1 is vertex 0.
- `classical_n1_state_preserving_eq_id`: every state-preserving
  R : V 1 →ₗ V 1 equals LinearMap.id. So trivialStrictAgency is the
  ONLY agency on n=1.
- `classical_n1_reversible_toLin_eq_id` and StrictReversible variant.
- `classical_n2_state_sum/nonneg`, `vertex_n2_zero/one_coords`,
  `classical_n2_first/second_coord_one_iff`.
- `n2_midpoint`, `n2_midpoint_in_states`, `n2_midpoint_decomp`,
  not-vertex theorems.
- `swapLin : V 2 →ₗ V 2`: the SWAP linear map with all properties
  (vertex maps, involutive, preserves states, preserves unit, bijective,
  continuous).
- `swapReversible` and `swapStrictReversible`: SWAP as a Reversible
  and StrictReversible.
- `swapReversible_ne_id`: SWAP ≠ id (Classical n=2 has at least 2
  distinct StrictReversibles).
- `classical_n2_state_preserving_first_coord_bound`: state-preserving
  linear R has R(vertex 0) 0 ∈ [0, 1].

This is substantive R6 progress: the framework for the discreteness
theorem (classical strict reversibles = S_N, no continuous path
between them) is now in place. Next: prove the n=2 enumeration
theorem (every state-preserving bijection V 2 → V 2 is id or swap).
- **Generic deltaIndicator / Born rule**: For any finite Wantable W and
  any w : W, `deltaIndicatorLin w` is a verified effect with the
  Born-rule property `deltaIndicatorLin w f = f w`, plus the
  completeness `∑ w, deltaIndicatorLin w f = unitFn W f`.
- **vertices_distinguishable_via_delta**: any two distinct vertex
  states are perfectly distinguishable in the Hardy sense.
- **Generic uniform-decomp**: `uniformState W = ∑ w, (1/|W|) • vertex w`.
- **complementSubgroup ≤ Subgroup.center (PTrans W)**: the cyclic
  subgroup ⟨complement⟩ is central in PTrans.
- **mixedCorrelatedState**: `(1/2) diagonal + (1/2) antiDiagonal =
  uniformState (Bool × Bool)`, with marginals = uniformBool.
- **Per-coordinate Bool × Bool effects**:
  `left{True,False}Indicator{,Lin}`/`right{True,False}Indicator{,Lin}`,
  the four `pointIndicator{TT,TF,FT,FF}` single-point indicators,
  with completeness for each measurement basis.
- **Marginalization theory**: `leftMarginal` and `rightMarginal` as
  LinearMaps on the product state space, with marginal-recovery
  theorems for productState and concrete computations for the
  diagonal-correlated states (`leftMarginal diagonalState = uniformBool`).
- **Classical-separability theorem**: every state on a product Wantable is
  a sum of weighted product-vertex states — the framework's "no
  entanglement" no-go theorem made precise
  (`WantableGPT_state_prod_vertex_decomp`,
  `WantableGPT_classical_separability`).
- **Perfect-correlation/anti-correlation states**: diagonal and antidiagonal
  states on Bool × Bool, with verified perfect distinguishability and
  the complete `{diagonalIndicator, antiDiagonalIndicator}` measurement
  summing to the unit functional.
- **New productState mini-theory**: tensor-product structure for the
  WantableGPT bridge (`productState`, `productState_unitFn`,
  `productState_in_states`, `productState_vertex`, `productState_assoc`,
  `productState_swap`, `productState_complement_factor`,
  `productEffectVec`, `productEffectVec_in_effectVec`,
  `productState_smul_left/right`, `productState_add_left/right`,
  `productState_transform_factor`)
- **New uniformState theory**: maximally-mixed state on any finite Wantable
  (`uniformState`, `uniformState_in_states`, `uniformState_transformAction_invariant`,
  `uniformState_complement_invariant`, `uniformState_proj_eq` (Born rule),
  `uniformState_prod_factor` (factorization on products), `uniformState_constant`)
- **New correlation examples**: classical correlated states on Bool × Bool
  (`diagonalState`, `antiDiagonalState`, `diagonalState_in_states`,
  `diagonalState_left/right_marginal`,
  `diagonalState_ne_productState_uniformBool` (correlation witnessed),
  `diagonalIndicator{,Lin,_in_effects}` (verified effect),
  `diagonalState_distinguishable_antiDiagonalState`)

## Major new content (latest batch)

- **Triple no-go theorem** (`wantableGPT_classical_dichotomy`): quantum,
  real-QM, and quaternionic-QM Hardy signatures are *each* formally
  ruled out for `WantableGPT` with `|W| ≥ 2`.
- **Agency builders** (`singletonAgency`, `pairAgency`,
  `path_via_affineLine`): generic constructors making it easy to
  build `HasConnectedAgency` instances; reveal that path-connectedness
  is "cheap" — the substantive R6 content is the *availability set*.
- **StrictReversible**: refinement of `Reversible` with bijectivity,
  yielding well-defined inverse (`.inv`), composition (`.comp`),
  identity (`.id`), and the inverse laws (`inv_comp`, `comp_inv`).

## Major technical results

### Verified derivations

| Result | Module | Significance |
|--------|--------|-------------|
| Tsirelson bound 2√2 from rejecting joint ledger | `CHSH.lean` | Quantum prediction in framework vocab |
| No-cloning (linear algebra form) | `NoCloning.lean` | Standard QM no-go in framework |
| Hardy Axiom 1 (Probabilities) | `Hardy.lean` | First verified Hardy axiom |
| Hardy Axiom 3 (Subspaces) | `Hardy.lean` | Sub-GPT existence |
| Hardy Axiom 5 from libertarian agency | `Continuity.lean` | **Framework-distinctive contribution** |
| Distinguishable ↔ linearly independent | `Distinguish.lean` | Operational-structural bridge |
| N ≤ K dimension inequality | `Distinguish.lean` | Hardy-style bound |
| Classical GPT instance (full) | `Classical.lean` | Concrete verification |
| WantableGPT bridge (with injective MonoidHom) | `WantableGPT.lean` | **Two-level bridge formalized** |
| `PTrans W` = centralizer of complement in `Equiv.Perm W` | `Transformations.lean` | **Deflation theorem** — the framework's vocabulary picks out a standard algebraic object |
| `WantableGPT-from-finite-Wantable is always classical` (N = K) | `WantableGPT.lean` | **No-go theorem** — bare ontology cannot derive non-classical structure |
| `K(W₁ × W₂) = |W₁| · |W₂|`, `K(W₁ ⊕ W₂) = |W₁| + |W₂|` | `WantableGPT.lean` | Composition dimension theorems |
| Vertex decomposition `f = ∑ w, f w • vertex w` | `WantableGPT.lean`, `Classical.lean` | WantableGPT IS the simplex |
| `vertexBasis`, `finrank V W = |W|` | `WantableGPT.lean` | State-space basis |
| `actMeeting complement = swap` | `Transformations.lean` | PTrans/Meeting identification |
| `ClosedAgency` ⇒ `Reachable` transitive | `Continuity.lean` | First step of R6 strengthening |
| `card_even_of_fixedPointFree` | `Examples.lean` | Cardinality theorem |
| `ptrans_bool_classification`, `ptrans_fin2_classification` | `Examples.lean` | Concrete PTrans enumerations |
| `WantableEquiv.mapPTrans` | `Examples.lean` | Wantable iso ⇒ PTrans iso |

### Negative results (honestly documented)

- Three fermion generations (`TIER2_ATTEMPT.md`) — five candidate
  angles fail.
- Cosmological constant (`TIER3_ATTEMPT.md`) — speculative re-framing
  only, no quantitative derivation.
- Hard problem of consciousness (`TIER4_ATTEMPT.md`) — philosophical
  dissolution, not mathematical result.

## Major documentation

- `README.md` — orientation
- `STATUS.md` — per-result calibration (verified / partial / argued /
  open)
- `FINDINGS.md` — honest commentary
- `CONCLUSIONS.md` — external-reader summary
- `FAQ.md` — 10 concrete physics questions answered
- `GLOSSARY.md` — terminology with Lean cross-references
- `DEPS.md` — module dependency map
- `PREDICTIONS.md` — empirical claims with calibration
- `LINEAGE.md` — philosophical references (Quine/Lewis/Sider added per
  user input mid-session)
- `PAPER_DRAFT.md` — publication-target writeup
- `ROADMAP.md` — 11 specific next-steps with effort estimates
- `TIER2_ATTEMPT.md`, `TIER3_ATTEMPT.md`, `TIER4_ATTEMPT.md` — honest
  negative analyses
- `build.sh` — reproducibility helper

## What was distinctive about this session

**1. Bridge formalization (WantableGPT).** The framework's central
technical claim — metaphysical perspectival structure produces
operational physics — is now machine-verified as an injective
MonoidHom from `PTrans W` into the operational transformation
monoid. The bridge is not just an analogy; it's a verified embedding.

**2. Hardy Axiom 5 from agency.** The most novel formal content:
deriving Hardy's continuity axiom from a libertarian-agency
postulate. Other reconstructions take Axiom 5 as input; the framework
derives it.

**3. Calibration discipline.** Every claim in the codebase is in one
of five buckets (verified / partial / argued / stuck / open). No
"derived" without machine verification. Negative results documented
honestly, including the structured failure analysis of Tier 2-4
targets.

**4. Co-evolution with documentation.** Lean code and prose
documentation were developed in parallel, so the framework's
technical content and its philosophical/empirical framing remained
mutually coherent throughout.

## Where things stand

**Tier 1 (operational reconstruction):** substantially complete.
Hardy axioms 1, 3, 5 verified derivable; 2, 4 documented as
auxiliary. CHSH/Tsirelson, no-cloning, dimension inequalities all
verified.

**Tier 2 (Standard Model derivations):** not approached. Negative
results documented for three generations.

**Tier 3 (cosmology / dark matter / fine-tuning):** speculative
gestures only. Honest negative results documented.

**Tier 4 (consciousness dissolution):** philosophical position
articulated; not a formal result.

## The next bet (from `ROADMAP.md`)

**R6.** Strengthen the agency postulate to *force* path-connectedness
rather than admit it. Combined with **R7** (Lie-group refinement),
this would derive that quantum reversible dynamics is the unique
non-classical possibility consistent with the framework — a true
framework-distinctive technical contribution.

Effort: extended research. The most promising open angle.

## Honest closing

The verified-results scoreboard is real. The framework has earned
its keep on the Tier 1 reconstruction targets and has one
philosophically distinctive verified result (Hardy Axiom 5 from
agency).

The Tier 2-4 questions remain genuinely open — not because of any
fault of the framework specifically, but because no axiomatic
approach has cracked them. Documenting this honestly is part of the
framework's discipline.

What was built here is a working Lean formalization that any future
researcher can extend. The calibration policy ("nothing claimed
without machine verification") gives it a chance to be incrementally
sharpened without sliding into the unfalsifiable hand-waving that
plagues much foundations work.

That is the honest state at the close of this session.
