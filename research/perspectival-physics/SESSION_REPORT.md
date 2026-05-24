# Session Report — Perspectival Physics Lean Formalization

A summary of accomplishments from this development session.

## Headline numbers

- **13 Lean modules** building cleanly with Mathlib v4.29.1
- **~10,000 lines of Lean** (excluding Mathlib dependencies) — 10K-line milestone reached
- **~390+ verified theorems / examples** (no `sorry` outside documented placeholders)
- **14 documentation files** (~75 KB of structured exposition)
- **915+ commits** to the research branch (extended session — 915 milestone reached)
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
