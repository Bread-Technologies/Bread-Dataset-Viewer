# Research Roadmap

Concrete next steps for continuing the program, ordered by tractability
and impact. Read after `STATUS.md` and `CONCLUSIONS.md`.

## Tier 1: Tractable extensions (weeks)

### R1. Prove vertices are pure states of the classical simplex

`Classical.vertex n i` should be an extreme point of `Classical.gpt n`
in the sense of `Continuity.PureState`. The argument is the standard
"if `t·x + (1-t)·y = eᵢ` with `x, y ∈ Δⁿ` and `t ∈ (0,1)` then
`x = y = eᵢ`": coordinate-wise analysis forces every coordinate to
match.

Estimated effort: 50–100 lines of Lean. Mathlib provides
`convex_stdSimplex` but not (yet) the extreme-point characterization;
it would need to be developed.

### R2. Strengthen Hardy Axiom 3 with operational-dimension preservation

The current `axiom3_holds` proves existence of a sub-GPT; Hardy's
"behaves like a system of dimension M" additionally requires the
sub-GPT's operational dimension matches. Statement and proof would
combine `axiom3_holds` with the structure of the sub-state-space's
linear span.

Estimated effort: 100 lines + supporting lemmas.

### R3. Lin-indep wrapper for no-cloning

Connect `no_cloning` (which uses a bilinear-form hypothesis) to
`LinearIndependent ℝ ![v₁, v₂]` via `Basis.constr` + `LinearMap.exists_leftInverse_of_injective`.
A previous attempt encountered typeclass-resolution timeouts. The fix:
careful explicit annotations, or working in `FiniteDimensional ℝ V`.

Estimated effort: 100 lines once the typeclass interaction is sorted.

### R4. Quantum GPT instance (2-dim qubit)

Build the qubit GPT explicitly:
- `V := { M : Matrix (Fin 2) (Fin 2) ℂ // M = star M }` — Hermitian
  2×2 complex matrices, viewed as ℝ-vector space (dim 4).
- `states := { ρ // 0 ≤ ρ ∧ trace ρ = 1 }` — density matrices.
- `effects := { E // 0 ≤ E ∧ E ≤ I }` — POVM elements.

Verify the GPT structure. Then prove (vs. the classical instance):

  - `Classical.gpt n` has discrete reversible-transformation set
    (permutations); cannot satisfy a non-trivial `HasConnectedAgency`.
  - The qubit GPT (with unitary reversibles) does — `U(2)` is a
    connected Lie group.

This makes the framework's classical-vs-quantum dichotomy *formally
verifiable* at the level of the agency-axiom satisfaction.

Estimated effort: 300–500 lines + significant Mathlib infrastructure
work (positivity for matrices, density-matrix predicates, etc.). May
benefit from importing Physlib instead of building from scratch.

### R5. Tensor product of GPTs (Hardy Axiom 4)

A GPT composition operator. Build `gptTensor (G₁ : GPT V₁) (G₂ : GPT V₂) : GPT (V₁ ⊗ V₂)`
with at least the *product-state* component (separable states; possible
extensions to entangled state spaces are theory-dependent).

Then prove the multiplicative dimension property `N_⊗ = N₁ · N₂` for
the simplest case (product of perfect-distinguishability sets).

Estimated effort: 300–400 lines.

## Tier 2: Framework-distinctive contributions (months)

### R6. Forcing path-connectedness from agency

The framework's central open question — **and now made more urgent by
the no-go theorem `wantableGPT_is_classical`**, which establishes that
the bare WantableGPT bridge cannot deliver non-classical structure.
Any quantum derivation must come from the agency refinement.

State a refinement of the agency postulate that, given the broader
perspective-wanting structure, *forces* path-connectedness of
reversible transformations rather than admitting it as a hypothesis.

One candidate: "at every instant there are infinitely many available
transformations, with no smallest non-trivial choice." Formalize as
a density condition + closure under composition. Show this implies
connectedness in a natural topology.

Partial step now complete: `ClosedAgency` extends `HasConnectedAgency`
with closure under composition, and yields transitivity of the
`Reachable` relation (`Reachable.trans`). This is the first piece of
the strengthening. R6 proper requires moving from closure to density.

**Insight (Lean: `path_via_affineLine`).** Path-connectedness in
`HasConnectedAgency` is "cheap" when V has the appropriate topological
structure (TopologicalSpace + ContinuousAdd + ContinuousSMul): the
affine interpolation `γ t = (1-t) R₁ + t R₂` is automatically jointly
continuous. So the substantive content of `HasConnectedAgency` is the
*availability set* itself, not the path-connectedness condition.
R6 therefore needs to:
- Restrict `avail` to "physical" reversibles (e.g., those preserving
  the state space along the path, not just at endpoints),
- And/or postulate that `avail` is *dense* in a topologically rich
  subset of `Reversible G`.

The current `path_via_affineLine` does not preserve state-preservation
along the path; it only matches at endpoints. Strengthening to a path
of state-preserving transformations is the key open piece.

Estimated effort: extended research. Likely interleaves with the
philosophical work in `LINEAGE.md`.

### R7. Lie-group refinement

Strengthen `HasConnectedAgency` to a *Lie-group* postulate (smooth
manifold structure on the transformation group, smooth action on
state space). Prove that the framework predicts the reversible
transformation group is necessarily a *connected Lie group*, not just
path-connected.

This bridges to the standard QM picture where reversible dynamics is
`U(N)`, a connected Lie group. The framework would then directly
distinguish quantum dynamics from classical (discrete `S_N`) at the
axiom level.

Estimated effort: extended research, requires Mathlib Lie-group infrastructure.

## Tier 3: Genuinely open / speculative (years)

### R8. Gauge group derivation

Argue (with formal scaffolding where possible) that the framework's
"forces are connections" reading constrains the gauge group structure.
Currently: no path is known to derive U(1)×SU(2)×SU(3) from any
axiomatic system. Specific particle content (fermion generations,
matter representations) is empirical input in all known approaches.

### R9. Dark matter multi-sector — quantitative

Move P5 in `PREDICTIONS.md` from Suggested to Derived. Requires:
- Multi-sector model with specific composition data.
- Lagrangian-level coupling structure.
- Quantitative gravitational signatures distinguishing multi-sector
  from single-species CDM.
- Experimental tests (proposed observations).

### R10. Cosmological constant — relational calculation

P6: replace the standard QFT zero-point sum (yielding 10¹²⁰ excess)
with a relational measure counting actual rather than potential
meetings. Concrete formula and reduction to observed Λ. No path
currently known.

## Tier 4: Philosophical articulation

### R10b. Multi-sector dark matter, formal model

Move P5 in `PREDICTIONS.md` toward Derived status by:
1. Choosing an N-sector composition data (specific Wantable structure
   for each sector, e.g., N disjoint Wantables).
2. Postulating gravity as universal coupling across sectors.
3. Demonstrating quantitatively distinct gravitational signatures
   (halo profile, substructure, scaling laws).

Estimated effort: substantial research with cosmological-simulation
collaborators. Out of scope for pure Lean work but suitable for a
follow-on paper.

### R11. Quine–Rovelli formalization

Move P-A3 (the Quine–Rovelli parallel) from prose to a formal claim
at the level of category-theoretic universal properties: show that
"reference is inscrutable up to translation manual" (Quine semantic)
and "facts are observer-dependent up to relational frame" (Rovelli
physical) are different concrete instances of a single universal
property in a suitable category.

This is conceptually novel work; success would constitute a real
unifying claim across semantic and physical levels.

## Session updates (latest)

### Done this session

- **R6 Birkhoff disconnect for Classical n=2**: `classical_n2_strict_reversible_path_id_swap_empty` formally proves no continuous bijective state-preserving path connects id to swap on Classical Bool. Formally hypothesis-free.
- **R6 n=2 enumeration**: `classical_n2_det_one_eq_id` and `classical_n2_det_neg_one_eq_swap` — det=±1 state-preserving Rs are exactly id/swap. Plus `classical_n2_state_preserving_determined` parametrizes the Birkhoff polytope at n=2.
- **R7 algebraic scaffold**: `GroupClosedReversiblePath` / `GroupClosedAgency` in Continuity.lean. `trivialGroupClosedAgency` witness for any GPT.
- **Tier 1 #2 Hardy A4**: BOTH halves derived for WantableGPT — `Hardy_Axiom4_WantableGPT_dimension` (dimension multiplies) and `Hardy_Axiom4_WantableGPT_state_exists` (state-half existence) — plus `productStateBilin` as the bilinear-map packaging.
- **Tier 2 #6 baby step**: `scaleHom` continuous-PTrans witnesses on ℝ. Three distinct PTrans ℝ shown.
- **Tier 3 #11 Lean step**: `MultiSectorWantable n W` construction (sigma-type) plus 11 worked examples and cardinality-distinctness.
- **Axiom refinement**: `PatternStableWantable` typeclass in Ontology.lean — formulation (a) trivial-stability scaffold + instances for Bool/Fin n/Bool×Bool.
- **Documentation**: ORIGINAL_PROMPT.md, TIER1_5_HILBERT.md, TIER2_GAUGE_SCOPING.md, TIER3_DARK_MATTER.md, TIER4_DISSOLUTIONS.md, R6_GENERAL_N_SCOPING.md, HARDY_A2_AS_PARSIMONY.md, MULLER_DIVERGENCE.md, PATTERN_STABLE_WANTABLE.md. STATUS.md, FINDINGS.md, CONCLUSIONS.md, PAPER_DRAFT.md refreshed.

### Next critical-path priorities

1. ~~**R6 general-n via det-sign**~~ — **DONE**: `classical_general_no_strict_path_id_to_swap01` for any n ≥ 2 via `Matrix.toLin' ∘ Equiv.Perm.permMatrix`. Handles transpositions / det = -1 elements.
2. ~~**R6 closure for ALL non-id permutations**~~ — **DONE via discreteness**: `classical_general_no_strict_vertex_preserving_path_id_to_perm` for any σ ≠ 1 under a vertex-preserving path hypothesis. Critical mathematical correction: the naive "state-preserving bijection = permutation" claim is FALSE for n ≥ 3 (counterexample: t·I + (1-t)·C bijective throughout for the 3-cycle C). The discreteness argument requires the additional vertex-preservation hypothesis on paths.
3. ~~**L6 TransitiveAgency under vertex-preservation**~~ — **DONE**: `classical_general_vertex_preserving_no_transitive_agency_unconditional` — no TransitiveAgency on Classical n ≥ 2 when underlying strict paths preserve vertices.
4. ~~**R1 forward + reverse**~~ — **DONE**: `vertex_is_pure` (vertex is pure state) AND `pure_state_of_classical_is_vertex` (pure state is vertex). The pure ⇔ vertex equivalence in Classical is fully formalized.
5. ~~**L7 PurePreservingTransitiveAgency on Classical, UNCONDITIONAL**~~ — **DONE**: `classical_general_no_pure_preserving_transitive_agency`. Combined with R1 forward + reverse, the L7 no-go is unconditional.
6. ~~**CircleGPT positive existence (UNCONDITIONAL)**~~ — **DONE**: `CircleGPT.circleTransitiveAgency_unconditional` — non-degenerate TransitiveAgency on a non-classical GPT. The pure-state classification is closed via `pure_state_classification_holds`.
7. ~~**Hardy A5 strong-form bridge**~~ — **DONE**: `Hardy.axiom5_strong_of_transitive_agency` packages `Continuity.TransitiveAgency.hardy_axiom5` into the substantive form of A5.
8. ~~**Dichotomy theorem**~~ — **DONE**: `Dichotomy.framework_dichotomy_existential` — single Lean expression of the classical-vs-quantum dichotomy.
9. **R7 Lie-group bridge** — needs Mathlib LieGroup wiring. The single biggest remaining piece; with CircleGPT we have the U(1) example concretely; making the avail set into a topological group with smooth structure is the next step.
10. **Vertex-preservation as axiom**: investigate whether vertex-preservation along paths is forced by the framework's pattern-stability metaphysics (Axiom IV) or must be added as an additional operational postulate. This is the key open methodological question after the R6 correction.
11. **PatternStableWantable formulation (b)**: reachable-closure / orbit-cardinality non-trivial stability predicate. (Mostly done via Stable_nontrivial.)
12. **u(1) toy formalization**: per TIER2_GAUGE_SCOPING.md, the smallest non-trivial Lie-group gauge instance.
13. **gptTensor**: tensor-product-of-GPTs construction, S1 tomographic locality. (In progress.)
14. **qQM exclusion via local tomography** (S1 step in TIER1_5_HILBERT.md): once gptTensor lands, prove K_AB = K_A · K_B for the tensor — qQM violates this. Smallest tractable Tier 1 #5 piece.

## Methodology constants

For all of the above:

- **Every non-trivial derivation in Lean.** Prose arguments are
  working notes, not results. No `derived` without machine-verified.
- **Honest documentation of failure.** When stuck, document the
  precise bottleneck. Update `FINDINGS.md` / `PREDICTIONS.md`
  immediately when status changes.
- **Cross-check with existing programs.** Where framework predictions
  align with Hardy / CBH / Müller / Renou, cite. Where they deviate,
  flag and design tests.
- **No realist drift.** The default is realist physics; the framework
  rejects it. Maintain perspective-first reading throughout.
- **No compatibilist drift.** Free-will-as-substantial is rejected;
  agency at the instant, identity in the pattern. Don't soften.
- **Metaphysics-fixed, axioms-adjustable** (per user clarification).
  When current axioms can't derive a Tier target, refine the formal
  axiom encoding (preserving the §2 metaphysics). PatternStableWantable
  is the first such refinement in this session.
