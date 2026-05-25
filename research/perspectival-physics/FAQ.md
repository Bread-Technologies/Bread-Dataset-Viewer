# FAQ — Concrete Questions the Framework Answers

A short list of physics-foundational questions and the framework's
verified-in-Lean answers. For full context see `PAPER_DRAFT.md` and
the cited modules.

## Q1. Why is the CHSH bound 2√2 (Tsirelson), not 2 (Bell)?

**Framework answer:** Because there is no observer-independent joint
ledger of facts. Algebraically, the bound is 2 in the commutative
case (which IS the joint-ledger case) and 2√2 in the noncommutative
case. The framework rejects the joint-ledger assumption
(Frauchiger–Renner C-drop; Quine's ontological relativity at the
semantic level; Rovelli's relational QM at the physical level), so
lands on Tsirelson.

**Verified:** `Perspectival/CHSH.lean :: bound_realist`,
`bound_perspectival` (via Mathlib's CHSH module).

## Q2. Can an unknown quantum state be cloned?

**Framework answer:** No. Any linear cloner on a set containing two
linearly independent vectors (and their sum) yields a contradiction
via the cross-term cancellation forced by linearity.

**Verified:** `Perspectival/NoCloning.lean ::
no_cloning_of_linear_independent`.

**Framework reading:** A "want" cannot be duplicated into two isolated
copies; wanting is intrinsically two-sided (Axiom II). Linearity is
the structural shadow of this two-sidedness.

## Q3. What is the maximum number of perfectly distinguishable states
in an N-dimensional state space?

**Framework answer:** Exactly N. A family of N perfectly
distinguishable states is linearly independent; in a finite-dim state
space of dimension N, this is the maximum possible.

**Verified:** `Perspectival/Distinguish.lean ::
perfect_distinguishable_imp_linear_independent`,
`operational_dim_le_state_dim`.

## Q4. Why does quantum mechanics have continuous reversible dynamics
between pure states, while classical theory does not?

**Framework answer:** Because libertarian agency, formalized as
path-connectedness of the reversible-transformation group, forces it.
Given the agency postulate and transitivity on pure states, between
any two pure states there exists a continuous path of reversible
transformations realizing the change.

Classical theory's reversible transformations are *discrete*
(permutations), so it cannot non-trivially satisfy the agency
postulate.

**Verified:** `Perspectival/Continuity.lean ::
hardy_axiom5_of_agency`, `hardy_axiom5_transitive`.

**Framework reading:** This is the framework's most distinctive
technical contribution. The agency postulate is the philosophical
commitment that makes the difference; the derivation of Hardy
Axiom 5 from it is novel formal content.

## Q5. Why can't broadcasting (general copying) be done quantumly,
even when cloning is impossible?

**Framework answer:** Classically, broadcasting is *possible* (just
diagonal copy). Quantumly, it is *impossible* for non-commuting states
(Barnum–Caves–Fuchs–Jozsa–Schumacher 1996). The framework constructs
the classical broadcaster explicitly. The quantum impossibility
requires density-matrix machinery beyond our current import scope
and is documented as open.

**Verified:** `Perspectival/NoBroadcasting.lean :: classicalBroadcaster`
(classical case). Quantum case: OPEN.

## Q6. What is the formal status of "different observers, different
facts"?

**Framework answer:** This is the framework's rejection of the C
axiom (consistency of observer reports) in Frauchiger–Renner. It is
*encoded* as the absence of an observer-independent joint algebra of
observables, which manifests as the noncommutativity hypothesis in
the CHSH bridge. The framework's predictions are then those of the
noncommutative case (Tsirelson, not Bell).

**Verified:** `Perspectival/CHSH.lean :: bound_perspectival` (the
noncommutative case is exactly the bound the framework predicts).

## Q7. Does the framework give a unique GPT, or many?

**Framework answer:** Currently, *many*. The framework's axioms I–IV
are too weak to pin down a single GPT. The classical n-outcome
instance (`Classical.gpt n`) and the WantableGPT instance
(`WantableGPT.gpt W`) are both consistent with the framework. The
quantum GPT (a qubit) would also be consistent. The framework is
*permissive* about which GPT is realized; deriving a unique answer
would require additional structure (the most plausible: the agency
postulate + connectedness picking out quantum).

**Verified:** Both `Classical.gpt` and `WantableGPT.gpt` are
machine-verified `Perspectival.GPT` instances. Moreover, a verified
**no-go theorem** (`WantableGPT.wantableGPT_is_classical`) establishes
that the bridge from a *finite* Wantable to a GPT via
`WantableGPT.gpt` *always produces classical signature* (N = K = |W|),
ruling out quantum signature for this particular bridge construction.
Quantum structure must therefore come from one of: (i) additional
postulates on top of I–IV (continuity / agency, composition rules), or
(ii) a different bridge construction (e.g., infinite-dimensional
Wantable, or a complex-vector-space variant of WantableGPT).

## Q8. Why three generations of fermions?

**Framework answer:** *Unknown.* This is honest: the framework's
axioms I–IV are silent on the generation count. Multiple candidate
angles (higher-order complement, hidden symmetries, anomaly
cancellation, topology, universal properties) fail to give a
derivation. The Standard Model takes three generations as input, and
the framework does the same.

See `TIER2_ATTEMPT.md` for the structured failure analysis.

**Verdict:** Honest negative result.

## Q9. Cosmological constant, fine-tuning, dark matter?

**Framework answer:** *Speculative.* The framework gestures at
relational/structural readings (Λ as "category error" for treating
vacuum as substantial; multi-sector dark matter from disjoint
Wantables) but does not produce quantitative predictions.

See `PREDICTIONS.md` for the calibrated catalog.

**Verdict:** Honest open questions; no formal content in this codebase.

## Q10a. What are the simplest examples?

**Framework answer:** The boolean Wantable (`Bool` with
`complement := not`) is the canonical minimal non-trivial example.
The WantableGPT on `Bool` has two vertices (`vertex true`, `vertex false`),
the complement action swaps them, and the projection `proj true`
operationally distinguishes them. See `Examples.lean` for these and
others (Fin 2, ℤ, Unit, Empty, product Wantables).

## Q10b. Are there examples I can play with?

**Framework answer:** Yes — `Perspectival/Examples.lean` contains a
dozen-plus worked examples on the simplest Wantables (Bool, Fin 2,
Fin 3, Fin 4, ℤ, Unit, Empty, Bool × Bool, Bool ⊕ Bool, lists,
options, function spaces) showing the framework in action.

## Q11. What is the framework's resolution of the measurement problem?

**Framework answer:** Measurement is not a separate axiom; it is the
actualization event re-entering the Tier B (operational, reversible)
description. The framework's two-tier architecture:

- **Tier A:** irreversible meeting-structure. Wanting → actualization.
- **Tier B:** reversible-limit emerging from bracketing actualization
  events. Unitary evolution lives here.

Standard QM postulates unitary evolution AND collapse separately,
creating the measurement problem (when does collapse happen? Is it
"real" or epistemic?). The framework dissolves this by deriving both
from a single foundation:

- Between actualization events, Reality evolves "unitarily" (Tier B,
  bracketed). The status function is invariant; the relational
  configuration evolves reversibly.
- AT an actualization event, the system + apparatus meeting clears,
  irreversibly. The actualized set grows.

Formalized in `Perspectival/TierA.lean` (axioms I-II + actualization)
and `Perspectival/TierB.lean` (bracketing + measurement_is_actualization
theorem). See `SEAMS.md` for the catalogue of where Tier A leaks
through Tier B as measurable / observable signatures.

## Q12. Why a "two-tier" architecture?

**Framework answer:** Because the foundation is irreversible (wanting
is directional, actualization is one-way) but the standard physics
formalisms (QM unitary evolution, GR field equations) are reversible
in their natural form. The mismatch was the v1 program's central
problem — every place the formalization broke was where the
irreversible foundation leaked through.

The v2 architectural correction makes this two-tier structure
explicit: Tier A is the irreversible foundation; Tier B is the
reversible limit emerging by bracketing actualization events. The
framework's distinctive empirical content lives at the *seams* —
where Tier A content leaks through Tier B (measurement, vertex
preservation, decoherence, Lyapunov instability at erasure points).

The user's published paper (Witkowski, Brown, Truong, Entropy 2024,
26(3), 203) grounds Axiom II mechanically: reset/erasure is strictly
impossible under conservative (reversible) dynamics, by Picard-
Lindelöf. This is the same fact the two-tier architecture rests on.

## Q13. What is entropy in the framework?

**Framework answer:** Entropy is not a property the universe has;
it is *subjectivist coarse-graining* (Jaynes). An observer's count of
distinguishable macrostates over their coarse-graining IS the entropy.
Different perspectives use different coarse-grainings; different
coarse-grainings yield different values. This is real subjectivism —
the multiplicities are real (physical construction determines them);
the count is perspective-relative.

The framework owns the word "subjectivism" rather than relabeling to
gain realist respectability. See
`ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md` for the full statement and
the discipline of catching substantialist drift.

## Q14. How does the framework derive the Second Law?

**Framework answer:** Via a both-halves argument:
1. **Subjectivist count (Jaynes):** entropy = observer-relative count
   of distinguishable macrostates.
2. **Physical construction:** what counts as distinguishable is
   structurally determined (not arbitrary).
3. **Many-to-one collapse:** reducing the count requires collapsing
   the coarse-graining — a many-to-one map on phase space.
4. **Mechanical impossibility:** many-to-one is forbidden under
   conservative dynamics (Picard-Lindelöf, WBT 2024).
5. **kT ln 2 cost:** forcing the collapse via nonconservative dynamics
   costs at least kT ln 2 per bit (Landauer).

Therefore observer-relative entropy does not decrease under
conservative dynamics, and forcing a decrease costs kT ln 2 per bit.
Subjectivist where subjectivist (count); mechanical where mechanical
(cost of collapse). **The Second Law is necessary, not contingent,
and grounded in the user's published paper, not in statistical-
mechanical postulate.**

See `ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md` and `SEAMS.md` Seam 3.

## Q15. Past Hypothesis, Boltzmann brains, black hole entropy?

**Framework answer:** All three are puzzles built on entropy-as-
substance ontology. Once entropy is reframed as subjectivist coarse-
graining (per addendum):
- **Past Hypothesis dissolves** — "low entropy in past direction"
  is constitutive of past, not a contingent fact.
- **Boltzmann brains dissolve** — no substantial high-entropy
  state-space to fluctuate.
- **Black hole entropy reframes** — S = A/4 = dimensionality of
  distinguishable-from-outside structure under outside-observer
  coarse-graining; not horizon-substance.

See `TIER4_DISSOLUTIONS.md` items #17-#22.

## Q16. How are multi-step trajectories formalized?

**Framework answer:** Via the `RealityChain` inductive type in
`Perspectival/TierB.lean`. A `RealityChain P C R₁ R_n` is a finite
sequence of `TrajectoryStep`s linking Reality states from R₁ to R_n,
where each step is either:
- **bracketed** (Tier B reversible inter-event evolution), or
- **actualization** (Tier A irreversible seam crossing).

The chain admits three count functions:
- `actualizationCount` : number of seam crossings
- `bracketedCount` : number of reversible steps
- `length` : total step count

These satisfy `counts_sum` (`actualization + bracketed = length`) and
`append additivity` (counts of `ch₁.append ch₂` are sums of
component counts).

**Key theorems:**
- `bracketed_only_implies_eq` : a chain with 0 actualizations has
  R₁ = R₂ (bare Tier B is trivial on Reality function).
- `distinct_endpoints_implies_actualization` : R₁ ≠ R₂ forces at
  least one seam crossing along the chain.

These make the framework's "evolution + measurement" architecture
operationally concrete and computable.

## Q17. What's the difference between `RealityChain` and `RealityChain'`?

**Framework answer:** Both are inductive types representing
trajectories of Reality states linked by TrajectoryStep witnesses.
The difference is in the steps themselves:

- `RealityChain` uses bare `TrajectoryStep` (bracketed | actualization).
  This does NOT generally imply `RealitySuccessor` along the endpoints
  because the actualization arm carries only an `AtSeam` witness, which
  doesn't preserve the actualized-set invariant.

- `RealityChain'` uses `TrajectoryStep'` (step + is_successor pair).
  Each step explicitly carries a `RealitySuccessor` witness, so chains
  built from `TrajectoryStep'` automatically imply
  `RealitySuccessor R₁ R_n` via `RealityChain'.implies_successor`.

The strict version supports a substantial **iff theorem**:
`R₁ ≠ R₂ ↔ actualizationCount > 0` (i.e., `eq_iff_zero_count`). The
plain version only has the forward direction.

**Constructors:** `TrajectoryStep'.bracketed` (any bracketed
transition lifts) and `actualizeAt_strict_step` (any pointwise
actualization at a potential meeting lifts).

**Forgetful map:** `RealityChain'.toRealityChain` discards the
successor evidence to recover a plain chain. Length and
actualizationCount are preserved.

## Q18. Is there a formal Lean module for decoherence?

**Framework answer:** Yes — `Perspectival/Decoherence.lean`
formalizes the framework's Seam 4 reading of decoherence (per
`SEAMS.md`): decoherence as the accumulated effect of Tier A
actualization events at the system-environment interface.

**Core content:**
- `actualizationRate` : the count-based rate (count, length) along
  a strict chain.
- `coherent_regime` : count = 0 → rate (0, length).
- `decoherence_regime` : bracketed = 0 → rate (length, length).
- `concatenated_decoherence` : rate composes coordinate-wise under
  chain concatenation.
- `decoherence_certificate` : single Lean expression bundling these.

**What's NOT formalized:**
- Continuous-time exponential-suppression dynamics.
- Operational definitions of "environment Tier A density".
- Quantitative decoherence-time predictions.

These open extensions are documented as Tier 2 work. The current
module establishes the count-based structural shadow.

## Q10. How do I read this codebase?

**Framework answer:** Start with `README.md` for orientation, then
`STATUS.md` for the verified-results scoreboard, `FINDINGS.md` for
honest commentary on what's been earned vs. what remains open, and
`CONCLUSIONS.md` for an external-reader summary. The Lean modules
are catalogued in `DEPS.md`. The publication-target writeup is in
`PAPER_DRAFT.md`. For the v2 architectural correction specifically,
see `ORIGINAL_PROMPT.md`, `SEAMS.md`, and `V2_AUDIT.md`. For the
entropy / coarse-graining addendum, see
`ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md`.
