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
machine-verified `Perspectival.GPT` instances.

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

## Q10. How do I read this codebase?

**Framework answer:** Start with `README.md` for orientation, then
`STATUS.md` for the verified-results scoreboard, `FINDINGS.md` for
honest commentary on what's been earned vs. what remains open, and
`CONCLUSIONS.md` for an external-reader summary. The Lean modules
are catalogued in `DEPS.md`. The publication-target writeup is in
`PAPER_DRAFT.md`.
