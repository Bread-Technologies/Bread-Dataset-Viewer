# Framework Predictions — Calibrated

A catalog of empirical predictions and proposed experimental tests
that flow from the perspective-wanting axioms (when they flow at all),
honest about which are *derived*, which are *suggested*, and which are
*speculative*.

## Calibration legend

  D  Derived  — the framework forces this; not derivable without it.
  C  Consistent — the framework permits it; doesn't force it.
  S  Suggested  — the framework's philosophical content makes it natural.
  X  Speculative — gestured toward but not formalizable here.

## Quantum-foundational predictions

### P1 — Tsirelson saturation, not Bell saturation  [D]

Experiments measuring CHSH correlations between spacelike-separated
spin-1/2 systems will saturate the Tsirelson bound 2√2, not the Bell
bound 2.

**Status.** Verified experimentally for decades; loophole-free
confirmations (Delft 2015, NIST 2015, Vienna 2015) settle the matter.
The framework's specific contribution is *not* the prediction itself
(any QM-respecting framework predicts this) but the *identification*
of the philosophical hinge: commutativity ↔ observer-independent
joint ledger of facts. Rejecting the latter forces the former
(`Perspectival/CHSH.lean :: bound_perspectival`).

### P2 — No-cloning  [D, but framework-agnostic]

No linear cloner exists for distinguishable states. Verified in our
framework (`Perspectival/Distinguish.lean :: no_cloning_of_distinguishable`).

### P3 — Continuous reversible transformations between pure states  [D]

Given the libertarian-agency postulate (connected group of reversible
transformations) and transitivity on pure states, Hardy Axiom 5
holds. Quantum mechanics does; classical theory (with reversibles =
permutations) does not. The framework predicts a Quantum-side outcome.

**Status** (upgraded from [D, conditional] to [D]): the
classical-vs-quantum dichotomy is now MACHINE-VERIFIED at the
TransitiveAgency level. `Perspectival/Dichotomy.lean ::
framework_dichotomy_existential`:
- Classical n ≥ 2: no `PurePreservingTransitiveAgency` exists
  (UNCONDITIONALLY).
- CircleGPT (the rebit-like continuous-symmetry GPT): an unconditional
  `TransitiveAgency` exists.

The framework's bridge to Hardy A5 strong form
(`Continuity.TransitiveAgency.hardy_axiom5`,
`Hardy.axiom5_strong_of_transitive_agency`) lifts this to: classical
GPTs (n ≥ 2) fail strong-form Hardy A5; continuous-symmetry GPTs
(CircleGPT) satisfy it. The prediction is now formally entailed by
the framework's agency hierarchy.

### P4 — N ≤ K (operational dim ≤ state-space dim)  [D]

Any GPT with N perfectly distinguishable states has state-space
dimension at least N (`Perspectival/Distinguish.lean ::
operational_dim_le_state_dim`).

## Cosmological / dark-sector predictions

### P5 — Plural hidden sectors (dark matter is multi-species)  [D-qualitative, S-quantitative]

The framework's `Composition.lean` shows that disjoint-union
Wantables admit no cross-system meetings — independent perspectival
sectors are *structurally* prohibited from non-gravitational
interactions. The framework's natural ontology is therefore a
*multiplicity* of weakly-coupled sectors, not a single dark species.

**Upgraded this session:** `MultiSectorWantable n W` is now a formal
Lean construction (in `Examples.lean`), with worked examples for n=2,3,4
and cardinality-distinctness theorems showing the axioms ADMIT arbitrary
n. Single-species DM is not forced — multi-species is the natural
non-uniqueness default. See `TIER3_DARK_MATTER.md` for the full analysis.

Specifically: if gravity is geometry (acting on all sectors uniformly
by being part of the universal patterning of Axiom IV) but other
forces are sector-internal connections (as Axiom IV suggests for
"forces are connections"), then dark matter should consist of
multiple Wantable sectors, distinguished from baryonic matter by
incompatible complement structures.

**Testable signatures (suggested, not derived).** A multi-sector dark
ontology should produce gravitational signatures distinguishable from
a single-species cold-dark-matter scenario:

  - Modified halo substructure: multiple sectors with different
    self-interaction cross-sections give different small-scale
    structure (vs. cusp/core, vs. missing satellites).
  - Distinct kinematics in galaxy clusters if the sectors have
    different temperatures/dissipation timescales.
  - Possibly different scale-dependence of clustering vs. ΛCDM.

**Honest qualification.** None of these signatures is *derived* from
the framework. The framework's contribution is the qualitative
prediction that the dark sector is *plural*, not the quantitative
shape of the predicted signatures. Sharper predictions would require
either an N-sector model parametrized by composition data (Axiom III
with multiple disjoint Wantables) or a Lagrangian-level
specification — neither present in this codebase.

### P6 — Cosmological-constant value as relational artifact  [X]

The standard QFT calculation (zero-point energy of every field
mode) yields a value 10¹²⁰ too large compared to the observed Λ. The
framework reads this as a *category error*: treating the vacuum as a
substantial thing with its own energy, rather than as the absence of
meetings (Axiom III). In a relational ontology, "vacuum energy" is
not a property of nothing-in-particular; it is a measure of which
meetings occur. The 10¹²⁰ discrepancy arises from summing over modes
that never participate in any meeting.

**Calibration.** This is interpretive philosophy, not derivation.
The framework does *not* give a quantitative prediction for Λ here;
it gestures at the form a quantitative argument might take (count
"actual" rather than "potential" meetings). A real prediction would
require formalizing the relational measure and showing the
calculation goes through. Not done in this codebase.

### P7 — Fine-tuning as coherence-forcing  [X]

The framework's libertarian-agency commitment, formalized as
HasConnectedAgency, requires a richness of the transformation group.
Specific physical constants (fine-structure, weak mixing angle, mass
hierarchies) are claimed to be *forced* by coherence requirements on
this group rather than contingent.

**Calibration.** Suggested, not derived. No path to *quantitative*
forcing has been formalized. The framework provides the conceptual
shape ("forces are connections; representations are matter; coherence
constrains") but the constants emerge from physical Lagrangians we
have not formalized.

## Foundations-of-consciousness predictions

### P8 — No combination problem  [D conceptually]

The hard problem of consciousness, in Chalmers's framing, is the
explanatory gap between physical structure and subjective experience.
The combination problem (Goff and others) is the panpsychist's worry
about how micro-experiences compose into macro-experiences.

The framework dissolves both: matter is how consciousness appears
under perspectivization into structural relations (Axiom I + Quine/
Rovelli parallel). There is *no combination* — there is one
consciousness viewing itself from inside its own transformations.
Apparent combination is structural patterning (Axiom IV).

**Calibration.** This is a philosophical dissolution, not a
derivation. The framework reframes the question rather than answering
the original question on its original terms. The reframing is
defensible (see `LINEAGE.md`; closer to Schopenhauer than Goff) but
is not a *physics* result.

### P9 — Lightning-bolt panexperientialism is partial  [X]

Nagel's "what is it like to be a lightning bolt" question is answered
in pieces: there is *something it is like* to be each electron
transition (micro-perspectives at each event), but no unified
lightning-experience because no integrating structure.

**Calibration.** Whitehead's panexperientialism refined. Not
formalizable in the current Lean codebase. Suggested by Axiom I + IV
(perspective at each occasion; unified experience requires sustained
pattern stability).

## Entropy and Second Law predictions (per addendum)

### P11 — Second Law derivable, not contingent  [D conceptually]

Per `ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md`, the framework predicts
that the Second Law follows necessarily from:
(i) subjectivist coarse-graining (Jaynes);
(ii) physical construction determining distinguishability;
(iii) mechanical impossibility of many-to-one collapse under
conservative dynamics (WBT 2024 Picard-Lindelöf).

**Empirical content:** the kT ln 2 erasure bound (Landauer's principle)
is *mechanically derivable from pure dynamics*, not a statistical-
mechanical postulate. The framework's prediction goes further:
deviations from kT ln 2 (in either direction) at the bit-erasure
scale would be empirical evidence against the framework. Current
nano-scale Landauer experiments are consistent with kT ln 2; the
framework predicts no anomalies.

**Status.** Conceptual derivation in place (per WBT 2024 +
framework Tier A); formal Lean encoding of the mechanical half
(`actualizeAt_many_to_one`, `axiom_II_actualization_irreversible`).
Quantitative experimental tests via increasingly precise nano-scale
Landauer measurements.

### P12 — Past Hypothesis is a category error  [S]

The framework predicts that the standard "Past Hypothesis" debate
(why was the early universe in a low-entropy state?) will be
recognized as a category error in foundations-of-physics work.
"Low entropy" presupposes substantial entropy; the framework's
reframing (low entropy = "from this coarse-graining, past-direction
configurations are fewer," constitutive of past) dissolves the
puzzle rather than answering it.

**Testability.** Not directly testable; this is a meta-prediction
about how the foundations community will eventually re-categorize
the problem.

### P13 — Boltzmann brain reasoning has no purchase  [S]

The framework predicts that Boltzmann brain reasoning — which
relies on substantial high-entropy state-spaces from which fluctuations
occur — has no purchase under the framework's relational ontology.
Cosmological models making Boltzmann brain predictions presuppose
ontology the framework rejects.

**Testability.** Indirect — affects how cosmological multiverse
scenarios get evaluated.

## Methodological predictions

### P10 — Sharper Bell-style inequalities from observer plurality  [S]

Frauchiger–Renner (2018), Bong et al. (2020) — strong no-go results
sharper than Bell for *observer-extended* setups. The framework
predicts that further inequalities of this kind exist whenever the
realist commitment to observer-independent facts is in play.

**Status.** Some such inequalities already exist (Local Friendliness;
Frauchiger–Renner C). The framework's prediction is that the program
of constructing such inequalities continues to yield new results, and
that the *operational hinge* in each case will be (some form of) the
observer-independent-ledger assumption that the framework rejects.

**Testability.** Each new inequality is a candidate experimental
test. Loophole-free Wigner's-friend experiments are technologically
challenging but in principle feasible.

## Summary

| ID | Prediction | Status |
|----|-----------|--------|
| P1 | Tsirelson, not Bell, saturation | D (verified) |
| P2 | No-cloning | D (framework-agnostic) |
| P3 | Continuous reversibles between pure states | D, conditional |
| P4 | N ≤ K | D |
| P5 | Dark matter is multi-species | S (qualitative only) |
| P6 | Λ as category error | X |
| P7 | Fine-tuning forced by coherence | X |
| P8 | Hard-problem dissolution | D conceptually |
| P9 | Partial panexperientialism | X |
| P10 | Sharper Bell-style inequalities | S |
| P11 | Second Law derivable, not contingent | D conceptually |
| P12 | Past Hypothesis as category error | S |
| P13 | Boltzmann brain reasoning has no purchase | S |

The strongest claims are D (P1–P4); they are also the most quantum-
foundational and the least *philosophically distinctive*. The most
distinctive claims (P5, P7, P9) are S/X — suggestive, not derived.

This is the calibration the framework currently has to live with.
The work of moving items right-to-left (D ← C ← S ← X) is the
ongoing research program.
