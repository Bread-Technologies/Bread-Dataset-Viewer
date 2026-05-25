# Tier A / Tier B Seams — Framework's Empirical Signatures

Per ORIGINAL_PROMPT v2 §2 and first move #9, the framework's
distinctive empirical content lives at the SEAMS — places where
Tier A (irreversible meeting-structure) leaks through Tier B
(reversible-limit) descriptions. This doc catalogues them and the
mathematical / experimental form they take.

## What a "seam" is

Within a bracketed interval (between actualization events), Tier B
applies and dynamics are reversible. AT an actualization event,
Tier A asserts itself: a potential meeting becomes actualized, the
many-to-one collapse occurs, and reversibility is lost. The
*observable consequence* of this loss — what an experimenter sees
that distinguishes the framework from purely-Tier-B descriptions — is
a seam signature.

The mathematical encoding is in `Perspectival/TierB.lean`:

- `BracketedTransition R₁ R₂` characterises Tier B intervals
  (reversible, equivalence-relation).
- `AtSeam R₁ R₂` characterises actualization events (not bracketed,
  not reversible).
- `seam_breaks_bracketing` is the structural theorem: at the seam,
  Tier B's reversibility fails.

## Seam 1 — Measurement / collapse in QM

**Tier B description:** unitary evolution on Hilbert space.
**Tier A content:** the "click" of a detector is an actualization
event — a potential meeting between the system and the apparatus
clears, irreversibly.

In standard QM, measurement is a separate postulate (collapse rule)
added on top of unitary evolution. The framework dissolves this: the
collapse postulate IS the actualization event re-entering the Tier B
description. The two-tier architecture eliminates the measurement
problem by construction.

**Empirical signature:** the discreteness of measurement outcomes,
the non-reversibility of completed measurements, the apparent
"jump" from superposition to eigenstate. All Tier A content visible
in the Tier B picture.

**Formal correlate (in Lean):** `AtSeam` predicate; `actualize`
operation as the structural transition.

## Seam 2 — Vertex preservation (the R6 patch is now a derived theorem)

**Tier B description:** state space of a GPT, with pure states (=
extreme points / vertices in classical) playing a privileged role
in operational reconstruction.

**Tier A content:** pure potential states correspond to definite-but-
not-yet-actualized meeting configurations. Under bracketed (reversible)
dynamics, these definite configurations cannot smear out — that would
violate the structural commitment that the actualized-set is
preserved.

In v1 of this program, vertex preservation appeared as a "patch" to
the R6 disconnect theorem (without it, the naive R6 argument fails
for n ≥ 3 — see `Classical.lean` SUMMARY block). Under v2, vertex
preservation is *not a patch*; it is a derived theorem at Tier B
expressing the constraint that bracketed dynamics preserve pure
potential states.

This is the cleanest example of a v2-progressive patch: what looked
like an ad-hoc addition under v1 is, under the two-tier architecture,
a derived consequence of the bracketing operation. The progressive
character is exactly what the v2 prompt's methodology section §10
asks for.

**Empirical signature:** classical reversible dynamics on N ≥ 2
points are discrete (no continuous symmetry), but classical
*irreversible* dynamics (with actualization) admit continuous
relaxations. The discontinuity is the seam.

**Formal correlate:** `Classical.classical_general_no_pure_preserving_transitive_agency`
in `Classical.lean`; framework_dichotomy_existential in `Dichotomy.lean`.

## Seam 3 — Erasure events (Witkowski-Brown-Truong Lyapunov instability)

**Tier B description:** computational dynamics on a phase space,
modeled as reversible Hamiltonian flow.

**Tier A content:** when a many-to-one operation is forced (e.g.,
erasing a bit, mapping two distinct states to one canonical state),
the actualization is irreducibly nonconservative. The user's 2024
paper proves this via Picard-Lindelöf applied to time-reversal-
symmetric ODEs: approaching the reset point yields Lyapunov
instability.

**Empirical signature:** the kT ln 2 erasure bound (Landauer's
principle) is derivable from pure mechanics, not statistical
mechanics. Approaching reset under near-conservative dynamics shows
divergent sensitivity to initial conditions at the reset point — a
DIRECTLY OBSERVABLE Tier A signature.

**Formal correlate:** `TierA.axiom_II_actualization_irreversible`
proves the structural shadow (ActualizationMap is not reversible).
The dynamical content is in Witkowski-Brown-Truong 2024.

**This is the user's published paper. It is the framework's mechanical
foundation for Axiom II.** Cite it directly in any Tier 1 writeup.

## Seam 4 — Decoherence

**Tier B description:** entanglement with environment causes
exponential suppression of off-diagonal density matrix elements over
some decoherence timescale.

**Tier A content:** every entanglement event is a partial actualization
— a meeting between the system's wants and the environment's
complementary wants begins to clear. Decoherence is the accumulated
effect of many small actualizations.

**Empirical signature:** decoherence rates depend on the
"actualization density" of the environment, not just statistical
properties. The framework predicts environments rich in Tier A
content (lots of irreversible interactions) decohere systems faster
than statistical models predict. **Testable in principle.**

**Formal correlate:** not yet formalized in Lean. A future module
`Decoherence.lean` would encode this.

## Seam 5 — Cosmological constant (Tier 3)

**Tier B description:** quantum field theory vacuum energy summing to
~10¹²⁰ × observed Λ.

**Tier A content:** vacuum is not a substantial "thing" with energy;
it is the structural absence of actualized meetings. Counting
"potential meetings" as substantial-energy carriers is a category
error.

**Empirical signature:** the observed Λ ≈ 10⁻¹²² in natural units is
the relational-measure remainder when the actualized-meeting
structure is properly counted. The framework predicts Λ is *not* a
mystery requiring fine-tuning; it is the natural Tier A magnitude.

**Formal correlate:** not yet formalized. Tier 3 target.

## Seam 6 — Dark matter (Tier 3)

**Tier B description:** dark matter is a single hidden species with
unknown coupling.

**Tier A content:** disjoint perspectival sectors (different families
of Wantables with no cross-system meetings — see `Composition.lean`)
cannot interact except via gravity (the only universal coupling).
The framework predicts plural hidden sectors.

**Empirical signature:** halo structure shows multi-component
gravitational signatures distinct from single-species CDM. The
framework's prediction is *qualitatively different* from standard
dark matter models.

**Formal correlate:** `MultiSectorWantable` in `Examples.lean`.

## Seam catalogue summary

| Seam | Tier B description | Tier A content | Empirical signature |
|------|--------------------|----------------|---------------------|
| 1. Measurement | Unitary evolution | Actualization event | Discrete outcomes, non-reversal |
| 2. Vertex preservation | GPT state space + extreme points | Bracketed dynamics preserve definite potential states | Classical/quantum discreteness boundary |
| 3. Erasure | Reversible Hamiltonian flow | Many-to-one collapse | Landauer kT ln 2 + Lyapunov instability at reset |
| 4. Decoherence | Off-diagonal suppression | Accumulated partial actualization | Decoherence rate depends on environment Tier A density |
| 5. Cosmological constant | QFT vacuum energy | Vacuum = structural absence of actualization | Observed Λ as natural Tier A magnitude |
| 6. Dark matter | Single hidden species | Multi-sector perspectival families | Multi-component halo signatures |

## Status of each seam

- Seam 1 (Measurement): structurally encoded in `TierB.lean`.
  Formal "measurement = actualization" theorem documented; no
  separate axiom required. ✓ DERIVED.
- Seam 2 (Vertex preservation): formally proved as Tier B theorem
  via L6 closure. Vertex-preservation as derived rather than
  postulated is the v2-progressive reframing. ✓ DERIVED.
- Seam 3 (Erasure): structural shadow in
  `axiom_II_actualization_irreversible`; dynamical content cited
  to Witkowski-Brown-Truong 2024. ✓ STRUCTURAL.
- Seam 4 (Decoherence): not yet formalized. ○ OPEN.
- Seam 5 (Cosmological constant): philosophical sketch only.
  ○ OPEN, Tier 3.
- Seam 6 (Dark matter): structural Lean encoding via
  `MultiSectorWantable`; quantitative predictions open. ○ PARTIAL.

The framework's program advances by closing more seams. Each seam,
when closed in Lean, becomes a framework-distinctive prediction —
something the bare Tier B operational reconstructions cannot deliver.
