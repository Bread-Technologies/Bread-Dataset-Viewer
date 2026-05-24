# Tier 3 #11 — Dark Matter as Multi-Sector Prediction

A focused research note on whether the perspectival-reconstruction
framework can deliver the Tier 3 target #11 from `ORIGINAL_PROMPT.md`:
*"Dark matter. Sharp framework prediction: plural hidden sectors, not
single species. Derive quantitative gravitational signatures
distinguishing multi-sector from single-species."*

This note is narrower in scope than `TIER3_ATTEMPT.md` (cosmological
constant) and is meant to deliver a single honest verdict on #11.

## 1. The target, restated precisely

The standard ΛCDM model posits a single cold-dark-matter species: one
particle (or one near-degenerate family), gravitationally interacting
only, with a Maxwell-Boltzmann phase-space distribution at decoupling.
This is enormously successful at large scales (CMB acoustic peaks,
linear-regime structure) and increasingly strained at small scales
(missing satellites, too-big-to-fail, cusp/core, diversity-of-rotation-
curves).

The framework's Tier 3 claim is *not* that ΛCDM is wrong on large
scales — it is that the dark sector should generically be **plural**:
multiple Wantable sectors, each weakly coupled to the others (and to
the baryonic sector) except through gravity. The question this note
addresses: does the framework actually *force* this, and does it force
any *quantitative* signature distinguishing N-sector from 1-sector
dark matter?

## 2. Logical chain from Axioms I–IV

Following the ontology in `Perspectival/Ontology.lean` and the
composition lemmas in `Perspectival/Composition.lean`:

**Step (a) — Axiom IV says matter is representation, force is
connection.** A "species" of matter, in this framework, is not a
substance but a stable pattern under some transformation group acting
on a Wantable `W`. Distinct representations of distinct groups give
distinct species.

**Step (b) — Axiom II says wants are intrinsically relational; every
want has a complement.** The complement structure is *internal* to a
given `Wantable W`. Two distinct Wantables `W₁`, `W₂` have *distinct*
complement structures: `Wantable.complement : W₁ → W₁` does not
mention `W₂` at all.

**Step (c) — `Meeting.sum_no_cross` (formally proved).** In the
disjoint union `W₁ ⊕ W₂`, *no meeting has cross-component sides*. Both
sides of any meeting live in the same summand. This is a theorem, not
a postulate; it follows mechanically from the component-wise
complement on the sum.

**Step (d) — There is no privileged unification axiom.** Nothing in
I–IV forces the universe's total Wantable to be a single irreducible
piece. The framework is *agnostic* about how many disjoint sectors
exist; what it is *not* agnostic about is that disjoint sectors do not
interact via meetings (Axiom III + step c).

**Step (e) — Gravity, if it is "the universal patterning of
spacetime" rather than a sector-internal connection, is the one
mechanism that does not respect the disjoint-union firewall.** This
step is the load-bearing one and is *not formalized* in the framework
(see §6 honesty catalog). The intuition is that gravity in Axiom IV is
on the "background structure of meeting-events" side rather than on
the "internal force = connection on a particular representation" side.

**Conclusion the framework supports:** the universe's Wantable is
generically a disjoint union of multiple sectors `W_baryon ⊕ W_dark₁ ⊕
W_dark₂ ⊕ …`, each internally rich but pairwise non-meeting, all
coupled only via the universal patterning (gravity). *Single-species
dark matter is a special case requiring an extra "minimality" postulate
the framework does not contain.*

This is the precise sense in which the framework predicts plural
hidden sectors: not by *forbidding* a single sector, but by
*declining to privilege* it.

## 3. Cross-reference to existing astrophysics

This is not a new prediction *as physics*. Multi-sector dark matter is
a well-developed line:

- **Hidden valleys** (Strassler & Zurek 2007): multiple gauge groups
  in hidden sectors, weakly coupled to the SM.
- **Mirror matter** (Foot, Volkas, and earlier Lee & Yang 1956): a
  parity-doubled dark sector with its own electromagnetism and atomic
  physics.
- **Twin Higgs / mirror Higgs** (Chacko, Goh, Harnik 2006): naturalness-
  motivated dark sector with mirror SU(2)×U(1).
- **Atomic / dissipative dark matter** (Kaplan, Krnjaic, Rehermann,
  Wells 2010; Foot 2014): dark matter with internal "dark photon" and
  ability to cool.
- **Dynamical dark matter** (Dienes & Thomas 2011): an ensemble of
  components with a distribution of masses and lifetimes.
- **Schmaltz et al.** various models with dark Higgs sectors.

The framework's contribution is *not* novel astrophysics. It is a
*motivational* argument: from a foundational-ontology standpoint, the
*default expectation* should be N ≥ 2 hidden sectors. Single-species
dark matter requires positing an additional uniqueness condition
nothing in I–IV provides.

## 4. Quantitative signatures — what does the framework actually
   predict?

Honestly: the framework predicts **N ≥ 2** sectors with shared gravity
and otherwise disjoint complement structures, and that is essentially
all. It does not fix:

- The number of sectors.
- Their relative mass densities (`Ω_i`).
- Their internal couplings (whether sector *i* has a dark photon, a
  dark colour force, a dark Higgs, etc.).
- Their temperatures or dissipation timescales.
- Their kinetic mixing with the SM.

Therefore the *generic* signatures the framework is consistent with —
and which would *distinguish* multi-sector from single-species — are
those already catalogued in the multi-sector DM literature. We list
them with attribution rather than claiming them as framework
derivations:

**(i) Multi-component halo profiles.** If two dark sectors have
different self-interaction cross-sections (one collisionless, one
mildly dissipative), the resulting halo is a superposition of an NFW-
like outer profile and a cored inner component. Diversity of
rotation-curve shapes across galaxies of similar mass (Oman et al.
2015) is a possible signature. *Source:* atomic/dissipative DM
literature, not framework-derived.

**(ii) Multiple-population kinematics in clusters.** A multi-sector
dark cluster, after a merger like Bullet, would show *several*
offset peaks in lensing reconstruction rather than the single offset
seen so far. Current data are consistent with single offset but
allow O(10%) sub-components. *Source:* generic multi-component
expectation.

**(iii) Substructure beyond ΛCDM.** Each dark sector can fragment
independently, producing subhalo mass functions that *sum* rather
than match the single-CDM prediction. Strong-lensing flux-ratio
anomalies (Vegetti et al., Hsueh et al.) and stellar-stream
perturbations (GD-1, Pal 5) constrain total subhalo abundance; an
excess over single-CDM expectation, if found, would *favour* multi-
sector but cannot uniquely select it (warm DM and self-interacting
DM also modify substructure).

**(iv) Multiple matter-power-spectrum kinks.** If sector *i*
decoupled at temperature *T_i* and has free-streaming length λ_i,
the linear matter power spectrum has a suppression scale per sector.
Multi-sector DM predicts *multiple* small-scale cutoffs rather than
one. Lyman-α forest, 21-cm tomography (HERA, SKA) and high-redshift
luminosity functions (JWST) are the relevant probes.

**(v) Non-thermal gravitational-wave backgrounds.** Internal phase
transitions in dark sectors at temperatures `T_i` produce stochastic
GW backgrounds peaked at frequencies set by `T_i / H(T_i)`. Multiple
sectors give multi-peak GW spectra. LISA and pulsar-timing arrays
(NANOGrav, EPTA) are sensitive in different bands.

**None of (i)–(v) is forced by the framework.** All five are
predictions of *some* multi-sector dark-matter model in the
literature. The framework's contribution is that the *prior* for
multi-sector models should be *higher* than for single-species, given
that nothing in I–IV picks out N = 1.

## 5. Proposed experimental tests

A constructive experimental program (none of which the framework can
take credit for inventing, but all of which it motivates):

- **Direct-detection target diversification.** Single-target
  experiments (xenon, argon) optimize for *one* WIMP mass window.
  Multi-target campaigns (xenon + silicon + germanium + helium) are
  better at distinguishing multiple species. Argument for funding
  diversity, not consolidation.
- **Cluster-merger lensing surveys.** Higher-resolution weak-lensing
  reconstructions of merging clusters (Euclid, LSST/Rubin) to search
  for multi-peak dark distributions.
- **Subhalo abundance from stellar streams.** Roman, Rubin to detect
  density gaps in cold streams; compare to ΛCDM predictions.
- **JWST high-z luminosity functions** as multi-cutoff probes.
- **Multi-band stochastic GW searches** (LISA + PTA + LIGO/Virgo/KAGRA
  + ET) for multi-peak structure.

## 6. Honest catalog: framework-distinctive vs framework-agnostic

| Claim | Framework-distinctive? | Status |
|-------|------------------------|--------|
| Dark sector is plural by default | Partially (declines uniqueness) | Suggested |
| Disjoint sectors do not interact non-gravitationally | Yes (formally proved as `Meeting.sum_no_cross`) | Derived |
| Gravity couples sectors universally | No (assumed, not derived) | Speculative |
| Specific signatures (i)–(v) | No | Pre-existing literature |
| Number of sectors, mass spectrum, couplings | No | Not predicted |

**What the framework genuinely contributes.** A *prior shift*: the
ontology makes single-species dark matter look like an *unmotivated
restriction* of the natural multi-sector default. This matters for
experimental program design (favouring diversification) and for
Bayesian model comparison (lower prior weight on minimal-DM
extensions of the SM).

**What the framework does not contribute.** Any quantitative shape,
mass scale, or signature distinguishing multi-sector from
single-species. The Tier 3 brief asks for "quantitative gravitational
signatures." The framework as currently formalized does not deliver
them. It delivers *motivation* for the qualitative prediction.

**Comparison to existing multi-sector proposals.** Mirror-matter,
hidden-valley, atomic-DM, and dynamical-DM proposals all *posit*
specific multi-sector structures and derive specific signatures. The
framework neither subsumes nor reproduces those calculations; it
provides a foundational *reason* the proposals are *generic* rather
than baroque.

## 7. One concrete next step toward Lean-formalizable claim

The smallest formal step that would convert §2 from "suggested" to
"derived (qualitative)" is a `MultiSectorWantable` structure capturing
the gravity-couples-all-but-no-cross-meetings configuration. Sketch:

```
structure MultiSectorWantable where
  sectors : ℕ → Type u
  [wantable : ∀ i, Wantable (sectors i)]
  -- The total Wantable is the dependent sum (Σ i, sectors i).
  -- A "gravitational coupling" is a predicate `GravCouples` that
  -- holds for any pair of meetings across sectors, despite no
  -- Meeting (Σ i, sectors i) having cross-sector sides.
```

Then prove:

1. **No cross-sector meetings** — generalize `Meeting.sum_no_cross` to
   dependent sums.
2. **Gravity-coupling well-definedness** — define `GravCouples` as an
   external relation on meeting-pairs, not as a Meeting in the total
   Wantable.
3. **Uniqueness-of-sectors is an extra postulate** — formalize a
   `SingleSector` predicate on `MultiSectorWantable` and show it is
   *not* implied by I–IV (i.e., the multi-sector models are non-
   empty).

This last item — the formal non-implication — is the load-bearing
honesty claim of #11. If we can prove "the axioms admit multi-sector
models" in Lean, we have *earned* the prior-shift argument. If the
axioms turn out to *force* single-sector somehow, that is also a
result and should be documented (per §7 of `ORIGINAL_PROMPT.md`).

This is one focused Lean session of work. It would not produce
quantitative astrophysical signatures, but it would convert P5 in
`PREDICTIONS.md` from **S (qualitative only)** to **D (qualitative,
formally derived as non-uniqueness)** — a real but bounded upgrade.

## Verdict

The framework delivers the *motivation* for multi-sector dark matter
honestly and (with the §7 next step) formally. It does **not** deliver
the quantitative signatures Tier 3 #11 asks for. Calibration: P5
remains **S** until the `MultiSectorWantable` formalization is done,
at which point it can move to **D (qualitative)**. The quantitative-
signatures half of #11 is **not achievable** with the framework as
currently constituted; it requires astrophysical model-building the
axioms do not constrain.

This is the honest verdict per §7–8 discipline.
