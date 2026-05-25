# Tier 3 Attempt — Cosmological Constant

A structured exploration of whether the framework can derive (or
re-frame) the cosmological-constant problem. As with `TIER2_ATTEMPT.md`,
this is honest documentation of where the analysis lands.

## The target

The cosmological constant Λ is observed to be ~10⁻¹²² in Planck units
(equivalent dark-energy density ~10⁻⁹ J/m³). The standard QFT
calculation (sum of zero-point energies of all field modes) yields
~10⁻³⁵ kg/m³ if cut off at the Planck scale — a factor of ~10¹²⁰ too
large. This is "the worst prediction in physics" or "the
cosmological-constant problem."

Proposed framework angle: read the discrepancy as a category error
about what "vacuum energy" is.

## The framework's candidate move

**Sketch.** Standard QFT treats the vacuum as a substantial entity
with its own energy density (the sum of mode zero-points). The
framework's Axiom III ("reality is the structure of meetings between
wants") rejects substantial vacuum-as-thing. The "vacuum" in the
framework is the *absence* of meetings — a region where no
clearings occur.

Under this reading, summing zero-point energies over all field modes
is counting *potential* meetings (each mode could clear in some
configuration), not *actual* meetings (only those that do clear). The
observed Λ is the relational measure of actual meetings; the QFT
calculation is the (much larger) measure of potential meetings.

The ratio ~10¹²⁰ then becomes a measure of how sparse actual meetings
are relative to the potential meeting space.

## Why this isn't a derivation

### Step 1: formalize "actual" vs "potential" meetings

In our Lean codebase, `Reality W := Meeting W → Prop` is a predicate
on meetings — picking out the *actual* ones. A "potential meeting" is
any element of `Meeting W`. The set `{ m : Meeting W | reality m }` is
strictly smaller than `Meeting W` in general.

This much is formalizable. But to compute Λ we'd need:

  - A measure on `Meeting W` (how to weight each potential meeting)
  - A natural projection from "all potential meetings" to "actual ones"
  - A way to compute the energy contribution of each meeting

None of these is in our framework. They'd require:

  - A field-theoretic dynamics on perspectival transformations (we
    have group structure but no Lagrangian)
  - A spacetime structure (Wantables are pre-spatial in our
    formulation)
  - A coupling to gravity (we have no gravity at all)

### Step 2: connect to the QFT calculation

Even given the formalization above, recovering the *quantitative*
QFT calculation (zero-point sum = 10¹²⁰ × observed) requires:

  - Identifying perspectival modes with QFT modes
  - Showing the integration measure is the same
  - Showing the framework's relational measure differs by the right
    factor

These are major formalization tasks, none of which is currently
attempted.

### Step 3: explain why the relational measure is the *observed* Λ

The harder question. Why ~10⁻¹²² and not 0 or 10⁻¹⁰⁰? This requires
a quantitative theory of which potential meetings become actual ones,
which depends on cosmological dynamics not in our framework.

## Possible alternative angles

### Anthropic / observation-selection

The observed Λ is bounded above by the requirement that galaxies form
(Weinberg 1987 bound). This is a *selection effect*, not a derivation.
The framework's perspective-centric view is compatible with anthropic
reasoning (perspectives only exist in regions where they can; Λ that
prevents perspectives prevents Λ-observers).

But this is not a *derivation* — it's an explanation of why we don't
see WORSE values. Doesn't derive the specific value 10⁻¹²².

### Modified gravity

If gravity is itself a derived/emergent phenomenon (Verlinde-style
entropic gravity), then Λ might be naturally small. The framework's
relational ontology is consonant with such approaches but doesn't
specify one. Untracked open territory.

### Holographic bound

The cosmic horizon entropy bound (Bekenstein-Hawking applied to the
cosmological horizon) gives a relation between Λ and horizon area
that "explains" why Λ is small without deriving the exact value.
Compatible with the framework's relational picture; not derived from
I–IV.

**Per `ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md`**: the framework reads
S = A/4 as the dimensionality of distinguishable-from-outside
structure under the outside-observer's coarse-graining (not as
horizon-substance storing information-stuff). The holographic bound
is a structural relation among coarse-grainings, not a substantialist
"information storage on horizon" claim. This is the same anti-
substantialist hygiene the framework applies to QM and to entropy
generally. See `TIER4_DISSOLUTIONS.md` item #20.

## Honest verdict

The framework provides a *reading* of the cosmological-constant
problem — "the QFT calculation counts potential meetings; the
observed value reflects actual ones; the discrepancy reflects this
ratio." This is conceptually appealing.

But it is **not a derivation**. Producing a quantitative prediction
requires field-theoretic dynamics, a spacetime structure, and a
gravity coupling — none of which are in the framework.

**Verdict: speculative re-framing, not derivation.** This is the
honest status. Future work would need to attach a Lagrangian-level
specification or a holographic-bound argument to the framework's
relational ontology to produce a real quantitative prediction.

## What would close this gap

1. **A spacetime construction from Wantable.** Show that a continuum
   spacetime structure emerges from the framework's transformation
   group (e.g., via the Lie-algebra of an extension of `PTrans W`).
2. **A coupling to gravity.** Argue (or postulate) how Wantable-meeting
   density translates to a stress-energy tensor.
3. **A holographic-bound derivation.** Show that the framework's
   relational measure on `Reality W` is bounded by the horizon area
   of the cosmological structure.

Each is multi-year research. None attempted here.
