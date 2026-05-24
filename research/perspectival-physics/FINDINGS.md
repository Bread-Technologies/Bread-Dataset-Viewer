# Findings — Honest Research Log

A running, calibrated record of what we've actually established, what
remains argued-but-unproven, and what's stuck. Read alongside
`STATUS.md` for the per-file breakdown.

## Real findings (verified, non-trivial)

### F1. Tsirelson bound is the framework's natural prediction (verified)

`Perspectival/CHSH.lean :: bound_perspectival` machine-verifies, via
Mathlib's `tsirelson_inequality`, that for a spacelike pair of binary
perspectival observables in a (general, possibly noncommutative)
ordered *-algebra over ℝ:

  A₀·B₀ + A₀·B₁ + A₁·B₀ − A₁·B₁  ≤  √2³ · 1

The companion `bound_realist` shows that if the algebra is required
to be **commutative** — equivalently, if there is an observer-
independent joint ledger for the four observables — the bound drops
to 2 (Bell's bound). Because the framework rejects the joint-ledger
assumption (Frauchiger–Renner C-drop), it lands on Tsirelson.

**Honest qualification.** This is a re-interpretation, not a
derivation of QM. The *-algebra structure is imported, not derived
from I–IV. What is genuinely earned: identifying *which* algebraic
hypothesis is the philosophical hinge (commutativity ↔ observer-
independent ledger), and machine-verifying that giving it up yields
exactly Tsirelson.

### F2. No-cross-system meetings as structural no-signaling (verified)

`Perspectival/Composition.lean :: Meeting.sum_no_cross` proves that in
the disjoint-union Wantable `W₁ ⊕ W₂`, every meeting has both sides
in the same summand. Two independent perspectival domains cannot,
by the structural fact of complement acting component-wise, produce
cross-system meeting events. This is a structural (not measure-
theoretic) form of the no-signaling principle.

### F3. No-cloning theorem (linear-algebra form) — fully proven

`Perspectival/NoCloning.lean :: no_cloning` formally proves: given a
set `S` closed under sums, two elements `v₁, v₂ ∈ S` (with `v₁+v₂ ∈ S`),
a linear cloner `C : V →ₗ[ℝ] V ⊗ V` with `C v = v ⊗ v` on `S`, and a
bilinear form `B` with `B v₁ v₂ + B v₂ v₁ ≠ 0`, contradiction.

The structural lemma `cross_terms_vanish` is the heart of the proof:
linearity forces `v₁ ⊗ v₂ + v₂ ⊗ v₁ = 0`. The bilinear form `B`
witnesses that this is impossible. The hypothesis "there exists a
bilinear form distinguishing the pair" is weaker (and cleaner to
verify) than "v₁, v₂ are linearly independent," but is implied by it.

Framework reading: a *want* cannot be duplicated into two isolated
copies. Linearity is the structural shadow of Axiom II's
two-sidedness. The theorem itself is independent of the philosophy;
the philosophy provides the reading.

### F4. Libertarian agency ⇒ continuous reversible state paths (verified)

`Perspectival/Continuity.lean :: continuous_path_of_reachable`
formally proves: given the framework's libertarian-agency postulate
(formalized as `HasConnectedAgency` — the set of reversible
transformations is path-connected and contains identity), any two
states reachable by the available transformations are connected by a
continuous path in `V`.

This is the formal *easy direction* of the framework's distinctive
claim that "libertarian agency at every instant ⇒ Hardy Axiom 5
(continuity of reversible transformations between pure states)."

**Honest framing of what is still missing:**

  1. Whether "libertarian agency" really forces *path-connectedness*
     rather than mere richness is the philosophical-to-formal step
     this file does NOT settle.
  2. Transitivity of the group action on pure states is left as a
     separable hypothesis; full Hardy Axiom 5 would require it.
  3. Restriction to PURE states (extreme points) is bookkeeping left
     for follow-up.

What this DOES show: the easy half of the framework's most distinctive
contribution is real, machine-verified mathematics. The hard half —
deriving connected-group structure from agency — is well-posed and is
the next research target.

### F5. Classical GPT instance — fully constructed (verified)

`Perspectival/Classical.lean :: gpt` provides a complete instance of
the GPT structure for the n-outcome classical theory. Verifies
convexity of the standard simplex (states), convexity of the unit
hypercube (effects, as inner-product functionals), normalization, and
[0,1]-valued probabilities. The first concrete example showing the
GPT framework is non-vacuous.

### F6. Axiom 1 (Hardy) is DERIVABLE (verified)

`Perspectival/Hardy.lean :: axiom1_holds` formally proves that every
`GPT` instance satisfies Hardy's probability axiom. Trivially so by
construction, but it's worth recording: the formal type-checker
confirms the "DERIVABLE" categorization.

## Argued findings (prose-level only — presumed wrong until verified)

### A1. Hardy Axioms 3 and 5 are DERIVABLE in principle

Argued in `Hardy.lean`. The framework's pattern-stability (Axiom IV)
plausibly supports subspace closure. The libertarian-agency commitment
plausibly favors continuous reversible transformations between pure
states. **Neither is formally proven.** Formal derivation is the next
substantive task.

### A2. Hardy Axioms 2 and 4 are AUXILIARY

Argued: K-minimality (Axiom 2) is a selection principle across
theories, not entailed by I–IV. Tensor composition (Axiom 4) requires
more than the disjoint-union structure we have built.

### A3. The Quine/Rovelli parallel

Ontological relativity at the semantic level (Quine) prefigures
relational QM at the physical level (Rovelli). The framework unifies
both by making perspective-with-directedness the fundamental thing.
This is interpretive, not derivational; documented in `LINEAGE.md`.

## Stuck / open

### O1. Deriving the *-algebra structure from I–IV

The deepest open question of Tier 1. We can re-state Tsirelson in our
vocabulary, but we have not shown that the framework's axioms *force*
the *-algebra picture. The classical route (orthomodular lattice →
projection lattice → von Neumann algebra) is well-trodden but **not
yet formalized in Lean** (Mathlib has neither orthomodular lattices
nor Solèr's theorem).

### O2. Deriving complex (vs. real or quaternionic) Hilbert space

Renou et al. 2021 experimentally ruled out real QM; Hardy's
reconstruction with composite-system reasoning forces complex. We
have the Hardy axioms stated; the formal derivation that the choice
of field is forced has not been attempted here.

### O3. Hardy's K = N² (the actual reconstruction theorem)

Stating the axioms ≠ proving the theorem. Hardy's proof of K = N²
from axioms 1–5 is non-trivial and is not yet in Mathlib. This is
multi-week work even with full focus and would be a publishable
formalization contribution on its own.

### O4. Tier 2 targets (gauge groups, generations) — open in any framework

The gauge group U(1)×SU(2)×SU(3) and three fermion generations are
not known to be derivable from any axiomatic system by anyone. The
framework offers no obvious additional purchase. To be explicit:
**we have not made progress here, and there is no published path
that would let an AI session make progress here without
fundamentally new mathematics.**

### O5. Tier 3/4 — dissolution claims

The "hard problem dissolution" and "category-error reading of the
cosmological constant" are philosophical moves, not mathematical
ones. They live in `LINEAGE.md` (and a future paper), not the Lean
codebase.

## Meta-assessment

**What the framework has earned, technically.** A Lean-verified
re-statement of CHSH/Tsirelson in perspective-wanting vocabulary,
with the philosophical hinge identified as commutativity ↔
observer-independent ledger. A typed ontology that's internally
coherent. A scaffold for Hardy-style reconstruction.

**What the framework has NOT earned.** Any technical result that
realist axioms can't already deliver. The CHSH/Tsirelson bound,
no-signaling-as-structural, and Hardy Axiom 1 are framework-agnostic
in the sense that they follow from the underlying mathematics; the
perspective-wanting language is providing interpretation, not proof
power.

**What it would take to change this.** A theorem of the form: *I–IV
(plus minimal additions X, Y) imply some Hardy axiom that cannot be
motivated as cleanly from realist axioms*. The most plausible target
is Axiom 5 (continuity of reversible transformations) via the
libertarian-agency commitment to genuine choice at each instant. A
formal version: showing that the framework requires the set of
reversible transformations to be a connected Lie group rather than
a discrete group. **This is not yet attempted; it is the next bet
worth making.**

## Disposition

The honest summary, calibrated: the framework is internally coherent
and gives a Lean-verifiable home to standard reconstruction-program
results. It has not yet demonstrated unique technical purchase
beyond philosophical re-reading. The most promising open angle is
Axiom 5 (continuity) from libertarian agency; the gauge-structure and
generations questions remain open for everyone and likely for this
session too.

That is the honest state. Updating as work progresses.
