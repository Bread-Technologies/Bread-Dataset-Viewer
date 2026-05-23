# Perspectival Physics — Status Catalog

Live, calibrated record of the research program. Every claim falls into
exactly one of:

- **✓ VERIFIED** — Lean 4 type-checks; proof contains no `sorry`.
- **▲ PARTIAL** — Lean 4 type-checks; proof contains `sorry` placeholders.
  The `sorry` location is documented.
- **○ ARGUED** — informal argument in prose, no formal verification.
  Presumed wrong until verified.
- **✗ STUCK** — attempted and failed; failure mode documented.
- **? OPEN** — not attempted; open in the program.

## Axioms (the inputs)

These are inputs, not results. See `Perspectival/Ontology.lean`.

| Axiom | Encoded | Notes |
|------:|---------|-------|
| I — existence = perspective with directedness | `Existent` structure | Minimal: a perspective is its want; no substrate |
| II — wants are intrinsically relational | `Wantable` class with involutive `complement` | Self-complement (fixed points) not yet excluded |
| III — reality is the structure of meetings | `Meeting`, `Reality := Meeting → Prop` | Bare set; no measure, no probability yet |
| IV — particulars are stable patterns | `Pattern` placeholder | "Stable" requires evolution; not yet defined |

## Verified results so far

| Result | Location | Status |
|-------:|----------|--------|
| Complement is an involution | `Ontology.lean :: Wantable` | ✓ axiomatic |
| Meeting.swap is involutive | `Ontology.lean :: Meeting.swap_swap` | ✓ |
| Complementary symmetry of meeting sides | `Ontology.lean :: complementary_symm` | ✓ |
| Perspectival transformations form a monoid (id, comp, assoc, unit laws) | `Transformations.lean :: PTrans` | ✓ |
| invFun uniqueness from toFun | `Transformations.lean :: invFun_unique` | ✓ |
| PTrans extensionality | `Transformations.lean :: ext` | ✓ |
| Action of PTrans on Meeting is functorial | `Transformations.lean :: actMeeting_id, actMeeting_comp` | ✓ |
| Disjoint-union Wantable structure (no cross-system meetings) | `Composition.lean :: instWantableSum, Meeting.sum_no_cross` | ✓ |
| Componentwise PTrans on disjoint unions | `Composition.lean :: PTrans.sumMap` | ✓ |
| Spacelike pair of binary perspectival observables → CHSH tuple | `CHSH.lean :: SpacelikePair, toCHSHTuple` | ✓ |
| **Realist case** (commutative *-algebra) ⇒ CHSH expression ≤ 2 | `CHSH.lean :: bound_realist` | ✓ via Mathlib |
| **Perspectival/Tsirelson case** ⇒ CHSH expression ≤ 2√2 | `CHSH.lean :: bound_perspectival` | ✓ via Mathlib |

## What is NOT YET done — honest open list

| Target | Tier | Status | Bottleneck |
|--------|------|--------|------------|
| Hardy reconstruction in this language | 1 | ? OPEN | Needs GPT (convex state spaces) — Mathlib has the pieces |
| Tsirelson 2√2 from axioms | 1 | ▲ PARTIAL | Bound is verified given the *-ring picture (`bound_perspectival`). DERIVING the *-ring picture from I–IV remains open |
| No-cloning / no-broadcasting | 1 | ? OPEN | Needs operational composition structure |
| Complex Hilbert space (vs real/quaternionic) | 1 | ? OPEN | Renou-style; needs tensor products in GPT |
| Gauge group U(1)×SU(2)×SU(3) | 2 | ? OPEN | Unknown to anyone from any axiomatic framework |
| Three fermion generations | 2 | ? OPEN | Unknown to anyone |
| Specific particle representations | 2 | ? OPEN | Wigner gives the form; specific reps are empirical |
| Mass hierarchies | 2 | ? OPEN | Empirical input in all known approaches |
| Cosmological constant value | 3 | ? OPEN | Open problem; "category error" claim ARGUED only |
| Dark matter multi-sector prediction | 3 | ? OPEN | Sharp prediction; experimental test pending |
| Fine-tuning forcing | 3 | ? OPEN | Argued; not derived |
| QM/GR unification | 3 | ? OPEN | Framework provides setting; no technical fix yet |
| Hard problem dissolution | 4 | ○ ARGUED | Philosophical move; no formal counterpart |

## Honest meta-assessment

**Strength of the framework so far (this codebase):** the encoded ontology
is mathematically thin. It captures involutive complement + meetings +
group actions on meetings. None of that is uniquely "perspectival" —
it's the formal structure of any relational symmetry. **The philosophical
load is not yet doing technical work.** That gap is the actual research
problem and must be confronted head-on.

**What would constitute the framework "earning its keep":**
- A theorem of the form: *axioms I–IV (+ minimal compositional postulates)
  imply some Hardy axiom*, derived non-trivially.
- A toy model where the perspective-wanting vocabulary picks out a
  specific GPT (e.g., qubit) that realist axioms don't.
- A sharp testable prediction not derivable from existing reconstructions.

**Until one of those lands, the program has not yet justified itself
technically.** That is the honest position and the working target.
