# Perspectival Physics

A foundations-of-physics research program that attempts to derive
operational quantum theory — and ideally substantial portions of the
Standard Model — from agent-centric axioms about perspective, wanting,
and meeting.

This directory lives inside the Bread-Dataset-Viewer repo as the only
available durable storage for the work. The research is unrelated to
the dataset viewer; it is parked here because it is the authorized
push target.

## Layout

**Lean code** (`Perspectival/`):
- `Ontology.lean` — axioms I–IV encoded as Lean 4 types.
- `Transformations.lean` — PTrans as a Group, MulAction on meetings.
- `Composition.lean` — disjoint-union, no-cross-system meetings.
- `CHSH.lean` — Tsirelson 2√2 via Mathlib's CHSH module.
- `GPT.lean` — generalized probabilistic theory data + Monoid on
  self-Transforms.
- `Hardy.lean` — Hardy's 5 axioms as predicates (3/5 derivable).
- `NoCloning.lean` — linear-algebra no-cloning theorem.
- `NoBroadcasting.lean` — classical broadcaster (quantum case open).
- `Classical.lean` — concrete n-outcome classical GPT instance.
- `Continuity.lean` — libertarian agency → Hardy Axiom 5.
- `Distinguish.lean` — distinguishability ↔ linear independence.
- `WantableGPT.lean` — bridge: Wantable → GPT, with injective MonoidHom.
- `Examples.lean` — worked end-to-end demonstrations.

**Documentation**:
- `STATUS.md` — calibrated per-theorem catalog. **Read first.**
- `FINDINGS.md` — honest commentary, limitations, open targets.
- `CONCLUSIONS.md` — external-reader summary.
- `FAQ.md` — concrete physics questions answered.
- `GLOSSARY.md` — terminology with Lean cross-references.
- `DEPS.md` — module dependency map.
- `PREDICTIONS.md` — empirical claims with calibration.
- `LINEAGE.md` — philosophical references.
- `PAPER_DRAFT.md` — publication-target writeup.
- `ROADMAP.md` — future research steps.
- `TIER2_ATTEMPT.md` — negative result on three generations.
- `TIER3_ATTEMPT.md` — negative result on cosmological constant.
- `TIER4_ATTEMPT.md` — discussion of consciousness dissolution.
- `build.sh` — reproducibility script.

**Project config**:
- `lakefile.toml` — Lake project; depends on Mathlib (git, v4.29.1).
- `lean-toolchain` — Lean 4.29.1.

## Calibration policy

Every claim in this directory falls into one bucket:

- **✓ VERIFIED** — Lean type-checks without `sorry`.
- **▲ PARTIAL** — Lean type-checks; `sorry` placeholders documented.
- **○ ARGUED** — prose only; presumed wrong until verified.
- **✗ STUCK** — attempted, failed; failure documented.
- **? OPEN** — not attempted.

No claim of "derived" without machine verification. Plausibility is
not proof.

## Lineage

**Technical lineage** — extends operational reconstructions: Hardy
2001, Clifton-Bub-Halvorson 2003, Chiribella-D'Ariano-Perinotti 2010,
Müller 2020/2024, Renou et al. 2021.

**Philosophical lineage** — see `LINEAGE.md`. Key additions to the
standard reconstruction-program toolkit:
- Libertarian agency without substantial self (Parfit completed, not
  rejected; persistence via stage theory — Lewis, Sider, Quine).
- First-person primacy as structure (Husserl, Schopenhauer, Whitehead).
- Market-of-wants ontology (Hayek; Aristotelian functional essences).
- Rortian "real is honorific" with Quinean teeth (inscrutability of
  reference). Rovelli's relational QM as the physical counterpart of
  Quinean ontological relativity.

The philosophy is the input; the derivations are the work.

## Build

Without Mathlib:

```
lean --root=. -o build_local/Perspectival/Ontology.olean Perspectival/Ontology.lean
LEAN_PATH=$(pwd)/build_local lean --root=. Perspectival/Transformations.lean
```

With Mathlib (full stack):

```
lake update      # may need lakecache.blob.core.windows.net allowed in network policy
lake build
```
