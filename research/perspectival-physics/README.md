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

- `Perspectival/Ontology.lean` — axioms I–IV encoded as Lean 4 types.
- `Perspectival/Transformations.lean` — perspectival transformations,
  their group laws, and action on meetings.
- `STATUS.md` — calibrated catalog of verified / partial / argued /
  stuck / open. **Read this before reading anything else here.**
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

Extends operational reconstructions: Hardy 2001, Clifton-Bub-Halvorson
2003, Chiribella-D'Ariano-Perinotti 2010, Müller 2020/2024, Renou
et al. 2021. Adds a specific philosophical refinement (libertarian
agency without substantial self; first-person primacy as structure;
market-of-wants ontology). The philosophy is the input; the derivations
are the work.

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
