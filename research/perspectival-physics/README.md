# Perspectival Physics

A foundations-of-physics research program that attempts to derive
operational quantum theory — and ideally substantial portions of the
Standard Model — from agent-centric axioms about perspective, wanting,
and meeting.

This directory lives inside the Bread-Dataset-Viewer repo as the only
available durable storage for the work. The research is unrelated to
the dataset viewer; it is parked here because it is the authorized
push target.

**Headline results** (all machine-verified, no `sorry`):
1. **Hardy QUADCHOTOMY**: four GPT instances at distinct Hardy K-
   signatures — classical (K=N), CircleGPT (rebit, K=N(N+1)/2),
   QubitGPT (qubit, K=N²) at N=2, and QutritGPT (qutrit, K=N²) at N=3
   (`Dichotomy.hardy_quadchotomy`).
2. **Classical-vs-quantum L7 dichotomy**: `framework_dichotomy_existential`
   — no `PurePreservingTransitiveAgency` on Classical n ≥ 2
   (UNCONDITIONAL via R1 forward + reverse + L6 vertex-preservation),
   while CircleGPT carries an unconditional `TransitiveAgency`.
3. **Hardy gauge ladder**: `framework_gauge_ladder` — U(1) on CircleGPT,
   full non-abelian SO(3) on QubitGPT (qubitStrictConnectedAgency_full),
   SU(3) toehold via λ₃ generator on QutritGPT — all the SM gauge
   factors structurally instantiated.
4. **Triple no-go theorem**: the bare-ontology bridge `WantableGPT.gpt W`
   always yields the *classical* signature; each of the three
   non-classical Hardy signatures is ruled out for `|W| ≥ 2`
   (`WantableGPT.lean :: wantableGPT_classical_dichotomy`).
5. **Hardy A5 strong-form derivable**: `axiom5_strong_of_transitive_agency`
   derives the substantive form of A5 from the agency hierarchy
   (`Continuity.TransitiveAgency.hardy_axiom5`).
6. **Tsirelson 2√2** via Mathlib's CHSH module and the framework's
   commutativity ↔ joint-ledger identification (`CHSH.lean`).
7. **Hardy A4 dimension multiplicativity** at the general GPT level via
   `gptTensor_finrank_eq_mul` (= K_A · K_B); forward direction of N-mult
   via `gptTensor_distinguishable_general` (`Hardy.lean`, `GPTTensor.lean`).
8. **TomographicLocality** excludes BOTH rebit and qQM from the
   framework's preferred composition, leaving qubit as the unique
   non-classical signature consistent with both L7 and local tomography
   (the *structural* qubit-forcing argument; full formal qubit_uniqueness
   theorem deferred).
9. **No-cloning + No-broadcasting** via linear independence (`NoCloning.lean`,
   `NoBroadcasting.lean`).

The triple no-go theorem is the framework's most distinctive recent
contribution: it makes precise what the bare axioms can and cannot
deliver, sharpening the next research step (R6/R7 agency
strengthening).

## Layout

**Lean code** (`Perspectival/`):
- `Ontology.lean` — axioms I–IV encoded as Lean 4 types.
- `Transformations.lean` — PTrans as a Group, MulAction on meetings.
- `Composition.lean` — disjoint-union, no-cross-system meetings.
- `CHSH.lean` — Tsirelson 2√2 via Mathlib's CHSH module.
- `GPT.lean` — generalized probabilistic theory data + Monoid on
  self-Transforms.
- `Hardy.lean` — Hardy's 5 axioms (4/5 derivable; A2 motivated).
  A4 dimension half + N-mult forward direction (general GPT level).
- `NoCloning.lean` — linear-algebra no-cloning theorem.
- `NoBroadcasting.lean` — classical broadcaster (quantum case open).
- `Classical.lean` — concrete n-outcome classical GPT instance,
  L6/L7 closures, R1 (pure ⇔ vertex).
- `Continuity.lean` — libertarian agency → Hardy Axiom 5;
  7-level agency hierarchy; OneParameterFamily / HasMultiAxisAgency.
- `Distinguish.lean` — distinguishability ↔ linear independence.
- `WantableGPT.lean` — bridge: Wantable → GPT, with injective MonoidHom.
- `Examples.lean` — worked end-to-end demonstrations.
- `CircleGPT.lean` — rebit / real-QM 2-level system (K=3=N(N+1)/2);
  full pure-state classification; rotOneParameterFamily (U(1) gauge).
- `QubitGPT.lean` — qubit / complex-QM 2-level system (K=N²=4);
  three SO(3) rotation generators + full SO(3) StrictConnectedAgency.
- `QutritGPT.lean` — qutrit / complex-QM 3-level system (K=N²=9);
  λ₃ Gell-Mann generator (SU(3) toehold).
- `GPTTensor.lean` — general GPT tensor product (Hardy A4 dimension
  half + TomographicLocality + productEffect for N-mult).
- `Dichotomy.lean` — framework's classical-vs-quantum dichotomy theorem,
  Hardy trichotomy + quadchotomy, gauge ladder, framework_certificate.

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
