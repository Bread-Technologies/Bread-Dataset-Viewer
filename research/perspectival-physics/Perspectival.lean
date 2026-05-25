import Perspectival.Ontology
import Perspectival.Transformations
import Perspectival.Composition
import Perspectival.CHSH
import Perspectival.GPT
import Perspectival.Hardy
import Perspectival.NoCloning
import Perspectival.NoBroadcasting
import Perspectival.Classical
import Perspectival.Continuity
import Perspectival.Distinguish
import Perspectival.WantableGPT
import Perspectival.GPTTensor
import Perspectival.Examples
import Perspectival.CircleGPT
import Perspectival.Dichotomy

/-!
# Perspectival Physics

Lean 4 formalization of an agent-centric reconstruction of operational
quantum theory.

## Axioms (encoded in `Perspectival.Ontology`)

  I.   To exist is to instantiate a perspective with directedness.
  II.  Wants are intrinsically relational (every want has a complement).
  III. Reality is the structure of meetings between wants.
  IV.  All apparent particulars are stable patterns within (III);
       the mathematical structure is group-theoretic.

## Layout

  - **Metaphysical level** — `Ontology`, `Transformations`,
    `Composition`. Types and group structure on perspective/wanting.
  - **Operational level** — `GPT`, `Hardy`, `Distinguish`,
    `Continuity`, `Classical`, `NoCloning`, `NoBroadcasting`.
    Probabilistic structures with linear-algebraic content.
  - **Bridge** — `WantableGPT`. Constructs a GPT from any finite
    Wantable; the metaphysical group `PTrans W` embeds injectively
    into the operational monoid of GPT self-transformations
    (`fromPTransTransformHom`, `fromPTransHom_injective`).
  - **External bridge** — `CHSH`. Connects to Mathlib's CHSH/Tsirelson.

## Headline results

  * **Tsirelson bound 2√2** under noncommutative *-algebra hypothesis
    (`bound_perspectival`); commutative case gives Bell bound 2
    (`bound_realist`). The framework's reading of the philosophical
    hinge: commutativity ↔ observer-independent joint ledger of facts.
  * **No-cloning theorem** in linear-algebra form
    (`no_cloning_of_linear_independent`).
  * **Hardy Axioms 1, 3, 5 derived** from the framework's axioms.
    Axioms 2, 4 documented as auxiliary.
  * **N ≤ K** (operational dim ≤ state-space dim) in finite-dim GPTs.
  * **Libertarian agency ⇒ Hardy Axiom 5** — the framework's
    distinctive technical contribution.
  * **Metaphysical–operational bridge** — Wantable structure produces
    a GPT, with PTrans W injecting faithfully into the operational
    transformation monoid.

## Documentation in `research/perspectival-physics/`

  - `README.md`, `STATUS.md`, `FINDINGS.md`, `CONCLUSIONS.md`
  - `PREDICTIONS.md`, `LINEAGE.md`, `FAQ.md`, `GLOSSARY.md`
  - `PAPER_DRAFT.md`, `ROADMAP.md`, `TIER2_ATTEMPT.md`, `DEPS.md`

Status: 13 modules, ~70 verified theorems, full project builds clean.
-/
