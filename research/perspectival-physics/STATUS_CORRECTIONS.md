# STATUS.md — What Needs Fixing

## 1. Axioms section (top of file, "## Axioms (the inputs)")

**Wrong:** Shows 4 axioms (I–IV).

**Correct:** There are exactly TWO axioms per ORIGINAL_PROMPT_V2:
- Axiom I: Existence = wanting (directional + relational). Encoded in `TierA.lean` as `Want`, `Existent`, `Wantable`, `axiom_I_directedness`, `axiom_I_relationality`.
- Axiom II: Actualization is irreversible (the possible/actual cut is real). Encoded in `TierA.lean` as `Meeting`, `MeetingStatus`, `actualize`, `axiom_II_actualization_irreversible`. Mechanical content: Witkowski-Brown-Truong 2024.

Old Axioms III (reality = meetings) and IV (particulars = stable patterns) were definitions, not axioms. They are now infrastructure in `Ontology.lean` and `TierB.lean`.

## 2. What is NOT an axiom and NOT to be derived (explicitly dissolved)

These should be added somewhere prominent:

- **Born rule**: QBist Dutch-book coherence. Not a framework theorem, not derived from Axioms I–II. The framework explains *why* agents must use probabilities, but the numerical form `|⟨ψ|φ⟩|²` is adopted from QBism, not derived.
- **Entropy**: Jaynesian subjectivist coarse-graining. Not a substantial property. The Second Law is *necessary* (WBT 2024 proves many-to-one collapse is mechanically forbidden under conservative dynamics), but entropy itself is observer-relative coarse-graining, not a framework output.
- **Hilbert space**: Tier B structure, imported not derived. The clearing condition constrains correlations (separable CHSH ≤ 2 proved in `Clearing.lean`; Tsirelson ≤ 2√2 is open pending C*-algebra bridge).

## 3. Module count

**Wrong:** "13 modules" (in the footer of Perspectival.lean and possibly STATUS.md).

**Correct:** 14 modules. Two new modules added this session:
- `Perspectival/Actuality.lean` — Problem C (classical/non-classical divide)
- `Perspectival/Clearing.lean` — Problem B (clearing condition → CHSH gap)

## 4. Seam 4 status

**Wrong:** "Seams 1-3 have formal correlates; Seam 4-6 open."

**Correct:** Seam 4 (Decoherence) has a complete count-based structural shadow in `Perspectival/Decoherence.lean` (~2400 lines, build-verified). The open part is continuous-time exponential suppression dynamics (Tier 2). Update to: "Seams 1-4 have formal correlates (Seam 4 at count-level); Seams 5-7 open."

## 5. New modules not yet in the status table

The following modules exist and build clean but may not be listed in the verified-results table:
- **`Perspectival/Actuality.lean`**: `Frame`, `Decomposes`, `decomposition_unique`, `Compatible`, `Incompatible`, `PerspectiveRelative`, `Square` witness (`square_perspectiveRelative`), `actuality_bridge`. All zero sorry.
- **`Perspectival/Clearing.lean`**: `clearingProb`, `clearingProb_self_delta`, `compatible_iff_clearing_deterministic`, `incompatible_iff_clearing_intermediate`, `square_clearing_maximal_indeterminacy`, `square_clearing_all_half`, `compatible_correlator_bounded`, `ProductClearing`, `quantum_tsirelson_bound_conj` (open conjecture, placeholder `True`). Zero sorry except the conjecture which is explicitly marked open.

## 6. v2 architectural status section

The section "### v2 architectural status" at the bottom is broadly accurate but should note:
- Actuality.lean and Clearing.lean now provide the formal encoding of Problems B and C
- The clearing condition (Axiom II at Frame level) separates compatible (classical, CHSH ≤ 2) from incompatible frames; getting to exactly Tsirelson requires deriving the Hilbert space from the clearing condition (open)
- Seam 4 is now structural-complete at count level (not open)
