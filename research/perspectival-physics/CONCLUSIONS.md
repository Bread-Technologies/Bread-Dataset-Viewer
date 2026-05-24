# Conclusions — Perspectival Physics Lean Formalization

A summary aimed at an external reader. For per-result granularity see
`STATUS.md`; for honest commentary see `FINDINGS.md`; for the
publication-target writeup see `PAPER_DRAFT.md`.

## What was built

A Lean 4 codebase formalizing the perspectival-physics research program:

- **12 modules**, ~1800 lines of Lean, ~38 machine-verified theorems
- **Zero `sorry`** outside intentional placeholders (Hardy Axiom 2 is
  `True` because formalizing K-minimality across theories is delicate)
- **Zero compile warnings** on a clean build
- **One subagent-verified survey** of existing Lean QM formalizations
  (no prior work on GPTs, Hardy, or perspectival foundations)
- **Six documentation files**: README, STATUS, FINDINGS, LINEAGE,
  PAPER_DRAFT, PREDICTIONS, CONCLUSIONS

## Key technical results

1. **Tsirelson bound 2√2 as the framework's natural prediction** —
   the philosophical hinge (commutativity ↔ observer-independent joint
   ledger) is identified and the bound is machine-verified in
   perspective-wanting vocabulary via Mathlib's CHSH module.

2. **No-cloning theorem** with full chain from operational
   distinguishability through structural linear independence to
   tensor-product impossibility — machine-verified.

3. **3/5 Hardy axioms machine-verified DERIVABLE**:
   - Axiom 1 (Probabilities) — trivially from GPT structure
   - Axiom 3 (Subspaces) — constructive sub-GPT existence
   - Axiom 5 (Continuity) — from libertarian-agency postulate
     formalized as path-connectedness of reversible transformations

4. **N ≤ K (operational dim ≤ state-space dim)** for finite-dim GPTs
   — derived from perfect-distinguishability via linear independence.

5. **Classical GPT instance** fully constructed and verified — convex
   simplex, coordinate-projection effects, [0,1]-valued probabilities.

6. **Group action structure** — `PTrans W` is a proper Lean `Group`
   acting on `Meeting W` via Mathlib's `MulAction` interface. The
   action extends to `Reality W` (predicates on meetings) and, via
   the `WantableGPT` bridge, to the GPT state space.

7. **Structural characterization** — `PTrans W` is *exactly* the
   centralizer of `Wantable.complement` (as a permutation) inside
   `Equiv.Perm W` (`Transformations.lean :: mem_range_toEquivPermHom_iff`).
   Forgetting the resp_complement law gives an injective MonoidHom
   into the symmetric group, with image the Z/2-equivariant
   permutations. *The framework's vocabulary picks out a standard
   algebraic object* (Quinean ontological deflation).

8. **Triple no-go theorem for the bare ontology** — for any finite
   Wantable `W` with `|W| ≥ 2`:
   - The `WantableGPT.gpt W` construction always yields the *classical*
     GPT signature `N = K = |W|` (`wantableGPT_is_classical`).
   - The quantum signature `K = N²` is formally ruled out
     (`wantableGPT_not_quantum`).
   - The real-QM signature `2K = N(N+1)` is formally ruled out
     (`wantableGPT_not_realQM`).
   - The quaternionic-QM signature `K = N(2N-1)` is formally ruled out
     (`wantableGPT_not_quaternionicQM`).
   - Composition theorems give `K(W₁ × W₂) = |W₁| · |W₂|` and
     `K(W₁ ⊕ W₂) = |W₁| + |W₂|`.

   This is a comprehensive structural delimitation. Quantum
   derivation requires additional postulates (agency / composition /
   non-finite structure) beyond I–IV; the bare ontology *cannot* even
   in principle produce a non-classical Hardy signature via the
   WantableGPT bridge for `|W| ≥ 2`.

## The framework's distinctive contribution

Of the verified results, **only Hardy Axiom 5 from libertarian agency**
(`Continuity.lean :: hardy_axiom5_of_agency` and refinements) is
*technically distinctive*: it uses the framework's specific
philosophical commitment (libertarian agency at each instant,
formalized as path-connectedness of the transformation group) to
derive a Hardy axiom that other reconstructions take as a postulate.

Every other verified result is *framework-agnostic* in its proof: the
CHSH/Tsirelson bounds, no-cloning, no-broadcasting (classical
construction), distinguishability lemmas, Hardy Axioms 1 and 3, and the
N ≤ K inequality are all theorems any reconstruction can claim. The
framework's philosophical vocabulary provides *interpretation*, not
*proof power*, for these results.

## What was NOT achieved

Honestly documented:

- No quantum GPT instance (would require density-matrix machinery
  beyond what we imported from Mathlib).
- No derivation of the *-algebra picture from I–IV (it is imported
  in the CHSH bridge).
- No derivation of complex (vs real/quaternionic) Hilbert space
  (the Renou et al. 2021 program).
- No full Hardy reconstruction (K = N² target unproven).
- Tier 2 (gauge group U(1)×SU(2)×SU(3); three fermion generations):
  no progress possible from the present axioms; not known to anyone
  from any axiom system.
- Tier 3 (cosmological constant; dark matter quantitative
  predictions; fine-tuning forcing): philosophical gestures only.
- Tier 4 (hard-problem dissolution; partial panexperientialism):
  philosophical, not technical.

## The most promising next bet

The Hardy Axiom 5 derivation establishes that the framework's
libertarian-agency commitment has at least one place where it does
unique technical work. The next research target is to push this
further:

**Conjecture.** The framework's axioms, plus a refinement of the
agency postulate that forces *path-connectedness* (rather than
admitting it as a hypothesis), suffice to single out *connected Lie
groups* as the structure of reversible perspectival transformations.
This would distinguish quantum theory (U(N), connected Lie) from
classical theory (S_N, discrete) at the framework level.

The conjecture has not been proven. It is the natural next research
program target.

## Reproducibility

To rebuild from scratch in this container:

```bash
# Install Lean 4.29.1 (network policy permitting)
# Tarball at: https://github.com/leanprover/lean4/releases/tag/v4.29.1

cd research/perspectival-physics
lake update      # requires lakecache.blob.core.windows.net unblocked
                 # for fast caching; otherwise full source compile
lake build       # builds Mathlib subset + Perspectival modules
                 # full compile takes ~1-2 hours on 4 cores
```

All proofs are deterministic. No external data or empirical inputs.
Mathlib version: `v4.29.1`.

## Acknowledgments

Research direction: perspectival-physics program (independent
formulation). Technical lineage: Hardy 2001, Clifton-Bub-Halvorson
2003, Chiribella-D'Ariano-Perinotti 2010, Müller 2020/2024, Renou
et al. 2021. Philosophical lineage: see `LINEAGE.md` (Whitehead,
Schopenhauer, Quine, Lewis, Sider, Rovelli, Hayek, and the Madhyamaka
tradition).

Lean ecosystem: Mathlib (extensively used; CHSH/Tsirelson modules,
convex analysis, tensor products, linear independence, group theory,
topology). Physlib (consulted but not imported in this codebase).

## Disposition

This is the honest state of the framework. The verified results
form a real, internally coherent body of mathematics. The
philosophically distinctive predictions remain mostly in the
Suggested/Speculative columns. Continued work would target the
items in **The most promising next bet** above.

If the framework's central conjecture survives further scrutiny, it
would constitute the first reconstruction of quantum-mechanical
structure from explicit agent-centric axioms with a derivation
(rather than postulation) of the continuity axiom. If it fails, the
negative result tells us where the gap between philosophical
agency-talk and mathematical group structure lies. Either outcome is
a real research result.
