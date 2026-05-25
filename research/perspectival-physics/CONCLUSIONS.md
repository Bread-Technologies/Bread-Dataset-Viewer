# Conclusions — Perspectival Physics

A summary aimed at an external physicist or philosopher reading the
program for the first time. For per-result granularity see `STATUS.md`;
for the publication-target writeup see `PAPER_DRAFT.md`; for the position
relative to Müller's algorithmic idealism see `MULLER_DIVERGENCE.md`.

## 1. What this program is

A Lean-4-verified formal extension of the operational quantum-mechanical
reconstruction lineage — Hardy (2001), Clifton–Bub–Halvorson (2003),
Chiribella–D'Ariano–Perinotti (2010), Müller (2020, 2024), Renou et al.
(2021) — built on a specific philosophical refinement of that lineage:

- **Perspective-with-wanting as existence.** Axiom I: to exist is to
  instantiate a perspective with directedness. Perspective is not a
  property of a substrate; it is what existence consists in. This is a
  strictly stronger move than Müller's observation-stream ontology.
- **Anti-Dennett libertarian agency.** Each instant of choice carries the
  full weight of choice; the chooser is the perspectival structure at
  the moment of choosing, not a substantial subject and not the causal
  history. Compatibilism (Dennett 2003; imported by Müller 2024) is
  rejected as a category-mismatched rescue mechanism for a physicalism
  the framework has already withdrawn. See `MULLER_DIVERGENCE.md`.
- **Anti-Goff, Russellian-monism-extended.** Matter is how
  perspective-with-wanting appears under structural relations, not a
  substrate with intrinsic experiential properties added. Closer to
  Schopenhauer's Will and to Strawson's reading of Russellian monism
  than to Goff's panpsychism; the combination problem dissolves because
  there are no atomic experiential bricks to combine.

What is *not* on offer: a new dynamical theory, a new gauge calculation,
or a new experimental prediction at the quantitative level. What *is* on
offer is (a) a Lean-machine-verified body of theorems that derives parts
of the Hardy reconstruction and several adjacent operational results
from explicitly agent-centric axioms, and (b) an honestly catalogued map
of which further targets are tractable, which are gated on specific
formal gaps, and which the framework can only motivate.

## 2. What has been formally derived

All items below are Lean-4 theorems with no `sorry`. Line-precise
references are in `STATUS.md`; named theorems are given here so the
external reader can locate them in the repo.

**Hardy axioms.** Axioms 1 (Probabilities), 3 (Subspaces), and 5
(Continuity) are derivable in the framework's language. Axiom 1 follows
from the bare GPT structure (`Hardy.lean :: axiom1_holds`). Axiom 3
holds constructively (`Hardy.lean :: axiom3_holds`). Axiom 5 is derived
from the libertarian-agency postulate
(`Continuity.lean :: hardy_axiom5_of_agency` and
`hardy_axiom5_transitive`) — this is the framework's single most
distinctive technical contribution. Axiom 2 (Simplicity / K-minimality)
is *motivated* by Axiom IV (anti-substantialism: excess K beyond what
stable patterns require would be substance-behind-pattern) but not
formally derived; the candidate refinement
(`PatternStableWantable`) and the alternative CDP-purification path are
documented in `HARDY_A2_AS_PARSIMONY.md`. Axiom 4 (Composite-state
multiplication) is partially derivable via `productStateBilin` and the
product-Wantable state construction on `WantableGPT`.

**CHSH / Tsirelson.** In the framework's vocabulary, the
commutativity-versus-noncommutativity hinge is identified with
observer-independent-joint-ledger versus genuinely perspectival
spacelike pairs. The realist (commutative) bound 2 and the perspectival
(noncommutative) Tsirelson bound 2√2 are both verified, via Mathlib's
CHSH module, as `CHSH.lean :: bound_realist` and `bound_perspectival`.

**No-cloning and no-broadcasting.** Full chain from operational
distinguishability through linear independence to the tensor-product
impossibility (`Distinguish.lean :: distinguishable_imp_linear_independent`,
`no_cloning_of_distinguishable`, `perfect_distinguishable_imp_linear_independent`,
`operational_dim_le_state_dim`; `NoCloning.lean`; `NoBroadcasting.lean`).
The N ≤ K (operational dim ≤ state-space dim) inequality is verified
explicitly.

**Triple no-go for the bare WantableGPT bridge.** For any finite
Wantable `W` with `|W| ≥ 2`, the WantableGPT-from-finite-Wantable
construction lands strictly on the classical Hardy signature `N = K =
|W|`, and *each* of the three non-classical signatures is ruled out:

- `WantableGPT.lean :: wantableGPT_is_classical` — `K = N`;
- `wantableGPT_not_quantum` — `K = N²` fails;
- `wantableGPT_not_realQM` — `2K = N(N+1)` fails;
- `wantableGPT_not_quaternionicQM` — `K = N(2N−1)` fails;
- `wantableGPT_classical_dichotomy` — bundled form.

This is a sharp, framework-distinctive negative result: the bare
WantableGPT bridge *cannot in principle* produce any non-classical
Hardy signature. Quantum derivation must come from additional
postulates — agency strengthening (`Continuity.lean`), composition
beyond disjoint union, or non-finite Wantable structure. Composition
behaviour is fully verified at the bridge level:
`finrank_V_prod_eq_mul`, `finrank_V_sum_eq_add`.

**R6 Birkhoff disconnect for ALL n ≥ 2.** Proven this session.
On any classical n-outcome GPT (n ≥ 2), no continuous path of bijective
state-preserving linear maps connects `id` and the (01)-transposition.
`classical_general_no_strict_path_id_to_swap01` is the headline theorem.
Generalized via `swap01LinGen` (= `Matrix.toLin' ∘ Equiv.Perm.permMatrix ℝ ∘ Equiv.swap`)
with one-line det computation through `LinearMap.det_toLin' +
Matrix.det_permutation + Equiv.Perm.sign_swap`. The n=2/3/4/5 cases are
named specializations. Hypothesis-free (auto-continuity is derived from
the joint continuity field of the `StrictReversiblePath` structure).
For n=2 specifically: `classical_n2_strict_reversible_path_id_swap_empty`
with a determinant-based IVT argument
(`n2_disc_det`, `n2_disc_det_id = 1`, `n2_disc_det_swap = -1`,
`ivt_path_one_to_neg_one`, `n2_disc_det_zero_implies_not_injective`).
The strict-reversible group
of `Classical n=2` is therefore at least *two-component* —
Boolean swap is genuinely disconnected from identity through bijective
state-preserving dynamics. This is the framework's first formally
verified discriminator separating *the class of theories where strict
connected agency is possible* from *the class where it is not*.

**Hardy A4 state-half via productStateBilin.** The product-Wantable
state construction and its bilinear extension (`Examples.lean ::
productState`, `productStateBilin`, with composition
`productState_assoc`, `productState_complement_factor`,
`productState_transform_factor`, and the same-marginals-different-state
classical witnesses `diagonalState` / `antiDiagonalState`) deliver the
state-side of Hardy A4 inside the framework. The full multiplicative
composition theorem requires the genuine GPT tensor product (R5,
currently open).

## 3. What is framework-distinctive (not just recovered)

Most verified results in §2 — Tsirelson, no-cloning, N ≤ K, Hardy 1, 3,
the classical no-go — are *framework-agnostic* in their proofs: any
operational reconstruction can claim them. The framework's
philosophical vocabulary supplies *interpretation* for those results
but not *proof power*. The genuinely framework-distinctive
contributions are these:

**A5-from-agency.** `hardy_axiom5_of_agency` derives Hardy Axiom 5 from
the libertarian-agency postulate formalized as path-connectedness of
the available reversible-transformation set. Other reconstructions
*postulate* continuity of reversibles; the framework derives it from
its agency commitment. This is the load-bearing exchange of a
structural postulate for a philosophical one.

**The WantableGPT bridge as an injective MonoidHom.**
`WantableGPT.lean :: fromPTransHom` and `fromPTransHom_injective`,
together with `transformAction_vertex` and `complementPTrans_sq`,
provide a verified embedding of `PTrans W` (the framework's group of
perspectival transformations, i.e., the centralizer of `complement`
inside `Equiv.Perm W` per `Transformations.lean ::
mem_range_toEquivPermHom_iff`) into the GPT-transformation monoid. The
bridge is faithful and respects complement; it is the technical hinge
between framework vocabulary and standard operational structure.

**The triple no-go for the bare ontology.** Per §2: the conjunction
"WantableGPT is always classical *and* each of the three non-classical
Hardy signatures is provably excluded for `|W| ≥ 2`" is novel — we
know of no comparable Lean-formalized structural delimitation of the
GPT signature lattice. Negative results of this sharpness are useful
because they tell the program *exactly* where additional postulates
must do work.

**The agency hierarchy.** Four progressively stronger postulates on
the available transformation set:
`HasConnectedAgency` (path-connectedness, used to derive A5);
`StatePreservingAgency` (path-connected with state-preservation along
the path); `StrictConnectedAgency` (bijective and state-preserving
along the path); and `GroupClosedAgency` (closure under composition
and inverse, with `Reachable.equivalence` proving `Reachable` is an
equivalence relation under closure + inverse availability). The
hierarchy is constructed and used: the n=2 disconnect rules out
`StrictConnectedAgency` containing both `id` and `swap` on the
classical 2-outcome GPT (`classical_n2_no_two_element_strict_agency`).

**Philosophical dissolutions (#14, #15, #16).** Per
`TIER4_DISSOLUTIONS.md`: each canonical Tier-4 question smuggles in an
external vantage that Axiom I forbids — substrate beneath experience
(#14), viewpoint where nothing obtains (#15), time-axis beneath
meeting-pattern (#16). The dissolution is not "the question is
meaningless"; it is that the question's apparent intelligibility
depends on an ontology the framework refuses. This is philosophical
argument, not derivation; it earns its keep only if Tier 1–3 succeed
in making the underlying axioms do technical work elsewhere.

## 4. What is open and the conjectured path

**R6 general n.** The classical n = 2 disconnect (id ≠ swap through
bijective state-preserving paths) is verified hypothesis-free. The n =
3 detector (`n3_swap01_detector`) is scaffolded but the full
StrictReversiblePath-level theorem is not yet wrapped. The general-n
case via the sign-of-permutation invariant on `Classical n` is the
natural next target. The positive complement — *quantum* reversibles
form a connected Lie group, so `StrictConnectedAgency` *is* satisfied
in cQM — requires a quantum GPT construction beyond the present
codebase (density-matrix machinery).

**R7 Lie-group refinement.** Strengthening agency from
path-connectedness to smoothness so that the connected identity
component of the reversible-transformation group is a Lie group; this
is the prerequisite for any Wigner-style derivation of particle
representations.

**S1 / S2 / S3 — toward complex Hilbert space (Tier 1 #5).** Per
`TIER1_5_HILBERT.md`: (S1) tomographic locality of composition rules
out quaternionic QM and is the most tractable Lean target, via a
genuine GPT tensor product extension of Mathlib infrastructure. (S2)
connectedness of the reversible group rules out real QM and is gated
on the same agency-connectedness gap as R6/R7. (S3) observable-as-
generator duality — the framework's reading of Stone's theorem in
agency vocabulary — would force complex over real and is currently the
most speculative input. This is the framework's intended structural
complement to Renou et al. 2021's experimental falsification of rQM:
Renou rules rQM out of *nature*; (S2) would rule rQM out of *the
framework's axioms*.

**Tier 2 #6 — gauge structure.** Per `TIER2_GAUGE_SCOPING.md`: the
modest in-scope target is the `u(1)` toy step, using the verified
`scaleHom : ℝˣ ↪ PTrans ℝ` MonoidHom (`Examples.lean ::
scaleHom_injective`) to articulate the gauge-as-connection move on its
smallest nontrivial example. Full `U(1) × SU(2) × SU(3)` is *not* in
scope; "which Lie group" and "which representations" are honestly
documented as empirical input under any known framework, not as
forthcoming derivations.

**Tier 3 #11 — multi-sector dark matter.** Per `TIER3_DARK_MATTER.md`:
the framework supports the qualitative prediction that the dark sector
should be plural by default (no-cross-meetings between disjoint
Wantable sectors, `Meeting.sum_no_cross`, plus the absence of any
uniqueness clause in I–IV). Quantitative signatures distinguishing
multi-sector from single-species dark matter are *not* derivable from
the present axioms; the next concrete step is a `MultiSectorWantable`
formalization upgrading the prediction from S (suggested) to D
(qualitative, formally derived as non-uniqueness).

## 5. Methodology: metaphysics fixed, axioms adjustable

The user clarification recorded at the head of `ORIGINAL_PROMPT.md`
fixes the program's methodological commitment:

> *The metaphysics (§2 of the prompt) is fixed. The axioms (§1) are a
> formalization attempt and can be adjusted if they prove inadequate.*

The fixed point is the philosophical commitments: perspective-with-
wanting as existence; anti-Dennett libertarian agency; anti-Goff
Russellian-monism-extended; Heraclitean / Whiteheadian / Bergsonian /
Madhyamaka about persistence; market structure of wanting; particulars
as patterns, not substances. These are not subject to revision under
formal failure; they are the inputs the program is testing the
formal-derivative power of.

The *encoding* — the specific Lean predicates `Wantable`, `PTrans`,
`HasConnectedAgency`, etc. — is, by contrast, a working attempt. When
bare Axioms I–IV cannot derive a Tier 1–3 target, the licensed move is
to *strengthen* or *refine* the formal axioms while preserving the §2
commitments. The R6 / R7 agency strengthenings exemplify this: they
add structure to the formal apparatus (path-connectedness,
state-preservation, bijectivity, closure) without departing from the
libertarian-agency commitment. Similarly the candidate
`PatternStableWantable` refinement
(`HARDY_A2_AS_PARSIMONY.md`) would expose Axiom IV's anti-substantialism
in the Lean encoding without altering the underlying philosophical
claim.

The fixed point is the metaphysics; the adjustable surface is the
encoding. If no encoding succeeds, the metaphysics has failed
empirically. If an encoding succeeds, that vindicates the
philosophical commitments. Either outcome is informative.

## 6. Calibrated honesty about scope creep

Per ORIGINAL_PROMPT §8: *"Setting for X is not derivation of X."* The
program holds this discipline explicitly. The following items are
*setting-only* and are catalogued as such:

- *Gauge fields as connections.* The framework supplies an
  interpretive vocabulary (`PTrans` analogous to Christoffel; local
  PTrans force a connection-form) but does not derive `U(1) × SU(2) ×
  SU(3)`. Per `TIER2_GAUGE_SCOPING.md` §9, the modest in-scope target
  is the `u(1)` toy step.
- *Dark matter multi-sector.* The framework's no-cross-meetings
  theorem supplies a motivational prior for plural sectors but does
  not derive any quantitative signature; per `TIER3_DARK_MATTER.md`
  §6, signatures (i)–(v) are pre-existing literature, not framework
  derivations.
- *Cosmological constant, fine-tuning, QM/GR unification.* Argued
  philosophical settings; no technical derivation.
- *Three fermion generations.* `TIER2_ATTEMPT.md` documents five
  candidate angles, all negative.
- *Hard-problem / why-something / before-big-bang dissolutions.*
  Philosophical arguments from Axiom I; not formal derivations.
  Per `TIER4_DISSOLUTIONS.md`, they earn their keep only if Tier 1–3
  succeed.
- *Hardy A2.* Motivated by Axiom IV pattern parsimony; not derived.
  Catalogued AUXILIARY.
- *The CHSH / Tsirelson `*-ring picture.* The bound is verified
  *given* the operator-algebraic structure; the structure itself is
  imported from Mathlib, not derived from I–IV.
- *Complex Hilbert space.* Tier 1 #5 remains open; the three required
  strengthenings (S1, S2, S3) are catalogued explicitly.

This list is the program's standing self-audit. Every entry on it
distinguishes what the framework *provides interpretive vocabulary for*
from what it *formally derives*.

## 7. Co-authorship posture

Per ORIGINAL_PROMPT §10: *"Co-authorship to Markus Müller and other
relevant living researchers as merited."*

The framework's nearest neighbour in the contemporary literature is
Müller's algorithmic idealism (Müller 2020, 2024). The substantial
agreements — observer-centric ontology, first-person primacy of
prediction-conditional-on-perspective, no substantial external world —
are deep enough that the present program can be described, in one
aspect, as algorithmic idealism plus a specific refinement of the
observer. The principal divergence is on agency: Müller imports a
Dennett-style compatibilism that the framework rejects as
category-mismatched (a non-physicalist ontology does not need a
physicalism-rescue account of agency). The agency strengthenings
(R6/R7) that the framework requires for its conjectured quantum
reconstruction are not supportable on the compatibilist reading. The
divergence is productive: it generates concrete formal targets whose
outcomes will adjudicate.

Per the user's authorization, post-stabilization co-authorship with
Müller is on the table. Co-authorship would also be appropriate, as
merited by contribution, with researchers in the Hardy / Masanes /
Chiribella / Renou lineage if particular derivations land. The
program's posture is that productive divergence is preferred to
ornamental originality.

## 8. Disposition

This is the honest state of the program. The verified results form a
real, internally coherent body of Lean-machine-verified mathematics,
with one framework-distinctive derivation (Hardy A5 from libertarian
agency) and one framework-distinctive discriminator (the R6 n = 2
Birkhoff disconnect). The philosophically distinctive Tier 2–4
predictions remain in the Suggested / Argued / Speculative columns,
honestly catalogued. The next milestones — R6 general-n, the positive
quantum complement of the disconnect, a genuine GPT tensor for S1, the
`u(1)` baby step, and the `MultiSectorWantable` formalization — are
specified concretely enough to be worked.

If the program's central conjectural chain (constitutive choice ⇒
group-closure ⇒ connected Lie group ⇒ reversible quantum-like
dynamics, per `MULLER_DIVERGENCE.md` §4) survives further formal
verification, the framework will have produced the first
reconstruction of quantum-mechanical structure from explicit agent-
centric axioms with a derivation rather than postulation of the
continuity axiom. If it fails, the negative result will locate
precisely where the gap between philosophical agency-talk and
mathematical group structure lies. Either outcome is a real research
result. The metaphysics is fixed; the axioms remain adjustable; the
calibrated honesty discipline is the working constraint.

## Reproducibility

To rebuild from scratch:

```bash
# Install Lean 4.29.1
# Tarball at: https://github.com/leanprover/lean4/releases/tag/v4.29.1

cd research/perspectival-physics
lake update      # requires lakecache.blob.core.windows.net unblocked
                 # for fast caching; otherwise full source compile
lake build       # builds Mathlib subset + Perspectival modules
```

All proofs are deterministic; no external data or empirical inputs.
Mathlib version: `v4.29.1`. Per-result line-precise references live in
`STATUS.md`.

## Acknowledgments

Technical lineage: Hardy 2001, Clifton–Bub–Halvorson 2003,
Chiribella–D'Ariano–Perinotti 2010, Müller 2020 / 2024, Renou et al.
2021. Philosophical lineage: see `LINEAGE.md`. Lean ecosystem: Mathlib
(CHSH / Tsirelson, convex analysis, tensor products, linear
independence, group theory, topology).
