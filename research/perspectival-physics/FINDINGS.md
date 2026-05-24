# Findings — Narrative Research Log

A calibrated story of what the perspectival-reconstruction program has
and has not earned. Read alongside `STATUS.md` (the per-result catalog)
and `PAPER_DRAFT.md` (the writeup-form). This document is the narrative
companion: where the catalog enumerates, this document interprets, and
where prose argument is unavoidable, this document is where it goes.

Every claim below carries one of four calibration tags per
`ORIGINAL_PROMPT.md` §7:

- **(a) formally verified** — Lean 4 type-checks; no `sorry`.
- **(b) verbally argued** — a prose case the author considers tight,
  not yet machine-checked. Presumed wrong until verified.
- **(c) plausible** — consistent with what is verified, but uninvestigated.
- **(d) speculative** — a conjectural extension whose status is open.

## 0. The arc, in one paragraph

Tier 1 of the program — *establish that the framework can do real
operational work* — is substantially complete. Hardy's Axiom 1 is
derived from the GPT structure (a); Axiom 3 is derived in weak form
(a); Axiom 5 is derived from the framework's libertarian-agency
postulate (a) — the first machine-verified content that other
reconstructions take as input. Axioms 2 and 4 remain auxiliary in the
honest sense — *motivated* by the framework's metaphysics but not
*derived* from its Lean encoding (see `HARDY_A2_AS_PARSIMONY.md`). The
CHSH/Tsirelson 2√2 bound (a), no-cloning (a), no-broadcasting (a), and
the operational-dimension inequality `N ≤ K` (a) are all verified
inside the framework's vocabulary. A triple no-go theorem (a) rules
out the three canonical non-classical Hardy signatures (quantum,
real-QM, quaternionic-QM) for the bare WantableGPT construction,
sharpening the research target: any non-classical reconstruction must
come from *strengthenings* of the bare ontology, not from the ontology
itself. This session's R6 program is the first machine-verified such
strengthening, and the n=2 Birkhoff disconnect theorem
`classical_n2_strict_reversible_path_id_swap_empty` (a) is the
program's first framework-distinctive non-classical *discriminator*.
Tiers 2–4 remain honestly open, with Tier 2 #6 (gauge groups) reframed
via `TIER2_GAUGE_SCOPING.md`, Tier 3 #11 (dark matter) reframed as
motivational rather than quantitative-signature-deriving via
`TIER3_DARK_MATTER.md`, and Tier 4 (#14–#16) catalogued as
philosophical dissolutions in `TIER4_DISSOLUTIONS.md` rather than as
independent achievements. The fixed point per the user clarification
remains: the metaphysics in §2 of `ORIGINAL_PROMPT.md` is not
negotiable; the axioms in §1 are a formalization attempt and may be
refined (the R6/R7 strengthenings are exactly such refinements).

## 1. What Tier 1 has earned

### 1.1 The ontology layer — deflated, in a load-bearing way

The bare ontology is now mathematically thin and well-understood.
Verified: `Wantable` carries an involutive `complement` (a); `Meeting
W ≃ W` via `mk_fromSide` — meetings are not richer than wants (a);
`PTrans W` is *exactly* the centralizer of `complement` inside
`Equiv.Perm W` (a); `actMeeting complement = Meeting.swap` (a). These
are not novelties but *deflations*: the framework's perspectival
vocabulary picks out a precise, standard Z/2-equivariant
permutation-group object. The deflation is load-bearing — it means
the framework cannot derive non-classical physics from definitions
alone. The technical work must come from *postulates beyond I–IV in
their bare form*, which is exactly what the R6/R7 strengthenings
introduce.

### 1.2 The operational layer — Hardy axioms partially derived

A finite-dim GPT is a vector space with state cone, effect cone, and
unit functional; the full Mathlib-aware machinery is in (a). Hardy's
Axiom 1 is `axiom1_holds` (a); Axiom 3 in weak form is `axiom3_holds`
(a); Axiom 5 reduces to `hardy_axiom5_transitive` (a) given
path-connectedness of the reversible group, itself supplied by
`HasConnectedAgency`. The framework's claim that Axiom 5 is *derived*
— not assumed — rests on a step honestly identified: the *easy*
direction is verified (agency-as-path-connectedness ⇒ Axiom 5 by
direct construction); the *hard* direction — that libertarian agency
*forces* path-connectedness — is not yet in the codebase. The agency
postulate is currently the input, not the conclusion. See §L3 below.
This is one of the program's principal open scientific bets.

### 1.3 The triple no-go — sharpest framework-distinctive structural claim

`wantableGPT_classical_dichotomy` (a): for any finite Wantable `W`
with `|W| ≥ 2`, the bridge `WantableGPT.gpt W` lands strictly on the
classical row of Hardy's table — `N = K = |W|`, and *each* of the
three canonical non-classical signatures (quantum `K = N²`, real-QM
`2K = N(N+1)`, quaternionic-QM `K = N(2N−1)`) is formally ruled out.
Composition adds: `K(W₁ × W₂) = |W₁| · |W₂|`, `K(W₁ ⊕ W₂) = |W₁| +
|W₂|` (a). This sharply frames the research target: the bare ontology
distinguishes neither classical from quantum nor any non-classical
theory from another, so any "quantum-as-perspectival" claim must come
from a *specific* strengthening — and the program is now precise
about *which* strengthening.

### 1.4 The metaphysical-to-operational bridge — verified faithful

The framework's central technical claim — that the metaphysical
perspective-and-wanting layer *produces* operational physics — is now
a machine-verified injective MonoidHom. `WantableGPT.gpt W` (a)
constructs a full GPT from a finite Wantable; `fromPTransHom` (a) is
the induced MonoidHom `PTrans W → (V W →ₗ V W)`;
`fromPTransHom_injective` (a) is the faithfulness — distinct
metaphysical transformations give distinct operational ones. This is
the framework's distinctive content vs purely operational
reconstructions: the metaphysical group is not a parallel structure;
it is *recoverable from* the operational structure via the injection.
The remaining gap — whether the operational structure *uniquely
determines* the choice of GPT — is the open determinism question,
partially addressed by `wantableGPT_is_classical` (which says the
bare bridge is forced to be classical).

### 1.5 CHSH / Tsirelson and no-cloning — verified, but framework-agnostic

`bound_realist` and `bound_perspectival` (a) recover the 2 and 2√2
bounds, via Mathlib. The framework's contribution is *interpretive*:
it identifies *which* algebraic hypothesis (commutativity) is the
realist hinge, and reads its rejection ("no observer-independent
joint ledger") as a distinctive philosophical commitment. The
mathematical content is Mathlib's; the interpretive content is the
framework's. No-cloning is verified at the level of linear-algebra
impossibility (`no_cloning`, `no_cloning_of_distinguishable`,
`no_cloning_of_linear_independent`, all (a)). These are
framework-agnostic results in the sense that any GPT-style
reconstruction can claim them; they are interpretive victories for
the framework, not unique-proof-power ones.

## 2. This session's framework-distinctive contributions

This is where the program has earned new ground.

### 2.1 The R6 Birkhoff disconnect on Classical n=2

The single most important new theorem of the session,
`classical_n2_strict_reversible_path_id_swap_empty` (a):

> On the Classical n=2 GPT, no continuous path of bijective
> state-preserving linear maps connects `id` and `swap`. Empty
> `StrictReversiblePath`. No hypothesis required.

The proof chain is fully formal (a): a discrete determinant invariant
`n2_disc_det R = R(vertex 0) 0 − R(vertex 1) 0` evaluates to `+1` on
identity and `−1` on swap; the joint-continuity field of
`StrictReversiblePath` derives the continuity hypothesis; IVT forces
a zero of `n2_disc_det` along any such path; det = 0 implies the map
is non-injective on a state-preserving map, contradicting
bijectivity. As a corollary (a), `classical_n2_det_one_eq_id`: every
state-preserving linear `R` on `V 2` with det = 1 equals
`LinearMap.id`. Together with the symmetric det = −1 case (b, argued
in `SESSION_REPORT.md` line 47, *pending formalization*) this would
give the full n=2 enumeration `StrictReversible (Classical n=2) =
{id, swap} = S_2`.

To the best of our knowledge, no other GPT reconstruction has a
Lean-formalized version of this discreteness phenomenon. This is the
program's first verified *non-classical-discriminator*: it doesn't
recover a known result in framework vocabulary, it produces a *new*
result the framework's strengthened agency postulates make available.
Per `R6_GENERAL_N_SCOPING.md`, the extension to general `n ≥ 3` via
`LinearMap.det` ↔ permutation sign is technically straightforward
(~300 lines, all required Mathlib pieces exist), deferred as a polish
task; the *conceptual* content is at n=2.

### 2.2 The agency hierarchy — sharpening A5-from-agency

The R6 work introduced a four-level hierarchy of agency postulates in
`Continuity.lean` (`StatePreservingPath` → `StatePreservingAgency`;
`ReversiblePath` → `StrongConnectedAgency`; `StrictReversiblePath` →
`StrictConnectedAgency`), all formal (a). The hierarchy clarifies
what was previously a single postulate: state-preservation alone is
too weak (convex state spaces make affine interpolation
auto-state-preserving), unit-preservation strengthens but still
admits classical models, and *bijectivity-along-the-path* is the
substantive R6 condition. This is the kind of axiom refinement the
user clarification explicitly authorized: when the bare formulation
cannot do the work, sharpen it, preserving the philosophical
commitments in §2.

### 2.3 Classical-correlation no-factorization

`diagonalState` on `Bool × Bool` — the verified state `(1/2)(vertex
(t,t)) + (1/2)(vertex (f,f))` — is provably (a) *not* `productState
f g` for any pair of single-system states. This is the program's
first formal classical analog of entanglement-as-non-factorizability.
It is not Bell nonlocality (both `diagonalState` and
`antiDiagonalState` are perfectly distinguishable classical
mixtures), but it formalizes the operational content that *correlated
≠ factorizable* inside the bare classical bridge — the strongest such
result the framework can support before introducing R6/R7. Adjacent
(a)-verified theorems: `diagonalState_distinguishable_antiDiagonalState`,
`leftMarginal diagonalState = uniformBool`, and the *generic*
`WantableGPT_classical_separability` (a) — every state on a product
Wantable is a sum of weighted product-vertex states. The framework is
now formally precise about *where the classical bridge's ceiling lies*.

### 2.4 The Lie-group seed (`scaleHom` and continuous PTrans)

`scaleHom : ℝˣ →* PTrans ℝ` (a) embeds the multiplicative group of
nonzero reals — a one-dimensional Lie group — into the PTrans group
on the continuous Wantable `(ℝ, complement = Neg.neg)`. Verified
distinctness witnesses (`scaleHom (Units.mk0 2) ≠ scaleHom (Units.mk0
3)`, `scaleHom (-1) ≠ 1`) (a) and the existence of three pairwise
distinct PTrans (a) make this the first formal evidence that
continuous Wantables host substantively more PTrans structure than
finite ones. Per `TIER2_GAUGE_SCOPING.md`, this is the smallest
non-vacuous instance of "local perspectival transformation forces a
connection." It does not derive `U(1)`, let alone `U(1) × SU(2) ×
SU(3)`; it establishes (a) that the framework's bare vocabulary
already contains nontrivial Lie-group-like structure on the simplest
continuous example, which is the necessary scaffolding for any
serious Tier 2 attack later.

### 2.5 The R7 algebraic scaffolding

`Continuity.lean` now contains `ClosedAgency` (a; composition closure
strengthening `HasConnectedAgency`), `Reachable.equivalence` (a;
`Reachable` is an equivalence relation under `ClosedAgency` plus
per-element inverse availability), `StrictReversible` (a; Reversible
+ bijective `toLin` with `.id`, `.inv`, `.comp` and inverse laws),
and `complementSubgroup ≤ Subgroup.center (PTrans W)` (a; ⟨complement⟩
is central in PTrans). These are algebraic prerequisites for the R7
Lie-group refinement: a group is needed before its connected identity
component can be discussed; closure under composition is needed
before density can be discussed; centrality of involutions is the
kind of structural fact that, in the quantum case, will be invoked to
discuss tensor-factor structure. None of this *is* the R7 derivation,
but the scaffolding is in place (a) for it.

## 3. The path forward — open work in dependency order

### 3.1 R6 general-n (tractable, deferred)

Per `R6_GENERAL_N_SCOPING.md`: the extension of the n=2 Birkhoff
disconnect to arbitrary `n` via `LinearMap.det ↔ Perm.sign` is a
~300-line, medium-difficulty Lean task with all Mathlib pieces in
place (`Continuous.matrix_det`, `Matrix.det_permutation`,
`Matrix.doublyStochastic`, `Matrix.extremePoints_doublyStochastic`,
IVT). Bottleneck: `LinearMap ↔ Matrix` plumbing, not mathematics.
Deferred because the n=2 case already establishes the
framework-distinctive content; this is a polish task best done in the
paper-draft run-up. (c) plausible to verify on demand.

### 3.2 R7 (Lie-group refinement) — the next high-leverage step

R7 is what *positively* completes the R6 disconnect: classical GPTs
provably cannot support `StrictConnectedAgency` containing distinct
permutations; quantum GPTs ought to be exactly the theories that
*can*, because `U(N)` is a connected compact Lie group with every
pair of elements connected by a smooth path. The technical chain:
strengthen `HasConnectedAgency` to a smoothness postulate; show that
on a topologically-rich Wantable the connected identity component of
the available reversibles is a Lie group; build the quantum GPT
instance and verify it realizes the strengthened agency. (d)
speculative as to whether the chain closes cleanly; (c) plausible
that the first two arrows are tractable Lean targets in the same
~6–12 month window. This is the program's largest live bet.

### 3.3 S1–S3 (the Hilbert-space target)

`TIER1_5_HILBERT.md` decomposes the complex-vs-real-vs-quaternionic
Hilbert space derivation into three sub-targets:

- **(S1) Tomographic locality of composition** — construct
  `gptTensor` and prove `K_AB = K_A · K_B`. Tractable Lean target;
  rules out qQM via standard GPT arguments. (c) plausible.
- **(S2) Connected reversible dynamics** — gated on the same
  agency-connectedness gap as R6/R7. Rules out rQM (whose `O(N)` is
  disconnected). (d) speculative until R7 lands.
- **(S3) Observable-as-generator duality** — the philosophical
  step. Stone's-theorem-style identification of each one-parameter
  reversible family with its self-adjoint generator. Distinguishes
  cQM from rQM at the "anti-symmetric generators are observables"
  level. Not formalized; (c) plausible if R7 lands.

The honest reading: of the three Hardy non-classical signatures, qQM
exclusion is tractable now via local tomography; rQM exclusion is
gated on R7; full uniqueness (cQM picked out) is gated on (S3),
which is the most speculative and not yet a Lean target.

### 3.4 Hardy A2 as pattern parsimony (axiom-refinement candidate)

Per `HARDY_A2_AS_PARSIMONY.md`: the framework can *motivate* A2
(K-minimization) as a consequence of Axiom IV's anti-substantialism —
excess K beyond what stable patterns require would be "substance
behind pattern", which the metaphysics forbids. This is stronger than
Hardy's bare Occam appeal but does not yet *derive* A2; deriving it
requires formalizing pattern stability (D1), proving a
substance-behind-pattern impossibility theorem (D2), and refining the
`Wantable` typeclass to expose pattern stability (D3). All (b) in the
prose; (c) plausibly tractable. A worthy mid-priority refinement.

## 4. The Müller relationship — algorithmic idealism plus libertarian agency

`MULLER_DIVERGENCE.md` records the program's refined position vs
Müller's algorithmic idealism (Müller 2020, 2024). The substantial
agreement: observer-centric ontology, no substantial external world,
first-person primacy of "what should I expect next." The substantial
divergence: Müller imports a Dennett-style compatibilism about
agency in a footnote; the framework rejects it.

The rejection is not ornamental. The framework's R6/R7 strengthenings
— `StrictConnectedAgency` and its relatives — license group structure
on transformations precisely because *the chooser is constitutive of
the perspective at the moment of choosing*. On compatibilism, the
availability set is whatever the substrate happens to make available;
it need not be group-closed and need not yield reversibility.
Compatibilist agency cannot motivate `StrictConnectedAgency` *as an
axiom* — only as a phenomenological accident. Libertarian agency
without a substantial chooser can. This is what makes the framework's
distinctive philosophical commitment *technically load-bearing*: the
conjectural reconstruction chain *Axiom IV (constitutive choice) ⇒
group-closed availability ⇒ Lie group ⇒ quantum reversibles* (d) is
the specific arrow that, if it closes, justifies the metaphysical
commitment. If it doesn't close, the framework will need to retreat
— possibly toward Müller's more cautious compatibilism, possibly
toward a different refinement of Axiom IV.

The posture is collaborative. Müller is the nearest neighbour in the
contemporary literature; post-stabilization co-authorship is on the
table per `ORIGINAL_PROMPT.md` §10. The divergence is productive
because it is risky in Popper's sense — it has formal consequences
that can fail. Anti-Dennett libertarian agency is therefore *the*
load-bearing distinctive philosophical commitment of the program; it
is what makes the framework's specific Lean encoding earn its keep
beyond what Müller's program already does.

## 5. Tiers 2–4 — an honest catalog

### 5.1 Tier 2 (Standard Model derivations)

Per `TIER2_GAUGE_SCOPING.md`, the gauge group target #6 has been
*reframed*, not derived. The Lean baby step — `scaleHom_injective`
embedding `ℝˣ` into `PTrans ℝ` — is (a)-verified this session and is
the smallest non-vacuous example of "continuous local perspectival
transformation." Two unforced inputs are now documented as honest
empirical input rather than forthcoming derivations: *which* Lie
group is the gauge group, and *which* representations the fermions
inhabit. The framework reframes gauge fields as connections in the
fictitious-force / Christoffel sense (b) and predicts that gauge
groups should be *compact, semisimple-plus-abelian Lie groups*
generally; selecting the three SM factors is not in scope under
axioms I–IV alone. Three-generations is recorded ✗ NEGATIVE in
`TIER2_ATTEMPT.md` — five candidate angles fail. Particle reps and
mass hierarchies are gated on R7 and on empirical input.

Per `ORIGINAL_PROMPT.md` §7: "if the axioms prove unable to support
the derivations — that is also a result." Tier 2 #6, #8, #9 are
*results in this honest sense* — the framework's bare axioms do not
force the SM gauge group, do not pick out particle representations,
do not derive mass hierarchies, and the reasons *why* are documented
with calibration.

### 5.2 Tier 3 (cosmology, dark matter, fine-tuning, QM/GR)

Per `TIER3_DARK_MATTER.md`: dark matter #11 is now reframed as
*motivational* rather than *quantitative-signature-deriving*. The
framework genuinely contributes a *prior shift*: Axiom II + Axiom III
+ the formal `Meeting.sum_no_cross` theorem (a) make single-species
dark matter look like an unmotivated restriction of the multi-sector
default. This justifies experimental program design favouring
diversification (multi-target direct detection, multi-band GW
searches, cluster-merger lensing) but does not predict quantitative
signatures. The `MultiSectorWantable` formalization sketched in §7
of `TIER3_DARK_MATTER.md` is the smallest concrete next step to
convert the qualitative prediction from **S** to **D (qualitative,
formally derived as non-uniqueness)**. The quantitative half of #11
— specific gravitational signatures distinguishing N-sector from
1-sector — is **not achievable** with the framework as currently
constituted. The cosmological constant (#10), fine-tuning (#12), and
QM/GR unification (#13) remain ✗ SPECULATIVE in `TIER3_ATTEMPT.md`.

This is the user-authorized form of honesty: the framework *motivates*
some Tier 3 content (notably multi-sector dark matter) but does not
*derive* quantitative signatures. That the axioms cannot support the
derivation is itself a result, documented and calibrated.

### 5.3 Tier 4 (dissolutions of hard problem / why-something / origin)

Per `TIER4_DISSOLUTIONS.md`: the three Tier 4 targets (#14 hard
problem, #15 why-something, #16 origin/before-big-bang) are
catalogued as *dissolutions* rather than independent achievements.
Each canonical question smuggles in an external vantage that Axiom I
refuses: matter-as-substrate beneath experience (#14), a viewpoint
from which nothing-could-obtain (#15), a time-axis beneath the
meeting-pattern (#16). The dissolutions are (b) — philosophical
arguments the program considers tight — but explicitly *not*
derivations. They earn their keep only if Tiers 1–3 succeed in making
Axiom I do real technical work elsewhere; if Tier 1–3 fail, the
dissolutions revert to interesting-but-unmotivated philosophy in the
Schopenhauer / Whitehead / Madhyamaka tradition. The framework's
honest disposition is to treat #14–#16 as *consequences of taking the
axioms seriously*, not as independent achievements.

## 6. The metaphysics-as-fixed reading

Per the user clarification (`ORIGINAL_PROMPT.md` top): the metaphysics
in §2 is *fixed*. The axioms in §1 are a formalization attempt and
can be adjusted if they prove inadequate. The program's working
discipline is therefore: when the bare axioms cannot derive a Tier
1–3 target, the move is to *strengthen / refine* the axioms while
preserving the philosophical commitments — perspective-with-wanting
as existence, anti-Dennett libertarian agency, anti-Goff
Russellian-monism-extended, market-clearing of wants, Heraclitean
persistence, anti-substantialism about selves and things.

The R6/R7 strengthenings are an example of this in practice. The bare
`HasConnectedAgency` was found to be too weak (convex state spaces
make affine interpolation cheap; the substantive content is the
*availability set*); `StrictConnectedAgency` is the refined version
that does the work, and the n=2 Birkhoff disconnect (a) is the
verified fruit. The `PatternStableWantable` refinement (b)
catalogued in `HARDY_A2_AS_PARSIMONY.md` is a parallel example
targeting Hardy Axiom 2. The `MultiSectorWantable` refinement (c)
sketched in `TIER3_DARK_MATTER.md` is another, targeting the dark
matter qualitative prediction.

If the current axiom formulation runs out of room — if R6/R7 do not
deliver the quantum reconstruction, if S3 cannot be formalized, if no
strengthening selects the SM gauge group — the move is *not* to
abandon the metaphysical commitments but to refine the axioms
further. The fixed point is the philosophical commitments in §2 of
`ORIGINAL_PROMPT.md`. The Lean encoding is provisional. The program
will know it has failed only when no refinement of the axioms,
preserving the metaphysics, can do the technical work — and that
verdict, too, would be a result.

## Verified results (no `sorry`)

### Ontology & structure

- **F.O1** `Wantable` involution structure; `Meeting` swap involution;
  `Perspective`/`Existent` as types. (`Ontology.lean`)
- **F.O2** `PTrans` is a verified `Group` instance: identity,
  composition, inverses, all laws including `inv_mul_cancel`.
  (`Transformations.lean`)
- **F.O3** `PTrans` acts functorially on `Meeting`.
  (`Transformations.lean`)
- **F.O4** Disjoint-union `Wantable`; structural no-cross-system
  meetings (`Meeting.sum_no_cross`). (`Composition.lean`)
- **F.O5** Component-wise `PTrans` on disjoint unions.
  (`Composition.lean`)

### CHSH / Tsirelson bridge

- **F.C1** `bound_realist`: in a commutative ordered *-algebra over ℝ,
  the CHSH expression is ≤ 2. (`CHSH.lean` via Mathlib's
  `CHSH_inequality_of_comm`.)
- **F.C2** `bound_perspectival`: in a general ordered *-algebra over ℝ,
  the CHSH expression is ≤ 2√2. (`CHSH.lean` via Mathlib's
  `tsirelson_inequality`.)
- **F.C3** Identification of the philosophical hinge: commutativity ↔
  observer-independent joint ledger of facts. Rejecting the latter
  forces the Tsirelson bound.

### No-cloning

- **F.N1** `cross_terms_vanish`: a linear cloner forces the cross
  terms `v₁⊗v₂ + v₂⊗v₁` to be zero. (`NoCloning.lean`)
- **F.N2** `no_cloning`: contradicted by any bilinear form `B` with
  `B v₁ v₂ + B v₂ v₁ ≠ 0`. (`NoCloning.lean`)
- **F.N3** `outerForm`: outer product of two functionals as a bilinear
  form. (`Distinguish.lean`)
- **F.N4** `no_cloning_of_distinguishable`: full operational chain —
  if two states in `S` are perfectly distinguishable by some effect,
  no linear cloner can exist on `S`. (`Distinguish.lean`)

### GPT framework and Hardy axioms

- **F.G1** GPT data structure (`GPT.lean`); classical n-outcome
  instance fully constructed (`Classical.lean`).
- **F.G2** `axiom1_holds`: Hardy Axiom 1 (Probabilities) is
  DERIVABLE and machine-verified. (`Hardy.lean`)
- **F.G3** Vertices of the n-simplex as concrete pure states with
  coordinate-projection witnesses. (`Classical.lean`)
- **F.G4** `vertex_linear_independent`: concrete classical instance
  of the abstract `perfect_distinguishable_imp_linear_independent`.

### Distinguishability ↔ linear-algebraic structure

- **F.D1** `distinguishable_ne`: distinguishable ⇒ unequal.
- **F.D2** `state_ne_zero`: states are nonzero.
- **F.D3** `distinguishable_imp_linear_independent`: pairwise
  distinguishability ⇒ linear independence.
- **F.D4** `linear_dependent_states_eq`: converse — linearly
  dependent states are equal. Together with D3, gives:
  *in a GPT, two states are linearly independent iff they are unequal*.
- **F.D5** `perfect_distinguishable_imp_linear_independent`: a finite
  family of states with a Kronecker effect family is linearly
  independent.
- **F.D6** `operational_dim_le_state_dim`: in finite-dim GPT,
  N perfectly distinguishable states ⇒ state space has dimension ≥ N.

### Libertarian agency → Hardy Axiom 5

- **F.A1** `HasConnectedAgency`: formalization of the libertarian-
  agency postulate as a Lean class.
- **F.A2** `continuous_path_of_reachable`: continuous path between
  reachable states. (`Continuity.lean`)
- **F.A3** `hardy_axiom5_of_agency`: from agency + reachability,
  recover Hardy Axiom 5 in concrete form (continuous path of linear
  maps from identity to transformation realizing the reachability).
- **F.A4** `hardy_axiom5_pure_states`: pure-state restriction.
- **F.A5** `hardy_axiom5_transitive`: full Hardy Axiom 5 from
  agency + transitivity on pure states.

## Argued (prose) — presumed wrong until verified

- **A.H1** Hardy Axioms 2, 3, 4 categorizations (auxiliary, derivable,
  auxiliary respectively) — prose only.
- **A.P1** The Quine–Rovelli parallel (semantic ↔ physical ontological
  relativity) — philosophical, not derivational.
- **A.P2** Hard-problem dissolution; Λ-as-category-error; partial
  panexperientialism — interpretive moves in `LINEAGE.md` and
  `PREDICTIONS.md`.

## Open (not attempted, or stuck)

- **O1** Deriving the *-algebra picture from I–IV. The CHSH bridge
  imports it.
- **O2** Deriving complex (vs real/quaternionic) Hilbert space.
- **O3** Deriving the multi-sector dark-matter prediction at
  *quantitative* level. Qualitative form is argued in `PREDICTIONS.md`.
- **O4** Cosmological constant value, fine-tuning forcing — likely
  not achievable from these axioms alone.
- **O5** Gauge group U(1)×SU(2)×SU(3); three fermion generations.
  Open in any axiomatic framework.
- **~~O6~~** ✓ **CLOSED.** Lin-indep wrapper for `no_cloning` is
  now `no_cloning_of_linear_independent` in `NoCloning.lean`. The
  standard formulation (linear independence ⇒ no cloner) is verified
  via dual-functional extraction.

## The metaphysical→operational bridge (significant progress)

The `WantableGPT.lean` module formalizes a bridge between the two
structural levels. **The bridge is no longer just a partial action —
it's a verified injective MonoidHom.**

Specifically:

  ✓ Given a finite Wantable W, `gpt W` constructs a full GPT.
  ✓ `complementAction W` is a verified linear involution on the
    state space.
  ✓ `complementTransform`: the complement-action lifts to a full
    GPT.Transform automorphism.
  ✓ `fromPTrans φ`: every PTrans (metaphysical transformation)
    induces a GPT.Transform (operational transformation).
  ✓ `fromPTransHom`: the lifted map PTrans W → (V W →ₗ V W) is a
    Mathlib MonoidHom (identity preserved, multiplication preserved).
  ✓ `fromPTransHom_injective`: the MonoidHom is injective; distinct
    metaphysical transformations give distinct operational ones.

Together these show: **the metaphysical group PTrans W is faithfully
embedded in the operational monoid of linear maps on the state space.**
The metaphysical structure is not just *connected to* the operational
structure but *fully recoverable from it* via the injection.

This closes a substantial portion of the framework's central
technical claim. The remaining gap: showing the operational structure
*uniquely determines* the choice of GPT (rather than admitting many
GPTs consistent with a given Wantable), which is the OPEN question
about determinism vs. permissiveness of the bridge.

## The framework's two levels — and the gap between them (qualified)

The codebase has *two structurally distinct levels* that the framework
claims should be unified:

**Metaphysical level** (`Ontology`, `Transformations`, `Composition`).
Types describing perspective, wanting, meeting. Group-theoretic
transformation structure. Carrier: `Wantable W` for some `W`.

**Operational level** (`GPT`, `Hardy`, `Distinguish`, `Continuity`,
`Classical`, `NoCloning`, `NoBroadcasting`). Probabilistic structure
with convex state spaces, linear algebra, effects. Carrier: `GPT V`
for a real vector space `V`.

These two levels are *independently coherent* — each is internally
consistent and has its own verified theorems. They share the
`Ontology` foundation (the `Wantable` axioms motivate the operational
notions in prose), and the CHSH module imports both Mathlib's
operator-algebra side and our `Wantable`-derived `BinaryObservable`,
but the **bridge in the strong sense** — showing that the operational
structure *emerges* from the metaphysical — is not formalized.

What would such a bridge look like? A construction that, given a
`Wantable W` (possibly with additional postulates), *produces* a
concrete `GPT V` whose states correspond to some natural notion of
"perspective" on `W`, whose effects come from `W`'s complement
structure, etc. This is the framework's central technical claim
(Axiom IV: matter is patterning of perspectival transformations);
formalizing it is the natural Tier 1+ research target.

This gap is the framework's honest structural limitation. Both levels
do real work; they don't yet *unify*. ROADMAP R6 and R7 are the path
toward closing this gap.

### Bridge now built; bridge now also delimited

**Update.** `WantableGPT` (verified) provides a concrete bridge: for
any finite Wantable `W`, the construction `WantableGPT.gpt W` is a
machine-verified GPT instance whose vertices, distinguishability set,
and PTrans-induced automorphisms are all formally derived. So the
"strong-bridge" question has *partial* affirmative resolution.

But the same module now also contains a **triple no-go theorem**
(`wantableGPT_classical_dichotomy`): the bridge always lands on
classical structure — `N = K = |W|`, with `K = K_A · K_B` for product
composition and `K = K_A + K_B` for sum composition; and the three
canonical non-classical Hardy signatures (quantum `K=N²`, real-QM
`2K=N(N+1)`, quaternionic-QM `K=N(2N-1)`) are *each* formally ruled
out for `|W| ≥ 2`. So the bridge exists, but it cannot, by itself,
deliver any non-classical structure.

The ROADMAP R6/R7 program — strengthening the agency postulate to
force quantum-like path-connectedness — is the next bet *precisely
because* the bare ontology has been shown to be insufficient.
Furthermore, `path_via_affineLine` reveals that "path-connectedness"
in `HasConnectedAgency` is cheap (always satisfiable for topological
V); the substantive content of R6 is the *availability set* (which
transformations are admissible), not the connectedness itself.

**Reachable as equivalence relation.** Under `ClosedAgency` (closure
under composition) plus per-element inverse availability, the
`Reachable` relation is formally an `Equivalence`
(`Reachable.equivalence`). This formally characterizes when the
"dynamically connected" partition of state space is well-behaved. The
underlying observation: composition + inverse + identity make the
available set a group, and orbits under a group action are
equivalence classes. The R6 program is to identify which
*physically meaningful* condition justifies inverse availability,
since `Reversible` itself doesn't currently encode bijectivity (see
`StrictReversible` for a refinement that does).

## Structural deflations (clarifying)

Two clarifying deflations have been formally proven:

- `Meeting W ≃ W` via `mk_fromSide` (Ontology). A "meeting" is not
  a richer thing than a "want"; the two are in canonical bijection.
- `PTrans W` is *exactly* the centralizer of the `complement`
  involution inside `Equiv.Perm W` (Transformations). The PTrans
  group is not a novel algebraic structure beyond Mathlib's
  permutation group; it is the standard Z/2-equivariant subgroup.

These are not weaknesses but clarifications: the framework's
vocabulary picks out a specific, well-understood mathematical object.
The interesting research question is whether *additional* postulates
on top of I–IV can pick out non-classical mathematics; the bare
ontology, as the no-go and the deflations together establish, cannot.

## Continuous setting (path toward R6/R7)

The `ContinuousWantable` / `ContinuousPTrans` refinement (Examples.lean,
verified) packages Wantable on a topological space with continuous
complement, and the corresponding PTrans whose `toFun` is continuous.

A concrete observation in this setting: `Wantable ℝ` (with
`complement := Neg.neg`) admits not just `{1, complement}` but also
all scaling maps `x ↦ a*x` for `a ≠ 0` as elements of `PTrans ℝ`
(verified: `scaleByPTrans`). The PTrans group on ℝ contains
`ℝˣ` (the multiplicative group of nonzero reals — a 1-dimensional Lie
group). This is the first concrete realization in the codebase that
*infinite / topological Wantables naturally support Lie-group
structure on PTrans*, where finite Wantables only support finite
(discrete) subgroup structure.

This is the natural setting in which to attempt R6/R7 — strengthening
agency to force path-connectedness — because path-connectedness
is automatic in continuous Lie groups, whereas it must be added as
a postulate over finite/discrete carriers.

## Clarifications and limitations

### L1. Scope of `no_cloning`

`no_cloning` and `no_cloning_of_distinguishable` require the set `S`
to contain `v₁`, `v₂`, AND `v₁ + v₂`. For normalized state spaces
(simplices, density-matrix spaces) this is generically false:
`v₁ + v₂` has unit-functional value 2, not 1, so it's not a state.

The theorems should therefore be read as facts about **linear-algebra
cloners on the linear span of states**, not about cloners restricted
to the normalized state space. The standard quantum no-cloning
theorem (Wootters–Zurek) uses unitarity + ancilla and is a different
statement; the framework currently formalizes only the underlying
linear-algebra impossibility, which is logically weaker.

This is the kind of subtlety honest calibration is for. The Lean
result is what it is; the framework's *reading* (two-sided wanting
forbids isolation) is metaphorically apt but the literal theorem is
the pure-linearity one.

### L2. Tsirelson bound — interpretation vs. derivation

`bound_perspectival` uses `Mathlib.Algebra.Star.CHSH`'s
`tsirelson_inequality`. The mathematical content is Mathlib's; the
framework's contribution is the *identification* of which algebraic
hypothesis is the realist hinge (commutativity ↔ joint ledger). We
do not derive the *-algebra picture from I–IV; we import it.

### L3. Hardy Axiom 5 derivation — easy direction only

`hardy_axiom5_of_agency` proves: from agency (formalized as path-
connectedness of the transformation group), Hardy Axiom 5 follows
by direct construction. The HARD direction — that libertarian
agency forces path-connectedness, not mere richness — is not in this
codebase. The agency postulate `HasConnectedAgency` is the input,
not a theorem.

## Meta-assessment

**What is technically distinctive about the framework, given the
verified results.** Four contributions, each (a) machine-verified:

1. *Agency → Hardy Axiom 5*: the F.A1–F.A5 chain. Framework's
   philosophical commitment to libertarian agency, formalized as
   path-connectedness of the reversible-transformation group, yields
   Axiom 5 by direct construction. Other reconstructions take Axiom 5
   as input.
2. *WantableGPT bridge as injective MonoidHom*: the framework's
   metaphysical-to-operational claim is verified faithful;
   metaphysical PTrans is recoverable from operational structure.
3. *R6 Birkhoff disconnect for Classical n=2*
   (`classical_n2_strict_reversible_path_id_swap_empty`): the first
   framework-distinctive *discreteness* theorem the program has
   produced; no other GPT reconstruction has formalized this
   classical-vs-quantum separator in Lean. This session's flagship
   result.
4. *Algebraic R7 scaffolding* (`ClosedAgency`, `StrictReversible`,
   `Reachable.equivalence`, central `complementSubgroup`): the
   prerequisite infrastructure for the positive (quantum) complement
   of the R6 disconnect.

**What is technically NOT distinctive.** The CHSH/Tsirelson bridge,
no-cloning, the dimension inequality `N ≤ K` (F.D6) are
framework-agnostic in their proofs — any reconstruction can claim
them. The framework provides interpretation (commutativity ↔ joint
ledger; two-sided wanting ↔ no-cloning; perfect distinguishability ↔
linear independence), not unique proof power.

**The honest research position.** The bare ontology cannot support
quantum structure (`wantableGPT_classical_dichotomy` is the verified
obstruction). Therefore the framework must *strengthen* its axioms to
do quantum work. The R6/R7 strengthenings are the program's specific
bet on *how* to strengthen. The n=2 disconnect (a) shows that the
strengthening genuinely separates classical from non-classical at
the agency-postulate level. The positive complement — that quantum
reversibles `U(N)` *do* satisfy the strengthening — is the next
milestone, (d) speculative. If it closes, the framework earns its
keep on Tier 1 #5 (Hilbert-space derivation); if it doesn't, the
axioms need further refinement per the user clarification, and the
fixed point remains the philosophical commitments in §2 of
`ORIGINAL_PROMPT.md`.

**The honest research bottlenecks going forward** (in dependency
order):

1. Close R6 positively (R7): demonstrate that some quantum-like GPT
   realizes `StrictConnectedAgency` non-trivially via the connected
   Lie group `U(N)`. The largest live bet.
2. Build `gptTensor` and prove local tomography (S1): excludes qQM
   structurally as opposed to merely empirically. Tractable Lean
   target.
3. Formalize the agency–observable duality (S3): the philosophical
   step that distinguishes cQM from rQM at the
   "antisymmetric-generator-as-observable" level. Currently
   prose-only; (c) plausible if R7 lands.
4. Formalize `MultiSectorWantable` (Tier 3 #11 qualitative
   upgrade): converts the multi-sector dark matter prediction from
   **S** to **D (qualitative)** per `TIER3_DARK_MATTER.md`. One
   focused session of work.
5. Formalize `PatternStableWantable` (Hardy A2 candidate refinement):
   the smallest formal handle on A2 = pattern-parsimony.

**Until the positive complement of the R6 disconnect lands, the
program has earned only the negative side**: a class of theories
(classical) is provably excluded from supporting strict agency; the
class of theories that *do* support it has not yet been
characterized. The verified-results scoreboard is real, and the
philosophically distinctive predictions remain mostly in the
Suggested/Speculative columns (see `PREDICTIONS.md`). The
metaphysics is not negotiable; the axioms are a formalization
attempt and may be sharpened. The program's discipline — every
non-trivial derivation in Lean, every claim tagged with calibration,
every reframing documented as a scoping note — is what gives this
sharpening room to fail honestly. That is the honest current state,
the working target, and the framework's distinctive bet.
