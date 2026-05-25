# Glossary

Definitions and pointers for the framework's terminology. Each entry
links to where the formal Lean definition lives.

## Metaphysical (Wantable-level) terms

**Wantable** — A type `W` equipped with an involutive `complement`
operation: `∀ w, complement (complement w) = w`. Encodes Axiom II
("wants are intrinsically relational"). Lean: `Ontology.lean ::
Wantable`.

**Want** — An element of a Wantable. The "directedness" of Axiom I.

**Existent** — A wrapper structure carrying a single `want`. Encodes
Axiom I ("to exist is to instantiate a perspective with directedness").
Lean: `Ontology.lean :: Existent`.

**Meeting** — A pair `(side₁, side₂)` of complementary wants:
`complement side₁ = side₂`. Encodes Axiom III ("reality is the
structure of meetings"). Lean: `Ontology.lean :: Meeting`.

**Reality** — A collection of meetings (here: `Meeting W → Prop`).
Lean: `Ontology.lean :: Reality`.

**Pattern** — Placeholder for Axiom IV's "stable patterns." Currently
abstract pending a dynamical refinement. Lean: `Ontology.lean ::
Pattern`.

**PTrans** — A *perspectival transformation*: a self-bijection of `W`
commuting with `complement`. PTrans W forms a Group (verified). Lean:
`Transformations.lean :: PTrans`. The `Wantable.complement` itself,
packaged as a PTrans, lives at `PTrans.complement` and is verified to
be an involution (`PTrans.complement_sq`).

## Operational (GPT-level) terms

**GPT** — A *generalized probabilistic theory*: an ℝ-vector space `V`
with a unit functional, convex state set, convex effect set, and
[0,1]-valued probabilities. Lean: `GPT.lean :: GPT`.

**State** — An element of `G.states` for some GPT `G`. Probability
distribution / density matrix in the framework's preferred reading.

**Effect** — A linear functional in `G.effects`, taking values in
[0,1] on states.

**Transform** — A linear map between GPTs preserving the state set
and the unit. Self-transforms of `G` form a Monoid under composition.
Lean: `GPT.lean :: Transform`, `Transform.id`, `Transform.comp`.

**Distinguishable** — Two states `ρ₁, ρ₂` are distinguishable if some
effect `e` has `e ρ₁ = 1, e ρ₂ = 0`. Lean: `Hardy.lean ::
Distinguishable`.

**Perfect distinguishability witness** — A family of effects
`e : ι → V →ₗ ℝ` with `e i (ρ j) = δᵢⱼ`. Implies the family `ρ` is
linearly independent. Lean: `Distinguish.lean :: PerfectWitness`.

## Bridge terms (Wantable → GPT)

**WantableGPT** — Given a finite Wantable `W`, the GPT on `W → ℝ`
whose states are probability distributions on outcomes in `W`. Lean:
`WantableGPT.lean :: gpt`.

**complementAction** — The linear involution on `V W` induced by
`Wantable.complement`. Lean: `WantableGPT.lean :: complementAction`.

**complementTransform** — `complementAction` packaged as a GPT
self-transformation of `gpt W`. Lean: `WantableGPT.lean ::
complementTransform`.

**fromPTrans** — Lifts a `PTrans W` to a GPT self-transformation of
`gpt W`. Lean: `WantableGPT.lean :: fromPTrans`.

**fromPTransHom** / **fromPTransTransformHom** — `fromPTrans`
packaged as a Mathlib MonoidHom into the LinearMap monoid (resp. the
Transform monoid). `fromPTransHom_injective`: the homomorphism is
injective. Lean: `WantableGPT.lean`.

## CHSH terms

**BinaryObservable** — Self-adjoint involution in a *-ring; a ±1
observable in the QM dictionary. Lean: `CHSH.lean ::
BinaryObservable`.

**SpacelikePair** — Four binary observables A₀, A₁, B₀, B₁ with
cross-commutation Aᵢ Bⱼ = Bⱼ Aᵢ. The CHSH setup. Lean: `CHSH.lean ::
SpacelikePair`.

**CHSH expression** — `A₀·B₀ + A₀·B₁ + A₁·B₀ - A₁·B₁`. Bounded by
2 in commutative case, 2√2 in general. Lean: `CHSH.lean ::
SpacelikePair.chshExpr`.

## Agency / continuity terms

**Reversible** — A continuous linear self-equivalence of `V`
preserving the GPT's state and unit. Lean: `Continuity.lean ::
Reversible`.

**HasConnectedAgency** — The libertarian-agency postulate
formalized: the set of available reversible transformations contains
identity and is path-connected. Lean: `Continuity.lean ::
HasConnectedAgency`.

**Reachable** — `ρ₂` is reachable from `ρ₁` if some available
reversible sends `ρ₁` to `ρ₂`. Lean: `Continuity.lean :: Reachable`.

**PureState** — An extreme point of the GPT's state set. Lean:
`Continuity.lean :: PureState`.

## Hardy's axioms

**Axiom 1 (Probabilities)** — Probabilities in [0,1] for all
state/effect pairs. DERIVABLE; formally proven. Lean:
`Hardy.lean :: axiom1_holds`.

**Axiom 2 (Simplicity)** — K minimal. AUXILIARY; cross-theory.

**Axiom 3 (Subspaces)** — A sub-state-space gives a sub-GPT.
DERIVABLE (weak form); formally proven. Lean: `Hardy.lean ::
axiom3_holds`.

**Axiom 4 (Composite systems)** — `N_AB = N_A · N_B`. AUXILIARY;
multiplicative beyond disjoint-union.

**Axiom 5 (Continuity)** — Continuous reversible transformations
between pure states. DERIVABLE from libertarian agency; formally
proven via the agency postulate. Lean: `Continuity.lean ::
hardy_axiom5_transitive`.

## No-go theorems

**No-cloning** — No linear map `C : V → V ⊗ V` exists with
`C v = v ⊗ v` for two linearly independent vectors (and their sum).
Lean: `NoCloning.lean :: no_cloning_of_linear_independent`.

**No-cross-system meetings** — In a disjoint-union Wantable, no
meeting has sides in different summands. Lean: `Composition.lean ::
Meeting.sum_no_cross`. (Structural form of no-signaling.)

**Tsirelson bound** — Per the framework: 2√2 in the noncommutative
*-algebra case (rejection of observer-independent ledger). Lean:
`CHSH.lean :: bound_perspectival` via Mathlib.

**No-go: WantableGPT is always classical** — For any finite Wantable
`W`, the bridge `WantableGPT.gpt W` produces a GPT with N = K = |W|,
i.e., the *classical signature*. Quantum structure cannot be derived
from the bare Wantable axioms; it requires additional postulates.
Lean: `WantableGPT.lean :: wantableGPT_is_classical`.

**Structural deflation: PTrans is the complement-centralizer** —
For any Wantable `W`, `PTrans W` is in bijection (and group-iso) with
the centralizer of `Wantable.complement` (viewed as a permutation) in
`Equiv.Perm W`. The framework's "perspectival transformations" are
exactly the Z/2-equivariant permutations of the outcome set. Lean:
`Transformations.lean :: mem_range_toEquivPermHom_iff`.

## Entropy / coarse-graining (per addendum)

Per `ORIGINAL_PROMPT_V2_ADDENDUM_ENTROPY.md`, the framework adopts
anti-realism about entropy. The following terminology is load-bearing:

**Coarse-graining** — an observer's count of distinguishable
macrostates over some space of microstates. The coarse-graining is
structurally grounded in real multiplicities (real subjectivism),
not arbitrary.

**Entropy (framework reading)** — the observer-relative
coarse-graining of distinguishable states; Jaynes-style subjectivist
quantity. NOT a substantial property of the universe; NOT an
observer-independent absolute. Always reference the coarse-graining
when speaking of entropy ("under this coarse-graining, X
distinguishable macrostates" is the framework-native form).

**Subjectivist (framework usage)** — perspective-relative; real
multiplicities exist; structural constraints on consistent
value-assignments are real. Not "anything goes" — that is bad
subjectivism, which nobody defends. The framework owns the word;
realist-respectability relabeling is drift.

**Many-to-one collapse** — the operation of mapping multiple
microstates to a single one. Mechanically forbidden under conservative
dynamics (Picard-Lindelöf applied to time-reversal-symmetric ODEs).
The kT ln 2 erasure cost is the mechanical price of forcing such a
collapse via nonconservative dynamics. NOT the cost of "destroying
information-substance."

**Both-halves framing** — the framework's account of the Second Law
requires both the subjectivist coarse-graining count (Jaynes) and the
mechanical impossibility of many-to-one collapse (WBT 2024).
Subjectivist where subjectivist (count); mechanical where mechanical
(cost of forcing collapse). Together they yield the Second Law as
necessary, not contingent.

## Decoherence (Seam 4) vocabulary

**Trajectory chain.** `RealityChain' P C R₁ R₂` — a finite sequence
of bracketed/actualization steps connecting Reality state R₁ to R₂.
Carries witnesses of each transition.

**Actualization count.** `tierAEventCount ch` — the number of
actualization steps in a strict chain. The "Tier A irreversible
content" of the trajectory.

**Bracketed count.** `bracketedCount ch` — the number of bracketed
(Tier B reversible-limit) steps in a strict chain.

**Trajectory complexity.** `trajectoryComplexity ch` — weighted
measure `2 * count + bracketed`. Distinguishes more chain types
than count alone.

**Coherent regime.** A chain with `actualizationCount = 0`. All
steps are bracketed; the trajectory stays in the Tier B reversible
limit.

**Pure-decoherent regime.** A chain with `bracketedCount = 0`. All
steps are actualizations; maximal Tier A irreversibility per step.

**Mixed regime.** A chain with both positive actualization count
and positive bracketed count.

**DecoherenceEquivalent.** Two chains are decoherence-equivalent
iff they have equal `tierAEventCount`. The equivalence relation
captures the framework's anti-realism: only the count is
path-independent across chains with same endpoints.

**Loop chain.** A chain `RealityChain' P C R R` with equal endpoints.
By the kernel characterization, every loop chain is coherent
(count = 0).

**Loop power.** `loopPower ch n` — the n-fold composition of a
loop chain with itself.

**Coherent kernel.** The set of chains with `tierAEventCount = 0`.
Characterized exactly by endpoint equality
(`coherent_kernel_iff_endpoints_eq`).

## Cross-references

- For per-theorem status see `STATUS.md`.
- For honest commentary on what's been earned vs. what's open, see
  `FINDINGS.md`.
- For empirical predictions, see `PREDICTIONS.md`.
- For module dependency graph, see `DEPS.md`.
- For philosophical references, see `LINEAGE.md`.
- For concrete physics questions, see `FAQ.md`.
- For next research targets, see `ROADMAP.md`.
- For the negative result on three generations, see `TIER2_ATTEMPT.md`.
