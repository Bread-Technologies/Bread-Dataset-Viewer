# Tier 2 Scoping Note — The Standard Model Gauge Group as a Coherence Requirement

This is a research scoping note for **Tier 2 target #6** of the
perspectival-physics program: deriving (or, more honestly, *reframing*
the question of) the Standard Model gauge group `U(1)_Y × SU(2)_L × SU(3)_c`
as a coherence requirement on local perspectival transformations. It is
written in the spirit of `TIER2_ATTEMPT.md` — survey, calibrate, mark
the gap. It commits no result. It identifies the one next step that
might be Lean-actionable.

## 1. Target, stated precisely

The Standard Model takes three independent Lie groups as input:
- `U(1)_Y` — weak hypercharge, abelian,
- `SU(2)_L` — weak isospin, acting only on left-chiral fermions,
- `SU(3)_c` — colour, exact.

After electroweak symmetry breaking the unbroken subgroup is
`U(1)_em × SU(3)_c`. The chirality of `SU(2)_L` and the specific
hypercharge assignments are empirical input; nothing in the standard
formulation explains *why these three factors* and not, say, `SU(5)`,
`SO(10)`, `Sp(2)×SU(4)`, or a single `E_8`.

**The framework's target version of the question.** Under axiom IV
("all apparent particulars are stable patterns within the structure of
meetings; the mathematical structure of any such patterning is group-
theoretic"), the gauge group is supposed to be the *local* symmetry of
perspectival transformations. The target is to argue that
`U(1) × SU(2) × SU(3)` is the unique minimal coherence-preserving
choice of *local* `PTrans` structure on a Wantable that has already
been refined to support continuous, smooth perspectival dynamics.

**No path to this is currently known**, in this framework or any
other. Honesty discipline (per the original prompt, §8: "scope creep
— 'setting for X' is not 'derivation of X'") requires that this note
identify reframings and partial steps, not promise a derivation.

## 2. What the existing formalism can already do

The Lean codebase, as of this note, has the following load-bearing
pieces relevant to a gauge-group story:

- **`Perspectival.Transformations.PTrans W`** — the group of
  self-bijections of a Wantable `W` commuting with `complement`. Verified
  Lean `Group` instance. `mem_range_toEquivPermHom_iff` identifies
  `PTrans W` as exactly the centralizer of `complement` inside
  `Equiv.Perm W`. This is the framework's group-theoretic carrier of
  axiom IV.

- **`Perspectival.Continuity.HasConnectedAgency`** — the postulate
  that the set of reversible perspectival transformations is path-
  connected and contains the identity. Used to derive Hardy Axiom 5
  in `hardy_axiom5_of_agency`, `hardy_axiom5_transitive`. This is the
  framework's libertarian-agency commitment in formal dress.

- **`Examples.lean :: ContinuousWantable, ContinuousPTrans,
  scaleByPTrans, scaleHom_injective`** — a worked continuous case
  (`W = ℝ`, `complement = Neg.neg`) where `ℝˣ` embeds as a 1-dimensional
  Lie subgroup of `PTrans ℝ`. Translations are excluded by Z/2-equivariance.

- **`wantableGPT_is_classical` + triple no-go** — verified evidence
  that the *bare* axiomatic content (Wantable → GPT) yields only the
  classical simplex. Any non-classical (hence any gauge) structure
  must come from the continuity/agency refinement, not from the discrete
  axioms alone.

The gauge story therefore lives downstream of `HasConnectedAgency`
and downstream of the continuous-Wantable infrastructure, not at the
level of `Wantable` itself.

## 3. The gauge-as-connection analogy

The cognitive scaffolding in `ORIGINAL_PROMPT.md` §3 (and the Faizan
2022 blog post) frames gauge bosons as connections in exactly the way
Christoffel symbols are: not *fundamental* objects, but the price of
comparing perspectives at different points. The picture:

- A *global* symmetry acts the same at every spacetime point. A
  *local* (gauge) symmetry can act differently at different points.
- Promoting a global symmetry to local breaks naive derivatives — the
  derivative compares values at infinitesimally separated points, and
  if the symmetry transformation differs between them, the comparison
  is frame-relative.
- A *connection* (gauge field) is exactly the apparatus that restores
  meaningful comparison: it tells you how to transport a perspective
  from one point to its neighbour so that derivatives become covariant.
- Connection one-forms `A_μ` live on a principal `G`-bundle over
  spacetime; their curvature `F = dA + A∧A` is the gauge field
  strength; Yang–Mills dynamics is `Tr(F∧⋆F)`.

In framework vocabulary, the analogy reads: **a global `PTrans` group
acts uniformly across all meetings; a local `PTrans` group acts
differently at each meeting; coherence — the possibility of relating
adjacent perspectives — *requires* a connection-like compensator
exactly when the action is local.** Gauge fields are then the
framework's fictitious forces, in the precise sense Einstein gave the
phrase: artifacts of choosing perspectives independently at each point.

This is a *reframing*, not a derivation. It buys the framework the
right to say "gauge fields are not extra ontology; they are the
transformation cost of local perspectival freedom." It does **not**
buy us `U(1)×SU(2)×SU(3)`.

## 4. The gap between PTrans and a Standard Model Lie group

The honest accounting:

| What we have                                          | What we need                                                  |
|-------------------------------------------------------|---------------------------------------------------------------|
| `PTrans W` — Z/2-equivariant `Equiv.Perm W`           | A *Lie* group with `dim ≥ 1 + 3 + 8 = 12`                     |
| `scaleHom : ℝˣ ↪ PTrans ℝ` (abelian, 1-dim)           | A *non-abelian* compact factor (`SU(2)`, `SU(3)`)             |
| Global PTrans on a single Wantable                    | A *local* PTrans, i.e. a `PTrans`-bundle over a base manifold |
| `HasConnectedAgency` (path-connectedness)             | Smooth manifold + Lie-group structure on the connected component |
| Discrete or topological group                         | Compact, semisimple ⊕ abelian factor structure               |
| `complement` involution (Z/2)                          | A larger internal symmetry providing colour and isospin       |

The structural gap divides into three sub-gaps:

(a) **From finite permutation to continuous Lie group.** R6/R7 of
`ROADMAP.md` is precisely this. Forcing path-connectedness from
agency (R6) gets us a topological group; smoothness (R7) gets us a Lie
group. Neither is verified; R6 has a partial closure result (`ClosedAgency`,
`Reachable.trans`) but the move from closure to density is open.

(b) **From a global group to a connection on a principal bundle.**
There is no infrastructure in the codebase for principal bundles,
fibre bundles, or connection one-forms. Mathlib has partial bundle
support; smooth principal bundles with structure group `G` and
connection forms are not, to the best of present knowledge, in a
state suitable for the level of formalization the rest of the
program demands.

(c) **From "a Lie group" to *this specific* Lie group.** Even granting
(a) and (b), no argument is known that selects `U(1)×SU(2)×SU(3)` over
the continuum of compact semisimple ⊕ abelian alternatives. Candidate
narrowings — anomaly cancellation, Connes-Chamseddine spectral
triples, division-algebra constructions (`R⊗C⊗H⊗O`), grand unification
embeddings — are all consistent with the framework but none follows
*from* it.

## 5. The R6/R7 strengthening sketch

The natural lift of the existing roadmap toward gauge structure runs:

1. **R6 (path-connectedness from agency).** Strengthen
   `HasConnectedAgency` to a density condition: "at every instant
   the set of available reversible perspectival transformations
   has no smallest non-trivial element." On a sufficiently rich
   topological Wantable, this would force the reversible-transformation
   set to be the path-component of the identity in `PTrans W` — a
   *topological group* rather than a discrete one.

2. **R7 (Lie-group refinement).** Add a smoothness postulate on
   the action of `PTrans W` on the state space — the framework's
   reading of "the choice at each instant varies smoothly with
   neighbouring instants." Combined with R6 and the standard
   Cartan / Mostow theorems on locally compact connected groups
   acting smoothly on manifolds, this would deliver a Lie-group
   structure on the connected identity component.

3. **Localisation.** Promote `PTrans W` to a *bundle* of groups
   over a base — the framework's reading is that *meetings happen at
   places*, so axiom III's `Meeting W` already carries an implicit
   base-space dependence we have not yet axiomatised. A sheaf or
   bundle of Wantables, with `PTrans` acting fibrewise, is the
   natural categorial home.

4. **Connection 1-form.** Whenever the fibrewise group action is
   *local* (varies across the base), a `g`-valued connection 1-form
   `A ∈ Ω¹(M, 𝔤)` is the unique-up-to-gauge object compensating
   the local action so that meetings between spatially separated
   wants remain comparable. Curvature `F = dA + A∧A`. Yang–Mills
   action emerges as the natural quadratic invariant.

5. **Selection of `G`.** *Unsolved.* Even granting steps 1–4, the
   framework alone does not pick the three factors. The most
   honest framing is: the framework predicts that gauge groups
   are *compact, semisimple-plus-abelian Lie groups*, with the
   specific factors as empirical input mediated by Wantable
   structure not yet formalised.

## 6. Catalog — in scope, gap, unreachable

- **In scope (verified or near-verified).** `PTrans` as a Lean
  group; centralizer-of-complement identification; continuous
  Wantable examples; `scaleHom_injective` as a 1-dim Lie embedding;
  `HasConnectedAgency` and Hardy Axiom 5 derivation; the no-go
  results that pin down where the gauge story *cannot* come from.

- **Gap (work that could plausibly be done in this program).**
  R6 strengthening to a density / no-smallest-step formulation;
  R7 Lie-group refinement; statement of axiom III as a *local*
  rather than *global* structure (sheaf/bundle of Wantables); a
  Lean development of `g`-valued connections on a trivial principal
  bundle for some baby `G` (e.g. `U(1)`).

- **Currently unreachable.** Selection of the specific factors
  `U(1)×SU(2)×SU(3)`; derivation of fermion representations
  (`16` of `SO(10)`, chirality, hypercharge assignments); the
  three-generations count (see `TIER2_ATTEMPT.md`); EWSB and the
  Higgs sector. These remain empirical input under any known
  framework.

## 7. The one most tractable Lean-verifiable next step

**Proposal.** Lean-formalise the toy statement:

> Let `W` be a `ContinuousWantable` with `W = ℝ`. The identity
> component of `PTrans W` (under a suitable topology) contains a
> *smooth* one-parameter subgroup isomorphic to `(ℝ, +)`, realising
> the abelian Lie algebra `u(1)` of the simplest local symmetry. A
> `u(1)`-valued connection one-form on the trivial bundle `ℝ×U(1) → ℝ`
> compensates a position-dependent rescaling so that comparison of
> wants at separated points is well-defined.

This is the smallest non-vacuous instance of "local perspectival
transformation forces a connection." It uses only the abelian case
(no Lie-algebra non-commutativity), reuses the existing
`scaleHom_injective` infrastructure, and connects to a `u(1)` gauge
field — the framework's own analogue of electromagnetism.

What it would *not* establish: anything about `SU(2)` or `SU(3)`,
anything about the specific factor structure, anything about
spacetime as base. What it *would* establish: the framework can
articulate the gauge-as-connection move at the formally verified
level on its smallest non-trivial example. That is a real prerequisite
for any honest Tier 2 progress and is achievable in the existing
Mathlib + framework infrastructure without speculative inputs.

## 8. Cross-references

- **Wigner 1939** — "On Unitary Representations of the Inhomogeneous
  Lorentz Group." A *particle* is an irreducible unitary representation
  of the symmetry group of spacetime. In the framework's reading,
  particles are stable patterns under PTrans — exactly Wigner-style
  irreducible representations, once `PTrans` has been refined to a
  Lie group.

- **Yang–Mills 1954.** Gauge invariance with a non-abelian group;
  curvature `F = dA + A∧A`; the canonical action `Tr(F∧⋆F)`. The
  framework would re-derive (not just import) this if it could
  motivate `dA + A∧A` as the obstruction to coherently composing
  local PTrans moves.

- **Atiyah, *Geometry of Yang-Mills Fields* (1979)**, and Kobayashi–
  Nomizu, *Foundations of Differential Geometry* I–II. Standard
  references for the principal-bundle / connection-1-form picture
  the framework is reaching for.

- **Connes–Chamseddine spectral action.** A non-framework but
  ontologically congenial attempt to derive `U(1)×SU(2)×SU(3)` from
  a noncommutative-geometric structure. Worth comparing as a sibling
  reframing; its choice of almost-commutative geometry is a free
  input analogous to our choice of Wantable.

- **TIER2_ATTEMPT.md** — the parallel three-generations negative
  result. The two notes together delimit the framework's Tier 2
  reach: neither the gauge group nor the generation count is in
  scope under axioms I–IV alone.

## 9. Disposition

The work this note scopes is *modest*. It commits the program to one
Lean-verifiable baby step (the `u(1)` toy) and to documenting the
two unforced inputs (which Lie group, which representations) as
honest empirical input rather than as forthcoming derivations. If a
future result selects the three SM factors from coherence alone, this
note will look quaint; until then, the program's contribution to Tier 2
target #6 is to *reframe* the question and to clear the formal ground.
Anything more would be the kind of scope creep §8 of the original
prompt forbids.
