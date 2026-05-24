# Agency Hierarchy — A Stratification of the Libertarian-Agency Postulate

**Module:** `Perspectival.Continuity` (`Perspectival/Continuity.lean`).
**Companion notes:** `TIER1_5_HILBERT.md` (S1/S2/S3 strengthenings),
`TIER2_GAUGE_SCOPING.md` (R7 as Lie-group precursor to gauge structure),
`R6_GENERAL_N_SCOPING.md` (extension of the R6 disconnect from `n=2` to
general `n`).

## Why a hierarchy

`HasConnectedAgency` was introduced as the framework's formal proxy for
Axiom IV refined by the libertarian-agency commitment: at every instant
the perspective genuinely chooses, so the space of available reversible
transformations must be a *connected* set, not a discrete one. The bare
class is the weakest formal expression of that idea, and it turns out to
be too weak to pull non-classical structure out of the axioms. Each
successive class in the hierarchy below adds exactly one structural
demand that the philosophy already commits us to but the previous class
left implicit; each demand reflects a separate clause of the framework's
metaphysics (perspectival continuity, state-space respect, genuine
invertibility, group closure, smooth/Lie structure).

The hierarchy is the technical scaffolding for the framework's
classical-vs-quantum disconnect at the agency level: the strongest
versions are vacuous on classical GPTs (forcing `avail = {id}`) and
non-trivially satisfiable on quantum ones (where `U(N)` is a connected
compact Lie group).

## The six levels

### Level 1 — `HasConnectedAgency G` (Hardy A5 ingredient)

**Adds:** a designated `avail : Set (Reversible G)` containing the
identity, with the property that any two members of `avail` are
connected by a *jointly continuous family of linear maps*
`γ : unitInterval → V →ₗ[ℝ] V`. The intermediate `γ(t)` need only be
linear; it need not preserve states, preserve the unit, or be
bijective.

**Philosophical content:** Axiom IV plus the agency commitment in its
minimal form — there is a continuous availability space of reversible
choices, with no smallest non-trivial reversible move. This is the
Heraclitean / Bergsonian commitment to the continuity of becoming, but
encoded only at the endpoints.

**Already proven (Lean):** `Reachable.refl`,
`continuous_path_of_reachable`, `hardy_axiom5_of_agency`,
`hardy_axiom5_pure_states`, `hardy_axiom5_transitive`. Constructors
`trivialAgency`, `singletonAgency`, `pairAgency` (with affine
interpolation via `path_via_affineLine`) show the class is satisfiable
on any topological-vector-space GPT.

**Enables / conjectures:** Hardy Axiom 5 in concrete form.

### Level 2 — `StatePreservingAgency G` (R6 weak)

**Adds (to L1):** paths must preserve states at *every* `t`, not just
at the endpoints. Uses `StatePreservingPath` carrying
`preserves_states_along : ∀ t ρ ∈ G.states, γ t ρ ∈ G.states`.

**Philosophical content:** continuity of the *trajectory through state
space*. The intermediate moments of a reversible transition must
themselves be coherent perspectival configurations — half-finished
reversibles are not licensed.

**Already proven (Lean):** `continuous_state_preserving_path`;
`HasConnectedAgency.ofStatePreservingAgency` (forgetful instance);
constructors `StatePreservingPath.id`, `.const`, `.reverse`.

**Status caveat:** the file's R6 comment block (around line 737) flags
that this level is **trivially satisfied** for every GPT: because
`G.states` is convex, the affine interpolation `γ(t) = (1-t)R₁ + t R₂`
between any two state-preserving linear maps is itself
state-preserving. So L2 alone gives no classical-vs-quantum
discrimination; the discriminating content must come from L3.

### Level 3 — `StrongConnectedAgency G` (R6-bis)

**Adds (to L2):** paths are sequences of *Reversibles* — each `γ(t)`
must additionally preserve the unit (`preserves_unit_along`) and be
continuous as its own map (`continuous_at`). Carried by
`ReversiblePath`.

**Philosophical content:** every intermediate moment of a reversible
transition is itself a *bona fide* reversible perspectival
transformation, not merely a state-preserving linear smear. Wants
(unit) are preserved throughout, not only at the endpoints.

**Already proven (Lean):** `ReversiblePath.toStatePreservingPath`
(forgetful), `ReversiblePath.id`, `ReversiblePath.const`. The class
`StrongConnectedAgency` is defined; substantive theorems about it are
delegated to L4 (where the further bijectivity demand makes the
disconnect sharp).

### Level 4 — `StrictConnectedAgency G` (R6-tris) — **load-bearing**

**Adds (to L3):** each `γ(t)` is *bijective* (`bijective_along`).
Carried by `StrictReversiblePath`; the available set is now
`Set (StrictReversible G)`.

**Philosophical content:** genuine invertibility of every intermediate
moment. The transition is reversible all the way down — not just
information-preserving on the convex span of states, but a continuous
sweep through honest perspectival isomorphisms. This is what the
libertarian-agency commitment actually demands: each instant is a real
choice from a continuous Lie-group-like family of *invertible*
moves, not a discrete jump nor a degeneration through non-bijective
intermediates.

**Already proven (Lean):** `StrictReversiblePath.toReversiblePath`
(forgetful), `StrictReversiblePath.id`, `trivialStrictAgency`,
`trivialStrictAgency_reachable_iff`. On the classical side,
`Classical.lean` proves:

- `classical_n2_strict_reversible_path_id_swap_empty` (line 882) — the
  central disconnect: no `StrictReversiblePath` on Classical-`n=2`
  exists between `id` and `swap`.
- `R6_framework_main_classical_n2` (line 2103) — packaged form: any
  `StrictConnectedAgency` on Classical-`n=2` containing both `id` and
  `swap` is `False`.
- `R6_framework_classical_n2_avail_choice` (line 2111) — corollary on
  the structure of admissible `avail`.

**Conjectures / next milestones:** `R6_conjecture_classical_general_n`
(line 2131, stated not proven) extends this to general `n ≥ 3` via the
`det = ±1` sign-disconnect of `Equiv.Perm`; see
`R6_GENERAL_N_SCOPING.md` for the ~300-line proof sketch using
`Continuous.matrix_det` and `Matrix.det_permutation`. On the quantum
side: `StrictConnectedAgency` on `U(N)` is conjecturally non-trivial
(since `U(N)` is path-connected and compact), giving the
*positive* half of the classical-vs-quantum dichotomy.

This is the **substantive R6 level** — the level at which the
framework's agency postulate actually does discriminating work.

### Level 5 — `GroupClosedAgency G` (R7 algebraic scaffold)

**Adds (to L4):** the underlying availability set is closed under
composition; equivalently the "displacement" `R₂ ∘ R₁⁻¹` is itself a
`StrictReversible`. Carried by `GroupClosedReversiblePath` with field
`composition_in_strict`. The composition-closure analogue at the
`Reversible` level is the parallel class `ClosedAgency` (line 469)
which yields `Reachable.trans` and `Reachable.equivalence`.

**Philosophical content:** the availability structure is a *group*,
not merely a connected set. Two real choices combine into a real
choice. This is the algebraic precursor to identifying the
transformation set with a Lie group (Axiom IV's "group-theoretic
structure: forces are connections, matter is representations").

**Already proven (Lean):**
`StrictConnectedAgency.ofGroupClosedAgency` (forgetful instance),
`trivialGroupClosedAgency`. The transitivity payoff at the
`Reversible` (L1-extended) level: `Reachable.trans`,
`Reachable.refl_symm_trans`, `Reachable.equivalence`, and the
preorder/preorder-plus-symmetry lemmas (lines 476–549).

**Conjectures:** under R7, `GroupClosedAgency` on a finite-dimensional
GPT forces `avail` to carry a Lie-group structure. The classical
contrast: Birkhoff–von Neumann pins the bijective state-preserving
maps on Classical-`n` to the discrete `S_n`, whose only connected Lie
sub-component is `{id}`. The quantum contrast: `U(N)` is its own
connected Lie group.

### Level 6 — `SmoothConnectedAgency G` (R7 full) — **not yet in Lean**

**Adds (to L5):** the path γ is *smooth* (`C^∞`), giving the
availability set the structure of a Lie group acting smoothly on `V`.
This is the conjectured `SmoothReversiblePath` referred to in scoping
notes; it is not yet a Lean class because it depends on Mathlib's
`Geometry.Manifold.Algebra.LieGroup` and the smooth-structure machinery
on `Reversible G`.

**Philosophical content:** full continuity of becoming — not merely
topological connectedness but differential structure. This is the
level at which the framework can talk about *generators* of one-
parameter families and so invoke Stone's theorem
(observable-as-generator duality is (S3) in `TIER1_5_HILBERT.md`).

**Already proven (Lean):** *nothing yet*. The class definition is
deferred. `Examples.lean :: ContinuousWantable, scaleByPTrans` gives
the worked 1-dimensional Lie subgroup example (`ℝˣ ↪ PTrans ℝ`) that
will anchor the eventual general definition.

**Conjectures:** the framework's predicted route to (a) Hardy's
`K = N²` (cQM) over `K = N(N+1)/2` (rQM) via continuous reversible
1-parameter families admitting observable generators; (b) the local-
`PTrans` gauge story in `TIER2_GAUGE_SCOPING.md`, where Lie-group
structure on availability is the precondition for talking about
connections (gauge bosons) at all.

## ASCII implication diagram

The arrow `A → B` means "every `A` is a `B`" (forgetful instance);
the arrow points from stronger to weaker.

```
                  SmoothConnectedAgency        [L6, R7 full]
                       (not in Lean yet)
                              │
                              │ forget smoothness
                              ▼
                  GroupClosedAgency            [L5, R7 algebraic]
                       (group closure on avail)
                              │
                              │ StrictConnectedAgency.ofGroupClosedAgency
                              ▼
                  StrictConnectedAgency        [L4, R6-tris]  ← LOAD-BEARING
                       (bijective along path)
                              │
                              │ StrictReversiblePath.toReversiblePath
                              ▼
                  StrongConnectedAgency        [L3, R6-bis]
                       (Reversible along path)
                              │
                              │ ReversiblePath.toStatePreservingPath
                              ▼
                  StatePreservingAgency        [L2, R6 weak]
                       (state-preserving along path)
                              │
                              │ HasConnectedAgency.ofStatePreservingAgency
                              ▼
                  HasConnectedAgency           [L1, Hardy A5 ingredient]
                       (continuous path of linear maps)

   Parallel / orthogonal augmentation at L1:
       HasConnectedAgency  ──extends──▶  ClosedAgency
       (composition closure at the Reversible — not StrictReversible — level;
        gives Reachable.trans, Reachable.equivalence under inverse availability)
```

## Where each level "earns its keep"

| Level | Lean class | Forgetful to | Active proofs | Distinctive payoff |
|---|---|---|---|---|
| L1 | `HasConnectedAgency` | — | `hardy_axiom5_*` | Hardy A5 (modulo transitivity hypothesis) |
| L2 | `StatePreservingAgency` | L1 | `continuous_state_preserving_path` | (vacuous on convex states — no discrimination) |
| L3 | `StrongConnectedAgency` | L2 | scaffolding only | precursor to L4 |
| L4 | `StrictConnectedAgency` | L3 | `classical_n2_strict_reversible_path_id_swap_empty`, `R6_framework_main_classical_n2` | classical disconnect (n=2 proven, general n scoped) |
| L5 | `GroupClosedAgency` | L4 | `trivialGroupClosedAgency`, `Reachable.equivalence` (via parallel `ClosedAgency`) | group/Lie-group precursor |
| L6 | (`SmoothConnectedAgency`, deferred) | L5 | — | observable-as-generator, gauge structure |

## Cross-references

- **`TIER1_5_HILBERT.md`** explains the (S1) tensor / local tomography,
  (S2) connected reversible dynamics, (S3) observable-as-generator
  triple that jointly target the complex-vs-real-vs-quaternionic
  Hilbert space discrimination. (S2) is precisely the work that L4
  begins and L6 would complete; (S3) is what L6 unlocks.

- **`TIER2_GAUGE_SCOPING.md`** identifies L6 (and a *local* version
  thereof — local `PTrans` rather than global) as the framework's
  technical handle on gauge structure: gauge fields are the
  connection-compensators required when the smooth availability
  structure is allowed to vary across meetings.

- **`R6_GENERAL_N_SCOPING.md`** estimates ~300 lines of Mathlib-API
  plumbing to extend the L4 disconnect from `n=2` to general `n ≥ 3`
  using `Continuous.matrix_det` and `Matrix.det_permutation`. The
  conjecture is `R6_conjecture_classical_general_n` (`Classical.lean`
  line 2131); it is downstream of, not blocked by, current Mathlib.

## One-line summary

The hierarchy is the framework's staged commitment of the libertarian-
agency postulate: L1 buys Hardy A5; L4 buys the classical-vs-quantum
disconnect; L6 (conjectural) would buy the complex-Hilbert and
gauge-structure stories. Each level is exactly the strengthening
needed to make the next tier-1 / tier-2 target Lean-derivable from
the framework's metaphysical commitments rather than imposed by hand.
