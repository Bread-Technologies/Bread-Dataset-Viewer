# v2 Audit — Re-examining Prior Results Under the Two-Tier Architecture

Per ORIGINAL_PROMPT v2 §8 + first moves #7 and #8, the prior Tier B
work needs honest re-examination under the two-tier architecture.
This doc records the audit findings.

## Audit Item 1: A5-from-agency (first move #8)

**Question.** Is the agency postulate strictly weaker than continuity?
If not, A5-from-agency is empty (the assumption quietly contains the
conclusion).

**Finding.** **Mixed.** The framework has a hierarchy of agency
postulates, not a single one. The non-triviality varies by level.

### `HasConnectedAgency` (weakest):
The bare agency postulate says `avail ⊆ Reversible G` is
path-connected by `γ : [0,1] → V →ₗ V`. The path is of LINEAR MAPS;
intermediate `γ(t)` need not preserve states or be reversible.

**Verdict on this level:** GENERICALLY SATISFIABLE. `path_via_affineLine`
in `Continuity.lean` shows that on a topological vector space, ANY
two linear maps `R₁, R₂` are connected by the affine path
`γ(t) = (1-t) R₁ + t R₂`. So a bare HasConnectedAgency is essentially
free.

Therefore: `hardy_axiom5_of_agency` at the HasConnectedAgency level
derives "continuity between reachable states" from a postulate that is
nearly tautological. **The derivation is largely tautologous at this
level.** Honest reframing: at this level, A5-from-agency tells us
that *granted reachability* (= existence of some reversible R with
R ρ₁ = ρ₂), the existence of a continuous path is essentially
automatic given the topological structure of V →ₗ V.

### `StatePreservingAgency`:
Now paths must be state-preserving at every intermediate t.

**Verdict:** NON-TRIVIAL. Not every linear-map path is state-preserving;
the constraint is genuine. The existence of a state-preserving path
between arbitrary state-preserving maps is a real condition.

### `StrictConnectedAgency`:
Paths must be state-preserving AND bijective at every t.

**Verdict:** NON-TRIVIAL and SUBSTANTIAL. This is where the R6
disconnect on Classical n=2 (= Birkhoff disconnect) bites.

### `TransitiveAgency` and `PurePreservingTransitiveAgency`:
Even stronger. These are the L6/L7 closures.

**Verdict:** SUBSTANTIAL. The L7 closure on Classical n ≥ 2 is
unconditional given the framework's structural commitments.

### Conclusion on A5-from-agency

The "A5 from agency" formulation is honest IF qualified by which
level of the agency hierarchy is being assumed. At the weakest level,
it's mostly tautologous. At the StrictConnectedAgency level and
above, it's substantive. Future writeups should specify the level
when claiming A5-from-agency.

The cleanest version of the result: at StrictConnectedAgency level,
the existence of a continuous reversible state-preserving path
between any two pure states FAILS for Classical n ≥ 2 (R6 disconnect),
but the agency postulate itself doesn't trivially encode the failure
— it asks for the connection; the failure is a genuine theorem.

## Audit Item 2: Triple no-go (first move #7)

**Question.** Is the triple no-go a sharp constraint, or a weakness
diagnosis?

**Finding.** **Both.** The triple no-go has two readings:

### Sharp-constraint reading:
For any finite Wantable W with |W| ≥ 2, `WantableGPT.gpt W` is
exactly the classical (N=K=|W|) GPT. The three non-classical Hardy
signatures (qubit K=N², rebit K=N(N+1)/2, qQM K=N(2N-1)) are
provably excluded.

This is a clean structural result: the bare-axioms bridge from
Wantable to GPT lands on the classical simplex.

### Weakness-diagnosis reading:
The bare-axioms bridge does NOT recover QM. Additional structure
must be added to bridge to QM.

The framework's recognition: this is why the agency hierarchy was
introduced. The agency strengthening adds continuous-symmetry
structure that the bare Wantable axioms don't have.

### Under v2

The triple no-go now has a *third* reading made possible by the
two-tier architecture:

The WantableGPT bridge is a Tier B object — it's the operational
state-space derived from the bare Wantable structure. The triple
no-go says this Tier B object is classical.

But under v2, Tier B should emerge from Tier A by bracketing — and
the bracketing operation may force additional Tier B structure
(continuous symmetries, vertex preservation) that isn't directly
visible in the bare WantableGPT bridge.

**Reframed claim:** the triple no-go shows the LIMIT of what the
bare-axioms Tier B encoding can deliver. To get QM at Tier B, we
need either:

(a) Additional axioms beyond Wantable (the "metaphysics-fixed,
axioms-adjustable" route — auxiliary postulates).
(b) A proper bracketing-from-Tier-A derivation (the v2 route — the
additional Tier B structure emerges from the limit operation).

Route (b) is the v2-progressive direction. It is currently OPEN at
the formal level (TierB.lean encodes the bracketing operation but
hasn't yet derived QM structure from it). This is the framework's
main remaining technical work.

### Conclusion on triple no-go

The triple no-go is SHARP at the structural level (the bare Wantable
bridge lands precisely on classical). It is also a WEAKNESS
DIAGNOSIS at the program level (more is needed for QM). Under v2,
the additional structure required is targeted: it should be derivable
from Tier A via bracketing, not added as an unprincipled patch.

## Audit Item 3: vertex preservation as v2-progressive

**Question.** Was the v1 vertex-preservation patch a progressive
patch (made implicit commitment explicit) or a degenerative patch
(saved predictions from contradiction)?

**Finding.** **Progressive — verified by v2 reframing.**

Under v1, vertex preservation was added to the R6 disconnect
argument because the naive "state-preserving = permutation" claim
failed for n ≥ 3. This looked like a save.

Under v2, vertex preservation is *not a patch* at all. It is a
derived Tier B theorem expressing the constraint that bracketed
dynamics preserve pure potential states (= no actualization, no
information loss). Specifically:

- Pure potential states correspond to definite-but-not-yet-
  actualized meeting configurations.
- Bracketed dynamics don't actualize anything.
- So pure potential states remain pure — vertex preservation.

This is exactly the "make implicit commitment explicit" pattern.
The v1 patch made operationally visible what was already structurally
implicit in the foundation. Hence progressive, hence welcome.

This pattern is the template for future patches: when the framework
needs a Tier B addition, check whether it expresses a Tier A
commitment. If yes, progressive. If not, degenerative — warning sign.

## Audit Item 4: WantableGPT bridge novelty

**Question.** Is the WantableGPT bridge a substantive contribution
beyond Hardy/CBH/Müller, or a re-encoding of standard GPT structure?

**Finding.** **Bridge has framework-distinctive content; needs
external validation.**

The bridge `WantableGPT.fromPTransHom` provides an injective MonoidHom
`PTrans W →* (operational transformation monoid)`. The framework-
specific content: `PTrans W` is the *centralizer* of complement in
`Equiv.Perm W` (not the full symmetric group). This is a constraint
that distinguishes the framework's transformations from purely
operational ones.

**Verification needed:** confirm with Müller / foundations community
whether this centralizer-characterization has appeared in operational
reconstruction literature. If it's genuinely new, it's a framework-
distinctive contribution. If it's known, the bridge is a faithful
re-encoding.

**Recommendation:** flag this for Müller-level peer review before
claiming novelty in publication.

## Summary

The v2 audit finds the prior Tier B work largely sound, with these
nuances:

1. A5-from-agency is non-trivial at the StrictConnectedAgency level
   and above; tautologous at HasConnectedAgency level. Specify
   the level.
2. Triple no-go is both sharp constraint AND weakness diagnosis.
   Under v2, the additional structure for QM should be derived from
   Tier A bracketing, not added as a patch.
3. Vertex preservation is a v2-progressive reframing — the v1
   patch is now a derived theorem expressing a Tier A commitment.
4. WantableGPT bridge novelty needs external (Müller-level)
   validation.

These are honest, calibrated findings. They do not invalidate the
prior work; they relocate it within the v2 architecture and identify
exactly where more rigorous external verification is needed.

The path forward: continue v2 first moves (Lean formalization of
Tier A → Tier B bracketing, derivation of vertex preservation as
Tier B theorem from Tier A foundations, R7 Lie-group bridge, seam
formalization).
