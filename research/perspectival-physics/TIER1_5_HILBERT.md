# Tier 1, Target #5 — Complex (vs Real / Quaternionic) Hilbert Space

A research note sketching a path from the framework's current
operational machinery to a derivation that the QM-like generalized
probabilistic theory (GPT) consistent with the framework's
strengthened axioms must be *complex*, not real or quaternionic.
This is the framework's intended extension of Renou et al. 2021.

## 1. The target, restated in framework language

In the Hardy / Müller / Masanes–Müller reconstruction style, the
finite-dimensional candidates for "QM-like" GPTs are classified by
the Hardy signature `(N, K)` plus a compositional rule:

| Theory             | N–K relation       | Composition (K_AB) |
|--------------------|--------------------|--------------------|
| Classical          | `K = N`            | `K_A + K_B` or `K_A · K_B` |
| Real QM (rQM)      | `K = N(N+1)/2`     | `K_A · K_B` (with constraints) |
| Complex QM (cQM)   | `K = N²`           | `K_A · K_B`        |
| Quaternionic (qQM) | `K = N(2N − 1)`    | violates *local tomography* |

The framework's Tier 1 target #5 is: starting from axioms I–IV plus
the *strengthened* operational postulates already in our Lean
codebase (`HasConnectedAgency`, `ClosedAgency`, tomographic
locality of composition), derive that the only consistent
GPT-instantiation of `WantableGPT` extended along these axes is the
**complex** one.

This is to be distinguished sharply from two adjacent claims:
- **Renou et al. 2021** (Nature 600, 625) experimentally falsified
  *real-amplitude* QM by exhibiting a network Bell-style scenario whose
  quantum predictions cannot be reproduced by any rQM model with the
  standard tensor rule. That is an *empirical* exclusion within an
  assumed quantum framework.
- The framework's target is a *structural* exclusion: starting from
  agency-refined perspectival axioms, complex Hilbert space falls
  out as the unique consistent quantum-like compositional structure,
  without input from Renou's experiment. Renou rules out rQM as a
  description of nature; the target here is to rule out rQM as a
  realization of the framework's axioms. The two together would be
  complementary, not redundant.

## 2. What the current Lean code already says

`WantableGPT.lean` builds, for any finite `Wantable W`, a GPT whose
state space is the standard simplex on `W`. The verified theorems
of interest are:

- `finrank_V_eq_card`: `dim_ℝ(V W) = |W|`.
- `wantableGPT_is_classical`: `K = N = |W|`.
- `wantableGPT_not_quantum`, `wantableGPT_not_realQM`,
  `wantableGPT_not_quaternionicQM` (bundled as
  `wantableGPT_classical_dichotomy`): for `|W| ≥ 2`, each of
  `K = N²`, `2K = N(N+1)`, `K = N(2N − 1)` fails.

The bridge therefore lands strictly on the *classical* row of the
table. This is the explicit no-go we work against: any non-trivial
discrimination among rQM, cQM, qQM must be driven by axioms strictly
stronger than what `Wantable` + `WantableGPT.gpt` provides. The
`Continuity.lean` module already introduces one such strengthening
(`HasConnectedAgency`), used to derive Hardy Axiom 5
(`hardy_axiom5_transitive`). That is the lever to push on.

## 3. The strengthening needed

The path to rule out rQM and qQM from the framework, rather than from
experiment, requires three further structural commitments — each
already half-present in the codebase as a postulate or placeholder:

**(S1) Tomographic locality of composition.** When two perspectival
systems compose, the joint state is determined by its marginal
statistics together with the statistics of jointly-performed local
measurements. In Hardy's framework this is the multiplicative rule
`K_AB = K_A · K_B`. Quaternionic QM is known (Wootters, Hardy,
Barnum–Müller–Ududec) to *violate* this rule: for qQM
`K_AB > K_A · K_B`. Our current `Composition.lean` provides only
disjoint-union (additive) and product (multiplicative-at-the-
cardinality-level) composition; the genuine GPT tensor product is
missing (`Axiom4_Composite_States_Multiply` is a placeholder).
Constructing it and proving local tomography is what excludes qQM.

**(S2) Connected reversible dynamics.** `HasConnectedAgency`
postulates a path-connected group of reversible transformations on
states. The framework's *agency* refinement — that at every instant
the perspective genuinely chooses, with no smallest non-trivial
choice — is the philosophical motivation. Real-QM has reversible
dynamics group `O(N)`, which is *disconnected* (two components).
Strengthening agency to *connectedness* of the reversible group is
what excludes rQM at the dynamics level. This is the gap flagged in
ROADMAP R6/R7 — moving from `path_via_affineLine` (cheap; always
satisfiable on topological V) to a non-trivial constraint that the
*availability set* is connected in a non-vacuous sense.

**(S3) Energy / observable–generator correspondence.** Stone's
theorem gives one-parameter unitary groups from self-adjoint
generators. The Hardy-style derivation of cQM uses the fact that any
continuous reversible 1-parameter family of pure-state
transformations admits a generator that is itself an observable; this
"observable-as-generator" duality is what distinguishes cQM from rQM
(in rQM, antisymmetric generators are *not* observables). The
framework's libertarian-agency reading licenses (S3) by identifying
each perspectival transformation with its dual measurement — the
*want for the transformation* and its *clearing*. This needs to be
formalized as a structural axiom on the agency set.

## 4. Sketch of the technical chain in Lean

A plausible chain of theorems, in order of dependency:

```
HasConnectedAgency  ──┐
ClosedAgency        ──┼─►  reversible_group_is_Lie  (R7)
StrictReversible    ──┘            │
                                   ▼
                       reversible_group_connected
                                   │
                                   ▼                       ┌─► not_realQM_from_agency
       gptTensor (R5) ──► local_tomography_holds  ────────┤
                                   │                       └─► not_quaternionicQM_from_agency
                                   ▼
                          observable_generator_duality (S3)
                                   │
                                   ▼
                       hardy_signature_is_complex  (Tier 1 #5)
```

Concretely, the new Lean targets would be:

1. `gptTensor : GPT V₁ → GPT V₂ → GPT (V₁ ⊗ V₂)` with the property
   `finrank (gptTensor G₁ G₂).ambient = (finrank G₁) * (finrank G₂)`
   under local tomography (R5 in `ROADMAP.md`).
2. `local_tomography (G_AB) : ∀ ρ ∈ G_AB.states, ρ is determined by
   its marginal-and-product effect values` — to be proven for
   `gptTensor` of WantableGPTs strengthened by (S1).
3. `not_quaternionicQM_of_local_tomography`: a theorem of Hardy /
   Barnum–Müller form, that local tomography forces `K_AB = K_A · K_B`
   and hence excludes the qQM signature `K = N(2N − 1)` (because the
   qQM `K_AB` is strictly larger).
4. `reversible_group_connected_of_agency` (refines `Reachable.equivalence`
   already in `Continuity.lean` to a topological-connectedness claim on
   the *group*, not just the orbit relation).
5. `not_realQM_of_connected_reversibles`: rQM's `O(N)` is disconnected;
   any GPT realization with connected reversible group cannot have rQM
   signature.
6. `hardy_signature_complex`: the only Hardy signature consistent with
   (1)–(5) plus Axioms 1, 3, 5 is `K = N²`.

Of these, (1)–(2) are tractable extensions of Mathlib's tensor product
infrastructure; (3) is well-trodden in the GPT literature and would
mostly be a transcription; (4) is the substantive open piece — the
*genuine* research bottleneck flagged repeatedly in `ROADMAP.md` and
`FINDINGS.md`; (5)–(6) follow once (4) lands.

## 5. Relation to Renou et al. 2021

Renou et al. show that in a network scenario with three independent
sources, rQM cannot reproduce certain quantum correlations. This is an
*empirical* falsification of rQM as a description of nature, modulo
auxiliary assumptions about how independent sources compose. The
framework's target #5 would be a complementary *structural*
falsification: rQM cannot be a model of axioms I–IV strengthened by
(S1)–(S3). Together: nature is not rQM (Renou) *and* the framework's
axioms cannot be realized by rQM (target #5). Either result alone
leaves the other open; the framework's target is the second.

The framework would not, in this form, "reproduce" Renou's
experimental result. Reproducing Renou would require constructing the
specific network scenario inside `WantableGPT` and computing
correlation bounds — a separate, much larger derivation that is not
part of Tier 1 #5 as stated.

## 6. Honest catalog: tractable vs blocked

**Tractable (months, plausible Lean targets):**
- (1) ~~`gptTensor` construction.~~ **DONE** — `Perspectival/GPTTensor.lean`.
- (2) ~~Local-tomography predicate and its proof for the constructed tensor.~~ **DONE** — `TomographicLocality` + `gptTensor_tomographic_local`.
- (3) ~~qQM exclusion via local tomography.~~ **DONE** at the structural level (documented in `GPTTensor.lean`'s comment block); rebit also excluded by the same argument (K_AB = K_A · K_B fails for both).
- A Lean-encoded statement of Renou's network scenario as a GPT
  configuration — not a derivation, but a precise formal target. **OPEN.**

**Blocked on R6/R7 (the agency-connectedness gap):**
- (4) Connectedness of the reversible group from agency — currently
  only the *path-connectedness of the availability set* is postulated,
  and `path_via_affineLine` shows this is cheap when V is topological.
  The substantive content (which transformations are admissible) is
  what must be tightened.
- (5) rQM exclusion via connectedness.
- (6) The full uniqueness theorem.

**Speculative (the agency–observable duality, S3):**
- A formal statement of observable-as-generator that earns its keep
  by deriving Stone's theorem in this setting. Without it, cQM is
  consistent with the strengthened axioms but not uniquely picked out —
  some weaker non-classical theory (e.g., the "Spekkens toy GPT")
  could fit.

**Verdict.** Of the chain above, (1)–(3) close *one* of the three
non-classical no-gos (qQM) by importing standard GPT results into our
predicate language and constructing the tensor; this is publishable
incremental progress. The rQM exclusion (4)–(5) is the framework's
*distinctive* contribution but is gated on the same agency-connectedness
strengthening that gates the Hardy Axiom 5 derivation; it is not
unlocked in this session. The full uniqueness statement (6) is gated
on (S3) and is the most speculative.

The honest status of Tier 1 #5 is therefore: **the qQM exclusion is
tractable as a Lean target via local tomography; the rQM exclusion
remains open and is the same bottleneck as R6/R7; the full
"complexity is forced" theorem requires an axiom (S3) that has been
philosophically argued but not formalized.** A successful pursuit
would yield, at minimum, a formally verified extension of the
existing `wantableGPT_not_quaternionicQM` theorem from the bare
`K = |W|` argument to a genuine local-tomography argument that
applies to *strengthened* WantableGPTs, not only to the trivially
classical one.
