# Hardy Axiom 2 as Pattern Parsimony

A research note investigating whether Hardy's Axiom 2 — currently
catalogued AUXILIARY in `Perspectival/Hardy.lean` — can be reframed
under the framework's metaphysical commitments to acquire substantive
content. **Status:** MOTIVATION-LEVEL only. The framework does not
*derive* A2; it can, however, *justify* A2 in a way Hardy himself does
not — by tying K minimization to the framework's commitment to
patterns-not-substances (Axiom IV) rather than to bare Occam's razor.
This note is a candidate AXIOM REFINEMENT in the sense of the
user clarification: the bare Wantable encoding does not yet make
pattern stability explicit; if it did, A2 could plausibly become
DERIVABLE.

## 1. Hardy's Axiom 2, precisely

Hardy 2001 §3 ("Simplicity"): *For each given N, K takes the minimum
value consistent with the axioms.*

Operationally (Hardy 2001 §5):
- `N` (operational dimension) = max size of a perfectly distinguishable
  set of states.
- `K` (state-space dimension) = min number of probability
  measurements determining a state = `dim ℝ⟨effects acting on
  states⟩`.

A2 is a *selection principle across theories*, not a structural axiom
about a single theory. Given N, the candidate K-values are
`K ∈ {N, N(N+1)/2, N², N(2N−1), …}` (classical, real, complex,
quaternionic, ...). Hardy invokes A2 to pick the smallest K
*compatible with the other four axioms*. With Axiom 5 (continuity of
reversibles) ruling out `K = N` (no continuous reversible group on the
simplex's vertex permutations except trivially), the *next* smallest
compatible K is `K = N²`: complex QM.

In the framework's current Lean encoding
(`Perspectival/Hardy.lean`, line ~100), A2 is a placeholder
(`def Axiom2_Simplicity (_G : GPT V) (_n _k : ℕ) : Prop := True`)
with the prose tag **AUXILIARY**: independent of I–IV, addable
without contradiction, not derivable from the bare Wantable
ontology.

## 2. Framework reading: K minimization as pattern parsimony

Hardy's own justification for A2 is bare *Occam's razor*: among
empirically adequate theories, prefer the simplest. This is a
*meta-theoretic* virtue with no grounding in the operational
structure itself. Hardy is candid that A2 is the most contestable
of his five axioms; Chiribella, D'Ariano, Perinotti 2010
("Probabilistic theories with purification") explicitly **drop** A2,
replacing it with a *purification* postulate and recovering QM
without any minimality clause. Their position: A2 is a stylistic
preference, not an information-theoretic principle.

The framework can do better than Hardy without going as far as CDP.
Axiom IV — *all apparent particulars are stable patterns within
meetings, not substances behind them* — provides a substantive
reading of K minimization:

- A GPT's K is the count of operationally independent degrees of
  freedom in its state space. Every additional dimension is a degree
  of freedom requiring **stable pattern formation** to be real in the
  framework's sense — a pattern that recurs across meetings rather
  than a substance posited behind them.
- Under Axiom IV, postulating a degree of freedom that is *not*
  required by any stable pattern is an ontological fiction: a
  substance behind the pattern. The framework forbids this.
- *Therefore:* the framework prefers the **minimum K consistent with
  the patterns it must support**. This is not bare Occam; it is the
  metaphysical claim that excess K beyond what stable patterns
  require would have to be substance-behind-pattern, which the
  metaphysics rules out.

This is a *substantive justification* for A2: K minimization is the
operational shadow of the anti-substantialism commitment in Axiom IV.

## 3. MOTIVATE vs DERIVE — calibrated claim

The above is a **motivation**, not a derivation. The honest
distinction:

- **MOTIVATE:** the framework's commitments give a non-arbitrary
  reason to *prefer* A2 to its negation. This is stronger than
  Hardy's Occam appeal (which is theory-external) because it is
  grounded in the framework's metaphysics (which is theory-internal).
- **DERIVE:** the framework's formal encoding (`Wantable`,
  `PTrans`, `WantableGPT.gpt`) *entails* A2. **This is not
  achieved.** The bare Wantable structure does not contain a
  predicate for "stable pattern formation" or "informational
  sufficiency" that would let one prove "any K exceeding the
  pattern-required minimum violates Axiom IV".

The Tier 1 catalog should continue to mark A2 as AUXILIARY (not
formally derived). But the prose justification can be upgraded from
"unmotivated outside Hardy's Occam" to "motivated by Axiom IV's
anti-substantialism" — a real philosophical gain even without a
formal derivation.

## 4. What additional structure would be needed to fully derive A2

To upgrade A2 from MOTIVATE to DERIVE, the framework would need to
formalize:

**(D1) Pattern stability predicate.** A Lean predicate
`PatternStable : GPT V → Set V → Prop` or similar, capturing what
"stable pattern within meetings" means operationally. Candidate
formalizations:
- *Informational sufficiency*: a sub-state-space is pattern-stable
  iff its dimension equals the operational dimension N of its
  perfectly-distinguishable set. (This is essentially `K = N` for
  the sub-space — the classical signature for patterns.)
- *Reachable closure*: a pattern is stable iff the orbit of a state
  under `HasConnectedAgency`-permitted transformations is contained
  in the pattern set.
- *Markov-blanket-style*: a pattern is stable iff its statistics are
  invariant under the choice of measurements outside its
  effect-span. (Friston-flavoured; consistent with the
  `Information-theoretic: Jaynes, Friston` lineage tag.)

**(D2) Substance-behind-pattern impossibility theorem.** A theorem
of the form: any K exceeding the minimum required to host the
pattern-stable structures *necessitates* unobservable degrees of
freedom — i.e., effects that do not separate any pair of
distinguishable states. Such degrees of freedom would be "substance
behind pattern" in the framework's sense, and Axiom IV would forbid
them.

**(D3) Refinement of Wantable to encode pattern stability.** The
current `Wantable` typeclass exposes only the complement involution.
A refinement (`StablePatternWantable` or similar) could expose a
predicate distinguishing stable from transient pattern configurations,
making the Axiom IV commitment formally visible at the Lean level.
This is exactly the **axiom refinement** path the user authorized in
the ORIGINAL_PROMPT clarification: "if the bare Wantable axioms don't
motivate K minimization, refine the formal Wantable encoding to make
pattern stability explicit."

With (D1)–(D3) in place, a candidate theorem statement would be:

```
theorem A2_from_pattern_parsimony
    (G : GPT V) (n : ℕ) (hN : HasDimensionN G n)
    (h_stable : ∀ ρ ∈ G.states, PatternStable G {ρ}) :
    Module.finrank ℝ V = K_min n hN
```
where `K_min n hN` is the least K in the Hardy table consistent with
the other axioms. **This theorem is not proven; it is the formal
target a successful A2-derivation would meet.**

## 5. Comparison to Hardy 2001 §5 and Chiribella–D'Ariano–Perinotti 2010

**Hardy 2001 §5.** Hardy uses A2 *twice*: (i) at K = N to pick out
classical when continuity (A5) is dropped; (ii) at the next K value
(K = N²) to pick out complex QM. A2 is the *only* axiom doing
theory-selection work; the others are structural. Hardy concedes A2
"may be regarded as having a different status to the others"
(Hardy 2001 p. 12). The framework's reading — A2 as pattern
parsimony grounded in Axiom IV — fits Hardy's intuition that A2 is
metaphysically loaded, but supplies the metaphysical grounding Hardy
leaves implicit.

**Chiribella–D'Ariano–Perinotti 2010.** CDP reconstruct QM from six
axioms *without* a minimality / simplicity clause. They replace A2
with a **Purification Postulate**: every mixed state arises as the
marginal of a pure state on a composite system. Their derivation
shows A2 is *eliminable* given a strong enough composition axiom.
This is significant for the framework: it suggests A2's content
could be absorbed into refinements of Axioms III–IV (the
meeting / pattern structure) without an explicit minimality clause.
If the framework's strengthening of Axiom IV plus a CDP-style
purification (which would be a candidate derivation from
"every wanting has a complement clearing" — Axiom II) yielded QM,
A2 would be **dispensable** rather than **derivable**. This is an
alternative path worth investigating in parallel.

## 6. Catalog entry — candidate AXIOM REFINEMENT

Per the user clarification ("the metaphysics is fixed; the axioms can
be adjusted"), this note formally catalogs the following refinement
candidate:

> **Refinement candidate: PatternStableWantable.** Extend the
> `Wantable` typeclass with a predicate or structural constraint
> capturing pattern stability (informational sufficiency, reachable
> closure, or Markov-blanket invariance — to be determined). This
> would make Axiom IV's anti-substantialism formally visible in the
> Lean encoding and is the prerequisite for upgrading Hardy A2 from
> AUXILIARY to DERIVABLE.

**Catalog status:**
- Tier: bridges Tier 1 (Hardy reconstruction) and Tier 1.5
  (`TIER1_5_HILBERT.md` — complex Hilbert space).
- Honesty band: **(c) plausible but unchecked** in the ORIGINAL_PROMPT
  §7 four-band schema.
- Dependencies: requires formalization of pattern stability (D1),
  which is currently not present in the codebase.
- Cross-reference: relates to the (S3) "observable-as-generator"
  duality in `TIER1_5_HILBERT.md` §3 — both are framework
  refinements that strengthen Axiom IV with structure not present in
  the bare `Wantable` typeclass.
- Falsification path: if no Lean predicate for pattern stability can
  be defined that simultaneously (i) is faithful to Axiom IV and
  (ii) entails K minimization, the refinement fails. Then either A2
  remains AUXILIARY (Hardy's status quo) or A2 is dispensed with via
  a CDP-style purification refinement.

**Verdict.** The framework can give Hardy A2 a substantive
philosophical justification (pattern parsimony grounded in Axiom IV)
that Hardy himself does not supply. This is a real interpretive
gain. It is *not* a derivation: the bare Wantable encoding lacks the
pattern-stability predicate that would close the gap. The candidate
refinement is concrete enough to attempt in a future Lean session
but should be undertaken in parallel with the CDP-style purification
alternative, since either could subsume A2 differently.
