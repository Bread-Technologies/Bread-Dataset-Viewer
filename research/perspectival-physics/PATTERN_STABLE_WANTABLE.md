# PatternStableWantable — A Concrete Axiom-Refinement Proposal for Axiom IV

**Status:** research proposal, formulation-level. No Lean
implementation in this note. Companion to
`HARDY_A2_AS_PARSIMONY.md`; concretizes the catalog entry §6 of that
note ("Refinement candidate: PatternStableWantable") into a specific
typeclass design with three candidate stability predicates, a
recommendation on which to formalize first, and an identification of
the smallest change to `Perspectival/Ontology.lean` that would
suffice.

The user clarification in `ORIGINAL_PROMPT.md` authorizes this kind
of move explicitly: *"the metaphysics is fixed; the axioms are
adjustable."* The present note is an adjustment-candidate for the
bare `Wantable` encoding so as to make Axiom IV's anti-substantialism
formally visible — and, downstream, to upgrade Hardy A2 from
AUXILIARY to DERIVABLE.

## 1. Axiom IV, restated precisely

From `ORIGINAL_PROMPT.md` §1:

> **IV. All apparent particulars (selves, things, laws, space, time)
> are stable patterns within (III), not substances behind them.
> Group-theoretic structure: forces are connections, matter is
> representations.**

Three claims are packed in: (1) **pattern-as-particular** —
electrons, selves, laws are all patterns in Axiom III meetings, not
carriers of those patterns; (2) **no substance-behind-pattern** —
nothing additional "has" the pattern; recurrence is identity;
(3) **group-theoretic instantiation** — when patterns admit
symmetry analysis, forces appear as connections, matter as
representations (Wigner 1939).

The present `Wantable` in `Perspectival/Ontology.lean` encodes
Axiom II and gestures at Axiom III via `Meeting`. Axiom IV is
gestured at by `Pattern := Reality → Prop` (line 234) but is
*vacuous*: `Pattern.trivial` and `Pattern.empty` are the only
inhabitants, and there is no stability condition. So Axiom IV is
not formally active in any derivation.

## 2. The proposed typeclass

```
class PatternStableWantable (W : Type u) extends Wantable W where
  Stable    : W → Prop
  -- candidate stability predicate; see §3 for three options.
  stable_complement : ∀ w, Stable w → Stable (complement w)
  -- complementary partners co-stabilize (Axiom II + IV consistency).
  stable_nonempty   : ∃ w, Stable w
  -- ruling out "no patterns" — otherwise the typeclass holds vacuously
  -- and Axiom IV reduces to its negation.
```

Two minimal sanity conditions are imposed: complement-closure (a
pattern's complement is also a pattern; required because Axiom II
says every want has its partner and Axiom IV says particulars are
patterns), and non-vacuity (at least one stable want exists; a
universe with no patterns is not what Axiom IV is claiming).

The interesting content is in `Stable` itself. Three candidate
formulations follow.

## 3. Three candidate stability predicates

### (a) Informational sufficiency (Friston / Markov blanket)

```
Stable w  :=  ∃ (P : W → Prop), Finite {v | P v} ∧ P w ∧
                ∀ v, P v ↔ P (complement v) ∧
                (∀ f : PTrans W, P (f.toFun w) → P w)
```

**Reading.** A want `w` is *pattern-stable* iff it lies in a finite
predicate that (i) is closed under complementation and (ii) is
*Markov-blanketed* against `PTrans`: outside transformations don't
leak in. The predicate `P` plays the role of the Markov blanket
(Friston 2010, 2019): an interface across which conditional
independence holds.

**Lineage.** Friston's FEP defines a self-evidencing system as one
whose internal states are conditionally independent of external
states given the blanket. (a)-stability is the framework's
structural analog: identity sustained by a finite information
envelope, not by an underlying substrate.

### (b) Reachable closure (attractor dynamics)

```
Stable w  :=  let orbit := {v | ∃ f : PTrans W, f.toFun w = v}
              Finite orbit ∧
              ∀ v ∈ orbit, ∀ f : PTrans W, f.toFun v ∈ orbit
```

**Reading.** A want is pattern-stable iff its orbit under all
perspectival transformations is finite and closed. The orbit is the
"pattern" — the recurrence-set of the want under the framework's
permitted dynamics. Substance-behind-pattern would show up as orbit
points that lie outside any finite closed set, i.e. as a *reservoir*
of additional structure the want would have to carry around.

**Lineage.** Dynamical-systems attractor theory; Whitehead's
"actual occasions" reaching their satisfaction; Hayek's spontaneous
order as the closure of feedback loops.

### (c) Pattern-coherence under composition

```
Stable w  :=  ∀ (W' : Type u) [PatternStableWantable W'] (w' : W'),
              Stable w' → StableProd (w, w')
```

where `StableProd` is the lifted stability predicate on `W × W'`.

**Reading.** Pattern-stability is the property of *surviving
composition*: the pattern persists when the system is placed in
context with other patterns. This is the "purification-compatible"
reading — close in spirit to CDP 2010 Axiom 1.

**Lineage.** Categorical composition; Whitehead's prehension chains;
Buddhist *paticca-samuppada* (dependent origination) at the level of
patterns of patterns.

## 4. Which Wantable instances survive

Currently `Perspectival/Examples.lean` supplies these instances:
`Bool`, `Fin 2`, `Fin 3`, `Fin 4`, `Unit`, `Empty`, `ℤ`, `ℝ`,
`Option W`, `List W`, function spaces, products, sums.

Under formulation (a) **informational sufficiency**:

- `Bool`, `Fin 2`, `Fin 3`, `Fin 4`: **survive.** Finite, with
  finite predicates closed under complement. Trivially Markov-
  blanketed (whole carrier is the blanket).
- `Sum`, `Product` of survivors: **survive** under componentwise
  blankets.
- `Unit`: **fails non-vacuity** in a non-trivial sense — its only
  pattern is the trivial one; this should arguably *not* be a
  pattern-stable Wantable because `Unit` has no internal pattern
  structure to be stable about. (Formally it survives the literal
  predicate; philosophically it is the degenerate case.)
- `Empty`: **fails non-vacuity** (`stable_nonempty` cannot be
  witnessed; the typeclass cannot be instantiated). This is correct:
  Axiom IV says particulars are patterns; if there are no wants,
  there are no patterns to be stable about. The empty Wantable is
  not an existent.
- `ℤ`, `ℝ`: **fail finite-blanket** under (a). They are admissible
  only with a topological / measure-theoretic refinement of
  formulation (a) where "finite" is replaced by "compact" or
  "of finite information". This is the correct outcome: an
  unbounded continuum has no business carrying Axiom IV's
  particular-claim without further structure.
- `List W`, `A → W`: **fail finite-blanket** generically.

Under formulation (b) **reachable closure**, the survival set is
similar but the boundary is drawn by orbit-finiteness under
`PTrans`, which on `ℤ` (PTrans = translations and negation) is
generically infinite. Result: same finitist filter.

Under formulation (c) **composition-coherent**, all current Wantable
instances would *trivially* survive (composition is already total
in the typeclass system), so (c) on its own filters nothing. (c) is
the right *additional* clause once the base predicate is fixed but
cannot be the base predicate.

So all three formulations enforce a real restriction: `Empty` is
out (correct, Axiom IV is about existents); `Unit` is borderline
(degenerate, no internal pattern); the unbounded continua are out
absent further structure. This is the right behavior: Axiom IV
should not be claiming that *any* type with an involution counts as
a pattern-bearing reality.

## 5. Why this would motivate Hardy A2

`HARDY_A2_AS_PARSIMONY.md` argues verbally that K minimization is
the operational shadow of "no substance behind pattern." The
present typeclass makes that argument precise:

- In a `PatternStableWantable`, every want that is a *real
  particular* (Axiom IV) satisfies `Stable`. The set of stable
  wants is the set of particulars the GPT must support.
- A GPT's K is the dimension of its state space. Every dimension
  must be required by some stable want (a separating effect for at
  least one pair of distinguishable stable wants). Otherwise the
  dimension supports no pattern and so corresponds to substance-
  behind-pattern.
- Therefore K = the minimum dimension required to host the stable
  pattern structure. This is Hardy A2.

The formal target theorem from `HARDY_A2_AS_PARSIMONY.md` §4 is
now well-typed: `h_stable : ∀ ρ ∈ G.states, PatternStable G {ρ}`
becomes `h_stable : ∀ ρ ∈ G.states, Stable (representativeOf ρ)`
for a `PatternStableWantable`-derived GPT.

## 6. Smallest change to Ontology.lean

The proposal is **purely additive**: do *not* modify the existing
`Wantable` typeclass (lines 31–34 of `Perspectival/Ontology.lean`).
Instead, add a single typeclass declaration after the current
`Wantable` block (after line ~99) and a single instance of the
trivial `Stable := True` pattern as a `PatternStableWantable.dummy`
to confirm typeclass resolution still works. The minimum diff is:

```
class PatternStableWantable (W : Type u) extends Wantable W where
  Stable : W → Prop
  stable_complement : ∀ w, Stable w → Stable (complement w)
  stable_nonempty   : ∃ w, Stable w
```

That is it. Four lines. No existing theorem in the codebase needs
to change, no existing `Wantable` instance breaks (because
`Wantable` is not refined, only extended in a sibling typeclass).
GPT derivations that currently rely only on `Wantable` continue to
work; new derivations that need pattern stability can take
`[PatternStableWantable W]` as a stronger hypothesis. This is
exactly how Mathlib structures stronger algebraic typeclasses
(`AddGroup` → `AddCommGroup`).

A trivial `Stable := True` auto-instance on finite types would be
convenient but is *wrong philosophically* — we want `Stable` to
discriminate; the trivially-true predicate defeats the point. So
the minimum diff is the four-line `class` declaration and nothing
else.

## 7. Recommended formulation to formalize first

**Recommendation: formulation (a) — informational sufficiency.**

Reasons:

1. **Tractable.** `Finite {v | P v}` is a standard Mathlib idiom.
   No new mathematical apparatus is required (unlike (b)'s orbit
   analysis under the full `PTrans` group, which on infinite
   Wantables can require nontrivial Lie-theoretic input).
2. **Empirical.** It produces the right boundary in §4: finite
   types pass, unbounded continua fail. (b) gives the same boundary
   but with more work; (c) gives no boundary on its own.
3. **Lineage-coherent.** It is the most direct link to Friston's
   FEP, which is explicitly named in `ORIGINAL_PROMPT.md` §4
   (Information-theoretic lineage). Formalizing (a) lets us cite
   that lineage in Lean comments without strain.
4. **Composable later.** Once (a) is in place, (c) can be added as
   an additional clause: `Stable w ∧ ∀ w', Stable w' → StableProd`.
   And (b) can be derived as a *theorem* for finite-blanket
   instances: a finite Markov blanket implies a finite orbit under
   blanket-preserving PTrans. So (a) is the foundation; (b) and
   (c) become theorems or extensions, not competing axioms.

Formulation (b) is the *second* priority because it is the cleanest
match to "attractor" intuitions and to Whitehead-Bergson process
metaphysics. It should be formalized after (a) is in place, as a
theorem about orbits of (a)-stable wants.

Formulation (c) is the *third* priority. It is the natural bridge
to CDP 2010 purification and to categorical / monoidal composition,
but cannot stand as the base predicate.

## 8. Cross-references

- **Friston FEP (2010, 2019)**: a system's Markov blanket
  conditionally separates internal from external states.
  Formulation (a)'s finite predicate plays this role; a
  pattern-stable want is a want with a Markov blanket.
- **Whitehead, *Process and Reality* (1929), Part II ch. 2**:
  actual occasions are concrescences of prehensions, not enduring
  substances. A `Stable` want is the framework's analog: identity
  (it satisfies `Stable`) without substance (no carrier beyond the
  want and its complement).
- **Buddhist *paticca-samuppada***: dependent origination. A
  pattern stable under (b) — closed orbits of mutual re-emergence
  — is the structural reading of dependent co-arising.
- **Hayek, *The Sensory Order* (1952)**: classification as
  spontaneous-order pattern-stabilization; the framework reads
  physical particulars the same way.
- **Rorty, "the world well lost"**: real-as-honorific. See §9.

## 9. Pattern-stability vs compatibilist drift

`ORIGINAL_PROMPT.md` §8 lists *compatibilist drift* as a failure
mode. The compatibilist move is: "what we call X (freedom,
selfhood, an electron) is just a stable pattern in the underlying
deterministic substrate." Substrate real; pattern derivative.

The framework's move is the opposite. There is no substrate under
the pattern. The pattern *is* the particular.
`PatternStableWantable.Stable` is not a predicate over a hidden
microphysics; it is a predicate over wants themselves, where wants
are the basic ontological items per Axiom I.

Formulation (a) could be misread compatibilistically as "the
pattern is real because finitely describable in an underlying state
space." That reading is wrong. The finite predicate `P` is the
pattern's own self-organizing constraint on which complementary
partners it recruits — not a projection from a larger substrate.
The Markov blanket is metaphysically basic, not emergent. This is
the Russellian-monism-extended position from `ORIGINAL_PROMPT.md`
§2: appearance is not a curtain in front of the noumenon,
appearance *is* how the noumenon is structured for a perspective.

A pattern-stable want is real because it coheres — and coherence
is the only reality the framework recognizes. The "stability" in
`PatternStableWantable` is Rorty-honorific in form
(real-for-some-purpose) without being deflationary in content (the
purpose is being a particular at all).

## 10. Catalog entry

- **Tier**: bridges Tier 1 (Hardy reconstruction) and Tier 1.5
  (complex Hilbert space).
- **Honesty band**: (c) plausible but unchecked — concrete enough
  to attempt in Lean, but not attempted yet.
- **Dependencies**: requires nothing beyond current
  `Perspectival/Ontology.lean`. The proposed diff is four lines and
  purely additive.
- **Falsification path**: if formulation (a) is in place and the
  candidate theorem `A2_from_pattern_parsimony` (see
  `HARDY_A2_AS_PARSIMONY.md` §4) still cannot be proved, then either
  (a) is too weak (escalate to (b) + (c)) or A2 is not actually
  derivable from Axiom IV alone, and CDP-style purification (as a
  separate refinement of Axiom III) should be pursued instead.
- **Cross-reference**: `HARDY_A2_AS_PARSIMONY.md` (motivation);
  `TIER1_5_HILBERT.md` (downstream consumer); `Perspectival/
  Ontology.lean` (the four-line addition site).
