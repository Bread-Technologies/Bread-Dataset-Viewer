# MULLER_DIVERGENCE — Algorithmic Idealism and the Perspectival Reconstruction

Position note for the companion paper. Scope: where the present
framework agrees with, extends, and diverges from Markus Müller's
algorithmic idealism (Müller 2020, arXiv:2001.07411; Müller 2024,
*Foundations of Physics*). Citations are paraphrased — Müller is
cited as "argues" / "claims" rather than verbatim. The posture is
collaborative: the divergence is productive, and post-stabilization
co-authorship is a live option (ORIGINAL_PROMPT §10).

## 1. Substantial Agreement

The two programs share more than they differ on. In particular:

1. **Observer-centric ontology.** Müller argues that the fundamental
   posit of physics is not a third-person external world but the
   first-person sequence of observations of an observer. The
   perspectival framework's Axiom I — "to exist is to instantiate a
   perspective with directedness" — is a strictly stronger version of
   the same move. Both reject the view that the third-person world is
   ontologically prior to the first-person stance.

2. **Algorithmic / Solomonoff substrate.** Müller takes algorithmic
   information theory and Solomonoff's universal prior as the formal
   engine: given an observer's past, the probability of the next
   observation is fixed (up to UTM choice) by a universal prior over
   computable continuations. The framework treats this as a
   legitimate engine for prediction-conditional-on-perspective; the
   Lean GPT/Wantable bridge is intended to be compatible with, and
   eventually reducible to, an algorithmic-prior structure on
   perspective-trajectories.

3. **First-person primacy of "what should I believe to experience
   next."** Both reorient the foundational question away from "what
   is the world made of?" toward "given my present perspective, what
   should I expect next?". The perspectival framework adds that the
   *asker* is itself a stable perspectival pattern (Axiom IV), not a
   substantial subject.

4. **No substantial external world.** Müller argues that ordinary
   physical-world talk is a derived compression of the observation
   stream rather than a description of stuff behind it. The framework
   agrees: apparent particulars are stable patterns within the
   structure of meetings, not substances behind them (Axiom IV).

The agreement is deep enough that the present framework can fairly
be described, in one aspect, as algorithmic idealism *plus a
specific refinement of the observer*.

## 2. Points of Divergence

### 2a. Free will: rejection of compatibilism

Müller 2024 endorses a Dennett-style compatibilism in a footnote,
treating agency as functional/emergent rather than as a fundamental
posit. The present framework rejects this concession. The rejection
is not ornamental; it is load-bearing.

The technical issue is this. On compatibilism (Dennett 2003,
*Freedom Evolves*), agency reduces to the causal structure of the
substrate — neural causation supporting counterfactual sensitivity,
deliberation, and rational responsiveness. Wegner 2002 (*The
Illusion of Conscious Will*) goes further and treats the felt sense
of agency as post-hoc confabulation; the framework rejects Wegner as
well. Compatibilist agency, in either form, is a *property* of an
antecedently specified causal structure — not constitutive of the
perspective.

The framework's libertarian agency, by contrast, is constitutive.
Axiom IV identifies the chooser, at the moment of choosing, with the
perspectival structure itself — not a homunculus inside it, not the
causal history producing it. This is closer in spirit to van Inwagen
1983 (*An Essay on Free Will*) than to Dennett, though van Inwagen's
"agent causation" is hosted by a substantial agent, which the
framework refuses. The position is therefore *libertarian without a
substantial chooser*: each instant chooses with the full weight of
choice; the chooser is the perspectival clearing at that instant.

This matters because of the agency strengthenings in the Lean
development. The R6 / R7 strengthenings — in particular
`StrictConnectedAgency` (state-preserving *and* bijective
transformations with a connectedness condition over the available
agency-class) — license the move from a generic GPT to reversible
group-structured dynamics. The argument: if the chooser is
constitutive of the perspective, the available transformations must
be *closed under genuine choice* (not merely under causal
succession), forcing group structure rather than a mere monoid or
convex structure. On the compatibilist reading the availability set
is whatever the substrate happens to make available, which need not
be group-closed and need not yield reversibility. Compatibilism
cannot motivate `StrictConnectedAgency` *as an axiom*; at best it can
be assumed phenomenologically. Conjecturally, this is precisely what
is needed to recover quantum-like Lie-group reversible dynamics from
the agent-centric axioms — see §4.

### 2b. UTM selection: Hayekian clearing of UTMs

Müller leaves the choice of universal Turing machine open, treating
the UTM-dependence of Solomonoff probabilities as a residual
parameter. The framework offers a structural suggestion. Axiom III
(market structure of wanting) treats reality as the clearing of
complementary directednesses — Hayek's distributed-knowledge
argument generalised from prices to wants. Applied to UTM
selection: there is no privileged UTM; what is realized at a
perspective is a *clearing* over UTMs weighted by the local market
of wants, in the same sense in which a market-clearing price vector
is not the verdict of any single participant. This is a
suggestion, not yet a theorem; it predicts that UTM-dependence in
the algorithmic prior should be physically realized as residual
fine-structure in the perspective's transition statistics, with the
dependence structure of residual price dispersion in a Hayekian
market.

### 2c. Computational primacy: bit-strings vs. Wantable types

Müller takes bit-strings (finite observation histories over a
finite alphabet) as the fundamental datum on which the universal
prior is defined. The framework takes `Wantable` — a type with an
involutive complement (Axiom II) — as fundamental, with bit-strings
recovered as the special case of a two-element Wantable. The
contention: the complement structure is not optional furniture.
Without it there are no meetings (Axiom III), and without meetings
no event-structure to predict over. Bit-strings can be retrofitted
with a complement, but free-standing AIT does not exhibit the
relational core of Axiom II. The relationship is therefore
bit-string AIT ⊂ Wantable-AIT, with strict inclusion when the
complement structure is non-trivial (n-valued Wantable for n > 2;
continuous Wantable). See `DEPS.md` and `FINDINGS.md`.

## 3. Principled Rejection of Compatibilism

To be explicit about the three-way distinction:

- **Dennett 2003**: physical determinism is retained; free will is
  the emergent functional capacity for rational, counterfactually
  sensitive self-control. Free will is *real* but *reducible*.
- **Müller 2024**: physicalism is itself replaced by an
  observation-stream ontology, but Dennett-style compatibilism is
  imported as the account of agency. This is a *category match
  failure*: a non-physicalist ontology does not need a
  physicalism-rescue account of agency.
- **Framework**: physicalism rejected, *and* compatibilism rejected,
  *because the rescue is unnecessary*. With perspective as
  fundamental and agency constitutive of perspective, there is no
  determinism to be rescued from. Libertarian agency without a
  substantial chooser is the consistent completion.

The framework's quarrel with Müller is therefore narrower than its
quarrel with Dennett. Against Dennett: the metaphysics is wrong.
Against Müller: the metaphysics is largely right, but a vestigial
compatibilism has been imported where it does no work and obstructs
the agency strengthenings needed to recover quantum dynamics.

## 4. Libertarian Agency as a Testable Technical Commitment

The framework's libertarian agency is not an idle philosophical
preference. It is what licenses `StrictConnectedAgency` and its
relatives in the Lean development. The conjectural reconstruction
chain is:

  Axiom IV (constitutive choice) ⇒ availability set closed under
  genuine choice ⇒ group structure on transformations ⇒ connected
  Lie group ⇒ reversible quantum-like dynamics.

Each arrow is a target for formal verification (see ROADMAP and
PAPER_DRAFT §§ on R6/R7). If the framework is wrong, this is where
it would be wrong: either the arrow from constitutive choice to
group-closure fails, or the empirical dynamics prove inconsistent
with the resulting group structure. The libertarian commitment is
therefore *risky* in Popper's sense — it has formal consequences
that can fail. This is the correct shape for a metaphysical
commitment in foundations of physics: it earns its keep by enabling
a derivation compatibilism cannot.

## 5. Collaborative Posture

The divergence is not antagonistic. Müller's program is the nearest
neighbour to the present framework in the contemporary literature
and the agreements in §1 are substantial. The framework extends
algorithmic idealism along one specific axis — replacing emergent
compatibilist agency with constitutive libertarian agency, plus
associated machinery (Wantable types, market-clearing UTM, agency
strengthenings). Per ORIGINAL_PROMPT §10, co-authorship with Müller
after results stabilise is on the table; the natural division is for
Müller's published algorithmic-idealism core to be cited as the
observer-centric substrate, with the framework contributing the
agency strengthenings and the perspectival refinement of the
observer. If the strengthenings deliver the conjectured quantum
reconstruction, the divergence will have proved productive; if not,
it will have failed informatively, and the framework will need to
retreat — possibly toward Müller's more cautious compatibilism,
possibly toward a different refinement of Axiom IV. Either way, the
right next step is to do the derivations and let them adjudicate.

## References

- Dennett, D. 2003. *Freedom Evolves*. Viking.
- Müller, M. 2020. "Law without Law: from observer states to
  physics via algorithmic information theory." arXiv:2001.07411.
- Müller, M. 2024. "Algorithmic idealism." *Foundations of
  Physics*.
- van Inwagen, P. 1983. *An Essay on Free Will*. Oxford UP.
- Wegner, D. 2002. *The Illusion of Conscious Will*. MIT Press.
