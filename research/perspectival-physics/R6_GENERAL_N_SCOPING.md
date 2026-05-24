# R6 General-n Disconnect: Scoping Note

**Subject:** Technical feasibility of extending the R6 classical-agency
disconnect theorem from `n = 2` to general `n ≥ 3` in Lean 4 + Mathlib.

**Status:** Scoping only. No Lean code changed. No commits.

**Cross-references:**
- Existing n=2 theorem: `classical_n2_strict_reversible_path_id_swap_empty`
  in `/root/perspectival-physics/Perspectival/Classical.lean` (around
  line 882).
- Roadmap entry: R6 ("Forcing path-connectedness from agency"), with R7
  ("Lie-group refinement") as immediate downstream.
- Mathlib infrastructure: `Continuous.matrix_det`,
  `Equiv.Perm.permMatrix`, `Matrix.det_permutation`,
  `Matrix.doublyStochastic`, `Matrix.extremePoints_doublyStochastic`
  (Birkhoff–von Neumann), `LinearMap.det_toMatrix`.

---

## 1. Target statement (n ≥ 3)

For Classical `n`-outcome GPT and any two permutations `σ τ : Equiv.Perm
(Fin n)` of opposite sign (i.e. `Perm.sign σ ≠ Perm.sign τ`):

> **Theorem (target).** There is no continuous family of bijective
> state-preserving linear maps `γ : unitInterval → V n →ₗ[ℝ] V n`
> with `γ 0 = σ.permMatrix.toLin'` and `γ 1 = τ.permMatrix.toLin'`,
> all bijective along the path.

Equivalently (the existence-free packaging used in the n=2 case):

```lean
theorem classical_general_strict_reversible_path_even_odd_empty
    (σ τ : Equiv.Perm (Fin n)) (hsign : Perm.sign σ ≠ Perm.sign τ)
    (p : StrictReversiblePath (gpt n)
            (permStrictReversible σ) (permStrictReversible τ)) :
    False
```

Specialization recovers `n=2` (id vs swap) and yields immediately for
`n=3` the six-element split: `{id, (012), (021)}` (even, det = +1) vs
`{(01), (02), (12)}` (odd, det = −1).

This is exactly the topological fact that `GL(n, ℝ)` has two connected
components, restricted to its discrete intersection with the Birkhoff
polytope = `S_n` (Birkhoff–von Neumann), with `det` (a continuous
function valued in `{+1, −1}` on permutation matrices) as the
sign-changing invariant along any path through `GL(n, ℝ) ∩
doublyStochastic`.

---

## 2. Mathlib infrastructure survey

The relevant pieces all exist in current Mathlib:

| Need | Mathlib lemma / def | File |
|---|---|---|
| Determinant of a matrix | `Matrix.det` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| Continuity of det over `ℝ` | `Continuous.matrix_det` (line 205) | `Mathlib/Topology/Instances/Matrix.lean` |
| Permutation matrix | `Equiv.Perm.permMatrix` | `Mathlib/LinearAlgebra/Matrix/Permutation.lean` |
| det of perm matrix = sign | `Matrix.det_permutation` (line 64): `det (σ.permMatrix R) = Perm.sign σ` | same file |
| Sign of identity / swap | `Equiv.Perm.sign_one = 1`, `sign_swap = -1` | `Mathlib/GroupTheory/Perm/Sign.lean` |
| Matrix↔LinearMap bridge | `Matrix.toLin'`, `LinearMap.toMatrix'`, `LinearMap.det_toMatrix`, `Matrix.det_toLin'` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean`, `Mathlib/LinearAlgebra/Determinant.lean` |
| det = 0 ⇒ not injective | `Matrix.isUnit_iff_isUnit_det`, `ker_toLin_eq_bot`, `det_ne_zero_of_left_inverse` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`, `ToLinearEquiv.lean` |
| Doubly stochastic matrices | `Matrix.doublyStochastic` | `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean` |
| Birkhoff–von Neumann | `Matrix.extremePoints_doublyStochastic`, `doublyStochastic_eq_convexHull_permMatrix` | `Mathlib/Analysis/Convex/Birkhoff.lean` |
| GL(n, R) | `Matrix.GeneralLinearGroup` (`GL n R`) | `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` |
| IVT on connected images | `IsPreconnected.ordConnected` (already used at line 763 of `Classical.lean`) | `Mathlib/Topology/Connected/Basic.lean` |

Notably absent — and **not required for the disconnect direction**:
- No need for Birkhoff–von Neumann itself; we only need that
  permutation matrices ⊂ doubly stochastic ⊂ matrices, and `det` is
  continuous on the ambient space.
- No need for Lie group structure; that's R7.

The pieces we *do* need that aren't off-the-shelf:
- A converted `n2_disc_det`-style invariant that reads
  `det (γ t : V n →ₗ[ℝ] V n)`, going through `LinearMap.toMatrix'`.
  This requires choosing the basis explicitly (the standard basis on
  `Fin n → ℝ`) and tracking that `(γ t).toMatrix' = M(γ t)` where
  `M(γ t) i j = (γ t) (vertex j) i`. Straightforward once written
  carefully.

---

## 3. Proof sketch (structural analogue of n=2 chain)

The n=2 proof has the shape:

```
n2_disc_det : (V 2 →ₗ V 2) → ℝ              -- the invariant
n2_disc_det_id = 1                          -- value at id
n2_disc_det_swap = -1                       -- value at swap
ivt_path_one_to_neg_one                     -- IVT on [-1, 1]
n2_disc_det_zero_implies_not_injective      -- det = 0 ⇒ ¬injective
n2_disc_det_path_continuous                 -- continuity from joint continuity
⇒ classical_n2_no_strict_path_id_to_swap
```

For general n, replace `n2_disc_det` with the actual determinant of the
matrix representation:

```
detLin (R : V n →ₗ[ℝ] V n) : ℝ := Matrix.det (LinearMap.toMatrix' R)
  -- equivalently: LinearMap.det R, via det_toMatrix'

detLin_permLin σ : detLin (Matrix.toLin' σ.permMatrix) = (Perm.sign σ : ℝ)
  -- via det_toLin' + det_permutation; cast Units ℤ → ℝ

detLin_continuous_of_joint  : Continuous (fun t => detLin (γ t))
  -- compose Continuous.matrix_det with the matrix-entry continuity,
  -- itself coming from n_vertex_coord_continuous_of_joint (already
  -- in Classical.lean line 1779)

detLin_zero_implies_not_injective :
    detLin R = 0 → ¬ Function.Injective R
  -- via Matrix.isUnit_iff_isUnit_det.not + ker_toLin_eq_bot contrapos

ivt_path_one_to_neg_one (already in file) applied at heights ±1
  → path passes through detLin = 0
  → bijectivity fails
  → contradiction with hbij.
```

The general-n disconnect is exactly the n=2 proof with `n2_disc_det`
swapped for `LinearMap.det` (or `Matrix.det ∘ toMatrix'`). The
"discrete sign" structure of `Perm.sign : Perm n → ℤˣ` (image
`{+1, -1}`) gives the two endpoint values for any (even, odd)
permutation pair.

Two technical wrinkles, both surmountable:

(a) **State-preserving ⇏ doubly stochastic in column form.** Our `V n
= Fin n → ℝ` with `unitFn = ∑ i, x i` makes states the standard
simplex, and a state-preserving linear map's matrix (in the standard
basis) is *column-stochastic* (each column sums to 1; entries
nonneg). Mathlib's `doublyStochastic` requires both row and column
sums = 1. We only need the column-stochastic side for the disconnect
argument; `Matrix.colStochastic` (`Mathlib/LinearAlgebra/Matrix/
Stochastic.lean`) is the right object. The disconnect theorem does
NOT need Birkhoff — we only need: "a continuous path of bijective
column-stochastic matrices preserves sign of det". So `colStochastic`
+ `Continuous.matrix_det` suffices.

(b) **Sign as ℝ vs as ℤˣ.** `Perm.sign σ : ℤˣ` and `det _ : ℝ`. Cast
via `Int.cast (Perm.sign σ : ℤ)`. `Matrix.det_permutation` returns
the cast properly when the ring is ℝ. Minor bookkeeping.

---

## 4. Effort estimate

| Item | Lines | Difficulty |
|---|---|---|
| `detLin : (V n →ₗ V n) → ℝ` def + `detLin_eq_Matrix.det` | 20 | trivial |
| `detLin (matrix of perm) = ±1` (3 lemmas: id, swap, general σ) | 40 | easy (just `det_permutation` + cast) |
| `detLin_continuous_of_joint` from existing `n_vertex_coord_continuous_of_joint` | 30 | easy (compose `Continuous.matrix_det` with `continuous_pi` of entry continuity) |
| `detLin_zero_implies_not_injective` | 30 | medium — need `LinearMap.det_eq_zero_iff_not_injective` or build from `Matrix.isUnit_iff_isUnit_det` + `ker_toLin'_eq_bot` |
| General-n `permLin σ : V n →ₗ V n` and its `StrictReversible` packaging | 80 | medium (analogous to `swapLin`/`cyclicShiftLin` but parametrized by `σ`) |
| Main theorem `classical_general_strict_reversible_path_even_odd_empty` | 60 | easy once pieces in place |
| Wiring + corollaries (no `StrictConnectedAgency` containing both an even and an odd `permLin`) | 50 | easy |
| **Total** | **~300 lines** | **medium overall** |

**Bottleneck:** the matrix-representation `LinearMap.toMatrix'` ↔
`Matrix.toLin'` bookkeeping. Specifically, proving the equality
`(LinearMap.toMatrix' R) i j = R (Pi.single j 1) i` (or equivalently
`= R (vertex n j) i`) and that for `R = permLin σ` this matrix is
exactly `σ.permMatrix`. This is well-trodden in Mathlib but requires
~50 lines of careful unfolding. Once that bridge is in place,
`Matrix.det_permutation` and `Continuous.matrix_det` do all the heavy
lifting.

A secondary concern: `LinearMap.det_eq_zero_iff_not_injective` doesn't
exist as-named in Mathlib; one constructs it from `LinearMap.det`'s
relation to `IsUnit` via finite-dimensional structure
(`LinearMap.isUnit_det` family). Adds ~30 lines.

**Verdict on effort:** ~250–400 lines, dominated by API plumbing
between `LinearMap` and `Matrix`. No deep mathematics. The n=2 proof
is 250+ lines for a *single instance*; general n at ~300 lines
*subsumes* it and is cleaner.

---

## 5. In scope for current session?

**Recommendation: DEFER to a dedicated R6-completion session.**

Reasons:

1. **Net-positive but not net-urgent.** The n=2 case already
   *establishes* the framework-distinctive content (R6 disconnect
   between Classical agency and quantum agency). The n ≥ 3 extension
   is a generality strengthening, not a new conceptual result.
   `STATUS.md` should already record n=2 as the load-bearing R6
   anchor.

2. **Right-sized as a focused task.** ~300 lines is one solid session.
   Mixing it with other R6 / R7 work in a single session risks
   half-finished plumbing that leaves the build broken.

3. **R7 is the more valuable next step.** R7 (Lie-group refinement)
   is what distinguishes the framework's predictions for *quantum*
   agency. Once R6 n=2 + structural prediction for general n is on
   record, the marginal value of the formal general-n disconnect is
   smaller than the marginal value of starting R7's connected-Lie-
   group bridge to U(N).

4. **Tractable any time.** Nothing about the general-n disconnect is
   gated on philosophical progress, Mathlib evolution, or other
   unresolved scope. It can be picked up whenever a session
   specifically targets "polish R6 to general n" — for instance, in
   the run-up to the paper draft, where general-n is more rhetorically
   useful than n=2.

**Tractable later** (label, not "blocked"): all infrastructure exists;
this is a writing-up task, not a research task.

---

## 6. Cross-reference to R7 (next step after R6)

R7 in `ROADMAP.md` strengthens `HasConnectedAgency` to a Lie-group
postulate. The relevant interface from R6 general-n to R7:

- **R6 (general n) output:** for any `n`, the set of bijective
  state-preserving linear maps on Classical `V n` decomposes
  into n! discrete connected components (one per permutation),
  each a single point (since the bijective state-preserving locus
  consists exactly of permutation matrices when restricted to the
  vertex action — *this* is where Birkhoff–von Neumann
  (`Matrix.extremePoints_doublyStochastic`) would actually be
  needed if we wanted the *exact* characterization, not just
  disconnect).
- **R7 input:** the *quantum* analogue replaces this discrete S_n
  with U(n) (or for real Hilbert space, O(n)), which is a
  **connected compact Lie group**. The framework predicts that
  `StrictConnectedAgency` is satisfiable only by Lie-group-shaped
  transformation sets, ruling out classical GPTs at the agency-axiom
  level.

The R7 build will need:
- `Matrix.GeneralLinearGroup` (in Mathlib).
- `LieGroup` (Mathlib `Mathlib/Geometry/Manifold/Algebra/LieGroup.lean`).
- Connectedness of `U(n)` (Mathlib has `unitaryGroup` and surrounding
  topology; check `Mathlib/LinearAlgebra/UnitaryGroup.lean` and
  `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` for path-
  connectedness; this may itself be partial in Mathlib).

The R6 general-n result is **not a prerequisite for R7**; they are
parallel strands. R6 nails down the classical side; R7 nails down the
quantum side. They jointly give the framework's classical-vs-quantum
dichotomy at the agency-axiom level.

**Concrete handoff:** when R6 general-n is formalized, expose two API
lemmas R7 will rely on:

```lean
-- "Classical strict-connected agency is trivial."
theorem classical_strict_connected_agency_is_trivial
    (A : StrictConnectedAgency (gpt n))
    (R : StrictReversible (gpt n)) (hR : R ∈ A.avail) :
    R.toLin = LinearMap.id

-- "Permutation reversibles of different signs are not in the same
-- StrictConnectedAgency."
theorem classical_no_mixed_sign_strict_agency
    (A : StrictConnectedAgency (gpt n))
    (σ τ : Equiv.Perm (Fin n)) (hsign : Perm.sign σ ≠ Perm.sign τ)
    (hσ : permStrictReversible σ ∈ A.avail)
    (hτ : permStrictReversible τ ∈ A.avail) :
    False
```

The first is the *strongest* form (everyone's identity); the second
is the direct disconnect. The second follows immediately from the
disconnect proof. The first requires also showing bijective
state-preserving ⇒ permutation matrix (which *does* need
`Matrix.extremePoints_doublyStochastic`, i.e. genuinely Birkhoff–von
Neumann). That stronger form is a natural follow-on (~150 more lines)
and is the right "final R6 deliverable" before crossing to R7.

---

## Bottom line

- Statement of the target is unambiguous and uses standard Mathlib
  notions.
- All required Mathlib pieces exist.
- Effort: ~300 lines for the disconnect; ~450 lines including the
  full "classical strict agency = trivial" characterization.
- Bottleneck is `LinearMap ↔ Matrix` plumbing, not mathematics.
- Recommend deferring to a dedicated session; not on the critical path
  given n=2 already establishes the framework-distinctive content.
- R7 (Lie group / U(n) connectedness) is the higher-leverage next
  step; R6 general-n is a polish task best done in the paper-draft
  run-up.
