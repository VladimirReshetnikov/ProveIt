# Lean formalization plan and source audit

## Status

`Outline.lean` is an **uncompiled outline**. It contains finite data definitions,
theorem specifications, the form of the internal iPRA target, and a conditional
translation to the native calculus. It does not contain the completed internal
proof of any isoperimetric theorem. No Lean or Lake executable was available
on PATH in this session. There are no added axioms or `sorry` declarations;
that fact does not establish the theorem specifications.

The human mathematical arguments are in the accompanying report. The Lean
work below is still required to turn those arguments into kernel-checked
derivations in the particular first-order iPRA theory.

## Pinned repository

The inspected ProveIt snapshot is commit
`22afac4c9db7a0e060c081cc11db0dc96fe59e93`.

- Toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Root `lakefile.toml` declares the `ConciseIPRA` library with source directory
  `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.

Inspected APIs:

| File in `ConciseIPRA/Lean/ConciseIPRA/` | Actual relevant content |
|---|---|
| `Syntax.lean` | Scoped first-order formulas `Fm`; `Fm.QF` recognizes formulas without quantifiers. |
| `Deduction.lean` | Intuitionistic natural-deduction judgment `Prf Ax Γ φ`; substitution and weakening are derived. |
| `PR.lean` | Primitive-recursive symbol syntax `PR`, terms `PTm`, theory `PRAAx`, and rule `PRA.qfInd`. |
| `TeqRec.lean` | Primitive recursion derived in the scalar equational presentation using paired accumulators. |
| `NativeBiInterpretation.lean` | `pra_iff_native`, `native_iff_pra`, round trips, and equiconsistency. |

Direct pinned source prefix:

<https://github.com/VladimirReshetnikov/ProveIt/tree/22afac4c9db7a0e060c081cc11db0dc96fe59e93/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA>

The existing package
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/geometry/isoperimetric_ipra/`
contains a previous sharp planar human proof, rational diagnostic scripts,
and uncompiled Lean blueprint. Its README was inspected and its proof
architecture is explicitly distinguished from a completed formal derivation.
The present package's planar contribution is developed in its own report;
repository placement alone is not used as evidence that the old package's
universal theorem has been machine checked.

## Three distinct layers

1. **Finite executable specification.** `Polygon`, upper edge lengths,
   rational support coefficients, rational boxes, and vertex masks are
   finite data. Lists of rationals are convenient external Lean objects.
2. **Internal arithmetic theorem.** Every datum is encoded by a natural;
   every fixed checker is compiled to a specific `PR 1` symbol. The main
   result must be an inhabitant of

   ```lean
   Prf PRAAx [] (checkerFormula checker.symbol)
   ```

3. **Interpretation of presentations.** A curve or region means the fixed
   numerical approximation program and its certified error bounds described
   in the report. A theorem for such a presentation is a first-order schema
   after fixing the program. Quantification over arbitrary Lean functions
   `Nat → Rat`, `Real`, or `Set (EuclideanSpace ...)` is not an iPRA theorem.

A Mathlib proof of an inequality is useful for checking algebra and geometry,
but cannot be fed to `pra_iff_native`. That theorem takes an internal
`Prf PRAAx` derivation. Likewise, a Python test returning true on every tested
input supplies no such derivation.

## Concrete coding convention

The following elementary convention suffices; replacing it by a repository
codec requires proving the corresponding conversion laws.

- Encode an integer `z` by `2z` for `z ≥ 0` and `2(-z)-1` for `z < 0`.
- Encode a rational by a signed numerator and a positive natural denominator.
  Reduced fractions are optional. Equality and order are checked by cross
  multiplication; addition and multiplication keep positive denominators.
- Pair naturals by `pair(a,b)=(a+b)^2+a`. Decode by scanning pairs `a,b ≤ n`
  in a prescribed order and return `(0,0)` when no pair encodes `n`.
  The pairing is injective. Every coordinate of an encoded pair is bounded
  by its code, so decoding is primitive recursive.
- Encode the empty list by `0` and `a :: xs` by `1+pair(a,code(xs))`.
  A decoder takes its fuel from the input code; every tail code is strictly
  smaller, and a length-bounded decoded sequence can be produced by ordinary
  primitive recursion on that fuel. No unbounded minimization is involved.
- Encode a polygon as a list of pairs of rational codes, box endpoints as
  lists of length `d`, and the coefficient family as a list of rational pairs.
- In the `d`-cube, bit `v` of a natural mask says whether vertex `v<2^d`
  lies in the set. Bits beyond `2^d` are ignored, or are rejected by a
  well-formedness check; choose one convention and prove it preserves counts.

The full specification must preserve invalid-input behavior: the closed
checker equation expresses an implication. Invalid input or false hypotheses
therefore yield `0`, just as a valid input satisfying the conclusion does.
This convention does not allow an arbitrary constantly-zero replacement:
`CompiledChecker.semantics` must identify the symbol with the stated checker,
and its defining arithmetic equations must be available internally.

`evalPR` in the outline is an external semantics defined by recursion on a
Lean syntax tree. It is not a primitive-recursive universal interpreter for
all primitive-recursive programs. Each algorithm is compiled separately.

## Exact finite targets

### Polygon target

For rational vertices `p`, nonnegative rational upper lengths `u`, and
precision `k`, establish

```text
if normSq(edge_i) ≤ u_i² for every i,
then 4*piLower(k)*abs(signedArea(p)) ≤ sum(u)² + 2^(-k).
```

The chosen `piLower` routine must come with a separately proved enclosure
theorem. The exact finite spectral identities and refinement bounds in the
report establish the checker equation. Translation, orientation reversal,
and edge subdivision are first proved as finite identities.

### Triangle target

Define

```text
H = 2*a²*b² + 2*b²*c² + 2*c²*a² - a⁴ - b⁴ - c⁴.
```

For nonnegative side lengths satisfying the triangle inequalities, prove

```text
27*H ≤ (a+b+c)^4,
H³ ≤ 27*(a*b*c)^4.
```

Since `H=16*T²` for geometric area `T`, these imply the two radical
inequalities in the article without any irrational comparisons in the
checker. Equality and strictness reduce to the explicit polynomial
nonnegativity decompositions in the human proof.

### Support functions and Wigner caustics

Store the finite real Fourier coefficients as rational pairs. After dividing
by the known positive power of π, the essential deficit is the rational sum

```text
sum_{n≥2} (n²-1)*(a_n²+b_n²).
```

Split it into even and odd modes. The circle equality criterion deletes all
modes `n≥2`; the constant-width equality criterion deletes the even modes.
The factor from the double covering of the Wigner caustic must be stated and
proved before identifying the odd-mode expression with geometric area.
For infinite supplied presentations, all tail estimates are explicit input
data and their use must be traced in each finite-precision theorem.

### Rational-box Brunn--Minkowski target

For dimension `d>0`, nonempty finite rational box unions `X,Y`, and rational
`q≥0`, with `a=vol X>0`, `vol Y>0`, and `q^d*a≤vol Y`, prove

```text
vol(X+Y) ≥ a*(1+q)^d.
```

The union-volume routine first sorts all coordinate endpoints, forms the
elementary grid cells, and retains occupied cells. The sum of the pairwise
Minkowski-box volumes is not the union volume; the dissection step is
essential. Primitive-recursive bounds for endpoint sorting and grid
enumeration follow directly from the finite input lengths.
The positive-volume premise for `Y` is essential when `q=0`: an empty `Y`
would satisfy the numerical hypothesis but its Minkowski sum would be empty.

The matched-cut recursion in the report should be encoded as a bounded
computation tree with the number of boxes in each child problem as its
decreasing measure. The total number across both children need not decrease.
Choose a cut separating two whole boxes in one input: each child then has
at most one fewer box from that input, while the matched cut creates at most
one piece of each box in the other input in each child. Prove
at every node: the rational volume ratio and parameter `q` are preserved,
the child volumes add to the parent volume, and the Minkowski sum pieces
used for the lower bound are disjoint up to grid-cell boundaries. These are
the invariants needed for the internal proof; merely implementing cuts is
insufficient. A queue construction with at most `2^(m+n+1)` iterations
records the whole cut tree. Then process that recorded tree bottom-up,
maintaining a Boolean conjunction of the inequalities at all processed
nodes. This uses a quantifier-free invariant. Do not use an internal
induction formula quantifying over all unbounded rational input codes.

The higher-dimensional isoperimetric consequence additionally needs the
report's certified inner box approximants, ball approximants, and explicit
one-sided upper bound on the volume of the outer parallel set. The outline
exposes an `OuterVolumeData` interface but does not construct these data from
an arbitrary set. An actual geometric perimeter theorem must verify the
interface's relationship to that perimeter.

### Hypercube targets

Use bounded sums to count vertices, internal edges, and boundary edges.
The exact logarithm-free edge target is

```text
2^(2*internalEdges(d,S)) ≤ card(S)^card(S),
d*card(S) = 2*internalEdges(d,S) + edgeBoundary(d,S).
```

The convention `0^0=1` covers the empty set. For nonempty sets, interpreting
the first inequality via increasing logarithms gives the displayed article
inequality. The internal arithmetic theorem itself needs no logarithm.

For the Harper threshold statement, prove

```text
card(S) ≥ sum_{i=0}^r choose(d,i)
  ⇒ card(closedNeighborhood(S)) ≥ sum_{i=0}^{r+1} choose(d,i).
```

The full compression theorem uses the simplicial order: increasing Hamming
weight, then lexicographic order with `1` before `0`. Its initial segments
and rank function are computed by enumerating the finite cube. The rank-sum
potential is bounded by `2^(2*d)`, so a saturated coordinate compression is
obtained after that many iterations, with identity steps after saturation.
The exceptional compressed families and low dimensions are handled by the
finite lemmas in the report. This bound makes the algorithm primitive
recursive but does not by itself prove its boundary monotonicity.

## Internal induction discipline

`PRA.qfInd` admits quantifier-free formulas only. A bounded universal is first
converted to a primitive-recursive Boolean fold with value `1` exactly when
all its entries pass. A bounded existential is a bounded search with an
explicit witness or failure flag. Prefix conjunctions are maintained as
numerical invariants. When induction needs all prior stages, keep a finite
table of their Boolean invariants, using the explicit bound specified for
the problem. The internal induction formula is then an equality between
primitive-recursive terms.

In particular, do not use induction on the statement “for every real curve
...”, an unbounded arbitrary-input universal, or an unbounded existential.
For dimension induction in the cube, quantify over masks below
`2^(2^d)` inside a bounded Boolean fold. For a fixed precision geometric
proof, include all input-code and intermediate-certificate bounds explicitly.
The unbounded universal closure is introduced only after the internal
quantifier-free derivation with parameters is complete.

## Recommended module order

1. `Codecs`: total number encodings, bounded lists, rational arithmetic.
2. `OrderedArithmetic`: internal ordered integer/rational lemmas and finite
   sum/product induction macros.
3. `ElementaryConstants`: fixed square-root, trigonometric, and π interval
   algorithms actually used by the chosen finite proof.
4. `PolygonCore`: shoelace identities, subdivision, finite spectral estimate,
   explicit finite-precision polygon inequality.
5. `SupportCore` and `TriangleCore`: exact coefficient and polynomial proofs.
6. `BoxCore`: endpoint dissection, rational cuts, finite Brunn--Minkowski.
7. `CubeCore`: count recurrences, edge inequality, coordinate compressions,
   Harper threshold theorem.
8. `PresentationTransfer`: separately fixed PR curve/region presentations and
   all modulus-based estimates from the report.
9. `InternalTheorems`: inhabitants of `Prf PRAAx [] ...` for the concrete
   compiled checkers; only then invoke `pra_iff_native`.
10. `Audit`: `#print axioms` for each final ambient theorem, a list of every
    actual internal proof target, and the successful build transcript.

To elaborate the outline in the pinned repository, copy it into a module
under the declared `ConciseIPRA` library (or register a separate library with
the same dependencies), run `lake build ConciseIPRA`, and then
`lake env lean PATH/TO/Outline.lean`. Resolve any elaboration issues before
reporting successful compilation. A separate library is preferable for the
eventual full development, to keep the foundational calculus independent of
the geometric development.
