# Lean formalization: checked core and remaining object proofs

## Status and exact boundary

All ten standalone `.lean` targets named in `build.sh` compile with Lean **4.32.0**, using `Std`
and no Mathlib dependency.  They contain no `axiom`, `opaque`, or `sorry`
declaration.  This statement does not mean every mathematical theorem in the
article has already been formalized in object iPRA.

There are three deliberately distinct sorts of declaration.

1. `RankedDescent.lean` and `CoherentTower.lean` prove mathematical theorems in
   Lean about finite computations under their displayed hypotheses.  These
   are **host-level theorems**.  For an iPRA application their operations must
   have fixed PR codes and their local hypotheses must be derived in the
   object theory.  Neither condition follows just from successful compilation.
2. `ObjectComposition.lean` manipulates the actual repository judgment
   `Prf PRAAx Γ A`.  Contract composition, specialization, existential
   introduction, the induction adapter, and `identityIteration_proved` are
   **object-level proof constructions**.  Input proof fields are genuine
   obligations.  No constructor asserts their existence.
3. `DescentTargets.lean` defines concrete PR programs, formulas, and
   `RankedDescentGoal : Prop`.  It does **not** prove that goal.  Its successful
   compilation checks the target's types and the PR syntax, not the missing
   arithmetic proof transformation. `ApplicationTargets.lean`,
   `WeightedNormTargets.lean`, and `HurwitzTargets.lean` similarly define
   executable finite programs and complete application goals without
   asserting those goals as theorems.  `ApplicationChecks.lean` supplies
   separately labeled concrete checks.

The build log prints axiom dependencies.  `CoherentTower.coherent` and
`CoherentTower.unique` use no axioms.  The displayed arithmetic and
object-proof-construction theorems use only Lean's `propext` and `Quot.sound`;
they do not depend on `Classical.choice` or `sorryAx`.  These are dependencies
of Lean's metatheory, not additional axioms of `PRAAx`.

## Upstream object theory

`ObjectKernel.lean` concatenates the following files at ProveIt commit
`052fbaebfc955294b4c02f6532ab7e7a3f760f7a`:

| Upstream file | Git blob SHA |
|---|---|
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean` | `a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348` |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean` | `0969040f77fdd3ed9526e360e7a998584b4d9d8c` |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean` | `3251631592070d9ed3687cc0bf7dbd5eb452e46f` |

The original import lines are replaced by `import Std` and the compatibility
notation `ℕ => Nat`.  After removal of import lines and boundary whitespace,
each source section is identical to its pinned upstream file.  The original
source files are retained in `upstream/` for reproducibility; they are not
additional targets of the standalone build.  The repository license is
preserved as `LICENSE-ProveIt.txt`.

The object language is not a new arithmetic theory:

- `PR k` has zero, successor, projection, composition, and primitive-recursion
  constructors.
- `PTm n` contains terms with `n` free de Bruijn variables.
- `Fm PTm n` contains equality, falsity, conjunction, disjunction,
  implication, and the two first-order quantifiers.
- `Prf PRAAx Γ A` is intuitionistic natural deduction with equality over the
  defining equations, successor separation and injectivity, and
  **quantifier-free** induction.
- `PRA.qfInd` is the actual derived interface to that induction schema.

An arbitrary Lean proof of a proposition about `Nat` is not accepted as an
object proof by any adapter in this package.

## 1. Bounded descent core

`RankedProcess S` has a fixed transition `step`, a Boolean `terminal`, a
predicate `valid`, and a natural-number `rank`.  Its hypotheses state:

```
valid s -> valid (step s)
valid s -> terminal s = true -> step s = s
valid s -> terminal s = false -> rank (step s) < rank s
```

The computation `run p s n` is ordinary finite iteration.  The checked lemmas
are:

| Declaration | Meaning |
|---|---|
| `RankedProcess.valid_run` | Validity persists through every finite run. |
| `RankedProcess.budget` | Terminal at stage `n`, or `rank(run n)+n <= rank(s)`. |
| `RankedProcess.terminates` | `rank(s)` transitions suffice to reach a terminal state. |
| `RankedProcess.invariant` | Any supplied transition invariant survives the run. |
| `RankedProcess.terminal_stable` | A terminal state is unchanged by additional transitions. |
| `contraction_decreases` | `b*h' <= a*h+C`, `a<b`, `C <= (b-a)*B`, and `B<h` imply `h'<h`. |

The last statement connects quantitative height contraction to natural-number
descent.  It does not supply the height inequality or the PR presentation of a
group.  Those remain application-specific assumptions.

### Object encoding already supplied

`DescentTargets.lean` implements the following **syntax constructors**, not a
universal interpreter:

```
Code.pred          : PR 1
Code.isZero        : PR 1
Code.add           : PR 2
Code.sub           : PR 2
Code.le            : PR 2
Code.iterate step  : PR 2
Code.boundedRun step rank : PR 1
```

`Code.iterate step` has the recursion equations

```
iterate step 0 s       = s
iterate step (n+1) s   = step (iterate step n s)
```

and `Code.boundedRun step rank s = iterate step (rank s) s`.
The constructors exist uniformly as a metalevel operation on finite syntax.
There is no claim that iPRA has a total universal evaluator for all PR codes.

For `p : RankedSymbols`, `p.conclusion` is the following precise open object
formula in one free variable `s`:

```
valid(s)=1 -> terminal(boundedRun(step,rank,s))=1.
```

`RankedLocalCertificate p` contains proofs in `Prf PRAAx []` of validity
preservation, terminal Booleanity, absorption, and strict decrease.  Booleanity
is explicit because a general unary PR symbol is natural-valued; its outputs
cannot silently be assumed to be zero or one.

The remaining target is exactly:

```
RankedDescentGoal :=
  forall p : RankedSymbols,
    RankedLocalCertificate p -> Prf PRAAx [] p.conclusion
```

### Complete proof route to `RankedDescentGoal`

1. Derive the defining equations for `Code.pred`, `isZero`, `add`, `sub`, and
   `le` using `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`.  Prove the familiar
   ordered-semiring laws for these **specific** codes in the object theory,
   by quantifier-free induction.  Required order lemmas are transitivity,
   preservation under addition, successor order, and
   `a+n <= n -> a=0`.  No unrestricted formula induction is needed.
2. Use the defining equations of `Code.iterate` to derive its zero and step
   equations.  The construction pattern is exercised by the compiled
   `identityIteration_proved`, which produces an actual `Prf PRAAx` proof of
   the iteration of the identity from `PRA.qfInd`.
3. Keep the initial state `s` as a free parameter.  Instantiate `PRA.qfInd`
   with `p.budgetInvariant`, whose quantifier-free status is already checked.
   In mathematical notation it is

   ```
   valid(run(n,s))=1 AND
     [terminal(run(n,s))=1 OR rank(run(n,s))+n <= rank(s)].
   ```

   Base: `run(0,s)=s` and `rank(s)+0<=rank(s)`.
   Step: split only the **proved Boolean flag**.  If terminal, absorption
   preserves it; otherwise decrease and the old budget yield the new budget.
   Derive validity from the preservation certificate.  Every displayed
   formula is quantifier-free once the indicated codes are expanded.
4. Instantiate the induction result at the term `rank(s)`.  If the result is
   not terminal, the budget forces its rank to zero, while strict decrease
   demands a successor below or equal to zero.  The object arithmetic lemma
   and `PRAAx.succNeZero` give falsity.  Finish by the terminal Boolean split.
5. Discharge `valid(s)=1` by `Prf.impI`.  Optional universal closure uses
   `Prf.allI`; the induction invariant never contains that closure.

This is a finite proof-building task.  The current package gives the exact
syntax, PR constructors, local proof interfaces, and host proof; it leaves
the ordered-arithmetic library and its integration in steps 1--5 unfinished.

## 2. Object-level composition of witnessed contracts

For formulas `P(x)`, `Q(y,x)`, a `TermContract P Q` consists of a fixed term
`f(x)` and a derivation

```
[P(x)] |-iPRA Q(f(x),x).
```

Suppose a second contract derives `R(g(y,x),y,x)` from `Q(y,x)`.
The checked `TermContract.compose` performs capture-avoiding substitution
`y := f(x)` in that proof and cuts in the first proof.  Its witness is
`g(f(x),x)` and its postcondition is `R(z,f(x),x)`.  Hence it derives

```
[P(x)] |-iPRA R(g(f(x),x),f(x),x).
```

`TermContract.specialize` simultaneously substitutes any fixed terms for the
free parameters.  `existsOutput` and `asImplication` introduce the existential
result and discharge the precondition.  These are all actual constructions
inside the repository's derivation relation.  For an external tool producing
a certificate, use a separately proved checker soundness contract and compose
it here; a successful host check alone is not substituted for that proof.

## 3. Coherent finite lifting

`CoherentTower` separates local algebra from finite recursion.  It contains
levels `Level n`, restriction maps, admissibility tests, and a chosen `lift`.
The hypotheses say that restriction preserves admissibility, the lift
preserves admissibility and restricts to its input, and an admissible point
above a given admissible input is that lift.

`stage seed n` is the recursively chosen lift at level `n`.  The kernel checks:

```
stage_admissible : admissible 0 seed -> admissible n (stage seed n)
coherent : restrict n (stage seed (n+1)) = stage seed n
stage_base : toBase n (stage seed n) = seed
unique : admissible n x -> toBase n x = seed -> x = stage seed n
```

In the square-zero lifting application, the explicit Taylor calculation and
frozen inverse matrix supply `lift_admissible`, `restrict_lift`, and
`fiber_unique`.  This file proves the finite compositional step.  It does not
assert those algebraic contracts, the PR coding of a tower, or an infinite
inverse-limit object in iPRA.

### Object-iPRA route for the tower

Encode all levels and their elements by numbers.  Fixed PR functions carry
the level argument explicitly: validity, addition, multiplication,
restriction, chosen section, kernel coordinate, correction, and root test.
For jets, use coefficient lists; for residue towers, use canonical residues.
The next-stage computation is the displayed finite correction formula from
the article, encoded with bounded loops for polynomial and matrix operations.

Existence and adjacent coherence use a Boolean prefix accumulator recording
all local stage checks through the current index.  Its induction formula is
an equation of PR functions.  Initial matrix inverse equations are fixed
input certificates; they are not recomputed by unbounded search.

Uniqueness needs care: one must not translate the host induction as induction
on a formula with a fresh unbounded universal quantifier over candidates.
Instead fix the final index `N` and candidate `x` as parameters.  Compute the
finite list of successive restrictions of `x` down to level zero.  First
certify by a bounded fold that each restricted entry is a root.  Then use
quantifier-free induction on `k<=N` to compare the algorithm's stage `k` with
the stored candidate at that level.  The base is the seed equality; the step
is the proved fiber-uniqueness contract.  At `k=N` the desired equality follows.
No common bound on all rational coefficient values is required: the fixed
candidate's finite restriction list supplies the needed finite data.

## 4. Frozen-inverse lifting: complete application definitions

`ApplicationTargets.lean` uses actual finite arrays: `Vector R d` for a
point, `Vector (Vector R d) d` for a matrix, and a finite list of monomials
for a polynomial.  A monomial contains a coefficient in `R` and a
`Vector Nat d` of exponents.  A polynomial system is a vector of `d`
polynomials.  Dimensions therefore agree by type, rather than through an
undefined `WellFormed` assumption.  Duplicate monomials are permitted.

`RingOps` supplies zero, one, addition, negation, and multiplication.
`RingLaws` lists additive associativity and commutativity, additive identity
and inverse, multiplicative associativity and commutativity, multiplicative
identity, and distributivity.  All other ordinary ring identities follow
from these.  There is no nontriviality requirement because the lifting
argument also works over the zero ring.

`FiltrationLaws o member N` explicitly states zero-level universality,
descending membership, `F^N={0}`, zero membership, additive and negative
closure, and `F^i*F^j` containment in `F^(i+j)`.  `member` is a Boolean
function.  The input record adds `N>0`, the seed residual condition, and
both inverse congruences.  It contains **no root-existence or uniqueness
field**.  `frozenIter` is the exact finite program from the article.

The named goals are fully expanded in terms of these definitions:

| Goal | Content |
|---|---|
| `TaylorRemainderGoal` | The polynomial Taylor error belongs to `F^(2k)`. |
| `JacobianCongruenceGoal` | Inputs congruent modulo `F^1` have congruent Jacobians. |
| `PrecisionInvariantGoal` | Stage `r` stays over the seed and has residual in `F^(r+1)`. |
| `FrozenLiftingGoal` | Stage `N-1` is the unique root over the seed. |
| `EvaluationTransportGoal` | Finite polynomial evaluation commutes with a supplied homomorphism. |
| `LiftTransportGoal` | Produced roots agree under such a homomorphism and compatible seed classes. |
| `JetPresentationGoal`, `JetTruncationGoal` | The concrete jet operations have the required laws and truncation transport. |
| `ResiduePresentationGoal`, `ResidueProjectionGoal` | The concrete residue operations and projections have the required laws. |

To finish the host formalization, prove the ring identities once from
`RingLaws`, then establish finite product difference and Taylor remainder
identities by induction on each exponent and monomial list.  Induct on the
iteration count to prove `PrecisionInvariantGoal`.  At stage `N-1`, apply
the filtration's `vanishes` field.  For uniqueness hold two candidate arrays
fixed and induct on the level of their difference, exactly as in the human
proof.  The homomorphism goals follow by induction on the same finite
arithmetic expressions and then by uniqueness in the target ring.

For the object theory, replace `R` by a fixed PR number presentation,
carry validity and the presented equality relation explicitly, and compile
all finite array operations into fixed PR codes.  The records in this file
are host-level local contracts; obtaining their **object derivations** is
an additional task.  Booleanize the finite vector and matrix memberships.
The induction invariants in the article then instantiate `PRA.qfInd`.
No theorem in the file reflects arbitrary host `RingLaws` proofs into iPRA.

### Concrete representations

`Jet N = Vector Rat N`.  `jetOps N` adds and negates coordinates and
multiplies by the explicit truncated convolution.  `jetMember N k` checks
the first `min(k,N)` coefficients.  `jetConstant`, `jetVariable`, and
`jetTruncate` are concrete array constructors.  The latter is padded by
zero when asked for extra coordinates, but `JetTruncationGoal` requires
the mathematically appropriate `M<=N`.

The modular carrier is `Fin(q^N)`, with operations reduced modulo that
modulus.  The positivity proof passed to `residueOps` only makes this finite
type inhabited.  `residueMember q N k` tests divisibility by
`q^min(k,N)`.  Projection is reduction modulo a lower power.  Primality is
not required: the presentation goal assumes only `q>=2`.

`ApplicationChecks.compositeRoot_eq` is a kernel-reduced proof that the
implemented producer sends `q=4`, `N=3`, `P=X^3-X-2`, seed `2`, and frozen
inverse `3` to residue `22`.  Two `#eval` diagnostics additionally check
the Catalan jet `[1,1,2,5,14]` and a weighted norm.  Those executable
rational diagnostics are recorded as checks, not kernel theorems.

## 5. Weighted norm: explicit programs and exact remaining goals

`WeightedNormTargets.lean` represents an X-polynomial by a finite
low-degree-first list of rational coefficients.  A bivariate polynomial is
a list of those rows, indexed by Y-degree.  Coefficient access is total
with default zero.  Polynomial addition, negation, multiplication, powers,
evaluation, normalization, coefficientwise equality, nonzeroness, degree,
and divisibility are all defined explicitly.

`Curve` contains `m,d,c,lower`.  Its `assumptions` predicate expands to
`m>=2`, `d>0`, `gcd(m,d)=1`, `c!=0`, at most `m` lower rows, and the strict
weight bound for every nonzero lower coefficient.  The represented equation
is `Y^m-c*X^d+lower(X,Y)`.  Thus neither irreducibility nor nonsingularity
is assumed.

`Curve.relation` is the explicit replacement for `Y^m`.
`reductionStep` removes the highest nonzero Y-row and replaces it using
that relation; `reduce` performs as many stages as the input row-list
length.  Under the displayed shape hypotheses every active step lowers
the Y-degree, so this fuel is sufficient.  Output lists may retain zero
rows; coefficient access, and hence the matrix program, is independent
of those trailing zeros.

`multiplicationMatrix` computes column `j` as the reduced coefficient
vector of `G*Y^j`.  `determinant` is a division-free Laplace recursion.
`norm` is that determinant, and `weight` scans every nonzero coefficient
of `G`.  `leadingWitness` explicitly selects indices attaining the maximum.
The target propositions are:

- `NormDegreeGoal`: nonzero norm, exact degree equal to weight, and the
  displayed leading-coefficient formula for every leading witness.
- `FiberPowerGoal`: a distinct list of roots in one rational fiber yields
  divisibility by the corresponding power of `X-u`.
- `CommonZerosGoal`: every supplied distinct list of common rational zeros
  has length at most the weight.
- `WeightedBasisCountGoal`: the explicit rectangular bounded scan has the
  branch-based floor-sum cardinality.
- `EventualDimensionGoal`: the stated eventual linear formula under the
  exact threshold `m*d-m-d<=L` (natural subtraction).

The route to proof is the article's sequence: prove monic-reduction
correctness and uniqueness, identify its multiplication matrix, establish
the determinant identities by finite permutation/Laplace expansions,
perform the Laurent rescaling coefficient calculation, and then prove the
fiber multiplicity lemma using the explicit Vandermonde row matrix.
Define Laurent polynomials for that step as finitely supported integer
exponents stored in lists, normalize by collecting equal exponents, and
compare coefficients; no completion is required.  A list of rational fibers
is grouped by exact rational comparisons.  Factor removal is repeated for
that finite list.  Each object-theory induction is an equality or a bounded
coefficient assertion after Booleanization.  The remaining substantial
work is exactly this polynomial/determinant proof library; the complete
theorem is not inferred from the executable examples.

## 6. Divided-power arithmetic with the correct coefficient demand

`HurwitzTargets.lean` defines binomial coefficients by Pascal recursion
and the finite product
`(a*b)[n] = sum(j<=n, choose(n,j)*a[j]*b[n-j])`.
It reuses rational finite vectors but replaces ordinary convolution.
The derivative consumes a vector of length `N+1` and returns the shifted
vector of length `N`.

`LeibnizGoal` includes the necessary truncations explicitly:

```
D_N(a*b) = D_N(a)*truncate_N(b) + truncate_N(a)*D_N(b).
```

The proof groups two finite sums using Pascal's identity.  It never
interprets a derivative as an endomorphism of one fixed truncation.

For a scalar polynomial `P(T,Y)` with rational coefficients,
`odeStep` sets coefficient `k+1` to coefficient `k` of `P(T,Y)` in the
Hurwitz product.  `odeProducer` performs `N-1` such updates, starting at
the supplied constant.  `satisfiesODE` states the initial coefficient and
every demanded coefficient equation explicitly; `PolynomialODEGoal`
states existence and uniqueness of this finite prefix.  The proof first
establishes that coefficient `k` of a polynomial expression depends only
on inputs through `k`, then inducts on the assigned index.  There is no
division by `k+1` or a factorial.  The executable diagnostic for `Y'=Y^2`,
`Y(0)=1` returns `[1,1,2,6,24,120,720,5040]`.  Analytic convergence is a
separate theorem and is not asserted by this target.

## Build

With Lean 4.32.0 on PATH:

```bash
bash build.sh
```

Or set `LEAN_BIN` to an absolute Lean executable.  The script writes generated
objects into `.build/`, compiles all ten standalone targets, and runs the
axiom audit.  Generated `.olean` files are disposable; the source files,
license, provenance, and build log are the reproducible deliverable.
