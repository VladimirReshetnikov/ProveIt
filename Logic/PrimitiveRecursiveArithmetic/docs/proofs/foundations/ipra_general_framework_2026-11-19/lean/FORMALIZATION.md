# Formalization plan and exact proof status

## 1. Status and build

The source API was inspected at ProveIt revision
`3ee850b4c2d650cf01263823fd5415963747c5d0`, whose `lean-toolchain` is
`leanprover/lean4:v4.32.0`. No Lean executable or compiled Mathlib cache was
available in the preparation environment. Consequently **none of the new
Lean files is reported as elaborated or kernel-checked**. Absence of
`sorry` from a source file does not change this status.

`QuantitativeElimination/MidpointCancellation.lean` supplies a complete
candidate proof term, with an explicit natural slack, for a useful
object-theory inequality. Its core polynomial identity was independently
expanded to zero in SymPy. This is an arithmetic verification of the
written identity, not verification of its Lean elaboration or its iPRA
derivation.

`QuantitativeElimination/RuntimeNormTargets.lean` defines three unfilled
closed `Prf PRAAx` obligations. The definitions are not axioms, assumptions
silently imported into later theorems, or proved theorems. They specify
the expected endpoint precisely enough to prevent replacing an internal
numerical dimension by an external fixed dimension.

Run `bash check_against_proveit.sh /absolute/path/to/ProveIt` in an existing
checkout of the pinned revision with its normal dependencies installed.
The script checks the revision, builds the direct upstream imports,
and attempts elaboration of the three local files, including the separate
ordinary-Mathlib specification file `SemanticSquarefreeTargets.lean`. It does not clone, fetch, or mutate
Git. All transitive imports are those of that pinned checkout; the small
`upstream/` directory is an inspection snapshot, not a complete vendored
Lean library. The repo's `lake-manifest.json` fixes its external imports.

## 2. Which theory the declarations concern

Use the existing ordinary-iPRA judgment

```lean
Prf PRAAx Γ φ
```

where `Γ : List (Fm PTm n)` and `φ : Fm PTm n`. `PTm n` is the syntax of
primitive-recursive terms in a finite scope; `Fm PTm n` is first-order
intuitionistic syntax. This is distinct from proving a proposition about
Lean's `Nat`, `Rat`, `Real`, or `Matrix` types.

The repo's `Core/Tactic.lean` defines `univ k` and `closeUniv k` for
universal closure. Its ring of provable term equivalence classes,
`Groth (Q Γ)`, is used to check polynomial certificates. `natEq` sends an
object equation into that ring and `deriveNat` sends a checked equation
back to an object proof. This use of an external ring tactic is justified
by the proved translation; it does not replace the target with truth in
the standard natural numbers.

Integers are pairs of natural terms, `ZT n`, with `u.pos-u.neg` as their
meaning. An integer inequality is

```lean
zle u v = le (u.pos + v.neg) (v.pos + u.neg)
```

so its slack is the explicit natural term

```lean
monus (v.pos + u.neg) (u.pos + v.neg)
```

from `Core/IntOrder.lean`. Rational comparisons use positive common
denominators and these signed numerators. All denominator positivity
conditions belong to the rational adapter and must remain explicit.

## 3. The new finite cancellation lemma

The mathematical data are signed values `C,A,B`, a natural weight `w`, a
natural penalty `P`, and natural errors `eL,eR`. The three assumptions are

1. `A <= C+eL`;
2. `B <= C+eR`;
3. `2wC+P <= w(A+B)`.

The conclusion is `P <= w(eL+eR)`. No lower bound, infimum, or residual
equal to an objective gap is used. If the assumptions' natural slacks are
`s1,s2,s3`, the complete certificate is

`w(eL+eR) = P+s3+w(s1+s2)`.

This identity is the entire new arithmetic argument in
`penalty_from_midpoint`. `penalty_closed` closes all ten natural
parameters, including the six signed components. It is therefore an
object-iPRA endpoint, conditional only on its displayed arithmetical
premises, once elaborated.

For the finite-cloud projection theorem, take `C=2F((x+y)/2)`,
`A=2F(x)`, and `B=2F(y)`. The parallelogram identity supplies premise 3
with `w=1` and `P=|x-y|²`. The cloud and near-minimality lemmas supply

`eL=L(2ηS+h)+2εS`, `eR=L(2ηT+h)+2εT`.

The exported arithmetic conclusion is exactly

`|x-y|² <= 2L(ηS+ηT+h)+2(εS+εT)`.

The mathematical advance is the construction of those comparisons from
finite clouds. It is not merely the cancellation identity. The geometric
adapters below remain formalization tasks.

## 4. Complete finite-cloud representation

Use a **single fixed codec** for lists, signed integers, positive
denominators, and vectors. A point is a numerical code for a list of `d`
rational coordinates. A cloud is a numerical code for a nonempty list of
point codes. A common positive denominator can be the product of all
displayed denominators used in the finite query. There is no need to
reduce fractions before every comparison, though denominator positivity
must be checked.

The numerical parameters are `d`, the two cloud codes, their lengths,
the anchor `z`, box bound `B`, their midpoint defects, a Hausdorff bound,
and optional objective errors. Programs are fixed once; all of these
values remain object-theory inputs. The predicates are:

- `Vector(v,d)`: every used coordinate is well formed, with denominator
  at least one; missing or extra entries follow a specified total codec.
- `Box(v,z,d,B)`: every coordinate of `v` and `z` lies in `[-B,B]`.
- `Near∞(u,v,h)`: all `d` coordinate distances are at most `h` after
  denominator clearing.
- `Hausdorff(S,T,h)`: each element of either nonempty list has a witness
  index in the other list satisfying `Near∞`.
- `MidpointClosed(S,η)`: for every pair of indices in `S`, some index in
  `S` is within `η` of their coordinatewise midpoint.
- `Cost(v,z)`: the exact rational sum of `d` squared coordinate
  differences.
- `NearMin(S,x,ε)`: `x` is a member of `S` and, for every used index `j`,
  `Cost(x,z) <= Cost(S[j],z)+ε`.

All quantifiers in these predicates are bounded by numerical lengths.
The ordinary formula is convenient for theorem statements. Induction is
on its Boolean translation from `Foundations/BoundedSyntax.lean`; it is
not induction on an arbitrary quantified formula.

The selector is the point at the least cost-minimizing index. Reuse
`ApproximateWitness.argmin` and `argmin_minimal`, after converting all
finite candidate costs to natural numerators on one common positive
denominator. Do not call a real-valued argmin or pass a real-number
comparison to the bounded search.

### Dependency order and invariants

| Step | Existing code | New adapter / exact invariant |
|---|---|---|
| Numeric lists and lookup | `MasterCertificate.entry`, `SequenceComposition.length` | Vector and rational decoder correctness |
| Exact rational coordinates | `GaussianRationalHorner` and rational arithmetic modules | Restrict imaginary part to zero, or add a real-rational wrapper |
| Finite cost | `Core.Sums` and the multiplication recurrence | Prefix cost equals sum of first `i` coordinate squares |
| Least finite minimizer | `ApproximateWitness.argmin_spec`, `argmin_minimal` | The actual selected point is in the cloud and no more costly than any indexed competitor |
| Nearest cloud witness | `FiniteHausdorff.nearest`, `distanceTo`, `hausdorff` | Sup-metric common-scale adapter and guarded nonempty lengths |
| Lipschitz cost | `Core.IntOrder`, `Core.OrderCertificates` | Prefix inequality `abs(Cost_i(u)-Cost_i(v)) <= 4iB h` |
| Midpoint identity | `Core.Tactic.ipra_ring` for one coordinate | Prefix sum of `4F(mid)+dist²=2F(x)+2F(y)` |
| Cloud stability | New `cloud_squared_bound` | Supply the repaired midpoint competitors; no unknown infimum |
| Name regularity | `DyadicNames`, explicit PR precision schedule | Two independent selected samples obey the scheduled finite distance bound |
| Real semantic recovery | External definition of regular Cauchy names | Interpret the proven finite arithmetic instances; do not add a completion axiom to iPRA |

The exact imports for the new file are the two at its top; the table
records the further geometric implementation plan.

At each numerical dimension `d`, all loops stop at a displayed bound.
Nested loops for midpoint checks stop at `length(S)^3`; a brute-force
search is primitive recursive even when inefficient. Coding a product of
denominators uses bounded recursion. Induction invariants contain only
fixed primitive-recursive terms and Booleanized finite predicates.

## 5. Current runtime norm API and the exact remaining obligations

The inspected `Analysis/GaussianPolynomialMonicNorm.lean` already computes
a norm polynomial using an actual numeric-dimensional multiplication
matrix and determinant. In its API:

```lean
input F G m a c
matrix F G m a c
norm F G m a c
run F G m a c
```

`m,a,c,F,G` are all numerical terms. The field represented by this
implementation is the Gaussian rationals. `F` stores the lower monic
rows of a polynomial in `Y`; its leading `Y^m` is implicit. `G` stores a
remainder of degree below `m` in `Y`. Both row arrays are descending in
`Y`. Each row is a descending coefficient list in `X`.

The shape `rowShape F m c` means every used row has `c+1` coefficient
slots. It does **not** state that the outer list has exactly `m` entries
or that raw rational codes are canonical. The actual program normalizes
coefficients. Weighted-support tests therefore inspect canonicalized
coefficients, not raw-code equality to the designated zero code.

The existing theorem `returned_zero_action` proves the original curve
equations imply every component of the left evaluation-vector product
with the actual returned matrix is zero. Its first evaluation-vector
coordinate is one. The missing implication is that the actual computed
determinant vanishes. `CommonZeroNormTarget` states that implication in
one universally closed object formula without taking a kernel/determinant
law as a premise.

### Weighted degree

Take integer weights `wx>=1` and `wy>=0`. The implicit leading `Y^m` has
weight `m*wy`. For row `i<m` and slot `j<=c`, the weight of the monomial
in `F` is

`wx*(c-j)+wy*(m-1-i)`.

`weightedRows` requires coefficients above a displayed cap to vanish.
The conditions for the norm theorem are `F`'s cap `m*wy` and `G`'s cap
`D`. The asserted bound is

`degree_X(norm) <= floor(m*D/wx)`.

This is a statement about actual support. It does not claim that the
already allocated norm buffer becomes shorter. `leadingZeros` says
precisely which of the descending slots must vanish; the original
storage cap remains `m*(a+(m-1)*c)`.

The monic reduction invariant is: after multiplying `G` by `Y^j` and
reducing, its coefficient of `Y^r` has `X` support satisfying
`wx*degree_X + wy*r <= D+wy*j`. The recurrence is bounded coefficient
convolution, followed by the monic relation. Apply QF induction to the
Booleanized finite support predicate over the actual column loop `j`.

For each numerical permutation word in the actual determinant, sum the
entry inequalities. The row-index sum equals the column-index sum, so
the `wy` terms cancel. Thus every product has `X` degree at most
`floor(mD/wx)`. A second QF induction over the actual permutation scan,
using `coefficient_leibniz`, proves the zero leading slots of the stored
determinant. No evaluation identity alone is enough to conclude this
coefficient statement.

### Variable dimension and further norm conclusions

`Algebra/DeterminantLaws.lean` proves many laws for every externally fixed
matrix size, with matrix entries as terms. These results are useful
mathematical templates, but their `k` is not the numerical `m` above.
The actual runtime determinant scans `m^m` digit words and filters the
permutations. Its coverage and uniqueness are in
`Foundations/RuntimePermutationWords.lean`. Adjacent column-swap
alternation has a numerical implementation in
`Analysis/GaussianPolynomialColumnAlternation.lean`.

To derive the missing kernel implication, complete runtime row operations
or runtime cofactor identities using these finite scans, and apply the
actual `returned_zero_action`. To derive nonvanishing from a displayed
coprimality certificate, also prove the corresponding multiplication
identity for the actual norm. To bound total common zeros sharply, add
fiber multiplicity: multiple distinct roots in one fiber force a
matching power of `X-a` to divide the norm. These are separate obligations;
none is supplied by the implementation of the norm program alone.

For fiber multiplicity, the human argument can use an explicit Vandermonde
minor and an explicit inverse certificate. The numerical formalization
must construct the relevant finite matrices and keep the nonzero
Vandermonde determinant, factor division, and all finite list lengths
as checkable object data. A host theorem about an unspecified field does
not by itself supply that coded-field adapter.

## 6. Finite-place Newton certificate

The further `LocalNewtonNormTarget` fills a genuine application gap at
the mathematical level: it is a local finite coefficient certificate for
nonvanishing, rather than an assumption that the norm is nonzero or an
unavailable global irreducibility oracle.

There is already an actual runtime translation program
`GaussianRationalTranslation.translated P cap z`. It returns descending
coefficients of `P(z+T)` using repeated synthetic division. The local
coefficient of `T^i`, for `i<=cap`, is its entry at `cap-i`. Define

`exactOrder(P,cap,z,v,b)`

to mean `v<=cap`, the canonically recoded `b` is nonzero, the coefficient
at `v` equals that recoding, and every coefficient below `v` is zero.
This is a bounded finite predicate; no formal or convergent power series
is an input.

For `F=Y^m+Σ f_j(X)Y^j`, the local condition at `X=z` supplies an integer
`e>=1` coprime to `m` and a nonzero coefficient `c0` such that:

- `f_0(z+T)` has exact order `e` and leading coefficient `-c0`;
- for `0<j<m`, every coefficient of `T^i` in `f_j(z+T)` with
  `m*i+e*j<=m*e` is zero.

This expresses `m*ord(f_j)+e*j>m*e` without introducing an infinity
sentinel for zero polynomials. For the reduced polynomial
`G=Σ A_j(X)Y^j`, a certificate supplies `k<m`, `v`, nonzero `b`, and
`s=m*v+e*k`. Every coefficient of weight below `s` vanishes, while the
coefficient of `T^v Y^k` is `b`. Coprimality makes that minimal pair
unique. The finite test runs over the actual stored coefficient bounds.

At a supplied rational place, these local data can be checked by bounded
scans. For `G`, scan the `m*(a+1)` translated coefficient positions,
discard zero coefficients, and minimize the natural weight `m*i+e*j`.
A displayed nonzero coefficient of the translated `G` guarantees the
scan is nonempty. To derive that guarantee from the original `G`, use
the actual translation/inverse-translation identities; do not silently
assume translation preserves a raw-code nonzero test. The loop's maximum
weight is `m*a+e*(m-1)`. Whether a general input curve has a successful
finite-place certificate of this special form is a separate mathematical
condition, not a conclusion of the checker.

The target states

`ord_z(norm)=s`,

with leading coefficient

`b^m * (((-1)^(m-1))*c0)^k`.

It additionally states degree at most `W` under the independently
displayed global weighted support conditions `m*deg(f_j)+d*j<=m*d` and
`m*deg(A_j)+d*j<=W`. Its local and global hypotheses are separate.

The direct finite proof does not need Puiseux roots. At initial weight,
the relation is `Y^m=c0*T^e`. In column `j`, the unique lowest-weight
entry of multiplication by `b*T^v*Y^k` lies in row
`(k+j) mod m`; its coefficient is

`b*c0^floor((k+j)/m)`

and its `T` exponent is `v+e*floor((k+j)/m)`. The selected row pattern
is a permutation. All other determinant contributions have strictly
larger total integer order; the sums of the row and column weights
cancel. The lowest contribution has order `m*v+e*k` and coefficient
`b^m*c0^k` times the sign `(-1)^((m-1)*k)` of the cyclic shift.

The implementation obligations are: a Booleanized support invariant for
each companion iterate; the explicit cyclic-shift permutation and its
sign for the actual word codec; coefficient convolution and finite
product extraction at the lowest degree; and the nonzero product law of
the coded Gaussian-rational field. These are finite source-bound steps.
The final target names the original norm constructor, not a substitute
abstract determinant with a desired property as a field.

The source file remains unelaborated. A general coded-field version is a
separate interface project; the current target uses the repository's
actual Gaussian-rational implementation.

## 7. Proof-status separation to preserve

1. The finite mathematical arguments in the report are human proofs with
   explicit arithmetic bounds and induction invariants.
2. The upstream API is source-inspected at a fixed revision. This task did
   not rerun the upstream build.
3. The midpoint source gives a complete proposed object proof, unelaborated
   here. Its algebraic certificate was independently checked.
4. The runtime norm files specify targets and a dependency path. They do
   not claim those targets have been proved in Lean.
5. Infinite-object semantic interpretations are metatheoretic explanations
   of finite arithmetic statements, not extra iPRA axioms.
