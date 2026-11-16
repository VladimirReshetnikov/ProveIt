# Formalization route and dependency boundaries

## 1. The actual object-theory endpoint

The pinned repository defines `PR k`, `PTm n`, `Fm PTm n`, `PRAAx`, and the
judgment `Prf PRAAx Γ A` in namespace `LeanProofs.ConciseIPRA`. This judgment
is intuitionistic first-order natural deduction with equality, the defining
equations of primitive recursive symbols, successor separation/injectivity,
and quantifier-free induction. The final native transfer is

```
pra_iff_native :
  Prf PRAAx Γ A ↔ NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA A)
```

This theorem consumes an object derivation. A host Lean theorem about `Nat`,
`Int`, `Rat`, or `List` cannot be substituted for that derivation.

## 2. Fusion: a completed proof builder

For fixed unary PR symbols `f`, `g`, `h`, `iterate f` is the binary PR symbol
defined by `iterate f 0 x=x` and `iterate f (n+1) x=f(iterate f n x)`.
`ObjectFusion.lean` proves both equations with `PRA.precZero`, `PRA.precSucc`,
`PRA.comp`, `PRA.proj`, and equality substitution.

The input to `fusion` is exactly a derivation, with one free variable, of

```
[] |-iPRA h(f(x)) = g(h(x)).
```

Its output is an actual derivation, with initial state free, of

```
[] |-iPRA forall n, h(iterate f n x) = iterate g n (h(x)).
```

The synthesized induction formula has counter at de Bruijn index 0 and
initial state at 1. It is a single equality and therefore quantifier-free.
The base uses both iteration-zero equations. The step substitutes the current
iterate into the supplied local equation, applies equality congruence to the
induction hypothesis, and uses both successor equations. There are no other
proof obligations hidden in the interface.

`SquaringTransport.lean` builds `square m` structurally from a binary PR
multiplication symbol `m`. Given an object proof of
`h(m(x,y))=m'(h(x),h(y))`, it specializes to `x=y`, obtains the local square,
and applies `fusion`. This is suitable for modular reduction or polynomial
evaluation after their multiplicativity proofs have been supplied. The
theorem does not assert those application-specific multiplicativity proofs.

## 3. Relational simulation: a completed proof builder

`simulation` takes a formula `R : Fm PTm 2`, a proof that it is quantifier-free,
fixed unary PR symbols `f,g`, and exactly the object derivation

```
[R(x,y)] |-iPRA R(f(x),g(y)).
```

It produces

```
[R(x,y)] |-iPRA forall n, R(iterate f n x, iterate g n y).
```

`qf_subst` checks preservation of quantifier-freeness under substitution.
The base substitutes the iteration-zero equalities in the initial relation.
The step substitutes the two current iterates into the supplied local
derivation, weakens its context, and substitutes the iteration-successor
equalities. Thus this theorem applies to proved finite congruences, error
relations, and presentation simulations that are expressed by fixed Boolean
tests. It does not permit a quantified or arbitrary host relation as the
induction invariant.

## 4. Integer eigenvalue lemmas: completed host theorems

`PrimitiveEigenvalue.Coordinate` is spelled `FiniteAlgebra.Coordinate` in the
code. Its fields hold an integer Bezout coefficient, an integer eigenvector
coordinate, and its integer image coordinate. `vectorSum` and `imageSum` are
explicit recursive weighted sums. `EigenEquation a b xs` is the finite
relation `b*z_i=a*w_i` for every list entry.

`weighted_eigen_equation` proves `b*imageSum=a*vectorSum` by finite induction.
When `vectorSum=1`, the denominator divides the numerator. The additional
certificate `u*a+v*b=1` and positivity of `b` imply `b=1`. This proof shortens
the coordinatewise divisibility argument: it combines the eigen-equations
with the primitive-vector Bezout identity first.

`EigenvalueBound.lean` defines the integer dot product and absolute column
sum by explicit list recursion. It proves the triangle estimate
`abs(dotColumn xs) <= W*absoluteColumnSum xs` from the coordinate checks
`abs(w_i)<=W`. A selected coordinate of absolute value `W>0`, its eigenvalue
equation, and a column sum at most `R` imply `abs(lambda)<=R` by positive
natural cancellation. Finding the selected coordinate is an ordinary finite
maximum scan; its existence lemma is not packaged as a theorem here.

## 5. Full finite-algebra definitions and exact remaining goals

`FiniteAlgebraTargets.lean` has no undefined implementation slots.

| Definition | Representation or program |
|---|---|
| `Monomial n`, `Polynomial n` | Rational coefficient plus an exponent vector of length `n`; finite lists of monomials. |
| `constant`, `variablePolynomial`, `scale`, `sub`, `mul` | Explicit sparse operations; multiplication adds exponent vectors. |
| `coefficientAt`, `polynomialEq` | Fold coefficients of equal exponent vectors; check all exponents in the union of supports. |
| `monomialValue`, `evaluate` | Finite powers, products, and sums. `zeroTest` enforces point length `n` before malformed list inputs can be accepted. |
| `Certificate n s d` | `d` polynomial generators, rational unit coefficients, positive integer denominators, integer action columns, and polynomial ideal witnesses. |
| `unitResidual`, `actionResidual` | Exact polynomial residuals. The action equation is `delta_k*X_k*b_j-sum_i A[k][j][i]*b_i=sum_l H[k][j][l]*F_l`. |
| `certificateOK` | Positivity/dimension checks and finite coefficient equalities. |
| `columnBound`, `coordinateGrid`, `cartesian`, `grid` | Absolute column sums and the explicit Cartesian rational grid. |
| `zeroTest`, `enumerate` | Finite exact filter, with empty result when the certificate is rejected. |

The source defines these proposition-valued targets, without asserting them:

1. `EvaluationTransportGoal`: coefficient equality implies equality of
   evaluations at a well-formed point.
2. `CertificateSoundnessGoal`: accepted ideal identities vanish at every
   common zero.
3. `GridCompletenessGoal`: every rational common zero belongs to the computed
   finite grid.
4. `EnumerationGoal`: membership in the returned list is equivalent to being
   a common zero, conditional on certificate acceptance.

The theorem `enumeration_of_gridCompleteness` already proves item 4 from
item 3. It uses only the specification of finite filtering; it does not
assume enumeration completeness under another name.

### Remaining host proof order

First prove finite polynomial evaluation preserves addition, multiplication,
and coefficient collection. Induct on monomial lists and exponent vectors;
the dimensions supplied by `Vector` justify zipped-coordinate evaluation.
These identities prove `EvaluationTransportGoal` and
`CertificateSoundnessGoal`.

Next evaluate the generators at a common zero. The unit identity supplies a
nonzero evaluation vector. Clear its denominators and use an extended-gcd
fold to construct a primitive integer vector together with its Bezout
coefficients. Apply `reduced_denominator_eq_one` to the integral action
matrix and eigenvalue `delta_k*p_k`. Prove the finite maximum scan's selected
index property and apply `integer_eigenvalue_bound`. This gives an integer
`z_k` with `p_k=z_k/delta_k` and `-R_k<=z_k<=R_k`.

Finally prove membership in `coordinateGrid` by index `z_k+R_k`, and prove
Cartesian membership by induction on the coordinate list. This establishes
`GridCompletenessGoal`, after which the checked filter theorem completes the
host proof. Duplicate-freedom follows from positive denominators and the
injectivity of each coordinate-grid map, followed by finite product and
filter lemmas; this extra claim is not part of the current formal target.

### Remaining object-iPRA proof order

Replace host `Int` and `Rat` by explicit numerical signed-integer and
positive-denominator codes. Give every malformed code a fixed default.
Normalize with bounded Euclidean computations and track the Bezout equation,
positive gcd, and exact divisions as Boolean invariants. Reify fixed list
folds, sparse polynomial multiplication, coefficient collection, matrix
action, finite maxima, coordinate grids, and filtering as explicit `PR`
syntax. For a *variable polynomial code* this is one fixed polynomial
grammar evaluator, not a universal evaluator for arbitrary PR programs.

Build the finite ring and integer-order lemmas in `Prf PRAAx`. Prove every
local loop contract there. Booleanize bounded list/matrix assertions before
using `PRA.qfInd`; keep the arbitrary rational candidate as a free parameter
when proving grid completeness. Instantiate the completed fusion and
simulation builders for compatible presentation changes. The final output
is a `Prf PRAAx` derivation of the checker-conditional enumeration theorem.
Only that derivation may be passed to `pra_iff_native`.

Lean's acceptance of structural or well-founded recursion on `Nat`, `List`,
or `Rat` does not itself establish primitive recursiveness, and the host
theorem does not automatically supply a PR reification. The human proof gives
the primitive-recursive bounds and QF invariant plan; the syntax and object
proof construction described in the preceding paragraph remains work.
