# Lean and iPRA completion plan

## Status boundary

`AlgebraicCore.lean` and `ConstructiveCorollaries.lean` are proposed ambient
Mathlib scripts. They contain no `sorry`, but Lean/Lake was unavailable in the
delivery environment, so they were not compiled. `ObjectTargets.lean` states
the deeply embedded targets against ProveIt's current `ConciseIPRA` API. No
claim is made that the final `Prf PRAAx` terms already exist.

An ambient theorem over `LinearOrderedField` is not an iPRA theorem. Completion
requires all stages below.

## Stage 1: natural-number encodings

Implement or reuse primitive-recursive codes for:

1. signed integers;
2. positive-denominator rationals;
3. pairs and fixed tuples;
4. sparse multivariate integer polynomials;
5. two-dimensional rational vectors;
6. regular dyadic names and explicit apartness witnesses.

Every operation used in the report must be represented by a concrete
`LeanProofs.ConciseIPRA.PR` term, not by a meta-level Lean function alone.

## Stage 2: polynomial normalizer

Define a primitive-recursive normalizer for sparse polynomials:

- insert a monomial into a lexicographically ordered coefficient list;
- merge equal exponent vectors;
- delete zero coefficients;
- implement addition, negation, multiplication, and exponentiation by a fixed
  natural exponent;
- return zero exactly when the normalized coefficient list is empty.

Prove its soundness by quantifier-free induction on the input lists and on the
fixed exponent loops. Then compile the 30 certificates listed in
`verification/results.json`. SymPy is only an independent audit; the object
checker must be this small PR normalizer.

## Stage 3: ordered rational arithmetic

Prove in `PRAAx` the defining equations and order properties for rational
codes. Required lemmas include:

- denominator positivity;
- cross-multiplication characterization of equality and order;
- decidability of coded rational comparisons;
- compatibility of addition and multiplication;
- cancellation only from a supplied nonzero/apartness certificate.

No use of classical `by_cases` on arbitrary formulas is needed. Case splits
are only on primitive-recursive Boolean comparisons.

## Stage 4: bounded positive roots and reciprocals

Reuse the mesh-search construction from the existing
`triangle_formulas_ipra` packet. For nonnegative rational `q` and precision
`k`, bounded search produces `rho(k,q)` satisfying

```
rho(k,q)^2 <= q < (rho(k,q) + 2^(-k))^2.
```

For a fixed regular name of a nonnegative real, choose an explicit precision
schedule and prove regularity of the resulting positive-root name. Prove
positive-root uniqueness in the form used by the report. For division, require
an apartness witness `|x| >= 2^(-d)` and use bounded Newton or interval
refinement to construct the reciprocal name.

## Stage 5: triangle certificate

Define a coded `TriangleCert` containing side names `a,b,c`, positive excess
names `x=s-a`, `y=s-b`, `z=s-c`, a positive area name `K`, and six half-angle
component names. Its checker verifies:

- `a=y+z`, `b=z+x`, `c=x+y`, `s=x+y+z`;
- `K^2=s*x*y*z`;
- the six half-angle square equations;
- positivity/apartness fields;
- the four positive-root product equations giving
  `A/2+B/2+C/2=pi/2` algebraically;
- `2*K*d=a*b*c` for the sine-law scale.

The polynomial checker then proves the two Mollweide crosses and the tangent
cross. Quotient statements are derived only after opening the stored
apartness witnesses.

## Stage 6: incenter and cotangent certificate

For coordinate input, define

```
I = (a*A + b*B + c*C)/(a+b+c),    r = K/s.
```

Use determinant linearity to prove that `I` has signed distance `r` from all
three side lines. The half-angle certificate proves `r*cA=x*sA` and cyclic
companions. This is already the denominator-free cotangent law. The inradius
square identity follows either directly from `K^2=s*x*y*z` and `r*s=K`, or by
the explicit certificate in `AlgebraicCore.inradius_certificate`.

## Stage 7: circle and line certificate

Define coded records:

```
Circle := (ox, oy, rho)       -- rho is radius squared
LineChart := (px, py, vx, vy)
```

with direction apartness `vx^2+vy^2 # 0`. Define

```
pow(P) = (px-ox)^2 + (py-oy)^2 - rho
f(t)   = pow(P+tV).
```

The polynomial normalizer proves

```
f(t) = p + 2*h*t + q*t^2
w*f(u) - u*f(w) = (w-u)*(p-q*u*w).
```

A stored root-separation witness `w-u # 0` licenses cancellation. This gives
the signed power theorem. External secants, internal chords, and tangents are
then order/sign corollaries. The tangent branch uses the stored circle and
orthogonality equations.

## Stage 8: first-order theorem schemas

First-order iPRA does not quantify over all real-number functions. For each
fixed tuple of primitive-recursive regular-name programs, instantiate the
construction and prove a universally quantified theorem over their numerical
parameters and requested precision. Keep the finite rational theorem uniform
in coded rational inputs.

Do not introduce a hypothetical total evaluator for arbitrary PR program
codes. Compilation is external and fixed before the object theorem is formed.

## Stage 9: transport to the native concise calculus

Construct the actual `Prf PRAAx [] ...` objects for the checker theorems and
use `ObjectTargets.transferToNative`, which invokes the existing
`pra_iff_native` equivalence. This final step is transport, not a replacement
for constructing the `PRAAx` derivations.

## Suggested module graph

```
MollweideCircleIPRA/
  Codes.lean
  Rational.lean
  Polynomial.lean
  PolynomialSound.lean
  RegularNames.lean
  PositiveRoot.lean
  Reciprocal.lean
  Vec2.lean
  TriangleCertificate.lean
  Mollweide.lean
  Cotangent.lean
  CircleCertificate.lean
  PowerPoint.lean
  ObjectTheorems.lean
  NativeExport.lean
```

The first complete milestone should be the finite rational/polynomial theorem;
regular-name lifting can then reuse it without changing the algebraic core.
