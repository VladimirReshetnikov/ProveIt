# Independent mathematical review

Reviewed: `research/framework_math.tex` and `research/sections_norm.tex`.
Scope: human argument, assumptions, quantifier order, finite algorithms,
and compatibility with the stated iPRA formalization plan. This is not
kernel verification of the application theorems.

## Main result

No mathematical error was found in the current finite-observable-module
argument. The proof extracts coordinate denominator and magnitude bounds
from stronger finite algebra data, so it does not make the invalid generic
inference from a cardinality bound to a search cutoff.

## Checks of the finite-observable argument

1. **Primitive scaling.** Multiplying the rational evaluation row by the
   product of denominators gives a nonzero integer row. Dividing by the
   positive gcd produces a primitive row and preserves all eigenvector
   equations. The scale need only be rational; no assumption that the
   gcd divides the denominator product is made.
2. **Rational eigenvalue integrality.** For reduced `a/b`, the coordinate
   equations imply `b | a w_j`. Bezout for `a,b` gives `b | w_j`, and
   Bezout for the primitive row gives `b | 1`. This proves `b=1` without
   determinant, characteristic polynomial, or a field closure.
3. **Correct matrix orientation.** The manuscript uses evaluation *rows*.
   Therefore the maximum absolute *column sum* is the correct bound.
   Choosing an index of maximum `|w_j|` gives exactly the displayed
   inequality. There is no row/column switch in the theorem or example.
4. **Reduced denominator bounds.** From `x=z/Delta`, canonical reduction
   divides both integers by their gcd. Thus the reduced denominator divides
   `Delta`, and the numerator magnitude is at most `|z|`. This also handles
   `z=0`, whose canonical denominator is one.
5. **Nonzero evaluation vector.** The checked unit identity, rather than
   linear independence or a special basis convention, ensures this. The
   condition remains valid when the displayed generators are redundant.
6. **Complete enumeration.** Every rational zero is forced into a fixed
   Cartesian grid before the filter is applied. Grid soundness comes from
   exact equation checking; completeness comes from the eigenvalue bounds.
   Distinct scaled integer tuples remain distinct rational tuples.
7. **Noncommuting matrices.** The argument uses their actions only on the
   evaluated nonzero row. Commutativity on unused directions is genuinely
   unnecessary, rather than an omitted hypothesis.
8. **Separated annihilator constructor.** For a boundary monomial,
   multiplication by `X_k` leaves precisely the multiple of the supplied
   monic `q_k`. The coefficient signs and ideal witness multiplication are
   correct. For degree one the optional `Delta` term in the radius is only
   an overestimate.
9. **Adjugate converse.** The action identity is `bC=r` with
   `C=X_k I-M_k`. Right multiplication by `adj C` gives the claimed ideal
   witness for `q_k b_j`; adding the multiplied unit witness gives `q_k`
   with the stated plus signs. Monicity and degree `D` hold independently
   of generator dependence.
10. **Elliptic-section example.**
    `F_1+(2x+1)F_2 = 4(y^2-1)` expands correctly. The multiplication
    columns, denominator scales `(2,1)`, radii `(2,1)`, fifteen candidate
    pairs and four retained points are consistent. The original cubic
    alone is not claimed to have only those four rational points.
11. **Open and projective charts.** The reciprocal equation `tG-1=0`
    gives a unique lift exactly on `G != 0`. Disjoint projective charts
    use the first nonzero coordinate and normalize it to one, so every
    projective point has one canonical representative. Complete lists
    remain conditional on supplied certificates for the extended/affine
    systems.

All finite-vector and matrix statements assume positive generator dimension;
the prose at the start says this. The implementation must retain that
validation condition, together with polynomial arity and canonical-code
conditions, as the draft already requests. The general observable-image
theorem does not enumerate source objects unless the observables determine
them or a finite reconstruction is separately supplied.

## Checks of the norm-to-list theorem

The nonzero norm hypothesis is essential and is checked explicitly. A
common rational zero gives a nonzero evaluation row with first entry one;
the adjugate identity forces the norm to vanish at its first coordinate.
No multiplicity or smoothness assumption is needed for this implication.

The rational-root bound must use the *first nonzero coefficient after
removing a power of the variable*. Using the literal constant coefficient
would incorrectly handle roots at zero. The current statement and code use
the correct version. Constant polynomials, monomials, and reduced zero
fractions are explicitly handled.

The norm root list can contain first coordinates with no rational common
zero. The second rational-root scan and the final `G=0` filter are therefore
necessary. They are present. Monicity of `F` ensures that every specialized
fiber remains nonzero of the same positive degree, including `m=1`.

An identically zero norm is correctly reported as unsupported, not as proof
of infinitely many rational points. Conversely a nonzero constant norm
gives an empty intersection. The global-cover corollary requires a genuine
proof that the *fixed supplied sections* cover every desired point. Covers
chosen separately for each supplied tuple do not meet this condition.

## Exact finite diagnostics

`research/norm_code/norm_intersections.py` was executed with Python's exact
`fractions.Fraction` and the parent `certified_points.Poly` datatype.
Its multiplication norm is computed by polynomial reduction and a Leibniz
determinant; the determinant values were independently compared against
exact scalar Gaussian elimination at three inputs per case.

Observed coverage: 11 intersection cases; 33 independent determinant
evaluations; 27 evaluation-row coordinate identities; 4 rejected
unsupported intersection inputs; 3 additional rational-root cases; and
rejection of the zero polynomial. The norm-to-module extension additionally
constructs 10 finite multiplication certificates which pass the independent
coefficient-identity checker. In each case the separate lattice grid
enumerator returns exactly the same points as the norm/fiber root scans.
The constant-norm case constructs and checks an ideal identity for one.
The recorded result is
`research/norm_code/norm_checks.json`. All passed. These finite checks do
not replace the universal human proofs or the future object-level proofs.

The added norm-to-module proposition was also reviewed directly. Its
identity follows with the stated signs from `b M = G b - F h`, multiplied
on the right by `adj M`. The first coordinate gives `N = U G + V F`.
Normalizing `N` to a monic polynomial gives exact reduction in `X`, while
monicity of `F` gives exact reduction in `Y`. In a `Y` boundary column,
reduce the finitely many coefficients `-X^i f_t(X)` by the normalized
norm. The resulting witness is `X^i F + sum_t s_t q Y^t`, exactly as
stated. The rectangular basis has `m deg(N)` elements. A nonzero constant
norm yields the separately handled inconsistency identity.

## Status safeguards

The human iPRA strategy needs all arithmetic scans, gcd routines, polynomial
loops and bounded array invariants represented by specific PR syntax and
actual `Prf PRAAx` derivations. A successful native Lean build, or a supplied
unproved target proposition, does not by itself discharge those obligations.
The current draft states that distinction. A source theorem asserting that
an external procedure is primitive recursive must not be inferred just from
termination in Lean; the explicit finite schedules in the human proof are
the intended route.

No claim of general effective Siegel, Faltings, uniform Mordell–Weil
generation, arbitrary singular Puiseux extraction, or mathematical
historical novelty is warranted by these results. The draft retains the
necessary boundaries.
