# Residual recombination with an even positive definite Gram matrix

Prepared for the current ProveIt contribution, 25 October 2026, with AI assistance.

## Exact lemma

Let r_0,...,r_(m-1) be integer polynomials in an integer tuple x. Let H be a
symmetric positive definite integer matrix of size m with even diagonal.
Then

    Q(x) = (1/2) r(x)^T H r(x)

is an ordinary polynomial with integer coefficients: the diagonal
coefficients H_ii/2 are integers, and each mixed coefficient is H_ij.
Moreover, for every real tuple x,

    Q(x) = 0  if and only if  r_i(x) = 0 for every i.

Indeed, positive definiteness says v^T H v > 0 for every nonzero real vector v.
Apply this to v=r(x). This argument proves equality of the entire real zero
sets and therefore of their integer zero sets. If each r_i has degree at most
two, Q has degree at most four. Its exact degree, coefficient height, support
and live variable set are finite arithmetic properties checked separately.

This lemma is elementary. No claim is made that positive definite forms,
Gram matrices, or root lattices are new mathematics. The contribution is a
specific coefficient-canceling recombination of the newly projected direct
ZFC refutation certificate, together with every polynomial coefficient and an
exact certificate.

## Why this is a different aggregation family

The usual sum of squares uses H=2I. Here every diagonal is still 2, but a small
number of off-diagonal entries are +1 or -1. Consequently

    Q = sum_i r_i^2 + sum_(i,j,s) s*r_i*r_j.

There are no additional variables. Positive definiteness prevents new zeros.
As a polynomial in the *formal residual coordinates*, Q has odd mixed
coefficients; it cannot be a sum of squares of integer linear forms in those
residual coordinates, whose mixed coefficients would all be even. This does
not assert that Q(x) has no other sum-of-squares representation after
substituting its particular residual polynomials.

## Principal 240-variable recombination

The input is the 240-variable direct quartic obtained by the companion
nonunit-affine-pivot construction from the shared-factorial-error source.
All 177 quadratic residuals remain exactly unchanged, including their order.
Number them from 0 to 176. The new polynomial adds these thirteen mixed terms
to their usual sum of squares:

    -r12*r16 -r12*r19 -r12*r17 -r49*r51 -r19*r51
    -r6*r21  -r17*r26 -r15*r21 +r14*r21 +r17*r19
    -r7*r19  -r7*r17  +r6*r50.

The mixed terms involve only two disjoint blocks. The first has coordinates

    (r6,r14,r15,r21,r50).

Its matrix H has diagonal 2, off-diagonal entries specified by those four
edges, and zeros elsewhere. In the displayed coordinate order, exact LDL^T
elimination has diagonal

    (2, 2, 2, 1/2, 1).

The second block has coordinates

    (r7,r12,r16,r17,r19,r26,r49,r51).

Its exact LDL^T diagonal is

    (2, 2, 3/2, 5/6, 4/5, 3/4, 2, 1/6).

Every listed pivot is strictly positive. The corresponding unit lower
triangular matrices L are given as exact rational numerator/denominator pairs
in `balanced/GRAM_CERTIFICATE.json`; the checker multiplies L D L^T and checks
every entry, rather than trusting a numerical eigenvalue calculation.
All 164 other residual coordinates have the one-dimensional block (2).

The determinants of the two nontrivial blocks are respectively 4 and 1. The
second block is an even positive definite unimodular lattice of rank 8, hence
is an E8 lattice Gram matrix by the standard uniqueness theorem. This
identification is descriptive and is not needed for the correctness proof.
An author-hosted primary reference for the identification is Noam D. Elkies,
"Yet another proof of the uniqueness of the E8 lattice",
https://people.math.harvard.edu/~elkies/Misc/E8.pdf .

## Exact metrics

| Object | Integer variables | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Projected input, ordinary sum of squares | 240 | 4 | 5,477 | 15,107 |
| Principal Gram recombination | 240 | 4 | 5,803 | 6,404 |

Thus the height falls by 57.61 percent while support grows by 5.95 percent.
This is a tradeoff and is not a variable-count record. The ordinary sum of
squares remains a useful alternative with fewer terms. Coefficient content
is 1 for the new polynomial, and all 240 coordinates occur in its collected
support.

## Lower-height companion

Starting from the separate 240-variable lower-height projected input with
9,217 monomials and height 4,512, add these seven mixed terms:

    +r21*r50 -r6*r21 -r19*r21 -r7*r15
    +r7*r50  -r16*r26 +r15*r31.

The two nontrivial H blocks have ordered residual coordinates
(6,7,15,19,21,31,50) and (16,26), with positive LDL diagonals
(2,2,3/2,2,1,4/3,1/4) and (2,3/2). The resulting polynomial has 240 integer
variables, degree 4, 9,357 monomials, and coefficient height 4,160.
The same universal Gram lemma proves exact equality of its zero set with
that source's zero set. Its full data and exact certificates are in `lowheight/`.

The balanced and lower-height companions have different residual coordinate
systems. Their edge indices are local to their own `source_equation.json` and
must not be exchanged.

## Transport of the consistency theorem

Write P_src = sum_i r_i^2 for the input. The lemma proves in elementary real
algebra, hence in ZFC,

    exists x in Z^240, Q(x)=0
    if and only if exists x in Z^240, P_src(x)=0.

Composing this equivalence with the companion exact nonunit projection and
the inherited direct C222 refutation calibration gives

    ZFC proves: no integer zero of Q if and only if Con(ZFC).

The inherited source calibration is a dependency. This component by itself
does not re-prove the proof-calculus-to-ZFC translation, establish Con(ZFC),
or supply a newly compiled end-to-end proof-assistant development. The new
Gram step is a complete ordinary mathematical proof with an exact finite
linear-algebra certificate.

## Verification and discovery

The search used floating-point inverse-matrix updates only to suggest a
finite signed edge set. None of those numerical calculations is part of the
certificate or its proof. The selected edge set is explicit above. Exact
rational factorization, source binding, full sparse polynomial multiplication,
all metrics, and variable liveness are verified using Python's standard
library only, with explicit errors instead of assertions. The verifier also
rejects a singular Gram form and a deliberately incorrect LDL identity.

The final equation does not refer to the search, an optimizer, floating point,
or a positive-definiteness oracle. It contains only the supplied integer
polynomials and thirteen signed products.
