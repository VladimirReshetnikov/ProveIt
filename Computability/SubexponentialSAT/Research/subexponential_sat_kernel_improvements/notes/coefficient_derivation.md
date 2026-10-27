# Exact packet coefficient extraction: practical improvement

## Scope and repository novelty

Pinned repository: `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.

The inspected seven indexed packets and seven incoming archives all retain
the streamed homogeneous finite-difference routine in
`Computability/SubexponentialSAT/Research/eth_contraction_improvements/code/packet_extraction.py`.
Search of all delivered `.tex`, `.py`, `.md`, and `.txt` sources found no
Gray traversal, centered arithmetic-grid polarization, or antipodal pairing
proposal. The incoming asymmetric, joint Cauchy, recursive, balanced-packing,
round-two, and packet-refinement texts explicitly allow the old routine.

This is a new integration and implementation within the inspected snapshot,
not a claim that Gray codes or polarization are new mathematics. The
squarefree specialization is the classical Glynn permanent identity.
Primary bibliographic source verified online: David G. Glynn, "The permanent
of a square matrix", European Journal of Combinatorics **31**(7), 1887-1891
(2010), DOI `10.1016/j.ejc.2010.01.010`.
Publisher: https://www.sciencedirect.com/science/article/pii/S0195669810000211
Author's institution:
https://researchnow.flinders.edu.au/en/publications/the-permanent-of-a-square-matrix/
Web retrieval refs, which root must open before citing: `turn3search0`,
`turn3search2`. The complete proof below is self-contained.

## Problem

Given R affine forms over

    A_p = (Z/2^p Z)[U,V] / (f(U), V^ell),

where f is any monic integer polynomial, compute a requested coefficient
`[Z^beta] product_r (a_r0 + sum_j a_rj Z_j)`.
The coefficient ring need not be a domain, and f need not be irreducible.
Homogenize using beta_0 = R-sum(beta_j). An impossible target has answer zero.
For a possible target let b=(beta_0,beta_1,...,beta_q), so |b|=R, and

    H(X) = product_r sum_i a_ri X_i,
    G = product_i (b_i+1),
    nu = sum_i v2(b_i!),
    O = sum_{i: b_i odd} b_i.

Delete coordinates with b_i=0 from the exponential loop: their grid
coordinates are identically zero. The original input is retained only once.
The shipped reference uses G evaluations at p+nu working bits and
reconstructs all row values at every grid point.

## Refinement 1: Gray traversal

A reflected mixed-radix Gray traversal visits the box `0<=g_i<=b_i` with one
unit coordinate change per transition. Maintain R row values, changing each
by `+a_ri` or `-a_ri`. Update the integer binomial product exactly by

    C(b_i,g_i+1)/C(b_i,g_i) = (b_i-g_i)/(g_i+1),
    C(b_i,g_i-1)/C(b_i,g_i) = g_i/(b_i-g_i+1).

These are integer-exact updates of the whole product, never division by an
even residue in A_p. Sign flips at every transition. The product of R row
values is then accumulated. This preserves p+nu working precision and G
evaluation points, and changes dense affine evaluation from O(R q G) ring
operations to O(input size + R G), with polynomial working space.

## Refinement 2: anisotropic centered antipodal grids

Choose the smallest positive integer steps for which centers are integral:

    h_i = 1 if b_i is even, 2 if b_i is odd,
    x_i(g_i) = h_i*g_i - h_i*b_i/2.

For any homogeneous polynomial H of total degree R=|b|,

    sum_{0<=g<=b} (-1)^{R-|g|} product_i C(b_i,g_i) H(x(g))
      = product_i (b_i! h_i^{b_i}) [X^b]H.

Proof: expand H in monomials. Each one-variable b_i-th difference kills a
monomial whose exponent in X_i is less than b_i. Since total degree is R,
the only monomial surviving all differences is X^b. Its i-th difference
equals b_i! h_i^{b_i}. This holds as a polynomial identity over Z, hence in
every commutative algebra before taking residues.

Complementation g -> b-g replaces x by -x. It multiplies H by (-1)^R
and the signed binomial weight by (-1)^R, so both terms are identical.
When every b_i is even, the only fixed point is the midpoint x=0; its
contribution is zero for R>0. Thus any representative set P containing one
point from each noncentral antipodal pair satisfies

    sum_{g in P} (-1)^{R-|g|} product_i C(b_i,g_i) H(x(g))
      = D [X^b]H,
    D = 2^{O-1} product_i b_i!,
    v2(D) = nu+O-1.

D is integral for every R>0. If O>0, O>=1; if O=0, at least one b_i is an
even positive integer and nu>=1. Degree R=0 is handled directly.
The number of product evaluations is exactly floor(G/2).

### Precision and ring correctness

Take creation-time canonical input coefficient representatives at p bits,
exactly as the shipped implementation does. Compute the representative sum
modulo 2^(p+nu+O-1). Its canonical coordinates are divisible by
2^(nu+O-1). Divide coordinates by that power of two in Z, then invert the
odd integer part of product_i b_i! modulo 2^p. Return the canonical output
modulo 2^p. This works because the quotient algebra by monic f and V^ell is
a free Z-module; reduction and the exact coordinate division commute in
the specified precision window. It never assumes canonical lifting is
multiplicative and never inverts an even residue.

Special cases:

* All b_i even: floor(G/2)=(G-1)/2 samples and **p+nu-1 working bits**, one
  fewer than the shipped full-grid routine.
* Exactly one odd b_i=1: G/2 samples at **the same p+nu working bits**.
* All b_i in {0,1}: G/2=2^(R-1) samples at p+R-1 bits, the Glynn case.

The anisotropic step choice minimizes the denominator's 2-adic valuation
among symmetric arithmetic grids with integer points: h_i*b_i must be
even, hence an odd b_i forces v2(h_i)>=1; even b_i permits h_i=1.
The resulting denominator valuation is sharp for this functional because
H=X^b has coefficient one and its representative numerator is exactly D.

### Streaming half-grid

If any b_j is odd, restrict that coordinate to
`0<=g_j<=(b_j-1)/2` and use full ranges elsewhere: one rectangular box.
If all are even, partition representatives by the first coordinate j
strictly below its midpoint: previous coordinates equal b_i/2, coordinate
j ranges from 0 to b_j/2-1, and subsequent coordinates use full ranges.
These disjoint boxes total (G-1)/2 samples. Each box admits the same Gray
traversal. Initial row evaluations are rebuilt once per box. Since there
are at most q nonzero exponents and in the all-even case G>=3^q, these
initializations are absorbed by O(R G) ring operations. Only a current
point, integer weight, R row values, and the accumulator are stored.

## Deliverable code

`code/streamed_coefficients.py` implements both Gray-only and
anisotropic antipodal Gray methods. `baseline_packet_extraction.py` is the
unmodified inspected reference implementation copied from the pinned repo.
`verify_and_benchmark.py` independently compares all methods to truncated
direct polynomial multiplication and records timing distributions.

Verification completed for both Python normal and `-O` execution:

* 340 exhaustive reflected-Gray product boxes, checking complete coverage
  and no duplication.
* 1,392 exhaustive small binary-coefficient scalar extraction cases.
* 900 random cases across five rings, including quadratic extensions,
  V-nilpotents, reducible/non-etale monic f, negative input representatives,
  zero-degree products, impossible targets, and all-even midpoint cases.
* All four coefficient methods agree exactly.

The benchmark result JSON contains all raw repetitions, medians, inputs,
seeds, ring parameters, precisions, exact evaluation counts and outputs.
The suite rotates method order and uses three timed repetitions per case.
The matrix families include squarefree, paired exponents, three modes,
mixed exponents, one-odd-exponent, many zero exponents, high and low working
precision, and extension/nilpotent rings. Each benchmark answer is checked
against direct polynomial DP outside the timed region.

## Interpretation and limits

The arithmetic and evaluation-count improvement is rigorously proved.
The timings are measured **packet coefficient-kernel** timings on
deterministically generated matrices, not end-to-end SAT runtimes or
results on industrial SAT instances. The squarefree case needs more
working bits; halving the number of evaluations alone does not guarantee
halving wall time on every input/ring. Gray-only retains the original
precision. This local replacement composes with every inspected successful
Cauchy, density, precision and packing proposal because it returns exactly
the same creation-precision tensor entry. It does not prove a better
global logarithmic exponent for 3-SAT or exact counting, whose dominant
enumeration remains elsewhere.

## Root's projective extraction: independent implementation review and tests

Root subsequently implemented `code/projective_coefficients.py`,
which applies a roots-of-unity filter with one smallest-positive-exponent
axis fixed to one. I reviewed that code independently. Every positive
homogenized exponent must be 1 or 2 for the delivered specialization.
The implementation checks the supplied cube root at the actual augmented
working precision. No additional coefficient-ring extension is allocated.

Let q1 be the number of positive homogenized exponents equal to one and
q2 the number equal to two. If q1>0, a one-exponent is fixed, giving
2^(q1-1)*3^q2 evaluations at p+q1-1 bits. If q1=0, a two-exponent is fixed,
giving 3^(q2-1) evaluations at p bits. The all-two case thus improves both
the antipodal evaluation count and its precision. In mixed cases the
evaluation count equals antipodal's and the working precision is smaller,
but extra coefficient-ring multiplications can still cost time.

`verify_projective.py` passes both normal and optimized (`-O`) Python:
10,028 exhaustive binary-coefficient cases; 813 random exact comparisons
of DP, the shipped finite differences, antipodal Gray, and projective
extraction; degree-zero and impossible targets; and four invalid-input
rejection checks. Tests include a root valid only at creation precision,
which must be rejected at the augmented working precision, and a
counterexample showing why the pivot must have minimum positive exponent.
The degree-four quotient by `U^4+U^2+1` is tested with explicit cube root
U^2, so the API is tested beyond its automatic quadratic default.

`benchmark_projective.py` generated ten same-input, three-repetition cases.
Representative results (medians, seconds):

| Family | Shipped | Antipodal | Projective | Projective/old speedup |
|---|---:|---:|---:|---:|
| R18, nine exponents2, quadratic ring | 2.914805 | 0.553943 | 0.422439 | 6.90x |
| R12, six exponents2, quadratic ring | 0.054527 | 0.013824 | 0.009337 | 5.84x |
| R12, six exponents2, nilpotent ring | 0.080007 | 0.024649 | 0.017121 | 4.67x |
| R12, six exponents2, p=1 | 0.044650 | 0.009691 | 0.006115 | 7.30x |
| R12, six exponents2, p=256 | 0.058326 | 0.017524 | 0.011246 | 5.19x |

For R18 the three grid counts are 19,683, 9,841, and 6,561; the three
working precisions are 41, 40, and 32 bits. Mixed cases are roughly tied
against antipodal (projective speedup 0.966 to 1.005), and the smallest
all-two case is also slightly slower than antipodal. These observations
support retaining both kernels, not a universal speedup claim for
projective over centered extraction.

Projective coefficient filtering also has classical algebraic provenance:
Carlini, Catalisano and Geramita, "The solution to the Waring problem for
monomials and the sum of coprime monomials", Journal of Algebra **370**
(2012), 5-14, DOI `10.1016/j.jalgebra.2012.07.028`.
Primary versions: https://arxiv.org/abs/1110.0745 and
https://arxiv.org/abs/1112.3474. Their monomial rank expression is
product_i(b_i+1)/(1+min_i b_i). Do not claim the root-grid principle is new.
