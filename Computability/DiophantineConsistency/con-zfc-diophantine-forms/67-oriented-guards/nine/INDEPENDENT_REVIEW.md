# Independent review of the nine-positive composition

Status: PASS for the new composition, conditional on the explicitly inherited
original31 compiler, fixed-tuple adapter and numerical ratio theorem.
Reviewed against nine/PROOF.md and generated literal DAGs on 2026-10-23.
This is a second internal mathematical/code review, not external peer review
and not a new proof-assistant kernel check.

## Mathematical review

1. Free C is not constrained prematurely. For C>=1, A>=3, J>0,
   D>=A^2, Lm=CD+1-A>0, F>=A^2, G>A and H>=1. The quotient shift
   E0=Jn+(J-2)W1^2+3W1C+2 is strictly positive even when Q is negative.

2. The real four-root factorization is valid before any root-integrality claim:
   a0 and a1 are positive. Both unconditional strict majorants make
   V0+V1+u0+u1>0 for every signed choice of real roots. Thus a zero implies
   m>0, without relying on distinct radicands. The case m=0 is separately
   excluded by E0^4>0. This ordering removes the need for an artificial
   separation gap or an extra h multiplier.

3. Positive margin gives |C-KY|<K/2, hence C>K and the old carrier range
   C>B1+W1. The latter uses Y>=64, K>=P+R, and P>U>=W1, so it is not an
   asymptotic comparison. Now a1>C^2 A^4>K^2 P^2>a0, since A^2>P.
   Therefore the rational signed root sum cannot vanish. The elementary
   identity 2xu0=x^2+a0-b1 gives rationality of both roots, and integral
   square roots follow from rational-square integrality. Divisibility J|Q
   then follows from the exact defining equality.

4. The CRT shift is the inherited free-coordinate bijection, not an assumption
   that a nonnegative index may be made positive arbitrarily. The coordinate
   j0=j-1 is retained. F=1 modulo J and C gives the displayed inverse
   j_old=1+((F-1)/C)B1+F j0. The converse uses the inherited divisibility
   witness and B1<C; that dependency is explicitly retained.

5. Baseline strictness is valid already for C=1: e>=7 and
   (8D+1)e^2-64D>0. For higher orders the exact truncation defect is a
   nonzero polynomial with nonnegative coefficients. The four remainder
   identities hold as formal polynomials. At orders1--3, only r1 can be
   negative, and its adverse part is <288i before division by scale;
   correction 512i/scale+lambda suffices. At order4, the bound
   252ie^2+(765/2)i is strictly below 256i(e^2+2).

6. The concavity step was rederived rather than accepted from numerical
   examples. With X=e^2D^3(D-1), G=XLm/D+CD+1,

       sqrt(X+D)G < sqrt(X)(G+Lm/2)
                         +(CD+1)/(2eD sqrt(1-1/D)).

   Its final fraction is below1 for A>=3,C,i>=1. Thus each selected
   correction proves the required strict majorant uniformly in arbitrarily
   large i. No asymptotic truncation theorem is being used.

7. Completeness needs no majorant gap: choose positive integral roots and
   n=m(V0+V1+u0+u1)-W1^2-Q/J. Integrality is immediate. One can verify
   W1^2+Q/J<2D explicitly from W1<A, J=4A-5, and D>=A^2:
   Q/J<3AC/(4A-5)<2C, while W1^2<A^2<=D and 2C<D.
   Meanwhile F>D and lambda>=8 yield V1>lambda sqrt(DF)G>2D.
   Thus n>0. This closes both directions without an unproved cofinality step.

## Independent implementation checks

check_majorant_sympy.py imports no author builder/verifier. With SymPy1.14.0
it checks all four remainder identities, the five complete division-free
majorant defect identities, and the two-defect norm expansion by exact
symbolic expansion. Results are in MAJORANT_SYMPY.json.

check_nine_independent.py imports no author builder/verifier. It reads actual
coefficient payloads, independently traverses live DAG nodes, counts binary
operations, propagates a total-degree upper bound and the corresponding
diagonal leading coefficient modulo three primes. In each of the twelve
order/domain variants the final certificate leader is nonzero. Therefore the
upper degree bound is attained for the actual coefficient tuple, not just
for generic formal ports. Subtracting 16deg(D) gives the primary degree,
using the independently reviewed exact certificate identity. Results are in
NINE_INDEPENDENT.json.

Confirmed positive endpoints:

- baseline: degree1731700, 462 operations;
- order0: degree1731700, 465 operations (dominated);
- order1: degree1663788, 475 operations;
- order2: degree1595876, 478 operations;
- order3: degree1527964, 482 operations;
- order4: degree1494006, 487 operations.

The natural variants also pass; their source-domain shifts are explicit.
The degree certificate is not substituted for the primary equation.

Minor wording improvement communicated: call the truncation defect's
nonzero coefficients positive, since some missing coefficients are zero.
No mathematical blocker was found.
