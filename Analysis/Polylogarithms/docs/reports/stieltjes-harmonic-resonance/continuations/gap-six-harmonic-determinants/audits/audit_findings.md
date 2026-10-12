# Audit and new result: complex harmonic degree

Pinned repository commit: `c4036d60715916ae72dd18983782fdb182840b86`.

## Solved source question

The incoming archive `docs/incoming/ProveIt_Bilinear_Tails_and_Determinants_2026-10-11.zip`
contains `ProveIt_Bilinear_Tails_and_Determinants_2026-10-11/sections/10_research_questions.tex`.
Lines 91–100 ask whether generic harmonic degree equals generic pencil rank for
every complex rational weight.  The existing real theorem is in
`sections/05_degree_rank.tex`, labels `deg:main` (line 106), `deg:rational`
(line 163), with its real-only limitation at lines 183–187.

`complex_rank.tex` proves the full complex assertion, in fact over every field
of characteristic zero.  Its central theorem is independent of the harmonic
setting: a rational symmetric matrix primitive with difference
`w(z) p(z) p(z)^T`, nonzero rational `w`, and constant-linearly independent
rational components of `p`, is always generically nonsingular.  Proof:
rationality forces generic rank to stabilize at sufficiently large integers;
equal ranks under a symmetric rank-one update force the image to remain fixed;
independence of `p` contradicts that fixed deficient image.  Complex isotropic
vectors do not break the rank update: an explicit principal minor is
`c w_j^2 det(A0)`.

The fragment contains rational denominator-degree bounds for possible
exceptions and the inherited coefficient-gcd exact test over complex fields.
It also provides explicit three- and four-dimensional adjacent-pole identities,
a genuinely nonreal later exception at N=3, and a discrete-residue interpretation.
The source is valid and is strengthened; no false source theorem is alleged.

## Verification

Run `python work_audit/verify_complex_rank.py`.
It writes `complex_rank_verification.json`; the completed run passes 66 exact
checks over rational arithmetic with i and symbolic parameters.  It includes:

- exact symbolic rank-one minor identity and a nonzero isotropic lower vector;
- independent finite moments versus harmonic decomposition;
- r=3 and r=4 adjacent-pole highest coefficients;
- full exceptional cutoff determinant polynomial at N=3 and a separate
  Vandermonde-product evaluation;
- an explicitly constructed rational weight with a varying-kernel pencil
  `[[0,X,0],[X,0,iY],[0,iY,0]]`, so the test does not only cover common kernels.

The last weight is

R(n) = (n^3+15n^2+85n+225)/((n+1)(n+2)(n+3)(n+4)(n+5))
       + i(n+25/2)/((n+1/2)(n+3/2)(n+5/2)(n+7/2)(n+9/2)).

The rational compression has denominator
`840 (N+2)(N+3)(N+4)(N+5)(2N+3)(2N+5)(2N+7)(2N+9)`
and numerator degree 11.  Thus its degree certificate is finite and explicit.

## Priority and primary references

The general rational summability/discrete residue criterion is classical, not
a new result here.  Chen and Singer, *Residues and telescopers for bivariate
rational functions*, Advances in Applied Mathematics 49 (2012), 111–133,
Proposition 2.5, DOI `10.1016/j.aam.2012.04.003`.

- https://arxiv.org/abs/1203.4200
- https://arxiv.org/html/1203.4200v1 (Proposition 2.5, lines 139–154 in fetched view)
- https://singer.math.ncsu.edu/papers/YAAMA1465.pdf

The general multiplication-of-measure determinant identity used for the parent
agent's proposed all-r adjacent-pole formulas should be credited to the existing
orthogonal-polynomial literature.  A particularly convenient precise source is:
C. Krattenthaler, *Hankel determinants of linear combinations of moments of
orthogonal polynomials, II*, Ramanujan Journal 61 (2023), 597–627.

- https://arxiv.org/abs/2101.04225 (version 5)
- https://doi.org/10.1007/s11139-021-00514-8

Its abstract explicitly describes the d-by-d determinant reduction, with four
proofs.  An all-r adjacent-pole/harmonic specialization and its exceptional
residue parameter interpretation can be claimed as new relative to inspected
repository material, while the general Christoffel determinant formula cannot.

Finite orthogonal polynomial zeros and simplicity are covered by:
https://dlmf.nist.gov/18.2, especially sections (i) and (vi).

The published general zeta-tail product/MZV reduction predates the repository:
M. E. Hoffman, *Sums of Products of Riemann Zeta Tails*, Mediterranean Journal
of Mathematics 13 (2016), 2771–2781, DOI `10.1007/s00009-015-0653-9`.

- https://arxiv.org/abs/1602.03399
- https://arxiv.org/html/1602.03399v1

## Avoided duplication

The canonical reports already prove equal/adjacent/gap-four prefix families;
the latest incoming Bilinear and Bernoulli archives complete smaller order ten.
The old order-eight exceptional residue class is no longer the freshest target.
The smaller-order-twelve family is also already completed in the latest
Ordered Boundary and Balanced incoming material. The full gap-six family
remained open in the inspected snapshot and is completed by the new effective
Gamma estimate and exact finite certificate in the present research. No new
false theorem was located in the targeted prior
shifted-tail and determinant material before changing focus to the genuinely
open complex-weight question.
