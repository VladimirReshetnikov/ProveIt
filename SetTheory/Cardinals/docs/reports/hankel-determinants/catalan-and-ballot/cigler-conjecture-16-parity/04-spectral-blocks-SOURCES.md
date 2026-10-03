# Sources and provenance

## Primary target

Johann Cigler, *Hankel determinants of middle binomial coefficients and
conjectures for some polynomial extensions and modifications*,
arXiv:2111.14492v3, 30 December 2021.

- Conjecture 17 and equations (80)--(83), printed pages 22--23.
- The displayed `K=5` middle block on printed page 24 supplies an immediate
  consistency check against the sign printed in equation (83).
- Source: https://arxiv.org/abs/2111.14492v3

## ProveIt input

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot inspected:
`ffddaa8b9c89e7bf027e1442cc6216bb010906d0`

Principal files:

- `SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/article.tex`
  - proves the rectangular-Schur identity;
  - proves the unique exponential-polynomial spectral decomposition and exact
    degree in the width variable;
  - explicitly records that the full coefficient structure in Cigler's
    Conjecture 17 remains open.
- `SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/02-schur-recurrences-STATUS.md`
  - records proof boundaries and the unresolved Conjecture 17 assertions.
- `SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/code/02-schur-recurrences-verify.py`
  - supplied useful independent definitions and exact test conventions.

## Classical tools used

- Jacobi--Trudi and bialternant formulas for Schur polynomials.
- Confluent Vandermonde determinants and normalized derivative rows.
- Finite differences and the binomial basis for integer-valued polynomials.
- Rectangular Schur complement reciprocity.

The article states and proves the specialized finite identities it needs; these
classical references are context rather than hidden computational assumptions.
