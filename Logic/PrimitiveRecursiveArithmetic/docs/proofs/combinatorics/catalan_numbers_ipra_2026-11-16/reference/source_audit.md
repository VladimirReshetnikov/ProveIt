# Source audit

Audit date: 2026-11-16

## Requested public pages

1. Wikipedia, **Catalan number**  
   <https://en.wikipedia.org/wiki/Catalan_number>

   Claims inventoried include the central, difference, and odd-binomial
   formulas; Segner and ratio recurrences; asymptotics; valuations, parity,
   primes, and last digits; integral and random-walk formulas; the listed
   combinatorial interpretations; all six formula proofs (each developed in
   the report); three Hankel determinant assertions and uniqueness; ballot, super-Catalan, Coxeter, moment, rational
   Catalan, and k-fold convolution statements.

2. Wolfram MathWorld, **Catalan Number**  
   <https://mathworld.wolfram.com/CatalanNumber.html>

   Claims inventoried include formulas (1)-(7), sums (8)-(12), product (13),
   the Riordan transform, generating functions (14), (16), (18), (19), the
   asymptotic expansion (20), decimal-digit convergence, recurrences (21)-(23),
   arithmetic facts, listed combinatorial models, Fuss-Catalan formulas
   (24)-(25), generalized Jonah formula (26), explicit formula (27), and
   convolution (28).

The mathematical claims are restated in the report rather than copied
verbatim. Source-specific computational and historical statements are marked
as such in `claim_map.csv`.

## Source corrections found during proof audit

The Coxeter paragraph of the Wikipedia revision is not correct under the
standard definitions.  The report records and proves the following repairs:

- standard generalized Catalan numbers satisfy `Cat(A_n)=C_{n+1}`, so the
  ordinary `C_n` corresponds to `A_{n-1}`;
- fully commutative elements are not generally equinumerous with root-poset
  antichains (`B_2` gives 7 versus 6);
- the unweighted sum over maximal proper subdiagrams fails for standard
  generalized Catalan numbers (`A_2` gives 5 versus 4); the report proves the
  correctly weighted type-A relation.

These are marked `SOURCE_CORRECTION` in `claim_map.csv`, rather than being
silently accepted or discarded.

## ProveIt repository

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Inspected branch snapshot:

`00bbe871268c453903499fb6afe07519e87d9631`

Key paths:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Combinatorics/Binomial.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Combinatorics/BinomialIdentities.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/combinatorics/bell_numbers_ipra/`
  (used only as a packaging/style precedent)
- `SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/`
  (relevant broader repository context)

Checked theorem names reused from `BinomialIdentities.lean`:

- `binom_sum`
- `central_binomial`
- `catalan_ratio`
- `catalan`

The exact existing Catalan formula is the universal closure of

`(n+1) * (binom (2*n) n monus binom (2*n) (n+1)) = binom (2*n) n`

with the source's shifted open-variable convention. No new kernel-check claim
is made for the Lean files in this package.

## Environment limitations

- Internet access from the container was unavailable; public pages were read
  through the web retrieval tool and repository files through the GitHub
  connector.
- `lean` and `lake` were not installed.
- `pdflatex` and Python were available; the report and exact checker were built
  and run locally.
