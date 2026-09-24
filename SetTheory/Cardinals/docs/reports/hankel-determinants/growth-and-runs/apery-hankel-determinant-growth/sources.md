# Source audit and precise problem status

Audit date: 18 September 2026.

## Selected conjecture

OEIS A228143, internal revision #40, timestamp `Sep 13 2026 08:32:57`:
https://oeis.org/A228143/internal

Its `%F` entry, attributed to Vaclav Kotesovec on September 13, 2026, conjectures
that the n^2-root of the (n+1)-by-(n+1) Apéry Hankel determinant tends to
(1+sqrt(2))^4/4. This is the target of the report. The accessed revision still
called that assertion a conjecture. Other arithmetic assertions on the page
are not the target of the report. The first ten displayed terms were used only
as an external check of independently generated exact integers.

The internal revision is the concrete status evidence. Supplementary keyword
searches were sparse or noisy and do not establish worldwide priority. In
particular, a recent conjecture date does not prove that no earlier general
result implies it.

## Known analytic input

G. A. Edgar, *The Apéry Numbers as a Stieltjes Moment Sequence*,
arXiv:2005.10733v2, 2 September 2020:
https://arxiv.org/abs/2005.10733
https://arxiv.org/html/2005.10733v2
https://arxiv.org/pdf/2005.10733

Precise locators (printed page numbers):

- Theorem 1, p. 1: positive absolutely continuous moment representation.
- Notation 3 and Proposition 4, p. 2: endpoint constants and Frobenius bases.
- Notation 6, p. 3: endpoint normalizations of the named solutions.
- Definition of the density, pp. 4-5: it solves the displayed Fuchsian equation
  on each of the two open subintervals.
- Propositions 25-26, pp. 14-16: density proportionality constants and endpoint
  behaviors.
- Corollary 27, p. 16: strict positivity on both open subintervals.
- Equation (1), p. 1: recurrence used for exact computation.

The report uses C=17+12*sqrt(2) and c=C^(-1). Edgar uses c and c_0 for these
same two constants. Confusing them would yield an incorrect interval length.
No third-party full paper or figure is redistributed in this archive.

## Definition and computation cross-reference

OEIS A005259:
https://oeis.org/A005259

Used for the identification of the Apéry numbers, their defining binomial sum,
and their recurrence. The 401 moments used in the principal computation were
independently recomputed directly from the sum.

## Orthogonal-polynomial background

NIST Digital Library of Mathematical Functions, §18.2:
https://dlmf.nist.gov/18.2

Relevant: monic polynomial norms; §18.2(ix), moments and Hankel determinants;
the caution after equation 18.2.30 about numerical conditioning. The report
gives its own Gram-factorization, norm-comparison, and power-weight determinant
arguments; no unquoted Szegő asymptotic theorem is required.

## Distinguishing theorem, computation, and priority

The main and shifted limits follow from the written proofs plus the explicitly
credited density theorem. Exact determinant tables are finite verification,
not evidence promoted to an infinite proof. The numerical decimals are not
interval-certified. This report is not peer reviewed or Lean-formalized.
A proof of a still-labelled OEIS conjecture is not, by itself, a certificate of
originality relative to the entire mathematical literature.
