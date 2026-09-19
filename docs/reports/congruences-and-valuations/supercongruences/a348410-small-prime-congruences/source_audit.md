# Source and priority audit

**Audit date:** 19 September 2026.

This is an evidence ledger, not a certificate that the worldwide literature
has been exhaustively searched.

## 1. Original OEIS target

https://oeis.org/A348410

The page defines the basket-counting sequence and records Peter Bala's
21 February 2022 conjecture that the prime-power differences are divisible
by p^(3r) for p>=5. The inspected live page still calls it a conjecture.
It also contains the coefficient formula, binomial sum, algebraic
generating-function material, and an asymptotic attributed to Kotesovec.
The page's site-wide footer date is not treated as the date of an edit to
that particular conjecture.

https://oeis.org/A352373

This page states the full integer-parameter odd-prime conjecture for
[x^n]((1+x)^u(1-x)^v)^n. It is the same family under
(u,v)=(-beta,-alpha). It does not supply the binary leading-defect formula
proved in the present article.

## 2. Existing proof candidate: decisive priority correction

Repository: rbajaj5/a183068-supercongruence.
Inspected immutable commit: 3085b46fdbce945d156d2b5b8b9d1a66627b4375.

https://github.com/rbajaj5/a183068-supercongruence/blob/3085b46fdbce945d156d2b5b8b9d1a66627b4375/related-results/CoefficientFramingCubicTower.md

The note contains an elementary proof candidate for the full integer-
parameter odd-prime cubic tower, the loss of one ternary power, rational
parameter extensions, and arbitrary integral coefficient slopes. It
explicitly makes no binary assertion. Its proof uses a reduced logarithm,
a quadratic coefficient estimate, and formal integration by parts.

This source was located during the source audit. The present article does
not claim first resolution of Bala's odd-prime conjecture, first proof of
the odd-prime parameter family, or first recognition that the general
rational-framing statement has a problem. The odd-prime proof is included
as a self-contained alternative, and the main research target is the
previously untreated binary completion within the checked source boundary.

The source's own status is a proof candidate pending independent review.
We have not converted that status into a claim of journal publication or
formal verification. We also do not certify all unrelated results in its
repository.

## 3. Generating-function literature

Tong Niu, *An explicit algebraic generating function for OEIS A348410*:
https://arxiv.org/abs/2605.16553

Helmut Prodinger, *The generating function of A348410 in OEIS using the
diagonal method and another sequence (A001008) from OEIS*, version 2:
https://arxiv.org/abs/2605.21255

These sources make the algebraic generating function an unsuitable novelty
claim. The present derivation and exact symbolic checks are included for
coherence and reproducibility, not priority. An additional search result
advertised a proof of the recurrence conjectures on SSRN; that document was
not used as a mathematical premise, and no claim about its correctness is
made here.

## 4. The rational-framing boundary

L. Felipe Muller, *Wolstenholme Type Congruences and Framing of Rational
2-Functions*, arXiv version 1 (April 2021):
https://arxiv.org/abs/2104.10754
https://arxiv.org/pdf/2104.10754

The inspected PDF identifies itself as version 1. Theorem 1.1, Theorems
1.2/6.2, and the coefficient-framing formula were checked. The PDF pages
containing the principal theorem and harmonic statement were also rendered
for inspection.

A previously documented period-four counterexample is at:
https://github.com/rbajaj5/a183068-supercongruence/blob/3085b46fdbce945d156d2b5b8b9d1a66627b4375/related-results/RationalFramingCounterexample.md

The present article supplies a smaller-period independent witness:
V(x)=x/(1-x)+3x^3/(1-x^3), interpreted over Q(sqrt(-3)). Its framed
coefficient sequence has b(1)=1, b(5)=201, so the difference is 200 rather
than a multiple of 125. The weighted harmonic sum is 361/144, equal to 4
modulo 5. Both values are checked exactly by `verify.py`.

The conclusion is limited to the printed precise uniform bounds in version
1. A single exceptional prime does not disprove a weaker statement allowing
an unspecified finite exceptional set. No general claim about all framing
results, a possible corrected theorem, or an author's intentions is made.

## 5. Asymptotic reference

Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
University Press, 2009, Chapter VIII. Authors' site:
https://ac.cs.princeton.edu/home/

The leading asymptotic for this particular sequence is already on OEIS.
The article derives two correction coefficients and an all-order Gaussian
moment formula without claiming that those standard methods are new.

## 6. Claim status of this archive

- The binary leading-defect formula and the denominator-12/24 consequences
  have complete intended proofs in `article.tex`.
- These formulas were not located in the source checks performed here.
  This does not establish global priority or exclude an equivalent result
  in a differently indexed literature source.
- The finer exact valuation 3r+1 for the basket sequence at powers of two
  is only a conjecture, checked through r=15.
- No external refereeing, author notification, OEIS submission, or Lean
  formalization has been performed.
- No source PDFs, third-party repository trees, or font files are bundled.
