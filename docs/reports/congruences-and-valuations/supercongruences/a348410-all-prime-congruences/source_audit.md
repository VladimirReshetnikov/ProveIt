# Source and priority audit

**Audit date:** 19 September 2026.

This is an evidence ledger, not a certificate that the worldwide literature
has been exhaustively searched.

This file covers the merged report, which combines two independently produced
research reports: `a348410-small-prime-congruences` and
`a348410-cubic-supercongruence`. Where the two disagreed about what a source
establishes, the more cautious statement is kept; Section 2 below records one
such case explicitly.

## 1. Original OEIS target

https://oeis.org/A348410

The page defines the basket-counting sequence and records Peter Bala's
21 February 2022 conjecture that the prime-power differences are divisible
by p^(3r) for p>=5. The inspected live page still calls it a conjecture.
The entry was opened directly; the coefficient formula, the binomial sum,
the algebraic generating-function material, the first 26 displayed values,
and an asymptotic attributed to Kotesovec were all read there. The page's
site-wide footer date is not treated as the date of an edit to that
particular conjecture. The open-status claim in this archive is limited to
that inspected record.

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
rational-framing statement has a problem.

**Status of the odd-prime theorem in the merged report.** The odd-prime
theorem is presented as a first-class theorem of the article, with a
complete self-contained proof (Theorem 1.2, proved in Section 3). That is a
statement about the article's structure, not about priority: priority for the
odd-prime statement is credited to the prior proof candidate above. The proof
is given here because the binary completion depends on the odd-prime bound
and should not rest on an external unreviewed argument.

One of the two merged reports stated that searches centred on the sequence
identifier and its supercongruence did not locate a direct proof. That
statement is superseded by the finding recorded here and is NOT carried into
the merged report: a prior proof candidate was in fact located, at the pinned
commit above.

The source's own status is a proof candidate pending independent review.
We have not converted that status into a claim of journal publication or
formal verification. We also do not certify all unrelated results in its
repository.

## 3. Generating-function literature

Tong Niu, *An explicit algebraic generating function for OEIS A348410*,
version 1, 15 May 2026: https://arxiv.org/abs/2605.16553

Helmut Prodinger, *The generating function of A348410 in OEIS using the
diagonal method and another sequence (A001008) from OEIS*, version 2,
23 May 2026: https://arxiv.org/abs/2605.21255

These sources make the algebraic generating function an unsuitable novelty
claim. Prodinger also extracts a recurrence, so the extraction recurrence is
likewise not claimed as new. The present derivations and exact symbolic
checks are included for coherence and reproducibility, not priority.
Algebraicity is not used to prove any congruence in the article. An
additional search result advertised a proof of the recurrence conjectures on
SSRN; that document was not used as a mathematical premise, and no claim
about its correctness is made here.

## 4. The rational-framing boundary

L. Felipe Muller, *Wolstenholme Type Congruences and Framing of Rational
2-Functions*, arXiv version 1 (21 April 2021):
https://arxiv.org/abs/2104.10754
https://arxiv.org/pdf/2104.10754

The inspected PDF identifies itself as version 1. The statements were checked
against the actual PDF and not only against the HTML rendering, because the
two can differ in the precise quantifiers: PDF page 3 for Theorem 1.1, page 4
for Theorem 1.2 (repeated as Theorem 6.2). Proposition 5.2(3) supplies the
framing coefficient formula and is cited alongside the three theorems. The
quoted version matters: no claim is made about an uninspected revision or a
subsequent correction.

A previously documented period-four counterexample is at:
https://github.com/rbajaj5/a183068-supercongruence/blob/3085b46fdbce945d156d2b5b8b9d1a66627b4375/related-results/RationalFramingCounterexample.md

The merged article supplies TWO independent smaller-period witnesses, both
retained because they buy different things.

- **V_1(x) = x/(1-x) + 3x^3/(1-x^3)**, interpreted over Q(sqrt(-3)), whose
  discriminant is -3 (Section 7.3). Its framed coefficient sequence has
  b(1)=1, b(5)=201, so the difference is 200 rather than a multiple of 125.
  The weighted harmonic sum is 361/144, equal to 4 modulo 5. This witness is
  the smaller of the two.
- **V_3(x) = 3x/(1-x) + 9x^3/(1-x^3)**, over Q alone (Appendix C). Its
  parameter-1 framing has f(1)=3 and f(5)=13428, whose difference 13425 is 50
  modulo 125. The weighted sum in Theorem 1.2 / 6.2 is 361/16, congruent to 1
  modulo 5, for the same input at n=p=5. This witness needs no field
  extension and has no ramified-prime exception: the rational 2-function
  condition is PROVED for it at every prime, by splitting p=3 from p!=3, not
  inferred from a finite test.

361/144 and 361/16 are values for DIFFERENT inputs and are not misprints for
one another; their residues modulo 5 differ, 4 against 1. Both values, and
both quadratic coefficients (11/6 and 33/2), are checked exactly by
`verify.py`, as are 10,000 instances of the rational 2-function condition for
V_3.

The conclusion is limited to the printed precise uniform bounds in version
1. A single exceptional prime does not disprove a weaker statement allowing
an unspecified finite exceptional set or a compensating scalar. No general
claim about all framing results, a possible corrected theorem, or an author's
intentions is made. Since a period-four counterexample was already public,
the observation itself is not claimed as new. None of the article's proofs
uses the disputed statements.

## 5. Asymptotic reference

Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
University Press, 2009, Chapter VIII. Authors' site:
https://ac.cs.princeton.edu/home/

The leading asymptotic for this particular sequence is already on OEIS.
The article derives two correction coefficients and an all-order Gaussian
moment formula without claiming that those standard methods are new.

## 6. Claim status of this archive

- The odd-prime cubic tower, the binary leading-defect formula, and the
  denominator-12/24 consequences all have complete intended proofs in
  `article.tex`. Priority for the odd-prime tower belongs to the prior proof
  candidate of Section 2.
- The binary formula and the sharp denominators were not located in the
  source checks performed here. This does not establish global priority or
  exclude an equivalent result in a differently indexed literature source.
- The finer exact valuation 3r+1 for the basket sequence at powers of two
  is only a conjecture, checked through r=15, and is used in no proof.
- No external refereeing, author notification, OEIS submission, database
  edit, or Lean formalization has been performed.
- No source PDFs, third-party repository trees, or font files are bundled.
