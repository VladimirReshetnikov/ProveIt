# Research status, attribution, and claim boundaries

**As of 19 September 2026.**

## Provenance of this report

This report merges two independently produced research reports on the same
OEIS conjecture: `a122251-numerator-formula` (the base document, whose
structure, notation and macros are retained) and
`a122251-prime-exclusion-proof` (which indexed everything by matrix size
m = n+1). Both proved the shared core theorem by the same argument — Cauchy's
double alternant, an exact residue-square count, Legendre's factorial
valuation, and the same CRT sharpness construction — so that argument is given
once, in the base document's words. Two genuinely different derivations are
preserved side by side and marked in the text: the explicit inverse matrix by
rational interpolation and by a cofactor computation from Cauchy's identity,
and the Lambert-series generating function from second differences and from
first differences. All ported material was reindexed from matrix size to the
OEIS index n, and the two verification suites were replaced by a single merged
run whose counts are reported below. The counts of the two original suites
were **not** added: their ranges overlap and their indexings differ.

## Why this problem was selected

The source problem is the prime-parameter numerator formula stated in the
comments of OEIS A122251. The entry's title still labels the p=3 assertion
as conjectural, and its comments explicitly give the general conjecture for
prime p. OEIS A122249 separately requests a proof for the p=2 instance.
The entries attribute these records to Paul Barry, 27 August 2006.

The live pages were consulted directly, together with their internal records
(`https://oeis.org/A122251/internal`, `https://oeis.org/A122249/internal`).
The retrieved internal revision tags were `#2 Mar 30 2012 18:59:15` for
A122251 and `#6 Oct 27 2024 12:12:17` for A122249; both records retained the
conjectural wording. Those tags, not the page footers, are the evidence for
the phrase "still recorded as conjectural". The site's global modification
date is not treated as the date of an individual conjecture update; footer
timestamps are in Eastern time, which is why the same retrieval is dated
18 September 2026 in America/Los_Angeles and 19 September 2026 by the footer.
A122249 also records a computational extension from 2024; adding terms is not
itself a proof of the infinite statement.

## Mathematical conclusion

The article gives a complete elementary argument for the stated prime formula.
It establishes a stronger result for all positive steps m and coprime offsets
a, together with a scaling formula — numerator and denominator — for
noncoprime parameters. It gives a closed form for the whole reduced fraction,
including a proof (not an assumption) that the stated denominator expression
is an integer, exact denominator valuations, and a sharp denominator gcd over
all coprime offsets. The CRT witnesses make the sharpness assertion
constructive, and a single constructed offset suffices for all primes at once,
so the gcd is already the gcd of two denominators. Dropping the Hankel
symmetry, the same residue count bounds the numerator support of
det(1/(a + m1*i + m2*j)) by the primes of m1*m2 and gives the corresponding
denominator divisibility; no exact numerator formula is claimed in that
generality.

These conclusions rest on the written proofs. They do not rest on extrapolation
from the finite computations. The elementary main argument does not require
MacMahon's enumeration, p-adic completions, or an external computer algebra
system. A second support argument derives the inverse matrix, by rational
interpolation and, independently, by a cofactor computation from the Cauchy
identity proved in the article.

## Historical status is a different question

Targeted searches for A122251, A122249, the numerator formulas, generalized
Hilbert-matrix numerators, and related Cauchy-matrix arithmetic did not locate
a direct earlier proof of the exact OEIS assertion. This was not a systematic
search of all older literature or all publications by the sequence author.

A database entry retaining a conjecture label does not establish that the
conjecture has never been proved elsewhere. The present work should therefore
be described as a proof of the recorded conjecture, with extensions, **not**
as a certified first solution to a long-standing open problem. Priority for
the extensions is also unverified. They may be consequences or restatements
of results in the literature on arithmetic Cauchy matrices.

## Classical ingredients and already-recorded results

- Cauchy's double-alternant determinant evaluation is classical. The article
  supplies a proof and cites Krattenthaler's 1999 survey, Eq. (2.7).
- Cauchy inverse formulas derived by Lagrange interpolation are classical.
  Schechter's 1959 paper is cited. The specialized four-binomial form and its
  prime-support application are worked out in the article, without claiming
  invention of Cauchy inversion. The second, cofactor derivation of the same
  inverse entries uses only the Cauchy identity already proved in the article,
  and is kept precisely because it needs no external result.
- The determinant of the inverse Hilbert matrix, the sequence L_n, is
  classical and recorded as OEIS A005249. Its product form is rederived here
  from the consecutive-size ratio, not claimed as new.
- MacMahon's boxed-plane-partition enumeration is classical. Its use is
  confined to a combinatorial interpretation and another divisibility
  explanation after the main elementary proof is complete.
- OEIS A122250 already records the Lambert-series generating function for
  E_3(n), and OEIS A122247 records the p=2 exponent sequence as the partial
  sums of A005187. Those generating functions are not represented as new
  discoveries; only the uniform general-prime derivations are given here, and
  two independent derivations are kept.
- Factorial valuations, binomial-basis interpolation, and elementary
  digit-counting methods are standard ingredients, proved here as needed.

## Verification performed

The included Python 3.14.4 run passed 159,555 exact integer/rational checks.
It independently eliminated 4,505 matrices (2,304 Hankel, 2,187 unequal-step,
and 14 for the published OEIS terms), compared the product and numerator
formulas on a broader 19,008-case parameter grid, verified inverse matrices by
multiplication, tested all the local residue counts and constructive primewise
gcd witnesses over the ranges given in the article, constructed 160 two-offset
gcd certificates, and compared the seven published terms of each of A122249
and A122251 with directly eliminated determinants rather than with this
article's own formula. This total is from the single merged run; it is not the
sum of the totals advertised by the two reports that were merged.

Analytic assertions such as the natural boundary are proved in the text;
finite numerical sampling is not claimed to establish them. No proof-assistant
validation or independent peer review took place. The PDF was compiled and
visually reviewed before packaging.

## Not claimed

This research does not classify arbitrary sparse Cauchy minors or determinants
of higher reciprocal powers; the unequal-step theorem covers index sets that
are arithmetic progressions, and only the exclusion half. The composite-base
substitution into the prime conjecture is explicitly disproved by an exact
example, as are shift independence and the square property without
coprimality. The denominator gcd is realized as the gcd of two explicitly
constructed denominators; it is not asserted to equal one actual denominator
in any parameter family.
The article does not claim an exhaustive literature search, accepted OEIS
edits, formal verification, or a published priority result.

## Sources

1. https://oeis.org/A122251 (internal record https://oeis.org/A122251/internal,
   revision tag `#2 Mar 30 2012 18:59:15`)
2. https://oeis.org/A122249 (internal record https://oeis.org/A122249/internal,
   revision tag `#6 Oct 27 2024 12:12:17`)
3. https://oeis.org/A122250
4. C. Krattenthaler, *Advanced Determinant Calculus*, Sém. Lothar. Combin. 42
   (1999), B42q. https://arxiv.org/abs/math/9902004 (full text also at
   https://arxiv.org/html/math/9902004v3)
5. S. Schechter, *On the Inversion of Certain Matrices*, Math. Tables Aids
   Comput. 13 (1959), 73–77. https://doi.org/10.2307/2001955
6. https://oeis.org/A005249 (determinant of the inverse Hilbert matrix)
7. https://oeis.org/A122247 (partial sums of A005187; the p=2 exponents)

The archive includes no copies of copyrighted third-party papers. The
`oeis_update_draft.txt` file is only a proposed comment and has not been
submitted to any site.
