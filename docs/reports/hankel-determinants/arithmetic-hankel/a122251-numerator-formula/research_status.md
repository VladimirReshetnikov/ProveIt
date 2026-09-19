# Research status, attribution, and claim boundaries

**As of 19 September 2026.**

## Why this problem was selected

The source problem is the prime-parameter numerator formula stated in the
comments of OEIS A122251. The entry's title still labels the p=3 assertion
as conjectural, and its comments explicitly give the general conjecture for
prime p. OEIS A122249 separately requests a proof for the p=2 instance.
The entries attribute these records to Paul Barry, 27 August 2006.

The live pages were consulted directly. The site's global modification date
is not treated as the date of an individual conjecture update. A122249 also
records a computational extension from 2024; adding terms is not itself a
proof of the infinite statement.

## Mathematical conclusion

The article gives a complete elementary argument for the stated prime formula.
It establishes a stronger result for all positive steps m and coprime offsets
a, together with a scaling formula for noncoprime parameters. It gives exact
denominator valuations and proves a sharp denominator gcd over all coprime
offsets. The CRT witnesses make the sharpness assertion constructive.

These conclusions rest on the written proofs. They do not rest on extrapolation
from the finite computations. The elementary main argument does not require
MacMahon's enumeration, p-adic completions, or an external computer algebra
system. A second support argument derives the inverse matrix by interpolation.

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
  invention of Cauchy inversion.
- MacMahon's boxed-plane-partition enumeration is classical. Its use is
  confined to a combinatorial interpretation and another divisibility
  explanation after the main elementary proof is complete.
- OEIS A122250 already records the Lambert-series generating function for
  E_3(n). That generating function is not represented as a new discovery.
- Factorial valuations, binomial-basis interpolation, and elementary
  digit-counting methods are standard ingredients, proved here as needed.

## Verification performed

The included Python 3.13.5 run passed 123,298 exact integer/rational checks.
It independently eliminated 2,304 matrices, compared the product and numerator
formulas on a broader 19,008-case parameter grid, verified inverse matrices by
multiplication, and tested all the local residue counts and constructive
primewise gcd witnesses over the ranges given in the article.

Analytic assertions such as the natural boundary are proved in the text;
finite numerical sampling is not claimed to establish them. No proof-assistant
validation or independent peer review took place. The PDF was compiled and
visually reviewed before packaging.

## Not claimed

This research does not classify arbitrary sparse Cauchy minors or determinants
of higher reciprocal powers. The composite-base substitution into the prime
conjecture is explicitly disproved by an exact example. The denominator gcd
is not asserted to equal one actual denominator in every parameter family.
The article does not claim an exhaustive literature search, accepted OEIS
edits, formal verification, or a published priority result.

## Sources

1. https://oeis.org/A122251
2. https://oeis.org/A122249
3. https://oeis.org/A122250
4. C. Krattenthaler, *Advanced Determinant Calculus*, Sém. Lothar. Combin. 42
   (1999), B42q. https://arxiv.org/abs/math/9902004
5. S. Schechter, *On the Inversion of Certain Matrices*, Math. Tables Aids
   Comput. 13 (1959), 73–77. https://doi.org/10.2307/2001955

The archive includes no copies of copyrighted third-party papers. The
`oeis_update_draft.txt` file is only a proposed comment and has not been
submitted to any site.
