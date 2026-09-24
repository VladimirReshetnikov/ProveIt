# Sources and status audit

Consulted on **19 September 2026**. These links identify the original
sources; the source papers themselves are not redistributed.

## The target and its revision history

**OEIS A377000** — https://oeis.org/A377000

The retrieved entry defines the esthetic-number array and labels three
statements as conjectures attributed to Chai Wah Wu on 21 October 2024:
the even-base differential-composition correspondence, row recurrences,
and the A182555 diagonal. It also suggests an A206603 diagonal.

**A377000 revision history** — https://oeis.org/history?seq=A377000

The retrieved history's newest displayed revision is #45, dated
5 November 2025, changing an arXiv link from HTTP to HTTPS. The current
search result and the history provide evidence beyond the older cached
main-page footer. A site-wide “last modified” footer is NOT interpreted
as the last mathematical edit to this particular sequence.

No separate resolution was located in the targeted searches. This does
not establish absence of an unpublished proof or an equivalent result
under different terminology. The article accordingly claims proofs of
the **listed statements**, not an independently certified new theorem in
the worldwide historical sense.

## Established mathematical background

Jean-Marie De Koninck and Nicolas Doyon, *Esthetic Numbers*,
Annales des sciences mathématiques du Québec 33 (2009), no. 2, 155–164.

https://www.labmath.uqam.ca/~annales/volumes/33-2/PDF/155-164.pdf

Equation (17), on printed page 162, gives the spectral enumeration of the
row counts. The article's spectral formula is an equivalent half-angle
version, independently derived from the reflection-orbit identity.
Recurrence existence already follows immediately from this published
formula; it is not presented as new here.

Branko J. Malešević, *Some combinatorial aspects of differential operation
composition on the space R^n*, Univ. Beograd. Publ. Elektrotehn. Fak.,
Ser. Mat. 9 (1998), 29–33; arXiv version posted in 2007.

https://arxiv.org/abs/0704.0750
https://arxiv.org/pdf/0704.0750

Printed page 31 describes the field types and operation graph, including
the odd-dimensional middle self-map. Equation (6) supplies the
operation-index adjacency rule used for an independent verification.
Meaningful formal words include words representing zero operators.

## The two sequence identifications

**OEIS A182555** — https://oeis.org/A182555

The sequence is defined by the generating function
(3-4z-sqrt(1-4z^2))/(2(1-2z)^2), starting at index zero. The article proves
that its positive-index coefficients equal T(k+2,k).

**OEIS A206603** — https://oeis.org/A206603

The entry describes the maximal apex of an addition triangle whose base
permutes {j-k/2: j=0,...,k}, and supplies the corresponding generating
function. The article proves the diagonal identity both by generating
functions and directly by sorting the binomial weights.

## Contribution boundary

The original papers are credited for their models and spectral formula.
The manuscript develops a single bijective explanation of the listed
relations and a uniform exact finite-width correction formula. From that
formula it derives fixed-offset polynomial corrections, their sharp
threshold, all finite exceptions, and the common quadratic irrational
part of every diagonal generating function.

These arguments are fully written out in the article. Their validity is
separate from historical priority, which remains unverified beyond the
stated literature search. No assertion is made that the manuscripts
cited above anticipated none of these consequences.
