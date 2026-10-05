# Source and attribution record

Checked October 5, 2026. These links identify source material; third-party PDFs
are not included in this package. Search results are bounded evidence, not a
certificate of global historical priority.

## Exact statement proved

Manuel Kauers and Christoph Koutschan, *Some D-Finite and Some Possibly D-Finite
Sequences in the OEIS*, Journal of Integer Sequences 26 (2023), Article 23.4.5.
Primary paper: https://arxiv.org/abs/2303.02793 (version 2, April 24, 2023).
Section 6.4 defines the arrays; Conjecture 18 is on printed page 33, PDF index 32.
The actual statement is the rising-factorial finite sum for n>1. The report
transcribes its prefactor, factor 3, summation limits, and generalized binomial
term, and proves exact equivalence by factorial cancellation.

OEIS A181198: https://oeis.org/A181198 and https://oeis.org/A181198/internal.
The retrieved internal snapshot still labels the order-two recurrence and finite
sum conjectural; its revision record is revision 39, January 1, 2024. The snapshot
was inspected October 5, 2026. Continued conjectural labeling does not establish
that no proof exists elsewhere. No OEIS edit is part of this deliverable.

## Prior results credited

*Fixed-height shifted rectangles: asymptotics and algebraicity*, October 3, 2026,
research report prepared for Vladimir Reshetnikov.
Source: https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles/article.tex
Inspected Git blob: 2b40ded9daa6549f786a52b880d5477de3b5adfc.
This report proves all-height leading constants and all-fixed-order expansions;
it expressly leaves the specific height-four and height-five operators unproved.
The present leading asymptotic is credited as recovered prior work.

*Rational diagonals and rare boundary phases in shifted rectangles*, October 4,
2026, companion report, 24 pages, inspected user-held copy. Its rational
diagonality and D-finiteness theorem is prior work relative to this report.
Its research questions leave the particular operators open. It is cited only
for overlap disclosure, not used as a mathematical dependency or redistributed.

Ping Sun, *Enumeration of standard Young tableaux of shifted strips with constant
width*, Electronic Journal of Combinatorics 24(2) (2017), P2.41.
Preprint: https://arxiv.org/abs/1506.07256.
Background on shifted-strip enumeration, hook products, and order statistics.
The present proof supplies its elementary determinant/Pfaffian identities directly.

NIST DLMF, https://dlmf.nist.gov/5.11, equation 5.11.1 and Section 5.11(ii).
The positive-real Stirling logarithm remainder is bounded in absolute value by
the first omitted term. This is the cited analytic input to the explicit error
construction; checked directly on October 5, 2026.

## Bounded priority check

Targeted A181198 / Conjecture 18 identifier and exact-coefficient searches did
not find a matching proof in the inspected material. The 2026 paper
https://arxiv.org/abs/2607.24832 was also inspected without finding a matching
height-four proof. This is not an exhaustive literature search. No first-ever
claim is made. The theorem proves the supplied mathematical statement regardless
of its eventual historical-priority assessment.

## Scope separation

- Proved here: the full height-four counting-to-period reduction, exact
  polynomial certificate, specified first-order identity, specified OEIS
  operator, and actual Conjecture 18 finite sum
- Derived here from that recurrence: a rational coefficient engine and effective
  fixed-order bounds, finite Lambert-W models, and qualified threshold envelopes
- Credited prior work: the leading asymptotic, existence of all-order fixed-height
  expansions, and D-finiteness established by other approaches
- Not claimed: height-five Conjecture 19, a canonical full exponentially small
  transseries, peer review, proof-assistant verification, or exhaustive priority
