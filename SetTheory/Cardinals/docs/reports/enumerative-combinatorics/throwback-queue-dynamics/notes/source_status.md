# Source and status check

Date of check: 19 September 2026.

## Selected primary source

Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive
Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, 18 pages.

https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.pdf
https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.html

The discussion immediately after Theorem 2, on printed page 4, explicitly
leaves the repeated-entry recurrence classification unresolved. Printed page
16 discusses the remaining perfect-mixing characterization problem. The PDF
page containing the recurrence question was also inspected as an image.

The source's distinct-input recurrence theorem is already proved. The present
article does not claim to newly prove the original A357081 recurrence conjecture.

## OEIS pages consulted

- A357081: https://oeis.org/A357081
- A000108: https://oeis.org/A000108
- A000312: https://oeis.org/A000312
- A003320: https://oeis.org/A003320

A000312 already records the prime-parking-function interpretation of n^n.
A003320 already defines the maximum-of-powers sequence. Their appearances here
are established throwback interpretations, not claims that the sequences or
classical enumerations themselves are new.

## Search scope and limitation

Public searches used the exact article title, the authors' names together
with throwback, and combinations of throwback sequences with repetition,
recurrence, perfect mixing, parking functions, and 2026. The JIS volume pages
and relevant OEIS entries were also inspected. Results were often sparse or
irrelevant. No later resolution of the selected repeated-entry or general
perfect-mixing questions was located.

This is not an exhaustive citation-index search, a check of unpublished work,
or a proof of priority. The proper claim is: the questions are explicitly open
in the cited 2025 paper, and this manuscript gives self-contained proposed
solutions whose proofs and priority should be independently reviewed.

## Distinctions preserved in the manuscript

1. Token recurrence is stronger than numerical-value recurrence when weights
   repeat. Both are addressed, and are never silently identified.
2. The exact recurrence core depends on the first overloaded *initial prefix*,
   not merely the globally smallest overload threshold.
3. All cycle and extremal-period theorems refer to labeled states/words. Numerical
   quotient periods may be smaller and may vary between cycles.
4. The source's assertion that existing individual limiting frequencies must
   sum to one is not true in general. The article supplies a throwback example
   and an exact infinite-product criterion, rather than merely objecting to
   the interchange of an infinite sum and a limit.
5. Computational checks support the proofs over specified finite ranges; they
   are not a proof-assistant formalization or independent peer review.
