# Source and novelty audit

Access date: October 1, 2026 (America/Los_Angeles).

## OEIS entries consulted

- https://oeis.org/A097356 — definition, initial 54 terms, and the January 8, 2024
  formula comment proposing the lower constant 0.088154883798697116....
- https://oeis.org/A206226 — square subsequence, initial 24 terms, leading constants,
  and the equivalent dilogarithm root expression for the exponential base.
- https://oeis.org/A206227 — positive-shift companion and leading constant.
- https://oeis.org/A206240 — negative-shift companion and alternative interpretation.
- https://oeis.org/A258268 — exponential-base constant and root formula.

The ambiguity between a limiting envelope and an eventual pointwise bound is
preserved explicitly in the article. The report does not attribute an intention
of asserting the stronger false inequality to the OEIS contributor.

## Primary literature

E. Rodney Canfield, *From Recursions to Asymptotics: On Szekeres' Formula for the
Number of Partitions*, Electronic Journal of Combinatorics 4(2), R6 (1997).
DOI: https://doi.org/10.37236/1321
Journal page: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v4i2r6
PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v4i2r6/pdf/

The uniform theorem on PDF page 2 and the bibliography on PDF page 16 were
inspected, including rendered page images. The publisher's online publication
date is November 21, 1996; the issue is dated 1997. The article's bibliography
uses the issue year and notes the online date.

Szekeres' 1951 and 1953 papers are attributed through Canfield's bibliography
and discussion. Their complete original texts were not independently inspected.

Dan Romik, *Partitions of n into t sqrt(n) parts*, European Journal of
Combinatorics 26(1) (2005), 1–17.
DOI: https://doi.org/10.1016/j.ejc.2004.02.005
Institutional metadata/abstract:
https://weizmann.elsevierpure.com/en/publications/partitions-of-n-into-tn-parts/
No theorem relies on uninspected portions of Romik's article.

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned snapshot: 905bdc785424922c79fc24f56d27960ecb1085dd

Inspected via the GitHub connector: root structure/README, the Oeis directory
structure, `Analysis/Transseries/README.md`, and the volume-scope README at
`Analysis/Transseries/docs/series-and-transseries/README.md`. These document the
transseries and inversion program, and distinguish formal claims from research
material. This report does not depend on an unverified theorem in the repository.

Indexed GitHub code search for A097356 returned no matches. This is not an
exhaustive search of every PDF, binary artifact, unindexed file, or future commit.
A related Lambert-W code search served only to locate the current transseries
project and did not establish the absence of prior related results.

## Priority boundary

Searches by sequence identifier, the lower-envelope decimal, and restricted
partition asymptotics did not locate a source explicitly stating the particular
second-order three-term classification or the clipped inverse given here.
This is not proof that these results are unpublished. The leading asymptotic
is explicitly identified as a consequence of classical theory, and the report
does not claim a new general Szekeres theorem or certified bibliographic novelty.

## Computational data

All partition counts in the CSV outputs were independently computed by the exact
recurrence in the package. They were not copied from the OEIS b-files. The fixed
OEIS reference prefixes are included in `verification/verify.py` solely to
cross-check definitions and indexing. No complete external article is bundled.
