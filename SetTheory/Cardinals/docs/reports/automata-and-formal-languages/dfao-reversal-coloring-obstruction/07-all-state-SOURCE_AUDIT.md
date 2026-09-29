# Source and novelty audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Observed commit: 8315d24e33a0f4901ca85f0e330ed1d5e19b1ae2
Inspection date: 29 September 2026.

Selected directory:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/`

Inspected sources, read through the GitHub connector:

1. `article.tex`, especially the orbit reduction, rightmost-singular argument,
   two graph forms, structural collection, and three-output extension.
   Git blob: 84923bc50f6233d63fd1a7341a0e16801cd715b8.
   The blob identity was also checked explicitly at the pinned commit.
2. `README.md`, including the exact three-output theorem, finite-range result,
   and explicit limits of the main article.
3. `03-eventual-SOURCE_AUDIT.md`, which records an eventual fixed-k analysis,
   balancing, rigidity, asymptotics, and recurrence results, but no established
   explicit fixed-k threshold.
   Git blob: f93f98bb9d992ffc7cbc5396c9e06cbba287dde7.
4. Repository root README and the research-report manifest, used to choose the
   topic and identify nearby work; unrelated claims in those documents are
   not dependencies of this manuscript.

Pinned main source:
https://github.com/VladimirReshetnikov/ProveIt/blob/8315d24e33a0f4901ca85f0e330ed1d5e19b1ae2/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/article.tex

The repository already contains finite comparisons at n=7..30 for a range of
output sizes including four. Neither these numerical values nor the graph
framework is claimed as new. The eventual audit was inspected, not every
proof of its companion manuscript. This paper does not rely on its eventual
theorem: all upper-bound arguments needed here are rederived.

## Primary literature

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
Automata with Output*, arXiv:1705.07150v2, 17 October 2017.

https://arxiv.org/abs/1705.07150
https://arxiv.org/html/1705.07150v2
https://arxiv.org/pdf/1705.07150v2

The primary text was inspected in HTML and PDF. Relevant PDF pages,
including the small-value table and the concluding problems, were visually
inspected using the web PDF screenshot tool.

Relevant items:
- Propositions 3–4: accessible reversal states are pairwise distinguishable;
  the reversal size is the coloring-orbit size.
- Section 3: definition of U_(a,b), the cited two-generation theorem, and
  explicit generators attributed to Krawetz.
- Theorem 3 / Corollary 3: the published lower construction and its count.
- Section 5, Problem 2 (printed page 17): optimality of the lower construction
  for n>=7. Only the four-output slice is claimed here.
- Table 3: prior small values and the distinction between established and
  candidate optima in that source. Small numerical values are not new here.

Markus Holzer and Barbara König, *On deterministic finite automata and
syntactic monoid size*, Theoretical Computer Science 327(3) (2004), 319–347.
DOI: 10.1016/j.tcs.2004.04.010.

Theorem 8 is imported through Davies's explicit statement. The original
2004 proof was not reconstructed or independently audited in full. Davies's
attribution of the explicit generators to Krawetz is retained; the underlying
thesis was not independently read in full.

## Contribution claimed by this package

- Exact four-output optimum for every n>=4, with the formula for n>=7.
- An explicit, elementary structural exclusion for n>=26, plus a bounded
  complete certificate for n=4..25.
- A strict structural margin greater than AB, an AB/2 stability radius,
  and the specialized 24AB second-cross-collision penalty.
- Exact missing-orbit inventory and extremal output-map count for the
  standard transition pair.
- Specialized exact sequence consequences, including the minimal order-15
  recurrence. General ideas of asymptotics, recurrence extraction, and
  primitive-word enumeration are not claimed as new methods.

## Search limits

The literature search was targeted to DFAO reversal, Davies's paper, the
binary exact maximum, and later resolutions. The repository was searched
for four-output follow-up work and the adjacent eventual audit was read.
This was not a systematic citation-index review, a survey of all theses, or
correspondence with the authors. A missing search hit does not establish
priority or prove the absence of a later published result. The manuscript
therefore makes no verified global-priority claim.
