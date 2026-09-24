# Literature search and source audit

> This file is the literature-search record of the **dfao-reversal-coloring-bound**
> source report, kept verbatim as provenance after the merge. It lists only that
> report's sources; the merged package's full source list and attribution
> boundaries, including Holzer and Koenig, are in source_audit.md.

Search date: **20 September 2026**.

## Primary source establishing the target

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite Automata
with Output*, arXiv:1705.07150v2, revised 17 October 2017.

- Abstract and version record: https://arxiv.org/abs/1705.07150
- PDF: https://arxiv.org/pdf/1705.07150
- HTML: https://arxiv.org/html/1705.07150v2

The PDF and HTML were inspected. The table and open-question text on printed
page 17 were also inspected as a rendered page image, not inferred solely from
search snippets. The selected question is Section 5, item 1. The orbit reduction
is Proposition 4; attainment with three letters is Corollary 2. Table 3 contains
the known small maxima used as regression checks in this package.

The conference version is associated with CIAA 2018 and DOI
10.1007/978-3-319-94812-6_12. The article cites the arXiv version actually consulted,
so its numbering and page references are unambiguous.

## Additional primary source

Marc Deléglise and Jean-Louis Nicolas, *The Landau Function and the Riemann
Hypothesis*, arXiv:1907.07664 (2019).

https://arxiv.org/abs/1907.07664

Used only to anchor the standard name and definition of `g(k)`. No analytic
number theory from this work is used in the candidate proof.

## Representative search queries

- "State Complexity of Reversals of Deterministic Finite Automata with Output"
- "1705.07150"
- "Davies" "reversal" "DFAO" "conjecture"
- "binary" "automata with output" "k^n"
- "DFAO reversal" conjecture
- "binary DFAO" reversal
- "1705.07150" "cited"

The targeted searches located the explicit published conjecture and related
records, but did not locate a later resolution of its nonattainment question.
Many returned items were unrelated or only repeated the original abstract.
No conclusion about priority should be drawn from a missing search hit.
This was not a systematic citation-index review, a survey of all theses, or
correspondence with the author.

## Attribution boundaries

The target question, reverse construction and exact orbit interpretation,
three-letter full-transformation witness, and reported small maxima are
existing material and are identified as such in the article. The candidate
contribution is the coloring/stabilizer obstruction and consequences derived
from it in this draft. A fuller novelty review could still locate equivalent
arguments or strengthen this attribution.

No third-party paper PDFs or images are redistributed in this package.
