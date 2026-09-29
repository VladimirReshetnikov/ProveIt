# Sources and provenance

Inspection date: 28 September 2026.

## Repository question

Repository: https://github.com/VladimirReshetnikov/ProveIt

Frozen commit: `e2b1f016a94102663f12b970e6dd434229f90d01`

Relevant report:

`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/insertion-degree-spectra/article.tex`

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/e2b1f016a94102663f12b970e6dd434229f90d01/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/insertion-degree-spectra/article.tex

Title: *Gaps in Bounded-Shuffle Hierarchies: Counterexamples, arbitrary finite
spectra, and a no-gap theorem for iteration depth*. Research note prepared for
Vladimir Reshetnikov, 20 September 2026.

The article's definitions, finite-profile construction, binary example,
algorithm/validation discussion, and closing limitations were inspected. Its
README and the repository report manifest were also consulted. In the closing
discussion, the report explicitly does not settle which finite spectra can all
be realized over one fixed binary alphabet. It also proposes studying the least
alphabet for {1,r} and smaller source languages.

The existing arbitrary-alphabet theorem and binary {1,2,4} example are background,
not claims of the present package. The new proofs do not assume any unverified
statement elsewhere in the repository.

## Primary preprint

Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion, Shuffle,
and Crossover Language Operations*, arXiv:2608.27755v1, submitted 27 August 2026.

https://arxiv.org/abs/2608.27755
https://arxiv.org/pdf/2608.27755

The inspected submission history listed v1. The 13-page PDF was read at the
relevant definitions and Section 11; page 9 was also inspected as a rendered
page. In particular:

- Section 2 defines the oriented k-insertion with empty pieces allowed.
- Section 11 defines minimum insertion degree and its spectrum.
- **Theorem 9 already proves the unary-source singleton interval theorem.**
- Conjecture 2 is the unrestricted both-singleton no-gap conjecture.
- Problem 1 asks whether competing finite source pairs can erase a degree.

Only these definitions and local spectrum questions are used. None of the
preprint's undecidability arguments is an input to the new proofs.

## Search and novelty boundary

Repository search for `insertion-degree` returned the existing report, its
README/SOURCES, and the report manifest. Targeted web queries included the
preprint title and identifier, `insertion-degree spectrum`, and combinations of
`binary`, `unary`, and `single unary word`. Some narrow queries returned no
useful additional mathematical matches. No equivalent to the fixed-binary
single-unary-source profile theorem or the sharp full-coverage length theorem
was identified in the sources inspected.

This is not an exhaustive priority check, and irrelevant broad search results
were not used as evidence. The new statements should be treated as proposed
research contributions with explicit proofs, pending independent mathematical
review and a wider literature check. Source articles and font files are not
redistributed in this archive.
