# Sources and literature-status notes

All sources were accessed on 20 September 2026. The article gives inline
numbered citations and a bibliography. These notes record exact locations.

## The selected question

Matthew Roughan, *Surreal Birthdays and Their Arithmetic*,
arXiv:1810.10373v2, version dated 25 October 2018.

- Abstract/version record: https://arxiv.org/abs/1810.10373
- HTML: https://arxiv.org/html/1810.10373v2
- PDF: https://arxiv.org/pdf/1810.10373
- The question is in the caption to Figure 3, printed page 7 (PDF page index 6).
- Form identity versus value equivalence is explained in Section 2, especially
  printed pages 2–3 and Figure 1.
- The Dali canonical form is Equation (1), printed page 3.

The figure caption was inspected in the rendered PDF as well as in parsed text.
The interpretation used in this report preserves structurally distinct,
equal-valued vertices. The paper's abstract/version record lists v1 and v2;
the selected question was read in v2. No statement is made about unindexed
private answers or correspondence.

## The 2023 journal version: metadata only

Matthew Roughan, *Surreal Birthdays and Their Arithmetic*, Mathematics Magazine
96 (2023), 329–343. DOI: 10.1080/0025570X.2023.2205819.

- https://doi.org/10.1080/0025570X.2023.2205819

The publisher's full-text and PDF endpoints were not retrievable in this
research session. No assertion is made that the 2018 wording persists unchanged
in that version, or that the journal version contains no answer. The quoted
question is therefore attributed to the accessible 2018 preprint only.

## Sign expansions and simplicity

Alessandro Berarducci, *Surreal numbers, exponentiation and derivations*,
arXiv:2008.06878 (2020).

- https://arxiv.org/abs/2008.06878
- https://arxiv.org/pdf/2008.06878
- Sections 2–3, printed pages 2–4: sign expansions, prefix simplicity,
  lexicographic order, convexity, and cut values.

The article's prefix-occurrence proof is given in full. It uses standard
simplicity facts from this background rather than claiming a new foundational
construction of surreal numbers.

Dierk Schleicher and Michael Stoll, *An Introduction to Conway's Games and
Numbers*, arXiv:math/0410026v2, 30 September 2005.

- https://arxiv.org/abs/math/0410026v2
- Section 5.1: the simplicity theorem and associated discussion.

This is cited beside Berarducci as a self-contained treatment of the simplicity
theorem itself, which the second classification proof and the two omega
propositions use through the recursive comparison relation.

## The Dali convention

Claus Tøndering, *Surreal Numbers—An Introduction*, version 1.7,
31 January 2019.

- https://www.tondering.dk/download/sur16.pdf
- Equation (2.71), printed page 25, defines the Dali map on the finite dyadics.

Although the URL ends in `sur16.pdf`, the served document's title page identifies
it as version 1.7, dated 31 January 2019. Bibliographic metadata in this archive
uses the document's actual title-page information, not an inferred date/version
from its filename. This is the same finite canonical convention used by Roughan.

The merged-in package `sparse-option-graphs` cited the same URL as "version 1.6,
2013". That attribution was not carried over: the audited title-page reading
(version 1.7, 31 January 2019) is used throughout. Equation (2.71) is the Dali
mapping in both readings, so no mathematical content depends on the choice.

## Later related work

Matthew Roughan, *Evolutionary Generation of Random Surreal Numbers for
Benchmarking*, arXiv:2504.07152v1, 9 April 2025; GECCO '25 Companion.

- https://arxiv.org/abs/2504.07152
- https://arxiv.org/html/2504.07152v1
- Sections 1–2 explain the form/graph viewpoint and the benchmark motivation.

This source is cited for context. The research archive does not reproduce its
code, claim measured speedups over it, or rely on a theorem in it to establish
the new graph bounds.

## Provenance of this archive

This archive is the merge of two independently prepared packages on the same
question, `canonical-forms-need-not-be-subgraphs` (the merge base) and
`sparse-option-graphs` (the donor). Both proved the shared negative answer with
a five-vertex pentagon of value 1/2, by the same argument shape but with two
genuinely different witnesses; both witnesses are printed in the merged article
and both appear in `results/all_small_counterexamples.json`, as entries 0 and 3.
Where the two packages recorded different statements about a source's status,
the more cautious statement was kept.

## Search scope and limitation

Targeted searches included combinations of “surreal”, “canonical”, “subgraph”,
“counterexample”, “girth”, and “cycle rank”, as well as the exact source title
and author. They surfaced the original question and related work, but no
subsequent answer was found. This is evidence about what was located, not a
proof that every result in the article is previously unpublished.

The final section's further questions are explicitly questions arising from
this investigation. They are not advertised as problems with a separately
verified comprehensive literature status.
