# Source and novelty audit

## Pinned continuation point

Repository: `https://github.com/VladimirReshetnikov/ProveIt`

Commit: `176e31c5c7ee369edf51edd815463dc029e3faed`

Report: `SetTheory/Cardinals/docs/reports/automata-and-formal-languages/insertion-degree-spectra/article.tex`

LaTeX blob: `7f5a958e7ac6d6df902d4efa40cfefa813bb20db`

Relevant inspected source ranges include lines 990–1230 (gap formula, safe targets, strict escape), 1400–1545 (volume bound, known m² construction, degree-three example), and 1790–1950 (Questions 21.1–21.10). The report README and repository research catalogue were also inspected. The proof comparisons do not rely on unseen repository content.

## Attribution

The gap formula, maximal insertion degree being at most the inserted length, the old strict escape sufficiency argument, the full-coverage volume lower bound, and the m² optimum for m >= 6 are not claimed as new discoveries. The paper credits the earlier report and reproves the needed finite arguments.

The earlier report expressly leaves exact lengths for m=3,4,5 open (Question 21.3). Its Question 21.4 asks which vectors attain the sharp bound and which targets are mandatory. These are the concrete continuation targets.

New relative to that report: the complete center criterion including its boundary branch; the all-parameter threshold; the small-case optimality proofs; the exact center classification and finite count formula; the explicit mandatory-target test; and the complete shortest degree-three language classification with minimum cardinality 37.

## External primary source

Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1, 27 August 2026.

`https://arxiv.org/abs/2608.27755v1`

Used for the insertion orientation, the relationship with singleton degree questions, and attribution of the unrestricted both-singleton conjecture. It is not used as an authority for the new theorems. The preprint and the relevant rendered page were inspected during research.

## Search boundary

Searches on 30 September 2026 covered the paper title, the earlier binary-insertion title, insertion-degree terminology, and isolated witnesses. Most exact phrase queries returned no relevant independent result beyond the cited preprint. This is a bounded source check, not an exhaustive bibliographic or historical-priority certification. No broad claim that a major classical problem has been solved is made.

## Formal status

The continuation report is an AI-assisted unrefereed draft. The current package has written proofs and exact Python checks only. No Lean or Rocq build was performed, and no inherited formal verification is claimed.

## Integration

An addition to the existing insertion-degree report is the natural destination. The repository was read only; this package does not create a commit, pull request, issue, or persistent Library upload.
