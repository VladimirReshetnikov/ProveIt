# Sources and provenance

Review date: September 28, 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit inspected:
`74f7f5bdba1aa728b340509701a0fa4e45e8dbf3`

The continuation source directory is:

```
SetTheory/Cardinals/docs/reports/enumerative-combinatorics/
polyomino-growth-finite-prefix-corrections/
```

The GitHub connector was used to inspect the source. Relevant files:

### article.tex

Git blob identifier returned by the connector:
`4a021fb34b96a08710b9de59a65f7199e10fb57b`

https://github.com/VladimirReshetnikov/ProveIt/blob/74f7f5bdba1aa728b340509701a0fa4e45e8dbf3/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/polyomino-growth-finite-prefix-corrections/article.tex

Sections reviewed include the finite-prefix report's spectral criterion and
counterexample (Section 8), the enumeration and certificate discussion,
formalization boundaries, and the proposed projects in Section 10. The source
explicitly leaves the equality case spr(J)=1 unclassified. The critical
classification and sharp rate are the principal continuation targets here.
No claim is made to a full audit of every theorem of the source report.

### code/model.py

Git blob identifier:
`97b241bd20073d03155fbada577d8f83df3bd092`

https://github.com/VladimirReshetnikov/ProveIt/blob/74f7f5bdba1aa728b340509701a0fa4e45e8dbf3/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/polyomino-growth-finite-prefix-corrections/code/model.py

Its variable order and TERMS list are transcribed in `code/bui_model.py`.
The article appendix also displays every monomial. The source's e-pattern
requires its anchor to be occupied and these positions to be absent:
(-1,0), (1,0), (-1,-1), (0,-1), (1,-1). This is the pattern used in the
vertical-column nonzero-forcing argument.

The Jacobian and independent directional-derivative implementations in the
present package were written for this report; the map itself is inherited.

### data/profiles_18.csv

Git blob identifier:
`82648328be3173ba14e55ddeaa4008dc8e23c1a3`

https://github.com/VladimirReshetnikov/ProveIt/blob/74f7f5bdba1aa728b340509701a0fa4e45e8dbf3/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/polyomino-growth-finite-prefix-corrections/data/profiles_18.csv

The complete returned table was copied to `data/profiles_18.csv`. It supplies
17 marked coefficient sequences, sizes 1 through 18, plus unmarked totals.
The checker uses the marked columns. No new size-18 enumeration was run.
Git blob identifiers here record source identity; they are not an independently
computed integrity or verification certificate for the mathematical input.

### README.md and formal-project context

The report README distinguishes its computer-assisted upper bound 4.498 from
the cited Lean endpoint 4.5235, and records the source's trust boundaries.
The present article reports that distinction rather than assuming every
repository report is machine-checked. No new Lean build was run.

## Primary external sources

### Vuong Bui

*A convolutional approach to bounding the number of polyominoes*,
arXiv:2511.00461v2, revised May 6, 2026.

https://arxiv.org/abs/2511.00461v2
https://arxiv.org/html/2511.00461v2

The current version's abstract and relevant HTML passages on recurrence
certificates and research questions were inspected. Version 1 had a different
title; its date and title should not be used as though they identified version 2.
The present article does not claim to resolve the neighborhood-refinement
question. The repository report supplies the exact local continuation context.

### Tobias Winkler and Joost-Pieter Katoen

*Certificates for Probabilistic Pushdown Automata via Optimistic Value
Iteration*, arXiv:2301.08657v2, February 26, 2023.

https://arxiv.org/html/2301.08657v2

Sections 2 and 3 were inspected, including the least-fixed-point spectral
criterion, characterization of strict inductive upper bounds, Perron-directed
search, and exact versus floating-point verification. These are prior methods,
not inventions of the present report.

### Alistair Stewart, Kousha Etessami, and Mihalis Yannakakis

*Upper bounds for Newton's method on monotone polynomial systems, and P-time
model checking of probabilistic one-counter automata*, arXiv:1302.3741.

https://arxiv.org/abs/1302.3741

The author preprint record and abstract were inspected for background
attribution. This was not a complete proof-level audit of the paper. The
present sharp truncation theorem is proved independently rather than assumed
from this source.

### Michael Drmota

*Systems of functional equations*, Random Structures & Algorithms 10 (1997),
103-124.

https://doi.org/10.1002/(SICI)1098-2418(199701/03)10:1/2<103::AID-RSA5>3.0.CO;2-Z

The publisher/search bibliographic record was checked. A mirror PDF fetch did
not provide a usable full-text review; no full reading of that PDF is claimed.
The citation credits classical positive-system singularity theory. The local
fold analysis needed by this article is supplied in full and is not an opaque
appeal to Drmota's theorem.

## Search and novelty limitations

Targeted searches covered positive polynomial system certificates, perturbation
and square-root behavior, finite-prefix convolution majorants, and the existing
polyomino continuation. Several search results were noisy or irrelevant and
were not used. The exact theorem package was not found in the specific source
material inspected, but this is not proof of global priority or absence from
the literature. The report should be treated as an unrefereed research draft
pending independent review.
