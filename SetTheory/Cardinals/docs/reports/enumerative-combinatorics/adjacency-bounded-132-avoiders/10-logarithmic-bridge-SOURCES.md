# Sources and attribution

## Pinned current repository

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 7421a4ca60fdf125411edf412f825aac54278b37
Combined article Git blob: b9697af6c8489fb1e0b3670037a50aa70fdc6f80
Inspected: 1 October 2026
Path: SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/article.tex
Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/7421a4ca60fdf125411edf412f825aac54278b37/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/article.tex

The current combined article includes Parts VI and VII. The target here is
Part II's section “Joint growth of length and adjacency bound.” It warns
that the fixed-cap Perron constants are not uniform and asks for joint
asymptotics when m grows with n.

Inherited source inputs, used with explicit credit:
- prop:endpoint: exact first/last deficiency recurrence
- crem:prop:block-lower: injective block lower bound
- crem:lem:uniform-tail: uniform Catalan coefficient defect
- crem:thm:corridor-quantitative: scalar-root and growth-rate corridor
- crem:thm:main-allorders: scalar-root inverse-logarithmic expansion

The squared-renewal coefficient majorant and the triangular-array clustered
renewal analysis supply the new logarithmic bridge. The report does not
replace the inherited estimates with a claim of independent discovery.

## Exact implementation provenance

checks/model.py is byte-identical to the exact endpoint model used in the
source's polynomial-rarity work. Its original Git blob is
 a4fdee376119a24c057623829b76cee71628b369.
Its SHA-256 is
 c693d80529b69762600edc4b4d271155e6aa12c9127bda9a59a839ee143538f7.
It inherits the Mayama–Akita endpoint recurrence and the repository's
05-model implementation (Git blob f0248e0d6181200257e2949c1a8fa8f9fecf5617).
The present envelope checks and cluster diagnostics are separate additions.

## Public primary references

N. Nadler, On 132-avoiding permutations with an adjacency constraint,
arXiv:2604.22135v1 (2026): https://arxiv.org/abs/2604.22135

T. Mayama and D. Akita, Finite-state enumeration of adjacency-constrained
132-avoiding permutations, arXiv:2605.23519v1 (2026):
https://arxiv.org/abs/2605.23519

These primary records were checked during this investigation. They provide
the enumeration setting. No external paper is redistributed. Targeted
source and literature inspection establishes the specific repository
question, not a worldwide priority claim. Fourier inversion, Abel summation,
Parseval, and exponential tilting are classical; all uniform estimates
needed for this triangular array are proved in the manuscript.
