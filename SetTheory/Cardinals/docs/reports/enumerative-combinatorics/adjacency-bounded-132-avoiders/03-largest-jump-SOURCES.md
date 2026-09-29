# Source and provenance ledger

Inspected on September 29, 2026. The research problem was chosen by comparing
repository report claims and explicit exclusions, rather than assuming that
all of the repository's AI-assisted mathematical claims are established.

## Repository context (GitHub connector)

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected head: 8d936ee2357f9decf78c2ecc7d9baf3100a6787d
Head commit metadata timestamp: 2026-09-29T15:42:32Z.

Relevant directory:
SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/

README blob: 7f56b878e420c9fb0a0df299f54f9c154c68780e
article.tex blob: f24ea59acf0f9809462f7fb0f055e78d38d4740a

The README was inspected in full and relevant portions of article.tex
were read. The report contains a September 19 part and a September 28
continuation. Its explicit exclusions include a joint limit in n and m.
This manuscript addresses that regime near m=n. It does not rely on the
existing report's growth-constant theorems.

## Primary literature

Nathaniel Nadler, "On 132-Avoiding Permutations with an Adjacency Constraint,"
arXiv:2604.22135v1, submitted April 24, 2026.
https://arxiv.org/abs/2604.22135
https://arxiv.org/html/2604.22135v1
Used for the original adjacency-bound problem and fixed-m context.
The arXiv record and available HTML were inspected.

Teruki Mayama and Dai Akita, "Finite-state enumeration of adjacency-constrained
132-avoiding permutations," arXiv:2605.23519v1, submitted May 22, 2026.
https://arxiv.org/abs/2605.23519
https://arxiv.org/html/2605.23519v1
Used for the established endpoint-state enumeration, fixed-m rationality,
and spectral context. The arXiv record and available HTML were inspected.

Svante Janson, "Simply generated trees, conditioned Galton--Watson trees,
random allocations and condensation," arXiv:1112.0510, 2011.
https://arxiv.org/abs/1112.0510
The arXiv record was inspected for general random-tree-limit context.
No theorem from this source is imported into the proof.

Svante Janson, "Patterns in random permutations avoiding the pattern 132,"
arXiv:1401.5679, 2014.
https://arxiv.org/abs/1401.5679
The arXiv record was inspected for related random-132-avoider statistics.
It concerns occurrences of patterns, not the largest adjacent difference.

Philippe Flajolet and Andrew Odlyzko, "Singularity analysis of generating
functions," SIAM Journal on Discrete Mathematics 3(2) (1990), 216--240.
DOI: 10.1137/0403019.
Classical background for the transfer principle. Attempts to retrieve
an author-hosted PDF or publisher copy in this session were unsuccessful;
no claim is made to have inspected that PDF. The manuscript states the
specific transfer form and checks its analytic hypotheses explicitly.

## Novelty boundary

Targeted searches for largest jumps and maximum adjacent differences in
132-avoiders did not provide an exhaustive literature assessment. Some
searches returned mostly unrelated results. This does NOT establish
publication priority. The result is presented as a proposed research
contribution extending a specifically identified repository gap, not as
an externally certified first solution of a named classical conjecture.

## Distribution

No source paper, external PDF, repository article, or font file is
redistributed. All article content and verification code in this package
were prepared for this response; the bibliography credits external context.
