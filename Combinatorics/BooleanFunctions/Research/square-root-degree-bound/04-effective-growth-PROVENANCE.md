# Source provenance

Inspection date: 8 October 2026.

## Repository snapshot

Repository: https://github.com/openai/math

Inspected main commit:
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`

Commit timestamp returned by GitHub: `2026-10-08T05:20:00Z`.

Relevant preprint: OpenAI, *Unbounded Violations of the Square-Root Degree
Bound*, 26 September 2026.

Base directory:
`preprints/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026/`

The following source files informed the comparison and derivation:

| Relative path | Git blob identifier | Role |
| --- | --- | --- |
| `README.md` | `319d69fe65650b3d4d4488bfc770bce5e3fb4e71` | Author/date and citation metadata |
| `build/sections/00-introduction.tex` | `feeeb98c5b4259df67dc48a3d69837452f0ca5ee` | Main unbounded-ratio statement; explicit absence of useful dimension/copy-count growth bounds |
| `build/sections/02-reporting.tex` | `508f215e2072d69dc91c864171cba4362016cd2c` | Reporting cancellation, variance deficit, Gaussian construction, nonquantitative transfer |
| `build/sections/04-mean-cost.tex` | `f70bbc4e83670d2f4ce3fb8b71cff3fec4453db0` | Comparison with the source's alternative mean-cost amplification method |

The article does not claim an audit of every section or other manuscript in
the repository. The Gaussian and uniform amplification proofs are supplied
in the new article rather than delegated to the upstream final theorem.

Frozen source-directory link:
https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026

## Primary mathematical references

Ryan O'Donnell, *Open Problems in Analysis of Boolean Functions* (2012),
arXiv:1204.6447. The linear-coefficients versus degree problem is on printed
page 9. That PDF page was visually inspected. This is a historical source,
not a claim that the 2012 list records the current status of all its problems.

https://arxiv.org/abs/1204.6447
https://www.cs.cmu.edu/~odonnell/papers/aobf-open-problems.pdf

Nathan Ross, *Fundamentals of Stein's method* (2011), arXiv:1109.1880.
Lemma 2.5 gives the Stein-equation derivative estimate used in the article.
Printed page 9 of the arXiv version was visually inspected. The article
supplies the leave-one-out derivation of its particular averaging constant.

https://arxiv.org/abs/1109.1880
https://arxiv.org/pdf/1109.1880

## Attribution and priority boundary

The reporting idea and observation framework are attributed to the OpenAI
preprint. The concrete uniform implementation, rational-threshold constants,
and 20-bit exact certificate are the work developed in this package.
No exhaustive priority search is claimed. No upstream source files are
redistributed; only bibliographic records and source identifiers are included.
