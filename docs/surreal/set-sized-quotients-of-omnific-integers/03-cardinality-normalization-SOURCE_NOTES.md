# Source and verification notes

## Repository inspected

VladimirReshetnikov/Surreal, snapshot:
`cd80e5e0adc2a1a25e8cc64d52abc8acb093d801`.

https://github.com/VladimirReshetnikov/Surreal/tree/cd80e5e0adc2a1a25e8cc64d52abc8acb093d801

The repository README and documentation inventory were inspected through the
GitHub connector. This was not a line-by-line audit of all repository reports.
No repository files were modified, and no new Lean build was performed.

## Companion manuscript

The available Library draft `omnific_integers(1).tex`, titled
*Omnific Integers and Diophantine Rigidity* (22 September 2026), was read in the
relevant sections through the Files connector. Its full-class set-target
rigidity, geometric divisor identity, common monomial divisor theorem, and
set-support clearing theorem are explicitly credited as prior work. Its
"exact size boundary" question motivates the cardinal realization theorem.
The companion file is not redistributed in this archive.

## Published background and primary online sources

- Conway, *On Numbers and Games*; Gonshor, *An Introduction to the Theory of
  Surreal Numbers*: classical normal-form and field background.
- L'Innocente and Mantova, *A factorisation theory for generalised power series
  and omnific integers*, arXiv:1710.07304v5 (22 January 2024).
  https://arxiv.org/abs/1710.07304v5
  The PDF was inspected, including its restricted Hahn-field facts. The
  support-restricted Hahn construction is classical, not claimed as new here.
- Barucci, Gabelli, and Roitman, *Complete integral closure and strongly
  divisorial prime ideals*, arXiv:math/0302223.
  https://arxiv.org/abs/math/0302223
  Terminological context; its theorems are not used as proofs of our results.
- Stacks Project, Tag 00H9: directed colimits of flat modules.
  https://stacks.math.columbia.edu/tag/00H9
- Stacks Project, Tag 00I8: valuation rings and the ordinary valuative
  characterization of normal domains.
  https://stacks.math.columbia.edu/tag/00I8
- Kuhlmann, *Dense subfields of henselian fields, and integer parts*,
  arXiv:1003.5681.
  https://arxiv.org/abs/1003.5681
  Related density context, not the claimed source of the normalization proof.

## Novelty boundary

The central contribution relative to the inspected material is the explicit
family of surreal subfields with attained ring/module detection threshold
kappa^(aleph_0), exact ideal-generation threshold cf(kappa), and its connection
to the normalization and uniform-denominator results. Some supporting facts
are elementary applications of standard algebra and are labeled accordingly.
The search was focused and does not prove absence from all published literature.
No resolution of Conway's general refinement problem is asserted.

## What was checked

The LaTeX source was compiled to PDF, references resolved, and rendered pages
were visually inspected. The included Python program was executed with exact
rational arithmetic; its output is included separately. It is not a theorem
prover and does not establish the transfinite/cardinal arguments. All such
arguments are given as mathematical proofs in the article and remain subject
to independent review.
