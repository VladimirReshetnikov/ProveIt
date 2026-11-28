# Pinned source and literature map

## Repository revision

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected revision: `cfab41369737c66ae520d179419509eb719367cd`.

Requested directory: `Analysis/GeneralizedRiemannHypothesis/`.

The analysis mapped the article's sections and inspected selected open questions and their mathematical dependencies, together with the exported RH/Dirichlet-GRH theorem interfaces. It was not a line-by-line proof audit of every article section or a rebuild of the full Lean development.

## Main source questions

1. **Sparse root counts beyond p terms.**
   `Article/sections/smd.tex`, labels `smd:thm:rankrule` and `smd:q:roots`.
   The source gives a finite rank rule through p exponents, separate open-disk results for p+1 and p+2 terms, and asks which further residue information governs larger term counts and deeper closed disks.

   https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/sections/smd.tex

2. **The Hessian at a general positive mirror spectrum.**
   `Article/sections/fil.tex`, labels `fil:thm:reflect`, `fil:thm:perturb`, `fil:lem:strip`, `fil:thm:hessian`, and the second question in `fil:sec:open`.
   The companion answers the distinct real-frequency, strictly positive-weight case. Independent variation of real parts, repeated-frequency strata, zero base weights, effective neighborhood radii, and all mixed-minor questions are not asserted solved.

   https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex

## RH/GRH scope

The inspected Lean wrapper and vendored interfaces concern RH and Dirichlet L-functions. This archive does not infer Artin or automorphic GRH, zero simplicity, or zero-spacing properties from those interfaces. No new formal verification of the claimed RH/GRH proof was performed. The two mathematical results delivered here use unconditional p-adic and Fourier arguments and therefore do not depend on the status of that proof.

## Primary literature checked

- H. W. Lenstra Jr., *On the factorization of lacunary polynomials*, Number Theory in Progress 1 (1999), 277–292. Theorem 3 and Sections 2–3 already supply geometric near-one bounds and use interpolation/Newton polygons; the deep exponential range is explicitly discussed. Its fixed-local-field optimal-root-count question is different from geometric root transport.
  https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1999b/art.pdf
  https://doi.org/10.1515/9783110285581.277
- M. Avendaño and T. Krick, *Sharp bounds for the number of roots of univariate fewnomials*, Journal of Number Theory 131 (2011), 1209–1228. Fixed-local-field bounds and generalized Vandermonde methods.
  https://mate.dm.uba.ar/~krick/AvKr11.pdf
  https://doi.org/10.1016/j.jnt.2011.01.006
- J. M. Rojas and Y. Zhu, *Root repulsion and faster solving for very sparse polynomials over p-adic fields*, arXiv:2107.09173. Sparse local-field algorithms and separation bounds.
  https://arxiv.org/abs/2107.09173
- E. A. Crain, W. E. Singhose, and W. P. Seering, *Derivation and properties of convolved and simultaneous two-mode input shapers*, IFAC Proceedings Volumes 29(1) (1996), 7278–7283. Established positive-input-shaping context; inspected through the publisher record and the authors' bibliography.
  https://doi.org/10.1016/S1474-6670(17)58856-4
  https://web.mit.edu/shaping/www/onlinepapers.html

These checks do not establish worldwide publication priority. The precise novelty claim is an extension beyond the statements in the pinned repository: the support-space transport preserving full deep-root data, its explicit finite residue precision, the exact eight-term classification, and the general positive-mirror Hessian.
