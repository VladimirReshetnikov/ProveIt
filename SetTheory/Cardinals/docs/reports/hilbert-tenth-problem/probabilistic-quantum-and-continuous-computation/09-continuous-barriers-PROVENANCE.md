# Provenance and proof status

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspection date: 2026-09-30.

Head observed during inspection: `f608f1cb3c5be8a736df1328c01b293aabfccf4e`.

The following live source files were read using the GitHub connector:

- `Computability/HilbertTenthProblem/README.md`
- `Computability/HilbertTenthProblem/Lean/MRDP.md`
- `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`

The public declarations inspected were `Diophantine.mrdp`, `Diophantine.mrdp_iff`, and `Diophantine.mrdp_dioph_iff`. The mathematical dependency is the equivalence between computably enumerable subsets of the naturals and projections of natural zero sets of finite integer polynomials. No optimized operation count or numerical universal-polynomial witness bound is used.

The repository was not built locally and its entire collection of informal reports was not audited. This is not an exhaustive duplication or novelty check.

## Primary literature used

The bibliography in the TeX/PDF gives full citations. Sources inspected include:

- Christopher Moore, *Generalized shifts: unpredictability and undecidability in dynamical systems*, Nonlinearity 4 (1991), 199–230. Author-hosted PDF.
- Olivier Bournez, Daniel S. Graça, Emmanuel Hainry, *Computation with perturbed dynamical systems*, JCSS 79 (2013), 714–724. Author institutional copy; DOI 10.1016/j.jcss.2013.01.025.
- Tomoo Yokoyama, *Coarse chain recurrence, Morse graphs with finite errors, and persistence of circulations*, arXiv:2504.01325v4.
- Sicun Gao, Jeremy Avigad, Edmund M. Clarke, *δ-Decidability over the Reals*, arXiv:1204.6671 and LICS 2012.
- André Platzer, Long Qian, *Differential Equation Inductive Robustness Axiomatization*, arXiv:2606.18685, June 2026 preprint.
- Sergei Ovchinnikov, *Max-min representation of piecewise linear functions*, Beiträge zur Algebra und Geometrie 43(1) (2002), 297–302; preprint arXiv:math/0009026.

No third-party paper, font file, or repository source copy is redistributed in this package.

## Claim boundaries

The proposed contribution is the joint quantitative/certificate/three-outcome realization package. The manuscript does not claim to originate Turing-complete continuous dynamics, infinitesimal-robustness decidability, graph bottleneck duality, the max–min theorem, ReLU realization of piecewise-affine maps, or MRDP.

The core proofs are supplied in the article. Classical universality and MRDP are external mathematical inputs. The neural corollary additionally uses the established max–min representation theorem.

There is no independent peer review or formal proof-assistant verification of the new results. No expanded universal transition table, extracted network weights, or fixed MRDP polynomial is supplied. In particular, the finite-grid quartic family's varying dimension is not a numerical bound for the fixed MRDP polynomial.

## Executed checks

The companion test script was run successfully and reports 5,660 assertions, using exact rational arithmetic and deterministic sampling. The test categories and sample ranges are recorded in the article and `results/verification.json`.

The PDF was compiled with pdfLaTeX. All pages were rendered for visual layout review. Reported tests concern the actual bundled reference implementation, not a universal-machine benchmark or a Lean build.
