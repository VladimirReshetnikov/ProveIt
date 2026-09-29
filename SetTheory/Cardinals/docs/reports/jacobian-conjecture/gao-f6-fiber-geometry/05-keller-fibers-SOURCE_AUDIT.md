# Source and attribution audit

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt  
Commit: `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`

The investigation surveyed the repository overview and then focused on its Jacobian branch. The principal repository sources were:

- `Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean`
- `Algebra/JacobianConjecture/Research/README.md`
- `ProveIt_Walkthrough.tex`, specifically its reference to Gao's account as external context for the repository's formal determinant and collision identities.

The Fabius overview was also inspected during topic selection, but it is not a mathematical dependency of this article. This was a targeted research survey, not a full audit of every repository file or a build of the repository's Lean development. No repository files were modified or uploaded.

## External construction and deferred question

Shuhong Gao, *Counterexamples to the Jacobian conjecture in dimensions greater than two*, arXiv:2608.00222v1, July 31, 2026.

- https://arxiv.org/abs/2608.00222v1
- https://arxiv.org/html/2608.00222v1
- https://arxiv.org/pdf/2608.00222v1

Section 4.5.1 specifies F6, its stage, its sweep, its determinant, and the sextic inverse polynomial. Appendix A.3 defers complete fiber stratifications for the higher-dimensional examples. The rendered formulas on PDF pages 22 and 23, and the deferred statement on page 31, were inspected directly.

The present paper addresses the F6 fiber-size question, including the exceptional target hyperplane. It does not claim to invent Gao's map, resolve the two-dimensional Jacobian problem, or resolve Gao's separate middle-branch rigidity problem.

## New derivations in this manuscript

The exact derivative-localization identity; exhaustive multiplicity classification; complete hyperplane fibers; unique square member; explicit omitted surface; obstruction to stabilization from dimension three; global nonproperness equation and C-adic coefficient; normalization and complete local analytic discriminant types; full S6 monodromy; the intermediate-field obstruction; and the explicit rational S6 target are developed and proved in the article.

The source comparison did not locate these results for this particular F6 in the inspected repository sources or Gao version 1. Targeted searches included combinations of Gao, F6, fiber, monodromy, omitted surface, codimension three, and the distinctive rational coefficients of the omitted parameter. No overlapping complete treatment was located. This limited search is not a comprehensive priority check and does not rule out independent or newly posted work.

## General Galois background

J. S. Milne, *Fields and Galois Theory*, version 5.10, September 2022:
https://www.jmilne.org/math/CourseNotes/FT.pdf

This source supports the standard background on Frobenius cycle types, Galois groups, and solvability by radicals. The particular polynomial factorizations and group deductions for F6 are provided in the manuscript and its exact certificate.
