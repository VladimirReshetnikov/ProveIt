# Repository audit: the differential-equation gap

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `e260237db9b71da8b74a0c13c8e6355119091100`

Review date: September 21, 2026 (Pacific time).

## Finding

The catalogue describes fifteen research packages, including extensive surcomplex analysis, trigonometry, analytic geometry, foundations, and symbolic computation. A broad new survey of those subjects would duplicate substantial existing work.

The specific opportunity is to develop differential-equation existence, obstruction, and support-control theorems. The inspected computer-algebra passage correctly distinguishes coordinate derivatives, formal-parameter derivatives, and the Berarducci–Mantova scalar derivation, but its subsection “Differential equations must name their category” provides a short uniqueness warning rather than a developed solution theory. The trigonometry README explicitly states that no derivation on No is chosen and that the global phase-extension classification is not a classification of differential-equation solutions.

The article therefore connects existing finite-angle and strong-summability ideas to a scalar differential-field solvability criterion and a constructive common-domain Hahn-coherent ODE theory. It does not claim the repository lacks all mention of differential equations or transseries.

## Inspected sources

### Documentation catalogue

Path: `docs/README.md`

https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/README.md

Read the catalogue, report descriptions, dependency guidance, ring distinctions, workspaces discussion, and status warnings. Used to avoid duplicating the already extensive geometry, analytic, and CAS material.

### Analysis report description

Path: `docs/surcomplex/analysis/README.md`

https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/analysis/README.md

Read the distinctions among arbitrary analytic germs, common-domain coherent sections, and ordinary lifts; the strong-summability convention; the fine-topology warnings; and the explicit non-claims. The new coherent theorems name their ring and do not transport conclusions to a larger germ category.

### Computer-algebra article

Path: `docs/foundations-and-computation/computer-algebra/article.tex`

https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/foundations-and-computation/computer-algebra/article.tex

The full source was retrieved, but the audit relies on targeted inspection, including source-line ranges 3100–3680 and 3580–3820. The source discusses factorial asymptotic series, infinite phase conventions, three derivative semantics, and then the brief subsection “Differential equations must name their category” before moving to host integration. The article gives credit for these existing distinctions; its scalar and coordinate solution theorems go beyond that warning.

### Trigonometry report description

Path: `docs/surcomplex/trigonometry/README.md`

https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/trigonometry/README.md

Read the finite-angle polar theorem, the global phase classification description, the coherence obstructions, and the explicit non-claims. In particular, the README says that no derivation on No is chosen and that the extension classification does not classify differential-equation solutions. The new article reproves the finite-phase construction needed to establish compatibility with the chosen scalar derivation, without claiming that polar decomposition is new.

## Established mathematical inputs

The external literature investigation used primary research papers and an author-authorized textbook manuscript:

- Berarducci and Mantova, *Surreal numbers, derivations and transseries*, JEMS 20 (2018), 339–390. https://arxiv.org/abs/1503.00315 ; https://doi.org/10.4171/JEMS/769
- Aschenbrenner, van den Dries, and van der Hoeven, *The surreal numbers as a universal H-field*, JEMS 21 (2019), 1179–1199. https://arxiv.org/abs/1512.02267 ; https://doi.org/10.4171/JEMS/858
- Teschl, *Ordinary Differential Equations and Dynamical Systems*, Chapter 4. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf
- Higman, *Ordering by divisibility in abstract algebras*, Proc. London Math. Soc. (3) 2 (1952), 326–336. https://doi.org/10.1112/plms/s3-2.1.326
- Neumann, *On ordered division rings*, Trans. AMS 66 (1949), 202–252. https://doi.org/10.1090/S0002-9947-1949-0032593-5

The BM and ADH papers and the relevant textbook chapter were inspected. Higman's publication metadata was checked against the publisher. The original Neumann paper was not retrieved in full; the support argument used here is proved completely in Appendix A instead of depending on an uninspected passage.

## Limits of the audit

This was a targeted review, not a line-by-line verification of every merged article or every archived source manuscript. A GitHub text search returned no hits, but that result was not used as evidence of repository-wide absence. No statement in the new article depends on treating a failed search as proof of absence.

The gap claim is confined to the inspected passages and their explicit boundaries. The new article does not assess the correctness of all the repository's research claims, and it does not claim its results are absent from the broader mathematical literature. Established inputs, deductions proved in the article, finite symbolic checks, and unaddressed generalizations are separated.
