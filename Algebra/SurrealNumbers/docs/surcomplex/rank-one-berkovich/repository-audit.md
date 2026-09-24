# Repository audit and topic selection

## Snapshot and method

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `e260237db9b71da8b74a0c13c8e6355119091100`

Inspection date: September 21, 2026.

The repository tree, documentation catalogue, selected report READMEs, and relevant introductory/source material were read through the connected GitHub interface. The review was targeted, not a full proof audit or a claim that every line in every file was read. An incomplete GitHub code-search response was not used as evidence of absence. The repository was not modified.

## Selected gap

A concrete rank-one Banach/Tate/Berkovich analytic theory and its exact relationship to the repository's Hahn-coefficient rings.

Berkovich geometry is explicitly mentioned and compared with other integration categories in the contours-and-stokes package. The gap is therefore substantive underdevelopment of that bridge, not the absence of a named topic. The article acknowledges this in its opening section.

## Sources inspected

All paths below are relative to the pinned repository snapshot.

| Path | Inspection scope and relevance |
|---|---|
| `docs/README.md` | Documentation catalogue and cross-report category warnings; used to select a topic distinct from the existing large reports. |
| `docs/surcomplex/analysis/article.tex` | Introductory field, normal-form, size and analytic-category material. The new article retains the distinction between Conway monomials and surreal exponentiation. |
| `docs/surcomplex/analytic-geometry/README.md` | Descriptions of the radius-free ring, common-domain ring, formal-coefficient ring, and their non-interchangeability. |
| `docs/surcomplex/polynomial-algebra/README.md` | Detailed coverage map of finite-degree valuation root geometry, Newton profiles, Hensel factorization, and residue duality. |
| `docs/surcomplex/polynomial-algebra/article.tex` | Introductory scope, source map and coefficient/geometry conventions; not an independent audit of every theorem. |
| `docs/surcomplex/contours-and-stokes/README.md` | Explicit six-part comparison with Berkovich and other categories, and the intrinsic-versus-full-fine topology qualification. This is the main evidence that the selected topic is a comparison needing deeper development, rather than an absent topic. |
| `docs/surcomplex/contours-and-stokes/article.tex` | Introductory category distinctions and references to external non-Archimedean geometry. |
| `docs/foundations-and-computation/foundations/README.md` | Lines 1–220 requested through the connector. The two opposite-sign quadratic-exponent examples, the fixed-workspace versus full-class qualification, and the provenance of the plus-sign entire series are explicit here. |
| `docs/foundations-and-computation/computer-algebra/README.md` | Capability contracts: exact denotation, coefficient access, decision procedures and certified approximation must remain separate. |

The source links in the article bibliography use the full pinned commit, not the moving default branch. Links to accompanying article sources are also provided for the reader; a bibliography link is not a claim that every linked file was independently proof-audited.

## Existing results deliberately not relabelled as new

1. The field and support machinery, and the distinction between intrinsic workspace topology and the full surreal topology.
2. Finite polynomial Newton profiles and residue-direction root counts.
3. Formal residue quotients and the need to distinguish actual-point and cluster residues.
4. Positive monomial rescaling of radius-free coefficient germs.
5. The nonpolynomial fixed-workspace example `sum t^(n^2) Z^n`.
6. General Hahn-field algebraic closedness and the standard Berkovich point classification.

## What the article adds

It proves a strict ring comparison, including the common-domain refinement, and an explicit positive-rescaling map into a Tate algebra. It supplies Banach proofs and quantitative tails for the convergent infinite-series category; gives principal ideals and finite quotient algebras in one variable; interprets the finite root data in Berkovich branch geometry; proves an explicit annulus retraction and computes the analytic residue obstruction; and carries the existing quadratic-exponent example through a complete zero, product and certified-computation analysis.

These are an exposition and deductions in established mathematics. The targeted audit and literature research do not certify first occurrence.

## Primary external sources used

- Bjorn Poonen, *Maximally complete fields*, L'Enseignement Mathematique 39 (1993), 87–106. Author's text: https://math.mit.edu/~poonen/papers/amsval.pdf
- Michael Temkin, *Introduction to Berkovich analytic spaces*, arXiv:1010.2235, version 2 (2011). https://arxiv.org/abs/1010.2235
- Jerome Poineau and Daniele Turchetti, *Berkovich curves and Schottky uniformization*, arXiv:2010.09043 (2020), Part I. https://arxiv.org/abs/2010.09043
- Alan D. Sokal, *The leading root of the partial theta function*, Advances in Mathematics 229 (2012), 2603–2621; arXiv:1106.1003. https://arxiv.org/abs/1106.1003
