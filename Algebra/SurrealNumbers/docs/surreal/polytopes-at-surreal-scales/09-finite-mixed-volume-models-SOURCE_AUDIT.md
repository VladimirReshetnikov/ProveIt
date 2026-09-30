# Source audit and mathematical status

Date: 30 September 2026.

## 1. Repository context actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `b2b626d8537f7dea8f20393ee4714c7201a7001e`.
This commit was returned by the GitHub connector's recent-commit query.
Some earlier code-search navigation results were indexed at
`6996fee43cc97b6c16351def7507d59a95bf62f0`; the direct source reads used for the
pinned context were then made at the commit above.

| Repository source | Inspected content | Role |
| --- | --- | --- |
| `Algebra/SurrealNumbers/docs/README.md` | Introductory status statement and reading routes; opening source lines 1–18 reread at the pinned commit | Distinguishes research prose, finite checks, and Lean coverage |
| `Algebra/SurrealNumbers/docs/surreal/euclidean-three-space/article.tex` | Source lines 80–245 at the pinned commit: abstract, status note, opening scope and scalar discussion | Motivates set-sized real-closed scalar fields, arbitrary scales, standard part, and valuation methods |

The pinned geometry source blob SHA was
`dc80119b142431067ce5e13243a893552aa487db`.

The entire geometry report was not read or independently verified. No theorem
about its rotation groups or other later material is imported into this
manuscript's proofs. No assertion is made that the present statements are absent
from every repository document or incoming archive. The repository was not
modified, cloned in full, built, or Lean-checked for this task.

## 2. Primary mathematical sources

The article's bibliography gives full publication details. The main sources
and the exact conceptual dependencies are:

### Brändén and Huh, Lorentzian polynomials

Annals of Mathematics 192 (2020), 821–891.
Author manuscript: https://arxiv.org/abs/1902.03719v8 (17 July 2024).

Theorem 3.20 relates M-convex functions to tropicalizations of Lorentzian
polynomials over a real Puiseux-series field. Theorem 4.1 supplies the classical
Lorentzian property of volume polynomials. Remark 4.3 discusses real volume
realization of matroid polynomials/supports and the elementary symmetric
four-variable quadratic obstruction. The manuscript does not claim the Fano
real-representability obstruction, the four-segment Plücker obstruction, or the
basic strict inclusion of volume polynomials in Lorentzian polynomials as new.

The explicit Fano family is checked by an independent Hessian calculation in
Section 9. Its M-convex profile follows from the cited theorem over a real
Puiseux field and then from scaling an integer-valued profile by a positive
value-group element. The separate arbitrary-rank necessity of M-convexity is
proved directly in Section 5 using polarized determinant exchange.

### Speyer and Sturmfels, The tropical Grassmannian

Advances in Geometry 4 (2004), 389–411.
https://arxiv.org/abs/math/0304218
DOI: https://doi.org/10.1515/advg.2004.023

The rank-two tropical Grassmannian/tree correspondence is classical.
Section 8 gives its own finite, arbitrary-ordered-value-group realization
argument using finitely many field representatives and integer residue labels.
It does not claim discovery of the rank-two correspondence.

### Schneider, Convex Bodies: The Brunn–Minkowski Theory

Second expanded edition, Cambridge University Press, 2014, volume 151.
https://doi.org/10.1017/CBO9781139003858

Classical inputs include Minkowski volume polynomiality, mixed-volume
monotonicity, homogeneity and covariance, and the zonotope determinant formula.
Appendix A explains why these particular finite-polytope statements transfer
to real closed fields. The manuscript does not transfer general integration or
compactness assertions to the surreal field.

### Tarski, A Decision Method for Elementary Algebra and Geometry

Revised edition, University of California Press, 1951.
https://www.rand.org/pubs/reports/R109.html

Used as context for real-closed-field transfer. The article spells out the
finite first-order assertions rather than appealing to transfer of an
unrestricted analytic theory.

### Gonshor, An Introduction to the Theory of Surreal Numbers

Cambridge University Press, 1986, LMS Lecture Note Series 110.
Used for the classical real-closed ordered-field setting of surreal numbers.
The constructions in the article are made inside a set-sized field containing
the finite input data and the real numbers.

### Menges, Comparing the sets of volume polynomials and Lorentzian polynomials

Combinatorics, Probability and Computing 35 (2026), 26–39.
Published online 19 September 2025.
https://doi.org/10.1017/S0963548325100151
Preprint: https://arxiv.org/abs/2310.07020

Used to delimit the novelty claim relative to the established real-coefficient
realization/classification literature. The paper's coefficient-level
classification is not being replaced by the valuation-profile classification
in Section 8; these are different problems.

### Huh, Volume polynomials

https://arxiv.org/html/2601.13249v4 (4 June 2026).
The earlier v3 was inspected initially; the v4 status and the relevant passages
were checked during final preparation, and the article bibliography cites v4.

Sections 2–3 and Examples 3.2 and 3.4 distinguish convex-body volume polynomials
from the projective/divisor notion. The characteristic-dependent projective
Fano question in Example 3.4 is not answered by the present manuscript.

## 3. What is proved here and what is not a priority claim

The manuscript develops explicit proofs of:

1. Simultaneous mixed-volume-valuation preservation by at most d independent
   segment generators per polytope, and the sharpness of the dm total bound.
2. A colored-minor criterion and a stronger full polarized-minor criterion,
   with an explicit finite integer specialization bound.
3. Real-polytope realization of every normalized weighted initial polynomial
   at arbitrary natural valuation rank, with coordinate-choice invariance.
4. Complete realization of finite quadratic M-convex profiles by
   parallelograms over the original field.
5. A full-support, strictly Lorentzian, three-level Fano cubic profile with no
   polytope lift, and a quadratic family separating coefficient and valuation
   realizability.

The classical building blocks are credited. These constructive formulations
and their synthesis are presented as results established in this manuscript,
not as results whose worldwide historical originality has been proved.
The search was targeted, not a systematic review of every publication or every
repository source. The ten research questions are proposed directions; they
are not all asserted to be independently documented open problems.

## 4. Verification boundary

The mathematical arguments are conventional proofs, not Lean proofs.
`verify.py` was executed successfully using Python 3.13.5 and SymPy 1.14.0.
It checks exact finite coefficient identities, Hessian identities and
characteristic polynomials, all exchange obligations for the explicit cubic
profile, deterministic rational sandwich examples, explicit quadratic
coefficient comparisons, and deterministic rank-two reconstructions.

The 23 sandwich examples and 15 rank-two reconstructions are tests of finite
instances, not exhaustive proofs of the general constructions. The Fano
exchange enumeration is exhaustive only for that one 84-element profile.
No arbitrary-surreal sign algorithm or normal-form parser is implemented.
The matrix criteria are finite mathematical certificates, not a claim of a
polynomial-time decision procedure for arbitrary surreal inputs.

The compiled PDF was checked for LaTeX warnings and visually inspected after
rendering. This is a layout check, not independent mathematical refereeing.
