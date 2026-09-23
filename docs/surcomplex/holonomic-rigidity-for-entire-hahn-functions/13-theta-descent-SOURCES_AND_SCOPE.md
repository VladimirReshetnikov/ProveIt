# Sources, repository comparison, and priority boundary

Research date: 23 September 2026.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/Surreal
Commit: `4cdeaec43ff1692ed2ad9f5bdf761a41872975a5`

The repository was read through the GitHub connector. The root and documentation inventories were inspected, followed by the relevant report passages. This was a targeted comparison, not a full audit of every file, archived manuscript, branch, or commit.

### Exact question answered

File:
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`

Question 19.1, source label `hol:q:nonlinear`, and its status discussion appear in the source ranges read around lines 4125–4290. The question asks whether a nonpolynomial strongly entire function over an order-unit Hahn field can satisfy an algebraic differential equation of order at least two, whether differentially algebraic quotients of entire functions must be rational, and whether absence of an order unit is necessary for all-order rigidity.

The status explicitly says that the no-order-unit case is already settled and the order-unit case has no counterexample in that report. The present function answers the existence question positively for every order-unit group and disproves the proposed rationality statement there. The obstruction without an order unit is credited to the repository and given a full proof in the article.

Other inspected passages in this report include the nonlinear corner criterion, the vanishing-corner monomial example, the first-order limitation, the source and priority discussion, and the dependency ledger. The report's README was also inspected.

### Prior theta and uniformization material

File:
`docs/surcomplex/hahn-tate-uniformization/README.md`

The pinned report already treats bilateral theta strong domains and Hahn–Tate uniformization at arbitrary rank. Neither bilateral theta summability nor Tate uniformization is claimed as newly invented here. The new manuscript concerns descent to an entire power series, the exact order-unit differential-algebraic existence boundary, the minimal-order certificate, and its stated consequences. The existing report's README, rather than its complete 65-page article, was inspected for this comparison.

## Public primary and institutional sources consulted

1. NIST Digital Library of Mathematical Functions, Chapter 20, §20.5: Jacobi theta product identities, especially 20.5.3 and 20.5.9.
   https://dlmf.nist.gov/20.5

2. NIST DLMF, Chapter 23, §§23.6 and 23.8: theta–elliptic relations and trigonometric expansions.
   https://dlmf.nist.gov/23.6
   https://dlmf.nist.gov/23.8

3. *Elliptic Curves and Modular Forms*, lecture notes hosted by M. Woodbury (2010), §16, printed p. 32. The page containing the Tate equation and invariant differential was inspected as a PDF image. The notes' formula normalization agrees with the article's constants. Hosting attribution is not a claim that Woodbury authored every part of the notes.
   https://www.mi.uni-koeln.de/~woodbury/research/ecnotes.pdf

4. A. Sebbar, *Finite and Infinite Order Differential Relations for Theta Functions*, Milan Journal of Mathematics 84 (2016), 317–347. DOI 10.1007/s00032-016-0261-6. The publisher abstract and references were consulted; the subscription full text was not inspected. The abstract explicitly describes classical third-order theta differential relations, so no novelty claim is made for such an identity as such.
   https://doi.org/10.1007/s00032-016-0261-6

5. Y. Ohyama, *Differential relations of theta functions*, Osaka Journal of Mathematics 32 (1995), 431–450. Publication metadata were consulted; the paper was not used in place of the supplied proofs.
   https://projecteuclid.org/journals/osaka-journal-of-mathematics/volume-32/issue-2/Differential-relations-of-theta-functions/ojm/1200786061.full

6. V. Mantova and M. Matusinski, *Surreal numbers with derivation, Hardy fields and transseries: a survey*, Contemporary Mathematics 697 (2017), 265–290. Institutional/author publication records and the public preprint were consulted for normal forms and bibliographic details.
   https://arxiv.org/abs/1608.03413

## What this search does not establish

Several broad keyword searches returned irrelevant results. They are not evidence that a result is absent from the literature. A repository content search that returned no matches was followed by direct file reads and was not used as proof of absence.

No exhaustive MathSciNet or zbMATH review, complete survey of book treatments, or full citation-network review was conducted. In particular, no assertion is made that Sebbar or Ohyama lacks a related minimal-order theorem. The article supplies its own proof and distinguishes the classical ingredients from the repository-specific answer.

The defensible claim is a fully worked answer to an explicitly verified repository question, plus a proposed theorem package whose exact bibliographic priority remains to be established. No named historical conjecture is claimed solved.
