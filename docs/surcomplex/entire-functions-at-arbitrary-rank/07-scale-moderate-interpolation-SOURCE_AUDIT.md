# Source and novelty audit

## Scope of the review

The repository was accessed through the GitHub connector at the pinned revision below. The documentation index, formalization ledger, and relevant portions of the arbitrary-rank entire-function report were inspected. This was a targeted review, not a claim to have independently audited every theorem in the repository.

Repository: VladimirReshetnikov/Surreal  
Pinned commit: `0097304c7ae9d5de46d2ea342e2494f8fc126303`  
Review date: 22 September 2026

The relevant unresolved issue is the image of the infinite jet map in the source file `docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`, subsection label `ent:subsec:jet-image`. The source establishes an injection into a product, exhibits failure of surjectivity, and identifies failure of an everywhere nonzero sequence to be invertible in the quotient. The present article supplies the exact restricted-product image, including confluent radius blocks.

The source already contains the coefficient-slope criterion, canonical products, ring trichotomy, and a disjoint-zero/non-Bézout example. These are not offered as new results here. Necessary support and division ingredients are re-proved to make the interpolation argument independent of the source report's unrefereed global preparation and factorization claims.

## Primary literature consulted

1. B. Poonen, *Maximally complete fields*, L'Enseignement Mathématique 39 (1993), 87–106. Author-hosted full text was inspected. Classical Hahn-field background.
2. W. Cherry, *Existence of GCD's and Factorization in Rings of non-Archimedean Entire Functions*, arXiv:1007.0984v2. Full-text first page and relevant analytic scope were inspected. Classical real-valued non-Archimedean antecedent.
3. W. Cherry, *Lectures on Non-Archimedean Function Theory*, arXiv:0909.4509. Analytic background over real-valued non-Archimedean absolute values.
4. O. Helmer, *Divisibility properties of integral functions*, Duke Math. J. 6 (1940), no. 2, 345–356. Publisher metadata verified; used only as a historical antecedent, not as a proof input.
5. N. Bruno, *Ideal Structure of Rings of Analytic Functions with non-Archimedean Metrics*, Ohio State University dissertation (2021). Institutional full text, introduction, and Definition 2.3 inspected. Its value group is explicitly a subgroup of the real numbers. Relevant prior work on analytic ideals and ultrafilters.
6. M. Henriksen, *On the ideal structure of the ring of entire functions*, Pacific J. Math. 2 (1952), no. 2, 179–184. Publisher-hosted full text and page 182 inspected. Prior free-maximal-ideal and residue-field results, including the classical transcendental-coordinate pattern.
7. H. Gonshor, *An Introduction to the Theory of Surreal Numbers*, LMS Lecture Note Series 110, Cambridge University Press (1986). Publisher metadata verified; cited for classical surreal normal-form theory.

Full bibliographic references and links are embedded in the article. Search results that were irrelevant to the mathematical setting were not used as evidence.

## Proposed new statements

- The exact block-Hermite restricted-product quotient at arbitrary rank, with eventual coarsened integrality as a necessary and sufficient condition.
- The explicit inverse-block gain and cardinal suppression construction, including cofinal truncation bounds independent of block dimension and multiplicity.
- The exact unit-ideal criterion and paired-root separation threshold.
- The scale-dependent boundary residue fields and the full free-ultrafilter locus for the specified paired-root example.

The underlying finite algebra and general ultrafilter method are classical. The article explicitly credits these and does not present the mere existence of ultrafilter maximal ideals or transcendental boundary coordinates as unprecedented.

No matching statement of these exact arbitrary-rank refinements was identified in the consulted sources. This is not proof of priority or a substitute for broader expert review. No named published conjecture is claimed to have been settled.

## Verification boundary

The complete proofs are in the article. The included program passed 1,876 exact finite assertions. It does not verify infinite Hahn support arguments, cofinality, the full theorem statements, or novelty. No proof-assistant verification or independent peer review was performed. No changes were made to the remote repository.
