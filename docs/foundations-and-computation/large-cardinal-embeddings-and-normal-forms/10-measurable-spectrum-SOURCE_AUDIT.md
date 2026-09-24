# Source and novelty audit

Date: 23 September 2026.

## Repository snapshot

The comparison is pinned to:

`VladimirReshetnikov/Surreal` at `7af8a3026c8440944e94df89020d42ca08f4e3dd`.

The read path used the GitHub connector. Root documentation, the report catalogue, selected report READMEs, and the relevant passages of the following maintained sources were inspected:

- `docs/surreal/omnific-preserving-automorphisms/article.tex`
- `docs/foundations-and-computation/large-cardinal-embeddings-and-normal-forms/article.tex`

The inspection was targeted, not a complete proof audit of the repository, its history, or every preserved source manuscript. No repository clone or Lean build was completed, and no repository files were changed.

An initial, earlier snapshot described automatic strongness of Oz automorphisms as open. A fresh read of the pinned snapshot showed that this had already been incorporated, along with constant-term duality. The article therefore **does not claim those results anew**. This prevents a stale novelty assertion based on the earlier read.

## Prior results expressly excluded from novelty claims

1. Conway/Gonshor normal forms and the generalized-series presentation of No.
2. Strong linear maps and the distinction from unrestricted Hahn/surreal automorphisms.
3. The finite-ultrafilter factorization mechanism for maps on direct products. Bergman's paper is the main classical source; the article gives a specialized null-ideal proof instead of claiming a new general ultrafilter theorem.
4. Automatic strongness of omnific-preserving field automorphisms and the constant-term adjoint package in the pinned omnific report.
5. The elementary embedding J obtained from a normal ultrapower, the associated termwise companion H_j, and the critical-point support defect in the pinned critical-point report.
6. Recovery of a derived measure from a coefficient of an elementary-embedding defect.

## Proposed contributions relative to the inspected material

- The general first-failure theorem for every countably strong real/complex coefficient-linear Hahn map.
- The coefficient-by-coefficient local complete-ultrafilter description and canonical strong-part/monomial-invisible decomposition.
- The full-Hahn support criterion and matching minimum field cardinality `2^kappa` for a first failure at kappa.
- Explicit order-preserving additive transvections stabilizing Oz, fixing every monomial and any prescribed set of parameters, with an exact measurable first failure.
- The corresponding surcomplex construction.
- The lower-bound direction making the measurable hypothesis optimal for countably strong coefficient-fixing omnific-preserving field embeddings.
- A concrete conditional negative answer to question `opa:as:q:targettests`, interpreted without a strongness hypothesis on the field embedding. The narrower question for strong field embeddings remains open here.

These are proposed research contributions, not a certificate that no equivalent statement exists elsewhere. They need independent proof review and a broader priority search.

## Primary literature checked

The article's internal bibliography gives persistent links and full citation details.

- George M. Bergman, *Families of ultrafilters, and homomorphisms on infinite direct product algebras*, JSL 79 (2014), 223–239, DOI `10.1017/jsl.2013.5`, arXiv `1301.6383`. The primary preprint and publisher record were consulted, with attention to the finite-complete-ultrafilter mechanism in Lemmas 3–4.
- George M. Bergman and Nazih Nahlus, *Linear maps on k^I, and homomorphic images of infinite direct product algebras*, J. Algebra 356 (2012), 257–274, DOI `10.1016/j.jalgebra.2012.01.004`, arXiv `0910.5183`. Publisher and author's records were consulted for related work and metadata; no uninspected theorem is used as a hidden premise.
- Richard Blute, Robin Cockett, Pierre-Alain Jacqmin, and Philip Scott, *Finiteness spaces and generalized power series*, ENTCS 341 (2018), DOI `10.1016/j.entcs.2018.11.002`, arXiv `1805.09836`. Used for context, not as the proof of the new first-failure theorem.
- Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the automorphism group of the surreal numbers*, arXiv `2509.22374v3`. The primary HTML was inspected for strong/unrestricted automorphisms, normal-form conventions, and class-size conventions.
- Thomas Jech, *Set Theory*, Third Millennium Edition, Revised and Expanded, Springer (2003), DOI `10.1007/3-540-44761-X`. Classical background on measurability and ultrapowers; metadata checked against the publisher.
- Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, Cambridge (1986), DOI `10.1017/CBO9780511629143`. Classical normal-form background; publisher metadata and the normal-form references in Kaplan–Krapp–Serra were checked.
- Irving Kaplansky, *Maximal fields with valuations*, Duke Math. J. 9 (1942), 303–321, DOI `10.1215/S0012-7094-42-00922-0`. Classical Hahn/valuation background; bibliographic details were checked against references in primary valuation-theory literature. No claim that this whole historical paper was read is made.

The supplied Wikipedia page was used for orientation, not as a research-proof authority. No third-party paper, source archive, or font file is redistributed in this package.
