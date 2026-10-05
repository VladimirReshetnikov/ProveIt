# Source and provenance ledger

Sources inspected on 4 October 2026. This is a selected source audit, not a complete historical-priority search.

## Research intersection

**Elliot Glazer, A Topological Tennenbaum Theorem (2023)**  
https://arxiv.org/abs/2311.13699

Primary source establishing the research connection with Borel models of arithmetic and continuity of operations. The article uses this as motivation, not as a hypothesis-free obstruction for arbitrary ordered fields. The supplied LinkedIn profile was not relied on for mathematical claims.

## Established support-ideal results

**Francisco Guevara and Carlos Uzcategui, Frechet Borel ideals with Borel orthogonal, arXiv:1312.4095v2**  
https://arxiv.org/abs/1312.4095  
https://arxiv.org/html/1312.4095v2

Originally submitted in 2013; version 2 dated 8 February 2017. Theorem I gives the F-sigma-delta ceiling for their ideal family; Theorem 4.13 identifies scattered restrictions of the well-order ideal. The displayed auto-generated HTML date is not treated as the paper's publication date. The manuscript credits these established facts and independently proves a cut test used in its certificate constructions.

## Standard descriptive set theory

**Alexander S. Kechris, Classical Descriptive Set Theory, Springer, 1995**  
https://doi.org/10.1007/978-1-4612-4190-4

Reference for the classical perfect-set, Borel-hierarchy, well-founded-tree completeness, and analytic-image inputs. The report gives its own explicit Fin/row-finiteness reductions and Kleene--Brouwer embedding argument.

## Closely related recent work

**Chris Hall, Julia Knight, and Karen Lange, Complexity of well-ordered sets in an ordered Abelian group**  
Monatshefte fur Mathematik 208 (2025), 665--686; published 11 June 2025.  
https://doi.org/10.1007/s00605-025-02079-w

The publisher abstract and metadata were inspected. This concerns order-type restrictions and support operations, rather than the report's unrestricted-input validity classification. No claim is made to solve an open problem from this paper. Its inaccessible full text was not treated as if it had been read.

## ProveIt implementation anchor

**Vladimir Reshetnikov, ProveIt**  
Commit: `c39974f12a45c8795575ab222f3b84b2901c394f`

https://github.com/VladimirReshetnikov/ProveIt/blob/c39974f12a45c8795575ab222f3b84b2901c394f/Algebra/SurrealNumbers/Surreal/HahnSeries/StrongEvaluation.lean

The selected file was read. It defines `PowerSeriesSummable`, constructs jointly summable evaluation families, and proves `evaluate_powerSeriesSum` and `summable_evaluate_powerSeries`. It uses the support and finite-co-support proof fields of Hahn `SummableFamily`. The repository was not cloned or rebuilt for this report, and no newly formalized theorem is supplied.

**mathlib official Hahn summability documentation**  
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/HahnSeries/Summable.html

Primary documentation for the standard Hahn summable-family interface. The report's explicit coefficient-bound data are additional representation information, not a claim that the existing formal abstraction already supplies computational moduli.

## Earlier project question

**Borel Presentations and Support Barriers in Omnific Arithmetic**  
Research report prepared with ChatGPT for Vladimir Reshetnikov, 3 October 2026.  
Prior Library artifact: `glazer_proveit_article.pdf`.

The title, abstract, and Question 12.3 were retrieved from the user's Library. The question asks for the exact Borel levels and Wadge degrees beyond finite lexicographic rank. The present report answers those classification parts. The earlier report is a project artifact, not a refereed publication, and is not bundled in this package.

## Original proof work and verification

The forbidden-order proof, real-code transfer, strong-family classification, closed certificate spaces, selector comparison, real-bound regularization, and fixed-group uniformity reduction are fully argued in the article. Their historical priority is not certified. Exact rational finite checks were run; the PDF was compiled, checked for unresolved references and overfull boxes, rendered, and visually inspected. These production checks are not independent mathematical peer review.
