# Sources and attribution boundaries

Sources were inspected for this work on 28 September 2026. The main ProveIt
report was retrieved from a pinned GitHub source, not inferred from the
repository's general README.

## ProveIt research question and existing results

Repository commit: `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`.

*Surreal Fields Across Set-Theoretic Universes*, merged report dated
22 September 2026:

https://github.com/VladimirReshetnikov/ProveIt/blob/e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9/Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-fields-across-universes/article.tex

Relevant existing material: fresh signs and all set-presented gaps
(Theorems 8.4-8.5); countable saturation and new reals; the class ACF
back-and-forth and real forms; Question 19.2 on forcing-specific full spectra;
Question 19.4, `univ:q:completeness`, on the completeness of the gap invariant.
These are unrefereed repository results. The present article reproves the
parts needed for its main theorem.

Project README and status overview:

https://github.com/VladimirReshetnikov/ProveIt/blob/e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9/Algebra/SurrealNumbers/README.md

## Published forcing inputs

Vera Fischer, Marlene Koelbing, Wolfgang Wohofsky.
*Fresh function spectra*. Annals of Pure and Applied Logic 174(9) (2023), 103300.

https://doi.org/10.1016/j.apal.2023.103300
https://www.logic.univie.ac.at/~vfischer/fresh_function_spectra.pdf

Relevant results: Proposition 2.2 (square-chain-condition obstruction),
Corollary 2.4 and its following Cohen example, Propositions 5.2-5.3
(coding lengths/functions/subsets), and Proposition 6.1 (the generalized-Cohen
fresh spectrum without cardinal arithmetic). Those forcing results are not
novel claims of this report. The article gives a maximal-antichain proof of
the square-chain-condition lemma and explicitly derives the surreal
consequences. The full generalized-Cohen gap theorem needs only the size
upper bound, closure, and the displayed block collapse argument.

## Classical surreal foundations

John H. Conway, *On Numbers and Games*, 2001 edition, originally 1976:
https://www.routledge.com/On-Numbers-and-Games/Conway/p/book/9781568811277

Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*,
LMS Lecture Note Series 110, Cambridge University Press, 1986:
https://doi.org/10.1017/CBO9780511629143

Philip Ehrlich, *The absolute arithmetic continuum and the unification of all
numbers great and small*, Bulletin of Symbolic Logic 18(1) (2012), 1-45:
https://doi.org/10.2178/bsl/1327328438

## Proposed contribution and limits

The main proposed contribution is the exact Boolean embeddability theorem
for old surreal fields whose full gap and saturation spectra agree, together
with its one-Cohen-real, arbitrary-poset, and involution consequences.
Archimedean residues are standard; the application retains their actual
rational cuts rather than only their cardinalities. The field-nonisomorphism
argument is not an argument about pure-order nonisomorphism.

The literature check is not an exhaustive priority determination. No outside
paper is redistributed, and the archive includes no claimed Lean proof.
