# Source audit and claim boundaries

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot used for the main source comparison:
`465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`.

The principal source is:

`docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`

Stable link:
https://github.com/VladimirReshetnikov/Surreal/blob/465a54b479a1ee842cbf7db1689a7d2f6bfe25e1/docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex

The accompanying README and the `docs/README.md` catalogue were also inspected.
The review was concentrated on the directly relevant report, not a claim to
have independently checked every proof in the entire repository.

## Results already in that source

The following are not claimed as new in the delivered article:

- Exact image of the value/jet interpolation map.
- Identification of the one-simple-node-per-shell quotient with sequences
  eventually integral in the radius coarsenings.
- Canonical product and entire divisibility background.
- Free-ultrafilter maximal ideals, their residue fields, and the maximal
  spectrum's identification with beta N.
- Cofinal extensions preserving entireness and the relevant zero-set background.

Relevant source labels include:
`ent:thm:image`, `ent:thm:quotient`, `ent:cor:single-node`,
`ent:thm:product`, `ent:thm:maximal`, `ent:sm:thm:maximal-all`, and
`ent:sm:thm:beta`.

The delivered article reproves the simple-node analytic statement that it
needs, rather than relying on the full merged report's unreviewed prerequisites.
This is a specialized exposition/proof, not an originality claim for interpolation.

## Primary literature

1. Carmelo A. Finocchiaro, Sophie Frisch, Daniel Windisch,
   *Prime ideals in infinite products of commutative rings*,
   arXiv:2009.03069v2, revised 24 August 2023.
   https://arxiv.org/abs/2009.03069v2
   The abstract, metadata, and relevant product/valuation-prime discussion
   were consulted. This is a direct antecedent for the abstract ultrafilter
   and valuation-domain mechanism.

2. The Stacks Project, Section 10.50, *Valuation rings*, Tag 00I8.
   https://stacks.math.columbia.edu/tag/00I8
   Standard valuation-ring facts are credited; the exact forms needed are
   also proved in the article.

3. B. H. Neumann, *On ordered division rings*, Trans. Amer. Math. Soc.
   66 (1949), 202–252.
   https://www.jstor.org/stable/1990552
   Standard positive-support Hahn–Neumann machinery is used as a classical
   input, not reproved or claimed as new.

4. J. H. Conway, *On Numbers and Games*, second edition, A K Peters, 2001;
   H. Gonshor, *An Introduction to the Theory of Surreal Numbers*,
   Cambridge University Press, 1986.
   Standard normal-form background is cited for the embeddings into No and No(i).
   These books were not subjected to an exhaustive page-by-page review here.

## Proposed extensions developed in this article

- All nonmaximal prime fibres of the specified entire divisor quotient.
- The order-unit versus continuum-chain dichotomy for reduced divisors.
- Local valuation rings and the simultaneous elementary-divisor-ring structure.
- Exact convex-subgroup intervals for prime extension under a cofinal enlargement.
- Stable minimal and maximal spectra but noninjective full spectral contraction.
- Explicit integer-indexed versus rational-indexed surreal scale examples,
  including continuum many prime extensions of one old maximal ideal.
- A precise bounded-multiplicity threshold for reduction of the prime spectrum.

The abstract ingredients have substantial classical precedent. The proposed
originality is in the stated analytic realization and combined constructions,
not in ultraproducts or the valuation-prime correspondence themselves.

## What this audit does not establish

A targeted search and comparison do not certify publication priority or the
absence of an equivalent result under other terminology. No named published
open conjecture is reported as solved. No peer review, proof-assistant check,
or claim of complete verification of the source repository is implied.

The complete prime classification is for one simple node per occupied shell,
with its bounded-multiplicity extension. The article does not claim a full
classification for arbitrary colliding shell algebras, arbitrary unbounded
multiplicities, or the entire proper-class field No(i).
