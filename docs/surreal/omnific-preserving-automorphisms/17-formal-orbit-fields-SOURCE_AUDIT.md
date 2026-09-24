# Source and novelty audit

## Scope and comparison pin

Prepared for the request about new results on surreal, surcomplex, and
omnific arithmetic. The repository comparison is pinned to:

    VladimirReshetnikov/Surreal
    efc5446229dbf61a97bdd5edae91dba20af9d131

The pin was retrieved from the GitHub connector. The repository was not
modified. This package does not redistribute repository manuscripts or
external papers.

## Repository material actually inspected

The GitHub connector was used to retrieve metadata, the root README, the
documentation catalogue, and targeted source material. The substantive
comparison concentrated on:

- `docs/surreal/omnific-preserving-automorphisms/README.md`
- `docs/surreal/omnific-preserving-automorphisms/article.tex`, with searches
  and relevant excerpts around its formal-flow and monomial orbit material
- `docs/surreal/omnific-preserving-automorphisms/02-parameter-rigidity-source_audit.md`
- `docs/surreal/independent-surreal-copies/README.md`
- `docs/surreal/omnific-diophantine-geometry/README.md`
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`

Some large connector responses were truncated in their initial display;
relevant monomial-orbit and non-claim passages were obtained by searching
the returned response. This was a targeted comparison, not a complete
reading of every page of the large merged manuscripts, all incoming
companions, or the whole Lean library. Root guide statements were not used
as substitutes for the more specific current manuscript description where
they differed.

The key predecessor labels are `opa:par:thm:orbitfield` and
`opa:par:cor:continuum`. Its non-claims explicitly state that its orbit-field
formula concerns monomials and only gives a lower bound for the full formal
image. The new article answers that full-image question for the specified
constant-term Euler derivation. Internal independent surreal copies are
separately distinguished from this paper's external formal embeddings.

No general automorphism-classification theorem, proposed quotient theorem,
or other unreviewed repository claim is used as a logical premise. The
Euler derivation, arithmetic restriction, and denominator lemma needed
here are reproved from classical normal forms.

## Literature consulted and roles

The article supplies bibliographic links for all entries. Primary-source
records and relevant accessible text were used for the following contexts:

- L'Innocente–Mantova, *A factorisation theory for generalised power series
  and omnific integers*, arXiv:1710.07304, Advances in Mathematics 442
  (2024), 109513: normal-form and omnific arithmetic context.
- Kaplan–Krapp–Serra, *Decomposing the automorphism group of the surreal
  numbers*, arXiv:2509.22374v3: modern automorphism setting and class-function
  conventions. The primary HTML was consulted.
- Bagayoko–Krapp–Kuhlmann–Panazzolo–Serra, *Automorphisms and derivations on
  algebras endowed with formal infinite sums*, arXiv:2403.05827: formal
  summability context. No unexamined theorem from it is needed in a proof.
- Gabriel Ng, *Taylor morphisms*, arXiv:2308.11731, Journal of Algebra 701
  (September 1, 2026), 219–255, DOI 10.1016/j.jalgebra.2026.04.028:
  generalized Taylor morphisms. Publication metadata was checked on the
  primary publisher site. The formal Taylor construction is not claimed new.
- Florian Heiderich, *Galois theory of Artinian simple module algebras*,
  arXiv:1111.6522, and the 2013 SMF introductory article: primary arXiv and
  publisher records identify the Galois-hull/Umemura background. These are
  context citations, not asserted theorem-number matches.
- Conway, Gonshor, and Kolchin are classical background references; a new
  cover-to-cover reading of their monographs was not performed. The
  differential-field lemmas used here are proved in the article, and no
  unchecked page-specific attribution is made to those books.

The supplied Wikipedia page was consulted as orientation, not used as the
proof source for technical results.

## Proposed contribution versus standard machinery

Proposed combined contribution:

1. exact full-image relation descent for the chosen surreal Euler flow;
2. explicit ordinal-indexed omnific witnesses, giving independent families
   of every set cardinality in the full image over the whole coefficient field;
3. transcendence of additive time over that entire orbit field;
4. exact rational/algebraic trajectory classification and finite-degree
   preservation for multiplicative time, together with the contrasting
   parameter recovery and persistence of the independent families.

Not claimed new: Taylor morphisms, Euler derivations, formal binomial
operators, the constants linear-disjointness lemma, the general idea of
combining a field with its Taylor image, the rational logarithmic-derivative
obstruction, Vandermonde identities, Eisenstein, or the abstract finite
scalar-extension arguments.

Searches and comparison did not establish a prior occurrence of the complete
surreal-specific package or the explicit omnific family. That is not an
exhaustive absence result. The abstract lemmas may already have stronger
general formulations in differential algebra. Priority and significance
require expert review independently of the correctness of the proofs.

## Verification status

This package contains conventional proofs and finite exact checks. No Lean
formalization was produced or executed, and no independent peer review is
claimed. The build audit concerns PDF production only, not mathematical
validity. The repository's own reported Lean builds are not represented as
checks performed in this session.
