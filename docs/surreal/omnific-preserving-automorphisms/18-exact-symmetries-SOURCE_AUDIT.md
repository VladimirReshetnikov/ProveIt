# Source and novelty audit

Date: 23 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Commit: `efc5446229dbf61a97bdd5edae91dba20af9d131`

The commit endpoint was queried explicitly to check the identifier type.
It reports commit time 2026-09-23T23:35:05Z and Git tree
`aba698290ee2cd54f97db3a8b4038c010fcb47d8`.
The commit title is “Prove the arithmetic homeomorphisms of omnific
separation quotients.” The article is pinned to the commit, not to an
unverified guess that an arbitrary 40-character SHA denotes a commit.

The following content was retrieved through the GitHub connector at that
snapshot:

1. Root `README.md` and the recursive repository inventory.
2. `docs/README.md`.
3. `docs/surreal/omnific-preserving-automorphisms/README.md`.
4. `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`.
5. `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`.

Some long connector responses were truncated in the displayed output.
The novelty comparison uses the substantive claim descriptions actually
visible in the guides. It is not an audit of every theorem or every line
in the repository's 61 reports. No unseen companion proof is used as a
premise of the article.

A supplementary GitHub content search for `left-orderable` returned no
matches. That search covers the default branch rather than a pinned
historical search and does not prove absence of equivalent statements.

## Closest acknowledged repository antecedents

The omnific-preserving guide identifies earlier work on:

- fixed fields and a relative Hahn hull;
- large parameter stabilizers and set-parameter nondefinability;
- nonabelian actions, including an explicit wreath product;
- support-cut twists, fixed fields, and finite-orbit restrictions;
- automatic strongness and coefficient-moving embeddings.

The article does not claim to be the first to obtain any of those broad
phenomena. In particular, the ordinary double lift and the mere existence
of nontrivial or nonabelian omnific-preserving automorphisms are not
presented as new results.

The precise proposed contribution is the *combined exact theorem*:
for every set S and every nontrivial left-orderable set group G, every
nonidentity element of a strong omnific-preserving realization has fixed
field H(H(S)). The article proves the free equivariant cut-filling step
needed to obtain that stronger elementwise assertion.

The conjugation-compatible set-group classification, its nonreal-
parameter obstruction, and the arithmetic fixed-fraction gap are also
proved with their scope stated. Historical priority is not certified.

## Primary literature checked online

### Kaplan–Krapp–Serra

Elliot Kaplan, Lothar Sebastian Krapp, Michele Serra,
*Decomposing the automorphism group of the surreal numbers*.

https://arxiv.org/abs/2509.22374
https://arxiv.org/html/2509.22374v3

Version v3: arXiv submission history dates it 23 April 2026.
The HTML also displays a typesetting date; the article identifies the
version by the arXiv version stamp rather than treating that display as
an additional publication date.

Relevant content: class-foundation conventions; external Hahn group and
field lifts; Propositions 3.4 and 3.9; Construction 3.10; qualifications
about preserving exponentiation, valuation, and the omega map.

### Kuhlmann–Serra

Salma Kuhlmann, Michele Serra,
*The automorphism group of a valued field of generalised formal power series*.

https://arxiv.org/abs/2107.03362
https://arxiv.org/html/2107.03362v3

Version v3: 11 April 2022. The arXiv record also supplies the related DOI
10.1016/j.jalgebra.2022.04.023. The article cites the inspected preprint
version rather than inferring journal volume and pagination.

Relevant content: general Hahn lifting and strongly additive automorphisms.

### Rivas

Cristóbal Rivas, *Left-orderings on free products of groups*.

https://arxiv.org/abs/1106.2094
https://arxiv.org/html/1106.2094v1

Version v1: 10 June 2011.
Proposition 1.1 supplies the countable dynamical-realization result used
only in the optional explicit-construction section. The main arbitrary-
cardinality realization is proved independently in the manuscript.

### Classical background

Conway, *On Numbers and Games*, Academic Press, 1976.
Gonshor, *An Introduction to the Theory of Surreal Numbers*, Cambridge
University Press, 1986, LMS Lecture Note Series 110.

The bibliographic metadata was cross-checked in the primary article's
reference list. The present work assumes the classical normal-form,
real-closedness, and set-cut theorems; it is not a new reconstruction of
those foundational results.

The user-supplied Wikipedia page was inspected as orientation, not used
as the proof source for the principal claims.

## What the searches do not establish

No search can certify that the exact realization theorem has never
appeared before under different terminology. The manuscript therefore
separates mathematical proof from originality assessment. It does not
claim peer review, a verified Lean proof, or resolution of a previously
published named conjecture whose statement was not matched exactly.
