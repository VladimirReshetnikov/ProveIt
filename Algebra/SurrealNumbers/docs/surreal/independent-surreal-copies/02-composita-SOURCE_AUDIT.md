# Source and novelty audit

## Repository snapshot

Repository: `VladimirReshetnikov/Surreal`.

Pinned commit: `7b256e0792df7718995b816ad12a77bf56731f8f`.

The commit metadata returned by GitHub records `2026-09-24T00:21:12Z`; this is 23 September in the Pacific time zone. The manuscript's date is 23 September 2026.

Primary comparison file:

`docs/surreal/independent-surreal-copies/article.tex`

Blob: `7d5cfe644e7c902f2b594179c337a6c633350fc3`.

The directly retrieved source ranges used here were lines 1120–1330 and 1640–1830. They include the explicit inner/outer copies, scale separation and re-expansion, finite coefficient-field control, and the exact compositum/dimension question. The report's README was read for its theorem inventory, stated single-witness result, and limitations. This is a targeted comparison, not a claim to have rechecked every proof in that 34-page report.

The repository root README and `docs/README.md` were consulted for the collection's scope and review status. READMEs for the omnific Diophantine and holonomic-rigidity reports were consulted to avoid repeating unrelated existing claims. No mathematical theorem from those reports is a proof dependency of this article.

The primary repository question is **Section 12, Question 3, “An exact description of ordinary composita.”** It asks for a characterization inside the Hahn join and transcendence degrees in natural set-sized and class-sized examples. The answer here is scoped to separated coordinates, the specified Laurent cardinal range, and the explicit pair of class copies. It is not an answer for every ordered amalgam or every coefficient extension.

## Contributions already in the repository

The maps induced by inner support intervals `(0,1)` and `(3,4)` are existing constructions. So are their intersections, their scale separation, the iterated Hahn interpretation, the necessary finite coefficient-field condition, and one transcendental witness obtained from an independent coefficient sequence. The monomial denominator-clearing mechanism for omnific fractions is also existing material. These are credited explicitly.

The finite-rank tensor-image argument is elementary algebra. It is used to formulate an exact coefficient criterion, without a priority claim for the underlying tensor fact. Coset slices and ordinary base-change arguments are likewise background mechanisms.

## Candidate contributions of this draft

1. The rapid **coefficient-degree** differential-independence theorem over `k((t))(x)`, allowing arbitrary Laurent-series coefficients in the polynomial relation.
2. Private coefficient-block differential independence over the entire finitely-generated-coefficient envelope, and its tree amplification.
3. Their combination giving the exact algebraic and differential transcendence degrees `|F|^(aleph_0)` under the stated hypotheses.
4. The explicit purely infinite omnific family with support order type omega, and sharpness of its support cardinality.
5. Tail resilience of this same predefined family under arbitrary set-sized parameter adjunction, including differential parameters.
6. Persistent nonintegrality of the arithmetic join after set adjunction and the Gaussian versions.

These are proposed research contributions with written proofs. A targeted source search did not establish that they appear elsewhere, but absence from that search does not establish novelty. No priority certification, peer review, or Lean verification is claimed.

## Public sources consulted

- Krapp, Kuhlmann, Serra, **Generalised power series determined by linear recurrence relations**, arXiv:2206.04126v3. Its abstract and introductory material were used for the comparison with recurrence-based rationality and subfield questions, not as a theorem proving our coefficient-rank criterion or dimension results.
- Kuhlmann, Matusinski, **Hardy type derivations on generalized series fields**, arXiv:0903.2197v4, DOI 10.1016/j.jalgebra.2011.11.024. General series-derivation definitions and source pages were inspected. We do not claim a full review of its Hardy-type theory. Our Euler derivation is proved directly and is not identified with a Hardy-type derivation.
- Berarducci, Mantova, **Surreal numbers, derivations and transseries**, arXiv:1503.00315v3, JEMS 20 (2018), 339–390, DOI 10.4171/JEMS/769. Consulted to distinguish the natural exponential-compatible surreal derivation from the artificial diagonal derivation here.
- L'Innocente, Mantova, **A factorisation theory for generalised power series and omnific integers**, arXiv:1710.07304. Consulted for existing omnific arithmetic and factorization context; no factorization result is claimed new here.
- Stacks Project, Tag 09IC, **Linearly disjoint extensions**. Used for standard terminology and the tensor definition. The particular transfer proofs used here are included in full.
- The user-linked Wikipedia page on surreal numbers was consulted for orientation only and is not used as a proof source.

Additional survey and automorphism search results were inspected during topic selection, but are not load-bearing references. This audit does not imply that all related literature has been read.

## Independence of verification claims

The mathematical proofs, source/priority comparison, finite computational checks, PDF build, visual inspection, and Lean formalization are distinct tasks. Only the first five were undertaken here, with source comparison and proof review explicitly limited as above. The finite checks do not verify the infinite proofs, and no Lean code is delivered or claimed.
