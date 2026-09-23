# Source, novelty, and verification audit

Date: 23 September 2026.
Manuscript: **Automatic Hahn Linearity of Omnific Isomorphisms**.

## What was actually consulted

The repository was accessed through the GitHub connector. Its main reference
was observed as commit:

`0865f043aec113c14c69ef45006bbc7546a4e75a`

The following reading guides and metadata were inspected:

1. The top-level `README.md` (including its foundational and Hahn-layer
   descriptions), whose returned blob SHA was
   `71c1710f27ae4df28310a12df6faccade1da3743`.
2. `docs/README.md`, with its report inventory and review-status distinctions;
   returned blob SHA `ee31a8f31f53ab167afc1dd3fc6d745e9858971a`.
3. `docs/surreal/omnific-preserving-automorphisms/README.md`.
4. `docs/surreal/omnific-diophantine-geometry/README.md`, explicitly fetched
   at the commit above.
5. `docs/surcomplex/three-duals-of-hahn-vector-spaces/README.md`.
6. Repository contents/tree metadata and the main ref.

These were targeted reads, not a clone and complete examination of every
manuscript. The attempted ranged fetch of the very large
`docs/FORMALIZATION.md` returned no content. No argument here relies on
claiming to have inspected that ledger in full. The guides explicitly
separate manuscript claims, proof-review scope, finite calculations, and
Lean coverage. We did not independently rerun any repository proof or build.

The user's Wikipedia link was used for orientation, not as the basis of a
technical theorem. The following primary sources were consulted for the
relevant background and source comparison:

- Kaplan, Krapp, Serra, *Decomposing the automorphism group of the surreal
  numbers*, arXiv:2509.22374v3 (23 April 2026). The strong/non-strong
  distinction, example of a non-strong automorphism, class conventions, and
  pure-field homogeneity were relevant. The v3 reference for the last point
  is **Remark 2.10** (not the numbering of an earlier version).
  https://arxiv.org/abs/2509.22374v3
- Kuhlmann, Serra, *The automorphism group of a valued field of generalised
  formal power series*, arXiv:2107.03362v3 (11 April 2022); Journal of Algebra
  605 (2022), 339–376; DOI 10.1016/j.jalgebra.2022.04.023. Relevant to
  established strong automorphism and monomial-factor theory.
  https://arxiv.org/abs/2107.03362v3
- Bagayoko, Krapp, Kuhlmann, Panazzolo, Serra, *Automorphisms and derivations
  on algebras endowed with formal infinite sums*, arXiv:2403.05827v2
  (22 September 2025). Relevant to summability terminology and formal
  exponential/derivation context. No unrestricted class-level operator
  exponential correspondence is imported into our convex-criterion proof.
  https://arxiv.org/abs/2403.05827v2
- Blute, Cockett, Jacqmin, Scott, *Finiteness spaces and generalized power
  series*, arXiv:1805.09836 (24 May 2018). Relevant as a precedent for support
  duality; the general framework is not claimed as new.
  https://arxiv.org/abs/1805.09836
- L'Innocente, Mantova, *A factorisation theory for generalised power series
  and omnific integers*, arXiv:1710.07304v5 (22 January 2024; initial
  submission 2017). Relevant arithmetic background, not a conjecture
  claimed solved again by the present manuscript.
  https://arxiv.org/abs/1710.07304v5

Conway's and Gonshor's books are cited for classical normal-form background;
this work did not undertake a new cover-to-cover audit of those books.
The arXiv pages, HTML, and selected PDF pages were checked in the targeted
comparison. The later date displayed inside the KKS HTML is not treated as
an additional arXiv revision.

Exact-phrase web searches were not exhaustive and sometimes returned mostly
irrelevant results. They are not evidence of absence from the literature.

## Existing results that are not claimed as new

The omnific automorphism guide already records a strong stabilizer
factorization (its Theorem 5.1), the convex-support criterion (its Theorem
3.3), many shears, coefficient-field reconstruction, and further fixed-field
and nondefinability results. The Diophantine guide records the fraction-field
identity, multiplier ring, real-coefficient reconstruction, and preservation
of constants by automorphisms. Those ingredients are credited in the article
and the necessary elementary arguments are reproved.

The three-dual guide concerns vector-valued Hahn spaces and a different
linearity convention. Our scalar residue representation theorem is not a
renaming of its distinction among continuous, strong, and representable
Hilbert functionals; conversely, it does not replace any of that theory.

Hahn multiplication, the Neumann support lemma, ordinary Taylor deformation
by a derivation, and field-derivation extension through separable algebraic
extensions are established mechanisms. They are not presented as inventions.

## Proposed contribution

The principal proposed contribution is the direct implication:

    abstract automorphism of Oz
        -> reconstructed real field and constant term
        -> preservation of the residue pairing
        -> preservation of all set-indexed Hahn sums.

The last implication is proved using a binary finite-row witness that detects
failure of well-ordering even when individual coefficient tests miss it. This
removes the strongness assumption from the existing real omnific stabilizer
factorization. The manuscript does not claim that no part of the residue
criterion has appeared before in a different support-duality language.

A second proposed contribution is the explicit scale-separated self-embedding
of the whole pair. Its exponent map sends the additive surreal group into its
purely infinite subgroup, preventing all collisions between distinct Taylor
blocks. It preserves and reflects the omnific predicate, moves a prescribed
transcendental real, and supplies a nonextendible *set-sized restriction* even
though it extends to an embedding of the entire pair.

The claimed surcomplex extensions preserve the distinction between named
conjugation and the weaker assumption of valuation compatibility. No full
unconditional Gaussian-automorphism classification is claimed.

## Verification and unresolved scope

Mathematical proofs, finite checks, and machine-checked proofs are separate:

- The paper supplies proofs of its numbered statements.
- `code/verify.py` passes 13,885 exact finite assertions. This does not prove
  the infinite or class-sized statements.
- There is no Lean or other proof-assistant certificate for this manuscript.
- The PDF was compiled and rendered; the local record is `BUILD_REPORT.json`.
- No historical-priority certification or independent refereeing was obtained.

The paper explicitly avoids four unjustified extrapolations: replacing
isomorphisms with arbitrary embeddings; extending set-sized residue dual
representation to the full class of surreals; deriving full Hahn fields as
fraction fields of arbitrary small canonical integer parts; and treating local
convex-support data as a complete global admissibility/invertibility theorem.
