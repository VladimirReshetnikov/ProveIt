# Source and provenance audit

Access date: 20 September 2026. This is a bounded literature check, not an
exhaustive mathematical priority search.

This file merges the provenance records of two independently prepared
packages, `multiple-chain-exponential-formula` (the base of the merge) and
`multiple-chains-exponential-identity`. Neither record was a subset of the
other: the first carries the upload hash and the version reasoning for the
pinned source, the second carries two adjacent 2026 papers and the
Section 9.4 cross-check. Both are retained below.

## 1. Requested selection basis: supplied manifest

The exact uploaded file is preserved as `context/manifest.tex`.
SHA-256 of that upload: `729fb6e3aef3f30c7c5284c4296681fba72b6d6af68211f178ad0bc3c5d15b41`.
Both merged packages shipped byte-identical copies of it (one under
`context/`, one under `provenance/`); only `context/manifest.tex` is kept.
This hash identifies the supplied source file; the package contains no
checksum manifest of its own files, and none should be added.

The complete catalogue was read; it records seventy-one packages. The
relevant entries are “Reciprocity and Matrix Duality for Preorder Polytopes”
and “A Reflexive Root-Polytope Model for Preorder h-Polynomials.” They describe
different targets in Athanasiadis–Chapoton: reciprocity/transpose duality and
polytopal realization. The Section 9.5 generating-function identity selected
here is not among the results described in the manifest. The catalogue itself
warns that it records claimed results without checking their proofs. No
unseen source package has been treated as verified, and no such package is
needed for either proof; the manifest was used only for topic selection and
duplicate avoidance.

## 2. Primary source of the target

Christos A. Athanasiadis and Frédéric Chapoton,
*Polytopes and posets associated to preorders*, arXiv:2605.26916v1 (2026).

- https://arxiv.org/abs/2605.26916v1
- https://arxiv.org/html/2605.26916v1
- https://arxiv.org/pdf/2605.26916v1

The target is the unnumbered display in Section 9.5, “Multiple chains,”
printed page 24 (zero-based page 23). Its introduction labels it as suggested
by experimental evidence. The chain has n preorder-equivalence blocks of
cardinality k, not n antichains of cardinality k. The paper's support
h-polynomial counts nonzero coordinates; it is not the Ehrhart h*-polynomial
of its nonnegative preorder polytope. The article's d replaces the paper's k,
and its t replaces the paper's t^2. The paper's substitution t^2 and factor
t^(-nk) are removed explicitly in Section 1 of the article.

The display was read in structured HTML and parsed PDF text. Repeated web
screenshot attempts for PDF page 24 failed with retrieval and cache errors,
and an attempted container retrieval also failed because the arXiv host could
not be resolved. Accordingly, no visual inspection of the source PDF is
claimed and no unavailable screenshot is treated as evidence. This does not
leave the formula unread: both text representations expose its full equation.
The v1 PDF carries a May 27, 2026 document date and a May 26 arXiv upload
stamp; the version identifier, rather than a rendering timestamp, is the
pinned source.

The first few k=2 rows printed in Section 9.4 of the same paper were matched
against the independently computed rows (1+4t+t^2; 1+12t+27t^2+12t^3+t^4;
1+24t+134t^2+236t^3+134t^4+24t^5+t^6; and the fourth row), as an additional
cross-check only.

The unversioned abstract record returned only v1 during this check. Targeted
searches using the paper identifier, multiple-chain terminology, and the
exponential identity found no later primary-source proof. This is limited
search evidence, not certification of current open status or novelty. Search
engine conjecture aggregators were not used as mathematical authorities.

## 3. Earlier composition-polytope work

Christos A. Athanasiadis,
*Lattice point enumeration of polytopes associated to integer compositions*,
arXiv:2510.23903v1 (2025).

- https://arxiv.org/abs/2510.23903v1
- https://arxiv.org/html/2510.23903v1

Equation (1) supplies the prefix-inequality composition-polytope model.
Theorem 1.2 already proves gamma positivity for every composition. Section 2
encodes lattice points by support positions and increasing positive partial
sums. The uniform-block gamma path interpretation in the article agrees with
that subset encoding after identifying the four membership types. This result
and that encoding are credited rather than presented as independently new
discoveries; the article reproves the qualitative property for equal blocks
only as a consequence of its explicit gamma-generating identity.

## 4. Classical walk methods and singularity analysis

Frank Spitzer, “A combinatorial lemma and its application to probability
theory,” Transactions of the American Mathematical Society 82 (1956), 323–339.
DOI: https://doi.org/10.1090/S0002-9947-1956-0079851-X

Cyril Banderier and Philippe Flajolet, “Basic analytic combinatorics of directed
lattice paths,” Theoretical Computer Science 281 (2002), 37–80.
DOI: https://doi.org/10.1016/S0304-3975(02)00007-5
Publisher: https://www.sciencedirect.com/science/article/pii/S0304397502000075

Philippe Flajolet and Andrew Odlyzko, “Singularity analysis of generating
functions,” SIAM Journal on Discrete Mathematics 3(2) (1990), 216–240.
DOI: https://doi.org/10.1137/0403019
Publisher record: https://epubs.siam.org/doi/10.1137/0403019

These are background attribution for factorization/kernel methods and
algebraic-path singularity analysis. The exact formal factorization needed for
the main theorem is proved in the article in both the Laurent-polynomial and
the Laurent-series forms, so no inaccessible theorem from these papers is a
hidden prerequisite, and the main formal theorem does not depend on the
transfer theorem at all. Spitzer's bibliographic details were cross-checked
through records of the original paper and its references; the AMS endpoint
could not be fetched and the original full text was not retrieved. No
quotation from inaccessible text is used.

## 5. Adjacent recent literature consulted

Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak, and Hongyu Wang,
*Counting Lattice Points in Minkowski Sums of Cross Polytopes*,
arXiv:2608.16037v2 (2026).
https://arxiv.org/html/2608.16037v2

Discusses support enumeration, root-polytope h* realization, and preorder
support duality; its introduction specifically connects duality to
Conjecture 5.4 of the target paper. No proof of the exact multiple-chain
formula was located in the consulted text.

Xue Yan, *Variations of colored multiset Eulerian polynomials and applications*,
arXiv:2608.15682v2 (2026).
https://arxiv.org/html/2608.15682v2

Discusses colored multiset Eulerian polynomials and applications to
composition/preorder polytopes. No proof of the exact Section 9.5 formula
was located in the consulted text.

## 6. Own derivations and computation

Both proofs, the rectangular application, the endpoint refinement, the radical
product and quartic, the gamma derivations, the fixed-support theorem, the
mixed-size theorem, the moment argument, and the explicit
asymptotic/statistical derivations are written out in `article.tex`. The
finite tables in `results/` were generated from the included code. The
article does not claim that every displayed corollary is previously
unpublished. There is no Lean or other proof-assistant certification in this
package.

No third-party paper PDF, font file, or unrequested external data is included.

## 7. Interpretation of the audit

The target is an identifiable published conjectural identity. The article
provides a complete candidate resolution, not just supporting examples. An
unlocated prior proof remains possible, and independent checking of both
correctness and priority remains necessary before publication.
