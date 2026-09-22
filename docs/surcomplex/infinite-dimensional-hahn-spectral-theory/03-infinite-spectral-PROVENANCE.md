# Provenance and research scope

Date: September 22, 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `a3124af79f66b8b9c196d76b4cbc5ac3938907c4`

Commit timestamp returned by GitHub: 2026-09-22T15:58:14Z.

The comparison used the documentation catalogue and the spectral-theory
README at that commit. The differential-equations and spectral-theory
inventories were also examined to avoid repeating finite-dimensional work.
The pinned spectral-theory scope explicitly restricts dimensions to ordinary
finite integers. This is a targeted scope comparison, not a line-by-line audit
of every theorem in the repository. Initially returned unpinned documentation
was older; the article's provenance is based on the pinned snapshot above.

## Primary sources consulted

1. H. Gonshor, *An Introduction to the Theory of Surreal Numbers*, Cambridge
   University Press, 1986. Publisher record for foundational normal forms.
2. B. H. Neumann, "On ordered division rings," Transactions AMS 66 (1949),
   202–252. DOI: 10.1090/S0002-9947-1949-0032593-5.
3. G. Higman, "Ordering by divisibility in abstract algebras," Proceedings LMS,
   series 3, 2 (1952), 326–336. DOI: 10.1112/plms/s3-2.1.326.
4. A. Greenbaum, R.-c. Li, M. L. Overton, "First-order Perturbation Theory for
   Eigenvalues and Eigenvectors," arXiv:1903.00785. Abstract and full HTML.
5. M. Kenmoe, M. Smerlak, A. Zadorin, "Dynamical perturbation theory for
   eigenvalue problems," arXiv:2002.12872. Abstract and full HTML.
6. P.-L. Giscard, S. J. Thwaite, D. Jaksch, "Evaluating Matrix Functions by
   Resummations on Graphs: the Method of Path-Sums," arXiv:1112.1588.
7. P. Ara, K. Goodearl, K. C. O'Meara, "Positive definite matrices and
   involutions: the manners of their infinite cousins," arXiv:2607.25134v1,
   July 27, 2026. Full HTML; particularly the operator-category distinctions
   and failures of general infinite-dimensional spectral assertions.

The source list and comparison do not certify the absence of all prior
versions of the new package. The elementary perturbation coefficients,
formal recursion mechanism, Neumann support lemma, Higman word lemma,
walk interpretation of products, and the broad phenomenon of positive
infinite matrices with no eigenvectors are not claimed as discoveries.

## Candidate contribution

The article's candidate-original contribution is the global arbitrary-rank
Hahn operator/module synthesis: unique normalized infinite diagonalization
with support control, all coherent resolvents, a complete commuting
projection calculus, marked-walk stability, and sharp finite-section error
thresholds, under simple ordinary residues and positive global support.

The explicit accumulating-level closed-form eigenpair is proved directly and
used as an independent check; no separate priority claim is made for that
solvable model.

## Verification

The executable code tests finite jets in exact rational/Gaussian rational
arithmetic. Its 218 checks do not formalize the support theorem, prove an
infinite claim by themselves, or certify novelty. The article supplies the
infinite arguments separately.

The PDF was compiled with pdflatex/latexmk and rendered for visual review.
The delivered directory intentionally excludes temporary TeX and rendering
files.
