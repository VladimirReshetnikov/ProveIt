# Source and proof audit

## Primary research sources

### Elliot Glazer and Bokai Yao, Reflection Principles in ZFU

- Version: arXiv:2602.21970v1, 25 February 2026.
- Abstract: https://arxiv.org/abs/2602.21970v1
- Full text inspected: https://arxiv.org/html/2602.21970v1
- Relevant locations: Section 1.1 (kernel, pure sets, urelement axioms and the
  common-atom-base criterion for Collection); Section 3.1 (small-kernel
  permutation constructions and symmetry arguments).
- Role here: identifies a direct intersection with Glazer's published research;
  supplies the modern research context, not the exact classification claimed
  in this manuscript.
- Important distinction: that paper's reflection/Collection separations are
  already established there. The present article does not present them as open
  or claim to have solved them.

### Joel David Hamkins and Bokai Yao, Reflection in second-order set theory with abundant urelements bi-interprets a supercompact cardinal

- Version: arXiv:2204.09766v2, 5 December 2022.
- Published: Journal of Symbolic Logic 89 (2024), 1007–1043.
- Abstract: https://arxiv.org/abs/2204.09766v2
- Full text inspected: https://arxiv.org/html/2204.09766v2
- Relevant location: “Consequences of nonrigidity for urelement set theory.”
- Role here: explicit attribution of the classical finite-actual-kernel model
  and its Replacement-without-Collection property; the authors credit the
  Replacement argument to Lévy.
- The basic model and homogeneity technique are not claimed as new.

### Elliot Glazer, Global choice is not conservative over local choice for Zermelo set theory

- arXiv:2312.11902, 2023.
- https://arxiv.org/abs/2312.11902
- Role here: supporting evidence of Glazer's interest in weak foundational
  theories and sensitivity to the available language/choice principles. No
  theorem from this paper is used in the proofs.

### Harry Gonshor, An Introduction to the Theory of Surreal Numbers

- Cambridge University Press, 1986; LMS Lecture Note Series 110.
- DOI: https://doi.org/10.1017/CBO9780511629143
- Publisher record checked:
  https://www.cambridge.org/core/books/an-introduction-to-the-theory-of-surreal-numbers/312AE504A3E88E804054BFB390446374
- Role here: classical sign-sequence presentation and simplicity theorem.
- The new set-theoretic classification does not depend on advanced surreal
  arithmetic, differential constructions, or any unrefereed surreal conjecture.

## Repository source

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Pinned commit: 8dc2592e951b3402951060a15b61d65162aadc0f
- Pinned inspected document:
  https://github.com/VladimirReshetnikov/ProveIt/blob/8dc2592e951b3402951060a15b61d65162aadc0f/Algebra/SurrealNumbers/README.md
- Document blob: 18478d58670c384953fb85dcd1a6d931c644aa32
- Relevant content: sign-sequence construction of surreal numbers and the
  explicit distinction between formalized results and AI-assisted research
  reports. The root repository README was also consulted for orientation.
- Boundary: no full source audit or repository build was performed, and no new
  formal theorem is represented as already checked by the repository.

## Prior project manuscript

“Surreal Cuts, Replacement, and Atom-Support Spectra,” prepared for Vladimir
Reshetnikov with ChatGPT, 3 October 2026, was retrieved from the user's Library.
Its abstract, principal-results statements, and attribution discussion were
consulted to avoid duplicating its small-kernel and named-enumeration results.
The present note instead classifies named group actions and proves the strict
bounded-output-kernel hierarchy. No result from the prior working note is an
assumption of the new proofs. No copy of that prior file is included here.

## New proof chain

1. Unique definable outputs have kernels invariant under parameter stabilizers.
2. A common finite atom reservoir puts the ambient range in the finite-kernel
   universe.
3. Equivariant maps of a transitive finite action are determined by one point.
4. A type with m copies and d local equivariant automorphisms has centralizer
   atom orbits of size m*d (when m is finite).
5. Pure codes for all labeled finite transitive actions define total selectors
   for finite type strata and small pointed orbits.
6. These selectors give necessity; the finite reservoir gives sufficiency.
7. The bounded-kernel proof includes all finitely repeated strata touched by
   parameter atoms. Omitting this term would leave a gap.
8. Repeated odd dihedral components realize every prescribed finite threshold
   with only two named involutions.
9. Pure-valued Collection follows separately by ambient rank bounding.
10. The surreal corollary uses identical pure universes and classical simplicity.

## Validation performed

- `verify_orbit_spectra.py` ran successfully: 203 finite checks.
- 35 cases independently compared the component-isomorphism algorithm against
  brute-force enumeration of all permutations of domains with at most 7 points.
- Even cycle lengths were tested as negative controls for odd-dihedral rigidity.
- The PDF was compiled with LaTeX and rendered for visual inspection.
- These steps are not Lean/Rocq verification and do not establish historical
  novelty. Independent proof review remains appropriate.
