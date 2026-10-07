# Report275 sources

## Pinned mathematical interface

Repository: VladimirReshetnikov/ProveIt

Commit: c94998a5db18ba63c815a3bf6c3877a0fde91930

- Corollary 5.8, Section05.lean lines 242–259: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section05.lean#L242-L259
- PolynomialOn and properness definitions: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean#L222-L226
- Scale-qualified repair: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs05Corollary58.lean
- Section 16 geometry qualifications: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/FORMALIZATION_STATUS.txt

The comparison uses the corrected repository gain α/16, rather than the original paper's printed α/8. The degree-one partition constant is 16. PolynomialOn 1 expands literally into the two coefficients c0+c1x. The all-modulus degree-one result in this report is a written theorem; it has not been added to Lean or used to change the repository's formal status. Reported source status is not a build rerun.

## Primary literature and method context

1. W. T. Gowers, A new proof of Szemerédi's theorem, Geometric and Functional Analysis 11 (2001), 465–588. https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
   - Corollary 5.8: printed page 493, PDF page 29
   - Lemma 5.4: Dirichlet input
   - Lemma 5.12: one-axis square-root modular-to-integer decomposition
   - Lemma 5.13: the whole-partition consequence
2. Yufei Zhao, Graph Theory and Additive Combinatorics: Exploring Structure and Randomness, Cambridge University Press, 2023. Author version last updated 18 June 2024: https://yufeizhao.com/gtacbook/gtacbook.pdf#page=235
   - Lemmas 6.4.5 and 6.4.6, printed pages 219–220, PDF pages 235–236
   - Classical cube-root phase partitions and a density increment, with explicit scale conditions
3. Mark Lewko, A Fourier-Free Density-Increment Proof of Roth's Theorem, arXiv:2605.19310v1, 19 May 2026: https://arxiv.org/html/2605.19310v1
   - Section 5: moments of progression sums
   - Section 6: passage to an ordinary integer progression

These sources are cited for context and exact interface comparison, not as substitutes for any proof in the article. The cube-root scale and the individual localization/moment mechanisms have precedents. Literature priority for the exact threshold-free local-cover formulation is unverified. No new global Roth, Ramsey or Szemerédi bound is asserted.

## Reproducible source fingerprints

The files inspected for the repository comparison can be independently obtained at the exact commit above. Their SHA-256 fingerprints are recorded below. They are provenance data, not a claim that a repository build was rerun.

- Section05.lean: 42ce4ee0c8b6080313fb03765aba4e5141a5e1ebf14eead5d8aadb99c6aafad2

- Definitions.lean: 7952261a1ad4d22e08cb28bd01a4acc360b578ca5b9fd0a4e1c05b9cde117ef6

- Proofs05Corollary58.lean: fa25d736ec83268a024c07b7cf1690915cbe1e8883bb7e2ad04a8aabfc1d090e

- FORMALIZATION_STATUS.txt: 3d712f56e2fe496f9fd03fe8188a498628570843c4c7c897c0fd6c11486973d4
