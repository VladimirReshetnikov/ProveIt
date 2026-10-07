# Report277 sources

## Pinned mathematical interface

Repository: VladimirReshetnikov/ProveIt

Commit: c94998a5db18ba63c815a3bf6c3877a0fde91930

- Corollary 5.8 predicate, Section05.lean lines 242–259: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section05.lean#L242-L259
- Polynomial partition constant, Section05.lean lines 44–46: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section05.lean#L44-L46
- PolynomialOn, Definitions.lean lines 222–226: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean#L222-L226
- Modular progressions, properness, density, balanced function, and exponential: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean

### Exact bytes and the earlier provenance correction

The fingerprints below refer to the same pinned commit. Report275 recorded hashes for all four files; Report276 repeated the first two. Their previously recorded SHA-256 values were for newline-normalized retrieval copies, each containing exactly one additional trailing LF, rather than the exact repository file bytes. The corrected raw hashes were obtained from decoded GitHub file bytes and checked against the Git blob identities.

- Section05.lean (17,122 raw bytes)
  - Correct raw SHA-256: cede89413bd9e431e4018a7e18b5a3388d51755bb38b9a2add5b73ac2fa6b07a
  - Previously recorded SHA-256 of raw bytes plus one LF: 42ce4ee0c8b6080313fb03765aba4e5141a5e1ebf14eead5d8aadb99c6aafad2
  - Git blob SHA-1 of the raw bytes: 882b17a01d76825b9dfd9679f00a93d5c0bf214c

- Definitions.lean (15,504 raw bytes)
  - Correct raw SHA-256: 17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b
  - Previously recorded SHA-256 of raw bytes plus one LF: 7952261a1ad4d22e08cb28bd01a4acc360b578ca5b9fd0a4e1c05b9cde117ef6
  - Git blob SHA-1 of the raw bytes: 97113b7afa6925a2dd4b76641eeaeff09597ab6a

- Proofs05Corollary58.lean (14,076 raw bytes)
  - Correct raw SHA-256: 20d1b6fcaced2a77ee50fd8ba17c66c7406be48ec2bc5b93347a791d7b3a9d78
  - Previously recorded SHA-256 of raw bytes plus one LF: fa25d736ec83268a024c07b7cf1690915cbe1e8883bb7e2ad04a8aabfc1d090e
  - Git blob SHA-1 of the raw bytes: a29e971bbe8929a94214ae47a44835944c48985c

- FORMALIZATION_STATUS.txt (22,597 raw bytes)
  - Correct raw SHA-256: c6c35635d8a1bdf10a3787917d16dbd2a5171fded28a26c73925291550694951
  - Previously recorded SHA-256 of raw bytes plus one LF: 3d712f56e2fe496f9fd03fe8188a498628570843c4c7c897c0fd6c11486973d4
  - Git blob SHA-1 of the raw bytes: 611abcec0df12dd719408266ed19db5d43703c47

The first two files define this report's mathematical interface. The other two appear here solely to correct the earlier provenance record: [Proofs05Corollary58.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs05Corollary58.lean) and [FORMALIZATION_STATUS.txt](https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/FORMALIZATION_STATUS.txt). They are not additional mathematical dependencies of Report277. The byte difference is solely the added newline; the mathematical source text and conclusions are unchanged. Earlier released files have been preserved unchanged.

The constant is K_k=(k!)²2^((k+1)²). The source conclusion is length at least (N/M)^(1/K_k)/8 and gain α/16. Its coefficient-polynomial definition has k+1 ordinary coefficients; it is not an arbitrary finite-difference polynomial notion over composite moduli. Its properness definition is carrier cardinality equal to parameter length, so it permits wrapping without repeated points. Empty-parent and N=1 cases are vacuous under positive correlation and the other hypotheses.

Report277 proves the entire written k≥1 interface without adding scale, minimum-correlation, or prime-modulus assumptions. It reproves the quadratic base and retains sharper affine and quadratic alternatives. No earlier report, private review, or unbundled research note is a mathematical dependency of the self-contained article.

The target is a Prop-valued catalogue declaration. This source-interface comparison is not a Lean theorem, a repository-build result, or a change to formalization status. No repository file was edited for this report.

## Primary literature

1. W. T. Gowers, A new proof of Szemerédi's theorem, Geometric and Functional Analysis 11 (2001), 465–588. https://sites.math.rutgers.edu/~zeilberg/akherim/GowersMasterpiece.pdf
   - Section 5 develops Weyl recurrence, polynomial localization, and local density increments
   - Corollary 5.8 is on printed page 493, PDF page 29
   - Its displayed gain is α/8; the displayed proof ends with α/16, which is the gain used in the pinned edited source
2. James Maynard, Simultaneous small fractional parts of polynomials, arXiv:2011.12275v1, 24 November 2020. https://arxiv.org/pdf/2011.12275v1
   - Theorem 1.1 and Corollary 1.2, PDF page 2, give coefficient-uniform simultaneous recurrence for zero-constant-term real polynomials
   - The stated constants depend on degree and the number of polynomials; they are not used as explicit numerical constants here
   - Lemma 6.1 is the Weyl exponential-sum estimate in this arXiv version; numbering may differ in other versions

These are primary sources for the classical context. The article gives its own full proofs of the explicit single-monomial recurrence estimates and every numerical input used downstream. No literature-priority or optimality claim is established. No global Ramsey/Szemerédi improvement or ordinary-integer rectification is asserted. Third-party sources are linked, not bundled.
