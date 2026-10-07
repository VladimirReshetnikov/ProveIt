# Report276 sources

## Pinned mathematical interface

Repository: VladimirReshetnikov/ProveIt

Commit: c94998a5db18ba63c815a3bf6c3877a0fde91930

- Corollary 5.8 predicate, Section05.lean lines 242–259: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section05.lean#L242-L259
- Polynomial partition constant, Section05.lean lines 44–46: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section05.lean#L44-L46
- PolynomialOn, Definitions.lean lines 222–226: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean#L222-L226
- Modular progression, properness, density, balanced function, and exponential definitions: https://github.com/VladimirReshetnikov/ProveIt/blob/c94998a5db18ba63c815a3bf6c3877a0fde91930/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean

Source-file SHA-256 fingerprints:

- Section05.lean: 42ce4ee0c8b6080313fb03765aba4e5141a5e1ebf14eead5d8aadb99c6aafad2
- Definitions.lean: 7952261a1ad4d22e08cb28bd01a4acc360b578ca5b9fd0a4e1c05b9cde117ef6

The degree-two constant is K=(2!)²2^9=2048. The source conclusion is length at least (N/M)^(1/2048)/8 and gain α/16. Its coefficient-polynomial definition has exactly three terms. Its properness definition is carrier cardinality equal to parameter length, so it permits modular wrapping without repetition. Empty-parent and N=1 cases are vacuous under the source's positive-correlation premise and other hypotheses. The article proves the entire k=2 implication without adding scale or prime-modulus assumptions.

This is a written source-interface comparison. It is not a Lean proof, a repository-build result, or a change to formalization status.

## Primary literature

1. W. T. Gowers, A new proof of Szemerédi's theorem, Geometric and Functional Analysis 11 (2001), 465–588. https://sites.math.rutgers.edu/~zeilberg/akherim/GowersMasterpiece.pdf
   - Section 5, especially Lemmas 5.3–5.5 and Corollaries 5.6–5.8
   - Corollary 5.8: printed page 493, PDF page 29
   - The original displayed gain α/8 differs from the pinned edited repository's α/16
2. Ben Green and Terence Tao, New bounds for Szemerédi's theorem, II: A new bound for r4(N), arXiv:math/0610604v2, 4 January 2024. https://arxiv.org/pdf/math/0610604v2
   - Section 6: linearization
   - Appendix A, Proposition A.2, PDF page 18: simultaneous quadratic recurrence uniform in real coefficients
   - The following paragraph discusses Schmidt's asymptotically stronger exponent and dependence of implicit constants on dimension
3. James Maynard, Simultaneous small fractional parts of polynomials, arXiv:2011.12275v1, 24 November 2020. https://arxiv.org/pdf/2011.12275v1
   - Theorem 1.1 and Corollary 1.2, PDF page 2
   - Coefficient-uniform simultaneous recurrence for arbitrary systems of zero-constant-term real polynomials, with exponent proportional to the inverse number of polynomials and constants dependent on degree

These primary works establish the classical context of recurrence and localization. Report276 gives its own full elementary proof of the numerical recurrence used in the article, rather than treating an implicit asymptotic constant as its explicit constant 1024. It claims neither a best recurrence exponent nor literature priority for the precise local-cover formulation. No higher-degree or global Ramsey/Szemerédi bound is asserted. Third-party sources are linked, not bundled.
