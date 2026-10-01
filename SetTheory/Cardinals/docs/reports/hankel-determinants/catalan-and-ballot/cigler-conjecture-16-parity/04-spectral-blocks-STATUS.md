# Research status and trust boundary

## Claims proved in the article

1. Existence and uniqueness of polynomial spectral blocks `C_{K,q}(n,t)` for
   every shift `K >= 1` and sector `0 <= q < K`.
2. Integer-valuedness in the width variable and polynomiality in `t`.
3. Exact bidegrees
   `deg_t C_{K,q} = q(K-1-q)` and
   `deg_n C_{K,q} = floor(q(K-1-q)/2)`.
4. Explicit nonzero leading coefficients in the width variable, separately for
   even and odd sectors.
5. Corrected reciprocal symmetry, with sign negative exactly for shifts
   divisible by four.
6. A direct counterexample to the sign printed in Cigler's equation (83), at
   `K=5`, `q=2`.

## Proof dependencies

The argument starts from the rectangular-Schur identity and unique spectral
sector decomposition already proved in the ProveIt report cited in
`SOURCES.md`. The new proof uses finite confluent bialternants, grouped Laplace
expansion, weighted assignment bounds, a derivative-jet collision lemma,
finite differences, and Schur complement reciprocity.

## Verification performed

The shipped exact verifier records:

- 36 polynomial-bidegree checks for `1 <= K <= 8`;
- 36 corrected-reciprocity checks;
- 36 leading-coefficient checks;
- 40 reconstructions at widths not used for interpolation;
- 216 integer-coefficient checks at integral widths;
- 36 independent original-Hankel/Schur bridge checks for `K <= 6`, `n <= 5`;
- the explicit nonzero residual produced by the printed sign at `K=5`, `q=2`.

The recorded run used Python 3.13.5 and SymPy 1.14.0.

## Limitations

- This is an AI-assisted mathematical research draft.
- It has not been independently refereed.
- It has not been checked in Lean, Rocq, or another proof assistant.
- The finite verifier is supporting evidence, not a proof of the all-index
  statements.
- Historical priority beyond the cited literature has not been exhaustively
  investigated.
