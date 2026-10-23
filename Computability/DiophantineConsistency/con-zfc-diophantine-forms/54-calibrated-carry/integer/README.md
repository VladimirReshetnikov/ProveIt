# Ten unrestricted integers: equal residual weights

All constructions use the ten unrestricted integer unknowns
`f,g,h,k,l,w,x,y,z,m`, with no additional witnesses, division or variable
exponents. Ordinary mathematics formalizable in ZFC proves that each
listed polynomial has an integer zero exactly when ZFC is inconsistent.
The inherited native compiler and Sun representation are identified
mathematical dependencies, not newly formalized here.

## Recommended artifacts

- Balanced: `generated/sun10_170_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json`.
  554 live binary operations (347 multiplications, 149 additions, 58 subtractions),
  exact total degree 14,699,152.
- Minimum live operations in this search:
  `generated/sun10_174_selective12_regular_homogeneous_sparse_popcount_equal.json`.
  513 operations, exact total degree 25,838,224.
- Slightly lower degree:
  `generated/sun10_170_selective12_packed_hybrid_sparse_popcount_equal.json`.
  558 operations, exact total degree 14,696,016.

The balanced prior-round comparator was 637 operations and degree 34,378,296.
The prior-round operation minimum was 582 operations and degree 50,822,936.
These are circuit complexity comparisons under the same binary +,-,* model,
not claims of globally minimal equations.

## What changed

1. The source worker proves that only twelve of the old positive source's
   31 coordinates need shifting. This reduces source records from 136 to 109.
2. The eighth incoming archive supplies one-bit target padding with signed
   borrows, plus a threshold calibrated to the mask's exact popcount.
   `SPARSE_SOURCE_PROOF.md` independently adapts these ideas to interior
   padding and the new support certificates.
3. New here: the source-conditional norm weights are `(1,b,b)`, not the
   prior `(1,r0,r0(Pn^2+K^2+3))` or incoming `(1,b,bK)`. The full proof in
   `CONDITIONAL_SEPARATOR_PROOF.md` recovers r0 first, then derives the strict
   inequality r2>r1 from Delta>0 before assuming either remaining square.
4. Exact parent homogenization, selective sparse fallback, and four further
   tail factorizations shorten the live evaluation circuit.

The source beta is exactly `2^864026`. The Yscale fixed leaf is
`2^13824395`. Full fixed integers are materialized as signed little-endian
magnitudes in `fixed/`, with compressed and uncompressed SHA-256 hashes.
The native four-port tuple is bound separately in `../native/`.

## Independent verification

Run from the bundle root:

    python integer/build_integer.py
    python integer/verify_integer.py
    python integer/check_local_lemmas.py

The scripts are independently authored for this task and do not execute
incoming upstream scripts. The verifier does not import the builder. It
checks fixed coefficient bytes and recipes, exactly expands D over four
symbolic native ports, replays the literal source and tail at 39 modular
assignments per circuit, checks live counts, and certifies exact degree
using nonzero leading diagonal coefficients at three primes.

For the balanced polynomial the top coefficient modulo 1,000,000,007 is
982,070,748. The finite checks also cover 2,793 popcount instances,
476 signed-borrow transitions, 4,752 positive-Delta bootstrap cases, and
38,016 strict radical-separation cases. Negative controls show why the
conditional hypothesis for equal weights matters and why the range
condition is needed for the exact popcount identity. These finite tests
support, but do not replace, the universal mathematical proofs.

`VERIFICATION.json`, `LOCAL_LEMMA_CHECKS.json`, `METRICS.json`, and
`RECOMMENDED.json` are the machine-readable results. Parent-level
independent reviews are in `../review/LOCAL_ADAPTER_PROOF_REVIEW.md` and
`../review/NEW_LOCAL_ADAPTER_CHECKS.json`.
