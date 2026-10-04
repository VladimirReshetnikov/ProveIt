# Bounded-counter compiler: two-witness linear-degree core

4 October 2026. A separate arithmetic packet; no report is renumbered or recounted.

## Main result

For each fixed deterministic two-counter program and horizon T, the positive inputs A,B represent counters A-1,B-1. `PROOF.md` gives one explicit integer polynomial with exactly two positive witnesses, five residual-square slots, and a unique witness pair for every accepted input.

- T>=1: exact degree max(2(T+1),4,2 deg F_S), bounded by 4T
- T=0: a separate five-slot definition has exact degree two
- The same fixed two-zero-test program attains degree 4T in this presentation for every by-horizon T>=2
- First-exactly-T semantics uses the same finite-table compiler; its fixed-program sharpness distinction is stated explicitly
- The accepted POWER12 composition has 28 positive witnesses, three external inputs, 31 variables, 17 square slots, and exact degree max(20,compiler degree)
- Decoded counters/outputs/compiler witnesses are unique; full composed witness fibers are infinite

All inputs and witnesses are ordinary positive integers. Expressions defining the clipped representatives are not extra variables. Full and empty tables and initially halted programs are covered.

## Separate one-witness alternative

`ONE_WITNESS.md` gives a product of cell-specific sums of squares with one unique positive native witness. For T>=1 its exact degree is 2n_I+4Tn_E+8Tn_C, at most 10T^2+8T.

The corresponding gap composition has 27 positive witnesses. The lower-degree form is 12 squares plus one nonnegative product-of-SOS block, not 13 residual squares. Squaring that block gives exactly 13 residual-square slots but doubles its degree contribution.

The appendix also proves the exact zero-versus-one native auxiliary-variable classification for a fixed finite clipping table, when no degree bound is imposed: zero variables suffice exactly when each accepted tail cell contains its entire coordinate-flat closure in the accepted table. Otherwise one positive variable is necessary and sufficient. A d-input generalization is included. This is a narrow finite-table statement, not an unbounded MRDP or global universal-polynomial claim.

## Honest cost comparison

The two-witness formula reduces degree and witness count but loses the predecessor's narrow expanded support. It has O(K^4) possible monomials and O(K^5 log K) expanded bits, compared with the prior three-witness O(K^2) monomial and O(K^4 log K) expanded-bit upper bounds, where K=T+1.

The one-witness alternative has O(K^6) collected monomials and O(K^8 log K) expanded bits. Its fully distributed SOS presentation can have 3^n_I 2^n_E slots. Both new factored circuits have O(K^2) integer-operation upper bounds, with encoded constants and table paid. These counts are not bit complexity and do not make finite-table generation free.

## Files and verification

- `PROOF.md`: two-witness theorem, costs, complete POWER composition
- `REVIEW_TWO_WITNESS.md`: separate static mathematical review, PASS; executed evidence and the one-witness appendix are outside that review's scope
- `ONE_WITNESS.md`: independently derived alternative, cost analysis, and restricted minimum-arity theorem
- `static_algebra.py`: freshly authored and inspected standard-library exact algebra
- `evidence/results.json`: completed finite checks and measured expansion counts
- `evidence/expanded_polynomials.json.gz`: selected complete coefficient lists, variable orders and residuals
- `SOURCE_PINS.json` and `dependencies/`: inert copies of accepted proofs/audits and their pinned Pell dependency
- `PRESERVATION.md`: the exact source-preservation boundary, including concurrent Report68 sealing
- `MANIFEST.sha256`: hashes of packet files other than the manifest itself

Completed fresh checks cover 285 interpolation-node identities; 42 two-witness expansions; 16,200 positive witness-box assignments; 18,432 canonical assignments across all K=3 tables; 24 one-witness expansions; 4,348 one-witness assignments; all 530 tables through K=3 against the zero-witness closure criterion; one complete base-two POWER expansion; ten two-witness gap compositions with 30 complete positive fixtures; five one-witness gap compositions in both presentations; and 30 d-input degree ledgers. The final receipt is authoritative for exact counts.

Only new static algebra, declared tables, and the explicitly declared exponent-zero POWER family are evaluated. No old checker, author/upstream science code, counter interpreter, physical simulator, schedule search, or Lean is executed. The mathematical proofs establish the infinite-domain claims; fixtures only corroborate them. The POWER composition remains conditional on the explicitly pinned accepted constructive Pell theorem pair.

The delivered packet is read-only. For a local replay while all pinned original source paths remain available, first make a writable copy, then run `python3 static_algebra.py` from that copy. It writes only the copied packet's evidence directory and reads pinned original files for integrity checks. It does not import or execute original code. The preservation inventories intentionally use absolute source paths and are not advertised as a source-free portable replay interface.

No claim of novelty, priority, minimum degree, smallest coefficients, global minimum arity, unbounded-horizon fixed polynomial, finite-fold POWER composition, or new physical dynamics is made.
