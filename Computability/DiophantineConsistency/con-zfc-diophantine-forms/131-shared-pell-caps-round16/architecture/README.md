# Fused factorial product with shared Pell index cap

Two recommended natural-domain endpoints are included:

- unified_cap_h12: 249 variables, 186 quadratic residuals, 27,078 quartic monomials, coefficient height 85,178,741.
- unified_cap_sparse_h12: 278 variables, 215 quadratic residuals, 5,524 quartic monomials, coefficient height 83,852,788.

Both are ordinary integer polynomials on nonnegative variables. Each polynomial
is the sum of the squares of the full listed residuals. The principal endpoint
minimizes variables among these measured variants; the sparse endpoint trades
29 variables for much lower density. No global minimality claim is made.

The incoming shared-cap principal was 261 variables, 194 rows, 31,679 monomials
and height 85,566,955. Its sparse companion was 292 variables, 225 rows, 6,140
monomials and height 83,933,334. The two corresponding composed endpoints here
strictly improve all four respective finite measures.

UNIFIED_CAP_PROOF.md gives the arithmetic composition and retained logical
scope. The new composition uses round15's single square-radius factorial/CRT
binomial, the incoming shared-index cap, K=R, and q=(NH)^K with H equal to one
plus the sum of the nine independent representatives. It does not need the
aggregate representative bound, and the radix base does not contain the
factorial numerator. The horizon-12 extension is proved explicitly.

## Rebuild and verification

From the repository root, run:

    python diophantine_zfc_round16/architecture/build_unified_cap.py --output DEST --horizon-minimum 12
    python diophantine_zfc_round16/architecture/build_unified_cap.py --output DEST_SPARSE --horizon-minimum 12 --sparse

The builder first uses the byte-pinned source in portable/source. A sibling
intake fallback is retained for development only. It never modifies imported
source, and the delivered architecture directory is runtime-self-contained. build_unified_cap.py and the loaded executable
closure recorded in REPRODUCTION.json determine the exact generated endpoint.

    python diophantine_zfc_round16/architecture/check_unified_cap.py DEST DEST_SPARSE --output CHECK.json

The checker imports no producer. It verifies the literal fused arithmetic and
self-radix, every cap constraint, seed positivity and exact index additions,
then independently expands every quadratic residual square and compares the
complete polynomial. Existing projection receipts separately check every
natural-domain elimination and restoration.

    python diophantine_zfc_round16/architecture/reproduce_unified_cap.py --output REPRODUCTION.json

This rebuilds both recommended endpoints in temporary subdirectories and
checks every emitted JSON byte against the saved reference. Repeat under
python -O to verify the optimized interpreter path. Saved normal/optimized
checks and reproductions are included. Finite tests supplement the unbounded
proof and do not replace the retained C222/ZFC calibration.

Other measured radix variants and the horizon-16 version remain as development
comparisons. They are not needed for the two recommended endpoints.
