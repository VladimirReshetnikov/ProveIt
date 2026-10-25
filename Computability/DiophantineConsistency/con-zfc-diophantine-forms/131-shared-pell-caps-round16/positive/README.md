# One square for three Pell conditions

The new recommended ten-positive tradeoffs are:

- equations/single_square.json: 87 binary operations, exact degree 436.
- equations/single_square_lean.json: 88 binary operations, exact degree 380.

These improve operation count, not degree, against the preserved 89/288
uncentered construction. The direct-coordinate 92/384 and 93/334 variants
are complete controls, not recommended frontier points; existing positive
constructions dominate them.

PROOF.md supplies the complete literal polynomial specification, the new
unbounded coprimality/root-recovery proof, both directions of positive-zero
existence, exact global leading forms and the inherited calibration boundary.
The additional strong-period divisor A(1+Delta*c^2) makes the first, strong
and auxiliary square conditions recoverable from one square equation.
The already computed V^2 supplies the least-operation transport majorant.

All ten variables are strictly positive. The fixed coefficients are the
whole compact44 BFS tuple, supplied as little-endian gzip-compressed integer
payloads together with their finite reconstruction recipe. They are fixed
before the variables. They are not the public indexed tuple, and no ports
are mixed. Parent and calibration proof sources are retained in provenance/;
SOURCE_PINS.json authenticates their unchanged bytes and keeps historical
source pins separate from the current comparison pin.

From this directory, with standard-library Python 3 only:

    python -B build.py --check
    python -B verify.py
    python -B -O verify.py --output CHECK_OPTIMIZED.json

The builder reads JSON as data and never executes inherited code. The
verifier independently evaluates the literal specification, checks all live
dependencies and coefficient bytes, and compares exact polynomial rays and
their complete highest homogeneous forms. Finite checks support the
unbounded proofs; they do not prove absence of zeros.

No new globally simplest equation, consistency proof, Lean theorem or
internal object-ZFC derivation is claimed. The ordinary arithmetic reduction
composes with the specified inherited native/controller/refutation theorem.
