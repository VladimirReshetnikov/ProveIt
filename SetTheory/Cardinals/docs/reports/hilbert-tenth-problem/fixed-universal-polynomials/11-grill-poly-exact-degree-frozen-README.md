# Exact degree follow-up

**Result: the same frozen universal Grill polynomial has total degree 69,339,973.**

All six external coordinates and 797,135 witnesses have degree one. No source or Report 23 file was changed. The previous 71,731,007 bound was a valid, non-sharp syntactic upper bound.

Start with `DEGREE_PROOF.md`. The first native norm cancels identically; the rewritten leading coefficient survives. A new streamed checker and an independent symbolic/raw-source checker establish the exact degree.

Files:

- `DEGREE_PROOF.md`: complete all-tuple identity, degree proof, and nonzero leading form
- `check_degree.py`: standard-library-only streamed upper-bound and coefficient checker
- `degree_certificate.json`: normal replay, two deterministic nonzero coefficient residues
- `degree_certificate_optimized.json`: matching optimized-Python replay
- `check_degree.log`, `check_degree_optimized.log`: replay logs
- `independent-review/`: independently implemented raw/symbolic verification and mathematical audit
- `MANIFEST.json`: packet inventory and hashes

The exact highest coefficient on the diagonal ray where every coordinate equals t is

−2^148 (2^551891 · 794976)^23113311.

It is nonzero; the source-stream computation independently gives residue 3 modulo 17 and 53,942,795 modulo 1,000,000,007.

To replay, extract Report 23 and set SOURCE_DIR to its `reproducibility/frozen/arithmetic/` directory. It contains the three unchanged pinned input files. Then run:

python check_degree.py --source-dir SOURCE_DIR
python -O check_degree.py --source-dir SOURCE_DIR --output degree_certificate_optimized.json
python independent-review/check_leading.py --source-dir SOURCE_DIR --output independent_leading_result.json
python -O independent-review/check_leading.py --source-dir SOURCE_DIR --output independent_leading_result_optimized.json

The complete source is not duplicated into this small follow-up packet. Its SHA-256 is recorded in every certificate. These are ordinary total-degree claims about one fixed integer polynomial, not a circuit optimization, a minimum-degree claim, or a new universality proof.
