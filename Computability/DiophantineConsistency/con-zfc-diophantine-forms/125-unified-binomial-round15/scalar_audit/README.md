# Independent scalar audit

Status: PASS for the selected eleven-unrestricted-integer pair, exact degree 464 / 119 operations and degree 488 / 118 operations. The proof/calibration boundary is stated in `SEMANTIC_AUDIT.md`.

Run from any working directory:

    python independent_audit.py
    python -O independent_audit.py --out AUDIT_RESULTS_OPTIMIZED.json
    python check_interpolation.py
    python -O check_interpolation.py

The independent graph checker uses Python and SymPy and imports no producer executable. By default it reads the sibling `../norm/` graph files and authenticated payloads; `--norm-dir` can select a relocated graph directory. It checks both selected paired graphs, their symmetric siblings, and the cancellation-explicit comparison graph. Its source-register and complete 35-term norm identities prove the same polynomial, not just agreement at sample points. Its exact finite-field univariate degree lower witness is combined with a universal upper-bound certificate. Full symbolic attained coefficients are also independently reviewed in the semantic audit and retained producer proof.

`check_interpolation.py` uses only the Python standard library. Its 1,720 lifting checks and five complete fixed-pair residue permutations are supplemental finite controls, not the proof of the unbounded interpolation theorem.

`REVIEW_BINDINGS.json` identifies the actual proof/source/graph files reviewed. `AUDIT_RESULTS.json` and its optimized companion record full payload pins and graph hashes. `MANIFEST_SHA256.json` binds the auditor's own files, excluding the manifest itself.

## Bounded split-carrier extension

The separate weak-Y extension also passes: eleven unrestricted integers, exact degree 416 / 125 operations centered, and 456 / 124 operations direct. Its proof ordering is reviewed in `CRT_CARRIER_AUDIT.md`. Run `python audit_crt_graphs.py` and `python -O audit_crt_graphs.py --out CRT_AUDIT_RESULTS_OPTIMIZED.json` for independent literal checks. It reads the sibling `../norm_weak/` directory and does not alter or supersede the frozen baseline.
