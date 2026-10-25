# Cofinal anchors and height one equations for ZFC consistency

Round 17 research contribution prepared with AI assistance for Vladimir Reshetnikov and the ProveIt repository, 25 October 2026.

## Achieved results

- Natural quartics: 229 variables / 179 residuals / 9184 terms / height 83954634; sparse 230 / 180 / 6858 / 83954472. A 228 / 178 / 9866 / 2445412949744 companion explicitly pays much greater height for one fewer variable.
- Unrestricted-integer direct quartics: 282 / 192 / 5491 / 128446; grouped 287 / 197 / 4313 / 128446; sparse 309 / 219 / 3922 / 128446.
- Height-one unrestricted-integer quartics: 793 variables / 51982 terms, 806 / 23719, and 994 / 11744. Every nonzero coefficient is ±1, and the constant is 1. These optimize height, not dimension relative to the direct family.
- Eleven-integer arithmetic graphs: exact degree/live-binary-operation pairs 328/130, 340/129, 352/125 and 398/121, using a complete authentic six-port numerical tuple.

The statements are ordinary mathematical equivalences with finite syntactic ZFC refutation, relative to the explicitly retained numerical C222 or source34/native/compiler/refutation calibrations. They imply the stated ZFC-provable equivalence between unsolvability and Con(ZFC), not a proof of consistency. This archive supplies no new end-to-end Lean, Rocq or encoded object-ZFC endpoint, no global minimality theorem, and no literature-wide priority claim.

## Start here

- The root PDF is the full research report. Editable source is report/main.tex and its included TeX files.
- ENDPOINTS.json gives every selected literal polynomial/graph path, domain, exact counts and hashes.
- CLOSURE_MAP.md separates new proofs, inherited arithmetic dependencies and the logical calibration boundary.
- VERIFY_PLAN.json and verify.py expose the entire finite replay, not a hidden external service.

## Offline verification

Run from any location with Python 3.10 or later:

    python3 /path/to/this/archive/verify.py

The default runs both ordinary and optimized Python. To save the resulting receipt:

    python3 verify.py --report REPLAY.json

Individual modes are available through --mode normal and --mode optimized. The mathematical checks need only the Python standard library. No network, parent repository, prior archive, private helper or absolute workspace dependency is needed. Each mode receives an independent disposable copy. The reference artifacts are never mutated by projection checkers. Deterministic reconstruction is compared byte for byte, and independent scripts check complete coefficients, exact transformations, numerical recipes and deliberate corruption cases.

A successful replay verifies finite algebra and artifact binding. It is not a replacement for the unbounded ordinary proofs or inherited logical calibration.

## Rebuild the report

With a normal TeX installation:

    sh build_report.sh

The script runs three passes and copies the PDF to the root descriptive filename. The shipped PDF was visually inspected page by page and compared by pixel identity with a fresh three-pass build. It was copied into the release ZIP without recompilation afterward. TeX build logs and page PNGs are intentionally not shipped.

## Formats and completeness

For a residual or polynomial, a JSON term [c,[i,j,...]] denotes c*x_i*x_j*... in the ordered zero-based coordinate list of equation.json (or polynomial.json for height one); [] denotes the constant monomial. Repeated indices denote powers. An expanded SOS polynomial records the variable count, while its adjacent equation.json records the ordered names. Direct and natural equations are exactly sums of the listed residual squares, with their fully collected coefficient files also supplied. Height-one polynomials are supplied both as full coefficient JSON and literal text, with exact graph certificates. Scalar JSON is a complete acyclic graph using only literal constants, fixed numerical ports, variables, addition, subtraction and multiplication.

MANIFEST_SHA256.json enumerates every release file except itself and the two explicitly named top-level replay receipts REPLAY.json and ISOLATED_REPLAY.json. Its exact-inventory check rejects undeclared files. There are no ancestor ZIPs or PDFs and no exploratory sweep outputs. Original imported source notices and licenses are retained.

## Comparison pin

https://github.com/VladimirReshetnikov/ProveIt/tree/1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61

The public comparison pin is distinct from older coefficient/calibration pins. Incoming placement is not mathematical acceptance. See review/ARCHIVE_AUTHENTICATION.json and the report for scope and provenance.
