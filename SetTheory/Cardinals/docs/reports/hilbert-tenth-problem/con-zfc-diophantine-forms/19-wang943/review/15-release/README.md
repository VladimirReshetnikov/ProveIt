# Combined explicit Diophantine forms for Con(ZFC)

This release combines and audits the reviewed fixed-machine constructions. Read `report/combined_con_zfc.pdf` for the mathematical comparison and selected equations. The literal equation data, coefficient recipe, proofs, provenance and bounded checks are included separately.

## What is improved

- **14 positive variables:** a degree-293 polynomial using 75 binary arithmetic operations, or five equations using 69 operations, maximum degree 244.
- **15 positive variables, lower degree:** the ordinary-strong form has degree 99 in 69 operations; two positive-root gap substitutions give degree 83 in 71 operations. Their six-equation systems use 61/63 operations and have maximum degree 28/22.
- **Low degree:** 33 positive variables and 24 quadratics give a quartic sum of squares; 25 variables and 16 cubics give a sextic; 20 variables and 11 degree-at-most-four equations give an octic.
- **Unrestricted integers:** 32 variables, degree 584 and 138 operations; or 33 variables, degree 159 and 134 operations. The 33-variable, degree-304, 130-operation alternative is also included. The strongest included unrestricted-integer quartic has 60 variables and 33 quadratic equations.
- **Smaller fixed-coefficient recipe:** 439 underlying tiles, exactly 10,762,728,984,864 allowed windows after the row-head restriction, and B=2^(5^43). The giant coefficients are specified by bounded formulas, not expanded.

`final_forms.json` and `final_forms.csv` are the complete artifact-index and result table. “Degree” means polynomial degree, maximum residual degree for a system, or degree of the literal sum of squares for a low-degree packet. In a sum-of-squares row, “equations” counts its residual equations; the sum of their squares is one equation. The operation model counts binary +, − and ×, including squaring and multiplication by a fixed coefficient; equality comparisons and reuse are free. Coefficient heights are not part of this operation count. No global optimum is claimed.

## One unambiguous coefficient binding

`COEFFICIENT_BINDING.json` selects the whole four-port tuple from:

`evidence/diophantine_zfc_round2/compiler/raw_coefficients_specification.json`

The ports are Bm1=B−1, Kconstant=DC+B·DR, MC, and MF=MF_native+B−1. They are fixed integers, never existential variables. Use that complete tuple for the final forms in the table. Do not splice coefficients from different old packages. Historical parent packets retain their original descriptions and hashes; the explicit release binding and the transfer proofs specify the selected new instance. In particular, inherited “Input-ignoring machine” contract wording describes the earlier normalized-machine template, not raw K215. The selected new instance is the blank-initialized Start-only compiler of RAW_MACHINE_COEFFICIENTS.md; no arbitrary-input normalization is asserted.

## Portable bounded replay

Requirements: Python 3.10 or newer; only its standard library is used. No network connection, package installation, SymPy, Lean or Rocq is required. From any directory, run:

    python3 /path/to/this-release/run_checks.py

The driver verifies every manifest hash, all 46 current-review source pins, the selected older proof-source pins (including Git blob hashes), and the exact K215 transition-table hash. It then copies the release to a fresh temporary directory, runs only newly authored checks there, compares regenerated final artifacts and receipts, and checks that the original release is unchanged. It never imports or executes the pinned received Python scripts. No binaries or cache directories are shipped.

The replay covers exact symbolic residual identities, norm and shear identities, port closure and liveness, operation ledgers, low-degree eliminations, integer-domain substitutions, exact sparse formal-cut degree upper bounds and attaining integer/coefficient specializations, package-06/08 arithmetic identity, the 24/16/11 displayed report equations, finite machine/tableau checks, and the bounded coefficient layout. Local deterministic examples and line-specialization diagnostics are labelled as such; they do not establish semantic compiler correctness.

Some owned helpers use Python assertions. The driver and the assertion-using helpers reject `-O` and `PYTHONOPTIMIZE`; run with assertions enabled. The driver deliberately has no option to execute received scripts.

Optional independent exhaustive count, with a C++17 compiler supporting `__int128` (GCC or Clang):

    python3 run_checks.py --exhaustive

Use `--cxx /path/to/g++` to select a compiler. This compiles the newly authored counter into the temporary directory, exhaustively enumerates all 439 centers and their left/right pairs with exact multiplicities, and compares the entire result with the shipped receipt. It does not enumerate the enormous full nine-cell alphabet. Compilation uses no `-DNDEBUG`, so its assertions remain active. No precompiled executable is distributed.

Default replay uses the shipped exhaustive-count receipt and independently reproduces every one of the 439 center counts by closed Python formulas. The optional mode additionally repeats the exhaustive enumeration itself.

## Layout and audit trail

- `report/`: final PDF and its TeX sources.
- `evidence/diophantine_zfc_round2/review/`: 46 byte-pinned received reports, proofs, data and inert source scripts; comparison and independent gate-count receipts.
- `evidence/diophantine_zfc_round2/pell/`: final positive-variable circuits, two proof notes, owned regeneration/check programs and receipts.
- `evidence/diophantine_zfc_round2/quadratic/`: the three final low-degree packets and independent sparse audit.
- `evidence/diophantine_zfc_round2/integers/`: final unrestricted-integer packets, parent JSON, signed-domain proof and independent audit. Optional research emitters are not needed and are not shipped.
- `evidence/diophantine_zfc_round2/compiler/`: the new bounded coefficient specification, mathematical proof, owned Python/C++ checks and exact receipts.
- `evidence/diophantine_zfc_round2/audit/` and `root/`: independent mathematical and coefficient reviews.
- `evidence/diophantine_zfc_review/`, `diophantine_zfc_encoding/`, `diophantine_zfc_compiler/`: necessary prior parent packets, source proofs and literal K215 table.
- `checks/check_final_forms.py`, `FINAL_CHECKS.json`: final-table cross-check and exact degree certificates.
- `MANIFEST.json`: release-relative paths, byte sizes and SHA-256 values, excluding only the manifest itself.
- `DEPENDENCIES.md`, `NOTICE.md`, `licenses/`: proof-scope limitations and retained source credit/licensing.

## Logical and verification scope

The claim is an ordinary mathematical construction, formalizable in ZFC, whose solvability is equivalent to a finite ZFC refutation and whose lack of solutions is therefore equivalent to Con(ZFC). It depends on the authentic K215 calibration and native/Pell compiler proofs. This is not a new end-to-end proof-assistant-checked theorem or an explicit encoded ZFC derivation. The bounded checks cannot prove Con(ZFC), find a refutation, or decide the equation's solvability.

Positive, nonnegative and unrestricted-integer domains are distinct. The positive-variable equations must not be silently interpreted over all integers. Use the supplied integer conversion and its proof for unrestricted integer witnesses. Positive-to-nonnegative conversion is the coordinate shift x=n+1; it preserves the number of variables and degree.

## Rebuild the report

With a standard TeX Live installation, run `pdflatex -no-shell-escape combined_con_zfc.tex` twice from `report/` to resolve cross-references. The optional `bash build_report.sh` records the Debian-specific build recipe used for this PDF; it has no project-workspace path dependency. The PDF is provided so no TeX installation is needed for reading or for the mathematical bounded replay. Rebuilding in place changes the release and therefore invalidates its frozen manifest; use a separate copy.

Degree audit qualification: an attaining specialization of the four formal coefficient ports proves a lower bound for the symbolic parameter family, not by itself for every numerical coefficient tuple. Uniform exact-degree claims for the authentic compiler tuple are supplied by the accompanying leading-term mathematical proofs. The low-degree sparse checks additionally record coefficient-independent leading monomials.
