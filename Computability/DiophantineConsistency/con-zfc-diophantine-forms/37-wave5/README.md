# Wave5: fourteen integer unknowns and smaller norms for Con(ZFC)

Review pin: `8c6eec9d19ef80538c8e61ff6e0180040583446a` of VladimirReshetnikov/ProveIt.

Start with `report.pdf` and its LaTeX source `report.tex`. The report compares wave4 packages24–30 and distinguishes variable count, domain, degree, arithmetic operations, coefficient size, and proof burden. The selected new families all use the **entire** source19/source30 compact943 coefficient tuple. The fourth port is shifted MF. No coefficient ports are spliced.

## Main constructions

- `signed/generated/signed14.json`: one polynomial over fourteen unrestricted integers. Its fixed base-scale constant is a bounded power-of-two recipe; it is not an additional unknown. This uses a new cofinal-base strengthening of the source completeness proof and a Pell-orbit restoration of j.
- `signed/generated/signed16.json`: lower-degree alternative over sixteen unrestricted integers, without the new base-scale constant. The fifteen-integer intermediate is included for the proof progression, not as a frontier winner.
- `nine/generated/nine_sharp_positive.json`: one polynomial in nine **strictly positive** integers. The natural-domain companion uses an explicit coordinate shift. These cannot be read over unrestricted integers.
- `positive/shift_half_product.json`: a new lower-degree product over twelve positive integers; other variants trade degree for arithmetic cost. The `short_plain` product is a cheaper evaluator for source30's existing fixed polynomial, not a different polynomial.
- `lowdegree/integer50_quartic.json`: one quartic over fifty unrestricted integers, from29 quadratic equations. It is much lower-degree than the14-variable equation.
- `lowdegree/integer24_ratio_product.json`: a cheaper moderate-degree alternative over24 unrestricted integers.

Each family includes complete ordinary mathematical proofs, explicit machine-readable polynomial data, generators, and finite checks. Full metrics are generated in its ledger/receipt and summarized in the PDF. Comparison source material is included separately and retains its original provenance and bindings.

## Reproduce

Run `python verify.py` from any working directory. Python3.10+, NumPy, and SymPy are needed; the requirements file records the version used. No network access or proof assistant is needed. The script checks the sealed source set, all four coefficient hashes and circuit bindings, copies the package into a temporary directory, rebuilds every new generated family, runs independent checks, and requires byte-identical generated artifacts. See `VERIFICATION.json` for the actual successful stages and regenerated file list. `negative_controls.py` tests deliberate corruption without altering the package.

Compile the PDF with `pdflatex report.tex` twice in a standard LaTeX installation. The PDF is included, so TeX is unnecessary to read or replay the arithmetic.

## Evidence boundary

These are mathematical arguments using the identified ordinary compiler, Jones ratio lemmas, and literal K215 calibration. The new finalizers and cofinal-base theorem have **not** been kernel-checked end to end. Modular checks, exact finite identities, coefficient materialization, and corruption tests supplement the universal arguments; they do not establish or decide Con(ZFC).

Four ordinary compiler coefficients and the Jones index z are materialized. The much larger y and the extra signed base-scale coefficient are specified exactly but not expanded. Arithmetic circuit counts treat those as fixed constants and are not bit-complexity bounds. No global minimum or universal-variable record is claimed. P67 remains the reviewed collection's lowest-operation single equation.

All new work is prepared for repository incorporation under its MIT-0 default. See `NOTICE.md`, `licenses/`, the source manifests, and the per-family proof notes for attribution. The archive preserves source snapshots required for replay; if repository intake omits duplicates or seals, replay from this complete archive rather than the incomplete placed subset.
