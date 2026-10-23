# Degree-separated ten-integer consistency equation

A fixed polynomial in ten unrestricted integer unknowns, exact degree **8,469,528**, with a **533-operation** division-free circuit. Its lack of integer solutions is equivalent in ZFC to Con(ZFC), with the explicitly stated inherited machine/compiler and Sun arithmetic dependencies.

The new source architecture uses separate quadratic, linear, and constant kernels instead of a dummy-coordinate homogenization. Only monomials of the same degree can interfere. Two elementary row operations reduce the source to 89 records; one shared word shift enforces positive witnesses. The source then combines with sparse borrow-tolerant target padding and the actual-mask-population binomial threshold.

Against the previous 659-operation, 21,111,400-degree calibrated-mask construction, this has 59.88% lower degree and 19.12% fewer gates. No global optimality or new unknown-count theorem is claimed.

## Files

- `report.pdf`, `report.tex`, `section.tex`: complete new source proof, literal final equation, inherited finalizer implications, and proof boundary.
- `generated/sun10.json`: literal polynomial DAG, ten variable leaves, fixed leaves, live gates, and named registers.
- `generated/source_records.json`: all 89 fixed coefficient recipes.
- `INSTANCE.json`: active whole original package-31 coefficient binding; `MF_source` is already shifted.
- `data/`: exact source, finite layout, all four compressed compiler-port payloads and their binding.
- `SOURCE_PINS.json`, `upstream/`, `licenses/`: exact inherited source identities, proof records, and required notices.
- `generated/INDEPENDENT_CHECKS.json`: full independent source, circuit, degree, and finite-control audit.

## Reproduce

Python 3.10+ and its standard library suffice:

    python3 reproduce.py

This rebuilds byte-identical generated artifacts and runs an independent checker, including under `python3 -O`. The checker does not import the builder. It reconstructs 22 raw residuals, verifies both inverse row operations and 22,544 isolation interactions, compares 59 exact local circuit identities, checks a Lucas factorization and the 35-term norm identity, audits gate liveness, verifies all payload pins, and certifies exact degree by nonzero modular leading coefficients.

To evaluate modulo an integer, in variable order f,g,h,k,l,w,x,y,z,m:

    python3 evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1 1

A modular zero is not an integer solution certificate. Gate counts exclude constructing fixed coefficient leaves and are not bit-complexity bounds.

Build the PDF with `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice in a normal TeX Live installation. The included PDF is ready to read.

## Proof boundary

The new unbounded extraction, positivity, borrow, and calibrated-population arguments are in `section.tex`. The original native-window compiler/K215 endpoint and Sun arithmetic theorems remain imported mathematical dependencies. This is ordinary mathematics formalizable in ZFC, not a new end-to-end proof-assistant certificate and not a proof of Con(ZFC).
