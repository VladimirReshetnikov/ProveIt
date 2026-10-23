# Fifteen integer unknowns and smaller Diophantine forms for Con(ZFC)

Prepared for ProveIt, 22 October 2026. Comparison snapshot:
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.

## Main result

This package specifies a polynomial in **15 unrestricted integer variables**
whose unsolvability is provably equivalent in ZFC to `Con(ZFC)`, by ordinary
mathematics composed with the pinned compiler and K215 calibration.
It improves the inspected concrete 17-integer construction; it is not a
global variable-count record or an end-to-end proof-assistant certificate.

The complete article is `report.tex` / `report.pdf`.

| Construction | Domain | Equations | Exact degree / maximum residual degree | Operations |
|---|---|---:|---:|---:|
| New square-radix signed Jones | 15 unrestricted integers | 1 | 813056 * 5^33 + 4184 | 1541 |
| New signed Jones | 16 unrestricted integers | 1 | 406528 * 5^33 + 10008 | 1550 |
| Optimized positive product | 12 strictly positive integers | 1 | 1081 | 108 |
| Same-coordinate positive system | 12 strictly positive integers | 3 | 1072 | 104 |
| Shifted positive system | 12 strictly positive integers | 3 | 1072 | 103 |

All binary +, -, and multiplication operations are charged, including by fixed
numerals. Fixed coefficient construction is excluded; reuse and system equality
comparisons are free. These are explicit circuit sizes, not lower bounds.

The mathematical improvements are a Pell-orbit removal of the final sign guard,
a cofinal square-radix choice removing another guard, and a smaller separating
weight. Factored evaluation supplies a separate large circuit reduction.
The positive product uses three exact identities in package 30's polynomial.

## Coefficient bindings

The integer families retain the original complete **T4** compiler/index tuple
from package 29, with no rebinding. Their fixed integers have explicit finite
recipes; they are not all materialized. The 15-variable form adds the fixed
leaf `b_floor=(2*z_index)^(5^33+1)` and removes the old `y_index` leaf.

The positive family uses the new complete **Wang943 mixed121** tuple:

    rho = 2^121, cell length = 8801,
    d = 1064921 = 11^2 * 13 * 677, B = 2^d.

All four ports are materialized in `compiler/coefficients/*.bin.gz`:
533099 raw bytes, 10485 gzip bytes in total. This reduces the earlier
smallest base exponent 1953125 by 45.4760448 percent. The tuple is defined
by `compiler/coefficients/COEFFICIENT_BINDING.json`; MF_source is already
shifted. Never splice individual ports or substitute it into the already
specialized integer Jones circuit without recomputing the latter's index.

## Exact equations and artifacts

- `integer15/generated/signed15.json`: principal 15-integer equation.
- `integer16/generated/signed16.json`: 16-integer companion.
- `integer15/SIGNED15_16_PROOF.md`: detailed new derivation.
- `positive/positive12_product108.json`: 108-operation positive polynomial.
- `positive/positive12_system104.json`: same-coordinate system.
- `positive/positive12_shifted_system103.json`: shifted positive system.
- `positive/OPTIMIZATION_PROOF.md`: exact identities and transport proof.
- `positive/INDEPENDENT_SIGNED_REVIEW.md`: separate mathematical review.
- `compiler/COEFFICIENT_PROOF.md`: complete finite recipe and unbounded
  Boolean-padding completeness argument.
- `references/COMPARISON_AT_PIN.md`: the inspected collection's comparison.
- `evidence/`: rebuild, degree, binding, and PDF checks.

For the integer JSON format, the only quantified unknowns are `variable`
nodes. `fixed` nodes are prescribed by the binding/recipe files. The `nodes`
array is a topologically ordered arithmetic circuit; `output` is equated to
zero. All exponents in its finite construction are fixed, not variables.
For the positive JSON format, the ordered `source` rows specify binary gates;
`output` is equated to zero or each pair in `comparisons` is equated.

## Offline rebuild and verification

Python 3.10 or later, standard library only:

```sh
python3 verify_all.py
```

This rebuilds the new coefficient payloads and circuits, runs independent
checks, verifies the complete positive binding, and writes
`evidence/VERIFICATION.json`. No network or repository checkout is required.
The verifier does not decide solvability or consistency.

To rebuild the PDF with a conventional TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

`make verify` and `make pdf` provide these commands. The verification does not
depend on a package-local SHA256SUMS ledger or TeX build files, so the repository's
ignore rules do not remove required inputs. Rebuilt PDFs need not have identical
timestamps.

## Proof boundary and comparison limits

ZFC proves the equivalence between absence of a root and its consistency;
this package neither assumes nor proves that ZFC is consistent. The native
compiler and K215 calibration are inherited mathematical results. The new
transformations have written proofs and executable finite audits, but no new
end-to-end Lean/Rocq certificate is claimed. Separate review was AI-assisted,
not external human peer review.

Existing nine-positive-variable, low-degree, and 67-operation constructions
retain their respective advantages. Sun's 2026 preprint states an abstract
10-integer representation theorem; its different compiler is not instantiated
here. No global minimum or priority claim is made.

The repository was not modified. New work follows its MIT-0 convention;
upstream attribution, machine licences, and notices are preserved.
