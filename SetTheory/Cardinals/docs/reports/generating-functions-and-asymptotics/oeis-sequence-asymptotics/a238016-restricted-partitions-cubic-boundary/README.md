# The Cubic Boundary for Restricted Partitions

Research report prepared for Vladimir Reshetnikov, 1 October 2026.

## Read the article

`restricted_partitions_cubic_boundary.pdf` is the compiled article.
`restricted_partitions_cubic_boundary.tex` is its complete editable source.
The source contains its bibliography; no separate BibTeX database is needed.

The report treats p_m(N), the number of partitions of N with all parts at most
m, equivalently the number with at most m parts. It includes an elementary
sharp cubic threshold, uniform all-order expansions, five explicit correction
terms for OEIS A238608, exponential sectors for p_m(q^m), inverse asymptotic
charts, and a Poisson repeated-part law in the conjugate at-most-m-parts model.
It ends with ten proposed further research directions.

## Status and attribution

The leading partition asymptotics have classical precedents. In particular,
the sufficiency of N/m^3 -> infinity is a consequence of the classical
Erdos-Lehner estimate discussed by Canfield; the leading cubic constant was
already posted on OEIS. The report does NOT claim to have newly discovered
these leading formulas. It provides proofs, sharpenings, explicit corrections,
and inverse/probability refinements. An exhaustive world-first priority claim
is not made. The proofs have not been independently peer reviewed or verified
in Lean. The inspected ProveIt generating-function source was not built here.

Numerical tests corroborate the formulas but are not proofs of their uniform
asymptotic remainders. Inverse charts apply with the stated error at exact
sequence sample values; arbitrary real thresholds still require discrete
rounding control. The report does not claim a full analysis of individual
root-of-unity waves or optimal truncation.

## Reproduce the computations

Tested with Python 3, SymPy 1.14.0, and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python derive_coefficients.py --order 5
python verify.py
python asymptotics.py
```

`derive_coefficients.py` derives all listed coefficients using exact rational
symbolic arithmetic, without fitting numerical partition values. It supports
other fixed orders; higher orders may be expensive. The standard verification
run requires the coefficient file to have at least five orders, so regenerate
with `--order 5` before running it after a lower-order experiment.

`verify.py` uses exact integer dynamic programming and an independent
divisor-sum recurrence, tests the finite inequalities, compares the displayed
OEIS initial values, and writes all numerical diagnostics. The full included
run passed 9,230 exact assertions and recorded 258 samples. Maximum m is 60;
coefficient arrays extend to N=320000. Floating-point diagnostics use 90
decimal digits. Run `python verify.py --quick` to cap the cubic runs at m=24.

The CSV values are signed approximation/exact - 1 where labeled as errors;
they are not certified enclosures. No network access is required after the
Python dependencies are installed.

## Build the PDF

A standard TeX Live installation with the packages named in the preamble is
sufficient. From this directory:

```sh
bash build.sh
```

This runs pdflatex three times to stabilize the table of contents and
cross-references. No shell escape or external bibliography tool is needed.

## Files

- `restricted_partitions_cubic_boundary.tex` and `.pdf`: complete article.
- `derive_coefficients.py`: exact critical-scale coefficient generator.
- `asymptotics.py`: reusable forward and inverse chart functions.
- `verify.py`: exact checks and numerical diagnostics.
- `coefficients.json`, `coefficients_tex.txt`: symbolic output through order 5.
- `exact_values.json`: 258 exact count samples, stored as decimal strings.
- `critical_errors.csv`: relative errors at truncation orders 0, 1, 2, 3, 5.
- `poisson_checks.csv`: zero probabilities, means, factorial moments, variance,
  and the generating function at u=1/2.
- `inverse_checks.csv`: cubic and exponential inverse sample-point errors.
- `verification_summary.json`, `verification_run.txt`, `symbolic_run.txt`:
  recorded successful runs.
- `OEIS_update_draft.md`: proposed source-aware comments; not submitted.
- `source_audit.md`: scope of the source and repository review.
- `requirements.txt`, `build.sh`, `SHA256SUMS.txt`: reproducibility support.

The repeated-part statistic is defined on partitions with at most m parts,
not on the original bounded-part-size representation. Conjugation preserves
the count but not that statistic.
