# Report214 exact finite reproduction

This directory is a self-contained Python-standard-library computation. Use Python
3.9 or newer. There are no third-party dependencies, downloads, symbolic-algebra
packages, random inputs, fitted constants, or stored moment arrays used as inputs.
The five small files in `results/` are comparison baselines, not inputs to the
mathematical calculation.

From the package root, choose a **new** output directory outside the source tree:

```sh
python3 -B code/reproduce.py --out /tmp/report214-finite-normal
python3 -B -O code/reproduce.py --out /tmp/report214-finite-optimized
```

Each invocation runs the underlying finite calculation under both normal and
optimized Python and compares all result bytes and stdout. It then exercises
deliberate failure cases under both modes. All mathematical and safety guards use
explicit exceptions; an AST scan rejects Python `assert` statements. Optimization
does not disable the checks. The output contains `results/`, `guard_checks.json`,
and `reproduction.json`. Receipts omit timestamps, optimization flags, temporary
paths, and interpreter paths, so unchanged source and results give identical
receipt bytes across the two commands on the same compatible Python environment.

To regenerate just the mathematical outputs without the failure harness:

```sh
python3 -B code/finite_checks.py --out /tmp/report214-finite-data
```

Add `--compare code/results` to require byte-for-byte agreement with the shipped
baseline before creating the output directory. All destinations must be new, with
an existing parent, and outside the source package. Existing directories, files,
and dangling symlinks are rejected rather than modified. Scratch directories are
created beside the requested output and cleaned automatically by the harness.
The package-wide driver separately handles the PDF, manifest, and archive.

## What is checked

- Fresh first-edge recurrence through half-length 32, with boundary identities,
  the one-deficit row, and the finite Catalan-factorial upper bound
- Independent exhaustive first-appearance-normalized tree-walk enumeration
  through half-length 7: 12,850 walks in total, comparing every root row and
  weighted rotation counts. Generation follows discovered edges or discovers
  the next vertex; it does not use recurrence rows, partitions, or Bell numbers
- Child-return polynomials `d_h` and `P_h` through `h=6`, computed with rational
  finite differences in the falling-factorial basis, then tested at `q=0,...,19`
  against the branch formula and the independent Newton-difference definition
- All set-partition size profiles for `n=1,...,5`, with their exact multiplicities,
  all urn occupancies for `s=0,...,5`, probability normalization, the exact branch
  identity, Newton exactness whenever collision excess is at most orders 1, 2,
  or 3, the urn factorial averages, and finite marked-collision inequalities
- Ordered distinct-block expectations versus the Bell exponential-formula
  reduction on eight listed configurations for `n=1,...,8`; the explicit
  `G_1` and `G_2` formulas; finite Poisson factorial-shift Bell identities
- Exact first and second Bell transforms through half-length 32, fresh Bell
  normalization, deficit factorial moments, and the rotation cancellation
- Scalar interpolation identities for `H=2,...,6`, `u=1,...,H`, `k=1,...,18`,
  and `z` in `{1,2,5}`, including vanishing terms below the boundary
- Termwise Poisson reindexing kernels at the stated integer samples. No
  truncated floating-point Poisson series is labeled an exact expectation

Exact scopes and check counts are in `results/checks.json`. The recurrence
triangle is represented only by a checksum and small independently enumerated
rows; no large numerical arrays are shipped.

## Output files

- `checks.json`: exact-check scopes/counts, small enumerated rows, root-array
  checksum, and exact selected ratios and correction values
- `selected_table.csv`: half-lengths 2, 4, 8, 12, 16, 24, 32; exact numerator and
  denominator plus display decimal for the ratio, `A_1`, `A_2`, and
  `ratio - 1 - A_1 - A_2`
- `polynomials.json`: ascending rational coefficients of `d_h` in monomials and
  falling factorials and of `P_h` in monomials, for `h=1,...,6`
- `table.tex`: the five requested numerical columns, rounded half-even to six
  decimal places from exact fractions
- `rows.tex`: rows 1 through 5 and return-count columns 1 through 5, with impossible
  entries explicitly zero

## Deliberate failures and limitations

The harness corrupts a value immediately before nine selected mathematical
comparisons. It also changes actual JSON/CSV/TeX reference bytes, inserts duplicate
JSON keys, removes/adds/links reference files, adds a Python source file, and
checks pre-write and output-path rejection. Each case must fail nontrivially at
its intended guard in both normal and optimized modes. Existing sentinel files,
directories, and dangling links must remain unchanged. The receipt records every
case. These are selected guard tests, not a claim that every possible bug,
malicious input, filesystem race, or mathematical error is detected.

The computations establish only the specified **finite identities and
inequalities**. They do not prove any asymptotic estimate, leading constant,
derivative bound, effective onset, error constant, inverse radius, or validity
when truncation order grows. Small-index residuals in the table are not a test of
the eventual asymptotic remainder. The article supplies the mathematical proofs;
its inverse enclosure constants and onset remain existential.
