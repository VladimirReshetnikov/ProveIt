# Arithmetic Transseries Beyond an Accumulation Cut

**Divisibility, summable inversion, and curvature-lifted resonances**  
Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read the article

- `arithmetic_transseries.pdf`: the complete article with proofs, nine further research questions, and appendices.
- `arithmetic_transseries.tex`: standalone editable LaTeX source. Its numerical table is embedded, so no external TeX input is required.

The article addresses the arithmetic-transseries direction in ProveIt's
*Combinatorial Transseries and Their Inverses*. It keeps the divisibility
indicators, gives a weighted absolute summation theory across an accumulating
action block, proves fixed-label inverse convergence with explicit tails, and
derives an all-order curvature-lifting law for inverse resonances.

## Scope and status

These are proposed mathematical research extensions with proofs, not a claim
of independently established publication priority. The lcm convolution,
well-ordering tools, and Lagrange inversion are classical ingredients.
The new theorems have not been formalized in Lean or independently refereed.

The inverse is an analytic inverse on each **fixed arithmetic sheet**, and an
identity on the exact range of the counting sequences. The article does not
supply a canonical global interpolation or a fractional shift of divisibility
indicators. It proves structural limitations on such interpretations. It does
not assert a general resurgence theorem.

## Reproduce the checks

Python 3.10 or newer and mpmath are needed:

```sh
python -m pip install -r requirements.txt
python verification/verify.py
```

The test suite reports 964 exact assertions and 48 numerical inverse-error
checks at 400 decimal digits. Exact checks use Python integers and Fraction.
The numerical checks are high-precision diagnostics, **not outward-rounded
interval certificates** and not a proof-assistant verification of the general
theorems.

Results are in:

- `verification/results.json`
- `verification/inverse_error_checks.csv`
- `verification/resonance_checks.csv`
- `verification/table.tex`

The `inverse_jet` function computes homogeneous inverse terms without
explicitly enumerating all action tuples. The `action_tuples` function performs
the exact finite fixed-action search described in the article.

## Rebuild the PDF

With a standard TeX installation containing the packages used in the source:

```sh
sh build.sh
```

This reruns the tests, synchronizes the embedded numerical table, and runs
pdflatex three times. To compile only the already supplied standalone source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
```

The delivered PDF has 25 pages. The final build had no LaTeX warnings, undefined
references, or overfull/underfull boxes. Rendered pages were visually inspected;
`validation.json` records the delivery checks.

## Provenance

The repository snapshot is `db68f0853c3c69cd930caedab6f6ad9addb11eaf`.
See `source_notes/provenance.json` and `source_notes/scope.md` for exact paths,
source blobs, the research question addressed, and the boundaries of the
repository/literature comparison. No repository mutation was performed.
