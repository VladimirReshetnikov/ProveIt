# Proving Two Arithmetic Conjectures for OEIS A321941

**Research draft, 1 October 2026.** The article gives human-readable proofs of
Brent–Glasser–Guttmann's integrality conjecture and the modulo-32 part of their
stronger numerical observation. The separate negativity conjecture remains
unproved here. This is not a peer-reviewed publication or a Lean/Rocq certificate.

## Main results

For the published asymptotic coefficients `d_k`, put `r_k = 64^k d_k`.
The article proves `r_0 = 1`, `r_k` is an even integer for every `k > 0`, and

    r_k = binom(2k,k) + 16*[k in {1,2}]  (mod 32).

The proof uses a quadratic Wronskian identity, integral rescaled shift operators,
and a triangular evenness induction. The article also establishes an integral
polynomial family `P_k(t)`, its universal congruence and extreme coefficients,
minimality of the scale 64, exact denominator formulas when the index has at
most four nonzero binary digits, and all-orders inverse coefficients with a
restricted denominator prime support. Nine further research topics are included.

The analytic existence of the original product expansion is an explicitly cited
published theorem, not a new claim in this package. The new arithmetic proof
identifies its coefficients with the unique formal master-series solution.

## Contents

- `article.pdf`: the compiled 18-page article.
- `article.tex`: the complete editable LaTeX source; bibliography is included.
- `verify.py`: reproducible exact and optional symbolic/numerical checks.
- `verification_output.txt`: the actual output of the archived check run.
- `verification_metadata.json`: versions, completed check ranges, and status.
- `coefficients.csv`: `r_k`, reduced `d_k`, valuations, and binary digit counts
  for indices 0 through 256.
- `polynomials.txt`: exact `P_k(t)` for indices 0 through 8.
- `numerical_checks.csv`: high-precision diagnostics at n = 25, 100, 400.
- `SOURCES.md`: source audit, URLs, repository commit, and novelty limitations.
- `BUILD_NOTES.txt`: compilation and PDF inspection information.

## Reproduce the checks

Use Python 3.10 or newer, with assertions enabled (do not use `python -O`):

```sh
python verify.py --order 256 --independent-order 128
```

The main integer and independent rational recurrences use only the Python
standard library. SymPy and mpmath enable additional checks:

```sh
python -m pip install sympy mpmath
```

The archived run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. All checks
ran successfully. Missing optional dependencies are explicitly reported as
skipped; they are not reported as passed. Use `--no-optional` for a standard-library
run, or `--out another_directory` to avoid overwriting archived output data.
The console log itself can be captured with shell redirection.

Executed exact checks include the new arithmetic formulas through index 256,
independent agreement with the published rational recurrence through index 128,
all thirteen displayed OEIS terms, parameter congruences at five additional
integer parameters through index 48, polynomial identities through degree 8,
the bilinear identity, and the five displayed inverse coefficients. Numerical
strings were stable between 80 and 120 decimal-digit working precision; these
are diagnostics, not interval certificates.

## Rebuild the article

A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages,
`microtype`, `hyperref`, `xurl`, `enumitem`, `fancyhdr`, and `booktabs` is sufficient.
No external bibliography program, figures, or font files are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Scope

Finite computation checks signs and normalization, but the global conclusions
come from proofs in the article. Negativity beyond the computed range is not
inferred. No effective remainder constants or exponentially small transseries
sectors are supplied. No OEIS entry or repository file has been changed.
An independent mathematical review and a broader priority search should precede
submission as a settled new result.
