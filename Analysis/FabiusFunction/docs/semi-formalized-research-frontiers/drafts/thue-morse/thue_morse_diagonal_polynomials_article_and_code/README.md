# Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue-Morse Prefix Summation

This archive accompanies the article requested for the two-dimensional table `s[n,k]` obtained by repeated summation of the signed Thue-Morse sequence.

## Main closed form

Put

- `epsilon(j) = (-1)^ThueMorse[j]`,
- `q = k - n - 1`, and
- `D_q(x) = s[x, x+q+1]` on nonnegative integral `x`.

The fixed-diagonal polynomial is

```text
D_q(x) = Sum[epsilon(j) RisingFactorial[2 x, q - 2 j]/(q - 2 j)!,
             {j, 0, Floor[q/2]}].
```

Equivalently,

```text
Sum[D_q(x) z^q, {q,0,Infinity}] = K(z^2)/(1-z)^(2 x),
K(z) = Product[1-z^(2^r), {r,0,Infinity}].
```

Thus the diagonal with `k=n+d` is `D_(d-1)(n)`, a polynomial of degree `d-1` with leading coefficient `2^(d-1)/(d-1)!`.  The article proves this formula, develops the exact dyadic block geometry of every row, derives coefficient and denominator formulas, classifies all rational roots by finite Thue-Morse tests, and connects normalized rows to the Rvachev up-function and the Fabius function.

## Archive contents

- `thue_morse_diagonal_polynomials.tex` - complete LaTeX source.
- `thue_morse_diagonal_polynomials.pdf` - rendered 33-page article.
- `thue_morse_diagonals.wl` - standalone Wolfram Language implementation and regression tests.
- `diagonal_analysis.py` - exact Python/SymPy verification and data-generation program.
- `generated/verification_report.txt` - pass/fail report for all automated exact checks.
- `generated/run_stdout.txt` - complete console transcript from the supplied Python run.
- `generated/diagonal_polynomials.csv` - expanded and factored diagonal polynomials through the configured cutoff.
- `generated/half_grid_roots.csv` - exact nonnegative rational-root data.
- `generated/normalized_row_pulses.{pdf,png}` - generated figure files.
- `figures/normalized_row_pulses.{pdf,png}` - synchronized copies used by LaTeX.
- `MANIFEST.sha256` - SHA-256 checksums for the release files.

## Reproduction

From the archive root, regenerate the exact tables, report, and figures with

```bash
python diagonal_analysis.py --output-dir generated --max-table-q 20
```

The script also synchronizes the figure files in `figures/`.  Then rebuild the article with

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  thue_morse_diagonal_polynomials.tex
```

The Python program uses exact Python integers and SymPy rational arithmetic for the identities and polynomial calculations.  Matplotlib is used only to render the illustrative figure.  The proof does not depend on floating-point experiments.

## Automated checks included

The supplied verification run checks, among other identities:

- the closed formula against literal repeated prefix summation for `0 <= n <= 5`, `0 <= k <= 70`;
- the exact signed dyadic block formula on the same grid;
- the original weighted recurrence;
- diagonal formulas through `q=30`;
- the nonnegative and negative half-grid root criteria;
- an infinite trailing-ones family of negative rational roots;
- the exact minimal coefficient-denominator formula through `q=24`; and
- pulse support, positivity, palindromy, mass, and plateau formulas through order 10.

All checks in `generated/verification_report.txt` pass.
