# Asymptotics of OEIS A277364

> **`data/a277364_exact.txt` is not distributed** (0.8 MB). Rebuild it with `python code/analyze.py`.
> **`data/diagnostics.csv` is not distributed** (1.1 MB). Rebuild it with `python code/analyze.py`.
The article proves that

    a(n) = sum_{k=0}^{floor(n/2)} S(n,k) ~ B_n,

and, with r = W_0(n),

    a(n) ~ exp(n*(r - 1 + 1/r) - 1) / sqrt(1+r).

It also derives an explicit first correction, a parity-sensitive equivalent
and first correction for B_n-a(n), the precise logarithmic size of the
omitted proportion, and an extension to every fixed cutoff alpha*n,
0 < alpha < 1. Full analytic proofs are in the article. This is an
application of classical Bell/Stirling asymptotics, not a claim to have
originated the Bell-number asymptotic expansion.

## Files

- `A277364_asymptotics.pdf`: the compiled article.
- `A277364_asymptotics.tex`: complete LaTeX source and bibliography.
- `code/analyze.py`: exact-integer enumeration, arbitrary-precision
  asymptotic diagnostics, validation, and optional figures.
- `code/make_tables.py`: generates the two LaTeX tables from the CSV.
- `data/a277364_exact.txt`: independently generated exact values, n=0..1000.
- `data/diagnostics.csv`: diagnostics for n=2..2001, with 35 significant
  digits saved for noninteger numerical quantities.
- `data/verification.json`: machine-readable record of checks actually run.
- `data/selected_diagnostics.txt`: selected readable numerical results.
- `data/table_main.tex`, `data/table_tail.tex`: article table inputs.
- `figures/`: the three figures as PDF and PNG.
- `OEIS_formula_note.txt`: formula extract, not submitted to OEIS.
- `requirements.txt`: Python dependency versions used in this run.

## Reproduction

The computations were executed with Python 3.13.5, mpmath 1.3.0,
and Matplotlib 3.10.8. From this directory:

```sh
python -m pip install -r requirements.txt
python code/analyze.py --max-n 2001 --plots
python code/make_tables.py
latexmk -pdf -interaction=nonstopmode A277364_asymptotics.tex
```

The already-generated PDF and figures do not require Python to read them.
To compile the existing source without regenerating data, run only the
last command. The source uses standard TeX Live packages including newpx,
amsthm, mathtools, tcolorbox, placeins, microtype, listings, and hyperref.
No font files are included. The mathematical analysis and reproduction
scripts make no network calls.

To regenerate just the numerical data without figures, omit `--plots`.
The exact table length can be changed with `--exact-through N`.
The precision of approximations can be changed with `--dps D` (D>=40).
The default uses 80 decimal digits. The integer counts remain exact at
any supported approximation precision.

## Validation and its scope

The executed checks were:

1. Agreement with every value in the displayed OEIS A277364 prefix,
   n=0..25.
2. Exact agreement between row-sum Bell counts and the independent
   binomial Bell recurrence through n=400.
3. The exact decomposition B_n=a(n)+D_n throughout n=0..2001.
4. Agreement of four explicit cumulants with numerical derivatives of
   the cumulant generating function.

The longer OEIS b-file was not used as a full external comparison in this
run. A locally saved copy can be checked using:

```sh
python code/analyze.py --max-n 2001 --oeis-file path/to/b277364.txt
```

The script reports how many supplied reference entries were checked.
Numerical consistency tests do not replace the analytic proofs.

## Numerical interpretation

`deficit` in the CSV is D_n/B_n, computed directly. It is not obtained by
subtracting a rounded a(n)/B_n from 1. `F_over_a_minus_1` and the analogous
columns are signed relative errors of the named approximation. The
first-corrected formulas are asymptotic approximations, not certified
finite-n error intervals. They need not improve the approximation at
very small n.

The `scaled_log_deficit` column converges to -1/2, but slowly. The next
term is log(log n)/log n, so moderate-n values should not be mistaken
for a contradictory limit.

## Sources

OEIS A277364: https://oeis.org/search?q=id:A277364&fmt=text
OEIS b-file: https://oeis.org/A277364/b277364.txt
NIST Bell numbers: https://dlmf.nist.gov/26.7
NIST Stirling numbers: https://dlmf.nist.gov/26.8
NIST Lambert W: https://dlmf.nist.gov/4.13
Moser–Wyman original paper: https://oeis.org/A000110/a000110_4.pdf

The reference papers themselves are not redistributed in this archive.
