# When the Secant Numbers Become Periodic

A counterexample, a complete classification, and a distribution law.
Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Main result

Let `sec(x) = sum(a(n) * x^(2n)/(2n)!, n >= 0)` (OEIS A000364).
The OEIS entry still records a conjecture that the sequence starting at
`n=1` is purely periodic modulo every positive integer `m`, with a period
dividing `phi(m)`. The counterexample is:

```text
m = 27, phi(m) = 18
a(1) = 1
a(19) = 23489580527043108252017828576198947741
a(1) mod 27 = 1
a(19) mod 27 = 10
```

The exact replacement is that pure periodicity from index one holds if
and only if **no odd prime cube divides m**. The least eventual period
always divides `phi(m)`. The report determines the least eventual period
and exact onset for every modulus, proves the natural density of every
bounded-onset class, and gives the mean onset with a rational certificate:

```text
1.05402581008837151 < mean first periodic index < 1.05402581008837162
```

The validity density of the original assertion is `8/(7*zeta(3))`,
approximately 95.0751282949379964 percent.

## What the contribution claim means

This resolves the specific assertion still displayed in OEIS A000364 as
consulted on 19 September 2026. Classical Euler congruences already imply
its failure. The report explicitly acknowledges Kummer/Stern congruences
and recent work on the different, full up/down sequence. It does not
claim every theorem is new, does not claim an exhaustive priority search,
and does not claim to resolve the remaining preperiod conjectures for
the full up/down sequence. All stated universal formulas are proved in
the article, not merely guessed from the included data.

## Files

- `article.pdf`, `article.tex`: the mathematical report and its source.
- `counterexample.py`: a standalone finite counterexample check.
- `secant_periodicity.py`: exact period, onset, coefficient and density-cutoff functions.
- `verify.py`: independent coefficient comparisons and modular checks.
- `certify_densities.py`: exact rational enclosures, with no floating-point assumptions.
- `data/`: machine-readable values, witnesses, logs and certificates.
- `oeis_correction.txt`: proposed correction wording, not submitted anywhere.
- `SOURCES.md`: source provenance and distinctions between sequences.
- `Makefile`, `build.ps1`: optional build helpers.
- `SHA256SUMS.txt`: checksums of the final package files other than itself.

## Reproduce the computations

The full package requires Python 3.9 or later and **no third-party Python
packages**. The isolated `counterexample.py` works with Python 3.8 or later.
The recorded run used Python 3.13.5.

```sh
python counterexample.py
python verify.py
python certify_densities.py
```

Both larger scripts accept `--output PATH` to write generated data to a
different directory. They do not use the network. A nonzero process exit
status indicates a failed check. Checks remain active under `python -O`.

The verification constructs exact coefficients through index 2100 by an
Entringer triangle and cross-checks the binomial recurrence through index
100. It checks the proposed periods and onsets for every modulus through
1000, with 130793 period-shift equalities and 2432 smaller-period witnesses.
The CSV table through modulus 10000 is formula-generated; its final 9000
entries were not independently checked against full coefficient blocks.
No proof-assistant formalization was executed.

The density script computes D_1 through D_10 and the mean bounds using
`fractions.Fraction` and 96 terms of a positive Euler transform for each
required eta/zeta value. Exact rational endpoints and outward-rounded
30-place decimal endpoints are included. Very large integers in the
certificate are intentional. On Python versions with an integer-to-text
digit cap, that cap is disabled only to serialize locally generated
certificate integers.

Runtime and the Python version in `verification.json` can change on a
rerun; mathematical data and witnesses should remain the same.

## API examples

```python
from secant_periodicity import analyze_modulus, secant_mod_odd

result = analyze_modulus(27)
print(result.preperiod)            # 2: the first periodic index is n=2
print(result.period)               # 18: the LEAST eventual period
print(result.pure_from_index_one)  # False
print(secant_mod_odd(19, 27))       # 10

print(analyze_modulus(3125))       # onset 2, period 1250
print(secant_mod_odd(10**100 + 123456789, 27))
```

Indexing starts at zero. In particular, onset `s=1` means the first term
`a(0)` can be exceptional but the OEIS claim concerning all `n>=1` is true.
Modulus 1 is assigned onset 0 and period 1. Powers of two have onset 0.

Factorization and primality tests use transparent trial division. These
are not suitable for cryptographically large arbitrary moduli. The
finite-moment coefficient routine needs O(q) modular exponentiations for
an odd modulus q: it is useful for huge indices and modest moduli, not
huge moduli. No assumption that integer arithmetic costs constant time
is made in the report.

## Build the PDF

Use a LaTeX installation with `latexmk`, pdfLaTeX and the packages named
in the preamble, especially `newpxtext`, `newpxmath`, `microtype`,
`tcolorbox`, `listings`, `hyperref`, and standard AMS packages. No fonts
are distributed with this archive.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

`make pdf` builds into `build/` and copies the PDF to the top level.
`make check` reruns the computations. On Windows, `./build.ps1` performs
both tasks; `./build.ps1 -SkipChecks` just builds the PDF. The helper
scripts stop on errors rather than silently retaining an old PDF.
