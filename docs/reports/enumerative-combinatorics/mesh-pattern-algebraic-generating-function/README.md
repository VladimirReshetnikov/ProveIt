# A proof of the generating-function conjecture for OEIS A289587

The article proves Thomas Scheuerle's generating-function conjecture for
permutations avoiding 321 and mesh pattern (12,174), and proves the equivalent
count for (12,234) by permutation inversion. The OEIS entry consulted on
September 20, 2026 explicitly labels the formula conjectural. No exhaustive
publication-priority claim is made.

## Main result

With

    D(x) = x^4 - 2*x^3 - 5*x^2 - 2*x + 1,
    P(x) = x^4 + 4*x^3 + 11*x^2 + 10*x + 3,
    Q(x) = x^2 + 5*x + 3,

and the formal square root having constant term 1,

    A(x) = (P(x) - Q(x)*sqrt(D(x))) / (8*x*(1+x)^2).

The proof first characterizes the mesh restriction by upper bonds and singleton
sum components, and then uses canonical record-run contraction. It also derives
refinements, exact coefficient algorithms and two-term asymptotics.

## Files

- `article.pdf`: complete mathematical article.
- `article.tex`: self-contained LaTeX source; bibliography and vector diagram included.
- `verify.py`: Python 3.9+ standard-library exact and exhaustive checks.
- `symbolic_check.py`: optional SymPy/mpmath algebra and asymptotic certificates.
- `verification.log`, `symbolic_check.log`: logs of completed successful runs.
- `data/`: coefficients, extended b-file, exhaustive counts, verification report,
  symbolic certificates, asymptotic constants and numerical ratios.
- `source_notes.md`: exact source URLs and the role of each source.
- `requirements-optional.txt`: third-party packages for the optional checker only.
- `Makefile`: convenience build and verification targets.

## Reproduce

The main checker has no external dependencies:

```sh
python verify.py --max-n 1000 --exhaustive 11
```

Do not use Python's `-O` flag, which disables assertions. The default command
checks all 82,500 permutations in Av(321) of lengths 0 through 11; it does not
enumerate all n! permutations at the largest lengths. As an independent
generator cross-check, it does compare against all n! permutations through
length 8. The completed run used Python 3.13.5.

The two coefficient algorithms agree at indices 0 through 1000. There are
23,713 contraction/inflation round trips on nontrivial indecomposables, 102
independent small-core inflation tests, and a complete comparison of the
four-variable enumerator against joint statistics through length 11.
Pointwise mesh transposition is checked through length 8. Both mesh totals
and the structural characterization are checked through length 11.

For optional exact symbolic certificates and 90-digit-precision calculations:

```sh
python -m pip install -r requirements-optional.txt
python symbolic_check.py
```

The mathematical constants in the article are given by exact expressions.
The accompanying decimal evaluations are high-precision numerical evaluations,
not interval-certified decimal bounds. The asymptotic expansion itself is proved.

To compile the article using an ordinary TeX Live or MiKTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A further LaTeX pass may be needed if a local installation changes page breaks.
Alternatively, run `make pdf` with `latexmk` installed. Neither the PDF nor the
standard-library checker requires an internet connection once this archive has
been extracted. No external graphics or font files are needed.

## Interpretation of the checks

Finite tests are supporting verification, not a proof for all indices.
The proof is the structural characterization, the canonical inflation bijection,
and the subsequent formal power-series derivation in the article.
The extended b-file was generated for this archive; it is not an official OEIS
b-file, and no OEIS edit or submission has been performed.
