# A277280: exact maximization and asymptotics

> **`data/computed_b277280_0_1000.txt` is not distributed** (0.6 MB). Rebuild it with `python code/reproduce.py`.
The main article is `article.pdf`; its complete source is `article.tex`.
The sequence is the largest **positive** coefficient of the physicists'
Hermite polynomial, with signs retained, not the largest coefficient magnitude.

## Main result

As n tends to infinity,

    a(n) ~ exp(sqrt(2n) - 1/2) / (sqrt(pi) (2n)^(1/4)) * (2n/e)^(n/2).

The unique maximizing exponent is d = n - 4k, where

    k = (2n + 6 - isqrt(8n + 21)) // 8,
    a(n) = n! 2^d / ((2k)! d!).

The article proves this exact formula, three rounding-sensitive asymptotic
correction terms, explicit finite-index bounds, sharp fluctuation envelopes,
limiting distributions, and a(n+1)/(a(n)*sqrt(n)) -> sqrt(2).

## Files

- `article.tex`, `article.pdf`: full proofs and discussion.
- `code/a277280.py`: exact single-term and streaming algorithms, ratio formula,
  high-precision logarithms, and numerical evaluation of analytic error bounds.
- `code/verify.py`: independent finite checks and optional external b-file check.
- `code/reproduce.py`: regenerate figures, tables, and computed terms 0..1000.
- `code/symbolic_check.py`: optional exact symbolic expansion verification.
- `data/verification.json`: report from the executed checks.
- `data/symbolic_check.txt`: executed symbolic-check report.
- `data/asymptotic_comparison.csv`: high-precision comparison data.
- `data/computed_b277280_0_1000.txt`: independently computed terms, not copied
  from the published OEIS b-file.
- `figures/`: three figures, each as a vector PDF and a PNG preview.
- `sources.md`: source URLs, normalization, and verification scope.
- `oeis_note.txt`: a compact formula/comment summary, not submitted to OEIS.
- `environment.json`: versions used for the supplied run.

## Run the code

The exact library requires Python 3.9+ and the standard library only:

    python code/a277280.py 100
    python code/verify.py

The optional high-precision routines and plots need the packages in
`requirements.txt`:

    python -m pip install -r requirements.txt
    python code/a277280.py 1000000000000 --log
    python code/verify.py
    python code/reproduce.py
    python code/symbolic_check.py

All supplied verification and regeneration commands work without network
access after dependencies have been installed. To additionally compare a
locally available complete OEIS b-file:

    python code/verify.py --oeis-file path/to/b277280.txt

The supplied execution checked the 25 displayed OEIS terms, not the whole
external b-file. See `data/verification.json` for exactly what was checked.
Finite numerical and symbolic tests complement, rather than replace, the
analytic proofs in the article.

## Build the PDF

A conventional TeX Live or MiKTeX installation with the packages imported by
`article.tex` is sufficient. From this directory:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The figures and table rows are already included, so Python is not needed
just to compile the PDF. Alternatively use `make pdf`; `make all` regenerates
the computations as well. On Windows the explicit commands above avoid any
requirement for GNU Make.

## Numerical conventions

The high-precision code evaluates exact formulas for the maximizing index.
Its floating-point log-gamma and Stirling-endpoint evaluations are diagnostics,
not directed-rounding interval certificates. The analytic inequalities in
Section 5 are rigorous independently of the numerical implementation.

No originality or exhaustive-literature-search claim is made. Source facts
are attributed in the article, and the mathematical results are derived in
full there.
