# A proof of the generating function for OEIS A289587

**Article:** *From Mesh Avoidance to Catalan Inflation*  
**Date:** September 20, 2026  
**Result:** The algebraic generating function marked conjectural in the
consulted OEIS entry is proved for every coefficient.

## Read first

`article.pdf` is the 13-page mathematical article; `article.tex` is its complete
LaTeX source. It includes the mesh diagrams as native TikZ, so no external image
files are required. The proof is conventional mathematics, not a proof-assistant
formalization. Finite computation corroborates the proof but is not used to
extrapolate the generating function.

The sequence counts 321-avoiding permutations that also avoid the mesh pattern
(12,174), or equivalently, by inversion, (12,234). The mesh identifiers are
explicitly decoded in the article and the program.

## Main identities

For every 321-avoiding permutation, the number of (12,174) occurrences is

    choose(number of fixed points, 2)
      + sum over maximal upper runs U of choose(length(U), 2).

An upper run consists of adjacent consecutive increasing values, all strictly
above their positions. Thus avoidance is equivalent to having no adjacent upper
succession and at most one fixed point.

With the formal square root having constant term 1,

    D = x^4 - 2*x^3 - 5*x^2 - 2*x + 1,
    P = x^4 + 4*x^3 + 11*x^2 + 10*x + 3,
    Q = x^2 + 5*x + 3,
    A = (P - Q*sqrt(D)) / (8*x*(1+x)^2).

The proof contracts maximal upper runs in the Narayana family, then separates
singleton direct-sum blocks. The article also provides fixed-point and excedance
refinements, a full mesh-occurrence generating function, positive finite sums,
and the asymptotic

    a(n) ~ K * gamma^n / n^(3/2),
    gamma = (1 + 2*sqrt(2) + sqrt(5 + 4*sqrt(2))) / 2
          = 3.5464554446849952445...,
    K     = 0.4139310680369706448....

## Reproduce the exact checks

Requires Python 3.9 or later. The main verifier uses only the standard library.
Run from this directory, without Python's `-O` option (checks use assertions):

```sh
python3 code/verify.py
```

The default run performs:

* literal mesh tests for both patterns through length 12;
* structural enumeration, Narayana distributions, and all fixed-point
  refinements through length 13;
* core contraction/inflation and full occurrence checks through length 10;
* independent radical-versus-recurrence coefficient checks through degree 200;
* alternating Narayana coefficient checks through degree 60 and positive
  finite-sum checks through degree 45;
* comparison with all 17 initial values in the consulted OEIS entry.

The executed default run passed every check. Its output and machine-readable
results are in `data/verification_log.txt` and `data/verification_results.json`.
At length 12, literal enumeration checked all 208012 Catalan permutations;
at length 13, structural enumeration checked all 742900 Catalan permutations.
The default run took about 18 seconds in the recorded environment; runtime and
memory use depend on the machine. Enumeration grows rapidly with the length.

A smaller smoke test, writing to a separate directory, is:

```sh
python3 code/verify.py --direct-n 8 --fast-n 9 --series-n 100 --out smoke-data
```

The optional algebra/asymptotics checks require SymPy and mpmath:

```sh
python3 -m pip install -r requirements-optional.txt
python3 code/symbolic_checks.py
```

They check seven symbolic identities exactly, then calculate the asymptotic
constants at 80 decimal digits of working precision. Numerical approximations
are not interval-arithmetic certificates. The included environment record
identifies the versions actually used.

## Build the PDF

A TeX Live installation providing `newtx`, AMS packages, `mathtools`, `geometry`,
`microtype`, `booktabs`, `tikz`, `enumitem`, `fancyhdr`, `xurl`, `hyperref`, and
`cleveref` is sufficient. The bibliography is inline; BibTeX is unnecessary.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make pdf`. The resulting PDF was rendered and visually checked before
packaging. Font files are not included in the archive.

## Contents and provenance

- `article.tex`, `article.pdf`: the proof and supplementary results.
- `code/verify.py`: independent exact enumerator and coefficient verifier.
- `code/symbolic_checks.py`: optional symbolic checks and asymptotic calculations.
- `data/coefficients.csv`: four sequences through degree 200; column names are
  explicit, and notation is explained in the article.
- `data/b289587_extended.txt`: the target sequence through degree 200, computed
  here; this is **not** an official OEIS b-file.
- `data/*results.json`, `data/verification_log.txt`: executed test results.
- `data/environment.json`: the local tool versions used for reproduction.
- `sources/source_audit.md`: source locations, what each establishes, and scope
  of the priority check.
- `OEIS_note.md`: a concise mathematical note suitable as a starting point for
  an OEIS update. Nothing has been submitted to OEIS.

The source entry attributes the generating-function conjecture to Thomas
Scheuerle on December 23, 2025. Standard results concerning 321-avoiders and
Narayana numbers are credited to the background literature and reproved where
needed. This archive proves the OEIS-listed conjecture; it does not claim that
an exhaustive priority search has excluded every earlier independent proof.
