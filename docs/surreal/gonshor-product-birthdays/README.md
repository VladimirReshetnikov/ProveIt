# Gonshor's Product-Birthday Conjecture
## An exact formula for ordinal-support series

Research draft dated 20 September 2026.

**Outcome:** a proof of the conjectured bound on a specified ring of surreal
numbers, with an exact birthday formula and an equality classification.
**The conjecture for arbitrary surreal numbers is not solved here.** Historical
priority for this special-case result has not been established. The written
proofs have not been checked in a proof assistant or independently peer reviewed.

The ring consists of Conway normal forms

    x = sum_{alpha in S} c_alpha omega^(-alpha),

where S is any set of ordinals and the coefficients are nonzero real numbers.
The exponent -alpha means the surreal negative of an ordinal. Arbitrary negative
surreal exponents are not included. The mathematical theorem allows transfinite
support; the executable code handles finite support only.

## Files

- `surreal_product_birthdays.pdf`: the 20-page article with proofs and sources.
- `surreal_product_birthdays.tex`: self-contained LaTeX source, with bibliography.
- `references.bib`: reusable BibTeX records (not required to compile the article).
- `code/ordinal_series.py`: exact ordinal arithmetic and finite-support series code.
- `code/verify.py`: deterministic tests and result generation.
- `verification.json`: the recorded test result shipped with this archive.
- `Makefile`: optional build, verification, and cleanup commands.

## Main conclusions

For every pair x,y in the ring, the canonical sign length satisfies

    ell(x*y) <= ell(x) natural_product ell(y).

Equality holds exactly when a factor is zero, a factor is +1 or -1, or both
factors are ordinary integers. If both birthdays are infinite, the inequality
is strict. The exact endpoint formula distinguishes support without a maximum,
a non-dyadic last coefficient, and a dyadic last coefficient with one of two
possible endpoint corrections. Ordinary ordinal operations and natural ordinal
operations are explicitly distinguished throughout the article.

For finite supports, a product's birthday is determined by the coefficient at
each maximum support index and its immediate predecessor. Constructing the
complete product is unnecessary. The executable rational case decides exact
dyadic status from reduced denominators; for arbitrary real coefficients, the
formula assumes those exact decisions and does not supply an algorithm for
computable-real names.

## September 22 proof review

The proof review retains the stated theorem and equality classification. It
expands the cofinal-support squeeze at limit stages, the leading-coefficient
argument for strictness under dyadic scaling, and the finite endpoint proof.
That proof now explains why the maximum product index has only one
contribution, and why a first Cantor-coefficient difference restricts the
predecessor to exactly two possible contributions. A new example contrasts
their cancellation to zero with their sum being non-dyadic.

The local-ring inverse proof now uses an explicit finite geometric identity at
each prescribed index, with the Cantor weight supplying the cutoff, including
at index zero. The notation distinguishes finite magnitude from finite birthday
and records `t^alpha = omega^(-alpha)`, whose ordinal indices multiply by natural
addition.

The imported all-minus sign rule was rechecked against Bournez–Guilmant,
arXiv:2201.08199v1, Definition 2.20 and Theorem 2.21 (printed page 13).
The two added cancellation examples agree in all three existing birthday
evaluators. The historical code and `verification.json` remain unchanged;
the recorded exhaustive and random suites below were not rerun in this review.

## Run the exact checks

Requires Python 3.10+ and its standard library. No external packages or network
access are needed. Run from this directory:

```sh
python code/verify.py --output verification-rerun.json
```

The default seed is 20260920 and the default random sample is 20,000 pairs.
The run also checks 76,636 exhaustive unordered product pairs, 64,401 exhaustive
endpoint computations, and separate elementary tests. The endpoint and block
evaluators share ordinal arithmetic and the classical sign theorem, so their
agreement is a consistency test, not independent formal verification.
Do not run Python with `-O`, which disables assertions; the script rejects it.

The supplied result is PASS. Elapsed time and Python version can vary between
machines; the mathematical assertions and deterministic counts do not depend
on elapsed time.

```sh
python code/verify.py --seed 42 --random-pairs 100000 --output larger-run.json
```

Finite testing does not establish the transfinite-support theorem. See the
article's induction proof and the discussion of cofinal support endpoints.
No general surreal canonicalizer is implemented.

## Use the module

This example can be run from the `code` directory, or with that directory on
Python's module search path:

```python
from fractions import Fraction
from ordinal_series import (
    ZERO, ONE, birthday_endpoint, birthday_product_fast, multiply,
)

# Indices denote omega^(-alpha): ONE is the infinitesimal omega^(-1).
x = {ZERO: Fraction(1, 3), ONE: Fraction(1)}
y = {ZERO: Fraction(3)}

assert birthday_endpoint(x).as_text() == "omega + 1"
assert birthday_product_fast(x, y).as_text() == "omega + 2"
assert birthday_product_fast(x, y) == birthday_endpoint(multiply(x, y))
```

`Ordinal((a0, a1, ..., ak))` denotes `omega^k*ak + ... + omega*a1 + a0`.
Only ordinals below omega^omega are represented. Coefficients must be `int`
or `Fraction`, not floating-point numbers. The implementation separates
`ordinary_add`, `natural_add`, and `natural_multiply` explicitly.

## Build the PDF

A conventional TeX installation with pdfLaTeX and the packages named in the
preamble is sufficient. The source contains its own bibliography; BibTeX is
not required. From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
```

Alternatively use `make all`. Three passes ensure stable references and contents.
`make verify` runs the default checks and replaces `verification.json`.
`make clean` removes intermediate TeX files without deleting the PDF.

The September 22 revision and the original baseline were each built with three
passes. Both final logs have no warnings, undefined references, or overfull or
underfull boxes. The revised PDF has 20 pages (baseline: 19); physical pages 4,
6–7, 9, 11–13, 15, and 19 were rendered and visually inspected around the changes.
The archive does not include third-party papers, books, font files, or a compiled
proof-assistant artifact. Source provenance and the limits of the literature
search are stated in the article.
