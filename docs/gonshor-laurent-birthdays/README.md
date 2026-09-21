# A Laurent-series case of Gonshor's birthday conjecture

Research article prepared for Vladimir Reshetnikov, 20 September 2026.

## Result and status

The article gives a detailed proof of

    b(x*y) <= b(x) (natural ordinal product) b(y)

for every x and y in the canonically embedded field R((omega^(-1))).
It also treats finite normal forms with ordinal exponents, derives exact
birthdays for finite and infinite Laurent series, and proves a reciprocal
corollary. The global conjecture for all surreal numbers is NOT solved here.

The mathematical proof uses the standard surreal normal-form and
sign-expansion theorems. It has not been independently refereed or verified
in a proof assistant. The restricted result is not asserted to be previously
unknown: the literature search did not establish priority.

## Contents

- `article.pdf`: the complete article, including references and proofs.
- `article.tex`: self-contained LaTeX source with an inline bibliography.
- `verify.py`: exact-arithmetic verification and exploratory search.
- `verification_results.json`: output of the completed full verification run.
- `AUDIT.md`: dependencies, edge cases, and scope of verification.
- `build.py`: cross-platform three-pass PDF build helper.
- `layout_audit.json`: final PDF text-boundary checks, page by page.

Third-party source papers and font files are not redistributed.

## Read first

The main result is Theorem 1.2. Its proof is in Section 7.3.
The exact finite Laurent formula is Theorem 5.1. The finite product argument
is Section 6, and the infinite birthday formula is Theorem 7.1.
Section 9 explains why the proof does not cover all surreal numbers.

A crucial notational distinction: `+` in an ordinal birthday expression
means ordinary ordinal addition, while the circled plus and circled times
mean natural ordinal operations. In particular, an infinite Laurent series
has birthday `b(positive part) + omega^2`, with ORDINARY addition.

## Reproduce the verification

Python 3.9 or later; standard library only:

    python verify.py --output verification_results.json

A smoke test:

    python verify.py --quick --output quick_results.json

The full recorded run used Python 3.13.5 and completed in approximately
36 seconds in this environment. Runtime varies. Timestamp, Python-version,
and elapsed-time fields will differ between runs. Compare the mathematical
counts and outcomes instead. Exact random-search equality counts should be reproduced
with the recorded Python version, because sampling algorithms can change
between Python releases:

- 117,649 finite Laurent coefficient patterns: formula agrees with sign expansion.
- 15,625 ordered finite Laurent product pairs: all satisfy the bound; 881 equalities.
- 12,200 designated pairs with a negative tail: the bound is strict in every case.
- 100,000 random dyadic-exponent pairs: all satisfy the bound; 202 equalities.
- 405 dyadic real-length checks, 12 named examples, and 3 ordinal arithmetic checks.

The random seed and ordered sampling list are included in the JSON output.
The random search goes beyond the proved theorem by allowing fractional
dyadic exponents. It is not a proof of that larger case.

## Rebuild the PDF

Install a TeX distribution such as TeX Live or MiKTeX providing pdfLaTeX and
the packages named in `article.tex`, then run:

    python build.py

Alternatively:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

No BibTeX, shell escape, network connection, or external illustration is
required. The document uses New PX text and mathematics, with subdued olive
headings and links. Building locally requires the installed TeX font packages;
the archive itself contains no font files.

## Program representation

An ordinal below omega^omega is represented by a tuple `(a0, ..., an)`,
meaning `omega^n*an + ... + omega*a1 + a0`. Zero is the empty tuple.
Polynomial exponents and coefficients are `fractions.Fraction` values.

`sign_birthday` uses exponent signs and Gonshor's two deletion rules.
`laurent_formula` independently implements the closed formula for integer
exponents. `natural_add`, `natural_multiply`, and `ordinary_add` are distinct
operations. No floating-point arithmetic is used in mathematical comparisons.
