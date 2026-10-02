# A Pole Hierarchy for Valley-Monotone Compositions

Research article and reproducible checks, October 1, 2026.

## Read first

`article.pdf` is the typeset article; `article.tex` is its complete,
self-contained LaTeX source. The report addresses Conjecture 2.3 of:

Rigoberto Flórez, José L. Ramírez, and Diego Villamizar,
*Restricted bargraphs and unimodal compositions*, Journal of
Combinatorial Theory, Series A 208 (2024), 105934.
DOI: https://doi.org/10.1016/j.jcta.2024.105934

The target counts compositions whose interior valley-plateau heights
are weakly increasing, equivalently non-decreasing bargraphs by area.
Its renewal kernel is an exact transform of the generating function
of OEIS A001523 (weakly unimodal compositions).

This is NOT a claim that the already-known leading asymptotic of A001523
was open. An OEIS number for the target bargraph-area sequence was not
verified; the report does not invent one.

## Results developed in the article

* A proof of the conjectured pure-exponential growth form, with exact
  constants, an exponentially smaller remainder, and rational interval
  certificates. The numerical estimates printed in the 2024 paper are
  reproduced as finite-area (n=100) approximations, not limiting constants.
* Infinitely many genuine simple positive poles tending to 1, with
  alternating residue amplitudes. This implies non-D-finiteness of the
  generating function and non-P-recursiveness of its coefficients.
* Finite-pole expansions with a remainder for each admissible radius
  below 1, allowing nonreal poles and multiplicities.
* A central limit theorem for the number of lowest-level valleys and
  a limiting, exponentially tight terminal component.
* All inverse-logarithmic orders of pole accumulation, expressed using
  Lambert W, and an asymptotic inversion of the positive-pole count.
* Inversion of specified finite-sector interpolants, with explicit
  qualifications for integer threshold rounding.

The article distinguishes prior generating-function results from its
analytic developments and contains six further research directions.
Conventional proofs have been checked within this work, but no Lean
formalization, independent peer review, or exhaustive priority audit is
claimed. Numerical evidence is kept separate from proved assertions.

## Exact verification (no dependencies)

With Python 3.10 or later, run in this directory:

    python verify.py

Do not use Python's `-O` option, because the test runner uses assertions.
The program overwrites `verification.json` with its results. It checks:

1. Integer coefficient calculations through area 200.
2. Independent exhaustive enumeration through area 17, and minimum-part
   restrictions 2 and 3 through area 13.
3. Agreement with A001523's supplied initial terms through area 20.
4. Rational enclosures of rho, lambda=1/rho, and C, with rigorous infinite
   tails and outward rounding at 90 decimal places. Arithmetic uses only
   Python integers and fractions; no floating point is used here.

Finite enumeration checks the implementation, not the infinite
asymptotic theorems. The interval certificate proves the stated numerical
bounds subject to its transparent arithmetic implementation and the
analytic tail inequalities proved in the article.

## Optional symbolic and numerical checks

Install the optional dependencies:

    python -m pip install -r requirements-optional.txt

Then run:

    python expansion.py
    python numerics.py

`expansion.py` computes six exact polynomial coefficients in c=log(2)
and verifies the formal implicit-equation residual. It writes
`expansion_coefficients.json`.

`numerics.py` writes `numerical_results.json` with high-precision
exploratory poles, amplitudes, limit-law constants, and convergence data.
Its fixed-cutoff numerical values are NOT additional rational
certificates. In particular, it does not certify an ordering of nonreal
poles, a natural boundary, or a uniform large-minimum-part approximation.

## Build the PDF

A standard LaTeX installation with pdfLaTeX, Latin Modern, AMS packages,
geometry, microtype, booktabs, hyperref, and the other packages listed in
the preamble is sufficient:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

On a POSIX system, `sh build.sh` runs these commands.

## Source and repository boundary

See `SOURCE_NOTES.md` for bibliography, overlap checks, and limitations.
No repository file was changed. No downloaded research paper, private
file, or font file is included. Only the generated article, code, and
computational outputs are bundled.
