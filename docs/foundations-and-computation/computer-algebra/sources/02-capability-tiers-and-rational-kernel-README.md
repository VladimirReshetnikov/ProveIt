# Surreal and Surcomplex Numbers in Symbolic Computer Algebra

A detailed article on exact representations, effective algebraic subfields,
certified Hahn sums and precision, analytic germs, exponential/logarithmic
and transseries layers, finite-angle trigonometry, complex branches, and
Wolfram Language architecture.

## Main files

- `surreal_cas.pdf`: the compiled article.
- `surreal_cas.tex`: self-contained LaTeX source with bibliography.
- `code/RationalHahn.wl`: small exact rational-function kernel over Q in
  finitely many hierarchically ordered infinitesimal monomials.
- `code/Checks.wl`: corrected suite of 34 finite checks.
- `code/RunChecks.wl`: driver for loading the package and running the suite.
- `reports/wolfram_verification.md`: actual execution record and limits.
- `sources/`: unchanged copies of the two supplied manuscripts.
- `SHA256SUMS.txt`: checksums for the distribution files.

The two additional archives mentioned inside the supplied trigonometry
manuscript were not supplied for this study. They are not included, and their
code or proofs are not claimed to have been independently reviewed.

## Compile the article

A normal TeX Live or MiKTeX installation with the common packages listed in
the preamble is sufficient. From the archive's root directory:

    pdflatex surreal_cas.tex
    pdflatex surreal_cas.tex

The bibliography is embedded; no BibTeX step or external graphics are needed.
The PDF was compiled with PDFLaTeX and visually inspected through a PDF
renderer. Temporary compilation and page-render files are not distributed.

## Run the reference code

In a fresh Wolfram Language session, from the extracted archive:

    Get["code/RunChecks.wl"]

or in a terminal where wolframscript is installed:

    wolframscript -file code/RunChecks.wl

The prototype implements rational coefficients only. Its ordered variables
{t1,...,td} denote Conway monomials with valuations
1, omega, omega^2, ..., omega^(d-1), respectively. They are not ordinary
numeric variables with small floating-point values. In particular, each next
variable is smaller than every positive ordinary integer power of its
predecessor.

The prototype supports construction, exact rational arithmetic, comparison,
sign, valuation, leading coefficient, and finite standard part. It does not
implement algebraic root extensions, arbitrary Hahn-series streams,
transcendental functions, general complex powers, or a complete surreal CAS.
Those capabilities are discussed as subsequent layers in the article.

The actual verification consisted of a 31/34 initial check evaluation plus
successful reevaluation of the three corrected test expressions. See the
report for the exact distinction between mathematical proofs, finite checks,
and expected local reproducibility.

## Interpretation of the article

Established literature, supplied-manuscript results, elementary deductions
proved in this article, and proposed interfaces are distinguished explicitly.
The article does not claim a complete zero/equality algorithm for arbitrary
computable coefficient streams, a universal finite encoding of all surreals,
a canonical infinite circular phase, or a formal proof of the theory.

Exact denotation, terminating computation, and a certified truncation are
separate representation capabilities throughout.
