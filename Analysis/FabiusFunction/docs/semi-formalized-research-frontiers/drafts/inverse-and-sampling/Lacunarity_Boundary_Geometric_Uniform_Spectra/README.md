# The Lacunarity Boundary

**Two-Moment Rigidity and Sharp Recovery of Geometric Uniform Spectra**

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

## Main result

For independent uniforms U_j on [-1,1], let X_a = sum_j a_j U_j.
Under a_(j+1) <= a_j/2 and sum_j a_j^2 = 1/3, the article proves

    sup_j |a_j - 2^(-j)|^2 <= (75/4) (19/675 - E[X_a^4]).

The fourth-moment deficit is nonnegative and vanishes only at the exact
dyadic spectrum. The resulting full-spectrum inverse modulus is exactly
Theta(sqrt(epsilon)) in total variation and Kolmogorov distance, including
in the predecessor's precisely defined infinitely smooth class.

Additional proved results include exact support rigidity, local prefix
conditioning Theta(2^r), testing sample complexity Theta(delta^(-4)), honest
reference-point confidence contraction of order N^(-1/4), and extensions to
geometric and nongeometric relative-ratio reference cones.

This answers the question titled "The sharp separation boundary rho=1/2"
in the repository article identified in SOURCES.md. The supercritical
comparison is a result attributed to that predecessor; the critical proofs
are independent of its unformalized quantitative theorems.

## Contents

- `article.pdf`: compiled research article.
- `article.tex`: complete self-contained LaTeX source, including bibliography.
- `code/verify.py`: standard-library exact rational regression checks.
- `results/verification.json` and `.txt`: recorded run with 29,776 assertions.
- `results/witness_diagnostics.csv`: 65-digit Decimal evaluations of explicit formulas.
- `results/build_report.txt`: compilation and PDF validation summary.
- `PROOF_AUDIT.md`: theorem dependencies and limitations.
- `SOURCES.md`: pinned repository provenance and primary literature.
- `Makefile`: optional build and verification commands.

## Reproduce

Compile with a TeX distribution containing the packages listed at the top
of `article.tex`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively, run `pdflatex article.tex` repeatedly until references stabilize.
No shell escape, downloaded assets, or network access is required.

Run the computational checks with Python 3.10 or later:

    python code/verify.py

The program uses only the standard library and writes by default to
`results-rerun/`, preserving the recorded output; since the editorial pass
(below) all three files are written with LF line endings on every platform.
To select another output location:

    python code/verify.py --output-dir /path/to/output

## Verification status

The universal claims are supported by the conventional mathematical proofs
in the article. The code checks finite instances and algebraic identities;
it is not a replacement for those proofs and is not formal verification.
The analytic Hellinger estimates are not certified by numerical integration.
Decimal outputs are diagnostics, not outward-rounded interval enclosures.

No Lean build was run. The manuscript has not been independently peer
reviewed. The contribution is presented relative to an explicitly documented
repository question; exhaustive literature priority has not been established.
No ProveIt repository files were changed.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`. The
`pdfauthor` and title-page wording ("prepared with ChatGPT",
"AI-assisted") is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). Two notes:
  - after equation (3.8), `m_4(a^0) = 19/675`: `X_{a^0}` has Rvachev's `up`
    law, and its fourth moment `19/675` is machine-checked as
    `Fabius.upMoment_four` (from `Fabius.moment_two`) in
    `Analysis/FabiusFunction/Lean/FabiusFunction/OrthogonalPolynomialJacobi.lean`,
    which the article does not cite; no result of the article is
    formalized;
  - in Section 10.2, after the question mapping: the answered question in
    `../Anchored_Dyadic_Recovery_Uniform_Spectrum/` now carries a
    reciprocal note; at the dyadic reference the article also settles the
    boundary case `q = 1/2` that the editorial note to "Geometrically
    separated classes" in `../Recovering_Uniform_Factors_Fabius_Rvachev/`
    leaves open; and `../Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/`
    proves, for a finite list of uniform factors, that the optimal anchored
    exponent is `1/2` whenever the reference has a repeated positive scale
    or a zero slot (`thm:anchored`), of which Theorem 4.5 is an
    infinite-spectrum counterpart at the dyadic reference, proved
    independently.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (MiKTeX pdfTeX 1.40.29): 22 pages, as delivered, with no error, undefined
  reference, multiply defined label, duplicate destination or overfull box;
  no Type 3 font. The two pages carrying the notes were rendered and
  inspected. `results/build_report.txt` describes the delivered build and
  is still accurate in every line.
- `code/verify.py`: the three outputs are written with LF line endings on
  every platform (CRLF on Windows for the JSON and text files, and CRLF
  everywhere for the CSV, before). A rerun of the amended program on a copy
  (2026-09-30, `py code/verify.py`, Python 3.14.4) passed all 29,776
  assertions and reproduced `results/witness_diagnostics.csv` byte for
  byte; `verification.json` and `verification.txt` differ only in the
  Python version.
- `README.md`: the line-ending sentence and this section.
