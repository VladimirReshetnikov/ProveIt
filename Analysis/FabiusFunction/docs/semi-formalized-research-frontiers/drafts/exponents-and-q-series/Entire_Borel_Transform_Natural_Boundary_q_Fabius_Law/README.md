# An Entire Borel Transform at a Natural Boundary

**Sharp logarithmic Gevrey asymptotics for a dilation-normalized q-Fabius law**

Research article prepared for Vladimir Reshetnikov, September 30, 2026.
Developed with ChatGPT. The PDF has 23 physical pages.

## Main results

For independent uniform digits U_j on [-1/2, 1/2], the article studies

    F_z(t) = log E exp(z t sum_{j>=0} exp(-j t) U_j),    z real and nonzero.

It proves a complete leading equivalent for the odd asymptotic coefficients,
with a Lambert-W saddle and Gaussian prefactor. Their sharp refined type is

    lim (over odd j) log(j) (|b_j(z)| / j!)^(1/j) = 1/(2 pi).

The formal series is divergent, Gevrey one of zero exponential type, and not
Gevrey of any smaller nonnegative order. Its Borel minor is entire, admits an
exact positive-real-ray Laplace reconstruction, and has an explicit leading
double-exponential equivalent on the imaginary Borel axis. Nevertheless F_z
has a meromorphic natural-boundary interval on the imaginary t-axis. Thus its
entire Borel minor has no uniform exponential bound in any open angular sector
about the positive direction.

A companion frozen-amplitude theorem computes the complete meromorphic Borel
pole set, residues (including collisions), and exact factorial type.

## Scope

The transform is centered and dilation-normalized: its individual digit
amplitude is z t. This is related to the repository's original normalization
by the exact change of variables in equation (2.3); it is not asserted that
every sharp estimate transfers unchanged to a fixed original transform
argument. The separate minimal rational-moment denominator conjecture remains
open in this work. Worldwide publication priority has not been independently
established. No Lean or Rocq compilation was performed.

The theorems have conventional proofs. Exact and numerical tests are included
as supplementary evidence, not as substitutes for those proofs.

## Files

- `q_fabius_borel.tex`: self-contained LaTeX article with embedded bibliography.
- `q_fabius_borel.pdf`: compiled 23-page article.
- `verify_results.py`: reproducible exact and high-precision checks.
- `verification_results.json`: machine-readable receipt from the successful run.
- `verification_run.txt`: text transcript of that run.
- `CLAIM_LEDGER.md`: theorem-level scope and proof status.
- `SOURCE_NOTES.md`: repository pin and source-comparison limitations.
- `build_receipt.json`: PDF compilation and layout checks.
- `requirements.txt`, `Makefile`: dependency and build commands.
- The submitted checksum ledger `SHA256SUMS.txt` (11 entries) was verified in
  full on filing (batch 67 of `docs/incoming/`) and not kept; the delivered
  archive remains in the repository history (see `docs/incoming/README.md`,
  batch 67 row).

## Build

Use a standard TeX Live installation with the packages named in the source.
No external bibliography processor, figure, or separately distributed font is
required. Run `make pdf`, or run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_borel.tex

Three passes are used to stabilize the contents and cross-references.

## Verification

Python 3.10 or later is suitable. The recorded run used Python 3.13.5,
mpmath 1.3.0, and SymPy 1.14.0, with 75 decimal digits.

    python -m pip install -r requirements.txt
    python verify_results.py

Since the editorial pass (below) a plain run, and `make verify`, write to
`rerun_results/` beside the script and leave the recorded
`verification_results.json` and `verification_run.txt` unchanged; both files
are written with LF line endings. To regenerate the recorded files in place:

    python verify_results.py --output-dir .

The script verifies 60 polynomial coefficient identities (495 nonzero
monomial coefficients), 90 numerical zeta/Bernoulli specializations, six
Laplace quadratures, independent imaginary-Borel evaluations, coefficient
asymptotic ratios, and selected boundary-cusp examples. Numerical calculations
are not interval-certified enclosures. The script needs no network once its
Python dependencies are installed.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`. The
byline ("Developed with ChatGPT") is kept as delivered.

- `q_fabius_borel.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). One note, at the end of Section 1.1: the companion article is
  filed beside this package
  (`../Unit_Circle_Barrier_q_Fabius_Transform/q_fabius_boundary.tex`), and
  its Section 11.2 now carries a reciprocal note; Part IX of
  `../geometric_q_fabius_frontiers/` leaves open whether the constants of its
  radial expansion at roots of unity obey a Gevrey bound
  (`p9:status:inverse-analytic`), and these endpoint theorems bear on that
  question without answering it; the conclusion of Theorem 10.2 is the
  phenomenon that
  `Analysis/Transseries/docs/series-and-transseries/Natural_Boundaries_Quadratic_Exponential_Feedback/`
  and `.../Natural_Boundaries_Survive_Nonlinear_Feedback/` prove for
  unrelated functions (reversions of exponential-feedback series); no
  theorem is shared. One marked change: the title page no longer sets page
  anchors (it is numbered 1, like the first arabic page), which removes the
  delivered source's one duplicate-destination warning.
- `q_fabius_borel.pdf`: rebuilt from the amended source with the
  `Makefile`'s three `pdflatex` passes (MiKTeX pdfTeX 1.40.29): 23 pages,
  as delivered, with no error, undefined reference, multiply defined label,
  duplicate destination or overfull box; every font is embedded and none is
  Type 3. Theorem and equation numbers are unchanged, so `CLAIM_LEDGER.md`
  and `build_receipt.json` stay correct. The page carrying the note was
  rendered and inspected.
- `verify_results.py`: the default `--output-dir` is now `rerun_results/`
  beside the script (it was the package directory, so a plain run or
  `make verify` rewrote the recorded files), and both files are written with
  LF line endings on every platform (CRLF on Windows before). A rerun of the
  amended program on a copy (2026-09-30, `uv run --no-project --with
  sympy==1.14.0 --with mpmath==1.3.0 python verify_results.py`, which
  resolved Python 3.13.5) passed; its JSON equals the recorded
  `verification_results.json` except `elapsed_seconds`, and its transcript
  equals `verification_run.txt` except the elapsed-time line.
- `README.md`: the retired ledger, the output location, and this section.
