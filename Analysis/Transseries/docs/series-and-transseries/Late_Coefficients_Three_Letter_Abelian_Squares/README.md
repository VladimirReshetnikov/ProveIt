# Late coefficients of three letter abelian squares

This package proves the asymptotic conjecture in OEIS A274600, the late coefficients of A002893. Read `honeycomb_late_coefficients.pdf`; the editable, self-contained source is `honeycomb_late_coefficients.tex`.

## What is proved

- The exact normalized Borel transform and the required complex continuation
- The leading factorial asymptotic and every fixed late correction order, with a rigorous remainder
- The exact physical median, lateral Stokes jump, and every fixed fluctuation order
- Lambert-function inversions for both the late coefficients and the original moment counts
- A convergent Lagrange generator of the inverse exponential sectors, with every fixed-sector remainder

(Editorial, 2026-10-02: the three inversions are cases of the inversion apparatus of the canonical transseries volume, which the article does not cite; an editorial note in the article now cites it. The checksum ledger is not shipped, so `replay.sh` stops at its first step; see "Offline replay" and the amendments below.)

The convergent auxiliary-parameter sector expansion is distinct from its all-fixed-order inverse-power fluctuations. The physical inverse is not the arithmetic mean of the lateral inverses. The note does not classify all farther Borel sheets or prove optimal-truncation/Stokes-smoothing estimates. The source/novelty search is bounded and is documented in the article and `SOURCES.md`.

## Offline replay

Requirements: Python 3.10 or later and mpmath 1.3.0 or compatible. Both replay scripts use no network. The exact arithmetic uses only Python integers and fractions. Numerical checks are consistency tests, not interval-certified proofs.

Run:

    bash replay.sh

The replay verifies the package checksums, checks the 22 displayed OEIS terms, independently matches the first 31 Borel-germ coefficients, generates coefficients through index 500, compares them byte-for-byte with the retained exact baseline, asserts finite sanity bounds for density integrals, the four-term Stokes-integral approximation, and the two Lambert inversions, and writes fresh reports to a temporary directory. It does not overwrite the sealed baseline reports. The temporary directory is removed after a successful replay. The exact inverse-sector family in equations (36c-h) is analytically reviewed; these scripts do not numerically test that family.

**In this repository (editorial, 2026-10-02).** `SHA256SUMS` is not shipped (see "Contents"), and `replay.sh` checks it first (lines 4-14), so it stops there. Run the rest of the replay by hand, from the package directory:

    work=$(mktemp -d)
    cp verify.py verify_analytic.py "$work/"
    python3 "$work/verify.py" && python3 "$work/verify_analytic.py"
    for f in coefficients_0_500.txt verification.json analytic_verification.json; do cmp "$work/$f" "expected/$f"; done

Each program writes its outputs beside itself, hence the copy. `replay.sh` compares only the coefficient file; the loop above also compares the two reports with `expected/`. On Windows in this repository use `uv run --no-project --with mpmath==1.3.0 python` for `python3`. Since the editorial pass both programs write LF line endings on every platform; as delivered they used the platform's, so on Windows all three files differed from `expected/` in their line endings only and the `cmp` of `replay.sh` failed. On 2026-10-02 the amended programs took 5 and 9 seconds on a copy, and all three outputs were byte-identical to `expected/`.

## Rebuilding the article

With an installed TeX Live distribution, run:

    bash build.sh

The source requires standard LaTeX packages: amsmath, amssymb, amsthm, lmodern, microtype, geometry, enumitem, xcolor, hyperref, booktabs, longtable, and array. The script has a local-format fallback for containers with installed but unindexed TeX files. No TeX packages are downloaded. SOURCE_DATE_EPOCH is fixed for reproducibility; byte-identical PDFs also depend on the TeX versions and font installations.

## Contents

- PDF and editable TeX source
- Two verification scripts and offline replay/build entry points
- Exact coefficients through index 500 and the retained numerical reports in `expected/`
- Source bibliography and bounded duplicate-search metadata
- Concise mathematical-check and final visual-QA records

The delivered checksum ledger `SHA256SUMS` was verified in full on filing (12/12) and not kept; the delivered archive remains in the repository history (the drop zone's batch 77; see `docs/incoming/README.md`). `CHECKS.md` still names it and describes the delivered 12-page PDF; it is kept as delivered.

The principal theorem is an analytic proof, not a machine-formalized theorem. No external OEIS submission or repository modification was performed.

## Editorial amendments (ProveIt, 2026-10-02)

Made in the editorial pass after batch 77 of `docs/incoming/` (see `docs/incoming/README.md`); every change to the source is marked `% ed. (2026-10-02)`, every change to a program `ed. (2026-10-02)`.

- `honeycomb_late_coefficients.tex`: an unnumbered environment "Editorial note (ProveIt, 2026-10-02)" is defined in the preamble (remark style; no counter is used). One note, at the end of Section 7 (after the lateral sector family), cites the canonical volume `../Transseries_And_Inversion/transseries_and_inversion.tex`, Part X (chapter `p0:sec:top`), which the article does not cite (its repository searches looked for the sequence numbers and "honeycomb"):
  - late coefficients: the seed (31) solves its factorial core (Proposition J.27, `p0:prop:factorial-core`, `kappa = 1`, `d = log kappa - 1`); (32)-(33) are its reversion about an arbitrary core (Theorem J.33, `p0:thm:core-reversion`, `Lambda = h`), whose first two coefficients are the terms of (32) (recomputed symbolically by the editors); recovering `n` by rounding is Theorem J.43(3) (`p0:thm:staircase`);
  - original moments: (35) is its exact solution of the dominant block (Theorem J.23, `p0:thm:lambert-core`, `a = L`, `b = -1`, branch `W_{-1}` by Corollary J.25, `p0:cor:branch-rule`), and (36) its all-orders reversion around the Lambert core (Theorem J.29, `p0:thm:lambert-centered`) with `Q(t) = -t/4 + t^2/32 + ...`, whose recurrence gives the coefficients `1/(4L)` and `1/(4L^2) - 1/(32L)` of (36);
  - sectors: (36c) is its perturbed inversion (Theorem J.21, `p0:thm:perturbed-inversion`) with `F = M`, `E = D`, `epsilon = t`; the radius of the `t`-disk is the article's own.

  The method is the volume's; only the coefficients are new to the repository. The article has no bibliography, so the note names the volume's path itself. No label was renamed or removed.
- `honeycomb_late_coefficients.pdf`: rebuilt from the amended source with `latexmk` (MiKTeX pdfTeX 1.40.29, the `SOURCE_DATE_EPOCH` of `build.sh`): 13 pages (12 as delivered); no error, overfull or underfull box, undefined reference, multiply defined label or duplicate destination; every font is embedded Type 1. Every section and equation number is unchanged (checked against the `.aux` of a build of the delivered source; the equations carry fixed tags). The two pages carrying the note were rendered and inspected.
- `verify.py`, `verify_analytic.py`: the outputs are written with LF line endings on every platform (as delivered, the platform's, so CRLF on Windows). They still write beside the program; the checks and the outputs are otherwise unchanged. Rerun on a copy: 5 and 9 seconds, all three outputs byte-identical to `expected/`.
- `README.md`: the pointer under "What is proved", the replay without the ledger, the Windows command, the running times, the file list, the retired ledger and this section.
- Recorded, not changed: `replay.sh` (it needs the retired ledger and calls `python3`), `CHECKS.md`, `SOURCES.md` and `build.sh`, which copies its result over the filed PDF.
