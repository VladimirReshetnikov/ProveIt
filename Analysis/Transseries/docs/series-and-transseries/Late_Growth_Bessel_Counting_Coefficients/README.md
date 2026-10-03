# Late growth of Bessel counting coefficients

This package accompanies the article `bessel_late_growth.pdf` and its editable
LaTeX source `bessel_late_growth.tex`.

The main theorem proves the late-coefficient conjecture for the rational
quotient A395976(j)/A395977(j), associated with the half-power expansion of
A336293. It gives every fixed inverse-factorial correction, both asymptotic
inverse constructions with rounding-aware integer enclosures, and a leading
late-coefficient corollary for each fixed positive integer number of colors.

The theorem proves eventual positivity, not positivity at every index above
five. It does not separate reduced numerator and denominator growth. The
fixed-order estimates and inverse enclosures have unspecified constants and
cutoffs; the numerical results are not interval-certified. No estimate is
claimed uniformly for a growing number of colors.

(Editorial, 2026-10-02: both inverses are cases of the inversion apparatus of
the canonical transseries volume, which the article does not cite; an editorial
note in the article now cites it. The checksum manifest is not shipped, so
`reproduce.sh` stops at its first step; see "Replay the checks" and the
amendments below.)

## Replay the checks

Requirements: Python 3.10 or newer and mpmath 1.3.0. The preparation environment
used Python 3.12.14. No SymPy or external data downloads are required.

```sh
python3 -m pip install -r requirements.txt
bash reproduce.sh
```

This verifies the distributed manifest, regenerates all five result files,
and checks that their hashes match the distributed results. A run took about
seven seconds in the preparation environment. All paths are relative.
The shell wrapper uses python3 by default; set PYTHON to select another
compatible interpreter, for example `PYTHON=/path/to/python3 bash reproduce.sh`.

**In this repository (editorial, 2026-10-02).** `MANIFEST.sha256` is not
shipped (see "Contents"), and `reproduce.sh` runs
`scripts/verify_manifest.py` first, which reads it, so the wrapper stops at
that step; its `--results-only` and `--pdf-only` comparisons read the same file.
Run the replay itself on a copy of the package instead, because
`scripts/replay.py` writes its five files into `results/` and replaces the
recorded ones, then compare the copy's `results/` with the filed files:

```sh
cp -r Late_Growth_Bessel_Counting_Coefficients /tmp/bessel-replay
cd /tmp/bessel-replay && python3 scripts/replay.py
for f in results/*; do cmp "$f" "$OLDPWD/Late_Growth_Bessel_Counting_Coefficients/$f"; done
```

(run the first command from `docs/series-and-transseries/`). On Windows in
this repository use
`uv run --no-project --with mpmath==1.3.0 python scripts/replay.py`; bare
`python` may not resolve. Since the editorial pass the program writes every
result file with LF line endings on every platform; as delivered it used the
platform's, so on Windows the regenerated files differed from the recorded
ones in their line endings only and the hash comparison failed. On
2026-10-02 the amended program ran completely on a copy in 36 seconds,
high-precision stage included, and reproduced all five recorded files byte
for byte. (At filing, on a heavily loaded machine, the high-precision stage
did not finish within 170 seconds.)

To rebuild the PDF as well:

```sh
bash reproduce.sh --with-pdf
```

The PDF build requires pdfLaTeX and the standard packages listed in the TeX
preamble (including Latin Modern, AMS math, geometry, booktabs, microtype,
and hyperref). TeX Live 2025 / pdfTeX 1.40.26 was used here. The build uses a
fixed SOURCE_DATE_EPOCH and suppresses volatile PDF metadata. A byte-identical
PDF is checked for this toolchain. Other TeX/font versions may produce a
different PDF despite rendering the same mathematics; in that case use
`bash build_pdf.sh` and inspect the output, separately from the default data
replay. Build logs and intermediate files remain in `.build/`.

(Editorial, 2026-10-02: the filed PDF is no longer the delivered one; it was
rebuilt from the amended source with MiKTeX pdfTeX 1.40.29, so the delivered
byte-identity check, which compared with the manifest's digest of the
delivered PDF, no longer applies. `build_pdf.sh` copies its result over the
filed PDF.)

## Contents

- `bessel_late_growth.pdf`, `bessel_late_growth.tex`: article and source
- `scripts/exact_algebra.py`: exact finite rational-series arithmetic
- `scripts/replay.py`: independent exact checks and high-precision checks
- `scripts/README.md`: computation details and limits
- `results/exact_coefficients.json`: d0 through d12 and c0 through c8
- `results/high_precision.json`: independent 200/300-digit computations to d100
- `results/original_sequence_and_inverse.json`: original-count and inverse checks
- `results/late_inverse_models.json`: late smooth-model inverse checks
- `results/numerical_tables.tex`: optional generated tables, independent of the article build
- `provenance/SOURCES.md`: source links and bounded retrieval account
- `build_pdf.sh`, `reproduce.sh`: PDF build and one-command replay
  (`reproduce.sh` needs the retired manifest; see "Replay the checks")
- `scripts/verify_manifest.py`: the manifest check, kept as delivered; it
  fails without `MANIFEST.sha256`

The delivered checksum ledger `MANIFEST.sha256` was verified in full on
filing (17/17) and not kept; the delivered archive remains in the repository
history (the drop zone's batch 77; see `docs/incoming/README.md`).

Exact arithmetic checks prove the finite identities they test. Agreement at
two numerical precisions is a consistency test, not a rigorous floating-point
error certificate. The asymptotic proofs are in the article.

No third-party full texts, repository snapshots, or private working/review
notes are distributed in this package.

## Editorial amendments (ProveIt, 2026-10-02)

Made in the editorial pass after batch 77 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-02)`, every change to the program `ed. (2026-10-02)`.

- `bessel_late_growth.tex`: an unnumbered environment "Editorial note
  (ProveIt, 2026-10-02)" is defined in the preamble (the theorem counter is
  unchanged). Two notes:
  - at the end of Section 7 ("Asymptotic inverses and integer thresholds"):
    both inverses are cases of the inversion apparatus of the canonical
    volume `../Transseries_And_Inversion/transseries_and_inversion.tex`,
    which the article does not cite. The cores `N(log N - 1) = Y` and that
    of `J` are its factorial core (Proposition J.27,
    `p0:prop:factorial-core`, `kappa = 1`, `d = -1` and `d = -1 - log 4`),
    the first also the core of its gamma inverse (`p6:sec:gamma`); the
    corrections are its reversion about an arbitrary core (Theorem J.33,
    `p0:thm:core-reversion`, with the kernel of Remark J.34,
    `p0:rem:core-instances`) on the grid `N^{-1/2}`, resp. `1/J`; the
    mean-value steps are Theorem J.47 (`p0:thm:backward-error`) and the
    two-ceiling enclosures the separation condition of Theorem J.43(2)
    (`p0:thm:staircase`, Definition J.41). The editors repeated both
    reversions symbolically (`A`, `B`, the `N^{-1/2}` coefficient of `r_A`
    and the intermediate formula for `C`; the residual of `r_d`); all agree.
    The method is the volume's; only the coefficients are new to the
    repository.
  - in Section 9, after the delivered sentence that "the manifest checks the
    distributed files": the manifest is not shipped, so `reproduce.sh` stops
    at its first step, and the replay now writes LF.

  One bibliography entry, `ed:tai`, is added after the delivered ones, so no
  reference is renumbered. No label was renamed or removed.
- `bessel_late_growth.pdf`: rebuilt from the amended source with `latexmk`
  (MiKTeX pdfTeX 1.40.29, the `SOURCE_DATE_EPOCH` of `build_pdf.sh`):
  15 pages (14 as delivered); no error, overfull box, undefined reference,
  multiply defined label or duplicate destination, and the one underfull box
  of the delivered build (in the paragraph on the two precision runs) and no
  other; every font is embedded Type 1. Every theorem, equation, table and
  section number is unchanged (checked against the `.aux` of a build of the
  delivered source). The pages carrying the notes were rendered and
  inspected.
- `scripts/replay.py`: the result files are written with LF line endings on
  every platform (as delivered, the platform's, so CRLF on Windows). It still
  writes into `results/` and replaces the recorded files; the checks and the
  outputs are otherwise unchanged. Rerun on a copy: 36 seconds, all five
  files byte-identical to the recorded ones.
- `README.md`: the pointer under the summary, the replay without the
  manifest, the Windows command, the running time, the PDF note, the file
  list, the retired ledger and this section.
- Recorded, not changed: `reproduce.sh` and `scripts/verify_manifest.py`
  (both need the retired manifest), `scripts/README.md` (its "about 7.3
  seconds" is the delivery's figure) and the article's own statement that the
  replay runs in about seven seconds.
