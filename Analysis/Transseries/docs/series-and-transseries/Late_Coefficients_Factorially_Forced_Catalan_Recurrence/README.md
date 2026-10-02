# Late coefficients of the factorially forced Catalan recurrence

This package accompanies the article proving the leading formula conjectured in OEIS A260879 and giving every fixed algebraic correction, an exact Stirling transform, selected smooth inverses, and discrete threshold enclosures for both the late coefficients and the original recurrence. A separate chapter proves the exact positive remainder after factorial-basis half truncation, its parity-dependent exponential scale, all fixed scalar corrections, and explicit lower bounds.

(Editorial, 2026-10-02: the smooth inverses are cases of the inversion apparatus of the canonical transseries volume, which the article cites only for its Fubini chapter; editorial notes in the article now cite the apparatus and give the Fubini results by number. The checksum ledger is not shipped, so `replay.sh` stops at its first step; see "Replay in this repository" and the amendments below.)

## Main files

- `late_factorial_coefficients.pdf`: the complete article
- `late_factorial_coefficients.tex`: editable source
- `results/numerical_tables.tex`: generated numerical tables used by the article
- `scripts/verify.py`: exact integer and rational-polynomial checks using Python's standard library
- `scripts/inverse_checks.py`: optional high-precision Gamma/Lambert inverse checks
- `scripts/render_tables.py`: deterministic table generation
- `scripts/remainder_coefficients.py`: nine exact even/odd scalar corrections
- `scripts/remainder_checks.py`: exact half-truncation complement/shape checks and high-index remainder illustrations
- `results/`: recorded calculation outputs, including exact coefficients through index 500
- `provenance/SOURCES.md`: literature links, version details, and scope of the prior-work comparison
- `VALIDATION.md`: review and reproducibility status
- `scripts/verify_manifest.py`: the manifest check, kept as delivered; it fails without `SHA256SUMS`

The delivered checksum ledger `SHA256SUMS` was verified in full on filing (27/27) and not kept; the delivered archive remains in the repository history (the drop zone's batch 77; see `docs/incoming/README.md`). The "Reviewed artifact digests" of `VALIDATION.md` are those of the delivered source and PDF; the table digest still matches `results/numerical_tables.tex`.

## Requirements

- Python 3.11 or newer
- For numerical inverse checks, mpmath 1.3.0 (`python3 -m pip install -r requirements.txt`)
- For rebuilding the PDF, pdfLaTeX/TeX Live with the standard article class and fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools, booktabs, array, microtype, hyperref, and enumitem packages
- Bash for the replay and build wrappers

No network is used by the scripts or replay. Dependency installation, if needed, is a separate optional step. The package does not install software automatically.

## Replay after ordinary Python ZIP extraction

From the directory containing the ZIP:

```sh
python3 -m zipfile -e late-factorial-coefficients-reproducibility.zip extracted
cd extracted/late-factorial-coefficients
bash replay.sh
```

Calling the script with `bash` is intentional: ZIP extraction with Python need not preserve executable permission bits. The full replay verifies the manifest, recomputes all recorded data in a fresh local folder, compares the data byte-for-byte, regenerates tables, and rebuilds the PDF. It reports whether the regenerated PDF is byte-identical to the supplied PDF in the active TeX environment. PDF binary identity across different TeX distributions is not promised.

To perform only the standard-library exact and Decimal checks:

```sh
bash replay.sh --core-only
```

That mode does not require mpmath or TeX. It compares all core outputs but omits the combined table file, because the archived table also contains optional inverse data.

For custom ranges, see `scripts/README.md`. To rebuild only the article:

```sh
bash build_pdf.sh
```

## Replay in this repository (editorial, 2026-10-02)

`SHA256SUMS` is not shipped, and `replay.sh` runs `scripts/verify_manifest.py` first (line 9), which reads it, so both modes stop there. Run the scripts into an empty directory instead and compare, as the replay does; from the package directory:

```sh
out=$(mktemp -d)
python3 scripts/verify.py --output-dir "$out"
python3 scripts/remainder_coefficients.py --output-dir "$out"
python3 scripts/remainder_checks.py --output-dir "$out"
python3 scripts/inverse_checks.py --output-dir "$out"   # needs mpmath
for f in "$out"/*; do cmp "$f" "results/${f##*/}"; done
```

Without `--output-dir` the scripts write into `results/` and replace the recorded files. On Windows in this repository use `uv run --no-project --with mpmath==1.3.0 python` for `python3`. Since the editorial pass the scripts write their JSON files and `numerical_tables.tex` with LF line endings on every platform (the CSV files always were LF); as delivered they used the platform's, so on Windows the byte comparison of `replay.sh` failed for those files. On 2026-10-02 the amended scripts took 4, 3, 14 and 23 seconds on a copy, and all twelve outputs, the optional inverse checks included, were byte-identical to `results/`. The full replay's PDF step (`build_pdf.sh`) overwrites the filed PDF, which since the editorial pass is a MiKTeX build of the amended source, so the delivered byte-identity report does not apply to it.

## Mathematical scope

Every asymptotic error is for a fixed finite order. The manuscript proves the conjectured leading late-coefficient law and its explicit correction expansion. The Gamma models are deliberately selected smooth carriers; no canonical continuous interpolation of the integer sequences is asserted. Ceiling enclosures have existential constants and are not numerical interval certificates.

The factorial-basis cutoff j<n/2 has a proved positive remainder of order n! n^(-1/2)2^(-n), with parity-dependent constants and all fixed algebraic corrections. This is a different truncation rule from the inverse-power series.

The least inverse-power term near k=(log 2)n and the scale n^(-1/2)2^(-n) motivate a research question; an optimal inverse-power truncation remainder is not proved here. The report does not assume Borel continuation or identify a Stokes constant.

The exact recurrence, factorial-series composition framework, and Fubini pole mechanism are prior work and are credited. The bounded source comparison is not a claim of universal priority. No third-party full texts or private working notes are included.

## Editorial amendments (ProveIt, 2026-10-02)

Made in the editorial pass after batch 77 of `docs/incoming/` (see `docs/incoming/README.md`); every change to the source is marked `% ed. (2026-10-02)`, every change to a program `ed. (2026-10-02)`.

- `late_factorial_coefficients.tex`: an unnumbered environment "Editorial note (ProveIt, 2026-10-02)" is defined in the preamble (the theorem counter is unchanged). Three notes:
  - after Lemma 4.1: the chapter the article credits, "The Fubini numbers: an exact pole lattice" of the canonical volume `../Transseries_And_Inversion/transseries_and_inversion.tex` (`q2:sec:fubini`), proves the exact form of the lemma: its Theorem V.6 (`q2:thm:weighted`) is the convergent pole sum for `M_N(v)`, Theorem V.1 (`q2:thm:fubini`) its case `v = 1`, and its pole-tail bounds (Theorem V.4, `q2:thm:pole-tail`) with `rho` replaced by `rho(eta)` give the uniform remainder. The note also records that the volume's Remark V.7 (`q2:rem:weighted`) has the direction reversed (it says the leading-pole approximation degrades as the weight grows and asks for the minimum of `rho`; the ratio `rho(v)/|rho(v) + 2 pi i m|` tends to 0 as `v -> infinity` and to 1 as `v -> 0`, so the maximum is needed, as the article's `v >= eta` presumes). The volume itself is not changed here.
  - at the end of Section 7: both smooth inverses are cases of the volume's inversion apparatus (Part X, `p0:sec:top`), which the article does not cite: the seeds solve its factorial core (Proposition J.27, `p0:prop:factorial-core`), the first shifts are the first coefficients of its reversion about an arbitrary core (Theorem J.33, `p0:thm:core-reversion`; both recomputed by the editors), for `J = 0` the original-sequence inverse is its gamma inverse (Theorem Q.25, `p6:thm:gamma`) shifted by one, the residual-to-root steps are its Theorem J.47 (`p0:thm:backward-error`) and the last sentence of Corollary 7.2 the separation condition of its Theorem J.43(2) (`p0:thm:staircase`). It points to the sibling package `../Factorial_Transseries_OEIS_A006014/`, whose note gives the same dictionary for A006014. The method is the volume's; the A260879 and A229741 data are new to the repository.
  - in Section 9, after the delivered sentence on the SHA-256 manifest: the manifest is not shipped, so `replay.sh` stops at its first step, and the scripts now write LF.

  One bibliography entry, `ed:tai`, is added after the delivered ones, so no reference is renumbered. No label was renamed or removed.
- `late_factorial_coefficients.pdf`: rebuilt from the amended source with `latexmk` (MiKTeX pdfTeX 1.40.29, the `SOURCE_DATE_EPOCH` of `build_pdf.sh`, the filed `results/numerical_tables.tex`): 18 pages (16 as delivered); no error, overfull or underfull box, undefined reference, multiply defined label or duplicate destination; every font is embedded Type 1. Every theorem, equation, table and section number is unchanged (checked against the `.aux` of a build of the delivered source). Two of the pages carrying the notes (Lemma 4.1, Section 7.1) were rendered and inspected.
- `scripts/verify.py` (its `write_json`, also used by `inverse_checks.py`), `scripts/render_tables.py`, `scripts/remainder_coefficients.py`, `scripts/remainder_checks.py`: JSON and TeX outputs are written with LF line endings on every platform (as delivered, the platform's, so CRLF on Windows); the CSV writer already wrote LF. Default output locations, checks and outputs are otherwise unchanged. Rerun on a copy: 4, 3, 14 and 23 seconds, all twelve outputs byte-identical to `results/`.
- `README.md`: the pointer under the summary, the file list, the retired ledger and the delivered digests of `VALIDATION.md`, the replay without the ledger, and this section.
- Recorded, not changed: `replay.sh` and `scripts/verify_manifest.py` (both need the retired ledger), `VALIDATION.md` (its digests and page count describe the delivered source and PDF), `scripts/README.md`, `build_pdf.sh`.
