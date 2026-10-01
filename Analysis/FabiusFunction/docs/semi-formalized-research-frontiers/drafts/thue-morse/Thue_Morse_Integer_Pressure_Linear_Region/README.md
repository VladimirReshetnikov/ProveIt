# A Linear Positivity Region for Thue Morse Pressure

This bundle contains the seven-page (eight since the editorial amendments below) report, editable LaTeX, reproducible exact checkers, and supporting data.

The theorem proves H_(m,m+s)>0 and positivity of the pressure coefficient at degree 4m+2s whenever m>=2048 and 128s+64<=m. This is a positive region of linear width beyond the first feedback boundary. The full proposed range below degree 6m remains open.

Three new estimates drive the proof: the sharp complete-multipartite matching multiplicity (d-1)_(2s+1), the exponential auxiliary-moment bound S_s<11(4*pi)^(2s), and contraction of the capped transfer operator on the fixed complex disk |a|<=1/16. All are proved in the report.

## Reproducing the checks

Run `python3 code/run_all.py` for the standard-library checks. These verify all 22 linear-strip side conditions, the rational saddle and tangent bounds, all 2,632 strengthened marked-pair profiles, and 35 saved true-response restoration identities.

Run `python3 code/reproduce_all.py` with SymPy installed to reconstruct the rational Fourier systems. It checks every original residual and normalization, recomputes the Schur data for m=2,...,8, and compares every deleted-insertion identity with the full nonlinear eigenvector recursion. These finite computations are supplementary identity checks; the universal linear-strip theorem follows from the analytic proof.

`make pdf` builds on a standard TeX installation. The optional `build_local.sh` creates a local format and uses the installed Debian TeX paths used during preparation. It does not install software or modify global configuration.

The `background` folder preserves the pinned original pressure source and the preceding mathematical reports. The earlier reports are dependencies and context, not silently revised copies. The new argument uses the pre-feedback triangle and the new offset-zero estimate, so it does not require replaying the earlier finite boundary enclosure archive. (The `background` folder was not filed; see the editorial amendments below.)

The final PDF is `article.pdf`; its editable source is `article.tex`. Intermediate page images and TeX format files are excluded from the deliverable archive.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the sixth of thirteen packages of one series, filed beside the
manuscript they continue, `../Thue_Morse_Integer_Pressure/`, in logical order:
the positivity series `../Thue_Morse_Integer_Pressure_First_Positive/`,
`../Thue_Morse_Integer_Pressure_Higher_Positive/`,
`../Thue_Morse_Integer_Pressure_Positive_Triangle/`,
`../Thue_Morse_Integer_Pressure_Feedback_Boundary/`,
`../Thue_Morse_Integer_Pressure_Beyond_Boundary/`,
`../Thue_Morse_Integer_Pressure_Linear_Region/`,
`../Thue_Morse_Integer_Pressure_Full_Range/`, and the sign series, which
imports the full-range theorem,
`../Thue_Morse_Integer_Pressure_Sign_Changes/`,
`../Thue_Morse_Integer_Pressure_Sign_Densities/`,
`../Thue_Morse_Integer_Pressure_Negative_Bound/`,
`../Thue_Morse_Integer_Pressure_First_Negative/`,
`../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/`, with the dataset
`../Thue_Morse_Integer_Pressure_First_Negative_Data/`. An earlier version of
`../Thue_Morse_Integer_Pressure_Full_Range/`, *The Full Pressure Positivity
Range for Large Integer Orders* (`m >= 4096`), was superseded by it and not
filed; neither was a duplicate archive.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Three notes:
  - after Theorem 1.1 and its paragraph: `128s + 64 <= m` implies `s < m`, so
    the pressure half is contained in Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_Full_Range/`; the response positivity in
    the linear region stays this note's own;
  - after the closing paragraph of Section 6: the remaining pressure interval
    up to `6m` is closed by `../Thue_Morse_Integer_Pressure_Full_Range/` (so
    for the pressure alone the width question is settled; for the responses it
    is open); the first negative degree is treated in
    `../Thue_Morse_Integer_Pressure_First_Negative/` and
    `../Thue_Morse_Integer_Pressure_First_Negative_Data/`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited: `[1]` and `[2]` are cited under
    other titles, as in `../Thue_Morse_Integer_Pressure_Beyond_Boundary/`
    (they are `../Thue_Morse_Integer_Pressure/` and
    `../Thue_Morse_Integer_Pressure_Positive_Triangle/`); `[3]` is
    `../Thue_Morse_Integer_Pressure_Feedback_Boundary/` and `[4]` is
    `../Thue_Morse_Integer_Pressure_Beyond_Boundary/`.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 8 A4 pages (7 as delivered),
  332,545 bytes; all 17 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `code/run_all.py`, `code/reproduce_all.py` and the five checkers that write
  records (`verify_saddle.py`, `verify_linear_strip.py`,
  `check_strong_pairs.py`, `check_schur.py`, `check_fixed_offset.py`): new
  option `--output-dir` (default `data/rerun/`; the drivers pass it on), with
  LF line endings. As delivered, every checker overwrote its recorded file in
  `data/`, with CRLF line endings on Windows. Pass `--output-dir data`, on a
  copy, to regenerate the recorded files. A checker that reads another
  checker's record reads the recorded file, as delivered. On the ProveIt
  machine use `py` rather than `python3`/`python`. `run_all.py` still checks
  the recorded identity file in `data/`. Reruns on a copy (2026-10-01, Python
  3.14.4, SymPy 1.14.0): `run_all.py` and `reproduce_all.py` passed; the three
  strip, saddle and pair records and `fixed_offset_identity_checks.json` equal
  the recorded ones byte for byte, the seven Schur records apart from
  `runtime_seconds`.
- The `background/` copies that this README describes (the repository
  manuscript and three earlier reports) were not filed; they are
  `../Thue_Morse_Integer_Pressure/`,
  `../Thue_Morse_Integer_Pressure_Positive_Triangle/`,
  `../Thue_Morse_Integer_Pressure_Feedback_Boundary/` and
  `../Thue_Morse_Integer_Pressure_Beyond_Boundary/`. The submitted checksum
  ledger was retired.
- `Makefile`: kept as delivered; it calls `python3` (use `py` on the ProveIt
  machine), and its `pdf` target runs `pdflatex` here and overwrites the filed
  PDF.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count, a parenthesis after the `background` paragraph,
  and this section.
