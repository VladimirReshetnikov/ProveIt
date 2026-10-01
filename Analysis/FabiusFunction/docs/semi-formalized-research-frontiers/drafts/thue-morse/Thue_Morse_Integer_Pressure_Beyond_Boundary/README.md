# Positivity Beyond the First Thue Morse Feedback Boundary

This bundle contains the seven-page (eight since the editorial amendments below) research report, editable LaTeX, exact mathematical checkers, and their saved results.

The report proves a fixed-offset asymptotic for H_(m,m+s), and positivity of both H_(m,m+s) and the degree-(4m+2s) pressure coefficient under either sufficient condition:

- m >= 800(s+1)^2
- m >= 2048 and 200(s+1) log(2m) <= m, with natural logarithm

The full proposed pressure range strictly below degree 6m remains open. These are ordinary mathematical results, not a Lean formalization or a priority claim.

## Verification

`python3 code/run_all.py` uses only the standard library. It checks exact cutoff inequalities, the saddle interval, 2,632 marked-pair profiles, 195 saved Schur pressure decompositions, and 35 saved restoration identities.

`python3 code/reproduce_all.py` requires SymPy. It reconstructs the rational Fourier matrices, checks every original linear-system residual and normalization, recomputes the Schur coefficients for m=2,...,14, and recomputes the deleted-insertion identities against the full nonlinear eigenvector recursion for m=2,...,8. The Schur pressure values are compared to the separately obtained direct phase-eigenvalue data in `data/direct_phase_reference.json`. The successful run is recorded in `data/full_replay.log`.

`python3 code/recompute_phase.py 2 3 4 5` optionally regenerates direct phase-eigenvalue pressure values. Pass additional moment orders through 14 for a larger independent replay. This is slower than the Schur recurrence.

The asymptotic and growing-strip theorems do not depend on a finite search. The scripts check exact identities and elementary side conditions used in the proof.

## Building the PDF

On a standard TeX installation run `make pdf`. The optional `build_local.sh` uses explicit paths for the Debian TeX installation used during preparation, creates only local build files, and runs two LaTeX passes.

The `background` folder preserves the pinned original pressure source and the preceding triangle/boundary LaTeX reports without edits. They supply the previously proved spectral normalization and strict tangent comparison. The new pressure proof uses the pre-feedback triangle plus the new offset-zero estimate, so it does not require replaying the earlier boundary's finite enclosure archive. (The `background` folder was not filed; see the editorial amendments below.)

The final PDF is `article.pdf`; the main source is `article.tex`. Intermediate renderings and local TeX format files are excluded from the source archive.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the fifth of thirteen packages of one series, filed beside the
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
  - after Theorem 1.1 and its paragraph: both sufficient conditions imply
    `s < m`, so the pressure half is contained in Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_Full_Range/`; the response positivity and
    the fixed-offset asymptotic stay this note's own (`s = 0` is
    `../Thue_Morse_Integer_Pressure_Feedback_Boundary/`);
  - after the closing paragraph of Section 6: the conjecture `E_{m,r} > 0` for
    `1 <= r < 2m`, also called open in the abstract, is proved in
    `../Thue_Morse_Integer_Pressure_Full_Range/` and is sharp (`E_{2,4} < 0`);
    the rate near 6.662966658 is now the theorem
    `N_m = gamma m - log log(2m)/Lambda + O(1)` of
    `../Thue_Morse_Integer_Pressure_First_Negative/`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited: `[1]`, cited as *Integer Thue-Morse
    Pressure*, is `../Thue_Morse_Integer_Pressure/` (*Integer Pressure and a
    Missing Taylor Coefficient*); `[2]`, cited as *The Full Pre Feedback
    Positivity Triangle for Thue Morse Pressure*, is
    `../Thue_Morse_Integer_Pressure_Positive_Triangle/` (*The Full Positive
    Triangle in Integer Thue Morse Pressure*); `[3]` is
    `../Thue_Morse_Integer_Pressure_Feedback_Boundary/`.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 8 A4 pages (7 as delivered),
  354,162 bytes; all 18 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `code/run_all.py`, `code/reproduce_all.py` and the five checkers that write
  records (`verify_previous_saddle.py`, `verify_explicit_strip.py`,
  `check_marked_pairs.py`, `check_schur.py`, `check_fixed_offset.py`): new
  option `--output-dir` (default `data/rerun/`; the drivers pass it on), with
  LF line endings. As delivered, every checker overwrote its recorded file in
  `data/`, with CRLF line endings on Windows. Pass `--output-dir data`, on a
  copy, to regenerate the recorded files. A checker that reads another
  checker's record reads the recorded file, as delivered. On the ProveIt
  machine use `py` rather than `python3`/`python`. `run_all.py` still checks
  the recorded Schur and identity files in `data/`; after `reproduce_all.py`,
  compare `data/rerun/` with `data/`. Reruns on a copy (2026-10-01, Python
  3.14.4, SymPy 1.14.0): `run_all.py` passed and wrote its three records equal
  to the recorded ones byte for byte; `reproduce_all.py` passed in 136 s and
  wrote the 13 Schur records equal to the recorded ones apart from
  `runtime_seconds`, and `fixed_offset_identity_checks.json` byte for byte.
- `code/verify_explicit_strip.py` (line 30) and
  `data/explicit_strip_checks.json` say that the analytic inequalities are
  proved in `explicit_strip_proof.md`; that file was not delivered. The
  inequalities are proved in Section 6 of the article.
- The `background/` copies (the repository manuscript, the triangle and the
  boundary articles) that this README describes were not filed; they are
  `../Thue_Morse_Integer_Pressure/`,
  `../Thue_Morse_Integer_Pressure_Positive_Triangle/` and
  `../Thue_Morse_Integer_Pressure_Feedback_Boundary/`. The submitted checksum
  ledger was retired.
- `Makefile`: kept as delivered; it calls `python3` (use `py` on the ProveIt
  machine), and its `pdf` target runs `pdflatex` here and overwrites the filed
  PDF.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count, a parenthesis after the `background` paragraph,
  and this section.
