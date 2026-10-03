# Canonical Thue–Morse pressure clusters

This package contains a nine-page (eight as delivered) mathematical report, its LaTeX source,
portable exact arithmetic checks, and an unchanged companion containing the
previous first-negative theorem and the analytic prerequisites used here.

## Results

For every fixed canonical Schur cluster index k, the report identifies its
leading proportional-degree coefficient asymptotic. The multiplier is the
classical rooted-tree constant (-1)^(k-1) 2 k^(k-1)/k! times
(log_2(2m))^(k-1). The permitted compact saddle window is enlarged by a new
weighted Green estimate on |a| <= 1/2, valid for even d = 2m >= 256.

The appendix characterizes the exact branch-admissibility threshold of this
particular product envelope and certifies a rational bracket for that threshold.
It is not a spectral-singularity assertion.

The cluster index is fixed. The report does not sum all clusters, identify a
later full-pressure sign transition, or assert a uniform Lambert-W approximation.
This is unrefereed ordinary mathematics, not a Lean formalization.

## Files and checks

- article.pdf and article.tex: the report
- checks/check_cluster_algebra.py: exact Lagrange and rooted-tree algebra through k=12
- checks/verify_green_half.py: exact scalar facts and contraction at radius 1/2
- checks/verify_envelope_threshold.py: two exact signs bracketing the unique threshold
- checks/*.json: reproducible exact outputs
- inputs/: unchanged preceding report PDF, TeX and full source archive (not filed; see the editorial amendments below)
- PROVENANCE.json: exact input and file hashes

All new checks require only Python 3 standard-library modules. Run from this directory:

    python -O checks/check_cluster_algebra.py
    python -O checks/verify_green_half.py
    python -O checks/verify_envelope_threshold.py
    python -O verify_package.py

The first three commands replace their corresponding JSON outputs (since the editorial amendments below they write checks/rerun/ instead). The threshold
checker imports the scalar checker locally and therefore also replays it.
The finite algebra checks are regressions for the general proof, not substitutes
for it. The scalar rational inequalities certify the stated analytic constants.
No floating-point decision enters these checks.

For a standard TeX Live installation, run pdflatex twice on article.tex. Required
packages are amsmath, amssymb, amsthm, mathtools, geometry, lmodern, microtype,
hyperref and xurl. build_local.sh supplies the explicit font/format setup used
in the preparation environment; no installation or network access is needed.
The bundled input archive has its own portable instructions and certificates.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the twelfth of thirteen packages of one series, filed beside the
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
  - after Theorem 1.1 and its paragraph: for `k = 2` (`C_2 = -K_2`) it
    contains Proposition 3.1 of
    `../Thue_Morse_Integer_Pressure_First_Negative/` and extends its window
    from `(2, 2 mu(arctan(2/5)))` to `(2, 2 sigma_R)`; that package's main
    theorem is neither restated nor re-proved;
  - at the end of Section 6, a Lean crosswalk: (3) is an instance of the
    Lagrange-Buermann formula `Fabius.Lagrange.coeff_subst_derivative`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/LagrangeInversion.lean`),
    the instantiation not formalized; the principal Lambert branch appears as
    `Fabius.cayleyTree` (`CayleyTreeFunction.lean`), its Taylor coefficients
    do not; no statement of the article is formalized;
  - then a series map (`[1]` is
    `../Thue_Morse_Integer_Pressure_First_Negative/`).
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 9 A4 pages (8 as delivered),
  382,657 bytes; all 21 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `checks/check_cluster_algebra.py`, `checks/verify_green_half.py`,
  `checks/verify_envelope_threshold.py`: new option `--output-dir` (default
  `checks/rerun/`), with LF line endings. As delivered, every checker
  overwrote its recorded file beside itself, with CRLF line endings on
  Windows. Pass `--output-dir checks`, on a copy, to regenerate the recorded
  files. A checker that reads another checker's record reads the recorded
  file, as delivered. On the ProveIt machine use `py` rather than
  `python3`/`python`. As delivered, the four-command sequence above failed on
  Windows: after the checkers had rewritten their JSON with CRLF,
  `verify_package.py` reported a SHA-256 mismatch; the checkers now leave the
  recorded files alone. Reruns on a copy (2026-10-01, Python 3.14.4, standard
  library, `py -O`) passed and wrote all three records equal to the recorded
  ones byte for byte.
- `verify_package.py`: as filed, it stopped with `FileNotFoundError`, because
  the three `inputs/` copies listed in `PROVENANCE.json` were not filed (they
  are `../Thue_Morse_Integer_Pressure_First_Negative/`, its PDF and its source
  archive). It now reports absent files and checks every filed one.
  `PROVENANCE.json`: the recorded SHA-256 values of the files changed in this
  pass (`article.tex`, `article.pdf`, `README.md`, `verify_package.py` and the
  three checkers) were recomputed; its other entries are as delivered.
  `py -O verify_package.py` passes on the filed package (11 files checked, 3
  not filed).
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count, the `inputs/` lines, the command list, and this
  section.
