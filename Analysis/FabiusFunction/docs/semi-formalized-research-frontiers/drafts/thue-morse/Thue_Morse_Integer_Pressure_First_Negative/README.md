# First negative degrees in integer Thue–Morse pressure

The article proves the asymptotic location of the first negative even phase Taylor coefficient above the cancellation at degree 2m:

    N_m = gamma*m - loglog(2m)/Lambda + O(1)

The constants are defined by a positive-series saddle equation. Exact rational checks place gamma strictly between 6.662966 and 6.662968, below 20/3. The coefficient 1/Lambda is approximately 1.240284909.

A further corollary gives the next-even-integer rule for an explicit saddle center when that center is outside an existential C/log(2m) neighborhood of the even lattice. The report gives no effective onset, no unconditional exact floor rule, and no claim about the frequency of close lattice approaches.

This is an unrefereed ordinary mathematical proof with exact compact-domain interval certificates, not a Lean formalization. Finite first-negative tables are supplementary and are not used to infer the theorem.

## Read the proof

- `article.pdf` and `article.tex` contain the complete new analytic argument and describe every imported estimate
- `inputs/all_integer_orders.pdf` and its unchanged source archive supply the weighted C1 Green theorem, dyadic tangent comparison and earlier all-order positivity result
- `inputs/eventual_66.pdf` and `.tex` supply positivity at all earlier degrees for sufficiently large orders and the third-Schur-term bound
- `inputs/infinite_sign_changes.pdf` supplies existence of N_m
- `inputs/repository_integer_pressure.tex` is the pinned repository source
- `inputs/independent_outer_certificate.zip` is a separate portable replay bundle for the outer contour, copied unchanged
  (of the `inputs/` entries only this archive was filed; see the editorial amendments below)

## Replay the exact certificates

The new checkers need only Python3 and its standard library. No network access or third-party package is needed. Run from the package directory:

    python3 -O checks/verify_model_crossing.py
    python3 -O checks/verify_contour_side_conditions.py
    python3 -O checks/verify_frozen_real_constants.py
    python3 -O checks/verify_local_complex_arc.py
    python3 -O checks/verify_sharp_certificate.py

The first also replays the preceding 6.6 endpoint checks. The local checker certifies 127 rational boxes with strict domain slack. The compact outer replay reconstructs the exact binary partition and checks all 2812 boxes, proving eta=1999/2000. Its runtime is about one minute on the production system. All failure checks remain active under Python's optimization flag.

Optional regeneration of the compact outer partition:

    python3 -O checks/produce_sharp_outer.py

Regeneration rewrites the certificate, with elapsed timings that may differ. Mathematical bounds and the deterministic partition are unchanged. Validate SHA256SUMS before regeneration if checking the original archive identity (`SHA256SUMS` was retired on filing; not in the repository).

The independent outer ZIP contains a separate saved-leaf replay and saddle-range check. Its README gives the two commands. The logarithmic spatial derivative proof is included there.

## Build the paper

A standard TeX Live installation with pdfLaTeX, AMS packages, geometry, Latin Modern, microtype, hyperref and xurl can compile `article.tex`. The included `build_local.sh` performs two passes and also supports the explicit TeX/font paths used in production.

The asymptotic proof uses a uniform local limit theorem; no finite list of coefficient checks replaces that argument. Conversely, the finite interval boxes certify only the compact scalar inequalities, whose operator and coefficient consequences are proved in the article.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the eleventh of thirteen packages of one series, filed beside the
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
  - after Theorem 1.1 and its paragraph: it implies the `liminf` bound of
    `../Thue_Morse_Integer_Pressure_Negative_Bound/` (not its strict
    positivity); the certified `N_m` of
    `../Thue_Morse_Integer_Pressure_First_Negative_Data/` satisfy
    `-1.75 < N_m - (gamma m - log log(2m)/Lambda) < 0.36` for `2 <= m <= 128`
    (checked on filing, `gamma` and `Lambda` evaluated numerically from their
    definitions);
  - after the proof of Proposition 3.1: it is the case `k = 2` of Theorem 1.1
    of `../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/`, there on the
    larger window `(2, 2 mu(arctan(1/2)))`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited: `[Repo]` (cited as *Thue-Morse
    Integer Pressure*) is `../Thue_Morse_Integer_Pressure/`, `[AllOrders]`
    `../Thue_Morse_Integer_Pressure_Full_Range/`, `[Bound66]`
    `../Thue_Morse_Integer_Pressure_Negative_Bound/`, `[Signs]`
    `../Thue_Morse_Integer_Pressure_Sign_Changes/`; the finite data of Section
    8 are `../Thue_Morse_Integer_Pressure_First_Negative_Data/`.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 11 A4 pages (11 as delivered),
  422,355 bytes; all 21 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- The five `checks/verify_*.py` that write certificates: new option
  `--output-dir` (default `checks/rerun/`), with LF line endings. As
  delivered, every checker overwrote its recorded file beside itself, with
  CRLF line endings on Windows. Pass `--output-dir checks`, on a copy, to
  regenerate the recorded files. A checker that reads another checker's record
  reads the recorded file, as delivered. On the ProveIt machine use `py`
  rather than `python3`/`python`. Reruns on a copy (2026-10-01, Python 3.14.4,
  standard library) (`py -O`) passed (the outer replay in 27 s) and wrote four
  certificates equal to the recorded ones byte for byte, and
  `local_complex_arc_certificate.json` and `compact_outer_replay.json` equal
  apart from the `seconds` timing. `checks/produce_sharp_outer.py` is kept as
  delivered: it regenerates and overwrites the 593 KB
  `checks/sharp_outer_certificate.json` (run it only on a copy); it was not
  run.
- Of the `inputs/` copies listed above only
  `inputs/independent_outer_certificate.zip` is filed (it holds the only copy
  of `logarithmic_bound.md`); the all-orders PDF and source archive are
  `../Thue_Morse_Integer_Pressure_Full_Range/`, the eventual-6.6m article is
  `../Thue_Morse_Integer_Pressure_Negative_Bound/`, the infinite-sign PDF is
  `../Thue_Morse_Integer_Pressure_Sign_Changes/`, and the pinned manuscript is
  `../Thue_Morse_Integer_Pressure/`. `VALIDATION.json` records hashes of those
  inputs as delivered. The submitted checksum ledger was retired.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the `inputs/` lines, the retired ledger in the regeneration
  paragraph, and this section.
