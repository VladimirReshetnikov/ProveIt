# An asymptotic lower bound for the first negative pressure degree

The six-page (seven since the editorial amendments below) article proves that, for every sufficiently large integer m, all even pressure coefficients at degrees 2m < N <= 6.6m are strictly positive. Therefore the first negative even degree N_m above the cancellation at 2m satisfies liminf N_m/m >= 6.6.

The threshold in m is existential. The package does not claim a numerical cutoff, an exact formula for N_m, or convergence of N_m/m. The separately certified interval (6.662966, 6.662968) concerns a positive comparison model, not the true limiting slope.

This is an unrefereed mathematical proof with exact rational scalar certificates, not a Lean formalization.

## Contents

- `article.pdf` and `article.tex`: the theorem, complete new third-cluster proof, full-disk quadratic estimate, and uniform saddle comparison
- `checks/verify_eventual_66.py`: exact endpoint-rate and norm side conditions
- `checks/verify_model_crossing.py`: optional exact bracket for the comparison-model crossing
- `checks/exact_intervals.py`: outward integer intervals, Machin pi bounds, and Taylor trigonometric bounds
- `checks/*_certificate.json`: reproducible exact outputs
- `inputs/all_integer_orders.pdf` and `.tex`: unchanged preceding report containing the full weighted Green argument and the all-m positivity theorem below 6m
- `inputs/all_integer_orders_sources.zip`: the unchanged reproducible source archive for that preceding report, including its dyadic tangent proof and scalar certificates
- `inputs/infinite_sign_changes.pdf`: unchanged preceding proof that N_m exists for every m >= 2
- `inputs/repository_integer_pressure.tex`: pinned repository source
  (the four `inputs/` entries were not filed; see the editorial amendments below)
- `PROVENANCE.md` and `SHA256SUMS`: source identity and content hashes (`SHA256SUMS` retired on filing; not in the repository)

## Replay

Python3 with the standard library is sufficient for both new scalar checkers:

    python3 checks/verify_eventual_66.py
    python3 checks/verify_model_crossing.py

All failure checks use explicit exceptions and remain active under Python's optimization flag. The second checker imports the first and therefore also replays its conditions. Outputs use exact rational strings; no floating-point calculation enters either certificate. The small proposed saddle brackets are checked, not trusted.

A conventional TeX Live installation with pdfLaTeX, AMS packages, geometry, Latin Modern, microtype, hyperref and xurl can build `article.tex`. The included `build_local.sh` also supports the explicit TeX/font paths of the production environment. It performs two passes and writes `article.pdf`.

The analytic local-limit argument establishes a common sufficiently large threshold but does not compute it. Passing these scalar scripts should not be described as a finite verification of all smaller m.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the tenth of thirteen packages of one series, filed beside the
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
  - after Theorem 1.1: the `liminf` bound is implied by Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_First_Negative/` (which uses this theorem
    as an input); the strict positivity is not; `N_50 = 330` in
    `../Thue_Morse_Integer_Pressure_First_Negative_Data/` gives `m_0 >= 51`;
  - after "Neither is claimed here": both are proved in
    `../Thue_Morse_Integer_Pressure_First_Negative/`
    (`lim N_m/m = gamma = 2 sigma` of this crossing); the last sentence
    printed by `checks/verify_model_crossing.py` is superseded in the same
    way;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited: `[Repo]`, cited as *Thue-Morse
    Integer Pressure*, is `../Thue_Morse_Integer_Pressure/`; `[AllOrders]` is
    `../Thue_Morse_Integer_Pressure_Full_Range/`; `[Signs]` is
    `../Thue_Morse_Integer_Pressure_Sign_Changes/`.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 7 A4 pages (6 as delivered),
  335,890 bytes; all 19 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `checks/verify_eventual_66.py`, `checks/verify_model_crossing.py`: new
  option `--output-dir` (default `checks/rerun/`), with LF line endings. As
  delivered, every checker overwrote its recorded file beside itself, with
  CRLF line endings on Windows. Pass `--output-dir checks`, on a copy, to
  regenerate the recorded files. A checker that reads another checker's record
  reads the recorded file, as delivered. On the ProveIt machine use `py`
  rather than `python3`/`python`. Reruns on a copy (2026-10-01, Python 3.14.4,
  standard library) passed and wrote both certificates equal to the recorded
  ones byte for byte. The "remains open" statement of this README (`N_m/m`
  convergence) is answered by
  `../Thue_Morse_Integer_Pressure_First_Negative/`.
- The `inputs/` copies listed above were not filed: the all-orders article,
  PDF and source archive are `../Thue_Morse_Integer_Pressure_Full_Range/`, the
  infinite-sign PDF is `../Thue_Morse_Integer_Pressure_Sign_Changes/`, and the
  pinned manuscript is `../Thue_Morse_Integer_Pressure/`. The submitted
  checksum ledger was retired.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count, the `inputs/` lines and the retired ledger
  under "Contents", and this section.
