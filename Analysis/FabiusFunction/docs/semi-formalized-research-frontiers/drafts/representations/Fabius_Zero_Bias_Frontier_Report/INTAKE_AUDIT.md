# Intake audit

## Provenance and safety

The delivered archive `Fabius_Zero_Bias_Frontier_Report.zip` had SHA-256
`fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`.
Its paths were traversal-safe and its 21-file delivered ledger verified
21/21 before any edit. `ARRIVAL_SHA256SUMS` preserves that ledger verbatim.
The live `SHA256SUMS` file records the last validated normalized checkpoint;
its current-source and pending-rebuild metadata rows must be refreshed after
the next PDF build.

## Mathematical-status audit

The paper's zero-bias tower, occupancy, spectral-peeling, and tower-limit
results are not declarations in the current Lean facade. Existing formal APIs
do supply substantial inputs: geometric and dyadic random-series laws, exact
moments/cumulants, arithmetic Fourier zeros and Thue--Morse signs, density
shape, and endpoint/Lambert asymptotics. The report now says explicitly that
its theorem environments are manuscript-level proofs and that its five
conjecture environments remain conjectural. No formal coverage count or
status ledger was changed by this intake.

The hostile read-through found no short counterexample or normalization
contradiction in the stated manuscript results. In particular, the universal
compact-support limit includes the necessary endpoint-reach hypothesis, and
the fixed Rvachev transport conclusion is separated from that general weak
limit. This audit is not a substitute for Lean formalization of the new layer.

## Numerical replay

The full default command was replayed without network data:

```text
python zero_bias_tower_experiments.py --max-level 2000 --samples 30000
```

Environment: Python 3.13.14, NumPy 2.5.2, SciPy 1.18.1, SymPy 1.14.0,
mpmath 1.3.0, Matplotlib 3.11.1. The random seed remained `20260830`.

- `collision_free_probabilities.csv`, `exact_even_moments.csv`, and
  `released_fourier_values.csv` reproduced the delivered bytes before the
  repository-required CRLF-to-LF normalization.
- `high_moment_ratios.csv` changed only floating fields; among 11,988 numeric
  fields the largest absolute change was `7.30526750203353e-14`.
- `occupancy_sampler_checks.csv` changed four last-place fields; maximum
  absolute change was `3.3306690738754696e-16`.
- `tower_moment_convergence.csv` changed 44 of 99 numeric fields; maximum
  absolute change was `4.263256414560601e-14`.
- All five PNGs retained their delivered pixel dimensions. Modern raster
  antialiasing changed 4.7--9.7% of whole RGB pixels, depending on the figure.
- All five vector PDFs were regenerated with embedded/subset CID TrueType
  fonts and no Type 3 fonts; byte identity is neither expected nor claimed.

## Editorial normalization

The report uses the repository's canonical article/A4/27 mm/Libertinus
preamble, apart from report metadata/running heads and required local notation.
The numerical generator pins PDF font type 42. Mathematical body, labels, and
conjecture boundaries were otherwise preserved, with only the explicit
formal-status and replay notes added.

The source used for the existing validated PDF had SHA-256
`e83f0e426ce872b4da4cd046fa5fcc8a53b4c5e29e60c60ecc6ff7bbc7fb823e`.
After a clean auxiliary state it received exactly three strict serial
`pdflatex` passes. That last validated PDF is 26 A4 pages, 770,486 bytes, with SHA-256
`2d90086da466124eae2e32addf6d68556f35459b4a6debac07be4859035a12b5`.
The third-pass log has no errors, undefined references, rerun requests,
duplicate destinations, or overfull boxes; its five underfull notices are
confined to a visually clean claim-status table. All 39 font rows are embedded
and subset, Libertinus is present, and no Type 3 font occurs. Text extraction
and representative visual checks of the title, status table, theorem pages,
five figures, conjectures, and appendix passed. Build auxiliaries were removed.

The current merge-resolved source has 1,926 lines and 72,038 bytes, with
SHA-256
`07a6876751b79db0b4af3fb7a765eced5846fb24ad82c02e19fb01314b65c834`.
It has no conflict markers and the focused canonical-notation audit reports no
findings, but it has not been compiled. The existing PDF remains the last
validated render. Its ledger row still verifies; the TeX and metadata rows
carrying this pending-rebuild notice must be refreshed together after a new
three-pass build.
