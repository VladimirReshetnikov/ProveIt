# Intake audit

## Provenance and safety

The delivered archive `Fabius_Zero_Bias_Frontier_Report.zip` had SHA-256
`fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`.
Its paths were traversal-safe and its 21-file delivered ledger verified
21/21 before any edit. That arrival ledger and the subsequent normalized
checkpoint ledger are now retired; their bytes remain recoverable from Git
history. The current TeX, PDF, README, and intake-audit rows describe the
synchronized 2026-08-31 repository rebuild.

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
formal-status and replay notes added. The package-local running title is
abbreviated to prevent collision with the long Section 9 mark, and explicit
plain-text bookmark forms remove the three math-in-heading warning sites.

The source used for the current validated PDF has SHA-256
`80b3d01e7555d322781fedf671f1984279cb8e997d964f96942cb117db79b9b2`.
After a clean auxiliary state it received exactly three strict serial
`pdflatex` passes on 2026-08-31, producing 25, 26, and 26 pages. The resulting
PDF is 26 A4 pages, 771,261
bytes, with SHA-256
`e7698059db2a24985b90258683af4fde277235159379fc7b294583dbb6bf0f37`.
The third-pass log has no errors, undefined references, rerun requests,
duplicate destinations, package warnings, LaTeX warnings, or overfull boxes;
its five underfull notices are
confined to a visually clean claim-status table. All 39 font rows are embedded
and subset, five are Libertinus, and no Type 3 font occurs. Every page is at
rotation zero and has extractable text; title, author, subject, and keywords
metadata are present. Physical pages 1, 13, 18--20, 22, and 26 passed visual
inspection, covering the title, theorem pages, all five figures, repaired
running heads, conjectures, and appendix. The 1,926-line, 72,171-byte
merge-resolved source has no conflict markers, and the focused
canonical-notation audit reports no findings. Build auxiliaries were removed.
