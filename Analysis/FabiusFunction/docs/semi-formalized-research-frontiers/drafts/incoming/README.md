# incoming — the drop-box for new drafts

> [!IMPORTANT]
> ## HARD PHASE BOUNDARY: PUBLISH THE INTAKE BEFORE ANALYSIS
>
> When one or more reports arrive, perform a **quick archival intake only**:
> fetch and merge `origin/main`; check archive safety and integrity; unpack each
> report; move it to the appropriate thematic directory; normalize repository
> line endings and refresh any affected checksum ledger; delete the ZIP; update
> `MANIFEST.md` and the destination `README.md`; then commit and immediately
> publish that intake commit to the feature branch and to `origin/main` by an
> ff-only push. Verify the remote SHA.
>
> **Do not begin claim-by-claim review, theorem comparison, proof repair,
> deduplication, editorial integration, experiment reruns, LaTeX rewriting, or
> Lean formalization until that intake commit is confirmed on `origin/main`.**
> Intake may read only enough title/abstract/package metadata to choose a safe
> destination and record honest provenance/status. If another ZIP arrives while
> an intake batch is in progress, finish and publish the current batch first;
> process the newcomer in the next quick-intake commit. A continuing stream of
> arrivals must never postpone publication indefinitely.

This directory is the **arrival point for new research drafts**: zip
archives (or bare directories) are committed here first, typically one
archive per externally prepared report.

**If you see a zip archive here, process it:**

1. **Unpack** it (each archive normally contains a single top-level
   directory with one LaTeX document, its compiled PDF, and any
   supporting data, figures, or scripts).
2. **File it**: move the unpacked directory into the thematic group
   under [`../`](../) that fits its subject — see
   [`../MANIFEST.md`](../MANIFEST.md) for the group structure
   (`representations/`, `integration-and-transforms/`,
   `spectra-and-arithmetic/`, `inverse-and-sampling/`, `thue-morse/`,
   `exponents-and-q-series/`, `frontier-compilations/`,
   `rvachev_up_fourier_decay/`). Read the document title/abstract to
   decide; create a new group only if nothing fits.
3. **Delete the archive** — the unpacked directory is now the source of
   truth, and git history archives the original zip.
4. **Record it**: add a row to [`../MANIFEST.md`](../MANIFEST.md) and
   mention it in the receiving group's `README.md`.
5. **Commit** the unpack as its own commit.
6. **Publish the quick intake immediately**: push the intake commit to the
   current feature branch, then push that same commit to `origin/main` with a
   fast-forward-only push (never force-push).  If `origin/main` has advanced,
   merge it first, resolve and validate the merge, and then retry the
   fast-forward push.

The warning at the top is a strict sequencing rule, not a preference. Only
after the quick archival intake is visible on `origin/main` may the deeper
phase begin. Keep every substantive reassessment or integration change in a
later commit so the original filed package remains a clean, reviewable
baseline.

If the group already has a consolidated volume (a single merged
document absorbing former member drafts), the new draft usually stays a
separate member until it is deliberately merged into that volume.

This `README.md` is the permanent explanation of the directory and
**must not be deleted** — it also keeps the directory present in git
when no archives are waiting.

Most recent processed batch (all filed and removed on 2026-08-30):

- `fabius_information_frontier_report.zip` (751,588 bytes; SHA-256
  `41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`)
  became
  [`../inverse-and-sampling/fabius_information_frontier/`](../inverse-and-sampling/fabius_information_frontier/).
  Its submitted 18-entry ledger verified before four CSVs received the
  repository's LF normalization; deeper claim audit and artifact normalization
  are deferred until after publication of this archival checkpoint.
- `geometric_comb_interpolation_report-3.zip` (1,296,171 bytes; SHA-256
  `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`)
  was a unique arrival, not a reship, and became the quick-gate archival package
  [`../inverse-and-sampling/geometric_comb_lagrange_jackson_newton_report/`](../inverse-and-sampling/geometric_comb_lagrange_jackson_newton_report/).
  Its submitted TeX/PDF remain unchanged; deeper audit, numerical replay,
  canonicalization, and rebuild are deliberately deferred.
- `Fabius_Zero_Bias_Frontier_Report.zip` (1,300,870 bytes; SHA-256
  `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`)
  became
  [`../representations/Fabius_Zero_Bias_Frontier_Report/`](../representations/Fabius_Zero_Bias_Frontier_Report/).
- `Inverse_Fabius_Computability_Report.zip` (689,198 bytes; SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`)
  became
  [`../inverse-and-sampling/Inverse_Fabius_Computability_Report/`](../inverse-and-sampling/Inverse_Fabius_Computability_Report/).
- `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256
  `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`)
  became
  [`../frontier-compilations/Geometric_Uniform_Frontier_Directions/`](../frontier-compilations/Geometric_Uniform_Frontier_Directions/).
- `inverse_fabius_iterates_nowhere_analytic.zip` (1,137,032 bytes; SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`)
  became
  [`../inverse-and-sampling/inverse_fabius_iterates_nowhere_analytic/`](../inverse-and-sampling/inverse_fabius_iterates_nowhere_analytic/).
- `inverse_q_analogs_report.zip` (894,405 bytes; SHA-256
  `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627`)
  became
  [`../exponents-and-q-series/inverse_q_analogs_report/`](../exponents-and-q-series/inverse_q_analogs_report/).
- `q_pochhammer_q_binomial_expansions_report.zip` (730,285 bytes; SHA-256
  `e8c6e5be4512abc0bacfd904e3f0027b35fd5e47e916a6ad11cc76b2893b3a07`)
  became
  [`../exponents-and-q-series/q_pochhammer_q_binomial_expansions_report/`](../exponents-and-q-series/q_pochhammer_q_binomial_expansions_report/).

The immediately preceding processed archive was
`Fabius_Rvachev_Frontier_Report_Package.zip` (outer SHA-256
`0028cb4f47134574ba7cd698bfc0ec11f08776b320cbc82b8467bea20d865f6d`),
filed as
[`../spectra-and-arithmetic/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](../spectra-and-arithmetic/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/).
