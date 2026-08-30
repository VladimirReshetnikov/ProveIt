# incoming — the drop-box for new drafts

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

Only after that quick archival intake is visible on `origin/main` should the
deeper phase begin: claim-by-claim mathematical reassessment, comparison with
the Lean corpus, deduplication against consolidated volumes, editorial
integration, documentation correction, or new formalization.  Keep those
substantive changes in later commits so the original filed package remains a
clean, reviewable baseline.

If the group already has a consolidated volume (a single merged
document absorbing former member drafts), the new draft usually stays a
separate member until it is deliberately merged into that volume.

This `README.md` is the permanent explanation of the directory and
**must not be deleted** — it also keeps the directory present in git
when no archives are waiting.

Most recent processed batch (all filed and removed on 2026-08-30):

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
