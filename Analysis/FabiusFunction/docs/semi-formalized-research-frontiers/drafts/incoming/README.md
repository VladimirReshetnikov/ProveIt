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

Most recent processed batch (all filed and removed on 2026-09-01):

- `Polynomial-Logarithmic-Transseries-1/` became
  [`../lambert-w/Polynomial-Logarithmic-Transseries-1/`](../lambert-w/Polynomial-Logarithmic-Transseries-1/):
  4,023-line/182,487-byte source, 119-page/584,392-byte PDF.
- `Polynomial-Logarithmic-Transseries-2/` became
  [`../lambert-w/Polynomial-Logarithmic-Transseries-2/`](../lambert-w/Polynomial-Logarithmic-Transseries-2/):
  5,014-line/168,311-byte source, 102-page/571,108-byte PDF.
- `Polynomial_Logarithmic_Transseries-3/` became
  [`../lambert-w/Polynomial_Logarithmic_Transseries-3/`](../lambert-w/Polynomial_Logarithmic_Transseries-3/):
  4,255-line/146,006-byte source, 87-page/510,663-byte PDF; its submitted
  line-411 trailing whitespace remains intact.
- `Polynomial-Logarithmic-Transseries-4/` became
  [`../lambert-w/Polynomial-Logarithmic-Transseries-4/`](../lambert-w/Polynomial-Logarithmic-Transseries-4/):
  3,138-line/118,001-byte source, 47-page/428,534-byte PDF.
- `Polynomial_Logarithmic_Transseries-5/` became
  [`../lambert-w/Polynomial_Logarithmic_Transseries-5/`](../lambert-w/Polynomial_Logarithmic_Transseries-5/):
  2,440-line/102,903-byte source, 44-page/389,188-byte PDF.
- `Polynomial_Logarithmic_Transseries-6/` became
  [`../lambert-w/Polynomial_Logarithmic_Transseries-6/`](../lambert-w/Polynomial_Logarithmic_Transseries-6/):
  4,354-line/150,235-byte source, 100-page/701,319-byte PDF.

These six bare-directory arrivals landed together in direct-arrival commit
`730e1763291099cd50ca1e20ed2c62c38d95ab4f`; none included an archive or
checksum ledger.  All six sources were already LF with a final newline, so no
normalization was needed.  They were filed byte-for-byte with a
repository-added two-row checksum ledger and archival README in each package.
All PDFs are readable,
unencrypted, embedded/subset, and Type-3-free, but none uses Libertinus; two
have a custom 522-by-738-point page, two are Letter, and two are A4.  Styling
repair, comparison, deduplication, claim review, PDF rebuilding, and Lean
crosswalking remain deferred until this checkpoint is published.  Full source
and PDF hashes are recorded in the destination README and package receipts.

The immediately preceding processed batch, also filed and removed on
2026-09-01, comprised these six archives:

- `Combinatorial_Coefficient_Calculus-2.zip` (1,096,487 bytes; SHA-256
  `a0ca605c1d3f1ee3e00eac1d69a8181e786dd414407a1b3b6db1a60f74d8766d`)
- `Combinatorial_Coefficient_Calculus.zip` (1,094,284 bytes; SHA-256
  `a22479ac8f58e1710117af9d0a3f515c7d24ec250548f537520c9f9024f4321a`)
- `Combinatorial_Formulae_and_Inversion_Theorems.zip` (1,101,493 bytes;
  SHA-256 `dae561780a4442a9f11acb7edf1ec508daca1db237db01fabf77c695ec924960`)
- `Unified_Combinatorial_Coefficient_Calculus.zip` (1,083,495 bytes;
  SHA-256 `c4217b088444eb3e4bf24a7542d360f02dfb8e240418b562a155ad0c251ab559`)
- `Unified_Combinatorial_Formulae.zip` (1,015,842 bytes; SHA-256
  `611b14cfda15357b679a05d9586811d8fb39f6fe7d971f00424da2bb848a5594`)
- `Unified_Combinatorial_Formulae_and_Inversion_Theorems.zip` (1,062,893
  bytes; SHA-256
  `ba62d0653fba9f0d1d867885e0b45272ba128973c1e49938d6cb1f597b457e33`)

All six became standalone archival packages under
[`../combinatorial-coefficient-calculus/`](../combinatorial-coefficient-calculus/).
Each safe flat archive contained exactly one TeX/PDF pair; all CRCs passed, the
filed payloads are byte-identical to their archive members, and every package's
two-row checksum ledger verifies.  Their similar titles and subjects were noted
without comparing or deduplicating them.  Claim review, canonical selection,
LaTeX rewriting, PDF rebuilding, and Lean crosswalking remain deliberately
deferred until this intake is published.

The preceding 2026-08-30 processed batch was filed and removed as follows:

- `fabius_dyadic_chaos_frontier.zip` (1,351,045 bytes; SHA-256
  `d57fd01c3991a6a7ecd6ba6e745729c745745d3265cb3cfd414aac1991b11b86`)
  became the quick-gate archival package
  [`../representations/fabius_dyadic_chaos_frontier/`](../representations/fabius_dyadic_chaos_frontier/).
  Its safe single-wrapper archive and submitted 30-entry ledger verified in
  full; nine CSVs received repository LF normalization, while claim audit,
  numerical replay, canonicalization, font repair, and rebuild remain
  deliberately deferred until after publication.
- `fabius_information_frontier_report.zip` (751,588 bytes; SHA-256
  `41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`)
  became
  [`../inverse-and-sampling/fabius_information_frontier/`](../inverse-and-sampling/fabius_information_frontier/).
  Its submitted 18-entry ledger verified before four CSVs received the
  repository's LF normalization; deeper claim audit and artifact normalization
  are deferred until after publication of this archival checkpoint.
- `geometric_comb_interpolation_report-3.zip` (1,296,171 bytes; SHA-256
  `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`)
  was a unique arrival, not a reship, and was first filed as a quick-gate
  archival package. It was later absorbed into the canonical
  [`comb_interpolation_synthesis/`](../inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/),
  whose pinned-source audit and companion-evidence index preserve its source
  results and unique reproducibility payloads.
- `Fabius_Zero_Bias_Frontier_Report.zip` (1,300,870 bytes; SHA-256
  `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`)
  became
  [`../representations/Fabius_Zero_Bias_Frontier_Report/`](../representations/Fabius_Zero_Bias_Frontier_Report/).
- `Inverse_Fabius_Computability_Report.zip` (689,198 bytes; SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`)
  became
  [`../inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`](../inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/).
- `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256
  `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`)
  became
  [`../frontier-compilations/Geometric_Uniform_Frontier_Directions/`](../frontier-compilations/Geometric_Uniform_Frontier_Directions/).
- `inverse_fabius_iterates_nowhere_analytic.zip` (1,137,032 bytes; SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`)
  became
  [`../inverse-and-sampling/analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`](../inverse-and-sampling/analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/).
- `inverse_q_analogs_report.zip` (894,405 bytes; SHA-256
  `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627`)
  was absorbed into the canonical consolidation
  [`../exponents-and-q-series/q_pochhammer_q_binomial_monograph/`](../exponents-and-q-series/q_pochhammer_q_binomial_monograph/),
  whose provenance and asset-disposition ledgers preserve the arrival.
- `q_pochhammer_q_binomial_expansions_report.zip` (730,285 bytes; SHA-256
  `e8c6e5be4512abc0bacfd904e3f0027b35fd5e47e916a6ad11cc76b2893b3a07`)
  was absorbed into the canonical consolidation
  [`../exponents-and-q-series/q_pochhammer_q_binomial_monograph/`](../exponents-and-q-series/q_pochhammer_q_binomial_monograph/),
  whose provenance and asset-disposition ledgers preserve the arrival.

The immediately preceding processed archive was
`Fabius_Rvachev_Frontier_Report_Package.zip` (outer SHA-256
`0028cb4f47134574ba7cd698bfc0ec11f08776b320cbc82b8467bea20d865f6d`),
filed as
[`../spectra-and-arithmetic/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](../spectra-and-arithmetic/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/).
