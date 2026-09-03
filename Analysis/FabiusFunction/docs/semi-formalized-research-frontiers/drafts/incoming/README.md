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

Most recent processed batch (three archives, filed and removed on 2026-09-03,
arrival commit `912d3bfbe`): the three Fibonacci-inversion articles, all to
`../series-and-transseries/special-function-inversion/` as its fourth subject.

- `Fibonacci_Inverse_LogPeriodic_Transseries.zip` → `Fibonacci_Inverse_LogPeriodic_Transseries/`: 2,554-line/89,365-byte source, 33-page A4/787,646-byte PDF.
- `fibonacci_inverse_transseries_article.zip` → `fibonacci_inverse_transseries_article/`: 2,857-line/98,788-byte source, 36-page A4/797,090-byte PDF.
- `fibonacci_inverse_transseries_article-2.zip` → `fibonacci_inverse_transseries_article-2/`: 1,884-line/64,334-byte source, 24-page A4/759,845-byte PDF.

Previous batch (six archives, filed and removed on 2026-09-03).
These arrived *while the batch below was being published*, which is the case the
rule at the top of this file covers: the first batch was finished and pushed to
`origin/main` before any of these was touched, and they were then taken in the
next quick-intake commit.  All six went to
`../series-and-transseries/special-function-inversion/`, joining the three
already there, and the nine now fall into three subjects with three
independently written articles each.

- `inverse_gamma_barnesG_transseries.zip` → `inverse_gamma_barnesG_transseries/`:
  1,655-line/72,966-byte source, 28-page A4/663,480-byte PDF.
- `inverse_gamma_barnes_transseries.zip` → `inverse_gamma_barnes_transseries/`:
  1,827-line/60,596-byte source, 25-page A4/324,795-byte PDF.
- `K_Function_Inverse_Transseries_LaTeX_and_PDF.zip` → `K_Function_Inverse_Transseries/`:
  2,644-line/90,380-byte source, 33-page A4/724,630-byte PDF.  **Renamed at
  filing**: the archive stem would have put the PDF at a 263-character path,
  past the Windows `MAX_PATH` limit of 260, after which `pdfinfo` reports
  *"No such file or directory"* for a file that plainly exists.  The directory
  is named after the document instead, which is also the corpus convention.
- `K_function_inverse_transseries_article.zip` → `K_function_inverse_transseries_article/`:
  2,581-line/84,722-byte source, 30-page A4/743,783-byte PDF.
- `inverse_subfactorial_transseries-2.zip` → `inverse_subfactorial_transseries-2/`:
  2,188-line/73,742-byte source, 27-page A4/725,870-byte PDF.
- `inverse_subfactorial_transseries-3.zip` → `inverse_subfactorial_transseries-3/`:
  1,878-line/81,203-byte source, 35-page Letter/530,302-byte PDF.

Every archive passed a CRC check with no absolute path, parent-directory
traversal, or symlink entry, and each held exactly one `.tex` and one `.pdf` at
top level.  All six sources are LF with a final newline; no normalization was
applied.  The last two archives both contain inner files named plainly
`inverse_subfactorial_transseries.*`, which were kept as submitted — the
directory name carries the distinction, following the precedent of
`lambert_inverse_transseries_bundle/`.  All six PDFs are readable, unencrypted,
pdfTeX-1.40.26, fully embedded and Type-3-free; five are A4 and one is Letter,
and three carry Libertinus faces.  None loads `docs/fabius-notation.tex`.
Comparison, deduplication, canonical selection, proof checking, numerical
reproduction and Lean crosswalking were all deferred.

The batch immediately before it (three archives, filed and removed the same
day):

- `Asymptotic_Inversion_Gamma_Barnes_G.zip` became
  `../series-and-transseries/special-function-inversion/Asymptotic_Inversion_Gamma_Barnes_G/`:
  2,376-line/83,252-byte source, 29-page A4/646,225-byte PDF.
- `inverse_k_function_transseries.zip` became
  `../series-and-transseries/special-function-inversion/inverse_k_function_transseries/`:
  2,259-line/66,867-byte source, 29-page A4/349,822-byte PDF.
- `inverse_subfactorial_transseries.zip` became
  `../series-and-transseries/special-function-inversion/inverse_subfactorial_transseries/`:
  2,631-line/95,404-byte source, 38-page A4/688,626-byte PDF.

These three archives landed together in commit `5a453e1dc`.  Each contained
exactly one `.tex` and one `.pdf` at top level with no wrapping directory, so
the destination directory was created at filing; none included a checksum
ledger, and none was added.  Every archive passed a CRC check and carried no
absolute path, parent-directory traversal, or symlink entry.  All three sources
were already LF with a final newline, so no normalization was applied and the
filed bytes are exactly the submitted bytes.  All three PDFs are readable and
unencrypted, produced by pdfTeX-1.40.26 at PDF version 1.7, with every font row
embedded and no Type 3 font; all three are A4, which is canonical, and two of
the three carry Libertinus faces — `inverse_k_function_transseries` does not,
which is the only styling debt recorded against this batch.  None of the three
loads `docs/fabius-notation.tex`.  Comparison, deduplication, proof checking,
numerical reproduction, editorial consolidation, and Lean crosswalking were all
deferred at intake and have not been carried out.

The preceding processed batch (all filed and removed on 2026-09-01):

- `Polynomial-Logarithmic-Transseries-1/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial-Logarithmic-Transseries-1/`:
  4,023-line/182,487-byte source, 119-page/584,392-byte PDF.
- `Polynomial-Logarithmic-Transseries-2/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial-Logarithmic-Transseries-2/`:
  5,014-line/168,311-byte source, 102-page/571,108-byte PDF.
- `Polynomial_Logarithmic_Transseries-3/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries-3/`:
  4,255-line/146,006-byte source, 87-page/510,663-byte PDF; its submitted
  line-411 trailing whitespace remains intact.
- `Polynomial-Logarithmic-Transseries-4/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial-Logarithmic-Transseries-4/`:
  3,138-line/118,001-byte source, 47-page/428,534-byte PDF.
- `Polynomial_Logarithmic_Transseries-5/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries-5/`:
  2,440-line/102,903-byte source, 44-page/389,188-byte PDF.
- `Polynomial_Logarithmic_Transseries-6/` became
  `../series-and-transseries/polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries-6/`:
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
crosswalking were deferred at intake and have since been carried out.

**The six destination paths above no longer exist.**  They record where each
arrival was filed, which is what this log is for, but the packages were filed
under `../lambert-w/` on 2026-09-01, regrouped into
`../series-and-transseries/polynomial-logarithmic-transseries/` on 2026-09-02,
and merged editorially the same day into the single canonical volume
[`../series-and-transseries/polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries/`](../series-and-transseries/polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries/).
The six directories were then deleted; git history is the archive, and that
volume's provenance appendix carries every source's intake and absorbed
SHA-256 receipt together with what each one uniquely contributed.

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
  was first filed at the historical path
  `../inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`
  and was later absorbed into the canonical
  [*Inverse Fabius Theory*](../inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/).
  Its arrival ledger, source disposition, and recovery revision remain in the
  canonical provenance package.
- `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256
  `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`)
  became
  [`../frontier-compilations/Geometric_Uniform_Frontier_Directions/`](../frontier-compilations/Geometric_Uniform_Frontier_Directions/).
- `inverse_fabius_iterates_nowhere_analytic.zip` (1,137,032 bytes; SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`)
  was first filed at the historical path
  `../inverse-and-sampling/analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`
  and was later absorbed into the canonical
  [*Inverse Fabius Theory*](../inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/).
  Its immutable arrival ledger, hostile audit, retained inverse-facing assets,
  and forward-report reconciliation boundary remain in the canonical package.
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
