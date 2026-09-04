# Spectra and arithmetic

## Source-only notation status (2026-09-01)

The two-adic-valuation notation pass changed the consolidated
`Spectra_and_Arithmetic_Frontiers` source and five standalone report sources.
The exact current live-TeX snapshots are:

| Live source | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `Automatic_Scale_Factorizations_Rvachev_2026-08-30/automatic_scale_factorizations.tex` | 1,682 | 62,490 | `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90` |
| `Digital_Spectral_Geometry_and_Log_Periodic_Saddles/Fabius_Rvachev_Frontier_Report.tex` | 1,940 | 61,049 | `92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1` |
| `Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex` | 2,307 | 90,871 | `e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e` |
| `fabius_holonomic_frontiers_report/fabius_holonomic_frontiers.tex` | 2,251 | 85,256 | `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f` |
| `Fabius_Total_Positivity_Frontier_Report/Fabius_Total_Positivity_Frontier_Report.tex` | 1,060 | 58,362 | `e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475` |
| `Spectra_and_Arithmetic_Frontiers/Spectra_and_Arithmetic_Frontiers.tex` | 8,183 | 349,076 | `683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1` |

These metrics and hashes describe the live TeX only. No PDFs were regenerated
for this pass. Consequently, every page-count, font, visual-inspection, and
three-pass-build statement below remains evidence about its earlier retained
PDF checkpoint, not evidence of byte-level or rendered parity with the current
source. Mutable live ledgers for the affected packages have been or are being
refreshed to record the source-only checkpoint; immutable arrival ledgers and
the historical build hashes recorded in package receipts remain unchanged.
`Fabius_Pascal_Frontiers_Report` likewise retains its already documented mixed
checkpoint: its reviewed PDF predates its current TeX.

## Direct-directory intake: late 2026-08-30 batch

Six tracked report directories arrived directly under `drafts/incoming/` in
`origin/main`, without ZIP archives or outer archive hashes.  They were moved
here in the quick intake phase and kept as separate manuscripts; the arrival
commits remain their byte-level provenance.  Internal checksum ledgers were
verified against the submitted bytes, then refreshed only where Git's
repository policy had normalized CSV files from CRLF to LF.  Repository
ledgers were added where the delivery was incomplete.  All delivered PDFs in
this batch passed a structural `pdfinfo` read and were unencrypted; this was
not a visual review, experiment replay, TeX rebuild, mathematical audit, or
Lean verification.

- [`Automatic_Scale_Factorizations_Rvachev_2026-08-30/`](Automatic_Scale_Factorizations_Rvachev_2026-08-30/)
  contains *Automatic Scale Factorizations of the Rvachev Law* (retained
  22-A4-page PDF checkpoint; current live TeX: 1,682 lines, 62,490 bytes,
  SHA-256
  `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`;
  with a 473-line program, eight data outputs, and three
  PDF/PNG figure pairs), from arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. At its normalized intake
  checkpoint, the submitted ledger covered all 21 non-ledger payloads and
  verified after six CSV hashes were refreshed for LF storage and the JSON
  summary's missing final newline was repaired. The
  current source selects the retained PNG plot companions; the exact
  three-pass rebuild embedded and subset every font, retained Libertinus prose,
  and had no
  Type 3 fonts, while the vector-PDF plots remain reproducibility payloads. The
  corresponding exact three-pass render is a retained historical checkpoint,
  not a current source/PDF parity claim. No PDF was regenerated after the
  notation-only TeX change, and the mutable live ledger is being refreshed for
  that source-only checkpoint. Its
  Thue--Morse scale partition, q-Mahler, Mellin, moment, plateau, and endpoint
  themes remain standalone pending claim and experiment review, comparison,
  and a Lean crosswalk.

- [`Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`](Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/)
  contains *Dyadic Radon Profiles in the Fabius--Rvachev Web* (31
  letter-paper pp, 2,064 source lines; with a 624-line program, ten data
  files, and four PDF/PNG figure pairs), from
  `03b2f61889674f7d64ac86d3233236f5fa7ce660`. Its complete 26-entry ledger
  now records the repository-normalized bytes; nine CSV entries changed only
  by CRLF-to-LF normalization. The title and abstract concern spectral
  reconstruction of dyadic projection profiles, zero multiplicities,
  q-sampled cumulants, automatic signs, Pascal factorizations, and exact
  cubature.

- [`Fabius_Pascal_Frontiers_Report/`](Fabius_Pascal_Frontiers_Report/)
  contains *Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals
  in the Pascal--Rvachev Hierarchy* (26 A4 pp, 1,927 source lines; with a
  426-line program, four CSV tables, and a captured numerical summary), from
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. The nine-file delivery had no
  checksum ledger or dependency lock. The repository-generated `SHA256SUMS`
  recorded the nine-payload scope before its repository-wide retirement on
  2026-09-01; its final snapshot remains recoverable from Git history. The
  retained 26-page A4 PDF was
  rebuilt in exactly three serial passes and has complete metadata,
  embedded/subset Type 1 fonts, six Libertinus rows, and no Type 3 font. The
  source changed after that receipt, so a new build is required before
  synchronization is claimed; the former ledger's final mixed checkpoint
  remains in Git history. Its higher-rank spectral
  signs and Lambert series, dyadic cubature, Laguerre--Pólya/Pascal hierarchy,
  and probabilistic duals remain pending comparison.

- [`fabius_holonomic_frontiers_report/`](fabius_holonomic_frontiers_report/)
  contains *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness in the
  Fabius--Rvachev System* (retained 30-A4-page PDF checkpoint; current live
  TeX: 2,251 lines, 85,256 bytes, SHA-256
  `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`;
  with a 644-line
  experiment, six CSV tables, a generated TeX fragment, a captured text
  check, and five PDF/PNG figure pairs), from
  `6d6737530ec541196c506f95ec20a701a29872b3`. Six CSV hashes in its complete
  26-entry ledger were refreshed for LF storage. At intake, all six delivered
  PDFs were readable and unencrypted (35 pages total). Those retained PDFs
  predate the current notation-only TeX; no PDF was regenerated, and the
  mutable live ledger is being refreshed for the source-only checkpoint. The
  report concerns finite
  sinc-product differential rank, exact signed overlaps, dyadic
  Thue--Morse/frequency spectra, and non-D-finiteness/non-P-recursiveness.

- [`Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`](Fabius_Rvachev_Carleman_Frontiers_2026-08-30/)
  contains *Critical Ultradifferentiable Geometry of the Fabius--Rvachev
  System* (24 A4 pp, 1,941 source lines; with a 544-line program, four CSV
  tables, and five PDF/PNG figure pairs), from
  `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. Four CSV hashes in its complete
  21-entry ledger were refreshed for LF storage. Its derivative spectrum,
  Denjoy--Carleman scales, discrete Fourier duality, lattice corrections,
  Lambert-W saddles, and Bell-edge behavior remain pending comparison and
  formalization.

- [`Dyadic_Spectral_Divisors_and_Gamma_Duality/`](Dyadic_Spectral_Divisors_and_Gamma_Duality/)
  is the title-derived filing of the generic incoming wrapper
  `Fabius_Rvachev_Frontier_Report-F/` from
  `d4605275f58f648ebcdeb74bc2ef5e4983abb6f0`. *Dyadic Spectral Divisors and
  Gamma Duality* is 22 A4 pages and 1,301 source lines, with a 379-line
  program, seven generated outputs, and three PDF/PNG figure pairs. Its
  submitted 3-entry ledger verifies those three payloads but is incomplete;
  the repository-added full `ARRIVAL_SHA256SUMS` ledger records all 20
  delivered files, including the submitted ledger. Its dyadic zero divisor,
  Laguerre--Pólya/non-holonomic structure, reciprocal-base counting, heat
  traces, Gamma/Thorin duality, and Lambert inversion remain separate pending
  semantic deduplication and a Lean crosswalk.

These reports overlap one another and the consolidated spectra volume in
zero-divisor arithmetic, Pascal/valuation profiles, derivative growth,
Laguerre--Polya and Pólya-frequency structure, holonomicity, and
non-P-recursiveness.  That claim-level comparison is intentionally deferred
until after publication.  A theorem label, proof in prose, symbolic
calculation, or numerical check in any manuscript does not imply that the
claim has been proved in Lean.

New standalone intake member:
[`Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](Digital_Spectral_Geometry_and_Log_Periodic_Saddles/),
*Digital Spectral Geometry and Log-Periodic Saddles* (retained 24-A4-page PDF
checkpoint; current live TeX: 1,940 lines, 61,049 bytes, SHA-256
`92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`),
arrived from the
rootless `Fabius_Rvachev_Frontier_Report_Package.zip` on 2026-08-30. The
title-based directory avoids collision with an unrelated q-series package
that used the same generic report filename. Its delivered zero-file audit was
replaced by a reproducible recursive audit of 188 prior TeX files (390,119
lines and 16,813,357 bytes) excluding this package directory, with raw corpus
digest `bb8a7de4c16a960f8d640d99797085b4f17cd0cdcc38b38caa4014536806b4d3`.
Its
failed numerical generation was repaired and rerun at 80-digit precision,
producing all three optional figures and the generated tables. No theorem-
level novelty is accepted on intake: the divisor/zeta/count/heat/cumulant,
exact `K`/Lambert/base-family, Appell/first-defect, Legendre--Bessel, sub-
Gaussian, and endpoint/inverse strands all have exact or stronger prior homes
in the consolidated corpus. Only minor corollary-level residue remains to
assess. The all-orders saddle and inverse claims were downgraded for a missing
uniform remainder, the global Strang--Fix conclusion was restricted to the
proved canonical Appell defect, and the false strict-curvature range was
corrected using center flatness at `b=2` and the exact plateau for `b>2`.
The report remains a separate overlap intake; its labels assert neither
novelty nor Lean status. It now reproduces the current primary document's
canonical A4 package, theorem, macro, boxed-environment, and listing-style
block verbatim, apart from permitted metadata and running-head text, with only
four required local notation commands appended. At its render checkpoint, the
validated PDF used fully embedded, subset Libertinus fonts and no Type 3 fonts,
and the then-current payload checksums, including the preserved ten-entry
arrival ledger, passed completely (18/18). That retained PDF predates the
current notation-only TeX; no PDF was regenerated. Its mutable current-live
ledger is being refreshed, while the arrival ledger remains immutable.

New standalone intake member:
[`Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`](Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/),
*Reciprocal-Integer Convolution Divisors of the Rvachev Law* (retained
35-A4-page PDF checkpoint; current live TeX: 2,307 lines, 90,871 bytes,
SHA-256
`e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e`;
with a 352-line exact/numerical experiment),
arrived from a rootless 14-file archive on 2026-08-30.  The package's
characteristic quotients
`Q_M(z) = Phi(z) / Phi(z/M)` classify reciprocal-integer decompositions of
the Rvachev law.  Its digit IFS and multiplicative cocycle lead to an exact
odd-singular/even-regular trichotomy, transport and inverse-Fabius bounds,
an arithmetic zero divisor and spectral zeta function, and finite
Thue--Morse quotients whose `M = 3` case recovers Stern/hyperbinary
coefficients.

This is a distinct sibling of the shape/Stein report under
[`../representations/`](../representations/): unequal reciprocal-scale
factors here do not conflict with that report's obstruction to identical
convolution roots.  The report nevertheless shares foundational zero-count,
Bernoulli/Bell, endpoint, and inverse-Fabius infrastructure with the
consolidated corpus, so it remains separate pending a theorem-by-theorem
crosswalk. The rootless archive supplied no checksum ledger or dependency
lock; at the repaired package checkpoint, the repository-generated 14-entry
`SHA256SUMS` covered every stored payload after five CSV files were normalized
to LF. The repair gives the
report a title-derived source/PDF pair and canonical A4/27 mm/Libertinus
styling; three final `pdflatex` passes produced the retained 35-page PDF with
all fonts embedded and subset, no Type 3 font, and no overfull box. Key pages and every
figure were inspected at that checkpoint. The PDF predates the current
notation-only TeX; no PDF was regenerated, no current source/PDF parity is
claimed, and the mutable live ledger is being refreshed. A temp-isolated
Python 3.12 replay regenerated every output: four
CSVs were byte-identical, the text summary was EOL-equivalent, and the endpoint
CSV had only 66 last-place differences (maximum `1.11e-16`).  All four PNGs
showed the expected layout drift between the unpinned packaged Matplotlib
3.10.8 and replayed 3.11.1 (1475 versus 1476 pixels wide), strengthening the
case for a dependency lock. The report cites the adjacent exact
`GeneralizedZeroDivisor` and `ReciprocalIntegerGammaZeros` APIs without
claiming that the quotient-family results themselves are formalized.
Manuscript theorem labels do not imply Lean proof status.

[`Fabius_Total_Positivity_Frontier_Report/`](Fabius_Total_Positivity_Frontier_Report/),
*Total Positivity and Cartwright Geometry in the Fabius--Rvachev Dyadic Sinc
Product* (retained 24-page PDF checkpoint; current live TeX: 1,060 lines,
58,362 bytes, SHA-256
`e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`),
arrived as a bare TeX/PDF/script package on 2026-08-30.
Its imaginary-square-root transform, Laguerre--Polya and multiplier-sequence
structure, exact zero divisor and Thue--Morse sign interpolation, Cartwright
geometry, and geometric-scale deformation extend the arithmetic/spectral
Fourier-product theme. The package shipped no checksum ledger, README,
environment pin, or captured run output. The repository repair regenerated
the four required figure/table inputs and four CSV evidence tables, normalized
the source to A4/Libertinus, rebuilt the PDF in three passes, and added a live
12-entry payload ledger; exact arrival hashes remain recorded in the global
manifest. That retained PDF predates the current notation-only TeX; no PDF was
regenerated, no current source/PDF parity is claimed, and the mutable live
ledger is being refreshed. The current source crosswalks the exact finite
general-base digit
count in `BaseDigitMultiplicity.lean` without promoting the analytic zero or
sign claims. Its novelty screen is already stale at its pinned
snapshot: matching Laguerre--Polya/PF-infinity/shifted-Jensen and zero-sign
material appears in `Frontier_Compilations/`. It therefore remains standalone
pending claim-by-claim crosswalk and deliberate deduplication. Its paper
theorem labels do not by themselves assert Lean status.

Arithmetic and spectral structure of the Rvachev Fourier product,
consolidated (2026-08-28) into the single volume
[`Spectra_and_Arithmetic_Frontiers/`](Spectra_and_Arithmetic_Frontiers/).
Its current live TeX has 8,183 lines and 349,076 bytes, with SHA-256
`683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`.
The retained PDF was not regenerated after the notation-only source change,
so its earlier render validation is a historical checkpoint rather than a
current source/PDF parity claim. The mutable live ledger is being refreshed.
The consolidated volume comprises:

- **Part I** — *Half-Integer Spectral Arithmetic*
  (formerly `Fabius_Half_Integer_Spectral_Frontier_Report/`);
- **Part II** — *Arithmetic Dyadic Rays of the Rvachev Fourier Product*
  (formerly `Fabius_Arithmetic_Rays_Frontier_Report/`);
- **Part III** — *Spectral Arithmetic and the Pascal–Rvachev Hierarchy*
  (formerly `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/`);
- **Part IV** — *Derivative Norm Spectra and Dual Moment Geometries of
  the Fabius–Rvachev System*
  (formerly `Fabius_Derivative_Norm_Spectrum_bundle/`, whose data,
  figures, and scripts live under `assets/`).

The member drafts were absorbed verbatim (labels, citation keys, and
asset paths mechanically prefixed per part; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
