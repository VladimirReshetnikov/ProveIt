# Spectra and arithmetic

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
  contains the 22-page *Automatic Scale Factorizations of the Rvachev Law*
  bundle from arrival commit `8a184546747082cbd92ad4675fb61981c6b8c3b6`.
  Six CSV hashes were refreshed for LF storage, and the JSON summary received
  its missing final newline; all 21 non-ledger payloads are covered.

- [`Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`](Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/)
  contains the 31-page *Dyadic Radon Profiles in the Fabius--Rvachev Web*
  bundle from `03b2f61889674f7d64ac86d3233236f5fa7ce660`.  Its 26-entry
  ledger now records the repository-normalized bytes; nine CSV entries
  changed only by CRLF-to-LF normalization.

- [`Fabius_Pascal_Frontiers_Report/`](Fabius_Pascal_Frontiers_Report/)
  contains the 27-page *Automatic Spectra, Exact Dyadic Cubature, and
  Probabilistic Duals in the Pascal--Rvachev Hierarchy* bundle from
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`.  The delivery had no checksum
  file, so the repository-generated `SHA256SUMS` covers all nine payloads.

- [`fabius_holonomic_frontiers_report/`](fabius_holonomic_frontiers_report/)
  contains the 30-page *Holonomic Rank, Exact Overlaps, and
  Non-P-Recursiveness* bundle from
  `6d6737530ec541196c506f95ec20a701a29872b3`.  Six CSV hashes in its
  otherwise complete 26-entry ledger were refreshed for LF storage.

- [`Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`](Fabius_Rvachev_Carleman_Frontiers_2026-08-30/)
  contains the 24-page *Critical Ultradifferentiable Geometry of the
  Fabius--Rvachev System* bundle from
  `92c9909242ed6a2ab51d68ed816d1aa2a5339719`.  Four CSV hashes in its
  complete 21-entry ledger were refreshed for LF storage.

- [`Dyadic_Spectral_Divisors_and_Gamma_Duality/`](Dyadic_Spectral_Divisors_and_Gamma_Duality/)
  is the title-derived filing of the generic incoming wrapper
  `Fabius_Rvachev_Frontier_Report-F/` from
  `d4605275f58f648ebcdeb74bc2ef5e4983abb6f0`.  The submitted three-entry
  ledger verifies exactly but is incomplete; the added
  `ARRIVAL_SHA256SUMS` covers all twenty delivered files, including that
  original ledger.

These reports overlap one another and the consolidated spectra volume in
zero-divisor arithmetic, Pascal/valuation profiles, derivative growth,
Laguerre--Polya and Pólya-frequency structure, holonomicity, and
non-P-recursiveness.  That claim-level comparison is intentionally deferred
until after publication.  A theorem label, proof in prose, symbolic
calculation, or numerical check in any manuscript does not imply that the
claim has been proved in Lean.

New standalone intake member:
[`Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](Digital_Spectral_Geometry_and_Log_Periodic_Saddles/),
*Digital Spectral Geometry and Log-Periodic Saddles* (24 A4 pp), arrived from the
rootless `Fabius_Rvachev_Frontier_Report_Package.zip` on 2026-08-30. The
title-based directory avoids collision with an unrelated q-series package
that used the same generic report filename. Its delivered zero-file audit was
replaced by a reproducible recursive audit of 140 prior TeX files (311,911
lines and 13,787,029 bytes) excluding this package directory, with raw corpus
digest `a6edc75336626f99b4a1a13e6d7b90dc14f8f2dede15b4a3de80879442932a2d`.
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
four required local notation commands appended. The validated PDF
uses fully embedded, subset Libertinus fonts and no Type 3 fonts. Current
payload checksums, including the preserved ten-entry arrival ledger, pass
completely (18/18).

New standalone intake member:
[`Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`](Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/),
*Reciprocal-Integer Convolution Divisors of the Rvachev Law* (34 A4 pp,
2303 source lines; with a 352-line exact/numerical experiment, six data files,
four PNG figures, and a README), arrived from a rootless 14-file archive on
2026-08-30.  The package's
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
crosswalk.  The rootless archive supplied no checksum ledger or dependency
lock; the repository-generated `SHA256SUMS` covers every stored payload after
five CSV files were normalized to LF.  The report now reproduces the primary
document's canonical A4 package, theorem, macro, boxed-environment, and listing
block verbatim apart from permitted metadata and running-head text; only the
required local settings, eight notation commands, status box, and Python
listing style follow it.  Exactly three strict serial `pdflatex` passes rebuilt
the 34-page PDF.  All 34 pages were text-checked and representative theorem,
figure, appendix-table, and bibliography pages were rendered visually.  All
25 fonts are embedded and subset, six faces are Libertinus, and no Type 3 font
is present.  A temp-isolated Python 3.13 replay with NumPy 2.5.2, Matplotlib
3.11.1, and mpmath 1.4.1 regenerated every output: four CSVs were
EOL-normalized exact, the text summary was byte-identical, and the endpoint CSV
had only 65 last-place differences (maximum `1.11e-16`).  All four PNGs showed
the expected unpinned-Matplotlib layout drift (1475 versus 1476 pixels wide),
strengthening the case for a dependency lock.  Lean was not run.  Manuscript
theorem labels do not imply Lean proof status.

New standalone intake member:
[`Fabius_Total_Positivity_Frontier_Report/`](Fabius_Total_Positivity_Frontier_Report/),
*Total Positivity and Cartwright Geometry in the Fabius--Rvachev Dyadic Sinc
Product* (22 pp), arrived as a bare TeX/PDF/script package on 2026-08-30.
Its imaginary-square-root transform, Laguerre--Polya and multiplier-sequence
structure, exact zero divisor and Thue--Morse sign interpolation, Cartwright
geometry, and geometric-scale deformation extend the arithmetic/spectral
Fourier-product theme. The package shipped no checksum ledger, README,
environment pin, or captured run output. Its TeX also depends on four absent
generated figure/table inputs, and the script's four CSV evidence tables were
not delivered; exact arrival hashes and filenames are recorded in the global
manifest. Its novelty screen is already stale at its pinned
snapshot: matching Laguerre--Polya/PF-infinity/shifted-Jensen and zero-sign
material appears in `Frontier_Compilations/`. It therefore remains standalone
pending claim-by-claim crosswalk and deliberate deduplication. Its paper
theorem labels do not by themselves assert Lean status, and its shipped Latin
Modern source/PDF still needs canonical-preamble and Libertinus normalization
in a later post-intake commit.

Arithmetic and spectral structure of the Rvachev Fourier product,
consolidated (2026-08-28) into the single volume
[`Spectra_and_Arithmetic_Frontiers/`](Spectra_and_Arithmetic_Frontiers/):

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
