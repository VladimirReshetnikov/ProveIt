# Spectra and arithmetic

New standalone intake members from the current archival batch:

- [`Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`](Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/),
  *Dyadic Radon Profiles in the Fabius--Rvachev Web* (31 letter-paper pp,
  2,064 source lines; with a 624-line program, ten data files, and four
  PDF/PNG figure pairs), arrived on 2026-08-30 as an already-unpacked bare
  directory. Its submitted ledger covers all 26 non-ledger payloads; nine
  CSV entries were refreshed after CRLF-to-LF normalization and the complete
  ledger now verifies. The title and abstract concern spectral reconstruction
  of dyadic projection profiles, zero multiplicities, q-sampled cumulants,
  automatic signs, Pascal factorizations, and exact cubature.

- [`Fabius_Pascal_Frontiers_Report/`](Fabius_Pascal_Frontiers_Report/),
  *Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals in the
  Pascal--Rvachev Hierarchy* (27 A4 pp, 1,943 source lines; with a 426-line
  program, four CSV tables, and a captured numerical summary), arrived as a
  nine-file bare directory. It supplied no checksum ledger or dependency
  lock; the repository-added `SHA256SUMS` records and verifies all nine
  payloads. The title and abstract concern higher-rank spectral signs and
  Lambert series, dyadic cubature, Laguerre--Pólya/Pascal hierarchies, and
  probabilistic spectral duals.

- [`Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`](Fabius_Rvachev_Carleman_Frontiers_2026-08-30/),
  *Critical Ultradifferentiable Geometry of the Fabius--Rvachev System*
  (24 A4 pp, 1,941 source lines; with a 544-line program, four CSV tables,
  and five PDF/PNG figure pairs), arrived as an already-unpacked bare
  directory. Its submitted 21-entry payload ledger now verifies after four
  CSV entries were refreshed for CRLF-to-LF normalization. The title and
  abstract extend the derivative spectrum into Denjoy--Carleman scales,
  discrete Fourier duality, lattice corrections, Lambert-W saddles, and
  Bell-edge behavior.

- [`Dyadic_Spectral_Divisors_and_Gamma_Duality/`](Dyadic_Spectral_Divisors_and_Gamma_Duality/),
  *Dyadic Spectral Divisors and Gamma Duality* (22 A4 pp, 1,301 source lines;
  with a 379-line program, seven generated outputs, and three PDF/PNG figure
  pairs), arrived in the generic bare wrapper
  `Fabius_Rvachev_Frontier_Report-F/` and was filed under this title-derived
  collision-safe name. Its submitted ledger covered only 3 of 19 payloads;
  the expanded repository ledger records and verifies all 19. The title and
  abstract concern the dyadic zero divisor, Laguerre--Pólya and non-holonomic
  structure, reciprocal-base counting, heat traces, Gamma/Thorin duality, and
  Lambert inversion.

- [`fabius_holonomic_frontiers_report/`](fabius_holonomic_frontiers_report/),
  *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness in the
  Fabius--Rvachev System* (30 A4 pp, 2,279 source lines; with a 644-line
  experiment, six CSV tables, a generated TeX fragment, a captured text
  check, and five PDF/PNG figure pairs), arrived as a bare directory. Its
  submitted ledger covers all 26 non-ledger payloads and now verifies after
  six CSV entries were refreshed for CRLF-to-LF normalization. All six
  delivered PDFs are readable and unencrypted (35 pages total), and the title
  and abstract concern finite sinc-product differential rank, exact signed
  overlaps, dyadic Thue--Morse/frequency spectra, and non-D-finiteness.

These five packages remain standalone pending post-publication claim review,
experiment assessment, semantic comparison, and Lean crosswalks. Manuscript
result, proof, novelty, and numerical labels do not establish Lean
verification.

New standalone intake member:
[`Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`](Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/),
*Reciprocal-Integer Convolution Divisors of the Rvachev Law* (32 pp),
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
crosswalk.  The rootless archive supplied no checksum ledger or dependency
lock; the repository-generated `SHA256SUMS` covers every stored payload after
five CSV files were normalized to LF.  All 32 PDF pages were rendered during
intake.  A temp-isolated Python 3.12 replay regenerated every output: four
CSVs were byte-identical, the text summary was EOL-equivalent, and the endpoint
CSV had only 66 last-place differences (maximum `1.11e-16`).  All four PNGs
showed the expected layout drift between the unpinned packaged Matplotlib
3.10.8 and replayed 3.11.1 (1475 versus 1476 pixels wide), strengthening the
case for a dependency lock.  TeX and Lean were not run.  Manuscript theorem
labels do not imply Lean proof status.

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
