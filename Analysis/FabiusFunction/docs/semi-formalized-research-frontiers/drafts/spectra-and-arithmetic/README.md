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
  contains *Automatic Scale Factorizations of the Rvachev Law* (22 A4 pp,
  1,702 source lines; with a 473-line program, eight data outputs, and three
  PDF/PNG figure pairs), from arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. Its submitted ledger covers all
  21 non-ledger payloads and verifies after six CSV hashes were refreshed for
  LF storage and the JSON summary's missing final newline was repaired. Its
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
  in the Pascal--Rvachev Hierarchy* (27 A4 pp, 1,943 source lines; with a
  426-line program, four CSV tables, and a captured numerical summary), from
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. The nine-file delivery had no
  checksum ledger or dependency lock, so the repository-generated
  `SHA256SUMS` records and verifies all nine payloads. Its higher-rank spectral
  signs and Lambert series, dyadic cubature, Laguerre--Pólya/Pascal hierarchy,
  and probabilistic duals remain pending comparison.

- [`fabius_holonomic_frontiers_report/`](fabius_holonomic_frontiers_report/)
  contains *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness in the
  Fabius--Rvachev System* (30 A4 pp, 2,279 source lines; with a 644-line
  experiment, six CSV tables, a generated TeX fragment, a captured text
  check, and five PDF/PNG figure pairs), from
  `6d6737530ec541196c506f95ec20a701a29872b3`. Six CSV hashes in its complete
  26-entry ledger were refreshed for LF storage. All six delivered PDFs are
  readable and unencrypted (35 pages total); the report concerns finite
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
in a later post-intake commit.  Its roadmap instruction to formalize the
finite cumulative multiplicity-count/digit-sum arithmetic is now stale:
BaseDigitMultiplicity.lean proves the cumulative floor-layer and base-b digit
recovery formulas for every integer base greater than one, including composite
bases and the zero endpoint.  That five-theorem arithmetic layer does not
identify analytic zero orders or prove the report's sign interpolation, which
remain part of the later claim-by-claim audit.

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
