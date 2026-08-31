# Spectra and arithmetic

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
