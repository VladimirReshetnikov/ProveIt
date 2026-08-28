# Representations

Series and orthogonal-expansion representations of the up-function,
consolidated (2026-08-28) into the single volume
[`Representation_Frontiers/`](Representation_Frontiers/) (108 pp):

- **Part I** — *Resolvent, Continued-Fraction, and Transform
  Representations of the Fabius–Rvachev System* (Jacobi coefficients,
  exact even moments, resolvent and logarithmic-derivative identities;
  formerly
  `Fabius_Rvachev_Representation_Frontiers/`);
- **Part II** — *Representation Atlas and New Analytic Bridges for the
  Fabius Function, Rvachev's Up-Function, and Their Fourier Images*
  (formerly `fabius_rvachev_representation_frontier/`);
- **Part III** — *Dyadic Multiresolution and Product–Series
  Representations* (rational mass arrays, Haar–Schauder expansions,
  Walsh–Thue–Morse products, beta-mixture limits, Bell–Bernoulli scale
  energies, inverse-quantile duality; formerly
  `Fabius_Rvachev_Multiresolution_Report/`).

(The random-variable representation is formalized in
`ProbabilityRepresentation.lean`, and `RandomSeriesLaw.lean` identifies the
unit-interval law with the affine image of the up measure.
`CauchyTransform.lean` defines the report-sign Cauchy--Stieltjes transforms and
proves their measure forms, the up-density form, holomorphy off the named interval cuts,
first-derivative kernel formulas, and the affine bridge
`S(z) = 2 R(2z - 1)`.  `CauchyCDF.lean` proves atom-exact compact-support
integration by parts for arbitrary finite measures with almost-everywhere
interval support, its probability-CDF normalization, and
`S(z) = (z - 1)⁻¹ - ∫₀¹ F(t) (z - t)⁻² dt` off `[0,1]`.
`CauchyRenormalization.lean` proves that both dyadic branches preserve the
up-transform slit domain, establishes
`R'(z) = 2 (R(2z + 1) - R(2z - 1))` there, and instantiates the reusable
`AffineDifferenceOrbit.lean` engine to obtain the exact all-order finite
Thue--Morse derivative orbit.  The logarithmic fixed point, the separate
higher-Cauchy-kernel integral identity, a named Stieltjes-transform DDE,
boundary/Plemelj formulas, moment/Laurent expansions, generalized order, and
Jacobi/Padé theory remain open.)

The mathematical bodies of the member drafts were preserved (labels,
citation keys, and asset paths were mechanically prefixed per part),
with top-level counters and reproduction instructions adapted to the
consolidated layout. Their standalone TeX/PDF pairs were deleted;
provenance with SHA-256 hashes is recorded in the volume itself, and git
history is the archive. Reproducibility files remain under the volume's
`assets/` directory, with each former package's README updated for its
new location.

A second wave of five separate member reports arrived 2026-08-28 and
stays unmerged until deliberately folded into the volume:
`Fabius_Rvachev_Multiresolution_Representations` (dyadic
multiresolution and sampling frontiers),
`Fabius_Rvachev_Polyphase_Representation_Report` (polyphase,
operator, and jump-measure representations),
`Fabius_Rvachev_Thue_Morse_Representation_Frontiers` (sampling,
Padé, Mellin, resolvent, and product–integral atlas),
`rvachev_fabius_representations_2026` (unit-circle, Bessel, and
spectral–monodromy representations), and
`fabius_rvachev_report_package` (integral, series, product, and
operator representations with Fredholm and Mellin–Barnes bridges).

See [`../MANIFEST.md`](../MANIFEST.md) for titles and provenance.
