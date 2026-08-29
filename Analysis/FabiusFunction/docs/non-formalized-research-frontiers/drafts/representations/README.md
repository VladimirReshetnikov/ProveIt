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
`S(z) = 2 R(2z - 1)`.  `AffineDifferenceOrbit.lean` formalizes the reusable
conditional all-order passage.  The logarithmic fixed point, the one-step
resolvent DDE, and hence its measure-specific Thue--Morse orbit and kernel
identity remain open.)

## Post-snapshot finite Gram--Stieltjes checkpoint

This status postdates the absorbed-draft hashes and pinned audit commits in
the consolidated volume; it does not revise their provenance or novelty
boundary.  At Lean source checkpoint `b3720d4b5`, the generic finite-algebra
layer consists of:

- `FiniteMomentGram.lean`: `momentFunctional`, `momentPairing`,
  `momentHankelMatrix`, `momentHankelDet`, and `finiteMomentPairing`, together
  with monomial and pure-power evaluation, support and bounded-range sums,
  scalar base change, the exact monomial-basis Gram-matrix identification
  `finiteMomentPairing_toMatrix`, and the integral-domain equivalence
  `finiteMomentPairing_nondegenerate_iff`;
- `GramStieltjes.lean`: the adjugate-column construction
  `gramStieltjesNumerator`, its lower-power orthogonality, top coefficient,
  next-determinant pairing, coefficient-extraction, and self-pairing
  identities; and, over a field, `gramStieltjesPolynomial`, its conditional
  monicity and exact degree, lower-degree orthogonality, uniqueness, and
  consecutive-Hankel-determinant self-pairing quotient.

These modules treat an arbitrary scalar moment sequence and finite linear
algebra only.  They do not identify that sequence with the analytic Fabius
moments, prove either moment or three-term recurrences, establish positivity
or determinant nonvanishing, locate roots, construct quadrature, or prove a
Jacobi/Stieltjes fraction or its convergence.

The mathematical bodies of the member drafts were preserved (labels,
citation keys, and asset paths were mechanically prefixed per part),
with top-level counters and reproduction instructions adapted to the
consolidated layout. Their standalone TeX/PDF pairs were deleted;
provenance with SHA-256 hashes is recorded in the volume itself, and git
history is the archive. Reproducibility files remain under the volume's
`assets/` directory, with each former package's README updated for its
new location.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and provenance.
