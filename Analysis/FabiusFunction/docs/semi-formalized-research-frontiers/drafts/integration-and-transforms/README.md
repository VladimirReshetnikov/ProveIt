# Integration and transforms

Antiderivatives, integral calculus, transform dualities, and fractional
calculus of the Fabius–Rvachev system, consolidated (2026-08-28) into
the single volume
[`Integration_and_Transform_Frontiers/`](Integration_and_Transform_Frontiers/)
(369 pages; twelve parts):

- **Part I** — *Antiderivatives of Monomially Weighted Fabius-Type
  Functions* (formerly `Fabius_Antiderivatives_Report/`);
- **Part II** — *Fabius Monomial Antiderivatives and Inverse-Quantile
  Integrals* (formerly `Fabius_Monomial_Antiderivatives_Report/`);
- **Part III** — *Dyadic Primitive Ladders and Mellin–Newton
  Antiderivatives* (formerly `fabius_monomial_antiderivatives_report-2/`);
- **Part IV** — *Integral Calculus and Transform Dualities*
  (formerly `Fabius_Integral_Transforms_Report/`);
- **Part V** — *Integral and Transform Frontiers*
  (formerly `Fabius_Integral_and_Transform_Frontiers/`);
- **Part VI** — *Integral and Transform Frontiers* (bundle variant,
  formerly `fabius_integral_frontiers_bundle/`);
- **Part VII** — *Integral Transforms and Fractional Calculus*
  (formerly `Fabius_Rvachev_Integral_Frontiers/`);
- **Part VIII** — *Integral, Transform, and Fractional Frontiers*
  (formerly `Fabius_Integral_Transform_Fractional_Frontiers/`);
- **Part IX** — *Fractional Integral Calculus and Complex-Order
  Transform Hierarchies* (formerly
  `Fabius_Rvachev_Fractional_Integral_Report/`);
- **Part X** — *Integral, Transform, and Fractional-Order Frontiers*
  (formerly `Fabius_Fractional_Integral_Transform_Frontiers/`);
- **Part XI** — *Fabius Fractional Transform Frontiers*
  (formerly `fabius_fractional_transform_frontiers_bundle/`);
- **Part XII** — *Integral and Transform Calculus for the
  Fabius–Rvachev–Quantile System* (the second-wave arrival of
  2026-08-28, formerly `Fabius_Integral_Transforms_Report/` — an
  independent report sharing its directory name with Part IV's
  2026-08-27 source; folded in 2026-08-28 by the same mechanical
  per-part step, support files under
  `assets/Fabius_Integral_Transforms_Report_second_wave/`).

The member drafts were absorbed verbatim (labels, citation keys, and
asset paths mechanically prefixed per part; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

The current ordinary Cauchy–Stieltjes foundation is formalized in
`CauchyTransform.lean`: it defines the report-oriented transforms of the
canonical up and unit-interval laws, proves their measure forms, the up-density
form, holomorphy off the named interval cuts, first-derivative kernel formulas,
and the affine bridge.  In Lean's totalized Bochner-integral convention the
bridge holds for every complex argument; in its classical analytic
interpretation it reads `S(z) = 2 R(2z - 1)` off `[0,1]`, equivalently in the
reverse direction off `[-1,1]`.  `CauchyCDF.lean` adds atom-exact
integration by parts for a finite measure almost everywhere supported on an
ordered compact interval and a spectral parameter off its complexification,
its probability-CDF normalization, and the exact Fabius formula
`S(z) = (z - 1)⁻¹ - ∫₀¹ F(t) (z - t)⁻² dt` on the unit-interval
slit domain.  `CauchyRenormalization.lean` proves invariance of the up-law
slit domain under both dyadic branches, the exact equation
`R'(z) = 2 (R(2z + 1) - R(2z - 1))`, and its all-order finite Thue--Morse
derivative orbit for every natural order.  The affine bridge makes a
unit-interval Stieltjes DDE an unexported consequence; no named wrapper is
claimed.  Logarithmic fixed points, survival and higher resolvent-power
wrappers, the separate higher-kernel integral identity, moment/Laurent and
Laplace/Fourier expansions, boundary/Plemelj theory, generalized complex
order, and second-kind/J-fraction/Padé transform identification remain open.

Part VI's positive-real causal Rvachev primitive and semigroup are now exact
Lean theorems.  `FabiusFractionalVolterra.lean` defines the total
`rvachevFractionalPrimitive`, identifies its compact-support cutoff at
`min x 1`, bridges every positive natural order to `normalizedVolterra`, and
proves additive composition of positive real orders on `x ≥ -1`.  The
transform and tail series, endpoint-moment and shifted-lattice formulas,
complex orders, and fractional derivatives remain frontier claims.

The generic finite algebra is supplied by `FiniteMomentGram.lean` and
`GramStieltjes.lean`.  They construct moment functionals, symmetric pairings,
finite Hankel matrices and determinants, a fraction-free adjugate polynomial,
and—over a field with the leading determinant nonzero—the unique normalized
monic orthogonal polynomial with its consecutive-determinant self-pairing
formula.  These modules are deliberately measure-free and make no positivity
claim by themselves.  The complementary Fabius-specific pipeline in
`MomentHankelMatrix.lean`, `MomentHankelValues.lean`, and the
`OrthogonalPolynomial*.lean` modules proves strict positivity, identifies the
up moments, constructs the monic polynomials, proves parity and the symmetric
three-term recurrence, and computes the first exact Jacobi data.  Root and
quadrature theorems, finite and infinite J-fraction identification, and
continued-fraction convergence remain open formalization work.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
