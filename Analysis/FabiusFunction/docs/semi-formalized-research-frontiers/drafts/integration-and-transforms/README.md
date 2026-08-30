# Integration and transforms

Antiderivatives, integral calculus, transform dualities, and fractional
calculus of the Fabius–Rvachev system, consolidated (2026-08-28) into
the single volume
[`Integration_and_Transform_Frontiers/`](Integration_and_Transform_Frontiers/)
(370 pp, twelve parts):

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

The current ordinary Cauchy–Stieltjes layer is formalized across
`CauchyTransform.lean`, `CauchyCDF.lean`, `CauchySurvival.lean`,
`CauchyHigherPowers.lean`, the `Stieltjes*.lean` modules,
`PoissonApproximateIdentity.lean`, `PoissonMassSwap.lean`,
`OrthogonalPolynomialJacobi.lean`, and `CauchyRenormalization.lean`. It includes
the report-oriented unit and up-law transforms and affine bridge; CDF and
survival integration by parts at every positive resolvent power; real
logarithmic and real-order resolvent hierarchies; real and complex exterior
Laurent expansions; finite-height Herglotz–Poisson identities; integrated
interval Stieltjes–Perron inversion; initial exact Jacobi data; and the up-law
derivative DDE with its all-order finite Thue–Morse orbit. A direct named
unit-interval Stieltjes DDE, complex logarithmic continuation, named
Laplace/Fourier forms, complex order, pointwise/nontangential Plemelj and
principal-value Hilbert-transform formulas, the full J-fraction/Padé package,
and a separate higher-kernel integral form of the Thue–Morse orbit remain open.

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
