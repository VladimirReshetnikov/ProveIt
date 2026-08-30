# Integration and transforms

Antiderivatives, integral calculus, transform dualities, and fractional
calculus of the Fabius–Rvachev system, consolidated (2026-08-28) into
the single volume
[`Integration_and_Transform_Frontiers/`](Integration_and_Transform_Frontiers/)
(369 pp, twelve parts):

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

The current ordinary Cauchy–Stieltjes foundation starts in
`MeasureCauchyTransform.lean`, which packages oriented transforms and every
kernel power, affine naturality, slit-domain calculus, and the DDE/adjacent
power recurrence of an arbitrary uniform affine fixed-point measure.  The law
need not be normalized and its invariant carrier needs no topology or
measurability.  `GeometricUniformCauchy.lean` specializes this to every
nonzero real `|q| < 1`, including negative ratios.  `CauchyTransform.lean`
then gives the canonical unit and centered transforms and powers, their
measure/density forms, the transform and all-power affine bridges, the direct
named unit equation `S'(z) = 4(S(2z) - S(2z - 1))`, and both complex-slit
adjacent-power recurrences.  `CauchyCDF.lean`, `CauchySurvival.lean`, and
`CauchyHigherPowers.lean` supply atom-exact CDF/survival integration by parts
at every positive kernel power; `CauchyRenormalization.lean` supplies the
centered DDE and its all-order finite Thue--Morse orbit.

The merged Stieltjes modules also prove the real logarithmic fixed point and
positive integer hierarchy for `z > 1`, real order lowering for `α > 1`,
real/complex exterior Laurent series, finite-height Herglotz--Poisson
identities, integrated interval Stieltjes--Perron inversion, and initial exact
Jacobi data.  Complex logarithmic continuation, complex order,
pointwise/nontangential Sokhotski--Plemelj and principal-value Hilbert
formulas, the separate explicit Thue--Morse higher-kernel identity, and the
full J-fraction/Padé theory remain open.

Part VI's positive-real causal Rvachev primitive and semigroup are now exact
Lean theorems.  `FabiusFractionalVolterra.lean` defines the total
`rvachevFractionalPrimitive`, identifies its compact-support cutoff at
`min x 1`, bridges every positive natural order to `normalizedVolterra`, and
proves additive composition of positive real orders on `x ≥ -1`.  The
transform and tail series, endpoint-moment and shifted-lattice formulas,
complex orders, and fractional derivatives remain frontier claims.

The independent 2026-08-28 `Fabius_Integral_Transforms_Report` arrival is now
absorbed as Part XII; it is no longer an unmerged member.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
