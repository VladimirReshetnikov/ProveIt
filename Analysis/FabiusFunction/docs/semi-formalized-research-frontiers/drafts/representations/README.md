# Representations

Series and orthogonal-expansion representations of the up-function,
consolidated (2026-08-28) into the single volume
[`Representation_Frontiers/`](Representation_Frontiers/) (296 pp,
eight parts):

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
  `Fabius_Rvachev_Multiresolution_Report/`);
- **Part IV** — *Integral, Series, Product, and Operator
  Representations* (Fredholm, exterior-power, total-positivity,
  heat-kernel, and Mellin–Barnes bridges; formerly
  `fabius_rvachev_report_package/`);
- **Part V** — *Polyphase, Operator, and Jump-Measure Representations*
  (formerly `Fabius_Rvachev_Polyphase_Representation_Report/`);
- **Part VI** — *Sampling, Padé, Mellin, Resolvent, and
  Product–Integral Representations* (formerly
  `Fabius_Rvachev_Thue_Morse_Representation_Frontiers/`);
- **Part VII** — *Unit-Circle, Bessel, and Spectral–Monodromy
  Representations* (formerly `rvachev_fabius_representations_2026/`);
- **Part VIII** — *Dyadic Multiresolution and Sampling Frontiers*
  (formerly `Fabius_Rvachev_Multiresolution_Representations/`).

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

The reciprocal-Gamma portion of Part II is now formal at source checkpoint
`71ab6f6728fceb753c88d8b0573077a59acf2682`.  The reusable convergence engine
is `ScaledInfiniteProducts.lean`; `GeometricReciprocalGamma.lean` constructs
the entire product
`G_q(z) = product_n Gamma(1 + q^n z)^(-1)` for complex `q` with `‖q‖ < 1`,
proves its Mahler equation, zero orbit, reflection, and dyadic Rvachev bridge;
and `DyadicGammaOrder.lean` proves the exact negative-integer zero set and
dyadic zero/pole orders.  The Gamma-side functions are totalized pointwise
inverses, with poles recorded by negative meromorphic order.  Still open are
the raw Gamma tprod away from its poles, arithmetic canonical regrouping,
logarithmic/digamma/Malmsten/heat/integral identities, D-finiteness,
general-base pole orders, and the reciprocal-Gamma derivative coefficient
needed by the separate Thue--Morse tower.

That paragraph is retained as the historical
`71ab6f6728fceb753c88d8b0573077a59acf2682` boundary.  The current overlay pins
the next tranche to `0ba35abd4`: the five public declarations of
`ReciprocalGammaJets.lean` are `deriv_Gamma_inv_neg_nat`,
`hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`,
`analyticOrderAt_Gamma_inv_neg_nat`, and `tendsto_Gamma_inv_div_add_nat`.
They establish the exact first jet, simple analytic order, and punctured local
coefficient of the entire reciprocal Gamma function at every nonpositive
integer, without assigning a derivative to raw Gamma at a pole.

The first eight public declarations of `ThueMorseGammaTower.lean` at that commit
are `hasDerivAt_dirichletMellinContinuation_neg_nat`,
`deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`,
`thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`,
`thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, and
`thueMorseGammaTower_dyadic`; the current integrated tree adds
`ofReal_exp_mpLimit_eq_gammaTower_div` as the ninth.  Their definitions are
total for every real parameter, while the Mellin, integral, dyadic, and ratio
theorems use positive parameters.  GammaLog is a chosen derivative coordinate,
not a proved `Complex.log` identity.  Only the parameter differential/iterated
ladder remains open within this tower; the raw Gamma tprod, arithmetic
canonical regrouping, Gamma-product logarithmic/digamma/Malmsten/heat-trace
identities, D-finiteness, and general-base pole orders remain separate
frontiers.

The mathematical bodies of the member drafts were preserved (labels,
citation keys, and asset paths were mechanically prefixed per part),
with top-level counters and reproduction instructions adapted to the
consolidated layout. Their standalone TeX/PDF pairs were deleted;
provenance with SHA-256 hashes is recorded in the volume itself, and git
history is the archive. Reproducibility files remain under the volume's
`assets/` directory, with each former package's README updated for its
new location.

Parts IV–VIII arrived 2026-08-28 as the five second-wave reports,
were first consolidated into an interim companion volume
(`Representation_Second_Wave/`, 183 pp), and were folded into the
main volume as Parts IV–VIII the same day.  The fold repaired a
rendering defect of the interim volume (its parts after the first
were numbered with `\appendix` letters running across part
boundaries, so sections collided as E–T/A–C/D–…; per-part arabic
numbering is now restored), restored the members' full part titles
(the interim volume had abbreviated three of them to one word), and
deduplicated colliding macro definitions between the waves; every
editorial intervention is marked `% ed.:` in the source.  Same
content-preserving discipline as the per-part merges; absorbed
member directories and the interim volume deleted, provenance with
SHA-256 for all eight sources in the volume's front matter.

The two fourth-wave polynomial-representation drafts (2026-08-28) were
merged the same day into the volume
[`Up_Polynomial_Synthesis/`](Up_Polynomial_Synthesis/) (*Exact
Polynomial Synthesis from Rvachev Up-Atoms*, 22 pp): the common-scale
dictionary construction (formerly
`Rvachev_Up_Polynomial_Representation_Package/`, *Exact Polynomial
Synthesis by Finite Rvachev Up-Function Dictionaries*) and the
antiderivative-train window construction (formerly
`rvachev_up_polynomial_representation/`, *Exact Polynomial Windows from
Finite Sums of Shifted and Scaled Rvachev up Functions*).  Unlike the
mechanical merges above, this is an editorial consolidation: shared
foundations stated once, the two constructions compared, the minimal
atom count sharpened to `N_d <= d+2`, and the canonical defect
identified with the shifted-quadrature first failure of the
`Dyadic_Comb_Frontiers` volume (exact special values via the spectral
Dirichlet values `D(2r)`).  A third source, the seventh-wave draft
`Rvachev_Up_Exact_Polynomial_Representation_Report/` (*Exact
Polynomial Plateaux from Rvachev's Up-Function*), was absorbed the
same day as the oversampled-lattice chapter: twisted Poisson
summation, exact reproduction order `v_2(m)` at radius-to-spacing
ratio `m` with the general-ratio defect series, the physical-scale
interval algorithm (`O(d)`-element description, `(2m+1)`-local
evaluation, full endpoint-jet matching), ghost-atom antiderivative
calculus, the exact Thue–Morse dyadic derivative stencil (convolution
inverse of the ladder's binary-partition weights), finite sinc-prefix
generators with the exact cumulant truncation law, and
odd-denominator cumulant arithmetic; its rational-arithmetic
verification package lives under
`assets/Rvachev_Up_Exact_Polynomial_Representation_Report/`.
Absorbed directories deleted; provenance with SHA-256 in the volume's
Appendix B and `assets/SHA256SUMS-absorbed.txt`.

`Legendre_Rvachev_Self_Reconstruction/` (*Legendre--Rvachev
Self-Reconstruction on [-1,1]*) landed 2026-08-29 and is **pending
merge into `Up_Polynomial_Synthesis/`**.  It is not a seventh
Lagrange-loop sibling: the six loop reports synthesize *Lagrange
cardinals* from shifted up-atoms, whereas this one turns the Legendre
strand inward, onto the self-reconstruction and energy structure of up
itself.  Its own `CORPUS_AUDIT.md` names
`lagrange_rvachev_loop_report_v3/` as the directly preceding
Legendre-aware report and lists what it imports rather than claims.
New here: exact orthogonality of the finite self-translate blocks,
Pythagorean tails and a Sobolev energy hierarchy, a positive rational
series and an infinite-sinc integral for the energy constant
`A_2 = int_0^1 F^2`, interlevel null trains with a quarter-grid lifting
decomposition, Hilbert--Schmidt identities for the even-projector
factorization, and a sharp central-coefficient root law.  Its
theorem-level checks are exact rational with residual `0`; the reported
energy value is a stabilized display of an exact partial sum, not a
certified enclosure of the limit, and the report says so.
Subsequent Lean module `FabiusLegendreEnergy.lean` now defines the
polynomial-form blocks `B_n = u_n*P_(2n)` and proves exactly their complete
orthogonality, the coefficient Parseval identity, the shifted coefficient-tail
identity in both `HasSum` and `tsum` forms, and the real-variable Legendre
series for `A_2`.  The blocks' finite up-translate realization and atom-Gram
formula, the report's Fourier-product and infinite-sinc integrals, and its
rationality claim for the partial sums remain outside that formalized tranche.

Three further Legendre-closure reports landed the same day, all
**pending merge into `Up_Polynomial_Synthesis/`** and all answering the
same question from different angles:
`legendre_rvachev_closed_loop/` (*Legendre--Rvachev Biorthogonal
Closure*) carries the arithmetic — exact `u_n` to `n=80` with 2-adic
valuations, reciprocal-MGF coefficients, and exact spectral sum rules;
`Legendre_Rvachev_Closed_Loop_Report_v3/` (*Legendre Polynomials in the
Rvachev Up Dictionary*) is the widest, and the only one to study the
**root geometry** of the deconvolved Legendre polynomials, with Sturm
certificates and an explicit Favard obstruction showing the family is
orthogonal for no measure; `Legendre_Rvachev_Closed_Loop_Report_v4/`
(*A One-Scale Legendre--Rvachev Closure*) is the narrowest by design,
restricting to a single scale.  The `_v3`/`_v4` suffixes are
deliberate: those two archives share a top-level directory name.

Together with `Legendre_Rvachev_Self_Reconstruction/` these make four
same-day Legendre reports beside the six Lagrange-loop ones, so the
pending merge into `Up_Polynomial_Synthesis/` now has ten members
waiting.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and provenance.
