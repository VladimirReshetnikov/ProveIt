# Inverse and sampling

This theme has three live navigation targets:

- [`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/)
  — the canonical inverse-Fabius synthesis;
- [`comb-interpolation/comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/)
  — the canonical additive and geometric comb synthesis;
- [`fabius_information_frontier/`](fabius_information_frontier/)
  — a separate information-geometry intake whose source/PDF synchronization
  and claim-level acceptance remain explicitly qualified.

## Canonical inverse synthesis

[*Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic
Sampling*](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.tex)
([PDF](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.pdf))
is the canonical editorial synthesis of five formerly live packages. It covers
dense-open analyticity and non-elementarity, positive inverse iterates,
inverse-dyadic germs, Barnes--Rvachev deconvolution, all-orders endpoint
inversion, dyadic self-sampling, exact inverse moduli, and certified
computation.

Its
[`theorem_concordance.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/theorem_concordance.csv)
fully dispositions all 194 immutable source-result rows: 54 are Lean-proved,
91 are human-proved frontier results, 10 are conjectures, 15 are open
problems, and 24 are non-applicable source environments.
[`LEAN_CROSSWALK.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/LEAN_CROSSWALK.md)
records exact module/declaration matches and separately classifies five
post-snapshot additions without changing those source totals.
[`ASSET_DISPOSITION.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/ASSET_DISPOSITION.csv)
accounts for all 88 source-subgroup files, and the live asset ledger covers 63
retained, deduplicated payloads.

The ten newest exact source-row matches are abstract effective inversion,
centered Appell deconvolution, positive-degree Appell mean-zero,
arbitrary-phase polynomial deconvolution,
`is:p3:cor:forced-superconvergence`, and
`is:p3:thm:Appell-lattice-reproduction`, together with the exact-dyadic
repository modulus, `is:p2:thm:Laurent-leading`,
`is:p2:thm:finite-prefix-expansion`, and `is:p2:thm:exact-recovery`.
The superconvergence pair is the parity-selected degree-`N+1` quadrature and
its explicit Rvachev--Appell lattice specialization.

`FabiusFunction.RvachevLaurentLeading` contributes one definition and six
theorems. Its manuscript-normalized punctured-neighborhood limit makes
`is:p2:thm:Laurent-leading` exact, together with the Fourier-product
coordinate, odd-core evaluation and nonvanishing, generic cofactor limit, and
general integer-pole companion. Puncturing is essential because Lean
totalizes inversion at the pole; lower Laurent coefficients and downstream
coefficient asymptotics remain outside this promotion. This first raised the
inverse concordance to 52 Lean-proved rows.

The eleven-definition/seventeen-theorem
`FabiusFunction.FinitePrefixAppellRecovery` module then makes both
finite-prefix rows exact. Its direct formulas hold for all `N,n`, including `N = 0`,
with uncentered base `1/2` and centered base `1/4`; its recovery theorems use
respectively `n+1` and `⌊n/2⌋+1` consecutive prefixes. Exact degrees `n` and
`⌊n/2⌋` are degrees of the outer scale polynomials in
`Polynomial (Polynomial ℚ)`. A fixed-inner-`x` centered specialization can
drop degree, for example at odd `n` and `x = 0`. The prefix moments form an
algebraic finite-convolution model; no random-variable, `HasLaw`, or
analytic-MGF realization is claimed. These two promotions give the current
inverse concordance totals: 54 Lean-proved and 91 human-proved frontier rows,
with the other categories unchanged.

The retained, fully reviewed publication checkpoint has 134 A4 pages and
2,027,726 bytes, with SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
Its historical three-pass receipt and page/font/visual gates, together with the
independently checked current 23-input source closure, are recorded in the
canonical package's
[`VALIDATION.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/VALIDATION.md).
The source changed after that render, so a fresh three-pass build remains
necessary before source/PDF synchronization is claimed.

The immutable extraction pin is
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`. The five old layouts are also
recoverable together at
`93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
snapshot. Their former paths, nested predecessor packages, arrival hashes, and
asset dispositions are recorded in
[`PROVENANCE.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/PROVENANCE.md);
they are provenance locators, not live navigation targets.

## Other live packages

[`comb-interpolation/comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/)
is the canonical union of the additive-dyadic and geometric-comb manuscripts.
It preserves the distinct modal, Mellin, regular-variation, spline,
reciprocal-product, Euler--Maclaurin, Ruffa, Thue--Morse, and interpolation
results while stating their common Gaussian--Pascal and Jackson--Newton spine
once. Its 180-row source disposition and 151-row historical-ledger audit pass;
its 232-row theorem concordance records 7 Lean-proved, 159 human-proved
frontier, 20 conjecture, 30 open-problem, and 16 non-applicable rows. It maps
canonical label
`gq:thm:richardson-generating` exactly to
`Fabius.geometricLagrangeRichardson_generating` in the new three-definition,
seven-theorem `FabiusFunction.GeometricRichardsonGenerating` module. The module
also exposes `Fabius.hasSum_geometricLagrangeRichardson_mul_pow` as the analytic
companion under its explicit convergence hypotheses. The one-definition,
fourteen-theorem `FabiusFunction.RvachevAppellHasse` leaf additionally makes
`gq:prop:q-Appell-falling` and `gq:thm:gaussian-Appell-decoder` exact by
combining their explicit q-falling and geometric decoder formulas with the
existing finite synthesis theorems. The retained 158-page PDF predates the
notation normalization and all of these chapter-01 crosswalks, so it remains a
historical checkpoint; no PDF was generated for the source-only updates.

[`fabius_information_frontier/`](fabius_information_frontier/) remains an
archival information-geometry intake. Its arrival and operational ledgers
distinguish the submitted PDF from later source changes; manuscript theorem
labels do not by themselves establish current Lean verification.

## Formalization notes

The latest effective-inverse layer gives nine inverse-computability rows exact
compiled counterparts: the main computability theorem, the three tolerant
difference branch certificates, tolerant bisection, restricted and totalized
sequential inversion, computable clamping, and abstract inversion from
computable positive rational gaps.  The principal new declaration is
`Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap`; its clamped
wrapper yields a total computable real function.  The newer
`RvachevSuperconvergentSynthesis.lean` leaf contributes one definition and
eight theorems: it packages the parity-selected phases, the extra-degree
monomial and polynomial rules, generic-mesh physical quadrature, deconvolved
polynomial synthesis, and the Rvachev--Appell specialization. These two latest
row promotions brought the canonical concordance to the historical
51 Lean-proved / 94 human-proved checkpoint. The Laurent promotion then made
that 52 / 93, and the finite-prefix pair gives the current 54 / 91, with 10
conjectures, 15 open problems, and 24 nonassertoric environments. The
zero-definition/one-theorem `FabiusFunction.HalfQBinomialRootSimplicity` leaf
also completes the separate q-frontier label `cor:halfbase-root-locus` over
the canonical rational polynomial: its simple-root theorem composes with the
existing rational zero classifier and Gaussian/half-q coefficient identity.
Injective scalar extension preserves the multiplicities, but this does not
classify every root over every extension field.  The later exhaustive
one-definition/four-theorem `FabiusFunction.GeometricUniformMomentRatFunc`
leaf packages one rational moment coefficient, proves its global
q-factorial clearing identity, identifies its safe inner and exterior
specializations, and handles the removable `q = 1` value.  It makes the
q-monograph label `thm:qF-moment-polynomial` Exact without assigning analytic
values at genuine unit-root poles.  That RatFunc tranche produced the
historical 924-module/11,615-declaration checkpoint.  The subsequent
`ProbabilityLaplaceMoments` theorems
`weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`
make q-frontier labels `prop:up-tail` and `cor:up-moments` Exact, including
the closed-tail convention and every positive natural moment order.  The
unrelated one-definition/one-theorem
`FabiusFunction.RvachevLegendreBiorthogonality` leaf then gives the historical
925-module/11,619-declaration checkpoint.  Its exact finite Legendre pairing
does not change this inverse-package ledger.  The later
one-definition/five-theorem
`FabiusFunction.GeometricUniformMomentReciprocity` leaf defines the combined
inner/exterior germ, identifies both strict branches, proves analyticity at
zero off the unit circle, and proves for `q != 0`, `‖q‖ != 1` the local
`EventuallyEq` `M_q(z) * M_(q⁻¹)(-z) = 1` and its exact all-order binomial
derivative convolution.  It makes q-monograph label `thm:qF-reciprocity`
Exact; no global pointwise identity through genuine inner-product zeros is
claimed.  Subsequent source-only tranches, including that reciprocity leaf,
give the historical reciprocity checkpoint 931/11,685.  The subsequently
merged upstream `DyadicBoundaryIdentity.lean` and
`FinitePrefixThueMorseCollapse.lean` modules add two modules and ten public
declarations, making the live census 933/11,695.  The q forward ledger is now
182 Exact / 78 Partial / 14 None / 8 interface rows, its relevant Dyadic
Gaussian--Thue--Morse chapter is 13/43/0/0, and its source concordance is 95
Lean-proved / 383 human-proved frontier / 60 non-applicable / 9 conjectures.
The preceding finite-prefix checkpoint was 923/11,610.  The retired source layouts remain immutable
provenance only; the source is newer than the retained historical PDF.

`QuarterCatalanGerm.lean` proves that the distinguished rational quarter germ
becomes the Catalan inverse of `X + 4 X^2` under the exact `9/4` parameter
rescaling, together with the reverse rescaling and every positive coefficient.
`FabiusInverseQuarterJet.lean` connects that quadratic inverse to the actual
smooth inverse: its full centered jet at `5/72 = F(1/4)` is the
factorial-scaled Catalan sequence. In ordinary mathematical notation, if
`G = F^{-1}` and `C_m` is the `m`-th Catalan number, the proved identity is

\[
G^{(m+1)}(5/72)=(m+1)!\,(-4)^m C_m \qquad (m\ge 0).
\]

This is equality of the full smooth jet, not local analytic equality. A named
nonzero flat-remainder decomposition remains open, as do the general-dyadic
analytic/algebraic shadow, convergence and identification of the inverse
Taylor series, and the corresponding all-orders Bell--Lagrange coefficient
formula.

`FabiusFunction.LagrangeRvachevSynthesis` supplies two definitions and seven
theorems closing the generic finite-node decoder, cardinal biorthogonality,
and exact interpolation loop. It does not by itself prove the geometric-node
Gaussian closed forms, but the downstream `FabiusFunction.RvachevAppellHasse`
leaf now proves their q-Pochhammer prefactor and elementary-symmetric formula.
The Matrix leaf supplies the typed right inverse; no module proves an
optimal/minimum-variation decoder theorem. The exhaustive public inventory is
in the root [`Analysis/FabiusFunction/README.md`](../../../../README.md).

The subgroup [`dyadic-up-extraction/`](dyadic-up-extraction/) holds one
document, the canonical volume
[*Exact Dyadic Extraction of Rvachev's Up-Function from Finite Sinc-Product
Splines*](dyadic-up-extraction/Dyadic_Up_Extraction/Dyadic_Up_Extraction.tex)
(77 A4 pages), consolidated on 2026-09-03 from six reports received on
2026-09-02.  It proves that at a dyadic point of depth `s` the finite
sinc-product spline equals the up-function value plus exactly `⌊s/2⌋`
geometric modes of ratio `1/4, 1/16, …` for every level `n ≥ s`, with no
remainder, and derives the quarter-base Gaussian-binomial row that recovers
the exact value from `⌊s/2⌋ + 1` consecutive rational samples; it ships one
exact-arithmetic verifier.  The six absorbed reports are listed in the
volume's provenance appendix and in the manifest; git history is the archive.
See [`../MANIFEST.md`](../MANIFEST.md) for titles, scope, and historical paths.
