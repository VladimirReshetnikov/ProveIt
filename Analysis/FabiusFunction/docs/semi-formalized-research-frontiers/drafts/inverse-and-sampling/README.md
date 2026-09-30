# Inverse and sampling

This theme has twelve live navigation targets:

- [`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/)
  — the canonical inverse-Fabius synthesis;
- [`comb-interpolation/comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/)
  — the canonical additive and geometric comb synthesis;
- [`fabius_information_frontier/`](fabius_information_frontier/)
  — a separate information-geometry intake with a synchronized canonical
  source/PDF pair; claim-level acceptance remains explicitly qualified;
- [`Geometric_Uniform_Entropic_Edgeworth/`](Geometric_Uniform_Entropic_Edgeworth/)
  — an archival arrival of 2026-09-28 that claims a proof of the
  information frontier's `conj:entropic-edgeworth`; unreviewed.
- [`Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/`](Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/)
  — an archival arrival of 2026-09-29 on the information frontier's
  Bayesian prefix operator, prefix Rényi information and
  corrected-prefix rate-distortion questions; unreviewed.
- [`Recovering_Uniform_Factors_Fabius_Rvachev/`](Recovering_Uniform_Factors_Fabius_Rvachev/)
  — an archival arrival of 2026-09-28 on the stability of recovering the
  uniform-factor spectrum from the law; unreviewed.
- [`Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/`](Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/)
  — an archival arrival of 2026-09-29 on optimal Hölder exponents for
  recovering finitely many uniform factors; unreviewed.
- [`Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/`](Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/)
  — an archival arrival of 2026-09-29 on minimax rates for recovering
  uniform factors under Gaussian smoothing; unreviewed.
- [`Flat_Boundaries_Sharp_Recovery_Uniform_Factors/`](Flat_Boundaries_Sharp_Recovery_Uniform_Factors/)
  — an archival arrival of 2026-09-29 on sharp minimax rates for
  recovering uniform factors without Gaussian smoothing; unreviewed.
- [`Local_Minimax_Geometry_Uniform_Factors/`](Local_Minimax_Geometry_Uniform_Factors/)
  — an archival arrival of 2026-09-29 on local minimax rates at mixed
  collision strata under Gaussian smoothing; unreviewed.
- [`Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/`](Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/)
  — an archival arrival of 2026-09-29 on the infinite-factor model:
  Gaussian-variance non-estimability and Christoffel recovery;
  unreviewed.
- [`Anchored_Dyadic_Recovery_Uniform_Spectrum/`](Anchored_Dyadic_Recovery_Uniform_Spectrum/)
  — an archival arrival of 2026-09-29 on recovering the whole
  uniform-factor spectrum, or a fixed prefix of it, at the dyadic
  reference law; unreviewed.

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
fully dispositions all 194 immutable source-result rows: 57 are Lean-proved,
88 are human-proved frontier results, 10 are conjectures, 15 are open
problems, and 24 are non-applicable source environments.
[`LEAN_CROSSWALK.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/LEAN_CROSSWALK.md)
records exact module/declaration matches and separately classifies five
post-snapshot additions without changing those source totals.
[`ASSET_DISPOSITION.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/ASSET_DISPOSITION.csv)
accounts for all 88 source-subgroup files, and the asset inventory covers 55
retained files. Eight checksum-ledger rows from the former 63-payload checkpoint
are retired.

The thirteen newest exact source-row matches are abstract effective inversion,
centered Appell deconvolution, positive-degree Appell mean-zero,
arbitrary-phase polynomial deconvolution,
`is:p3:cor:forced-superconvergence`, and
`is:p3:thm:Appell-lattice-reproduction`, together with the exact-dyadic
repository modulus, `is:p2:thm:Laurent-leading`,
`is:p2:thm:finite-prefix-expansion`, `is:p2:thm:exact-recovery`,
`is:p2:thm:TM-uncentered`, `is:p2:cor:Prouhet-canonical`, and
`is:p2:thm:TM-centered`.
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
analytic-MGF realization is claimed. These two promotions gave the historical
inverse concordance checkpoint of 54 Lean-proved and 91 human-proved frontier
rows.

The zero-definition/eight-theorem
`FabiusFunction.FinitePrefixThueMorseCollapse` module now makes the two
finite-prefix collapses and the intervening Prouhet corollary exact.  Its
uncentered block has sign `(-1)^N`, scale `(1/2)^choose(N+1,2)`, and residual
`n.descFactorial N * x^(n-N)`; its centered block is sign-free with scale
`(1/2)^choose(N,2)`.  The successor-indexed centered theorem is on the
manuscript's literal grid, while the common-denominator form strengthens the
statement to `N = 0`.  The cancellation and first-response companions cover
every clause of the Prouhet row.  These are rational coefficient-model
identities, not a new random-variable, `HasLaw`, analytic-MGF, or
Barnes-identification result.  The current concordance is therefore 57
Lean-proved / 88 human-proved frontier / 10 conjecture / 15 open-problem / 24
nonassertoric rows.

The canonical inverse package preserves its 134-page and two 137-page
historical checkpoints in
[`VALIDATION.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/VALIDATION.md).
The incoming `b899` tuple used a 293-line / 11,514-byte driver, a 17-file /
10,682-line / 431,748-byte closure with digest
`6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e`,
and a 137-page / 2,045,486-byte PDF with SHA-256
`cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995`.
The local first-merge tuple and older purpose-specific closure digests remain
history. The accepted current inverse source/PDF receipt is in the
[authoritative receipt
register](../MANIFEST.md#current-post-merge-publication-receipts); the
purpose-specific 23-input closure is regenerated independently and has no
PDF-parity role.

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
existing finite synthesis theorems. The retained 158-page and both later
160-page comb PDFs are historical checkpoints. The local nine-file
aggregate/PDF tuple is
`cef466ee56f6bb864faaac2244bccf1dbc2fd4032a717b6c81604551c0427309` /
`bb714c8be4b82de2a888e0302da3aaf957b9e885f2c5f59466b3ea5d659e3f71`;
the incoming `b899` 15-file closure/PDF tuple is
`9e22455b3f65eb48306ad21c57445b6052a56498cb363666ffb9b160f5cc8090` /
`ad8587049580e6fde371f534b6f8b4e56fa4c929173f87d3021ed369e5225d4c`.
Merged TeX inputs are newer, so a synchronized comb rerender is pending.

[`fabius_information_frontier/`](fabius_information_frontier/) remains an
archival information-geometry intake. Its retired arrival and operational
ledger checkpoints remain recoverable from Git and distinguish the submitted
PDF from the current incoming publication checkpoint. Its 2026-09-04 source
was 2,138 lines and 78,310 bytes, and passes 28/29/29 produced a final
29-page, 790,802-byte PDF; the SHA-256 values once recorded here described
that build, and the repository no longer keeps checksum receipts.
Its recorded publication gates passed and no checksum ledger is a live gate.
On 2026-09-29 an editorial note after `prob:Bayesian-spectrum` marked the
report's expected `q^{mn}` Appell diagonal of `C_m` incorrect (the diagonal
is identically 1; see the report README's erratum and
`Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/`); the source is now
2,156 lines/79,504 bytes and the rebuilt PDF 30 pages/888,775 bytes.
Manuscript theorem
labels do not by themselves establish current Lean verification.

[`Geometric_Uniform_Entropic_Edgeworth/`](Geometric_Uniform_Entropic_Edgeworth/)
holds *Entropic Edgeworth Expansions for Geometric Uniform Laws*, filed on
2026-09-28 by a quick archival intake (20-page A4 PDF, 1,399-line source,
exact-coefficient and diagnostic programs).  It claims a conventional proof
of `conj:entropic-edgeworth` in `fabius_information_frontier/`, the
all-orders expansion of the entropy deficit of the geometric uniform law as
`q ↑ 1`, with the new quartic coefficient `427297/4410000`, and Rényi and
finite-prefix extensions.  It does not address `conj:deficit-monotone`.
The claim has not been reviewed, the information frontier still states the
conjecture as open, and no Lean statement exists.

[`Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/`](Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/)
holds *Beyond Polynomial Diagonals: Nuclear Bayesian Operators, Exact
Null Modes, and a Rényi Phase Transition for Fabius–Rvachev Laws*,
filed on 2026-09-29 by a quick archival intake (21-page A4 PDF,
912-line source, an exact SymPy check program with high-precision
eigenvalue diagnostics).  It studies the conditional expectation `C_m`
of the information frontier above: `C_m` is in every Schatten class
with an infinite-dimensional kernel of explicit null modes, its
polynomial restrictions are unipotent (so the expected `q^{mn}` Appell
diagonal is in fact 1, as the editorial note recorded above states) but
badly conditioned, every finite-order Rényi information of the prefix
channel is finite with an exact critical order 2 in the large-depth
excess, and at the prefix's own distortion no postprocessing of the
prefix is rate-distortion optimal.  A closed-form spectrum and the
rate-distortion expansion remain open.  Unreviewed; its numerics are
diagnostics; no Lean statement.

[`Recovering_Uniform_Factors_Fabius_Rvachev/`](Recovering_Uniform_Factors_Fabius_Rvachev/)
holds *Recovering Uniform Factors: Exact Moment Fibres and Logarithmic
Instability Near the Fabius–Rvachev Law*, filed on 2026-09-28 by a quick
archival intake (20-page A4 PDF, 1,438-line source, an exact SymPy check
program with 90-digit diagnostics).  It asks how reliably the half-lengths
`a_j` of `Σ_j a_j U_j` can be recovered from the law near the dyadic
spectrum: finitely many moments never suffice (an analytic isomoment curve
through the dyadic spectrum), and explicit Chebyshev pairs with
polynomially separated spectra but exponentially close laws rule out any
Hölder inverse and give a `(log 1/ε)^{−2}` modulus and a `(log N)^{−2}`
minimax lower bound.  Full-law identifiability is credited to
Billey–Swanson.  The exact dyadic-scale identifiability of
`GeneralizedRvachevIdentifiability.lean` and the factor classification of
`../spectra-and-arithmetic/Arithmetic_Convolution_Factors_Fabius_Type_Laws/`
are related and not cited.  Unreviewed; no Lean statement.

[`Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/`](Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/)
holds *Sharp Stability Strata for Finite Fabius–Rvachev Deconvolution*,
filed on 2026-09-29 by a quick archival intake (22-page A4 PDF, 1,502-line
source, an exact SymPy check program with 100-digit Fourier diagnostics).
It is the finite-capacity counterpart of the uniform-factor article above:
with a known smooth background (for example the up law) and at most `r`
unknown uniform factors, the optimal local Hölder exponent for recovering
the factors in total variation is `1/M`, where `M` is the largest
positive-scale multiplicity or twice the number of vanishing factors; it
is 1 or `1/2` when one of the two configurations is the fixed base point.
Sharpness again comes from Chebyshev constructions.  It was written before
the uniform-factor article was filed and does not cite it.  Unreviewed; no
Lean statement.

[`Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/`](Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/)
holds *Gaussian Confounding and Sharp Recovery of Uniform Convolution
Factors*, filed on 2026-09-29 by a quick archival intake (19-page A4 PDF,
1,319-line source, an exact SymPy check program with 80-digit Fourier
diagnostics).  It changes the experiment of the finite-factor article above
by adding a Gaussian convolution: with a known bounded background (for
example the up law), at most `m` uniform factors and Gaussian variance `v`,
the optimal global rate for recovering the half-lengths from `n` samples is
`n^{−1/(4m)}` when `v` is known and `n^{−1/(4m+4)}` when it is unknown, and
detecting any factor has critical scale `n^{−1/4}` or `n^{−1/8}`
independently of `m`.  The key tool is a sharp inverse inequality for
consecutive shifted power sums.  The unsmoothed up-law experiment, and so
the finite-factor article's own statistical question, remains open.
Unreviewed; no Lean statement.

[`Flat_Boundaries_Sharp_Recovery_Uniform_Factors/`](Flat_Boundaries_Sharp_Recovery_Uniform_Factors/)
holds *Flat Boundaries Preserve Information*, filed on 2026-09-29 by a
quick archival intake (21-page A4 PDF, 1,554-line source, an exact SymPy
check program with mpmath Hellinger diagnostics).  It removes the Gaussian
smoothing of the Gaussian-confounding article above: over a known
background that is an infinite sum of uniforms (for example the up law), it
proves an all-order Hellinger expansion in which the flat support
boundary costs no information, and from it the same global minimax rates
as in the smoothed model, now with the Gaussian variance allowed to be zero:
`n^{−1/(4m)}` for the half-lengths with known variance, `n^{−1/(4m+4)}` with
unknown variance, `n^{−1/(2m+2)}` for the variance.  This settles the
Gaussian-confounding article's first open problem for global rates; the
finite-factor article's local rate at each collision pattern remains open
without Gaussian smoothing; with smoothing it is settled by
`Local_Minimax_Geometry_Uniform_Factors/` below.
Unreviewed; no Lean statement.

[`Local_Minimax_Geometry_Uniform_Factors/`](Local_Minimax_Geometry_Uniform_Factors/)
holds *Local Minimax Geometry of Uniform Convolution Factors*, filed on
2026-09-29 by a quick archival intake (21-page A4 PDF, 1,411-line
source, an exact SymPy check program with mpmath likelihood
diagnostics).  It localizes the Gaussian-confounding article above:
near a configuration with `r` vanishing half-lengths and positive
clusters of multiplicities `m_j`, each cluster is recovered at rate
`n^{−1/(2m_j)}` and the zero block at `n^{−1/(4r)}` (known variance) or
`n^{−1/(4r+4)}` (unknown), and the variance at `n^{−1/(2r+2)}`, so it is
root-`n` estimable when no factor vanishes.  This is the
Gaussian-confounding article's conjectured classification of local
strata, and, with Gaussian smoothing, the finite-factor article's local
rate at each collision pattern; without smoothing both stay open.
Unreviewed; no Lean statement.

[`Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/`](Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/)
holds *Gaussian Dust and Christoffel Recovery in Infinite Uniform
Convolutions*, filed on 2026-09-29 by a quick archival intake (23-page US Letter PDF, 1,522-line source, an exact SymPy check program).  It
drops the capacity bound: with infinitely many uniform factors of
bounded total variance `V`, the Gaussian variance is identifiable but
its exact minimax risk is `V/2` at every sample size, because many
small uniform factors ("Gaussian dust") imitate a Gaussian; uniform
consistency returns exactly on classes with uniformly vanishing tails.
A Christoffel hierarchy on a variance-weighted spectral measure gives
explicit bias bounds, exact for geometric spectra such as the up
law's.  Unreviewed; its numerics are diagnostics; no Lean statement.

[`Anchored_Dyadic_Recovery_Uniform_Spectrum/`](Anchored_Dyadic_Recovery_Uniform_Spectrum/)
holds *Anchored Recovery of the Dyadic Uniform Spectrum*, filed on
2026-09-29 by a quick archival intake (22-page A4 PDF, 1,622-line
source, an exact check program with mpmath diagnostics).  It takes up
the pointwise questions the uniform-factor recovery article above
leaves open: comparing a law directly with the Rvachev law, the
spectrum is recovered to within `exp[−Θ(√log(1/ε))]` from
total-variation or Kolmogorov error `ε` — no Hölder exponent, even for
smooth, fixed-variance, geometrically separated spectra, but far better
than the pairwise `(log 1/ε)^{−2}` — while every fixed number of
leading factors is recovered at Lipschitz rate with an arbitrary
summable tail.  Testing the dyadic law against `δ`-separated
alternatives needs `exp[Θ(log²(1/δ))]` samples.  The pairwise modulus
remains open.  Unreviewed; no Lean statement.

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
that 52 / 93, the finite-prefix pair gave 54 / 91, and the finite-prefix
Thue--Morse tranche gives the current 57 / 88, with 10 conjectures, 15 open
problems, and 24 nonassertoric environments. The
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
`FabiusFunction.RvachevLegendreBiorthogonality` leaf then gave the historical
925-module/11,619-declaration checkpoint.  Its exact finite Legendre pairing
and the other intervening declarations do not change this inverse-package
ledger; the finite-prefix Thue--Morse module changes only the three rows
identified above.  The later
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
declarations, making the historical 933/11,695 census.  The incoming union
adds one module and fourteen public declarations: the new zero-definition/
six-theorem `ProuhetBaseTwoBridge.lean` module, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`.  This makes 934/11,709 a historical
checkpoint. Later post-baseline additions contribute another 23 modules and
211 public declarations, giving 957/11,920; retaining the unconditional public
`Fabius.complexQPochhammerInf_eq_qPochhammerInfIn` compatibility theorem gives
the historical merge-union checkpoint 957/11,921. The residual-existence
certificate `Fabius.exists_eq_in_residual_interval` is included in the current
semantic union computed by `scripts/doc_audit.py` and pinned in
`docs/doc_audit_baseline.json`. The exhaustive lexical audit has no missing
module header or public-declaration doc comment.

The q forward ledger's semantic union is 181 Exact / 79 Partial / 14 None / 8
interface rows; the local q-Lucas correction is retained rather than reverting
that row to Exact. Its source concordance is 103 Lean-proved / 375 human-proved
frontier / 60 non-applicable / 9 conjectures. The preceding finite-prefix
checkpoint was 923/11,610. The retired source layouts remain immutable
provenance only. The canonical inverse-synthesis source now includes later
chapter edits and is newer than the retained historical 137-page `b899` PDF;
the separate information-frontier source and PDF remain synchronized under
their own receipt. The q-Lucas manuscript row remains Partial because Lean
proves only the primitive-root evaluation, not the polynomial congruence
modulo the cyclotomic polynomial.

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
