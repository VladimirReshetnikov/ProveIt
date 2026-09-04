# Canonical theorem provenance crosswalk

This is the assertion-level provenance ledger for the canonical volume
`Up_Polynomial_Synthesis`. It covers exactly the environments named
`theorem`, `lemma`, `proposition`, or `corollary` in the parent source and its
three canonical chapter files. Definitions, algorithms, conjectures,
questions, problems, remarks, warnings, and unlabeled displayed equations are
outside this count.

The ledger distinguishes mathematical provenance from formal verification.
A Lean entry below means only the scope stated in that cell. In particular, a
formalized input, dual quadrature identity, convergence theorem, or mesh
threshold is not silently promoted to a formalization of the entire canonical
assertion.

## Disposition vocabulary

- **Direct**: the canonical assertion is the legacy result with notation,
  normalization, domain, or exposition cleaned up.
- **Consolidated**: the canonical environment combines equivalent or adjacent
  legacy results; the cited source labels identify the components.
- **Strengthened**: the canonical statement adds a genuine conclusion,
  quantifier, common hypothesis, correction, or cross-identification.
- **Synthesized**: the canonical assertion is a new deduction of the
  consolidation and does not occur as one standalone legacy theorem.
- **Theoremized**: the mathematical content existed in legacy prose or a
  displayed equation but was promoted to a theorem-like environment here.

## Source keys

Let `REP` denote
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/`.
The L1--G4 paths in the key table are relative to `REP` at immutable
pre-retirement commit `443793e846934e7363e314ea01129b9f50197a58`; they are
historical source identities, not live navigation. Every other displayed path
is repository-relative in the current tree. The ten later reports are
immutable legacy sources for this audit; their full baseline hashes are recorded in
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/assets/provenance/SOURCE_SNAPSHOTS.md`.
The three earlier polynomial packages were absorbed before the later-report
consolidation; their retained payloads and historical hashes are under the
canonical package's `assets/` directory. The disposition table covers 113 rows:
106 retained payloads from L1--G4 have canonical destinations, while seven
checksum-ledger rows are explicitly retired in
`assets/provenance/COMPANION_PAYLOADS.csv`.

| Key | Historical package or live evidence source |
|---|---|
| P1 | `Rvachev_Up_Polynomial_Representation_Package` (retained payload: `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/assets/Rvachev_Up_Polynomial_Representation_Package/`) |
| P2 | `rvachev_up_polynomial_representation` (retained payload: `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/assets/rvachev_up_polynomial_representation/`) |
| P3 | `Rvachev_Up_Exact_Polynomial_Representation_Report` (retained payload: `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/assets/Rvachev_Up_Exact_Polynomial_Representation_Report/`) |
| L1 | `rvachev_lagrange_loop_report/rvachev_lagrange_loop_report.tex` |
| L2 | `Lagrange_Rvachev_Loop_Package/Lagrange_Rvachev_Loop.tex` |
| L3 | `lagrange_rvachev_loop_report_v3/lagrange_rvachev_loop.tex` |
| L4 | `Lagrange_Rvachev_Closed_Loop_Report/lagrange_up_loop.tex` |
| L5 | `Rvachev_Lagrange_Loop_Report_v5/Rvachev_Lagrange_Loop_Report.tex` |
| L6 | `Rvachev_Lagrange_Loop_Report_v6/Rvachev_Lagrange_Loop_Report_v6.tex` |
| G1 | `legendre_rvachev_closed_loop/legendre_rvachev_closed_loop.tex` |
| G2 | `Legendre_Rvachev_Closed_Loop_Report_v3/legendre_rvachev_closed_loop.tex` |
| G3 | `Legendre_Rvachev_Closed_Loop_Report_v4/legendre_rvachev_closed_loop.tex` |
| G4 | `Legendre_Rvachev_Self_Reconstruction/legendre_rvachev_self_reconstruction.tex` |
| X1 | `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/comb-interpolation/Dyadic_Comb_Frontiers/Dyadic_Comb_Frontiers.tex` |
| X2 | At pre-retirement revision `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`: `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/Inverse_and_Sampling_Frontiers.tex` |

Legacy theorem labels in the tables are exact labels from those source files.
For P1--P3, whose original report TeX is no longer duplicated beside the
canonical source, the package-level contribution map in the canonical
provenance appendix is the authority; no source theorem label is invented.
Any label written after P1--P3 (for example in a row that explains how two
already-canonical components imply a synthesized result) is explicitly a
canonical component label, not a purported label from the absorbed source.

The Lean path prefix used below is
`Analysis/FabiusFunction/Lean/FabiusFunction/`.

## `Up_Polynomial_Synthesis.tex` — 25 assertions

| Canonical environment, label, and title | Best legacy provenance | Disposition and assertion-level note | Explicit formal or evidence anchor |
|---|---|---|---|
| proposition `prop:tm-green` — Green pair and quasipolynomial structure | P2 | Direct normalization of the restricted-binary-partition Green sequence, its Thue--Morse convolution inverse, and quasipolynomial asymptotic. | None cited. |
| theorem `thm:A-factor` — `$q$-integer and cyclotomic factorization` | P1 | Direct consolidation of the alias annihilator factorization, coefficient law, degree, mass, and probabilistic interpretation. | None cited. |
| theorem `thm:scale-classification` — Scale classification | P1 (minimal dyadic ratio and odd overscaling); P3 (general integer-ratio sharp order) | Consolidated and strengthened into one iff/order/minimality statement. | Partial but exact natural-mesh universal slice: `rvachevCombExactThrough`, `exists_shift_tsum_shifted_monomial_ne_integral_nat_real`, `rvachevCombExactThrough_iff_padicValNat`, `rvachevCombExactThrough_iff_pow_two_dvd`, `rvachevCombExactThrough_two_pow`, `two_pow_le_of_rvachevCombExactThrough`, `isLeast_rvachevCombExactThrough`, and `isLeast_rvachevCombExactThrough_even` in `CompositeMeshSharpness.lean`. The canonical text explicitly excludes arbitrary real radii, target-specific claims, local dimensions, and atom minimality from that Lean scope. |
| lemma `lem:poisson-collapse` — Polynomial-coefficient Poisson collapse | P1 | Direct analytic engine for the common-scale dictionary. | Supporting dual quadrature face only: `Fabius.tsum_shifted_monomial_eq_integral_real` in `MonomialCombExactness.lean`; the canonical roadmap explicitly says the Appell-weighted synthesis direction remains outside that result. |
| theorem `thm:global-synthesis` — Global exact up-atom synthesis | P1; equivalent general-ratio monomial specialization in P3 | Consolidated normalization of moment deconvolution followed by Poisson collapse. | Same partial support as `lem:poisson-collapse`: `Fabius.tsum_shifted_monomial_eq_integral_real` in `MonomialCombExactness.lean`; not an exact Lean counterpart of the displayed Appell-weighted synthesis theorem. |
| theorem `thm:alias-family` — Complete dyadic alias family | P1 | Direct consolidation of the twisted root-of-unity relations, confluent independence, and recurrence-space completeness. | Supporting alias machinery is explicitly cited as `MonomialCombAlias.lean`; its relevant declarations are `iteratedDeriv_rvachevFourier_two_pow_int_eq_zero` and `fourier_monomialRvachevSchwartz_int_eq_zero`. No exact Lean counterpart of the complete finite null-family classification is claimed. |
| theorem `thm:local-dim` — Exact local dimension | P1 | Direct dimension/intersection/kernel theorem. | None cited. |
| proposition `prop:fixed-lower` — Universal fixed-dictionary lower bound | P1 | Direct fixed-dictionary dimension obstruction; the adaptive statement is deliberately not asserted. | None cited. |
| theorem `thm:endpoint-basis` — Unique `$(d+2)$-atom endpoint synthesis` | P1 | Direct endpoint reduction and uniqueness theorem, including rationality and fixed-dictionary optimality. | None cited. |
| theorem `thm:H-identity` — Compressed residual identity | P1 | Direct output-sensitive Bernoulli-symbol identity. | None cited. |
| theorem `thm:multicell` — Multi-cell dimension and basis | P1 | Direct multi-cell extension, physical rescaling, basis, and footprint theorem. | None cited. |
| theorem `thm:certificate` — Exact certificate, Thue--Morse form | P1 | Direct codimension-one polynomiality certificate. | None cited. |
| theorem `thm:defect-Fourier` — Explicit periodic residue | P1 | Direct canonical-defect Fourier theorem and quotient-coordinate decomposition. | None cited. |
| theorem `thm:defect-duality` — Defect--quadrature duality | P1 (defect series) plus X1 `thm:first-failure` (comb first-failure series) | **Synthesized** cross-volume identification with an explicit normalization constant; the source packages did not contain this standalone duality theorem. | Exact comparison source: X1 `thm:first-failure` / `eq:first-failure`; the rational special-value input is X1 `thm:D-rational`. |
| proposition `prop:one-step` — One-step identity | P2 | Direct causal antiderivative/refinement telescoping identity. | None cited. |
| theorem `thm:iterated-J` — Iterated train | P2 | Direct repeated-integration train with restricted binary-partition weights and support-edge invariance. | None cited. |
| lemma `lem:tail` — Tail polynomial | P2 | Direct moment-Appell tail evaluation. | None cited. |
| theorem `thm:finite-window` — Exact finite polynomial window | P2 | Direct finite truncation theorem and triangular polynomial basis. | None cited. |
| corollary `cor:two-atom` — Two atoms per degree | P2 | Direct canonical sparse-scale specialization of the finite window. | None cited. |
| theorem `thm:coefficient-transform` — Coefficient transform | P2 | Direct Appell-coordinate, derivative, recurrence, monomial, rationality, and complexity formulas. | None cited. |
| proposition `prop:ladder-structure` — Derivative ladder, Wronskian, interpolation | P2 | Direct Chebyshev-system and Vandermonde determinant package. | None cited. |
| proposition `prop:extension` — Extension operator and support | P2 | Direct compactly supported smooth extension operator and exact support bound. | None cited. |
| theorem `thm:collar` — Collar--atom tradeoff | P2 | Direct collar choice, atom bound, reflected train, and mixed-orientation consequence. | None cited. |
| lemma `lem:twisted-poisson` — Twisted Poisson identity | P3 | Direct normalized form of the report's entire generating identity. | Supporting monomial-comb Poisson machinery: `Fabius.tsum_shifted_monomial_eq_integral_real` in `MonomialCombExactness.lean`; the canonical text does not claim that this Lean theorem formalizes the complex entire identity. |
| theorem `thm:minimal-atoms` — Minimal atom counts | P1 (`prop:fixed-lower`, `thm:endpoint-basis`) plus P2 (`cor:two-atom` and the partition pair) | **Synthesized and strengthened** consolidation result: P1 supplies the new `d+2` universal upper bound and the fixed-dictionary lower bound; P2 supplies the independent two-atom constant construction. The adaptive equality remains conjectural. | None cited; `CompositeMeshSharpness.lean` is explicitly out of scope for atom-count minimality. |

## `chapters/Lagrange_Cardinal_Loops.tex` — 16 assertions

| Canonical environment, label, and title | Best legacy provenance | Disposition and assertion-level note | Explicit formal or evidence anchor |
|---|---|---|---|
| theorem `thm:lag-cardinal` — Universal Lagrange--Rvachev cardinal formula | L6 `thm:lagrange-synthesis` (strongest admissible-mesh form); equivalent forms in L1 `thm:pure-shift`, L2 `thm:cardinal-synth`, L3 `thm:literal-lagrange`, L4 `thm:lagrange-up`, and L5 `thm:lagrange-up` | **Exact/Complete Lean counterpart by assembly.** Consolidated equivalent cardinal and arbitrary-data identities; the canonical statement uses the parent physical-scale theorem to normalize all six versions to literal unit-radius translates. In Lean, `M ≠ 0` is the positive-mesh condition, `s.card - 1 ≤ padicValNat 2 M` is admissibility through degree `d = |s|-1`, `x ∈ [-1,1]` is unchanged, `Finset.Ioo (-(2M)) (2M)` is exactly `|k| < 2M`, and the factor `(M : ℝ)⁻¹` is `h`. Node injectivity is not needed for the polynomial identities and may be added for their cardinal interpretation. No redundant report-shaped wrapper is claimed. | `FabiusFunction.LagrangeRvachevSynthesis`: `Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp` proves the individual cardinal formula, and `Fabius.sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp` proves the arbitrary-data interpolant formula. The latter's coefficient is the normalized decoder applied to the nodal data, while `Lagrange.interpolate` is the canonical `I_X y`. This promotion does not promote the compound `thm:lag-right-inverse`. |
| corollary `cor:lag-nodes-only` — Nodes-only Bernoulli--Bell amplitudes | L1 `cor:coeff`; L2 `cor:explicit-b`; L3 `prop:appell-cardinal`; L4 `cor:nodes-only`; L5 `prop:symmetric-coeff` | **Exact/Complete Lean counterpart by composition.** Consolidated derivative, raw omitted-node elementary-symmetric/Appell, rational-descent, and Bernoulli--Bell coefficient forms. Rationality means a polynomial over `ℚ` and rational values at rational points (including lattice samples), not rational values at arbitrary irrational points. The Bell identity is formal coefficient algebra, not analytic reciprocal-MGF convergence. | `FabiusFunction.RvachevLagrangeNodesOnly`: the principal clause theorems are `Fabius.eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative`, `Fabius.eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell`, `Fabius.lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell`, `Fabius.map_rvachevDeconvolvedPolynomialRat_lagrangeBasis`, `Fabius.lagrangeRvachevDecoder_eq_ratCast`, `Fabius.rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant`, and `Fabius.momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne`; odd cumulants use the existing `Fabius.centeredRvachevFullCumulant_odd`. No single wrapper theorem is claimed, and this independent promotion does not promote `thm:lag-right-inverse`. |
| theorem `thm:lag-right-inverse` — Nodal closure, basis independence, and determinant identity | L1 `thm:factor` and `cor:perfect`; L3 `thm:UB`, `prop:moment-transmutation`, and `thm:basis-factorization`; L5 `thm:right-inverse`, `thm:coefficient-projector`, `cor:trace-identity`, and `cor:cauchy-binet`; L6 `thm:interpolation-factorization`, `thm:right-inverse`, and `thm:coefficient-projector` | **Consolidated; Partial Lean coverage only.** The boxed finite right-inverse clause `UB = I` is exact. The `BU` projector range/kernel, rank, trace, characteristic polynomial, intertwining, basis-factorization, moment-transmutation, and Cauchy--Binet clauses remain human proofs, so the compound assertion is not promoted wholesale. | In `FabiusFunction.LagrangeRvachevMatrix`, `Fabius.rvachevAtomIndexSet`, `Fabius.RvachevAtomIndex`, `Fabius.lagrangeRvachevEncoderMatrix`, and `Fabius.lagrangeRvachevDecoderMatrix` realize the finite matrices as `A = hU` and `D = h⁻¹B`; `Fabius.lagrangeRvachevEncoderMatrix_mul_decoderMatrix` proves exactly `UB = I`. |
| proposition `prop:lag-markov` — Positive Markov encoder and forced signed decoder | L5 `prop:Markov-pair` and `thm:sign-necessity` | **Exact Lean counterpart.** Consolidated qualitative Markov normalization and the conditional overlap sign obstruction; overlap remains an explicit hypothesis, not an unconditional conclusion. | `FabiusFunction.LagrangeRvachevMatrix`: `Fabius.lagrangeRvachevEncoderMatrix_nonneg`, `Fabius.sum_lagrangeRvachevEncoderMatrix_row_eq_one`, `Fabius.sum_lagrangeRvachevDecoderMatrix_row_eq_one`, and `Fabius.lagrangeRvachevEncoderMatrix_mul_decoderMatrix`; the generic obstruction is `Fabius.exists_neg_entry_of_rightInverse_of_row_overlap`, specialized by `Fabius.exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap`. |
| theorem `thm:lag-variation` — Decoder variation and the Lebesgue barrier | L5 `thm:TV-bound` and `prop:decoder-Lebesgue` | Consolidated quantitative total-variation, negative-mass, and Lebesgue lower bounds. | None cited. |
| theorem `thm:lag-exact-sequence` — Alias/sample exact sequence | L5 `thm:V-direct-sum` and `thm:exact-sequence`; P1 `thm:multicell` and alias dimension supply the normalized interval count | **Consolidated and strengthened**: separates the true synthesis kernel from the nonzero nodal-zero spline sector and records the corrected dimension split in one exact sequence. | None cited. |
| theorem `thm:lag-rank-one` — Rank-one complement and canonical nodal ghost | L2 `thm:ghost` and `cor:rank-one`; L3 `thm:rank-one` and `cor:functional-defect` | Consolidated cofactor normalization, rank-one complementary projector, functional ghost decomposition, and polynomiality test. | None cited. |
| corollary `cor:lag-square-completion` — Defect-completed square inverse | L2 `thm:defect-completed`; P1 `thm:defect-Fourier` supplies the canonical Fourier representative | **Strengthened/synthesized cross-identification**: retains the square inverse and identifies its nodal ghost with the canonical defect modulo interpolation. | None cited. |
| theorem `thm:lag-nested-flag` — Nested projector semilattice and coefficient flag | L1 `thm:nested-semilt` and `cor:details`; L5 `lem:nested-I`, `thm:projector-flag`, and `cor:dyadic-multiplicities` | Consolidated function-space semilattice, terminal coefficient lift, pairwise-annihilating details, and exact ranks. | None cited. |
| corollary `cor:lag-self-series` — Level-grouped self-series and dyadic absolute convergence | L1 `thm:self-mra`; L2 `thm:self-series` and `thm:cheb-loop`; L5 `thm:error-transfer`, `cor:no-truncation-error`, and `cor:Cheb-superalg`; L6 `thm:partial-sums` and `cor:same-error` | **Consolidated and strengthened** into a topology-neutral telescoping statement plus an absolutely and uniformly convergent dyadic Chebyshev--Lobatto specialization. | None cited. |
| proposition `prop:lag-q-lift` — Gaussian-binomial/Appell coefficient matrix | L3 `prop:q-row-lift` | Direct, with the node parameter and synthesis mesh cleanly separated. | None cited. |
| theorem `thm:lag-appell-vandermonde` — Appell--Vandermonde inverse and volume growth | L4 `thm:Appell-Vandermonde`, `cor:detT`, and `thm:node-independent-instability` | Consolidated inversion, exact determinant, raw-amplitude determinant, and node-free spectral-norm lower bound. | None cited. |
| proposition `prop:lag-even-four-atom-ladder` — Parity-adapted four-atom Appell ladder | L4 `prop:even-ladder` | Direct normalization of the causal/anticausal even Appell basis and its application to even Legendre cutoffs. | None cited. |
| theorem `thm:lag-cheb-root-rate` — Exact Chebyshev root-rate obstruction | L2 `cor:root-rate` (supported by `thm:cheb-loop`) | Direct, with the canonical statement making the eventual-uniform-bound and exceptional-subsequence boundary explicit. | None cited. |
| theorem `thm:lag-endpoint-amplitude` — Endpoint amplitude and quadratic-log barriers | L2 `thm:amplitude-barrier` and `cor:quadratic-growth` | Consolidated finite-degree amplitude inequality and asymptotic lower bound, with the constant-extension convention stated in the parent. | Supporting asymptotic input only: label `eq:dyadic-quadratic-law` in `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`; exact Lean limit `fabiusLogProfile_normalized_tendsto` in `FabiusLogSquaredAsymptotic.lean`. |
| theorem `thm:lag-prime-support` — Prime support of rational cardinal amplitudes | L4 `thm:prime-support` | Direct denominator-prime support theorem in canonical mesh notation. | None cited. |

## `chapters/Legendre_Spectral_Closure.tex` — 17 assertions

| Canonical environment, label, and title | Best legacy provenance | Disposition and assertion-level note | Explicit formal or evidence anchor |
|---|---|---|---|
| theorem `thm:leg-mode-synthesis` — Literal Legendre synthesis and Jacobi closed form | G1 `thm:legendre-synthesis` and `thm:Q-jacobi`; equivalent finite synthesis in G2 `thm:literal-legendre`, G3 `thm:legendre-endpoint`, and G4 `thm:Pd-synthesis` | Consolidated finite synthesis, Jacobi expansion, parity, and rationality; notation `Q^-` prevents collision with G3's smoothed family. | None cited for the complete theorem. |
| theorem `thm:leg-reverse-loop` — Reverse local loop and rational spectral closure | G1 `thm:reverse-loop`, `prop:Lambda-connection`, and `thm:rational-spectral-closure` | Consolidated strongest local/reverse closure, translated-kernel expansion, rational spectral identity, and parity vanishing. | Supporting canonical Legendre series only: `summable_abs_rvachevLegendreCoefficient`, `hasSum_rvachevLegendreSeries`, and `hasSum_rvachevLegendreSeries_uniform` in `FabiusLegendreSeries.lean`; no exact Lean counterpart of the reverse closure is asserted. |
| theorem `thm:leg-Gram` — Exact Gram isometry and coefficient projector | G2 `thm:Gram-isometry`, `cor:coef-projector`, and `thm:two-sided-kernel` | Consolidated Gram isometry, Gram-self-adjoint coefficient projector, two-sided atomic Christoffel--Darboux factorization, positivity, and rank. | None cited. |
| theorem `thm:leg-interlevel` — Interlevel null train and refinement cocycle | G4 `thm:interlevel-null` plus its displayed `eq:refinement-cocycle` | **Strengthened/theoremized**: the legacy null-train theorem is retained and its subsequent cocycle equation is promoted into the same theorem. | None cited. |
| corollary `cor:leg-lifting` — Exact quarter-grid Legendre lifting | G4 `thm:lifting` | Direct normalization of the exact null-gauge plus new-mode lifting split. | None cited. |
| theorem `thm:leg-flatness` — Endpoint flatness and finite jet sum rules | G1 `thm:flatness-sum-rules` and `thm:boundary-jets`; equivalent finite-jet strand in G4 `thm:endpoint-jets` | Consolidated infinite coefficient sum rule and finite synthesized-mode boundary jets. | None cited for the combined theorem. |
| corollary `cor:leg-thue-morse-boundary-jets` — Boundary jets as finite Thue--Morse identities | G1 `thm:boundary-jets` plus its prose/equation `eq:derivative-cell-law` | **Synthesized/theoremized**: makes the legacy prose conversion to a finite rational Thue--Morse identity fully quantified and canonical. | Exact cell-law input `iteratedDeriv_rvachev_cell` in `RvachevDerivativeDistribution.lean`; exact dyadic-value input `fabiusDyadic_cast` in `DyadicAnalytic.lean`. These inputs do not by themselves formalize the finite weighted sum. |
| corollary `cor:leg-central-sum` — Central-binomial dyadic cancellation | G4 `thm:center-sum` | **Exact/Complete Lean counterpart.** Direct central evaluation of the finite Legendre synthesis. Lean takes the printed `M = 4^n`, evaluates at zero, truncates the open synthesis block to `-M < k < M` by compact support, pairs nonzero nodes by evenness, clears `M`, and includes `n = 0`. Quantifying over any `BoundedFabius` satisfying `IsFabius` is a harmless strengthening. | `FabiusFunction.RvachevLegendreCentralSum`: `Fabius.eval_legendrePolynomial_even_zero` proves the normalized central value, `Fabius.eval_rvachevLegendreDeconvolutionPolynomial_even` proves the needed even-mode decoder parity, and `Fabius.rvachevLegendreCentralSum` is the displayed conclusion. The 0-definition/3-theorem module uses the existing even-mode synthesis. It does not supply the Jacobi closed form, all-degree parity or rationality of `thm:leg-mode-synthesis`, reverse closure, mesh minimality, or any `thm:lag-right-inverse` clause. |
| theorem `thm:leg-rank-one-details` — Rank-one atomized spectral details | G4 `thm:detail-atomization` | Direct orthogonal rank-one projector calculus and finite atomization. | None cited. |
| theorem `thm:leg-block-loop` — Blockwise self-loop and common-mesh partial sums | G1 `thm:block-loop`, `cor:fixed-scale`, and `thm:compressed-legendre`; equivalent loop forms in G2 `thm:block-loop`, G3 `thm:finite-loop`/`cor:infinite-loop`, and G4 `thm:block-loop` | **Consolidated and strengthened**: states both grouped per-mode reconstruction and a common-mesh cutoff, while explicitly restricting minimality to universal polynomial-space exactness. | Series inputs: `summable_abs_rvachevLegendreCoefficient`, `hasSum_rvachevLegendreSeries`, and `hasSum_rvachevLegendreSeries_uniform` in `FabiusLegendreSeries.lean`. Universal mesh threshold only: `isLeast_rvachevCombExactThrough_even` in `CompositeMeshSharpness.lean`; no target-specific minimality is claimed. |
| theorem `thm:leg-block-orthogonality` — Orthogonal translate blocks and exact tails | G4 `thm:block-orthogonality` and `thm:derivative-energies` | Consolidated block orthogonality, Parseval/tail identities, derivative energy, and spectral Sobolev energy. | The literal expanded atom-Gram cancellation is `sum_rvachevLegendreAtomCoefficient_mul_gram` in `FabiusLegendreTranslateBlocks.lean`; this is support for the atom-level expansion, not every spectral consequence in the canonical theorem. |
| theorem `thm:leg-A2` — Fabius square energy: rational series and sinc integrals | G4 `thm:A2-series` | Direct normalization, **strengthened** with the exact equality criterion for strict growth of partial sums. | Rational series support: `fabiusSquareEnergy_eq_tsum_ratCast` and `monotone_fabiusSquareEnergyPartialSumRat` in `FabiusLegendreRationalEnergy.lean`. Fourier/sinc equalities: `fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier`, `fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq`, and `fabiusSquareEnergy_eq_scaled_integral_Ioi_tprod_sinc_sq` in `FabiusSquareEnergyFourier.lean`. |
| corollary `cor:leg-dyadic-square-energy` — Nested dyadic-Fabius square series | G4 displayed equations `eq:Rn` and `eq:A2-dyadic-square` following `thm:A2-series` | **Theoremized and strengthened**: promotes the legacy nested-value formula to a corollary and records exact rationality of every inner quantity. | Exact coefficient identity `rvachevLegendreCoefficient_eq_fabius_sum` in `FabiusLegendreCoefficients.lean`; exact dyadic values `fabiusDyadic_cast` in `DyadicAnalytic.lean`. The first rational energy cutoffs are in `FabiusLegendreRationalEnergy.lean`. |
| theorem `thm:leg-Lambda` — Analysis kernel and Fourier--Bessel representation | G1 `prop:Lambda-basic` and `thm:Lambda-bessel` | Consolidated support, smoothness, parity, origin values, and Fourier--Bessel transform. | None cited. |
| lemma `lem:leg-dyadic-truncated` — Rational dyadic truncated moments | G1 `prop:Lambda-rational` and its proof's dyadic primitive calculus | **Strengthened**: extracts and proves the more general truncated-moment lemma that the legacy proposition used only to conclude rationality of the translated kernel. | Exact dyadic-value input `fabiusDyadic_cast` in `DyadicAnalytic.lean`; the truncated-moment induction itself is not claimed as a Lean declaration. |
| theorem `thm:leg-biorthogonality` — Legendre--up dyadic biorthogonality | G1 `thm:biorthogonality` | Direct finite analysis/synthesis biorthogonality identity. | None cited. |
| corollary `cor:leg-biorthogonal-matrices` — Finite biorthogonal matrices and projector identities | G1 `cor:spectral-projector` and `cor:trace-cauchy-binet` | **Consolidated and strengthened**: puts the common condition `v2(M) >= d` before all columns, then records the right inverse, projector, trace, and Cauchy--Binet identities under that single valid hypothesis. | None cited. |

## `chapters/Legendre_Transmutation_Arithmetic.tex` — 22 assertions

| Canonical environment, label, and title | Best legacy provenance | Disposition and assertion-level note | Explicit formal or evidence anchor |
|---|---|---|---|
| theorem `thm:leg2-dual-pullback` — Dual pullback Legendre geometries | G2 `thm:pullback-orthogonality` for `Q^-`; G3's moment-smoothed family and conjugation framework for `R` | **Synthesized dual packaging**: the `Q^-` half is direct legacy provenance; the `R` half is the elementary inverse pullback counterpart made explicit by the consolidation. | None cited. |
| proposition `prop:leg2-no-scalar-measure` — No scalar moment measure and the explicit Favard defect | G2 `prop:no-scalar-weight` | Direct scalar-moment obstruction and explicit degree-four Favard defect. | None cited. |
| theorem `thm:leg2-Q-operator-calculus` — Deconvolved Legendre operator calculus | L3 `prop:Q-recurrence`; G2 `thm:nonlocal-SL`, `prop:pullback-kernel`, and `thm:operator-CD` | **Consolidated** recurrence, transmuted Sturm operator, symmetry, reproducing kernel, kernel transmutation, and operator Christoffel--Darboux identity. | None cited. |
| theorem `thm:leg2-weighted-SVD` — Christoffel--Darboux cardinals and weighted SVD transfer | L3 `thm:CD-synthesis` and `thm:weighted-svd` | Consolidated Gauss cardinal kernel, atom coefficients, orthogonal normalization, and exact singular-value transfer. | None cited. |
| theorem `thm:leg2-appell-transforms` — Forward and inverse Legendre--Appell transforms | G3 `thm:C-transform`, `thm:D-transform`, and `thm:C-determinant` | Consolidated both changes of basis, finite inverse matrices, universal determinant, and moment-independence of the diagonal. | None cited. |
| corollary `cor:leg2-R-transmutation` — Smoothed transmutation and its dual geometry | G3 `thm:transmuted`; dual pullback conclusion from canonical `thm:leg2-dual-pullback` | **Strengthened**: retains the smoothed recurrence and differential equation and adds its explicitly normalized dual pullback orthogonality. | None cited. |
| theorem `thm:leg2-augmented-moment` — Legendre--Thue--Morse coordinate completion | G3 `thm:augmented-invertible` | Direct augmented transform, inverse-column identification, and normalized defect column. | None cited. |
| theorem `thm:leg2-compressed-one-scale` — Compressed one-scale Legendre closure | G3 `thm:legendre-endpoint`, `thm:finite-loop`, and `cor:infinite-loop` | Consolidated endpoint coordinates, exact `2N+2`-atom cutoff, finite certificate, and uniform reconstruction; kept distinct from the raw common-mesh train. | None cited. |
| lemma `lem:leg2-defect-parity` — Reflection character of the canonical defect | G2 `lem:defect-parity` | Direct periodic-residue parity and quotient character. | None cited. |
| theorem `thm:leg2-parity-split` — Parity split of the local up-spline space | G2 `thm:parity-split` | Direct even/odd sector equality theorem. | None cited. |
| lemma `lem:leg2-endpoint-tail` — Endpoint-tail generating function | G2 `lem:endpoint-tail` | Direct recurrence-to-endpoint generating function. | None cited. |
| theorem `thm:leg2-central-determinant` — Central `$q$-determinant` | G2 `thm:central-determinant` | Direct exact odd nonzero determinant, including the `N=0` boundary case. | None cited. |
| corollary `cor:leg2-central-basis` — Central reflected-pair basis and exact Gram duality | G2 `thm:central-basis` and `thm:central-Gram` | Consolidated pair-minimal even basis, rational coordinates, Gram inverse, and projection-kernel factorization. | None cited. |
| theorem `thm:leg2-Cinfty-convergence` — Superalgebraic convergence in every derivative | G2 `thm:Cinfty-convergence` and `cor:derivative-literal-loop` | Consolidated derivative-level superalgebraic convergence; the canonical theorem states the approximation norm cleanly and leaves the atom formula in the preceding synthesis results. | None cited. |
| theorem `thm:leg2-log-square` — Log-square decay inherited from the sinc product | G1 `thm:un-log-square` | Direct coefficient bound and liminf consequence in normalized notation. | Supporting exact Fourier-envelope bound `norm_rvachevFourier_le_decayGauge_abs` in `RvachevFourierDecay.lean`; label `eq:fourier-two-sided-envelope` is in `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`. The Bessel transfer to the displayed Legendre bound is not claimed as formalized. |
| theorem `thm:leg2-moment-units` — Every even up-moment is a two-adic unit | G1 `thm:moment-units` | Direct elementary moment-recurrence induction. | None cited. |
| theorem `thm:leg2-exterior-top-growth` — Exterior divergence and exact top-amplitude growth | G4 `lem:un-root`; L4 `thm:Legendre-anchor-divergence` and `thm:top-growth` | Consolidated sharp coefficient root obstruction, exterior-anchor divergence, exact top amplitude, and quadratic logarithmic limsup. | None cited. |
| theorem `thm:leg2-no-normal-closure` — No exponentially weighted normal Appell closure | L4 `thm:no-normal-closure` | Direct normal-convergence/analyticity obstruction. | Exact nonanalyticity input: label `eq:nonanalytic-up-support` in `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`; Lean theorem `canonical_rvachev_not_analyticAt` in `Analysis/FabiusFunction/Lean/FabiusFunction/NowhereAnalytic.lean`. These anchors support the obstruction input, not a formalization of the normal-convergence argument. |
| theorem `thm:leg2-Q0-asymptotic` — Central deconvolution asymptotic | L3 `thm:Q0-asymptotic` | Direct two-term factorial asymptotic, Stirling form, and root growth, with `Q^-` notation disambiguated. | Live canonical evidence: chapter 03 labels `is:p2:thm:three-shell` and `is:p2:eq:alpha-three-shell`; historical source labels X2 `p2:thm:three-shell` and `p2:eq:alpha-three-shell` remain recoverable at the pinned revision. This is source evidence, not a cited Lean declaration. |
| corollary `cor:leg2-Q-Lambert` — Lambert--`$W$` threshold with discrete monotonicity | L3 `cor:Q-Lambert` | **Strengthened/corrected**: retains the Lambert inversion and explicitly proves eventual discrete monotonicity before applying the least-integer threshold. | Same canonical nearest-pole evidence as the parent asymptotic: chapter 03 labels `is:p2:thm:three-shell` / `is:p2:eq:alpha-three-shell`; X2 records the historical source labels. |
| theorem `thm:leg2-central-growth` — Sharp central growth and failure of atomwise flattening | G4 `thm:central-root`; compatible nonflattening strand in L3 `thm:nonflattening` | Consolidated repeated-central-atom limsup and the absolute/unconditional flattening consequence, using the coefficient root obstruction established in `thm:leg2-exterior-top-growth`. | None cited. |
| proposition `prop:leg2-Q12-nonreal` — First nonreal zeros; exact computer-assisted certificate | G2 `prop:Q12-nonreal` | Direct exact Sturm result, extended table through degree 20, and explicit separation of exact counts from diagnostic approximations. | Exact retained evidence directory: `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/assets/evidence/legendre/root-geometry/`; authoritative files are `Q12_sturm_certificate.txt`, `sturm_real_root_counts.csv`, and `verify_sturm.py`. |

## One-to-one coverage audit

The canonical inventory and this ledger agree one-for-one:

| Canonical source | Canonical theorem-like environments | Crosswalk rows | Missing | Extra |
|---|---:|---:|---:|---:|
| `Up_Polynomial_Synthesis.tex` | 25 | 25 | 0 | 0 |
| `chapters/Lagrange_Cardinal_Loops.tex` | 16 | 16 | 0 | 0 |
| `chapters/Legendre_Spectral_Closure.tex` | 17 | 17 | 0 | 0 |
| `chapters/Legendre_Transmutation_Arithmetic.tex` | 22 | 22 | 0 | 0 |
| **Total** | **80** | **80** | **0** | **0** |

Static extraction found 80 distinct canonical labels and no unlabeled or
duplicate theorem-like environment among the four files. Set comparison
against the 80 canonical-label cells above found no missing label, no extra
label, and no duplicate crosswalk row. Thus the ledger has verified 1:1
coverage at the assertion-environment level.
