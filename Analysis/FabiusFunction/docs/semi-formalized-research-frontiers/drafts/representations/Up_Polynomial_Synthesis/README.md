# Exact Rvachev up-function polynomial synthesis

This directory is the canonical representation volume for exact polynomial
synthesis, Lagrange cardinal loops, Legendre spectral closure, operator
transmutation, and finite self-reconstruction by Rvachev up-atoms.

The report consolidates thirteen earlier packages:

- three exact-polynomial synthesis packages already absorbed into the original
  volume;
- six Lagrange--Rvachev reports;
- four Legendre--Rvachev reports.

Repeated background and equivalent matrix notations are stated once. Distinct
theorems are grouped by mathematical dependency, every theorem-like
environment has a proof, conjectures are explicitly labeled, and vague
normalization claims have been demoted to problems.

## Canonical artifacts

- Up_Polynomial_Synthesis.tex — report driver.
- chapters/Lagrange_Cardinal_Loops.tex — exact cardinal synthesis, right
  inverses, projectors, ghosts, nested details, conditioning, q-binomial rows,
  Appell--Vandermonde growth, and denominator support.
- chapters/Legendre_Spectral_Closure.tex — literal mode synthesis, blockwise
  self-reconstruction, energy, translated analysis, biorthogonality, reverse
  closure, Gram frames, refinement, and flatness.
- chapters/Legendre_Transmutation_Arithmetic.tex — pullback geometries,
  conjugated operators, Gauss/Christoffel--Darboux synthesis, smoothed
  Legendre--Appell connections, parity, central q-determinants, asymptotics,
  exact Sturm evidence, and consolidated conjectures.
- Up_Polynomial_Synthesis.pdf — accepted current 63-page report. The complete
  merged-source receipt is root
  `2385L/99806B/81f3ba09894aca8331ae33c77e2a56f78c107fa3b04072878cff8ad60e815b5a`,
  five-file aggregate
  `11bd62d880f5ba4c63d872fb0ba5d801d10ba2a2337ef5d098643383639086dd`,
  passes `61/63/63`, PDF
  `63pp/1077921B/0903f2920d21f0ea8182822c31338e0be268d4d77bc8ddb7a2ff861ba2a6aa5f`,
  and log
  `964L/38999B/52bd9d03864853f1ee31fa682fa96806345bb355582831c55fcc152c1acb2e7d`.
  Every recorded prohibited-log, A4/rotation, PDF 1.5, encryption,
  font/subsetting, Libertinus, Type-3, and visual gate passed. The former
  60-page artifact remains explicit history.
- assets/provenance/THEOREM_CROSSWALK.md — one-to-one provenance and evidence
  ledger for all 80 theorem-like assertions.
- assets/provenance/ — source snapshots, migration map, and asset policy.
- assets/provenance/COMPANION_PAYLOADS.csv — one-to-one old-to-new map for all
  113 selected companion payloads.
- assets/companion-evidence/ — 104 migrated scripts, exact tables, captured
  outputs, requirements, and useful PNG diagnostics, grouped by source slug;
  the provenance map also covers two already-canonical root-geometry files and
  seven retired checksum-ledger rows without live destinations.
- assets/evidence/legendre/root-geometry/ — exact Q12 Sturm certificate,
  complete counts through degree twenty, and a focused verifier.
- Package checksum manifests are retired; scoped hashes remain in the
  provenance CSVs and historical artifact receipts.

## Notation contract

- Q_n^- = M_u(D)^(-1) P_n is the deconvolved Legendre family used for
  synthesis samples.
- R_n = M_u(D) P_n is the distinct moment-smoothed Legendre family.
- A_n = M_u(D)^(-1) x^n is the Rvachev--Appell family.
- X_- = x - K'(D) and X_+ = x + K'(D), with K = log M_u.
- a_n is the coefficient of P_(2n) in the even Fourier--Legendre expansion of
  u.

These names are deliberately not interchangeable.

## Build and verification

From this directory, run three direct passes:

    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex
    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex
    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex

Then inspect the log for undefined references, missing files, overfull boxes,
and font substitution. Render all pages to images and inspect the full contact
sheet plus representative pages at original resolution. The committed PDF
must be A4, have embedded/subset fonts, and contain no Type 3 fonts.

The focused exact Sturm verifier requires SymPy:

    python assets/evidence/legendre/root-geometry/verify_sturm.py

Lean is verified separately from the repository root with one serialized
umbrella build:

    LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction

On PowerShell, set the two environment variables before invoking Lake.

## Evidence discipline

Human-readable proof, exact symbolic certificate, focused Lean build,
repository-wide Lean build, and remote CI are distinct evidence levels. This
package does not equate them.

Several analytical and finite-dimensional results in the new Lagrange and
Legendre chapters remain human proofs backed by exact scripts rather than Lean
theorems. The report says so explicitly. Existing compiled Lean declarations
are named where they discharge a claim; no source-only statement is presented
as kernel verified. The translated Legendre analysis kernel and its finite
biorthogonality identity are now the explicit exception described below.

The current `FabiusFunction.LagrangeRvachevMatrix` surface consists of the
finite-index declarations `rvachevAtomIndexSet` and `RvachevAtomIndex`, the
definitions `lagrangeRvachevEncoderMatrix` and
`lagrangeRvachevDecoderMatrix`, and six theorems:
`lagrangeRvachevEncoderMatrix_nonneg`,
`sum_lagrangeRvachevEncoderMatrix_row_eq_one`,
`sum_lagrangeRvachevDecoderMatrix_row_eq_one`,
`lagrangeRvachevEncoderMatrix_mul_decoderMatrix`,
`exists_neg_entry_of_rightInverse_of_row_overlap`, and
`exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap`. This closes
`prop:lag-markov` exactly, with positive row overlap retained as a hypothesis.
For the compound `thm:lag-right-inverse`, it closes only the boxed `UB = I`
clause; the `BU` projector, basis, spectral, moment, intertwining, and
Cauchy--Binet clauses remain human proofs. The crosswalk therefore remains at
80 canonical assertion rows (including 11 conjectures); no assertion-count
delta accompanies these evidence-status changes.

The older compiled module `FabiusFunction.LagrangeRvachevSynthesis` already
closes `thm:lag-cardinal` Exact/Complete by assembly, without a redundant
report-shaped wrapper. The individual-cardinal declaration is
`normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp`; the
arbitrary-data declaration is
`sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp`. Here `M ≠ 0`
is the positive-mesh condition, `s.card - 1 ≤ padicValNat 2 M` is admissibility
through degree `d = |s|-1`, the evaluation point remains in `[-1,1]`, the
integer open interval is exactly `|k| < 2M`, and `(M : ℝ)⁻¹` is the displayed
spacing `h`. The atoms are literal unit-radius translates. Node injectivity is
not needed for the polynomial identities and is supplied by the report when
they are read as cardinal interpolation. This promotion does not promote any
additional clause of the compound `thm:lag-right-inverse`.

The compiled source-only `FabiusFunction.RvachevLagrangeNodesOnly` module
promotes `cor:lag-nodes-only` from a human proof with no Lean anchor to an
Exact/Complete compositional counterpart. Its exhaustive public surface is
one definition, `rvachevDeconvolvedPolynomialRat`, and fourteen theorems:
`map_rvachevDeconvolvedPolynomialRat`,
`rvachevDeconvolvedPolynomial_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative`,
`rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell`,
`lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell`,
`map_lagrangeBasis_ratCast`,
`map_rvachevDeconvolvedPolynomialRat_lagrangeBasis`,
`lagrangeRvachevDecoder_eq_ratCast`,
`rvachevRawMomentRat_eq_centeredRvachevFullMoment`,
`momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant`,
`momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne`, and
`rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant`.
Together they give the printed derivative cutoff, the raw omitted-node
elementary-symmetric/Appell expansion, rational coefficient descent and
rational lattice values, and the complete-Bell link to formal centered
cumulants. This is exact by assembly rather than by a single wrapper theorem.
It does not claim rational values at irrational evaluation points or analytic
convergence of the reciprocal MGF. Its promotion is independent of the
existing synthesis assembly for `thm:lag-cardinal`, and neither result
promotes the larger `thm:lag-right-inverse`.

The compiled `FabiusFunction.RvachevLegendreCentralSum` module promotes
`cor:leg-central-sum` to Exact/Complete. Its exhaustive public surface has no
definitions and three theorems: `eval_legendrePolynomial_even_zero`,
`eval_rvachevLegendreDeconvolutionPolynomial_even`, and
`rvachevLegendreCentralSum`. The last theorem is the printed identity with
`M = 4 ^ n`: it evaluates the existing even Legendre synthesis at zero,
removes `|k| >= M` by compact support, pairs the remaining nonzero nodes by
evenness, clears the mesh factor, and uses the exact central Legendre value.
It is slightly stronger only in allowing any `BoundedFabius` satisfying
`IsFabius`, and it includes `n = 0`. This promotion does not formalize the
Jacobi closed form, all-degree parity or rationality in `thm:leg-mode-synthesis`,
nor reverse closure, mesh minimality, or any larger Lagrange right-inverse
claim. The accepted current 63-page package PDF renders these status
annotations; the former 60-page artifact remains historical.

The compiled source-only `FabiusFunction.RvachevLegendreBiorthogonality`
module promotes only `thm:leg-biorthogonality` to Exact/Complete. Its
exhaustive public surface is one definition,
`rvachevLegendreAnalysisKernel`, and one theorem,
`rvachevLegendreBiorthogonality`. The definition is exactly the printed
translated kernel `def:leg-Lambda`, the `(2m+1)/2`-normalized integral against
`P_m`; the theorem has exactly the
positive natural mesh encoded by `M != 0`, admissibility
`l <= padicValNat 2 M`, the open integer block `|k| < 2M`, the outer factor
`M^-1`, and the Kronecker value `if m = l then 1 else 0`. It includes
`l = 0` and `m = 0` and harmlessly allows any `BoundedFabius` satisfying
`IsFabius`. It does not promote the support, smoothness, Fourier--Bessel, or
rationality package in `thm:leg-Lambda`, nor
`cor:leg-biorthogonal-matrices`, the compound mode-synthesis/reverse/Gram
rows, or any Lagrange right-inverse claim.

Independently, the existing `FabiusFunction.TwoAdic` declarations make
`thm:leg2-moment-units` Exact/Complete by assembly. The repository sequence
`moment m : ℚ` is the manuscript's even moment `mu_(2m)`;
`moment_padicVal_two` proves its rational two-adic valuation is zero, and
`moment_num_den_odd` proves that its reduced numerator and denominator are
both odd. The latter is exactly `mu_(2m) = 1 mod 2` under the standard residue
convention for rational two-adic units. Both declarations include `m = 0`.
This is executable rational valuation/parity data, not construction of a
separate topological `ℚ_2` value, and it promotes no neighboring Legendre
asymptotic or matrix row. The accepted current 63-page package PDF renders both
promotions; the former 60-page artifact predates them.

The Q12 root transition is exact computer-assisted mathematics: rational
polynomials and rational Sturm chains decide root counts. Approximate complex
root locations are diagnostics only.

## Asset and retirement record

No two companion files among the ten later reports were byte-identical, even
after line-ending normalization. Similar filenames often use different ranges,
normalizations, or operators. The report prose and PDFs were therefore retired
after consolidation. Of 113 disposition rows, 106 retained evidence payloads
received canonical destinations; seven checksum-ledger rows were retired.

Historical checksum ledgers are provenance recoverable from Git history; they
are not retained or rewritten to fit new paths. Canonical Git-tree bytes are
tracked directly rather than through live package-local ledgers.

The ten source directories were retired on 31 August 2026 after 106 retained
payloads received canonical destinations, seven checksum-ledger rows were
retired, every theorem label received an auditable crosswalk, the PDF and exact
verifier passed, and a fresh checkout validated the then-recorded root checkpoint. Their exact
pre-retirement bytes
remain recoverable at commit
`443793e846934e7363e314ea01129b9f50197a58`; the completed gate is documented
in `assets/provenance/ASSET_INVENTORY.md`.
