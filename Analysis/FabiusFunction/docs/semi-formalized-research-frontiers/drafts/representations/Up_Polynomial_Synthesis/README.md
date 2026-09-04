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
- Up_Polynomial_Synthesis.pdf — rendered report.
- assets/provenance/THEOREM_CROSSWALK.md — one-to-one provenance and evidence
  ledger for all 80 theorem-like assertions.
- assets/provenance/ — source snapshots, migration map, and asset policy.
- assets/provenance/COMPANION_PAYLOADS.csv — one-to-one old-to-new map for all
  113 selected companion payloads.
- assets/companion-evidence/ — 104 migrated scripts, exact tables, captured
  outputs, requirements, and useful PNG diagnostics, grouped by source slug;
  the provenance map also covers the two already-canonical root-geometry files.
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
as kernel verified.

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
convergence of the reciprocal MGF, and it does not promote either
`thm:lag-cardinal` or the larger `thm:lag-right-inverse`. The retained package
PDF predates this source-only status promotion and was not rebuilt.

The Q12 root transition is exact computer-assisted mathematics: rational
polynomials and rational Sturm chains decide root counts. Approximate complex
root locations are diagnostics only.

## Asset and retirement record

No two companion files among the ten later reports were byte-identical, even
after line-ending normalization. Similar filenames often use different ranges,
normalizations, or operators. The report prose and PDFs were therefore retired
after consolidation, while 113 distinct evidence payloads received canonical
destinations and live hashes.

Historical checksum ledgers are provenance. They are preserved without
rewriting old hashes to fit new paths. The live companion and root ledgers hash
canonical Git-tree bytes and do not target removed arrival files.

The ten source directories were retired on 31 August 2026 after all 113
selected payloads received canonical destinations and hashes, every theorem
label received an auditable crosswalk, the PDF and exact verifier passed, and a
fresh checkout validated the live root ledger. Their exact pre-retirement bytes
remain recoverable at commit
`443793e846934e7363e314ea01129b9f50197a58`; the completed gate is documented
in `assets/provenance/ASSET_INVENTORY.md`.
