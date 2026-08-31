# Repository and mathematical audit

Audit date: 30 August 2026

## Provenance boundary

The earliest observable state of this package carried a self-excluding
11-entry SHA-256 ledger, and every listed file verified before modification.
That ledger is preserved byte for byte as `SHA256SUMS.arrival.txt`; its hash is
`eab71028a18157e98c36278b987009421c9eb79b7abb902c21a4986beb16477d`.
The arrival source hash was
`79d2f7fe05c457c207254ec35a8d18d880364a63b0e01b56181e1d7a599e1d65`;
the arrival PDF hash was
`a990c74070dbaf5a79c9840ec8a3cd30a757b651dbd94db0f4bd7bc02cabc036`.
The outer source archive is unavailable, so this record deliberately makes no
claim about an archive filename, byte count, ZIP member metadata, or outer
hash. `ARRIVAL_MANIFEST.txt` is an accurate reconstruction from the verified
ledger, not a submitted ZIP manifest.

## Hostile mathematical read

The source contains 25 theorem, three proposition, one lemma, eight corollary,
two conjecture, five problem, three definition, one algorithm, and five remark
environments. The audit traced hypotheses, normalization conventions, signs,
indices, convergence steps, and dependencies for all 37 labelled
nonconjectural results. It also checked that conjectural and proposed work is
not used as a proof premise. No fatal counterexample or result requiring
downgrade from theorem status was found.

The most material proof repair concerns the explicit density of the
q-exponential perpetuity. The final proof starts with the finite-product simple
partial-fraction decomposition, passes to the infinite identity under a
Gaussian-in-index dominating bound, and only then performs termwise Laplace
inversion. This removes the original unjustified jump from pole residues to an
infinite partial-fraction expansion.

Other substantive boundary repairs are visible in the report itself:

- the abstract now says that theorem statements have manuscript proofs, not
  undifferentiated proofs;
- numerical replay, manuscript proof, and Lean proof are explicitly distinct;
- the scope note limits “new” to the inspected local corpus and does not claim
  global literature novelty;
- the opening status box and closing roadmap separate already formalized finite
  Gaussian-comb facts from the report-specific obligations still outstanding;
- conjectures and numbered research problems remain explicitly labelled.

This audit is a manuscript-level hostile review, not a machine-checked proof of
the whole report. Literature priority was not exhaustively surveyed outside the
cited and linked local sources.

## Lean-status crosswalk

Read-only inspection of the live Lean corpus located relevant checked
infrastructure in:

- `FiniteQBinomialCore.lean`, `GeometricLagrangeQBinomial.lean`,
  `GeometricLagrangeQMoments.lean`, and
  `GeometricLagrangeCompleteHomogeneous.lean` for finite q-products, Gaussian
  weights, cancellation/residual formulas, complete-homogeneous formulas, and
  finite row norms;
- `LimitConditionNumber.lean` for convergence of the finite condition numbers
  to the fixed-q infinite product;
- `GeometricUniformLaw.lean` and `GeometricUniformCDF.lean` for the
  geometric-uniform probability law and CDF/density infrastructure;
- `RvachevQBinomialFilter.lean` for a finite Gaussian transform related to the
  Rvachev Fourier product.

No exact current declaration was located for the Jackson divided-difference
identification, locally uniform infinite Newton reconstruction, confluent
Puiseux--log filters, reversed-row l1 limit and regular-variation transfer,
Hermite--Genocchi/geometric-knot B-spline probability law, perpetuity scaling
limit, Fabius boundary expectation, or entire scale reconstruction. Those
report-specific results remain manuscript theorems. No Lean file was changed.

## Numerical replay

The companion program was run in a clean virtual environment with CPython
3.13.14 and the exact versions recorded in `requirements-lock.txt`. The direct
pins are `mpmath==1.4.1` and `matplotlib==3.10.8`. The plotting backend was
frozen to `Agg`, PDF/PS plot-font settings were pinned to TrueType output, and
CSV writers were made to emit LF records deterministically.

The replay regenerated these seven outputs byte for byte:

- `moment_checks.csv` —
  `3e9ffb76e72a054e60756ed6562ed115f17c83275d178f2bdfc891845cd099c0`;
- `stability_growth.csv` —
  `f32584d748ba545130c4a04dba5dfe80d9c187789cea26a73375ee32f5c6347d`;
- `regular_variation.csv` —
  `24722f71abe6f85d72e60ef2dd481d4665801be81501b7c36d14c56afdb48b4e`;
- `fabius_boundary.csv` —
  `6df1166c14ddbf1afb86f58572db59dfdbfcadcfef5f32f83c817ad54ce332f1`;
- `stability_growth.png` —
  `5c1374d8bd1a16fa998b5bf56a7df28c88a526f104a03d1308065da9387c1384`;
- `regular_variation_convergence.png` —
  `5abaf630673918a6b3419c717cd714c50914a0a73fa738508620027e901ee9cd`;
- `fabius_boundary_ratio.png` —
  `9793c0c5cb2f28eef134b70b0c3e8ff7ee5cf3f4841f0ce0df01a55fb8e0f279`.

The computations are reproducibility checks and diagnostics; they are not
substituted for the manuscript arguments.

## Document normalization

The report now uses the canonical primary article form: 11 pt one-sided
article, A4 paper, 27 mm margins, 15 pt header height, Libertinus with a guarded
fallback, the shared typography/navigation stack, and a centered page-number
footer. The theorem-family aliases are type-correct for `cleveref`. The final
source has 2,372 lines and SHA-256
`02dd81e5d1480e867c2482a38574accf06b6bedd19cbef5dccc6a585cca01711`.
Build and artifact validation is recorded separately in
`PDF_VALIDATION.txt`.
