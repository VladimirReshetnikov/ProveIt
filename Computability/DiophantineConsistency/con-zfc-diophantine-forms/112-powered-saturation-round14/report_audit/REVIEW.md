# Independent final report review: round 14

## Verdict and scope

PASS for the final mathematical exposition, principal literal metrics, and the reviewed 26-page PDF. No unresolved report-level error remains after the corrections listed below. The approved PDF and exact TeX hashes are recorded in `PDF_QA.json`.

The review checks the report against the frozen mathematical proofs, the independent scalar audit, and the independent natural/signed-direct audits. It includes an additional independent reconstruction of every principal quartic coefficient, complete visual page review, and a fresh TeX compilation. It does not claim a new proof of consistency, an independent recompilation of every transitive compiler/calibration dependency, a new Lean or Rocq endpoint, an object-language ZFC derivation, global minimality, or worldwide priority.

## Mathematical exposition checked

The final scalar section preserves the correct order: recover the guard before proving c and I nonzero; derive H dividing K_red^5 without improperly cancelling multiplicities; invoke the full pre-projection signed rank interface; use the authentic large base and the exact unit congruence to force the powered product to vanish; then restore the main projection. The p-adic interpolation proof includes odd-prime binomial lifting and the separate 2-adic doubling argument. The same strong pair remains fixed before choosing the supported-modulus residue. Completeness supplies the final integer n and reverses the integral shear.

The degree proof identifies a genuine specialized nonzero coefficient and exact degree 768. It explicitly distinguishes that degree from the minimal graph's naive 976 bound. The 141-operation graph has 88 multiplications, 26 additions and 27 subtractions; the 149-operation reduced graph is polynomial-identical. All six actual coefficient ports are retained, with shifted M_F and authentic beta identified. No coefficient payload size is mislabelled as expanded coefficient height.

The natural arithmetic section gives both directions for the reciprocal prime-power CRT reduction, the factorial ceiling lemma, the carry-free digit interface, the small amplification budget, the factorial-weight Horn-flow certificate, and the derived-label range. It retains precision 2K and the free index range, treats truth's unit weight explicitly, proves accumulator positivity before cancellation, and chooses the proof horizon before the accumulator sizes. The derived label is excluded from the independent-representative aggregate and receives its own coefficient-aware carry bound. The generic derived-range lemma explicitly requires K >= t+1.

The signed section retains the base-one exception and the raw-q orientation anchor, then the two-request argument that orients the K pair. It does not assume factorial or binomial semantics prematurely. The redundant auxiliary guard is removed only after presemantic exponent positivity is proved. Horn factorization, integral monic projection, and coordinate translation have both forward and reverse explanations. The 517-integer source is correctly distinguished from the 519-integer source.

The shared83 and weakened86 counterexamples are stated as failures of particular weakened arithmetic interfaces. They are not described as refuting the original modified75 compiler, source34, or the retained generalized signed kernel. The report keeps ordinary inherited calibration separate from finite literal-algebra/source-equality checks and from new proof-assistant verification.

## Principal metrics independently reconstructed

`check_final_metrics.py` imports no producer or prior checker. It explicitly squares and sums each final quadratic residual, combines every monomial, compares the entire expanded coefficient list, and verifies every declared variable occurs. `FINAL_METRICS.json` records the input hashes and passing results.

- 519 unrestricted integers: 321 quadratic residuals, degree 4, 6253 nonzero monomials, height 411060.
- 517 unrestricted integers: 310 quadratic residuals, degree 4, 6774 nonzero monomials, height 3904267.
- 349 nonnegative integers: 268 quadratic residuals, degree 4, 12768 nonzero monomials, height 86915503.

The comparisons preserve domain distinctions and tradeoffs. The 517-integer endpoint has fewer variables but larger support and height than 519. The 349-natural endpoint has fewer variables than the 363-natural reciprocal point but more support and height. The 350-natural horizon-16 companion is correctly reported at height 86523090. The existing 37-integer giant-coefficient quartic is acknowledged, so no general fewest-variable quartic record is implied. Residual counts are not reported as operation counts.

## Corrections requested and verified

1. Added parameter domains to the general saturation lemma and complete domain hypotheses to the range lemma.
2. Defined signed-base Pell polynomials by recurrence before their negative-base use.
3. Replaced the concise natural-branch summary with its full arithmetic proof.
4. Removed missing spaces in inherited comparison prose.
5. Corrected the 350-natural comparison from the older horizon-32 height to the current horizon-16 value.
6. Replaced the first strict factorial-sum inequality by a non-strict one, making the displayed chain valid also at n=1; the final strict bound is unchanged.
7. Corrected clean-build guidance to repeat pdfLaTeX until references stabilize. A fresh build needs three passes because the contents occupy two pages.

## PDF and source correspondence

Every one of the 26 pages was rendered at 100 dpi and visually inspected. No clipping, overlap, missing mathematical glyph, broken table, undefined reference, or unresolved TeX warning remains. After the n=1 edit only page 13 changed; after the build-guidance edit only page 25 changed. Both changed pages were rendered and inspected again, and the unchanged pages were compared byte for byte at the raster level.

The final TeX was compiled independently in a fresh directory using the installed TeX files and the author's already-created local format/font map. After three passes, the independently built PDF's 26 page rasters agree byte for byte with the inspected delivery PDF. Metadata-dependent PDF bytes need not match across compilations; the delivered PDF itself is bound by its SHA256 in `PDF_QA.json`.

## Source evidence

Reviewed sources include `radicals/PROOF.md`, `norm/PROOF.md`, all three architecture proof notes, `direct/section.tex`, `radicals_audit/INDEPENDENT_REVIEW.md`, `radicals_audit/AUDIT_RESULTS.json`, `direct_audit/UNIFIED_REVIEW.md`, `review/BASELINE_COMPARISON.md`, and `review/COUNTEREXAMPLE_SCOPE.md`, together with the principal literal equations and their separate independent receipts. The approved report's full TeX content was compared against these sources.

Archive sealing is a separate finite integrity check: its manifest, reviewed report bytes, principal endpoint bytes, and actual coefficient payloads must still agree with this review. Adding this review does not authorize later changes to the approved report or equations without replay.
