# Round 15 unified binomial and even Pell index equations

This archive supplies ordinary arithmetic proofs and exact finite artifacts for fixed polynomials whose unsolvability, under explicitly retained calibration theorems, is provably equivalent in ZFC to Con(ZFC). It does not prove consistency, decide solvability, or claim a new end-to-end Lean/Rocq certificate or global minimum.

## Principal endpoints

All four norm equations have eleven unrestricted integer unknowns and the same six complete source34 coefficient payloads.

| Equation | Exact degree | Live binary operations |
| --- | ---: | ---: |
| norm_weak/weak_integral_centered_paired.json | 416 | 125 |
| norm_weak/weak_integral_direct_paired.json | 456 | 124 |
| norm/integral_centered_paired.json | 464 | 119 |
| norm/integral_direct_paired.json | 488 | 118 |

The principal direct quartic at direct/integer442/ has 442 unrestricted integer variables, 290 residuals, 4,652 collected monomials and coefficient height 128,446. Its complete polynomial is expanded_polynomial.json, equal to the sum of squares of every residual in equation.json.

The principal natural quartic at architecture/unified_derived_cantor/natural/ has 329 nonnegative integer variables, 253 residuals, 12,210 terms and height 86,844,780. Nonnegative includes zero; positive does not. Six natural variants are included to preserve the exact source and tradeoff audit.

The dominated 446-variable signed companion is discussed in the proof as an audited comparison, but its equation files are intentionally not packaged. Experimental norm graphs are likewise omitted except for three equivalent baseline graphs needed by the independent cancellation audit. No final equation has an implicit free coefficient port.

## Reproduce offline

Requirements: Python 3.10 or later and SymPy. No network, original workspace, ProveIt checkout, or proof-assistant installation is required. The verifier does not install packages.

    python verify.py --report replay.json

This checks the top-level SHA-256/byte manifest, reconstructs all six fixed coefficients, then runs explicit normal and optimized checks, all six architecture rebuilds, both norm builders, the signed compiler and final centering, independent certificate replays and incoming literal-payload audits. Builders run only inside a fresh temporary copy. Generated equation and certificate artifacts must agree byte-for-byte with this archive. Use --mode normal or --mode optimized to select one checking mode. Running the driver itself under python -O does not disable its checks.

The retained source34 recipe command-line entry point intentionally refuses -O. The verifier invokes its construction in checked normal mode once, then independent complete payload checks run in both selected modes. This is not represented as a successful unsupported source-recipe mode.

To build the editable report, run ./build_report.sh with pdfLaTeX installed. It uses three passes and, when necessary, a private format without changing system configuration. PDF layout/date metadata can depend on the installed TeX version; the finite verifier's byte-equality claims concern literal mathematical artifacts, not a cross-version PDF byte identity.

## Read the proofs

The PDF and report/*.tex include every new unbounded argument in full: the scalar signed bootstrap, three-adic separation, powered projection, supported-modulus interpolation, both scalar carriers, exact degree proofs, unified factorial fixed point, carry bounds, CRT/Horn decoding, selective even indices, residue-one recovery, and both signed witness directions. Properly typeset reference definitions precede the literal-register proof displays.

The complete ordinary source texts remain in scalar/, architecture/, direct/, and the curated inherited source tree. Independent audit prose and executable checks are in scalar_audit/, direct_audit/, and report_audit/. The top-level report separates finite algebra verification from unbounded proof and inherited calibration.

## Provenance and comparison

The public comparison pin is ProveIt commit 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6. All eight incoming archives are reviewed with exact acquisition/source receipts in review/. The literal payloads used for ten quartic expansions and four circuit-count audits are included; the full input ZIP archives are not.

A comparison pin does not rewrite original provenance. The source34 coefficient binding retains 2605669a532342f153b13eb6b4a0af4b54f5fa37. The retained round-14 source comparison uses 84e16e43092614bae262ca59651cb9d77e31a255; its underlying direct logical calibration retains 08200eb10fde2db408c69dffd840d6920a569b1f. Required executable imports and runtime data are archive-relative.

The direct named boundaries are KEndpoint.c222_iff_zf_refutation and ConstructibleChoice.zf_refutation_iff_zfc_refutation. The norm branch retains its distinct native/source34/compiler/refutation calibration. Historical source-binding receipts are provenance records, not assertions that every historical bulk archive they mention is embedded.

## Files and licenses

MANIFEST_SHA256.json binds every delivered file other than itself. SOURCE_INVENTORY.json identifies curated source files. ENDPOINTS.json records final domains, metrics and equation hashes. VALIDATION.json records the release finite-replay summary. The full source notices and applicable MIT No Attribution, MIT and Apache notices are preserved. See NOTICE.md and source-specific license files; the top-level license does not relicense third-party material.
