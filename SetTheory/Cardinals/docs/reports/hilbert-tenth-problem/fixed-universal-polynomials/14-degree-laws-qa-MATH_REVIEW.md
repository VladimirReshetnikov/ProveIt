# Mathematical review of Report 24

Date: 3 October 2026

**Result: PASS. No unresolved mathematical defects were found in the reviewed article.**

Reviewed article: `article/report24.tex`

Reviewed TeX SHA-256:

`5962e0e6e36567841a60ca079b68fc2eb2a713b9d47cf54ea0767e69f4dc3bb7`

Final revision check: formatting adjustments, source-pin table column widths and row spacing, and the corrected spacing command between the outer loader residuals were verified against the previously reviewed version. No mathematical claim or formula changed.

## Scope and findings

The review compared the article with the pinned native source, 67-row kernel, loader source, and 130-row recoder receipt. It checked the source transcription and symbolic argument, rather than inferring the general theorem from numerical cases.

- The compact kernel matches the source, including the product in the sixth residual and the distinct native and recoder auxiliary coordinates
- The unrestricted norm identity cancels exactly the common squared term. The four unit-factor degrees are `5α+7`, `12α−16`, `3α+5`, and `α`, giving `deg U = 21α−4 = 63N−4`
- All ten native residual degrees are correct. The one-phase residual has degree one, and the strong norm residual is uniquely largest with degree `4α+10 = 12N+10`
- Multiplication of the highest forms gives scalar `2^138`, power `p^(29N−8)`, and total degree `87N+16`. The all-coordinate diagonal coefficient is exactly `−2^148(2Ks)^(29N−8)`
- One-phase, repeated-exponent, and allzero tables retain the required nonzero top factors. The source's uint32 domain and the mathematical extension to fixed nonnegative exponents are distinguished correctly
- The gluing law uses a positive sum of squares over the integers and remains valid for shared coordinates and ties. Its maximum degree must be exact. The integer-zero-set argument and placement of the added squares inside the unit finalizer are correct
- The recoder maximum is exactly `max(k+1,20)`, including the fixed degree-20 baseline and the tie at `k=19`. The canonical frame attains degree 34, so the full loader maximum is `max(34,k+1)`. The native-width equality has degree two
- The matching-width dominance condition, frozen-width crossover, and distinction between free external parameters and specialized program slices are correct
- The witness counts are `W_native=N+18` and `W_total=N+124`, excluding the supplied native input in the former and the six external coordinates in the latter. The affine degree identities are ledger-specific, with no encoding-independent lower-bound claim
- For a fresh input of exact degree `δ≥1`, putting `d=δ+2` gives `deg U=21dN+20−8d`, residual maximum `4dN+10`, and final degree `d(29N−8)+40`. The width, radix, and transport lane comparisons are valid throughout the stated domain. Fresh example variables are distinct from the native root auxiliary
- The article does not infer loader semantics, universality, minimal degree, or an all-table proof from finite regression checks

## Regression checks used in the review

Read-only data checks passed for the four frozen small DAGs, allzero and maximum-uint32 formula cases, complete univariate coefficient expansions, and the recoder's all-width degree bounds. Fresh-input expansions give degrees 936 and 1160; the difference-of-squares input drops to degree 712 on its cancelling all-ones ray, as stated.

The optional full-DAG regression also passed: 3,600,546 gates, 86 residual squares, exact degree 69,339,973, and leading coefficients 3 modulo 17 and 53,942,795 modulo 1,000,000,007.

These checks support the transcription and examples. The article's symbolic proofs establish the parameterized results. This review does not certify unrelated semantic dependencies or substitute for the separate rendering and release-integrity checks.
