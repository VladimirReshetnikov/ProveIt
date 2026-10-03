# Report 23 revision 1 mathematical review

Date: 3 October 2026

Result: PASS. No mathematical defect found in the revision's exact-degree theorem or its integration with the previously reviewed article.

## Inspected text and evidence

- Article: `article/report23.tex`
- Inspected TeX SHA-256: `851afef18a17295f84d63f0bd67334cdb384a7a85af1f90f80477956c8d66c97`
- Exact-degree research manifest SHA-256: `17fdac05bdfbe5bc31e86dfe2c7addbf45cea5409b184131f0cb2e9c2c51a888`
- Compared against `DEGREE_PROOF.md`, `independent-review/INDEPENDENT_LEADING_PROOF.md`, both checker implementations and their certificates, and the final prose-review PASS in `QA_RECEIPT.json`
- Verified all 14 files authenticated by the exact-degree manifest

This review focuses on the substantive new degree analysis and changed headline claims. It does not repeat the earlier edition's full semantic review or the separate visual and packaging checks.

## Mathematical checks

The local register aliases agree with the raw source, including the zero-based input index for gamma and gate 3,600,240 for the first unit factor. The distinctions between local u and a, the ordinary input x, the loader witness X, and the fixed exponent N_* are explicit and correct.

The identity

R15 = u² + 2uac + 2u gamma d + 2ac gamma d + gamma²d² − dc², with d = 4a + 3,

follows by unrestricted polynomial expansion of the displayed norm. No residual equation, positivity assumption, or valid-history hypothesis is used. The fourth term is uniquely highest, giving degree 5 alpha + 7 and leading form 8 gamma w² b_*³ k_* Q_*⁵.

An additional independent degree-only pass through all 3,600,546 raw gates, with precisely this identity at R15, reproduced the article's bounds. All 67 native-kernel rows were matched operand-for-operand. The four unit-factor degrees are 11,955,172; 28,692,380; 7,173,104; and 2,391,033, totaling 50,211,689. Direct inspection of the kernel formulas confirms their stated nonzero leading forms.

All 86 residuals are accounted for. The first ten bounds match the article in order; the next 75 have maximum bound 397,489; the final width residual has bound two. Residual 6 is uniquely maximal, with degree 9,564,142 and leading form i²c_*⁴. Its square therefore supplies the entire leading form of the positive finalizer factor, of degree 19,128,284.

The complete leading form has the stated constant 2^138, exponent 29N_* − 8 = 23,113,311 on the degree-three base, and remaining degree 40. Multiplying the nonzero factor forms proves exact total degree 69,339,973. The all-coordinate ray coefficient is exactly

−2^148 (2^551891 · 794976)^23113311.

Independent modular arithmetic reproduced residue 3 modulo 17 and residue 53,942,795 modulo 1,000,000,007. Either nonzero residue deterministically certifies attainment of the upper bound.

## Scope and consistency

The abstract, main theorem, size table, degree discussion, new theorem, further-questions section, and conclusion consistently report exact degree 69,339,973. The historical 71,731,007 is consistently retained as a valid syntactic upper bound; the difference is 2,391,034.

The article correctly separates unconditional algebra on the frozen polynomial from the language theorem's pinned semantic imports. It claims neither a smaller circuit nor a minimum over representations. The DAG, arithmetic manifest and kernel hashes match the earlier release. The raw operation census remains 803,517 multiplications and 2,797,029 additive gates; the manifest still has six external coordinates and 797,135 witnesses. No article or frozen source file was modified during this review.

Final layout verification: the only change after mathematical review was one `\clearpage` immediately before the bibliography. Removing that insertion reproduces the previously reviewed TeX hash exactly. The inspected hash above identifies the final source.
