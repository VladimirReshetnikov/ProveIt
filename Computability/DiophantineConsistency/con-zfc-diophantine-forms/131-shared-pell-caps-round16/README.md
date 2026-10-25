# Shared Pell caps and coprime product equations for ZFC consistency

Round 16, prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Recommended fixed equations:
- 249 nonnegative inputs, degree 4, 186 residuals, 27,078 monomials, height 85,178,741.
- 278 nonnegative inputs, degree 4, 215 residuals, 5,524 monomials, height 83,852,788.
- 324 unrestricted integer inputs, degree 4, 208 residuals, 5,808 monomials, height 128,446.
- 338 unrestricted integer inputs, degree 4, 222 residuals, 4,493 monomials, height 128,446.
- Eleven unrestricted inputs at degree/operation pairs 966/109, 882/110, 810/112 and 654/117.
- Ten strictly positive inputs at degree/operation pairs 436/87 and 380/88.

The report gives complete new unbounded proofs and explicit polynomial definitions. Actual coefficient payloads, literal quartic equations and complete collected coefficients, transformation certificates, finite source recipes, mathematical dependency closure and license notices are included. The domain is part of every result. The positive 384/92 and 334/93 variants are retained controls, not recommended frontier points.

The conclusion is the ZFC-provable equivalence between unsolvability on each specified domain and Con(ZFC), under the retained ordinary logical calibration. This does not prove consistency and is not a new end-to-end Lean/Rocq or encoded object-ZFC proof object. Finite audits verify artifacts and algebra, not their universal nonvanishing. No global optimum or literature-wide priority is claimed.

## Replay

With Python 3.10+ (standard library only), from this directory:

    python verify.py --report replay.json
    python -O verify.py --report replay-optimized-driver.json

Both normal and optimized child interpreters run by default. Use --mode normal or --mode optimized to select one. The verifier checks all manifest bytes before running in an isolated temporary copy. All supplied final endpoints and coefficients are regenerated and checked against reference bytes. No network, sibling source directory, ProveIt checkout or proof assistant is needed.

Build the TeX report with pdfLaTeX and its standard LaTeX packages:

    sh build_report.sh

The script performs three passes. The archive contains only the final PDF, not transient TeX outputs or page images. The complete unabridged proof sources also appear separately as Markdown for convenient review; report/ contains every TeX input.

CLOSURE_MAP.md maps mathematical dependencies to local files. SOURCE_INVENTORY.json is the curated whitelist; MANIFEST_SHA256.json binds every delivered file except itself. Review receipts authenticate comparison work against ProveIt f4d8db99e060339f3306a04d507c35bc1d0d68c5. Omitted incoming polynomial artifacts are not replayed by this compact archive, and the receipts are explicitly historical finite checks rather than a claim that every incoming program was executed.

ENDPOINTS.json is the concise integration index with domains, metrics and exact equation/polynomial hashes. REPLAY.json and ISOLATED_REPLAY.json record both-mode verification of the mathematical snapshot; subsequent changes were limited to documentation, presentation and audit receipts, not polynomial or executable mathematics. The final manifest authenticates all delivered bytes. Producer freeze receipts preserve their historical review state; the final audit disposition is in cap_audit/FINAL_AUDIT.md, scalar_audit/SEMANTIC_REVIEW.md and small_audit/SEMANTIC_REVIEW.md.
