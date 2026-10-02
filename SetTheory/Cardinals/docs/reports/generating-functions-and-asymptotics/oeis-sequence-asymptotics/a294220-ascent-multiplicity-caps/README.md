# Bounded multiplicity in ascent sequences

Research report dated 1 October 2026. Primary deliverables are `bounded-multiplicity-report.pdf` and its editable TeX source. This package is self-contained for every fixed cap b>=3. The separate, previously supplied cap-two report is identified in `provenance.json` and is not duplicated.

## What is proved

- The factorial root constant is mu_b=1/T_b, with T_b the integral of log(E_b(v))/(E_b(v)-1) and E_b(v)=sum_{j=0}^b v^j/j!
- For each fixed b>=3, log(a_n)=log(n!)-n log(T_b)+O_b(n/log n). The independent cap-two result implies this weaker bound there too
- An explicit principal-branch Lambert-W length approximation with additive error O_b(log X/(log log X)^3)
- Exact large-cap first variation (b+1)(zeta(b+2)-1), with nonlinear remainder between zero and 160 b^(5/2)(4/9)^b for every integer b>=3
- A rounding-safe Lambert-W cap inverse, including an explicit integer bracket

The cap-three sequence is OEIS A317784, the family is A294220, and cap two is A202058. Full prefactors, normalized ratio limits, all-orders expansions in length, and uniform joint cap/length results are not established here. No exhaustive priority claim is made.

## Reproduce

Dependencies: Python 3, mpmath 1.3.0, and a PDFLaTeX installation with the standard packages in the source. Poppler is useful for PDF inspection but is not required to build the report.

1. Install Python dependency: `python3 -m pip install -r requirements.txt`
2. Run exact and numerical checks: `./verify.sh`
3. Rebuild the PDF: `./build.sh`
4. Verify supplied-file hashes before rebuilding: `sha256sum -c SHA256SUMS`

`verify.sh` writes fresh results to `checks/replay/`, compares with the saved results, and fails if an assertion fails. The direct, raw-budget, and grouped recurrences are separate implementations. Exact enumeration and bijection checks use integers. Barrier tests use floating point. Quadrature uses 70 decimal digits; its decimal outputs are not interval-certified bounds.

The PDF build uses a fixed date epoch. PDF bytes can still depend on the TeX installation. The mathematical source and test results are the reproducibility targets across installations.

## Files

- `bounded-multiplicity-report.tex` and `.pdf`: integrated theorem, proofs, both inverses, literature, and open questions
- `build.sh`, `verify.sh`, `requirements.txt`: rebuild and rerun commands
- `checks/`: executable independent enumeration, involution, rank/barrier, constants, and large-cap tests, with saved JSON results
- `support/`: original fixed-cap, compaction, and leading large-cap proof records
- `audits/`: original independent audits, stronger cap-remainder/inverse audit, and fresh integrated report audit
- `provenance.json`: hashes of source proofs and the distinct cap-two deliverable
- `literature.md`: scoped primary-source and OEIS retrieval record
- `verification-summary.json`: release checks, scope, and numerical/visual validation status
- `SHA256SUMS`: hashes of supplied files

The superseded exploratory proposals are not included. Further exponential-sector work, if developed separately, is not a claim of this report. No external upload or OEIS edit was performed in preparing this archive.
