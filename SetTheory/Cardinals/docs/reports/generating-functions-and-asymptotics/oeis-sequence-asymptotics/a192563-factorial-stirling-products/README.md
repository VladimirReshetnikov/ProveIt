# Report 154

## Diagonal poly Cauchy permutations at all fixed orders

This report treats OEIS A192563, the diagonal of the sign-normalized second-kind poly-Cauchy array A344639. Its exact definition is

    a_n = sum_m [n,m] (m+1)^n,  a_0 = 1,

where [n,m] denotes an unsigned Stirling number of the first kind. It counts the (n,n)-poly-Cauchy permutations of Bényi and Ramírez, and a_n/n! is E[(C_n+1)^n] for the number C_n of cycles of a uniform permutation of n labels. This growing ordinary moment regime is distinct from fixed-order moment asymptotics.

## Results

- A complete expansion at every fixed order in r/n using the exact saddle r of F_n(z) = exp(z) Gamma(n+exp(z))/Gamma(exp(z)) and exact finite cumulants
- An explicit rational Gaussian-contraction formula for every coefficient, beginning E1 = kappa4/(8 b^2) - 5 kappa3^2/(24 b^3)
- A global positive-exponential-sum contour bound and a central integrated Taylor remainder
- A uniform extension to A_(n,k) when k/n lies in a fixed compact subset of (0,infinity)
- A smooth real-parameter inverse, differentiated from exact gamma/polygamma formulas, with threshold uncertainty O_R((log nu)^(R-1)/nu^R) before rounding
- Strictly justified bounds for both the first a_n >= X and the first a_n > X, including X = a_n
- The explicit inverse nu = L/(2 ell) [1 + ((3/2)log ell + 1 + log 2)/ell + O((log ell)^2/ell^2)], with L=log X and ell=log L

The proof is fully included in Report154.tex and Report154.pdf. It does not depend on a private audit file or on a previous report.

## Important qualifications

The exact sequence, Stirling formulas, generating functions, signed conventions, and combinatorial interpretation are prior art. Final 2022 Bényi–Ramírez Theorems 2.1 and 2.6 are cited with their final numbering. The inspected official OEIS mirror contains no diagonal asymptotic, but a bounded literature search is not a proof of global novelty. The full Yakymiv 2019 cycle-moment paper, the shifted 2014 paper, the recurrence 2019 paper, and the final 2022 transform article remain uninspected; these limitations are explicit in the report and SOURCE_PROVENANCE.json.

All expansion orders are fixed. No growing-order, optimal-truncation, or exponentially small sector theorem is claimed. Numerical constants and onsets for the asymptotic remainders are not supplied or certified here; the proof is compatible with making them effective. The small inverse uncertainty concerns a smooth center before floor/ceiling rounding. A finite nested-logarithm approximation cannot replace that exact-saddle center at the same precision. Likewise, E1 ~ -r/(12n) cannot replace exact E1 in the second-order remainder theorem.

## Files

- Report154.pdf: complete mathematical report
- Report154.tex: standalone editable LaTeX source, including bibliography
- companion/: exact integer/rational checks, safety regression tests, recorded results, and optional high-precision diagnostics
- SOURCE_PROVENANCE.json: public source URLs, inspected snapshot digests, roles, and limitations
- build_pdf.py: exclusive clean-directory PDF builder
- release_tools.py: descriptor-pinned local input/output helpers
- make_zip.py: frozen-allowlist and SHA-256 verified deterministic ZIP builder
- test_release.py: output-safety, manifest, and deterministic-archive regression tests
- release_checks.json: recorded normal and optimized release-test commands and results
- SHA256SUMS: hashes of all release members except itself

The archive omits private reviews, intermediate build directories, source journal PDFs, and earlier reports. No network access is used by the verification or build commands. No publication or repository update is performed.

## Exact checks

Python 3.11 or newer with its standard library is sufficient for the exact companion and release tests. See companion/README.md for the fixed finite coverage, exact commands, check counts, and recorded results. Tests run under both normal Python and python3 -O; correctness checks are not removable assert statements.

For release helper tests, from this directory:

    python3 -m unittest -v test_release
    python3 -O -m unittest -v test_release

Optional numerical diagnostics require exactly mpmath 1.3.0, listed in companion/requirements-numerical.txt. They use high-precision floating point and are not interval certificates, theorem proofs, or certified finite-input threshold decisions. No script installs software automatically.

## PDF reproduction

Requirements: a Linux/POSIX system with /proc/self/fd, pdftex/pdflatex, the TeX Live packages and fonts used by Report154.tex, and Python 3.11 or newer. The verified release toolchain is recorded in SOURCE_PROVENANCE.json.

From a clean extracted archive, choose an output directory that does not yet exist:

    python3 build_pdf.py --output-dir ./fresh-build
    cmp Report154.pdf fresh-build/Report154.pdf

The parent directory must already exist. Run builds only in a trusted parent directory that another process is not maliciously modifying at the same time. In particular, the mkdir-then-open directory creation step is not a security boundary against a same-user process replacing the new leaf directory before it is opened. The builder rejects existing destinations, static symlinked path components, and parent-traversal components; opened directory descriptors remain pinned. It creates isolated TeX configuration/cache directories, builds a local format, disables shell escape, fixes PDF metadata, and repeats LaTeX passes until cross-references stabilize. It rejects settled log warnings, overfull/underfull boxes, and missing characters. Fixed metadata and a fixed toolchain yield reproducible bytes; different TeX or font versions may change PDF bytes without changing the mathematics.

## ZIP reproduction

The distributed source ZIP contains every file needed to recreate itself, excluding the ZIP file. The manifest intentionally excludes itself and the ZIP to avoid circular hashes; make_zip.py adds the validated manifest as an archive member.

    sha256sum -c SHA256SUMS
    python3 make_zip.py --output ./Report154-rebuilt.zip
    cmp Report154_Source.zip Report154-rebuilt.zip

For the final comparison, keep the original downloaded ZIP alongside the extracted directory or adjust its path. Archive entries have a fixed order, a fixed 3 October 2026 timestamp, and fixed regular-file mode; storage is uncompressed to avoid compressor-version variation. The script rejects existing output paths and only packages its exact allowlist after verifying every listed digest. Extra local files are not included. The manifest is an integrity inventory, not a cryptographic signature or an authentication claim.

## Mathematical and computational boundaries

The exact programs verify algebraic identities and finite integer values; the analytic proof supplies the all-orders remainder. Optional residuals illustrate normalization, signs, and successive orders. They do not establish numerical error constants, monotonicity of the approximant at small real N, or that a chosen X is beyond the asymptotic onset. Equality-safe threshold statements are proved in the text and tested at finite exact examples only within the checks' documented scope.
