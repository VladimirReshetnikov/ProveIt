# Build and verification record

Date: 27 November 2026.

- Both complete papers were compiled with pdfLaTeX, with resolved cross-references and no overfull boxes.
- `hidden_symplectic_forms.pdf`: 10 pages. `spectral_skewness.pdf`: 9 pages.
- All pages were rendered to images and visually inspected. The recovery paper's final bibliography was adjusted to avoid an orphan reference page.
- The four verification programs were run successfully on the final packaged code. See `data/verification_summary.json` and the corresponding logs.
- The recovery counts and finite probability bounds use exact integer/rational arithmetic.
- The spectral identities include symbolic statements for arbitrary N and exact finite checks for N=3,...,40.
- The 27 independent filter moment solves use 100-digit arithmetic. They are numerical corroboration, not interval or formal proof certificates.
- A separate mathematical audit of both proofs found no gap; see `PROOF_REVIEW.md`. This is an internal proof review, not external journal peer review.
- No Lean formalization of the new results was compiled. `FORMALIZATION.md` describes a possible development.

Environment used: Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, Matplotlib 3.10.8, pdfTeX/TeX Live 2025. Standard LaTeX packages are listed in the paper preambles. The local TeX installation needed a task-specific format configuration; the distributed Makefile uses a normal configured pdfLaTeX installation and does not depend on that local repair.

The delivered JSON files are the computation outputs. The PDFs contain the proofs. `CHECKSUMS.sha256` records the bytes distributed in the ZIP; rerunning a program or rebuilding a PDF can legitimately change a file's checksum, including due to metadata or timing.
