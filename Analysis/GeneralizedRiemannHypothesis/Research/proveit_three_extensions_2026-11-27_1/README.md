# Three extensions of the ProveIt research program

**27 November 2026.** Source snapshot:
[cfab41369737c66ae520d179419509eb719367cd](https://github.com/VladimirReshetnikov/ProveIt/tree/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis).

Start with **research_report.pdf**. It contains a reading guide and all three complete papers. Each paper is also available separately with its LaTeX source.

## Main results

1. **Sharp Gram determinants with a growing number of zero minors.**
   For integral rank-two matrices with \(n\) indexed columns, if \(n=o(z)\) and \(z=o(n^2)\), the minima with at most \(z\), and with exactly \(z\), zero pair minors both satisfy
   \[
   E(n,z)\sim n^6/(729\Psi_*^2z^2).
   \]
   The positive constant \(\Psi_*\) is an explicit, rigorously attained one-variable maximum. The proof includes a construction meeting the exact integer zero count.

2. **Normal form for shortest positive filters.**
   At every strictly positive mirror configuration, the optimal width and measure vary analytically in centered polynomial coefficients, including through target collisions. In analytic normal coordinates, the width is exactly \(N\pi/\kappa+\|\eta\|^2\). An explicit positive graph-energy Hessian resolves the sign and degeneracy issue raised in the source. A cubic example has negative mixed curvature, and a two-mode corollary gives a quartic damping–frequency penalty.

3. **Two detection scales for finite-field bilinear observations.**
   The exact likelihood depends only on matrix rank, the number of zero rows, the number of zero columns, and the total number of zero entries. When the number of anchors is \(a=d-c\), dependence first becomes visible near \(m=a\), reaches a plateau, and has a second explicit Poisson transition near \(m=q^d\). A uniform Gaussian theorem covers the regime \(d-a\to\infty\).

These are unconditional mathematical results with self-contained written proofs. They do not depend on RH or GRH, do not establish a prominent classical conjecture, and have not been formalized in Lean. The new claims are distinguished from inherited mechanisms and classical background. Historical priority is qualified: the relevant source sections, related incoming reports, and a focused selection of primary literature were inspected, but this is not an exhaustive literature review.

## Contents

- **research_report.tex / research_report.pdf** — guide and complete collected papers.
- **papers/gram_determinants/** — full proof, exact rational certificate, weighted integer matrices, and four-square correction.
- **papers/positive_filters/** — full proof, symbolic integration, and 80-digit nonlinear moment checks.
- **papers/bilinear_detection/** — full proof, exhaustive finite counts, limiting-profile data, and vector/raster figures.
- **verification/** — a separately implemented exact conditional-count checker and a consolidated run record.
- **SOURCE_AUDIT.md** — precise relationship to the pinned repository and prior reports.
- **PROOF_REVIEW.md** — proof dependencies, checks, and remaining qualifications.
- **provenance/** — source hashes and a scoped bibliography.
- **build.py / verify_all.py / requirements.txt** — reproducibility.
- **SHA256SUMS** — hashes of the delivered contents, excluding this checksum file.

## Reproduce the calculations

Tested with Python 3.12.14, NumPy 2.3.5, SymPy 1.14.0, mpmath 1.3.0, and Matplotlib 3.10.8.

~~~sh
python3 -m pip install -r requirements.txt
python3 verify_all.py
~~~

The Gram checker uses only Python's standard library. The exact bilinear checker in its own paper folder also uses only the standard library. NumPy is required for the separate conditional-count implementation; SymPy and mpmath are required for the filter verification.

The programs write JSON results next to their sources. Re-running them may change incidental formatting or environment information, so the delivered checksum file describes the original delivered state.

The finite-field scripts test small **prime** fields. The written counting proof applies to all prime powers. Exhaustive enumeration and high-precision numerics check formulas and conventions; they do not replace the general proofs.

## Rebuild the PDFs

A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, microtype, geometry, hyperref, xurl, enumitem, graphicx, booktabs, and pdfpages is sufficient.

~~~sh
python3 build.py
~~~

To regenerate the scientific figure before compiling:

~~~sh
python3 build.py --figures
~~~

Each paper is compiled separately before the combined report. No network access or upstream Lean checkout is needed. The combined report preserves each paper's printed page numbers; its PDF bookmarks locate the three papers.

## Reading priorities

For the strongest new extremal asymptotic, begin with the Gram paper. For a direct answer to a stated Hessian question in the source, begin with the positive-filter paper. For an exact finite experiment and an explicit asymptotic phase diagram, begin with the bilinear-detection paper.

The global maximizer of the Gram constant has **not** been numerically certified; its approximate location is illustrative. The filter normal form requires strictly positive masses and is local for fixed degree. The detection theorem concerns the specified complete bipartite observation model; arbitrary overlapping-cycle graphs remain open.
