# Shape, Divisibility, and Stein Geometry of the Fabius-Rvachev Law

This archive contains the complete source and rendered form of a 32-page A4 research report prepared on 2026-08-30. The report audits the LaTeX research corpus under `Analysis/FabiusFunction/docs` in the `VladimirReshetnikov/ProveIt` repository, removes directions already developed there, and presents a repository-distinct probability/shape program for the Fabius-Rvachev law. The current artifact uses the repository's canonical article preamble with Libertinus prose; all fonts are embedded and subset, and the regenerated vector plots use TrueType outlines rather than Type 3 fonts.

## Main proved-here results

The report develops complete proofs of the following results, subject to the imported facts and citations identified in the text:

1. Strict log-concavity of the Rvachev up-density on `(-1,1)`, resolving the binary endpoint left conjectural in the audited geometric-family treatment.
2. Strict log-concavity of the associated CDF and survival function, strict hazard and reverse-hazard monotonicity, strict monotone likelihood ratio, and strict log-convexity of the inverse-Fabius derivative.
3. A dyadic score/hazard identity and an induced refinement inequality.
4. Absence of identical convolution roots of every integer order `r >= 2`, despite the unequal infinite-convolution construction.
5. A canonical Stein-kernel calculus, including exact Fabius-tail and conditional-moment formulas, rational values, Bell-Bernoulli moment identities, a sharp weighted Poincare inequality, and a symmetric invariant diffusion.
6. A hidden Legendre equation in the complete mode jet of the diffusion eigenproblem, together with nonanalyticity and polynomial-eigenfunction obstructions.
7. Exact logarithmic-coordinate endpoint formulas and rigorous bounds leading to a Lambert-W-scale Stein asymptotic conjecture.

The report explicitly labels imported facts, proved-here statements, and conjectures. “Repository-distinct” is deliberately weaker than a claim of absolute priority in the global literature.

## Contents

- `fabius_rvachev_frontier_report.tex` — complete LaTeX source.
- `fabius_rvachev_frontier_report.pdf` — compiled 32-page A4 report.
- `rvachev_frontier_experiments.py` — fully commented numerical experiment and validation program.
- `numerical_output/` — four vector-PDF figures, pointwise and endpoint CSV tables, and global diagnostics.
- `requirements.txt` — Python dependencies.
- `Makefile` — one-command regeneration of figures and PDF.
- `SHA256SUMS.txt` — integrity hashes for the packaged files.

## Reproduce the numerical outputs

From the archive root:

```bash
python3 -m pip install -r requirements.txt
python3 rvachev_frontier_experiments.py --output-dir numerical_output
```

The defaults use 200001 grid points and 24 fixed-point iterations. The program checks, among other identities,

- total probability mass `= 1`,
- `up(0) = 1`,
- `up(1/2) = 1/2`,
- score at `1/2 = 4`,
- `tau(0) = 5/36`,
- `tau(1/2) = 1/12`,
- `E[tau(Z)] = Var(Z) = 1/9`.

The Stein kernel is evaluated by stable one-sided quadrature on the positive half-axis and then reflected using exact evenness. This avoids cancellation at the negative endpoint.

## Rebuild the PDF

A standard TeX Live installation with `pdflatex` and the packages named in the preamble is sufficient:

```bash
make all
```

Equivalently, after regenerating the numerical figures, run `pdflatex` three times on `fabius_rvachev_frontier_report.tex`.

## Audit scope

The duplication audit followed the recursive documentation tree, the archive provenance map, the paper directory, and the semi-formalized frontier manifest. Canonical and consolidated master sources were read directly and searched for candidate collisions. Historical sources identified by the repository as absorbed or superseded were checked through their controlling consolidated descendants rather than treated as independent current theorems. The report’s Appendix D records the corpus map used for the audit.
