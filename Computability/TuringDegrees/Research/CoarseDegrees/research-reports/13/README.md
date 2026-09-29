# Exact Ideals and Optimal Jumps in Coarse Description Classes

A 26-page research manuscript prepared for Vladimir Reshetnikov, September 2026.

## Read the article

- `article.pdf`: compiled manuscript.
- `article.tex`: complete editable LaTeX source, with embedded bibliography.
- `build.sh`: runs finite diagnostics and builds the PDF.
- `checks/finite_checks.py` and `checks/results.json`: executed finite diagnostics.
- `audit/PROOF_AUDIT.md`: mathematical scope and critical proof obligations.
- `audit/SOURCES.md`: repository snapshot, source identities, and literature record.
- `audit/validation.json`: build and inspection record.

## Principal mathematical claims

Theorem 5.1 is a layered-reservoir construction for a countable array. It gives
an exact common lower ideal with a prescribed oracle H, exact intersections
of overlapping finite joins, and a bound on the jump of the entire join:

    L(Z) intersect L(H) = I,       (Z join H)' =_T H'.

Theorem 6.2 and Corollary 6.3 prove that the possible coarse-description cores
are exactly the countable Turing ideals. This completes the explicit robust
column-profile proposal in target C4 of the inspected ProveIt plan.

Theorem 3.5 proves that the plan's precise guarded c.e. set X is uniformly
coarsely equivalent to R(TOT). Its description spectrum consists exactly of
degrees d with 0'' <= d'. This statement is about the specified guarded set,
not every complete c.e. set.

Theorem 7.1 constructs descriptions D_i of X forming minimal pairs with 0',
with Z the full countable join and

    D_i' =_T Z' =_T (Z join 0')' =_T 0''.

This resolves the prescribed-guarded-set component of C6, including its
residual first-jump question. The independent spectrum lower bound makes
the first-jump bound optimal.

## Scope and status

These are conventional proofs, not Lean/Rocq certificates or independently
refereed results. The guarded set, dyadic coding criterion, robust coding,
reservoir methods, and C4's proposed formula are attributed to their sources.
The manuscript does not claim that the classical exact-pair phenomenon or
the absence of least coarse representatives is new. Bibliographic priority
for the extensions is not established by this bounded source check.

The prescribed-generic portion of C6 and repository targets C2, C7, and C8
are not claimed solved. Ten further research questions appear in Section 10.

The Python tests concern finite identities and amalgamation only. They do not
implement a halting oracle, test infinite genericity, verify Turing-degree
assertions, or certify the infinite mathematical proofs.

## Rebuild

A standard TeX Live installation with pdfLaTeX, latexmk, newpx, AMS packages,
geometry, microtype, booktabs, tabularx, enumitem, titlesec, fancyhdr, xurl,
needspace, xcolor, and hyperref is sufficient. No external image assets or
bibliography processor are required; no font binaries are distributed.

Run:

    ./build.sh

Or separately:

    python3 checks/finite_checks.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The tests require Python 3.10 or newer and only the standard library. They
can be run from any working directory and write `checks/results.json`.

## Repository version

The source documents' blob identities were verified at commit
`6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0` of
`VladimirReshetnikov/ProveIt`. The inspected plan and synthesis were unchanged
between initial retrieval and this final pinned check. See `audit/SOURCES.md`.
No change was made to the user's repository.
