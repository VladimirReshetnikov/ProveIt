# Theta-Resolved Optimal Truncation of q-Multinomial Transseries

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read first

`article.pdf` is the compiled article. `article.tex` is the editable source.
The PDF includes full conventional proofs, a source boundary, a claim ledger,
10 proposed further research questions, and references. This is an unrefereed
research development; global publication priority and Lean verification are
not claimed.

## Principal results

- An all-order critical-mesh expansion of the exact positive q-multinomial
  remainder, retaining both lattice phase and order tilt.
- Actual global optimization over Bernoulli orders, with a phase-dependent
  square-root-sized order shift, an explicit bounded correction, and a
  corrected leading minimum error.
- A fixed nonresonant mesh theorem with an exact arithmetic action greater
  than the first unresolved pole and an integer-order periodic prefactor.
- A rigorous mesoscopic overlap between the theta and two-point descriptions.
- An exact pole-resolved hierarchy; resolving L entire pole components moves
  the first unresolved critical-mesh action to 2*pi*(L+1)*a_min*x.
- Finite positive-sum truncation bounds and residual-to-inverse enclosures.

The article's domains of uniformity are part of the statements: fixed positive
ray, fixed pole count, bounded scaled mesh for the theta theorem; 0<h<beta and
nonresonance for the fixed-mesh theorem. A separate theorem states the precise
mesoscopic overlap. This is not a general theorem about all resurgent series.

## Contents

- article.tex / article.pdf — source and compiled article.
- code/verify.py — exact symbolic identities and high-precision diagnostics.
- code/plots.py — double-precision plots, not a proof tool.
- code/endpoint_check.py — independent 150–400 digit endpoint subtraction checks.
- data/*.csv — detailed numerical comparisons.
- data/verification_results.json — executed-test receipt.
- data/*_table.tex — generated tables used in the article.
- figures/*.pdf — two vector figures used in the article.
- SOURCE_AUDIT.md — source and mathematical-claim boundaries.
- requirements.txt — Python dependencies.
- build.sh — compile the shipped source and assets with pdfLaTeX.

## Rebuild

The shipped figures and tables suffice for rebuilding the PDF:

    ./build.sh

To regenerate the diagnostics and figures:

    python -m pip install -r requirements.txt
    python code/verify.py
    python code/plots.py
    python code/endpoint_check.py
    ./build.sh

The verification script performs no network calls. It uses 75 decimal digits
and directly evaluates positive, logarithmically scaled remainder sums. The
analytic tail bounds printed by the script do NOT include floating-point
roundoff. They are not interval certificates. In exact outward-rounded
arithmetic, the article's neighboring-ratio test and finite bounds would give
certified global minima when the intervals separate.

The two PNG/PDF rendering workflows used during document quality control are
not dependencies of the article. No repository files were modified.
