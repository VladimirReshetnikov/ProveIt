# Three extensions of the ProveIt methods

**Prepared 27 November 2026 for Vladimir Reshetnikov with ChatGPT.**

Start with **research_report.pdf**. Its complete LaTeX source is
**research_report.tex**, with five source fragments in **sections/**.

## Results

1. **Four wide arithmetic frequencies.** An exact certified analytic
   characterization of the maximum zero-free interval for
   ±{N,(m+1)N,(2m+1)N,(3m+1)N}, for every N ≥ 1 and integer m ≥ 2.
   For odd m there is a unique eight-atom annihilating probability measure
   on the critical arc, and the supremum is not attained even on an open
   zero-free interval. This resolves an infinite four-frequency subfamily
   of Kozma–Oravecz Question 1. The general question remains open here.

2. **Parity-dependent Ehrhart collisions.** For the symmetric edge polytope
   of a complete graph with a matching removed, the specified local
   collision windows have relative parameter widths (log d)^−2 in even
   dimension and (log d)^−2/3 in odd dimension. The paper gives all
   constants, quadratic and cubic normal forms, exact nearby double-root
   parameters, and the effect of integer rounding. These are local
   fixed-index results, not a global first-collision theorem.

3. **Minimal-counter spectral recovery.** Microscopic histograms of a fixed
   family of d primitive Dirichlet zero spectra give a uniform positive
   matrix of order T log T. Continuous Poisson intensity mixtures can
   therefore be estimated at the optimal squared-error rate
   min{1,1/(t T log T)} from exactly d independent aggregated count
   channels; d−1 suffice when the total intensity is known. Fewer fixed
   ordinary count channels cannot identify the corresponding interior
   parameter family. Growing bin widths can destroy the leading
   T log T information in all balanced directions, but this is not a
   claim that all smaller-order information disappears.

The three main results are unconditional. Dirichlet GRH is used only in
the application identifying the ordinate-built processes with the
repository's Li-coefficient semigroups.

## Build

A standard LaTeX installation with AMS packages, Latin Modern, microtype,
geometry, graphicx, booktabs, enumitem, fancyhdr, and hyperref suffices.

Run from this directory:

    ./build.sh

Equivalently, run pdflatex on research_report.tex twice. No BibTeX step is
needed; the bibliography is included in the main source.

## Verify

Run:

    ./verify.sh

The continuum certificate takes approximately three minutes on the
development machine. Do not use Python -O or disable assertions.
The three spectral verification commands and the finite mixture checks
use only Python's standard library. The Ehrhart exact checks require
SymPy and SciPy; optional high-precision illustrations require mpmath.
The complete optional dependency list is in requirements.txt.

The supplied exact certificates were replayed from this packaged copy:

| Verification | Result |
|---|---|
| Continuum spectral certificate | PASS: 1,127 cells, 121,990 positivity boxes |
| Spectral point/derivative enclosures | PASS |
| Independent m=3 Chebyshev certificate | PASS: 3,308 positivity boxes |
| Exact Ehrhart identities | PASS: 172 checks |
| Exact rational finite frames | PASS: 400 cases |
| Exact rational counter compression | PASS: 60 cases |

The continuum witness proves assertions for **every real parameter in
[0,1/3]**, not just a finite sample. The maximum contraction bound is
0.7136501831153487. Replay uses integer interval arithmetic on a 10^−24
grid with proved Taylor remainder bounds. SciPy is used only in optional
proposal generation, never in replay.

The independent m=3 certificate uses integer Chebyshev polynomials in a
different coordinate. It does not use trigonometric evaluation or the
continuum witness.

The finite Ehrhart and mixture checks validate the identities described
in the paper. They are not substitutes for the analytic asymptotic
arguments. High-precision Ehrhart collision values are illustrations,
not interval certificates.

## Archive map

- research_report.pdf — complete paper.
- research_report.tex and sections/ — complete editable LaTeX.
- checks/spectral/ — exact interval checker, rational witnesses,
  point checker, independent polynomial checker, illustration data.
- checks/ehrhart/ — symbolic identities, direct lattice counts,
  numerical and 80-digit collision illustrations.
- checks/mixtures/ — exact rational tests of estimator and compression
  identities.
- figures/ — the four-frequency figure in PDF, SVG, and PNG.
- provenance/ — source audit, pinned repository trees, and retrieved
  source hash report.
- validation/ — fresh continuum log, exact Ehrhart replay result,
  and verification summary.
- SHA256SUMS — checksums of the deliverable files.

The optional plot script writes its generated figure beside the script.
The delivered versions are collected in figures/. The component READMEs
document the individual commands and scope.

## Source and novelty boundary

The repository snapshot is commit
42efb893353a150857f5c8e2f9e7732d0d46f15f.
The comparison covers the current merged article and all 26 current
incoming archives, with detailed review of the relevant arguments.
The new results extend the current three-frequency theorem, the
strict first-order Ehrhart thresholds, and the existing binary
T log T Hellinger estimate. Those prior results are explicitly credited.

The upstream RH/Dirichlet-GRH source statements were inspected but the
vendored Lean development was not rebuilt. No new Lean formalization is
included. The gap theorem has a rigorous computational certificate and
an analytic reduction, with Python and the checker as part of its
trusted computational base.

The general Kozma–Oravecz wide-progression question and the all-width
complete-bipartite canonical-line question are not solved in this
packet. A targeted literature search did not locate the exact new
extensions, but exhaustive publication priority has not been established.
