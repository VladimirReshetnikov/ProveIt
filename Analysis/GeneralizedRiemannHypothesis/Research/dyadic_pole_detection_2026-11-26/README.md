# Sharp constants for dyadic pole detection

Research report prepared for Vladimir Reshetnikov, 26 November 2026.

## Start here

Read `report.pdf`; its editable and complete source is `report.tex`.
The mathematical proofs are in the report. The accompanying computations check
exact algebraic certificates and illustrate the extremal geometry.

For even n >= 2, with L = 2^(n-1), let r in (1/2,1) solve r + r^L = 1. The main result is

    min over complex z of max_(0 <= j < n) |1 + z^(2^j)| = sqrt(1-r+r^2).

The only minimizers are r*exp(plus or minus 2*pi*i/3). The report also proves an
explicit stability estimate, the separate exact three-filter quartic theorem,
and sharp recovery bounds for residues of shifted Mellin transforms.

The n=2 case is known (1956 competition, published in 1968). The larger even
family and three-filter refinements are proposed original extensions. Targeted
searches found no prior statements; worldwide priority has not been established.

## Connection to the requested sources

The inspected repository is lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207. Its analytic endpoint turns a one-sided
bound for a smoothed prime remainder into nonvanishing by detecting poles.
This note solves the cancellation problem when that remainder is observed
through positive sums at doubled shifts. The new extremal theorems are
unconditional and independent of RH or GRH.

The repository exports RH and Dirichlet GRH. We inspected its source and did
not perform a new full build or independent-kernel replay. The new results are
not claimed to be formally verified in Lean. See `formalization_plan.md`.

## Reproduce

Python 3.10 or later and the packages in `requirements.txt` are required.
A LaTeX installation with pdfLaTeX and the standard packages named in report.tex
is required for the PDF.

    python3 code/verify_results.py
    python3 code/make_figures.py
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

No network access is used by these scripts.

## Contents

- report.tex, report.pdf: complete paper and editable source.
- code/verify_results.py: exact identities, exact quartic root isolation,
  high-precision constants, and finite numerical sanity checks.
- code/make_figures.py: reproduces the static research figure.
- data/constants.csv: high-precision constants and noise factors.
- data/verification.json: execution record with clear scope of each check.
- figures/: vector and raster versions of the paper's figure.
- proof-review.txt: independent mathematical review and verification limits.
- formalization_plan.md: explicit Lean proof obligations; not a completed proof.
- research/source_audit.md: pinned source map and method analysis.
- research/novelty_review.md: prior art and search log.
- SHA256SUMS.txt: hashes of the final archive contents other than this hash file.

## Interpretation limits

The exact gains apply to the prescribed doubling pattern. Three unrestricted
exponents {1,2,3} already achieve gain 1, so no optimality across all delay sets
is claimed. Residue error bounds do not by themselves control errors in finite
real-variable samples. Odd n >= 5 is left unresolved by this note.
