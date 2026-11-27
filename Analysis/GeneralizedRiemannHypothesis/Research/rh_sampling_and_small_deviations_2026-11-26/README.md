# RH research: irregular sampling and small deviations

Prepared for Vladimir Reshetnikov, 26 November 2026.

## Read first

**cubic_sampling.pdf** is the main paper. It analyzes the supplied formal
RH/Dirichlet-GRH repository and proves an irregular sampling theorem
for smoothed sums with nonnegative coefficients. A gap of logarithmic
length h has a weighted integrated cost of order h cubed. The paper
includes a matching construction with positive bounded coefficients,
zero observations on a set of natural density one, and explicit
nonreal Mellin poles with no real poles.

**xi_small_deviations.pdf** is a second, independent research note. Using
RH as the zero-location input, it derives an explicit small-deviation
law for the random sum of independent exponential variables divided
by the squares of the positive zeta-zero ordinates. It gives exact
Lambert-W prefactors, a first relative correction, and a real
primitive Dirichlet-character/gamma-shape extension.

Both complete LaTeX sources are included. Each paper distinguishes
its established inputs from its proposed new contribution.

## Main conclusions and limits

1. The discrete cubic sampling budget and the explicit density-one
   obstruction are proved in full. The sharpness class is bounded
   positive real coefficients. It is not a construction of new primes
   or a counterexample for the von Mangoldt function.
2. The fourth-power sampling scale and Landau's underlying one-sided
   principle are prior work and are credited, especially Setiawan's
   November 25, 2026 preprint. The proposed new part is the irregular
   integrated budget with its matching obstruction.
3. The reciprocal-xi probability representation and saddlepoint
   method are prior work. The second note credits the especially
   close predecessor by Suvrit Sra, version 3 of November 2, 2026.
   Its proposed contribution is the explicit tail formula and
   extension, with constants and the first correction.
4. Targeted searches did not locate the exact resulting statements.
   This is not a certification of historical priority or peer review.
5. No new Lean proof is claimed. The main paper gives a formalization
   plan; the selected upstream sources were read, not rebuilt.
   RH/GRH acceptance is supported by the current primary verification
   statement. The repository's scope is Dirichlet GRH, not arbitrary
   automorphic or Artin GRH.
6. All sampling conditions are asymptotic conditions on an infinite
   sequence. The papers do not claim a finite numerical RH certificate.

## Reproduce

From the directory containing this README:

    python3 code/verify_cubic_energy.py
    python3 code/check_xi_small_deviations.py
    tectonic cubic_sampling.tex
    tectonic xi_small_deviations.tex

A normal TeX Live installation can instead compile each source with
pdflatex twice. Bibliographies are embedded, so no BibTeX run is required.
Python dependencies are listed in requirements.txt.

The cubic script reproduces symbolic identities, a finite coefficient
check, and the two-panel figure. It writes its JSON to checks/ and its
figure to figures/.

The xi script performs floating-point Fourier quadrature at 60 decimal
digits. It truncates a standardized Fourier integral at frequency 20.
Its values are illustrative numerical checks, not certified interval
bounds, and are not used to prove the theorem.

## Contents

- cubic_sampling.tex / cubic_sampling.pdf: main paper and full proof.
- xi_small_deviations.tex / xi_small_deviations.pdf: second paper.
- code/: reproducible symbolic and numerical scripts.
- checks/: generated check outputs and review notes.
- figures/: main paper's scientific figure in PDF and PNG.
- sources/REPOSITORY_AUDIT.md: scope, interfaces, commit, and build limits.
- sources/repository_metadata.json: inspected source identifiers.
- sources/snapshot_sha256.json: upstream snapshot hashes.
- sources/grh-lean-selected/: selected unmodified upstream sources.
- sources/novelty_search.json: bounded literature-search record.
- MANIFEST.sha256: integrity hashes for the deliverable files.

The upstream source snapshot is a small review selection, not a complete
buildable copy of the formal proof. Its original Apache-2.0 license,
NOTICE, and attribution files are retained.
