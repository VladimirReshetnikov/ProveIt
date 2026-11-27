ROBUST SPECTRAL IDENTIFICATION OF DIRICHLET CHARACTERS
Prepared for Vladimir Reshetnikov, 26 November 2026
====================================================

Main deliverable
----------------
report.pdf is the complete research report.
report.tex, angular.tex, and numerics.tex are its LaTeX sources.

Main theorem
------------
For primitive Dirichlet characters with conductors at most Q, including
arbitrary complex orders and the primitive principal character, a common
height H_Q = O(log^2(2Q) log log(3Q)) suffices for robust identification.
For every H >= H_Q, two distinct characters' signed zero multisets through
height H have clipped partial-matching distance at least c H/log(2Q).

The distance charges one for every unmatched occurrence (insertion or
deletion) and min(1, absolute displacement) for each matched pair. It works
with unequal list lengths, repeated zeros, missing data, and spurious data.
Every observation with combined corruption cost less than half the stated
separation has at most one compatible character.

The report gives completely explicit, intentionally conservative parameters,
a full proof, and a finite decoder using arithmetic prime values.

New content and prior work
--------------------------
The closest inspected predecessor is the ProveIt packet
Analysis/GeneralizedRiemannHypothesis/docs/incoming/quadratic_spectra.zip.
It already contains the B-spline decoder and high-cutoff sinc-squared
refinement for quadratic characters. Those ingredients are credited.

The present result removes any bound on character order, retains the complex
orientation, and treats partial matching with insertions and deletions.
The angular prime lemma supplies a uniform phase gap, avoiding the shrinking
separation of high-order roots of unity. The combined theorem was not found
in the inspected corpus or targeted primary-literature searches. Historical
priority is not certified by an exhaustive search or outside peer review.

Verification status
-------------------
The theorem has a complete human-readable proof, reviewed separately during
preparation. It is not a new Lean-kernel-checked theorem. The upstream RH and
Dirichlet-GRH theorem is the formal mathematical input; this session did not
rebuild the full upstream library.

The numerical conductor-5 example is explicitly exploratory. All detected
roots have small high-precision residuals, but the sign-change scan does not
certify completeness, simplicity, multiplicities, or GRH. The example's
height 40 is below the conservative universal cutoff in the theorem.

Reproduction
------------
Requires Python 3.11 or newer.
Python packages used: mpmath, numpy, scipy, matplotlib (see requirements.txt).
With a standard TeX Live/MiKTeX installation containing the listed packages:

  bash build.sh

This checks the constants, regenerates the illustration from the saved root
data, verifies the saved root residuals, and compiles the LaTeX report.

To recompute the root scan from scratch:

  python3 demo/complex_spectra_demo.py --height 40 --output demo
  python3 demo/verify_saved_data.py

To check the parameters alone:

  python3 code/verify_constants.py

The numerical scripts require no network access. Standard LaTeX compilation
requires the local packages named in the report preamble.

Contents
--------
report.tex / report.pdf   Full theorem, proof, analysis, and references.
angular.tex              Self-contained order-uniform angular-prime proof.
numerics.tex             Numerical example and verification scope.
code/verify_constants.py High-precision checks and exact B-spline constants.
data/constants.json      Recorded results of those checks.
demo/                    Reproducible complex-character example and figures.
evidence/                Source inventory, provenance, and proof audit notes.
formalization_plan.txt   Interfaces and proof obligations for future Lean work.
build.sh                 Standard rebuild sequence.
SHA256SUMS.txt           SHA-256 digest of every other file in the package.

Source snapshots
----------------
lsernau/grh-lean:
  72fead102f663d5c7a407964a13dc0cf9d977207
VladimirReshetnikov/ProveIt:
  4d7990202f9f106b2ffe8c209f073ad01d5e1987

No repository files were changed or pushed as part of this deliverable.
