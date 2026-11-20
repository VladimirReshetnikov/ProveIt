Sharper bounds for convex covers of unit space curves
20 November 2026

Open space_worm.pdf for the proofs. The convention is a separate proper
rotation and translation for each rectifiable path of length one in R^3.
The smooth and rectifiable versions have the same minimum.

RESULT

The minimum is attained and lies strictly between 0.01942 and
0.052942305538. The upper construction is an explicit rational polytope.
Its volume is exactly

  13235576384310899273916967194112370723463873
  / 250000000000000000000000000000000000000000000.

These bounds tighten 0.018975 < V3 < 0.052956040 in the stronger linked
report. The exact minimum remains undetermined.

REPRODUCE THE TWO VOLUME BOUNDS

From the extracted directory, run

  python3 check.py

Use Python 3.8 or later with assertions enabled, and GCC or Clang with
C++17 and signed 128-bit integer support. CXX can name the compiler.
The verifier compiles to a temporary directory. No network connection,
numerical optimizer, SciPy, or graphics package is needed for these checks.

lower/check_planar.py proves the width and length of the 69-vertex planar
test path. lower/witness.hpp gives all 61 vertices of the spatial test path
in order. lower/check_witness.py proves its length and the two concentric
ball estimates. lower/check_rotations.cpp and lower/shadow_lp.hpp exhaust
a quaternion chart and prove an area lower bound uniform in all
orientations and translations. Figure generation uses draw_shadow.py.

upper/poses.json specifies the rigid placements. upper/check_adaptive.py
constructs the rational polytope, checks every proposed supporting facet
against all generators, proves facet completeness and computes its volume.
upper/adaptive_facets.json is a list of hints checked from scratch.
upper/cover.obj is the certified covering polytope in Wavefront format
with exact terminating-decimal coordinates and outward-oriented faces.
upper/export_cover.py reproduces it using standard Python.
upper/draw_adaptive.py re-creates the upper-bound illustration. Both
illustrations are supplied as PDFs. Only redrawing them requires NumPy,
SciPy and Matplotlib.

READ AND BUILD THE REPORT

space_worm.tex includes shadow.tex, prism.tex and cover.tex. With a normal
TeX Live installation, run twice

  pdflatex space_worm.tex

The one non-elementary input specific to the upper bound is Keller's
planar covering theorem. The report links the paper and the pinned
machine-checked theorem. upstream_keller/ contains its original upper proof
sources and all 50 compressed multiplier shards, under the upstream license.
The Git blob digests and upstream certificate manifest have been verified.
See upstream_keller/PROVENANCE.txt for the separate Lean kernel replay,
which uses the pinned Lean and mathlib dependencies. The three-dimensional
reduction is proved in the report. The lower estimate is independent of the
planar covering theorem and uses only the explicit witness checks.

The two baseline reports are cited in the bibliography with their
GitHub locations. The numerical searches that suggested the test curve
and pose table are unnecessary for reproducing the proof.
