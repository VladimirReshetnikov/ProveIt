# Shortest surface paths on the unit oloid

Open **oloid_distances.pdf** for the point coordinates, all 45 distances, the crossing types, and the proof. The first two pages contain the results. The surface is the boundary of the convex hull of the two disks. Lengths are Euclidean arc lengths of curves constrained to that boundary.

## Verify

From the extracted directory, run these commands with Python 3.10 or later.

    python3 code/verify.py
    python3 code/straight_routes.py
    python3 code/tables.py

The first command replays all 154 reduced crossing patterns and the extra two-contact localization certificate. The second verifies finite-side intersections for 25 elementary distance formulas and a feasible upper bound in the close P6–P9 comparison. The third checks that both ends of each distance enclosure round to the same displayed value and regenerates the two TeX tables. These checks use the Python standard library.

## Numerical records

- **data/distances.csv** gives all 45 lower/upper enclosures, winning reduced words, dyadic upper-path parameters, and certified lower bounds for competing words. The latter fields are empty for a direct path.
- **data/trees.json** supplies binary subdivisions for the independent checker. Its special contact tree bounds both circular-edge parameters for P4 to P10. The paper and Lean roadmap explain the leaf inequalities.
- **code/geometry.py** contains the exact rational choices of points and the outward integer interval evaluator for the planar development.
- **code/certify.py** regenerates the distance enclosures. **code/check_routes.py** is a separate floating-point comparison using SciPy. Its output for all 154 patterns is in **data/route_comparison.csv**.

To reproduce the searches, run

    python3 code/certify.py --compare-routes --output data/distances.csv
    python3 code/verify.py --build
    python3 code/verify.py
    python3 code/check_routes.py --output data/route_comparison.csv --certificates data/distances.csv

Indices in the report and CSV are one-based. In every row the word and its parameters are ordered from the first point to the second. Circular parameters are fractions of a 2π/3 arc, measured from the corresponding disk's outermost axial point. Straight-side parameters run upward in the paper's planar V coordinate. Equation (6) gives each gate parametrization.

## Paper and Lean sources

The TeX source is **oloid_distances.tex**. The generated tables and vector figures are included. To rebuild with TeX Live, run pdflatex on oloid_distances.tex twice from this directory. **code/figures.py** can redraw the vector illustrations with NumPy and Matplotlib.

**lean/SurfaceDistance.lean** defines the continuous path problem, the unfolded route costs, all ten points, and the final enclosure statements. **lean/FORMALIZATION.md** gives the remaining geometry and certificate-soundness lemmas. The supplied Lean scripts have not been compiled or kernel-checked.
