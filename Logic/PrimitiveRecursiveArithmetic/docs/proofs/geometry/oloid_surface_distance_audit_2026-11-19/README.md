# Intrinsic distances on the unit oloid

Read **oloid_audit.pdf**. Pages 1–3 give the ten original points, all 45 distances and the elementary expressions. The report also gives isolated scalar equations for 19 distances, a two-equation system for P4–P10 and a constructive arithmetic treatment of shortest surface paths. **data/refined_distances.csv** records a width-10^-50 enclosure and correctly rounded 40-place result for each pair. **data/contacts.json** gives rational near-minimizers for the twenty curved words with certified contact error below 4×10^-34.

## Reproduce the numerical proof

Run from the extracted directory with Python 3.10 or later, without optimization flags.

~~~sh
python3 code/check_all.py
~~~

This verifies the printed input points, all original admissible crossing words and alternate-route lower bounds, finite-side reflection intersections, unique nonlinear contacts and their isolating intervals, and the exact endpoint for the near-tied P6–P9 competitor. It independently regenerates the 45 refined intervals into a temporary file, compares them byte for byte with the supplied CSV, and checks the original printed table. All of these checks use only the standard library.

- **code/verify.py**, **data/distances.csv**, **data/trees.json** and **code/geometry.py** reproduce the original global lower/upper certificates.
- **code/verify_roots.py** and **data/root_trees.json** localize every curved minimizing contact and check positive definite Hessians. **code/precise_distances.py** checks gradient residuals with a separate interval evaluator.
- **code/symbolic.py** evaluates the elementary distance formulas and the exact near-tie gap. **code/close_competitor.py** verifies B-endpoint optimality. **code/report_tables.py** regenerates the new printed constants and distances.
- **code/find_contacts.py** optionally regenerates the Newton guesses using mpmath. **code/check_routes.py** optionally repeats a floating-point optimization using NumPy and SciPy. **data/route_comparison.csv** records this numerical cross-check. Neither solver is a premise of the certificate.
- **code/close_figure.py** regenerates the near-tie diagram with NumPy and Matplotlib. The two other vector figures come from the supplied distance archive.

## Lean and iPRA

**lean/README.md** gives the toolchain, pinned ProveIt revision, imports, and reproduction commands. **lean/IntegerReplay** contains the working kernel replay of 219 concrete integer certificate assertions. **lean/DecimalTable.lean** checks decimal rounding and enclosure arithmetic. **lean/ObjectIdentities.lean** and **lean/ObjectMesh.lean** contain object-language iPRA derivations. The closing section of the paper states the hypotheses and remaining proofs for the geometric and arithmetic layers.

## Rebuild the report

All figures and generated table inputs are included.

~~~sh
pdflatex -halt-on-error oloid_audit.tex
pdflatex -halt-on-error oloid_audit.tex
~~~

**oloid_audit.tex** is the main file and inputs **roots.tex**, **moduli.tex**, **constructive.tex**, **extra_lean.tex**, and the table fragments under **data**. Gate letters A, B denote curved seams, and L, R denote straight symmetry rulings. Words are read from the smaller point index to the larger. A direct word is the empty word.
