# Farthest points on a rectangular N-box

Read **hyperbox_surface.pdf** for the constructive proofs, general coordinate algorithms, closed families, and Lean roadmap. The single TeX source uses the included figure **prism_figure.pdf**. All input lengths are strictly positive. The boundary includes the full interiors of facets.

## Run an example

For the box with sides 1, 1, 1, 5 the fixed-vertex maximum has squared length 802/25. The unrestricted squared diameter is 134 − 40√6, attained between opposite end facets. Run both computations from this directory.

~~~sh
python free_cad.py 1,1,1,5 --compare
python hyperbox.py vertex 1,1,1,5 --arrangement
~~~

The first command uses the proved prism formulas. The second independently enumerates fixed-vertex circumcenters and tests legal unfoldings.

| File | Inputs and outputs |
|---|---|
| **hyperbox.py** | Standard-library exact point distances and fixed-vertex maximizers for rational sides. All squared lengths and coordinates are fractions. The vertex-bits option reflects the origin into a prescribed corner. The arrangement option uses the general fixed-source algorithm. |
| **free_cad.py** | Exact unrestricted diameter and a maximizing pair for rational sides. Requires SymPy 1.14 or later. Recognized families use closed formulas. Other boxes use full projection and lifting, which can be prohibitively expensive. The raw option forces that calculation even for recognized families. |
| **certified_mesh.py** | Standard-library rational mesh bounds, a maximizing grid pair, an exact squared witness distance, and a rigorous enclosure of each continuum extremum. The mesh parameter m is the number of subdivisions per side. |
| **FreeExact.wl** | Alternative exact Wolfram Language solver for general positive real algebraic lengths. Uses polynomial crossing predicates and exact maximization. Instructions and tests are included. A Wolfram kernel was unavailable for execution. |
| **lean/** | Three typechecked Lean files, their reproduction instructions, and a compiler/axiom receipt. Two files construct explicit arithmetic derivations in ProveIt's Prf PRAAx. The report gives the remaining geometric formalization. |
| **checks.py**, **check_diameter.py** | Reproducible exact cross-checks. The latter also audits the 798 simple developments for the algebraic four-dimensional diametral pair. |
| **mesh_1115.json** | Example output of the coarser endpoint mesh calculation on the four-dimensional prism. |

Other calls, including a prescribed non-origin vertex and a point-to-point distance, are shown below.

~~~sh
python hyperbox.py vertex 3,1,2 --vertex-bits 1,0,1
python hyperbox.py point 1,1,1,5 --p 1/2,1/2,1/2,0 --q 1/2,1/2,1/2,5
python certified_mesh.py 1,1,1,5 --m 2
python checks.py
python check_diameter.py --cad
~~~

To rebuild the paper, run pdflatex twice on hyperbox_surface.tex. To regenerate its figure, run prism_figure.py in this directory with NumPy and Matplotlib installed.

For rational lengths a fixed-vertex farthest point has rational coordinates. A free pair may involve algebraic roots. For lengths given only by Cauchy approximations the report supplies a uniform value modulus and near-optimal endpoint coordinates, and proves the obstruction to uniform exact endpoint selection.
