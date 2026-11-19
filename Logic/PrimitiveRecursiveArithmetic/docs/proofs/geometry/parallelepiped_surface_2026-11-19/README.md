# Farthest points and intrinsic diameter of a parallelepiped

Read **parallelepiped_surface.pdf** for the geometric formulas, exact worked examples, constructive proof and Lean formalization roadmap. **parallelepiped_surface.tex** is the full article source. Its one figure is **surface_geometry.pdf**.

## Give the input

Choose three independent outgoing edges from a reference vertex. In the input order \(g_{11},g_{22},g_{33},g_{12},g_{13},g_{23}\), the diagonal Gram entries are the squared lengths, and each other entry is the product of its two lengths and the cosine of their included angle. A point \((u_1,u_2,u_3)\) represents \(o+u_1e_1+u_2e_2+u_3e_3\), with one coordinate equal to 0 or 1. The specified starting vertex is given by its three bits. The article also gives a conversion from interior dihedral angles.

## Exact and certified calculators

| File | Inputs and outputs |
|---|---|
| fixed_exact.py | Python standard library. Gives every fixed-vertex maximizer and the exact squared eccentricity for rational Gram data whose initial charts and unfoldings use rational square roots. |
| mesh_bounds.py | Python standard library. Accepts every rational positive-definite Gram matrix. Gives a rigorous interval for each extremum, rational endpoint coordinates, a verified surface route, and a separate interval for its witness distance. Increase the two mesh sizes and the integer scale to reduce the error. |
| SkewExact.wl | Wolfram Language implementation of the exact fixed and free candidate algorithms for real algebraic Gram matrices. Returns a winning pair and its length. See SkewExact_README.md for calls, optional independent quantifier elimination and test instructions. A Wolfram kernel was unavailable here, so this implementation was reviewed without executing it. |

For the skew solid in the worked quartic example, run the commands below from the archive directory.

~~~sh
python fixed_exact.py --gram 1,1,4,0,80/401,0
python fixed_exact.py --gram 1,1,4,0,80/401,0 --vertex 0,1,1
python mesh_bounds.py --gram 1 1 4 0 80/401 0 --m 12 --n 6 --scale 65536
~~~

The farthest point from the origin is \((1281/1604,1247/1604,1)\), at distance \(\sqrt{27065/3208}\). One diametral pair is approximately \((0.369305,0.695365,0)\) and \((0.630695,0.304635,1)\), at distance \(3.02533804635\ldots\). Section 7 of the paper specifies the squared diameter by its irreducible quartic, isolating interval, exact endpoint polynomials and a rational certificate covering all competing points.

For equiangular unit rhombohedra, let \(h\) be the common cosine of the three edge angles at the specified origin. The fixed answer is \(\sqrt{5+4h}\) at \((1,1,1)\) throughout \(-1/2<h<1\). The unrestricted diameter is \(\sqrt{5+4h}\) for \(0\le h<1\) and \(\sqrt{5-4h^2}\) for \(-1/2<h\le0\), attained in the latter case at \((1,0,0),(0,1,1)\). The paper proves these formulas by explicit face paths.

## Reproduce the certificates

~~~sh
python antipodal_check.py
python rational_cover.py
python skew_global.py --algebra-only
python skew_global.py
~~~

The first command uses only the standard library. It checks all 28 words for opposite face centers and evaluates the eight vertex eccentricities. The next two use SymPy. They verify the global upper bound on 18 rational rectangles, the local derivative and gate signs, the quartic root, and the 28 developed lengths at the exhibited point. These two checks suffice for the unrestricted result. The final command repeats the coverage and sign checks in the independently implemented nonlinear arithmetic decision procedure from the system libz3 shared library. The JSON and text files record representative outputs.

The certified mesh example uses a different Gram matrix. Reproduce mesh_example.json using the following command.

~~~sh
python mesh_bounds.py --gram 4 3 2 1 0 1 --m 12 --n 6 --scale 65536
~~~

## Lean and the article

Using Lean 4.32.0, run the stand-alone arithmetic and face-word development with the following command.

~~~sh
lean SurfaceCore.lean
lean QuarticCertificate.lean
~~~

The second module kernel-checks the quartic coefficient reduction, modular arithmetic, and root-bracketing arithmetic. LEAN_CHECK.txt records the compiler and axiom audit. The final article section gives explicit first-order iPRA endpoints for exact algebraic codes, a finite-precision scheme for named real inputs, and a path to a complete Lean implementation. The complete geometric theorem and its object-theory proof objects remain unformalized.

To rebuild the PDF, run pdflatex twice in the archive directory. The supplied figure is sufficient. Running make_figure.py regenerates it with NumPy and Matplotlib. The colors and level sets are illustrative. The marked fixed-vertex maximizer uses exact rational coordinates.

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error parallelepiped_surface.tex
pdflatex -interaction=nonstopmode -halt-on-error parallelepiped_surface.tex
~~~
