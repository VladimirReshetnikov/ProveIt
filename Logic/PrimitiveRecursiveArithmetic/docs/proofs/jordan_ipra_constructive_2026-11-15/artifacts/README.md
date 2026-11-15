# Executable finite kernel

Run from this package's root:

```sh
python3 artifacts/test_kernel.py
```

Only Python's standard library is required. Geometry uses exact
`fractions.Fraction` arithmetic throughout; there are no floating-point
tolerances. The output `test_results.json` includes returned paths, their exact
squared Euclidean clearance and infinity-norm clearance, finite search bounds, boundary-cycle lengths, and cyclic
sample degrees.

The kernel implements:

* signed rational ray-crossing index with half-open endpoint conventions;
* its orientation-independent mod-two parity, used in the main theorem;
* exact segment intersection, squared Euclidean distances, and rational
  infinity-norm distances (the flood-fill oracle uses the infinity norm);
* the rational affine honeycomb used in the article;
* finite reachability with an explicit vertex bound;
* degree-two boundary-cycle extraction;
* nearest-sample labels and the degree of their shorter cyclic walk.

The examples use simple rational polygons as exact distance oracles. This
checks the finite machinery and exercises the proof's connection and index
factorization mechanisms. It is **not** a substitute for the article's proof
for general curves and is **not** a formalized iPRA derivation. In particular,
the test code checks factorization on the listed probes; the theorem that it
holds under the quantitative hypotheses is a mathematical lemma in the article.

All searches are finite: a patch of radius M has (2M+1)^2 cells, flood fill
processes at most that many vertices, and boundary traversal uses at most the
number of separating edges. The Python source uses convenient standard-library
representations. The iPRA translation uses bounded integer and list codes;
there is no claim that Python itself is the trusted arithmetic proof checker.

## Reproducing the figure

With matplotlib installed, run:

```sh
python3 artifacts/make_figures.py
```

This reads the tested route from `test_results.json`, reconstructs the exact
square flood fill, verifies the recorded boundary-cycle length, and writes
`figures/finite_routes.pdf` and `figures/finite_routes.png`. The PDF is a vector
figure. Conversion to floating point is confined to drawing coordinates.
