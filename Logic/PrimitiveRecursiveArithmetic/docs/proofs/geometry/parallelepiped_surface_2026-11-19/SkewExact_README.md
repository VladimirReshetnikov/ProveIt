# Exact Wolfram Language calculator

Load the package with `Get["SkewExact.wl"]`. Supply a symmetric positive-definite
3 by 3 Gram matrix with exact real algebraic entries. For angles, use their
exact algebraic cosines. Points are triples in edge coefficients, so the
Cartesian point corresponding to `{x,y,z}` is `x a + y b + z c`. Each
returned association contains `"Point"`, `"OtherPoint"`, `"SquaredDistance"`
and `"Distance"`. Invalid inputs give `$Failed`.

```wl
g = (IdentityMatrix[3] + 31 ConstantArray[1, {3, 3}])/32;
SurfaceDistance[g, {0, 0, 0}, {1, 1, 1}]
VertexMaximum[g, {0, 0, 0}]
SurfaceDiameter[g]
```

The report proves the squared answer is 71/8 for each call in this example.
`VertexMaximum[g]` defaults to the origin. In degenerate optimization cases
different maximizing coordinates can have the same length.

For the vertex problem the calculator uses a direct chord on incident faces
and exactly ten words per opposite face. For the diameter it uses 28 words
on each of three faces. It rigidly develops their hinges,
and tests gate intersections in order, allowing common endpoints,
collinearity and zero segments. For an individual pair of algebraic endpoints
it intersects the closed parameter intervals directly. For the symbolic
optimization it uses a polynomial test. Every gate supplies linear inequalities
`A + B t >= 0` on its crossing time. A zero coefficient requires `A >= 0`.
Each lower bound at gate i must be at most each upper bound at any gate
j at or after i. These tests exactly characterize the existence of ordered
crossing times. Imposing 0 at the start and 1 at the end bounds all the times.

On each endpoint face the code first checks the four corners, the isolated
edge intersections of equal squared lengths, and the isolated interior
intersections of two equalities for three squared lengths. For the fixed
vertex these are intersections with bisectors and circumcenters. Duplicate
polynomials are discarded only during candidate generation. The report proves completeness of the candidate list. An optional independent
cross-check is enabled by `VertexMaximum[g, v, True]` or
`SurfaceDiameter[g, True]`. It uses real quantifier elimination to test
whether any point on a nontrivial closed face improves the candidate.
If certification does not return False, an exact semialgebraic Maximize
computes the optimum and a witness, and the gate evaluator checks the
witness again. If Solve returns an unresolved candidate system, the program
automatically invokes this independent route. Special algebraic coincidences
therefore do not require a genericity assumption. Exact optimization can be
very expensive, especially for high-degree inputs. Commercial CAS primitives
are implementations of real-algebraic operations, not a proof kernel for iPRA.

No Wolfram kernel was available when preparing this package. The Wolfram
source and its regression script are unexecuted. To run the regression checks
in a Wolfram installation:

```sh
wolframscript -file SkewExactTests.wls
wolframscript -file SkewExactTests.wls --extrema
```

The second command adds full extrema checks for a skew rhombohedron and a box.
