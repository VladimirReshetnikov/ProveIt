# Intrinsic diameters of four regular solids

Open **platonic_surface.pdf** for the results, proofs, coordinates, and constructive interpretation. All edge lengths are one. Distances and coordinates scale linearly with the edge length.

| Solid | Unique farthest point from a vertex V | Fixed-vertex and free diameter | Unordered maximizing pairs |
|---|---|---|---|
| Tetrahedron | Center of the opposite face, −V/3 | 2/√3 | 4 |
| Octahedron | Opposite vertex, −V | √3 | 3 |
| Icosahedron | Opposite vertex, −V | √7 | 6 |
| Dodecahedron | Opposite vertex, −V | √((17+7√5)/2) | 10 |

## Reproducing the work

From this directory, make pdf rebuilds the report with pdfLaTeX. Its section sources and three PDF figures are supplied. Run make check to replay the five exact Python checks with the standard library. Python should run with assertions enabled. The make figures command rebuilds the illustrations using Matplotlib. Floating coordinates in those programs are used only for drawing.

The exact dodecahedral computations check the spatial model, all 50 reduced face strips for the lower bound, the hinge crossings and corner gaps in the global upper bound, and a separate Lipschitz certificate glued across 30 edges. The icosahedral computation checks both comparison strips and the lower-bound calibration.

## Lean

The eight Lean files were compiled with Lean 4.32.0. The geometric reduction, path sampling theorem, metric completion, and assembly of the four full object-language theorems are written out in the report, together with their remaining Lean implementation dependencies.

Four files use core Lean. The other four construct object-language derivations in ProveIt's first-order intuitionistic primitive recursive arithmetic. They cover tetrahedral lattice and Voronoi inequalities, octahedral and icosahedral strip minima for arbitrary weights, the dodecahedral weighted gap, and the cyclotomic norm identities. File names, theorem names and their roles appear in the report and source comments.

Use the pinned ProveIt revision below. In that checkout, with its Lean toolchain, first build the providers.

    lake build IPRADerivations.Probability.Variance IPRADerivations.Probability.FiniteLaws

Then, in the extracted archive, run the following with Lean and Lake 4.32.0 on PATH.

    make lean PROVEIT=/absolute/path/to/ProveIt

The script writes its compiled objects into a temporary directory. Results of the completed Python and Lean runs are in verification/. The pin is 09fe17194da14cdd100947737952e44100bb71b8.

[ProveIt iPRA sources at the verified revision](https://github.com/VladimirReshetnikov/ProveIt/tree/09fe17194da14cdd100947737952e44100bb71b8/Logic/PrimitiveRecursiveArithmetic)
