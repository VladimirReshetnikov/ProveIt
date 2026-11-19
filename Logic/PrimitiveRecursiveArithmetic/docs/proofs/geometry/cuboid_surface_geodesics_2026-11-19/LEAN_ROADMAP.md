# Lean formalization roadmap

## Status

`FiniteAlgebra.lean` contains concrete algebraic identities and no `sorry`.
`FormalizationBlueprint.lean` is deliberately a specification skeleton; every
`sorry` marks a genuine remaining proof obligation. Neither file was compiled
in the artifact-generation environment because `lean` and `lake` were not
installed.

The recommended target is the ProveIt root toolchain pinned by the repository
(Lean/Mathlib 4.32.0 in the inspected revision). The relevant existing
namespace is `LeanProofs.ConciseIPRA`. The repository's triangle-geometry
packet also identifies reusable coordinate-algebra patterns and the important
separation between host-Lean identities and internal iPRA derivations.

## Completion order

1. **Metric layer.** Replace the list-based partition placeholder by a clean
   `Fin (n+1)` partition, prove refinement monotonicity, and establish the
   standard properties of `curveLength`, `SurfacePath`, and `intrinsicDist`.
   Alternatively, adapt Mathlib's rectifiable-curve API if its version-pinned
   interface is preferable.

2. **Six-face combinatorics.** Define exact face adjacency and a reduced face
   chain. Prove that a shortest path on a convex polyhedral surface is a finite
   polygonal line, crosses a face in a segment, and can be unfolded to a
   Euclidean segment. For the cuboid, enumerate the reduced chains by
   `native_decide` after proving the enumerator complete.

3. **Two finite unfolding theorems.** Prove:

   - a top-face point from a fixed vertex is the minimum of four source-image
     distances;
   - a normalized antipodal pair is the minimum of five distances `d1`-`d5`.

   These are the only geometric classification bottlenecks. Once proved, the
   rest is semialgebraic optimization.

4. **Fixed-vertex optimization.** Build the four planar Voronoi cells. Prove
   they are compact convex polygons and that a convex quadratic reaches its
   maximum at a polygon vertex. Enumerate boundary vertices and the four
   triple circumcenters. `FiniteAlgebra.lean` supplies the equidistance,
   omitted-source, and sign-factorization identities.

5. **Central symmetry.** Formalize the theorem that every diametral pair on a
   centrally symmetric convex surface is exchanged by the central involution.
   This is the one topological ingredient. A pragmatic first milestone can
   assume it as a named theorem, prove all cuboid-specific consequences, and
   later discharge it from a polyhedral specialization of the published
   result.

6. **Diameter optimization.** On
   `Omega=[0,A/2]x[0,B/2]`, prove the five-unfolding minimum formula. The ME
   criterion follows from three factorizations and interval arithmetic. For
   the two non-ME regimes:

   - `Q <= 0`: show the maximum occurs at `(A/2,tau)` by monotonicity of
     `g1,g3,g4` and strict convexity of `h(t)`;
   - `Q > 0`: show the hyperbolas `q1=0` and `q2=0` have one intersection,
     prove `d4,d5` are nonbinding there, and use the same convexity argument.

7. **The scalar radical root.** Prove the root function continuous and strictly
   increasing on `ell >= max (B+C) L0`. Derive its zero from the triple equality.
   This yields both uniqueness and a certified bisection implementation.

8. **Coordinate transport.** Package axis permutations and reflections so the
   sorted-box theorems immediately apply to arbitrary `(a,b,c)` and any of the
   eight selected vertices.

## Optional iPRA endpoint

For an internal intuitionistic-PRA result, do not formalize arbitrary real
curves. Compile the finite cuboid theorem instead:

- rational/dyadic side lengths and candidate coordinates;
- a finite face-chain checker and squared-length comparisons;
- bounded square-root brackets;
- monotone bisection for the unique interior root;
- quantifier-free case predicates with explicit separation data near regime
  boundaries.

The reusable ProveIt components are `Syntax.lean`, `Deduction.lean`, `PR.lean`,
`BiInterpretation.lean`, and `NativeBiInterpretation.lean`, together with the
bounded square-root scan described in the triangle-formulas packet. Host Lean
`ring` proofs do not by themselves produce derivations in `Prf PRAAx`; each
fixed arithmetic checker must be compiled to primitive-recursive syntax and
its soundness replayed in the object theory.
