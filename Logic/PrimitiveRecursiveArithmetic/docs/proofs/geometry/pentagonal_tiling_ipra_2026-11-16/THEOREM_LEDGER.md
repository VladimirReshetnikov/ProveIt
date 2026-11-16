# Theorem ledger: pentagonal tilings in intuitionistic PRA

Snapshot date: 2026-11-16.  Article target: the English Wikipedia page
`Pentagonal tiling` as read on that date.

## Status codes

- **H**: a complete human-readable constructive proof is given in the report.
- **X**: an exact executable finite certificate is shipped and passes the
  reference checker.  Floating point is not used for the decisive equalities
  or signs.
- **Lh**: a complete host-Lean arithmetic lemma is included in
  `lean/PentagonalTilingBlueprint.lean`.
- **Lo**: an explicit dependency-ordered route to a closed object-language
  derivation `Prf PRAAx` is given, but that derivation has not yet been built.
- **C**: proved conditionally from a finite certificate or from a named source
  theorem whose complete certificate is not shipped here.
- **O**: deliberately left open in this delivery; no proof is claimed.

The Python checker is evidence for a finite arithmetical certificate, not a
substitute for a `Prf PRAAx` derivation.  The report explains how every **X**
item becomes an iPRA theorem once the generic checker and its soundness theorem
are internalized.

## Ledger

| ID | Article statement or mathematical refinement | Status | Location / boundary |
|---|---|---:|---|
| P0 | A pentagonal tiling is a tiling whose tiles are pentagons. | H, Lo | Finite-coded definitions in Sections 2-3. |
| P1 | The Euclidean plane cannot be tiled by regular pentagons. | H, Lh, Lo | Strengthened to non-edge-to-edge tilings: `3k+5l=10` has no solution with `k>=1`. |
| P2 | A convex pentagon has angle sum 540 degrees. | H, Lo | Constructive fan triangulation; rational-turn encoding. |
| P3 | The listed angle equations for Types 1-15, together with the pentagon angle sum where needed, imply the derived identities in the report. | H, X, Lo | Exact rational linear-combination witnesses for every target are in Section 6 and `verification/results.json`; this does not by itself prove geometric realizability. |
| P4 | Every Type 1 pentagon tiles periodically. | H, Lo | Half-turn pair gives a centrally symmetric hexagon; parallelohexagon translation theorem. |
| P5 | A concrete rational Type 1 pentagon tiles periodically. | H, X, Lo | Two-tile cell, exact coordinates, five edge-pair witnesses. |
| P6 | A regular hexagon can be bisected into two congruent Type 1 pentagons. | H, X, Lo | Exact `Q(sqrt(3))` cell. |
| P7 | A regular hexagon can be trisected into three congruent Type 3 pentagons. | H, X, Lo | Exact `Q(sqrt(3))` cell; all Type 3 side and angle relations checked. |
| P8 | Convex hexagons can also be subdivided into four Type 4 and nine Type 3 pentagons. | O | The article diagrams were not converted into exact certificates here. |
| P9 | The Type 14 tile has the stated rigid nested-radical proportions and a six-tile local patch. | H, X, Lo | Exact ordered-quartic algebra, full distance-matrix congruence, convexity, all 15 pairwise separation checks, and connected placement; no complete lattice cell claimed. |
| P10 | The Type 15 pentagon has angles 150,60,135,105,90 and sides `a=c=e`, `b=2a`, `d=a sqrt(2+sqrt(3))`. | H, X, Lo | Exact dot/cross and side-square identities over `Q(sqrt(3))`. |
| P11 | Type 15 has a periodic twelve-pentagon primitive cell. | H, X, Lo | Exact cell area, 32 reverse boundary pairs, and 1,794 separating-axis instances. Minimality of the cell is not proved. |
| P12 | Each of the other named convex families (2,4-13) actually tiles. | C, Lo | The generic finite checker/soundness theorem applies once an exact diagram certificate is imported; no full coordinate set is shipped. |
| P13 | There are exactly fifteen convex monohedral pentagon families. | O | Rao's 371-case computer-assisted classification trace is not imported. A concrete import plan is given. |
| P14 | There are exactly eight edge-to-edge convex families. | O | Bagina/Sugimoto classification not reconstructed. |
| P15 | There are exactly twenty-four isohedral pentagonal tiling types, nine edge-to-edge. | O | Grünbaum-Shephard/Schattschneider classification not reconstructed. |
| P16 | There is no upper bound on `k` for certain `k`-isohedral Type 1/2 tilings. | O | Requires an explicit parametric family not developed here. |
| P17 | Rao's classification implies that no convex polygon tiles only aperiodically. | C | Immediate once the full classification and one periodic witness per family are imported. |
| P18 | Monohedral pentagonal tilings with every rotational order `n>2` exist. | O | Klaassen's construction is not internalized. |
| D1 | The dual of an edge-to-edge valence-five tiling has pentagonal faces. | H, Lo | Finite quotient dual construction. |
| D2 | Isogonality of the primal implies isohedrality of the dual; `k` vertex orbits give `k` face orbits. | H, Lo | Equivariance and orbit transport. |
| D3 | The three dual uniform pentagons have angle lists `(120,120,120,90,90)`, `(120,120,90,120,90)`, `(120,120,120,120,60)`. | H, Lh, Lo | At the center of a regular `p`-gon the dual angle is `360/p`. |
| D4 | The displayed 2-,3-,4-,5-uniform examples have pentagonal duals. | C | Follows from their finite valence-five primal incidence data, not shipped. |
| N1 | Two sphinx tiles form a parallelogram and the sphinx has periodic and substitution tilings. | O | Not reconstructed; the report states only a finite-certificate route. |
| N2 | An equilateral triangle divides into three congruent nonconvex pentagons. | H, X, Lo | Exact `Q(sqrt(3))` construction and finite planar-complex checks. |
| N3 | A square divides into four congruent nonconvex pentagons. | H, X, Lo | Exact rational construction and finite planar-complex checks. |
| N4 | A regular hexagon divides into six congruent nonconvex pentagons. | H, X, Lo | Exact `Q(sqrt(3))` construction and finite planar-complex checks. |
| N5 | The three units in N2-N4 tile the plane. | H, Lo | The triangle, square and regular hexagon have explicit translation/reflection tilings. |
| S1 | The regular dodecahedron is a spherical `{5,3}` pentagonal tiling. | H, X, Lh, Lo | Exact `Q(sqrt(5))` coordinates: 20 vertices, 30 edges, 12 supporting regular pentagonal faces. |
| S2 | The degenerate `{5,2}` tiling consists of two hemispheres with a five-edge equator. | H, Lo | Finite cell count `V=5,E=5,F=2`. |
| H1 | Regular hyperbolic `{5,n}` tilings exist for every integer `n>=4`; the pentagon angle is `2pi/n`. | H, Lh, Lo | Coxeter triangle `(pi/2,pi/5,pi/n)` and `10<3n iff n>=4`. Full uniform object-code is planned via algebraic root isolation. |
| H2 | `{5,4}` uses right-angled pentagons. | H, Lh | Substitute `n=4`. |
| H3 | `{5,infinity}` is the ideal limiting tiling with zero vertex angle. | H (limit statement), Lo | Finite orders are exact; the ideal case is represented separately, not by a natural `n`. |
| H4 | Infinitely many irregular hyperbolic dual pentagonal tilings `V3.3.p.3.q` exist. | O | Requires a separate uniform hyperbolic dual catalogue. |
| H5 | The polygonal binary pentagonal tiling is nonperiodic in two dimensions. | O | The group-theoretic nonperiodicity argument is not reconstructed. |

## Machine-checked finite results in this archive

The executable companion establishes, with exact rational/quadratic arithmetic:

- four periodic cells (2, 2, 3, and 12 pentagons);
- all reverse edge-pair witnesses after subdivision at T-junctions;
- exact area equality with the lattice covolume;
- a dual-lattice bound proving that only shifts with both coordinates in
  `[-2,2]` can overlap;
- every required convex separating-axis witness;
- Type 14 nested-radical identities, full congruence, convexity, connectedness, and all fifteen pairwise exact separation checks;
- nonconvex triangle/square/hexagon subdivisions;
- the dodecahedral coordinate and incidence certificate;
- the fifteen angle-ledger identities; and
- the hyperbolic order inequality through a general arithmetic equivalence.

See `verification/results.json`, `verification/periodic_witnesses.json`, and
`code/verify_pentagonal_tilings.py`.
