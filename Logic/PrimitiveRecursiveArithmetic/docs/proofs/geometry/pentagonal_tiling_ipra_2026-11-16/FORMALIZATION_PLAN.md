# Lean and object-iPRA formalization plan

## 1. Target and non-target

The target is a collection of explicit closed derivations in the checked
ProveIt calculus:

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] pentagonAngleSumFm
([] : List (Fm PTm 0)) ⊢[PRAAx] regularPentagonObstructionFm
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType1Fm
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType3Fm
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType15Fm
([] : List (Fm PTm 0)) ⊢[PRAAx] dodecahedronCertificateFm
```

The target is *not* merely a Mathlib theorem about real sets.  Host Lean is
used to organize encodings and to prove compiler correctness; the mathematical
endpoints are `Prf PRAAx` values.

The supplied `PentagonalTilingBlueprint.lean` contains completed small
host-level lemmas and interfaces, with no `sorry`, `admit`, or new axiom.  It
was not compiled in this environment because neither `lean` nor `lake` is
installed.

## 2. Reused checked ProveIt layers

Repository baseline: `VladimirReshetnikov/ProveIt`, main commit
`d91fc1854ebe1f4be70f5c690b6180aca57cc937` observed on 2026-11-16.

Use the following existing modules rather than rebuilding arithmetic:

- `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, `PRA.qfInd`;
- `IPRADerivations.Core.Basic`, `Semiring`: natural arithmetic and induction;
- `Core.Integers`: signed differences and ring identities;
- `Core.Order`: decidable equality and order;
- `Core.Pairing`: finite tuples and list codes;
- `Core.Search`: bounded minimization;
- `Core.LinearAlgebra`: finite vectors, matrices, determinants;
- `Core.Tactic`: universal closures and `ipra_ring`.

Research packets under `docs/proofs` are useful design references only; no
unverified result from them is taken as an axiom.

## 3. Module graph

### `PentagonalTilings/Encoding.lean`

Define canonical codes for:

1. signed integers as pairs of naturals;
2. reduced rationals `(z,q)` with `q>0` (reduction is optional for equality if
   cross multiplication is used);
3. quadratic numbers `a+b*sqrt(d)` as four rational coefficients plus `d`;
4. points, five-vertex polygons, finite lists, and lattice pairs;
5. certificates and their bounded lengths.

Every decoder is total.  Malformed data is rejected by a Boolean predicate;
there are no partial functions or choice operators in the object theory.

### `PentagonalTilings/Quadratic.lean`

Define primitive-recursive addition, multiplication, conjugation, norm and
exact sign.  For `x=a+b*sqrt(d)`, signs reduce to rational signs and one square
comparison when `a` and `b` have opposite signs.  Prove:

```lean
signQ_sound : ValidQ x -> signQ x = sign(emb x)
addQ_sound  : ...
mulQ_sound  : ...
```

The object-language proof avoids `Real.sqrt`: it proves the ordered-field
rules directly from the code invariant `r^2=d` and the chosen positive branch.
For the fixed fields `d=3,5,57`, positivity and nonsquareness are finite
arithmetic lemmas.

Nested Type 14 radicals are represented by a tower of quadratic extensions.
Use the same sign routine recursively, or replace each radical by its minimal
polynomial plus a rational isolating interval and use signed subresultant/Sturm
sequences.

### `PentagonalTilings/Geometry.lean`

Define exact point operations, dot product, determinant/cross product,
squared distance, doubled shoelace area, segment membership, and cyclic
congruence by the complete squared-distance matrix.  Define convexity by the
common sign of five turns.

Prove finite lemmas:

- cyclic distance matrices characterize the shipped congruences;
- a nonzero common turn sign gives a convex simple pentagon;
- the separating-axis test is sound for two convex polygons;
- shoelace area is additive under a certified planar subdivision.

### `PentagonalTilings/Lattice.lean`

For a nondegenerate lattice `(L1,L2)`, define dual coordinates by Cramer's
rule.  Prove the finite-shift lemma:

> If two cell polygons overlap after translation by `m L1+n L2`, then the
> integer `m` and `n` lie in intervals determined by the global dual-coordinate
> widths of the cell.

For all shipped periodic cells the computed ceiling is 2, so the checker only
needs the 25 shifts in `[-2,2]^2`.

### `PentagonalTilings/PeriodicCertificate.lean`

Define the Boolean verifier with these clauses:

1. well-formed nonzero lattice;
2. five vertices per tile;
3. common cyclic squared-distance matrix;
4. convexity where required;
5. total tile area equals absolute lattice determinant;
6. exact separating-axis witness for every bounded relevant translate;
7. split every edge at every translated certificate vertex lying on it;
8. pair every directed subedge with its reverse modulo an integral lattice
   vector.

The JSON file `verification/periodic_witnesses.json` contains the concrete
pairing/search trace and an explicit source edge, normal axis, and projection
order for every separation instance.  The object checker may either replay those witnesses or
perform bounded search itself.

### `PentagonalTilings/ArrangementSoundness.lean`

This is the central generic theorem.  Build the finite arrangement of all cell
edges and fundamental-parallelogram edges.  Triangulate every arrangement face
by a canonical fan.  Membership in each tile is constant on the relative
interior of a face.  Prove constructively:

- separation gives coverage multiplicity at most one;
- the shoelace sum is the sum of areas of covered arrangement triangles;
- equality with the cell area leaves no positive-area uncovered triangle;
- boundary pairing excludes a lower-dimensional hole and glues the quotient
  to the torus.

Conclude that all lattice translates form a tiling.  This proof is finite and
uses only quantifier-free induction over the encoded arrangement.

### `PentagonalTilings/Type1.lean`

Formalize two theorems:

1. the general Type 1 construction: half-turn a pentagon about the midpoint of
   the side joining the `B` and `C` vertices; `B+C=pi` merges the exposed edge
   pairs and produces a centrally symmetric hexagon;
2. every centrally symmetric hexagon with edge vectors
   `u,v,w,-u,-v,-w` tiles by translations generated by `u+v` and `v+w`.

Then replay the rational two-tile certificate and the regular-hexagon
bisection.

### `PentagonalTilings/Type3.lean`

Encode the regular hexagon over `Q(sqrt(3))`, its center, and three alternating
edge midpoints.  Prove the three pentagons are congruent and satisfy

```text
A=C=D=120 degrees,
a=b=sqrt(3)/2,
c=e=1/2,
d=1=c+e.
```

Replay the periodic certificate.

### `PentagonalTilings/Type14.lean`

Let `s=(sqrt(57)-3)/8`.  Prove

```text
4s^2+3s-3=0,
cos C = 1-2s^2 = (3sqrt(57)-17)/16,
b^2/a^2 = (11sqrt(57)-25)/8.
```

Encode the ordered quartic field `Q(sqrt(57),t)` with
`t^2=(6sqrt(57)-2)/64`, the six local polygons, their full cyclic distance
matrices, convex turn signs, shared-vertex graph, and all fifteen exact
separating axes.  Completion to a periodic certificate requires adding exact
lattice vectors and boundary pairings.

### `PentagonalTilings/Type15.lean`

Encode the twelve points `a[0]...a[11]` over `Q(sqrt(3))`, the three affine
transforms `b,c,d`, the twelve pentagons, and lattice vectors

```text
L1=(12+9sqrt(3),3),
L2=(1+sqrt(3),3+sqrt(3)).
```

Prove the five side squares and five dot/cross angle signatures.  Evaluate the
periodic checker to `1`, then use its soundness theorem.

### `PentagonalTilings/Nonconvex.lean`

For `n=3,4,6`, encode vertices `V_i`, inner vertices `W_i`, center `O`, and

```text
T_i=[V_i,V_(i+1),W_(i+1),O,W_i].
```

Verify rotational congruence, a negative turn at `O`, reverse pairing of every
internal edge, the outer boundary, absence of forbidden edge crossings, and
area equality.  Combine with explicit standard tilings of the triangle,
square and regular hexagon.

### `PentagonalTilings/Dodecahedron.lean`

Use the twenty `Q(sqrt(5))` vertices in the certificate.  Verify:

- common radius squared 3;
- exactly 30 minimal-distance edges, degree 3;
- exactly 12 canonical five-cycles;
- each is planar and regular;
- each face plane supports all remaining vertices on one strict side;
- every edge occurs in two faces and `20-30+12=2`.

Conclude that the convex hull boundary is the regular `{5,3}` spherical tiling.

### `PentagonalTilings/Hyperbolic.lean`

First internalize the pure arithmetic equivalence
`1/2+1/5+1/n<1 <-> n>=4`.  For the geometric existence theorem, use Coxeter
triangles.  Two viable constructive implementations are:

1. fixed-`n` certificates using algebraic reflection matrices and an exact
   fundamental polygon; or
2. a uniform primitive-recursive generator using cyclotomic polynomials,
   Sturm isolation for `cos(pi/n)`, and Coxeter normal forms.

Ten reflected triangles form one regular pentagon; `n` pentagons meet at a
vertex.  The ideal case is a separate code with a boundary root rather than a
natural order.

### `PentagonalTilings/Dual.lean`

On a finite periodic quotient, dualize vertices and faces.  Prove valence five
produces pentagons, and group equivariance transports vertex orbits to face
orbits.  For a regular `p`-gon, prove the angle between outward normals of two
adjacent edges is `2pi/p`; this yields the three displayed uniform-dual angle
lists.

### `PentagonalTilings/RaoImport.lean`

Do not restate the classification as an axiom.  Import a complete trace with:

- the finite list of 371 angle-condition representatives;
- exact linear-programming feasibility/infeasibility certificates;
- every backtracking node, local transition and terminal contradiction;
- the map from surviving leaves to one of the fifteen families.

Use rational Farkas multipliers for linear infeasibility.  For algebraic signs,
use isolating intervals.  Verify the trace with a primitive-recursive checker,
then prove its checker sound.  Only then state the closed iPRA classification
formula.  The present archive does not contain that trace.

## 4. Object-language compilation pattern

For each host primitive-recursive function `f`, define `toPR f` or an explicit
`PR k` symbol, prove its recursion equations, and expose a `PTm` application.
For a concrete certificate numeral `c`:

```lean
def verifyPeriodicPR : PR 1 := ...
def type15Code : PTm 0 := numeral certificateCode

def verifyType15Fm : Fm PTm 0 :=
  app verifyPeriodicPR (fun _ => type15Code) ≐ succ zero

theorem verifyType15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType15Fm := by
  -- unfold bounded loops with their defining equations;
  -- use qf induction for list/shift iteration;
  -- close polynomial identities with `ipra_ring`.
```

Then instantiate the generic object-language soundness theorem to derive the
coded tiling statement.  The certificate theorem and its geometric soundness
must remain separate, so that a small evaluator proof cannot conceal a gap in
coverage.

## 5. Suggested completion order

1. `Quadratic`, `Geometry`, `Lattice`.
2. Concrete Type 1 and Type 3 evaluator theorems.
3. Generic periodic checker and finite-shift theorem.
4. Arrangement soundness.
5. Type 15 evaluator and soundness instantiation.
6. Nonconvex subdivisions and dodecahedron.
7. Type 14 extension tower.
8. Coxeter/hyperbolic layer.
9. Rao trace import, only after a complete externally reproducible trace is
   available.

Each milestone should add an entry to `Checks/Axioms.lean` and reject any
`sorry`, `admit`, local axiom, or semantic theorem that bypasses `PRAAx`.
