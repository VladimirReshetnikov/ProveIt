# Euclidean Three-Space over the Surreal Numbers

**Coordinate geometry, spherical trigonometry, and the rotation group SO(3,No)**
Merged research report, 22 September 2026, from two manuscripts written
independently on the same day: 04 (the base, Part I) and 09 (Part II).
Prepared for Vladimir Reshetnikov.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 71 pages
README.md     this guide
code/
  04-three-space-verify_identities.py   source 04 checks (19 groups)
  09-so3-verify.py                      source 09 checks (24 checks)
data/
  04-three-space-requirements.txt, 04-three-space-verification.txt
  09-so3-requirements.txt, 09-so3-verification.txt
```

Every label in `article.tex` carries the prefix `e3:`. Material from source
09 carries the sub-prefix `e3:so:`. The report is new, so no earlier `e3:`
label existed. All 135 labels of the placed source 04 text are kept, with the
prefix added. Of source 09's 107 labels, 93 are kept. The other 14 were
nine section labels of source 09 sections that are no longer printed on their
own, and five labels of equations or a theorem now printed once under a source
04 or merge label. No label of this report is
cited in the [formalization ledger](../../FORMALIZATION.md), and none has a
Lean mapping.

## Two sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **04** (base) | *Analytic Geometry and Trigonometry in Surreal Three-Space: finite angles, arbitrary scales, spherical duality, solid angles, rotations, and curvature* (34 pages) | `d22a5b35d5b3` | Section 2 and all of Part I (Sections 3–15); Sections 28.1 and 28.3; the first proof of Theorem 2.2. Files prefixed `04-three-space-`. |
| **09** | *Rotations of Surreal Three-Space: Algebra, Spin, Infinitesimal Structure, and Topology* (31 pages, 19 sections, 26 numbered statements) | `dcf86662b574` | All of Part II (Sections 16–27). In Part I it adds Proposition 2.1 (localization), the three-part normal-form decomposition, the hat matrix and identities (3.4)–(3.6), Proposition 5.2, the algebraic-angle form of Theorem 5.3, and Theorem 5.6. It also contributes Sections 28.2 and 28.4. Files prefixed `09-so3-`. |

The merge was written at `50cb709`, after both manuscripts were placed in
`5fe7f8d`. The manuscripts themselves, their PDFs, their READMEs and source
09's checksum list are not shipped. The code and data files are byte-identical
to the delivered ones.

**Why one report.** Both manuscripts develop the finite algebra of spatial
rotations. Otherwise they are complementary. Source 04 is a geometry of points,
lines, spheres and spherical triangles that uses rotations as one tool. Source
09 is a structure theory of the rotation group. Source 04 is the base: it is the
wider development and fixes the scalar conventions.

**Printed once** (Section 1.1 lists the choices):

- the finite phase theorem, Theorem 2.2, with source 04's proof and source 09's
  logarithmic proof as a marked second route;
- the classification of distance-preserving maps, Theorem 5.1;
- the axis theorem and Rodrigues formula, Theorem 5.3;
- finite axis–angle representatives, Theorem 5.4;
- the Hamilton product and quaternion rotation formula, (5.6)–(5.7);
- the rational Cayley chart, Theorem 5.6; source 04's vector formula (5.15)
  is the same map;
- the standard part, valuation, strong summability and positive-support
  lemma, all in Section 2;
- the symmetric spectral theorem over a real closed field, in Section 4.3, to
  which Lemma 20.1 now refers.

**Cited, not reproved.** The two-to-one spin map `Sp(1,F) → SO(3,F)`
(Theorem 5.5) is `squat:thm:rotations`, Theorem 4.4 of the
[surquaternion report](../../surquaternions/surquaternions/). Both sources
reprove it by that theorem's first surjectivity route. Only source 09's
explicit lift formula (5.9) is printed.

**Renamed** (always in favour of one meaning per symbol; the table is in
Section 1.4):

- source 04's workspace `K` becomes `F`, because `K` is source 09's
  infinitesimal kernel, and its unit circle `U(K)` becomes `T(F)`;
- the Rodrigues matrix `R(n;c,s)` (source 09) and `Q_{n,θ}` (source 04)
  become `Rot(n;c,s)`, because `R` is a sphere radius;
- source 04's rotation matrices `Q` become `A`, and its isometry `F` becomes
  `Φ`;
- source 09's real rotations `R_0, R, S` in the split extension become
  `A_0, B, B'`;
- source 09's global rotation exponential and its differential, `E` and
  `J(w)`, become `𝓔` and `𝓙(w)`, because `E` is the spherical excess;
- source 09's dual number `τ` becomes `κ`, because `τ` is an oriented
  determinant;
- source 04's gnomonic and stereographic charts `G`, `H` become `Gn`, `St`;
- source 09's `sin_0, cos_0, cis_0` become `sin, cos, cis`;
- source 04's `[x]_×` becomes the hat notation;
- the word *fine* now always means the full surreal topology, as in source
  09, the surquaternion report, foundations and `docs/NOTATION.md`, while
  source 04's use of it for one workspace's order topology is written
  *intrinsic*.

## What the report claims

Numbers refer to the built `article.pdf`. Part I works in a set-sized
real-closed Hahn workspace `F = R((t^Γ)) ⊂ No`, or in any real closed field for
the finite algebra. Part II works over a real closed field `F`, adding
`F ⊇ R` where standard parts are used.

**Scalars (Section 2).** Every set-sized family of surreals lies in a
set-sized real closed subfield (Proposition 2.1). The finite phase map induces
`O/2πZ ≅ T(F)`, with canonical representatives in `[0,2π)` and `(−π,π]`
(Theorem 2.2). Inverse tangent, `atan2`, `acos` and `asin` are defined for all
surreal inputs and return finite angles.

**Part I, coordinate geometry (source 04).**

- Vector identities, Cauchy–Schwarz and the triangle inequality with its
  equality case (Theorem 3.1); the Cayley–Menger volume formula; projection and
  least squares without completeness.
- Closest points and distance of nonparallel lines (Theorem 4.1); sphere and
  line intersections; principal axes of quadrics without compactness.
- Isometries of `F^3` are affine and onto (Theorem 5.1); axis and Rodrigues
  (Theorem 5.3); every rotation has a finite axis–angle representation, with
  θ in `[0,π]` unique for `A ≠ I` (Theorem 5.4); the matrix Cayley chart with
  its composition law (Theorem 5.6); screw motions.
- The angular triangle inequality and chord bounds on `S²(F)` (Theorem 7.1);
  gnomonic and stereographic charts.
- Spherical sine and cosine laws (Theorem 8.2) and polar duality (Theorem 8.3).
- The side-data existence criterion, including the perimeter condition, and
  reconstruction (Theorem 9.1). The exact SSA alternatives have a continuous
  exceptional family at `a = b = α = π/2` (Proposition 9.2).
- Spherical Ceva (Theorem 10.1); circumcenter, incenter and bisector formulas.
- The branch-correct spherical excess `E = 2 atan2(d, M)` (Theorem 11.1);
  L'Huilier; a finitely additive area on geodesic polygons (Theorem 11.3);
  a branch-complete solid-angle formula.
- The sphere connection and curvature `1/R²`, geodesics, the exponential map,
  and explicit parallel transport. Holonomy equals the spherical excess, by a
  quaternion identity (Theorem 12.1). A normal-coordinate curvature correction
  holds.
- The valuation laws, and a relative gnomonic area estimate
  `|E/A_flat − 1| ≤ 4ρ²` that holds for arbitrarily thin triangles
  (Theorem 13.1). Conditioning estimates (Proposition 13.3).
- Worked configurations at several surreal scales (Section 14), and the
  counterexamples of Section 15.

**Part II, the rotation group (source 09).**

- Reflections, transitivity and the stabilizer `T_n ≅ SO(2,F)`; Euler
  coordinates; the quaternion matrix, `SU(2)` form and `P³(F)` model; a
  quaternion extraction algorithm without small divisors (Section 16).
- Rotations are conjugate exactly when their traces agree. The centralizer of
  a half-turn is `O(2,F)`, and commuting nonidentity rotations share an axis
  or are perpendicular half-turns (Theorem 17.1, Corollary 17.2).
- Standard part gives a split extension `G(F) ≅ K_F ⋊ SO(3,R)` (Theorem 18.1).
  The Cayley chart identifies `K_F` with `(m_F³, ⋆)` (Proposition 18.2).
- `K_F` has no torsion (Lemma 19.1) and is uniquely divisible
  (Theorem 19.2). Each element is a single commutator of elements of `K_F`, so
  `K_F` is perfect (Theorem 19.3); Bays–Peterzil is the published precedent.
- Every finite subgroup is conjugate to its standard part by an element of
  `K_F` (Theorem 20.2, via Lemma 20.1).
- `so(3,F)` is the cross-product algebra and is simple, and the spin
  differential has factor two (Proposition 21.1).
- Strong exponential and logarithm give inverse bijections
  `so(3,m) ↔ K` with the BCH law (Lemma 22.1, Theorem 22.2). The logarithm of
  a Cayley rotation is given exactly (Proposition 22.3).
- Valuation layers are `(R³,+)`, and their commutator is the cross product
  (Theorem 23.1). Finite jets are nilpotent while the whole kernel is perfect.
- Finite angles versus the Ehrlich–Kaplan phase, which has period class `2πOz`
  (Section 24).
- The global rotation exponential has complete fibers (Theorem 25.1). Its
  differential is exact, with `det = 4 Sin²(r/2)/r²`, critical radii exactly
  `(2πOz)_{>0}`, and rank one there (Theorem 25.2).
- Set-sized subsets of `G(No)` are closed and discrete in the fine topology
  (Theorem 26.1). The intrinsic topology is totally separated and not locally
  compact, and the standard-part quotient topology is discrete. In the
  semialgebraic category `π_1 = Z/2` and the spin map is the simply connected
  double cover (Theorem 26.2).
- Worked examples (Section 27): a tiny rotation with a macroscopic
  displacement (Proposition 27.1), a near-half-turn, and a nonreal octahedral
  group.

## What the report does not claim

Section 29 lists every limitation of the sources: 18 for source 04 (G1–G18),
22 for source 09 (S1–S22), and 4 for the merge (M1–M4). The main ones follow.

- The report is AI-assisted and has not been refereed. No statement has a
  Lean formalization, and the Lean layers of Sections 28.3–28.4 are proposals.
  At pin `50cb709` the repository has no three-dimensional Euclidean or
  rotation-group Lean module.
- No priority is claimed, and no named open problem is claimed resolved. In
  particular this holds for the gnomonic estimate, the SSA exceptional family,
  classical quaternion theory, and the perfectness of the infinitesimal
  rotation group (Bays–Peterzil, §3.1, is credited).
- The distance is field-valued, not a real metric. Area is finitely additive
  on geodesic polygons only, and no measure, Riemann or Darboux integral,
  completeness, ordinary compactness or general ODE existence is imported.
- The "double cover" is an algebraic two-to-one map. The familiar fundamental
  groups hold only in the semialgebraic category. Definable compactness is not
  compactness, and the fine topology does not make `G(No)` a real Lie group.
- The Ehrlich–Kaplan phase is canonical only for its normalization. No inverse
  function theorem is inferred from a nonsingular Jacobian. The dual number is
  formal. BCH truncations are finite-order certificates, not convergence.
- There is no classification of abstract subgroups or automorphisms, no Haar
  measure on the full class, and no physical model. The algorithms name no
  universal surreal data structure.
- The merge adds no mathematical result. Its remarks only relate statements
  to one another or to other reports.
- The checks test finite identities and finite rational cases. They do not
  establish summability, branch conditions, real closedness, transfer or
  topology.

## Relation to the neighbouring reports

**[Trigonometry](../../surcomplex/trigonometry/)** proves the finite phase
theorem over `No` (`trigonometry:thm:polar`), with its representatives
(`trigonometry:cor:representatives`), the planar half-angle chart
(`trigonometry:thm:cayley`), the spherical sine and cosine laws
(`trigonometry:thm:spherical`), and the global phase
(`trigonometry:def:globaltrig`, `trigonometry:thm:globalexp`). Theorem 2.2 here
is its Hahn-workspace form. Section 8 rederives the spherical laws from Gram
data and adds polar duality, reconstruction, area and holonomy. A treatment of
`SO(2,No)` is being added to that report at the same time. This report cites
only labels present at `50cb709` and does not duplicate that addition.

**[Surquaternions](../../surquaternions/surquaternions/)** contains the
rotation double cover (`squat:sub:spin`, `squat:thm:rotations`), the
quaternion Cayley chart (`squat:prop:charts`), the standard-part splitting of
the unit group (`squat:sub:unitreduction`), infinitesimal exp/log and the
graded rotation algebra (`squat:thm:principal-log`, `squat:thm:rotation-log`,
`squat:thm:graded`), the all-lengths support lemma (`squat:lem:neumann`), and
the radial-exponential differential (`squat:thm:exp-derivative`). Part II is
the 3×3 matrix counterpart. The spin differential's factor two relates them.
In particular the rank-one critical spheres of Theorem 25.2 are not the
rank-two ones of `squat:thm:exp-derivative`. At its pin, source 04 did not
cite this report, although the report already contained the double cover. The
citations in Section 5 correct this.

**[Foundations](../../foundations-and-computation/foundations/)** proves
small-set discreteness of the fine topology (`found:thm:discrete`) and
separates intrinsic from full-class topologies
(`found:prop:twotopologies`). Theorem 26.1 specializes the first.
`Surreal/Algebra/Geometry.lean` covers only the planar identities of the
trigonometry report.

**[Vector and tensor fields](../vector-and-tensor-fields/)**, placed in the
same commit, develops metrics and connections over real closed surreal
fields. The sphere computations of Section 12 are explicit and independent of
it.

[vector-and-tensor-fields](../vector-and-tensor-fields/), Part II, develops
field calculus over `K³` and leaves rotations and angles to this report. The
plane case, abelian, is Section 18 of
[trigonometry](../../surcomplex/trigonometry/) (`trigonometry:rot:sec:main`).

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python code/04-three-space-verify_identities.py > rerun-04.txt
python code/09-so3-verify.py > rerun-09.txt
```

The build gives 71 pages with zero errors, zero warnings, zero overfull or
underfull boxes, zero undefined references and zero duplicate PDF
destinations. Build on a copy of the directory, or remove the auxiliary files
afterwards. Both scripts need SymPy (`pip install -r
data/04-three-space-requirements.txt`; the two requirement files both pin
`sympy==1.14.0`). They print to standard output and write no files. The
recorded runs (Python 3.13.5) passed 19/19 groups and 24/24 checks. A rerun
for this merge with Python 3.14.4 reproduced both results, and only the
version and timing lines differ.
