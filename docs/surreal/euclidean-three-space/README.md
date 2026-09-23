# Euclidean Three-Space over the Surreal Numbers

**Coordinate geometry, spherical trigonometry, the rotation group SO(3,No), and surreal compact groups**
Research report, 22–23 September 2026, built from four independently written
manuscripts: 04 (the base, Part I) and 09 (Part II), merged at `50cb709`,
10 (Part III), added at `7b5f934`, all of 22 September 2026, and 11 (Part V)
of 23 September 2026, placed at `66d7e55` and added after it.
Prepared for Vladimir Reshetnikov.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 125 pages
README.md     this guide
10-rotation-quotients-SOURCE_AUDIT.md   source 10's source and novelty audit, verbatim
11-compact-groups-SOURCE_AUDIT.md       source 11's source and proof audit, verbatim
code/
  04-three-space-verify_identities.py   source 04 checks (19 groups)
  09-so3-verify.py                      source 09 checks (24 checks)
  10-rotation-quotients-verify.py       source 10 checks (39 checks)
  10-rotation-quotients-build.sh, 10-rotation-quotients-build.ps1
                                        source 10's delivered helpers (see below)
  11-compact-groups-verify.py           source 11 checks (33 checks)
  11-compact-groups-build.sh            source 11's delivered helper (see below)
data/
  04-three-space-requirements.txt, 04-three-space-verification.txt
  09-so3-requirements.txt, 09-so3-verification.txt
  10-rotation-quotients-requirements.txt, 10-rotation-quotients-verification.json
  11-compact-groups-requirements.txt, 11-compact-groups-verification_results.json
```

Every label in `article.tex` carries the prefix `e3:`. Material from source
09 carries the sub-prefix `e3:so:`, material from source 10 the sub-prefix
`e3:cut:`, and material from source 11 the sub-prefix `e3:cpt:`. When sources 04 and 09 were merged the report was new, so no earlier
`e3:` label existed. All 135 labels of the placed source 04 text are kept, with
the prefix added. Of source 09's 107 labels, 93 are kept. The other 14 were
nine section labels of source 09 sections that are no longer printed on their
own, and five labels of equations or a theorem now printed once under a source
04 or merge label. The addition of source 10 renamed or removed no existing
label: the report had 253 labels before it and has 330 after it, the 77 new
ones all `e3:cut:`. The addition of source 11 also renamed or removed no
existing label and changed no existing number: the report had 330 labels before
it and has 410 after it, the 80 new ones all `e3:cpt:`, and a comparison of the
built `.aux` files shows every one of the 330 earlier labels with its earlier
number. Of source 11's 67 labels, 62 are kept with the prefix; the other five
were its section on scalars and its three appendices, now printed as
subsections or paragraphs (Sections 39.4, 50.4, 36.7 and 39.2 with Appendix
B.5), and its size lemma, printed once as Lemma 33.1. The
[formalization ledger](../../FORMALIZATION.md) lists 64 statement labels of
Parts I–III (40 of Parts I and II, 24 of Part III) as pending, and does not
yet list Part V; no label of this report has a Lean mapping.

## Four sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **04** (base) | *Analytic Geometry and Trigonometry in Surreal Three-Space: finite angles, arbitrary scales, spherical duality, solid angles, rotations, and curvature* (34 pages) | `d22a5b35d5b3` | Section 2 and all of Part I (Sections 3–15); Sections 36.1 and 36.3; the first proof of Theorem 2.2. Files prefixed `04-three-space-`. |
| **09** | *Rotations of Surreal Three-Space: Algebra, Spin, Infinitesimal Structure, and Topology* (31 pages, 19 sections, 26 numbered statements) | `dcf86662b574` | All of Part II (Sections 16–27). In Part I it adds Proposition 2.1 (localization), the three-part normal-form decomposition, the hat matrix and identities (3.4)–(3.6), Proposition 5.2, the algebraic-angle form of Theorem 5.3, and Theorem 5.6. It also contributes Sections 36.2 and 36.4. Files prefixed `09-so3-`. |
| **10** | *Valuation Cuts and the Universal Set-Sized Quotient of Surreal Rotation Groups: exact commutators, normal subgroups, perfect residuals, and surcomplex special unitary groups* (24 pages) | `465a54b479a1` | All of Part III (Sections 28–35); Sections 36.5–36.6, the source 10 paragraph of 36.7, the non-claims 37.3, the last part of Section 38 with 38.1, and Appendix B.4. Files prefixed `10-rotation-quotients-`. |
| **11** | *Small Representations and Normal Structure of Surreal Compact Groups: a semisimplicity criterion, valuation-cut classification, and contrasts with split groups and omnific lattices* (24 pages) | `9693b28c24e6` | All of Part V (Sections 39–50) except the comparisons written for the addition (50.1, 50.2); the source 11 paragraph of 36.7, the non-claims 37.5, and Appendix B.5. Files prefixed `11-compact-groups-`. |

The merge of 04 and 09 was written at `50cb709`, after both manuscripts were
placed in `5fe7f8d`. Source 10 arrived later, as manuscript 03 of a later
batch. It was placed in `7b5f934` and numbered 10, after the highest existing
file prefix. Part III was written at `7b5f934`. Source 10 read this report at
`465a54b`, and `article.tex` did not change between that commit and
`7b5f934`, so its references to Part II are accurate. The manuscripts
themselves, their PDFs and their READMEs, and source 09's checksum list, are
not shipped. Source 10 delivered no checksum list. Its source audit is shipped
verbatim as `10-rotation-quotients-SOURCE_AUDIT.md`, and that file names the
delivered files by their unprefixed names. The code and data files are
byte-identical to the delivered ones.

Source 11 arrived as manuscript 06 of batch 29. It was placed in `66d7e55` and
numbered 11, after the highest existing file prefix; Part V was written on top
of that commit. Source 11 read this report's README and source 10's audit at
`9693b28` through a connector, after a local clone failed; `article.tex` did
not change between `9693b28` and `66d7e55`, so its descriptions of Part III
are accurate. Its manuscript, PDF and README are not shipped, and it delivered
no checksum list. Its audit is shipped verbatim as
`11-compact-groups-SOURCE_AUDIT.md` and names the delivered files by their
unprefixed names. Part V is printed after Part IV, not between Parts III and
IV, so that no section, theorem or equation number of Parts I–IV changes.

**Why one report.** Both manuscripts develop the finite algebra of spatial
rotations. Otherwise they are complementary. Source 04 is a geometry of points,
lines, spheres and spherical triangles that uses rotations as one tool. Source
09 is a structure theory of the rotation group. Source 04 is the base: it is the
wider development and fixes the scalar conventions.

**Printed once** (Section 1.1 lists the choices; the items for source 11 are
at the end):

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
  which Lemma 20.1 now refers;
- for source 11: the size lemma, printed once as Lemma 33.1 (source 11 proves
  it with the same map); the infinitesimal circle logarithm, Lemma 46.2, which
  is the infinitesimal factor of the trigonometry report's circle splitting and
  which Part III recalls as (35.1); the omnific statements of Section 49,
  credited to `odg:cor:orthogonal`, `ogl:lem:bounded` and `ogl:alg:thm:real`
  (only the count `|SU_n(Oz[i])| = 4^{n-1} n!` is not already in the
  collection); and the commutator bound, Lemma 43.1, which is the identity of
  source 10's proof of Lemma 29.2, stated for every compact group. Source 11
  reproves Theorems 30.3, 30.6, 33.2, 34.1 and 34.3 as special cases of its
  all-type theorems by Nash charts instead of quaternions and Givens
  elimination; both routes are kept, and each Part V theorem names the Part III
  case it contains.

**Why source 10 is an addition.** Source 09's conclusion names
"normal-subgroup classification compatible with convex valuations" as a
direction. Source 10 supplies it for subgroups normal in the full group. It
also sharpens two statements of Part II, recorded as forward remarks that change
no existing statement or label. Remark 23.2 records that the inclusion of
filtration levels in Theorem 23.1 is an equality of single-commutator images.
Remark 23.3 records the exact perfect residual behind "perfect rather than
residually nilpotent". A pointer after Theorem 19.3 records the mixed-depth
version of its commutator construction. Source 10's recalls of Part II (split
extension, spin map, near-one lift and Cayley chart, SU(2) matrix model,
perfectness of K) are cited, not repeated. The commutator bound, Lemma 29.2, is
(23.3); source 10's finite matrix proof is kept as a second route beside Part
II's BCH proof. The scalar identity in the proof of Theorem 19.3 is the
orthogonal-axis case of Lemma 29.1.

**Why source 11 is an addition.** Source 10 asks for "a uniform reductive
classification" separating semisimple from toral factors (Section 38.1).
Source 11 proves one for every connected real linear algebraic group with
compact connected real points (Theorem 39.1). It also classifies the normal
subgroups of the higher-rank groups that Part III leaves unclassified
(Theorems 42.3 and 42.4), and it reproves Theorems 33.2, 34.1 and 34.3 by a
uniform second route. Its groups and scalars are Part III's, so it belongs here
rather than in the omnific-groups report, whose kernels are constant-term
kernels over `Oz`.

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

Source 10's renamings (table in Section 28.4). Its depth `d(g)` is written
`v(U−I)`, since `d = √D` is a Gram quantity. Its commutators `[g,h]` become
`(U,V)`, with the set of single commutators written out and kept distinct from
the generated subgroup. `K_α`, `K_C` become `K_{≥α}` and `K_𝒞`, as in
Part II's filtration. The ideals `I_C` become `𝔞_𝒞`. The residuals `P_Δ`, `P_α`
become `K_{>Δ}`, `K_{≫α}`. The lower central series `γ_n` becomes `Λ_n`. The
target groups `H`, `T`, `H_0` become `𝒯`, `𝒯_0`, since `H_n` is a half-turn. The
spin map `R(q)` becomes `p(q)`, and `r_γ` becomes `U_γ = Cay(ω^{−γ}e_1)`. The
class `No(i)` becomes `No[i]` (`SC` in `docs/NOTATION.md`), `U(1)`, `U(n)`
become `T(No)` and upright `U(n,·)`, `M_F` becomes `K̃_F`, the circle angle
`ℓ(u)` becomes `ℓ_𝔪(u)` as in the trigonometry report, and `c_η` becomes
`coef_η`. The Cayley map is the same in both texts. The factor ½ in Part II
belongs to the layer map `ℓ_γ`, so `ℓ_γ(U_γ) = 2e_1`. Source 10's `Δ_α` is
`docs/NOTATION.md`'s `H_α`.

Source 11's renamings (table in Section 39.3). Its Nash chart `q` with
inverse `c` becomes `σ`, `σ^{-1}`, and its class quotient `q` and unitary
quotient `Q_n` become `ϖ`, `ϖ_n`: `q` is a quaternion, `c` a cosine
coordinate, and source 11 used `q` for both maps. Its Conway monomials `t^γ`
become `ω^{-γ}` and `[t^γ]` becomes `coef_γ`, as in Part III. Its letter `r`
(standard part `r_g`, `dim Z`, the number of simple factors, a matrix) is
replaced by `g_0 = st(g)`, `dim Z`, an index set and `g_0`; its `d` (`dim G_0`,
the diagonal `d(c)`) by `dim g` and an explicit diagonal matrix, since
`d = √D` is the Gram quantity. Its generic subgroup `K` in the series becomes
`𝒴`, since `K` is the kernel of standard part; `γ_n` and `D^n` become `Λ_n`
and `^{(n)}`; `H` becomes `𝒯`; `[g,h]` becomes `(g,h)`; "upper cut" becomes
"upper segment"; `L`, `E` become `ℓ_𝔪` and `exp(i·)`; `W`, `X`, `P`, `F`
become `𝒲`, `𝒳`, `Q`, `Ψ` (and `𝕂` for `No` or `No[i]`); and its graded map
`ℓ_α` becomes `gr_α`, which on `SO(3)` is the hat matrix of Part II's
`ℓ_α`. The new symbols `μ_G`, `ν(g) = v(g−I)`, `μ_{≥α}`, `μ_𝒞` are, for
`SO(3)`, Part III's `K_No`, depth, `K_{≥α}` and `K_𝒞`. Source 11's theorem
"every proper class subgroup `N ◁ G`" is printed as "every proper normal
subgroup (a set or a proper class)", its intended meaning.

## What the report claims

Numbers refer to the built `article.pdf`. Part I works in a set-sized
real-closed Hahn workspace `F = R((t^Γ)) ⊂ No`, or in any real closed field for
the finite algebra. Part II works over a real closed field `F`, adding
`F ⊇ R` where standard parts are used. Part III works over a set-sized real
closed `F ⊇ R` with its natural valuation `v : F^× → Γ = F^×/O^×` in
Sections 28–32. In Sections 33–34 it works over the full class `No`, in an
NBG-style set/class foundation.

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

**Part III, valuation cuts and the universal quotient (source 10).** Write
`K_𝒞` for the rotations in `K` whose depth `v(U−I)` lies in an upper segment
`𝒞` of `Γ_{>0}`.

- Canonical near-one lift with `v(U−I) = v(u)` and `v(1−a) = 2v(U−I)`
  (Lemma 28.1). The scalar commutator identity
  `Re(q_1 q_2 q̄_1 q̄_2) = N(q_1)N(q_2) − 2‖u×w‖²` (Lemma 29.1). The depth
  bound (Lemma 29.2).
- The exact mixed-depth image: the *set* of single commutators
  `{(x,y) : x ∈ K_{≥α}, y ∈ K_{≥β}}` equals `K_{≥α+β}`, with factors of
  depths `α` and `δ−α` (Theorem 29.3). For upper segments, the single
  commutators, the generated subgroup and `K_{𝒞+𝒟}` coincide, and
  `𝔞_𝒞 𝔞_𝒟 = 𝔞_{𝒞+𝒟}` (Theorem 29.4).
- The normal closure in `G` of `U ≠ I` is `K_{≥v(U−I)}`, and every element
  is a product of two conjugates of a power `U^m` (Theorem 30.3). There is no
  uniform width (Proposition 30.4). `SO(3,R)` is simple (Lemma 30.5). The
  proper normal subgroups of `SO(3,F)` are exactly the `K_𝒞`. They form a
  chain, and `K` is the unique maximal one (Theorem 30.6). Every cut quotient
  has coordinates `(𝔪/𝔞_𝒞)³` (Proposition 30.8).
- `K_𝒞` is perfect ⇔ `𝒞+𝒞 = 𝒞` ⇔ `𝒞 = 𝒞_Δ` for a unique convex subgroup
  `Δ`, with commutator width one (Theorem 31.2).
- `Λ_n(K_{≥α}) = K_{≥nα}` and `K_{≥α}^{(r)} = K_{≥2^r α}`, and
  `K_{≥α}/K_{≥mα}` has class exactly `m−1` (Theorem 31.3). Both series
  stabilize at stage ω at the perfect residual `K_{≫α}`, the largest perfect
  subgroup (Theorem 31.4). `K_{≥α}/K_{≫α}` is the universal residually
  nilpotent quotient, and `K_{≥α}` is residually nilpotent ⇔ `α` is an order
  unit (Theorem 31.6).
- For set-sized `F`, the compact elements of the normal lattice are the
  `K_{≥α}`, and the abstract group determines `Γ` (Proposition 32.1).
- Over `No`, every open value interval `(0,δ)` is a proper class
  (Lemma 33.1). **Every class homomorphism `SO(3,No) → 𝒯` into a set-sized
  group factors uniquely through standard part onto `SO(3,R)`** (Theorem 33.2).
  The proof applies normal closure and then the Hartogs ordinal of `𝒯` to the
  one-axis rotations `U_γ`, and uses no global choice. The only nontrivial
  set-sized image is `SO(3,R)` (Corollary 33.3). Set actions and
  representations over set-sized fields factor through `st` (Corollary 33.4).
  A set-sized precursor is the bound `|𝒯| ≥ |(0,δ)_Γ|` (33.4). No principal
  `K_{≥α} ≤ SO(3,No)` is residually nilpotent (Corollary 33.5).
- The same universal property holds for `SU(2,No[i])` (Theorem 34.1), and,
  via near-identity Givens factorizations (Lemma 34.2), for `SO(n,No)` with
  `n ≥ 3` and `SU(n,No[i])` with `n ≥ 2`, for fixed ordinary `n`
  (Theorem 34.3, Corollary 34.4).
- Examples in rank one and rank two, and a group with no order unit
  (Section 35). The factorization fails for the circle. The character
  `χ_η(u) = coef_η(ℓ_𝔪(u))` is a class homomorphism
  `T(No) → (R,+)` that is nonzero on the infinitesimal kernel, and the same
  failure holds for `U(n,No[i])` (Proposition 35.1).

**Part V, surreal compact groups (source 11).** Let `𝖦` be a connected real
linear algebraic group with compact connected `𝖦(R)`, `G = 𝖦(No)`,
`G_0 = 𝖦(R)`, `μ_G = ker st`, and `μ_S`, `μ_Z` the infinitesimals of the
derived group and of the central torus. Everything is over the full classes
`No` and `No[i]`, in NBG with choice.

- The small-observation theorem (Theorem 39.1): every class homomorphism to a
  set-sized group kills `μ_S = (μ_G, μ_G)`; the class map
  `ϖ : G → G_0 × μ_Z` is onto with kernel `μ_S`, and its points are separated
  by set-sized homomorphisms (Theorem 46.4, Proposition 46.3); a universal
  set-sized quotient exists exactly when `𝖦` is semisimple, and it is then
  standard part (Theorem 46.5). The standard-part splitting is Proposition
  39.2.
- A finite Nash-chart toolkit transfers real implicit-function statements with
  fixed real radii (Lemmas 40.1–40.5). With it, for a simple nonabelian Lie
  algebra, the normal closure in `G` of `I ≠ g ∈ μ_G` is `μ_{≥ν(g)}`
  (Theorem 41.3), and an element with noncentral standard part normally
  generates `G` (Theorem 41.5); no uniform width is claimed (Remark 41.4).
- The subgroups of `μ_G` normal in `G` are the `μ_𝒞` for upper segments `𝒞`
  (Theorem 42.2); every proper normal subgroup is `𝒜 μ_𝒞` with `𝒜` in the
  finite center (Theorem 42.3); for semisimple groups the ambient-normal
  infinitesimal subgroups are products over the simple factors, with no
  diagonal couplings (Theorem 42.4).
- For semisimple groups, `(μ_{≥α}, μ_{≥β}) = μ_{≥α+β}` and
  `(μ_𝒞, μ_𝒟) = μ_{𝒞+𝒟}` as generated subgroups (Theorem 43.2, Corollary
  43.3); the graded bracket (Proposition 43.5); `Λ_n(μ_𝒞) = μ_{n𝒞}`,
  `μ_𝒞^{(n)} = μ_{2^n 𝒞}`, and the derived series stabilizes at stage ω at the
  largest perfect subgroup (Theorem 44.1); no nontrivial ambient segment is
  solvable (Corollary 44.2).
- Semisimple invisibility, the universal quotient and set actions and
  representations of any set dimension (Theorem 45.2, Corollaries 45.3–45.4);
  the central–semisimple product (Proposition 46.1); the infinitesimal circle
  logarithm (Lemma 46.2).
- Examples: the compact symplectic and exceptional types; the exact unitary
  quotient `U(n,No[i]) → U(n,C) × 𝔪` (Proposition 47.1); trivial finite
  quotients of every compact connected group.
- Contrast: every set-sized image of `SL_n(No)` or `SL_n(No[i])`, `n ≥ 2`, is
  trivial, and set-sized images of `GL_n` factor through the determinant
  (Theorem 48.1, Corollary 48.2).
- Omnific points: `Oz ∩ O = Z` (Lemma 49.1); compact integral collapse
  (Proposition 49.2); `|SO_n(Oz)| = 2^{n-1} n!` and
  `|SU_n(Oz[i])| = 4^{n-1} n!` (Theorem 49.3).
- Section 50.1 (written for the addition) states the agreement with Parts II
  and III: for semisimple groups the invisible subgroup is all of `μ_G`, as in
  Theorems 33.2, 34.1 and 34.3; the torus characters are those of Proposition
  35.1; for `SO(3)` the segments, series and perfect residual agree with
  Theorems 30.6, 31.3 and 31.4, where Part III is stronger (single-commutator
  exactness, commutator width, width two for normal generation). Section 50.2
  records that neither `ogl:el:prop:finiteside` nor Theorem 39.1 implies the
  other.

## What the report does not claim

Section 37 lists every limitation of the sources: 18 for source 04 (G1–G18),
22 for source 09 (S1–S22), 18 for source 10 (C1–C18), 21 for source 11
(P1–P21, Section 37.5), and 9 for the merge and the two additions (M1–M9). The
main ones follow.

- The report is AI-assisted and has not been refereed. No statement has a
  Lean formalization, and the Lean layers of Sections 36.3–36.5 are proposals.
  At pin `50cb709`, and still at `7b5f934` and `66d7e55`, the repository has
  no three-dimensional Euclidean, rotation-group or compact-group Lean module.
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
- The merge adds no mathematical result, and neither do the two additions
  beyond their sources. Their remarks, Sections 50.1–50.2 and the status notes
  in Section 38 only relate statements to one another or to other reports.
- The checks test finite identities and finite rational cases. They do not
  establish summability, branch conditions, real closedness, transfer or
  topology. Source 10's 39 checks do not verify the classification, the
  transfinite series, the Hartogs argument or the universal factorization.
- **Source 10 (Part III).** The normal-subgroup classification and the
  universal factorization concern subgroups normal in the *full* group and
  homomorphisms of the *full* class group. Nothing is claimed about subgroups
  normal only in `K`, about abstract subgroups, or about homomorphisms defined
  only on `K_{≥α}` or `K_No`. Part II's non-claim about abstract subgroups
  stands.
- Commutator width one of `K` (Bays–Peterzil, proof of Claim 3.3; Theorem 19.3
  here), spin, standard part and the unequal-parameter identity are not new.
  The normal closure and cut classification carry no historical priority claim.
  The value-group recovery is not a first discovery of field recoverability,
  since Bays–Peterzil's Theorem 1.1 is stronger. It uses the whole subgroup
  lattice, not a first-order formula, and holds only for set-sized fields. The
  circle counterexample is a consequence of the established splitting of
  `trigonometry:thm:polar`. The literature search was not exhaustive, and
  failing to locate a statement is not priority.
- "Set-sized" means a set in the same NBG-style foundation, not a
  higher-universe type. A Lean version must be universe-relative and name its
  universes. No class of all classes is formed, and `G_No/K_No ≅ SO(3,R)` is
  shorthand. The theorem is not an automatic-continuity result, and
  infinitesimals still act faithfully on the class `No³`. The cardinal bound
  (33.4) does not force the kernel to contain `K`. The natural valuation is
  essential, and an arbitrary coarsening breaks the argument.
- Source 10 treats only `SO(n)` with `n ≥ 3` and `SU(n)` with `n ≥ 2`, in fixed
  rank, and its non-claims C15 and C18 stand as statements about source 10.
  Part V now supplies, over `No`, the higher-rank normal subgroups (Theorems
  42.3–42.4) and the uniform classification for compact connected groups
  (Theorem 39.1). There is still no higher-rank commutator width, and no
  single-commutator image at prescribed depths outside `SO(3)`. The status
  notes in Section 38.1 record what remains open: `K`-normal and `μ_G`-normal
  subgroups and homomorphisms defined only on the kernel; exact word images
  (only generated subgroups are exact in general); noncompact reductive groups
  and groups with disconnected real points; and first-order accessibility.
- **Source 11 (Part V).** AI-assisted, unrefereed and not Lean-verified; its 33
  checks do not prove the Nash-transfer, normal-generation or class arguments.
  Priority is not certified; the candidate-original package is only the exact
  invisible subgroup, the separating quotient and the semisimplicity
  criterion. Its repository comparison was targeted (a connector read at
  `9693b28`; the clone failed). The central decomposition and interpretability
  are Bays–Peterzil's, local openness is D'Andrea–Maffei's, quantitative normal
  generation is surveyed by Kramer, and the `SL_n` argument is the classical
  simplicity mechanism. `G(No)` is not claimed compact in the fine topology;
  the number of conjugates is not bounded; the segment theorems concern
  ambient normality only; the mixed theorem concerns generated subgroups; no
  nontrivial residual is claimed in rank-one Hahn fields; coefficient maps are
  not claimed to exhaust the additive dual; determinant is not a set-sized
  universal quotient; and exact normal closure fails for an element in one
  simple factor or in a torus.

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
only labels present at `50cb709` and does not duplicate that addition. That
treatment is now its Section 18 (`trigonometry:rot:sec:main`). Part III's
circle counterexample (Proposition 35.1) uses its circle splitting
(`trigonometry:thm:polar`, `trigonometry:eq:circlesplit`). On a layer, the
circle character induces its layer isomorphism
`trigonometry:rot:thm:graded`. Part V's infinitesimal circle logarithm (Lemma
46.2) is the infinitesimal factor of that splitting, the map
`trigonometry:rot:eq:ellm`; source 11 did not cite the trigonometry report,
and the credit is added here.

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

**[Omnific groups and lattices](../omnific-groups-and-lattices/)** proves
omnific rigidity for real algebraic groups (`ogl:alg:thm:real`), which contains
the compact collapse of Proposition 49.2, and a universal set-sized quotient
for `SL_n` of the finite surreals (`ogl:el:prop:finiteside`), compared with
Part III in `ogl:el:rem:e3`. Neither that proposition nor Theorem 39.1 implies
the other (Section 50.2). **[Omnific Diophantine
geometry](../omnific-diophantine-geometry/)** proves `SO_n(Oz)` finite
(`odg:cor:orthogonal`), which is Theorem 49.3(i). Source 11 cited neither;
both were in the tree at its pin.

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
python code/10-rotation-quotients-verify.py --output rerun-10.json
python code/11-compact-groups-verify.py --output rerun-11.json
```

The build gives 125 pages with zero errors, zero warnings, zero overfull or
underfull boxes, zero undefined references, zero multiply defined labels and
zero duplicate PDF destinations. Build on a copy of the directory, or remove the auxiliary files
afterwards. Both scripts need SymPy (`pip install -r
data/04-three-space-requirements.txt`; the two requirement files both pin
`sympy==1.14.0`). They print to standard output and write no files. The
recorded runs (Python 3.13.5) passed 19/19 groups and 24/24 checks. A rerun
for this merge with Python 3.14.4 reproduced both results, and only the
version and timing lines differ.

Source 10's script needs the same SymPy pin
(`data/10-rotation-quotients-requirements.txt`). It writes a JSON report,
by default `verification.json` in the current directory. Always pass
`--output` as above, or run it on a copy, so that the shipped
`data/10-rotation-quotients-verification.json` is never overwritten. The
recorded run (Python 3.13.5, SymPy 1.14.0) passed 39/39 checks: 12 groups of
general identities, 8 ordinary-power specializations, 16 one-parameter
commutator-depth examples and 3 unitary Givens identities. A rerun on a copy
with Python 3.14.4 also passed 39/39. Its report differs from the recorded one
only in the `python` field. The delivered helpers
`code/10-rotation-quotients-build.sh` and `.ps1` are kept byte-identical but do
not work from this layout. They `cd` to their own directory, call the
unprefixed `verify.py` and `article.tex`, and would overwrite
`verification.json` and `article.pdf` in place. Use the commands above
instead.

Source 11's script needs SymPy (`data/11-compact-groups-requirements.txt`
asks for `sympy>=1.12,<2`). By default it writes `verification_results.json`
next to the script, that is, a new file `code/verification_results.json`;
always pass `--output` as above, or run it on a copy. The recorded run
(Python 3.13.5, SymPy 1.14.0) passed 33/33 checks: `SL_2` factorizations and
root scaling, the matrix commutator identity, `so(3)` and `su(3)`
bracket-spanning certificates (determinants 16 and 4608/625 for `su(3)`),
Cayley-commutator derivatives, formal circle-logarithm identities, and the
monomial counts for `n ≤ 4`. A rerun on a copy with Python 3.14.4 and SymPy
1.14.0 also passed 33/33; its report differs from
`data/11-compact-groups-verification_results.json` only in the
`python_version` field. The delivered `code/11-compact-groups-build.sh` runs
`python3 verify.py` and `pdflatex article.tex` in its own directory; under
the shipped names it fails, and it is kept only as delivered.
