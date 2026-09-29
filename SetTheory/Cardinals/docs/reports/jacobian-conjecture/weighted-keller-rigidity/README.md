# All-Degree Rigidity of a Weighted Keller Class

**Classification, degenerations, and an obstructed double point** —
with Part II, **All-degree classification of affine-in-z weighted Keller
maps: constant-slope rigidity and obstructed nilpotent deformations**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, and in particular that project's research notes
on the weighted class of its map (`Algebra/JacobianConjecture/Research/README.md:180-248`).
It is built from **two manuscripts**: Part I is dated 24 September 2026, Part
II 29 September 2026. Author lines: "Prepared for Vladimir Reshetnikov" (both);
the delivered PDF metadata names the authors as "ChatGPT; prepared for
Vladimir Reshetnikov" (Part I) and "AI-assisted research draft prepared for
Vladimir Reshetnikov" (Part II).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | batch 36, manuscript 01 | `ProveIt_Weighted_Keller_Rigidity` (inner directory of the same name, main file `article.tex`, 23-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` | Sections 1–11 and Appendices A–D, apart from text marked `[write]` or dated "Added 29 September 2026" (written in `c69841a69`) |
| Part II | batch 44, manuscript 04 | `ProveIt_Affine_Weighted_Keller_Classification` (inner directory of the same name, main file `article.tex`, 22-page A4 PDF; delivered in `ae28ea2db`) | `9b24a3a8d` | `203016015` (addition, prefix `02-affine-slope-`) | Sections 12–25: Section 12 written at the write, Sections 13–23 are the manuscript's Sections 1–11, Sections 24–25 its Appendices A–B |

Every result, proof, example, table, question and limitation of both
manuscripts is printed. Where Part II restates Part I it is printed once
(Section 12.4 lists what). **Status: AI-assisted and unrefereed. None of the
report's own results, in either Part, is formalized in Lean or Rocq.**
Placement beside the Lean/Rocq development of the Jacobian project confers no
formal status on it (see "The formal project" below).

```
README.md                                  this guide (replaces both delivered READMEs)
article.tex                                the report: Part I, Part II, Part I's appendices, labels prefixed
article.pdf                                the compiled report, 54 pages (unnumbered title page, contents
                                           pages 1–3, Part I pages 4–23, Part II pages 24–48, Part I's
                                           appendices pages 49–53, references on pages 52–53)
code/verify_results.py                     Part I: exact companion checks, 13 groups (SymPy)
data/requirements.txt                      Part I: the source's pin, sympy==1.14.0
data/verification.json                     Part I: recorded JSON certificate: equations, matrix, orderings,
                                           tangent, rank minor, obstruction vector, cokernel functional
data/verification.txt                      Part I: recorded output of the run: 13 PASS lines
02-affine-slope-SOURCES.md                 Part II: the source's repository and literature ledger, as delivered
02-affine-slope-STATUS.md                  Part II: the source's claim and verification boundaries, as delivered
code/02-affine-slope-verify_results.py     Part II: 12 groups of exact checks (SymPy); see "Rerunning"
code/02-affine-slope-weighted_keller.py    Part II: exact rational recognition of the class (SymPy)
code/02-affine-slope-__init__.py           Part II: the package's one-line code/__init__.py
data/02-affine-slope-requirements.txt      Part II: the source's pin, sympy==1.14.0
data/02-affine-slope-verification.json     Part II: recorded JSON (versions, pin, 12 check records)
data/02-affine-slope-verification.txt      Part II: recorded summary: 12 PASS lines
```

Delivered names. Part I: the package had every file at its root;
`verify_results.py` is shipped as `code/verify_results.py`;
`verification.json`, `verification.txt` and `requirements.txt` are under
`data/` with unchanged names. Part II: the package had `code/`, `data/` and
root `SOURCES.md`, `STATUS.md`, `requirements.txt`; each is shipped with the
prefix `02-affine-slope-` (`code/X` → `code/02-affine-slope-X`, `data/X` →
`data/02-affine-slope-X`, root `requirements.txt` →
`data/02-affine-slope-requirements.txt`, `SOURCES.md`/`STATUS.md` at the report
root). `02-` is the next number in this report's local sequence (Part I's files
are unprefixed, counted as `01`). Neither delivered README nor PDF is shipped
(`article.pdf` is a build of this text), and neither package had a checksum
manifest. Every file under `code/` and `data/` and both `02-affine-slope-*.md`
files are byte-identical to the deliveries.

## Labels

Every label in `article.tex` carries the prefix `wkr:`; Part II's carry
`wkr:as:` (affine slope). 199 labels in all:

- 102 of Part I, unchanged (96 of the source and six added at the batch-36
  write). The two new subsections of that write (1.4, 1.5) end Section 1 and
  Appendix D is new, so no source number moved.
- 97 `wkr:as:` labels added in batch 44: 76 of the manuscript's 84 labels,
  unchanged after the prefix; the other eight (`eq:F0`, `eq:original-facts`,
  `eq:lift`, `prop:det`, `eq:weightedJ`, `eq:tame-map`, `eq:inverse`,
  `eq:original-normalization`) marked items that duplicate Part I and are
  printed there only. 21 are new: the five subsections of Section 12, its
  notation table, the four questions of Part I's Section 10.1–10.4
  (`wkr:as:q:quadratic`, `…:q:slope`, `…:q:stabilize`, `…:q:gluing`, placed on
  Part I's existing subsection headings), three previously unlabelled
  manuscript items (`cor:twoclasses`, `ex:shear`, `prop:complexity`), a
  remark, two future-work subsections, the conclusion and the three
  reproducibility sections.

Part II is inserted after Part I's Conclusion (Section 11) and before Part I's
appendices, so every Part I section, theorem, equation and appendix keeps its
number; this was checked against the `.aux` of a build of the committed text
(all 102 Part I labels have the same numbers; page numbers moved by one
because the contents grew to three pages). No label has a Lean or Rocq
mapping.

## Setting and notation

`K` is a field of characteristic zero. Source weights `(−1,1,2)`, target
weights `(2,1,−1)`; invariants `t = xy`, `v = x²z`; a weighted map is the
lift `L(p,q,r) = (p(t,v)/x², q(t,v)/x, x·r(t,v))`. `F_0` is the project's map
(determinant −2); the report **normalizes** `p_v(0) = q_t(0) = r(0) = 1`,
which makes the determinant **−1**, and Part I writes `r = 1 + βt + γv`. The
normalized representative is
`F_* = F_{1,1} = diag(−1/2, −3/2, 1/2) ∘ F_0 ∘ diag(1, −2/3, −2)`, and
`F_{a,b}` (a two-parameter family) is its diagonal orbit. Watch for these
readings:

- `t = xy` agrees with the project's research notes but **not** with the
  sibling report [arithmetic-local-global-fibers](../arithmetic-local-global-fibers/),
  where `t = y + 1/x` (Part II calls that variable `τ`), nor with the family
  parameter `t` of the project README.
- Part I: `u` is `1 + xy` in (1.1) but a **tangent vector** from Section 8 on;
  `h` is the project's `h = u²z + y²(1+3u)` in (1.1) but a **source-shear
  polynomial** `h(t)` in `T_h`; `ρ` is the torus parameter; `k` is the
  coefficient in `E = 1 + kt`. `a, b` are **family parameters**
  (`a = β²/γ`, `b = γ/β`), not the project's coefficient `a = [t²]p` (Research
  README line 210; the added notes write `α` for it) nor its stable variables
  `a, b`. `A, B, C, D` are coefficient polynomials in `t` (Section 5), not
  target coordinates.
- **Part II uses several of the same letters differently**; Table 1 in
  Section 12.3 fixes them. Above all: in Part II `a, b, c, d, e, g` are the
  **coefficient polynomials** of `p = a v + b`, `q = c v + d`, `r = g v + e`
  (so `g = r_v` is the "third slope", Part I's `G(t)`, and `e` is Part I's
  `R(t)`); Part I's family parameters are written `a_I, b_I` there. Part II's
  `U = 1 − 2βt/3` is Part I's `E`, its scalar `k = 9/β` is Part I's `c`, and
  `H` is the cube root in `g = H³`.
- Renamed from manuscript 04 (disclosed in Section 12.3): its field `𝕂` is
  printed `K`; its valuations `A, C, G` are `o_a, o_c, o_g`; its collision
  points `A, B` are `X_1, X_2`; its reduced algebra `A` is `Λ`; its degree cap
  `D` and coefficient algebras `A_D` are `𝖣` and `Λ_𝖣`. Part II's equations
  are numbered by section, as in Part I; the manuscript numbered them
  consecutively (1)–(59), and its section *k* is Section *k*+12.

## What the report claims

Theorem numbers are those of the built `article.pdf`.

### Part I (batch 36)

- **All-degree classification (Theorem 3.1).** For `p, q` affine in `v` and
  `r` affine in `(t, v)`, normalized, with no bound on ordinary degree: the
  Keller maps are exactly (A) `r = 1` and an explicit tame family, or (B)
  `β, γ ≠ 0` and `(p, q, r) = (p_{a,b}, q_{a,b}, r_{a,b})`. Exactly one of
  `β, γ` nonzero is impossible. The proof rests on one-variable rigidity:
  a constant weighted Wronskian (Lemma 4.1), a cubic–square relation
  (Lemma 4.2), and a linear common factor (Lemma 4.3).
- **Sharp support (Corollary 6.1).** Every noninvertible map of the class
  has degrees `(7,6,4)` and supports `(7,6,3)`: exactly sixteen monomials,
  and `q40 = 0` is forced rather than imposed. Every member of branch (B) is
  in one diagonal orbit of `F_*` (6.3), with collisions over the ground
  field (6.6)–(6.7) and the normalized witness `F_*(1,0,−1) = F_*(0,−9,71)`
  (Example 6.2).
- **Triangular extension (Theorem 6.3, Corollary 6.4).** For
  `r = R(t) + γv` with `R` arbitrary, every noninvertible map is
  `F_{a,b} ∘ T_h` with `T_h(x,y,z) = (x, y, z + y²h(xy))`; degrees
  `(2m+8, 2m+7, 2m+5)` for `deg h = m`, so the noninvertible maximum
  degrees are exactly `{7, 8, 10, 12, …}`.
- **Parameter plane (Theorem 7.1).** In the degree-seven coefficient space,
  `(a,b) ↦ F_{a,b}` is a closed embedding of `A²`; its invertible members are
  exactly the axes `ab = 0`; `r = 1` cuts out the reduced node. Reduced
  rigidity in all degrees for `r = 1 + t + v` (Corollary 7.2).
- **Double point (Theorem 8.1).** For `r = 1 + t + v` and ordinary degree at
  most seven, the full coefficient algebra is `Q[ε]/(ε²)` with
  `ε = q21 − 4`; tangent rank certificate (an 11×11 minor of determinant
  −18874368), a second-order obstruction `LH = −1/72`, the criterion
  Lemma 8.2, the functor of points (Corollary 8.3) and, on `βγ ≠ 0`, torus
  times the double point (Theorem 8.4). Explicit generators: (A.1).
- **Proposed work.** A recognition procedure (Section 9.1), a
  formalization order (Section 9.3) and nine research directions
  (Sections 10.1–10.9).

### Part II (batch 44)

- **Constant-slope rigidity (Theorem 15.1).** If all three numerators are
  affine in `v` (`p = a v + b`, `q = c v + d`, `r = g v + e`), the lift is
  polynomial and normalized, and the Jacobian is −1, then `g = r_v` is
  **constant**, with no bound on ordinary degree. This **answers Part I's
  Section 10.2** ("Must `G` be constant …?"): yes. The proof: a cube–square
  factorization from `J_2 = 0` (16.5), a rational moving coordinate giving
  `LL′ = α/U³` (Lemma 16.2: one critical root, and regularity forces a simple
  pole), and polynomiality at the origin (Section 16.6).
- **Complete normal forms (Theorem 15.2).** (T) the tame family (Part I's
  case A); (N) for `β, γ ≠ 0` and any `e` with `e(0) = 1`, `e′(0) = β`: the
  explicit forms (15.3)–(15.5), which are Part I's `F_{a,b} ∘ T_h` (Remark
  15.3). So Part I's classification covers every affine-in-`z` weighted Keller
  map. Reconstruction of (N) by the moving coordinate is a second proof of
  Part I's nonconstant branch (Section 17.2).
- **Consequences (Section 18).** Two tame source–target classes, identity and
  `F_0` (Corollary 18.1); explicit ground-field collision points after the
  shear (Proposition 18.2), e.g. `F(1,0,−1) = F(0,−9,−10)` for
  `e = 1+t+t²+t³` (Example 18.3, degrees `(10,9,7)`); the degree spectrum
  `{7} ∪ {8,10,12,…}` for the whole affine-in-`z` class (Corollary 18.4).
- **Cubic model (Proposition 19.1).** `[K(x,y,z) : K(P,Q,R)] = 3` with Galois
  group `S_3` for `F_0` and all of branch (N); degree 1 on (T). Not new for
  `F_0` (see "Neighbouring reports").
- **Nilpotent slopes (Section 20).** Slope constancy over every reduced
  `Q`-algebra (Theorem 20.1); explicit dual-number solutions with slope `G(t)`
  of every degree (Theorem 20.2, `O(t^m) = (m+3)(2m+3)/(m+1)·t^{2m}`); every
  nonzero first-order slope direction at the tame point `(v,t,1)` is
  obstructed at second order inside the affine class, whatever the
  second-order corrections (Theorem 20.3); a `v²` term repairs it and is
  minimal (Proposition 20.4); a divergence-free formal flow integrates it over
  `K[x,y,z][[ε]]` (Proposition 20.5); in the finite coefficient algebras
  `Λ_𝖣`, `g_1, …, g_{𝖣−1}` are nonzero nilpotents and give a
  `(𝖣−1)`-dimensional space of obstructed tangent directions (Corollary 20.6).
- **Recognition algorithm (Section 21).** A coefficient-only test with
  `O(𝖣)` field operations (Proposition 21.1, arithmetic model only), and the
  rational-coefficient implementation `code/02-affine-slope-weighted_keller.py`.
- **Proposed work.** Nine research directions (Sections 22.1–22.9).

## What Part II answers in Part I, and what it does not

- **Section 10.2 is answered** (and the exclusions at the end of Section 6.4
  and in Section 9.1 are lifted): dated pointers were added there and on the
  title page.
- **Sections 10.1, 10.3 and 10.4 stay open**; dated pointers say how Part II
  bears on them. Part II's nilpotent results live at the tame point with `r`
  free; Theorem 8.1's double point fixes `r = 1 + t + v` at the noninjective
  point. They neither extend nor contradict each other (the manuscript says
  so itself, Section 22.4). The quadratic repair (Proposition 20.4) needs a
  `v²` term but does not classify the quadratic class of Section 10.1.

## What the project already had, and whose it is

The manuscript of Part I cites the project's research notes for its
baseline, but presents two of their ingredients in its own words without
saying so. Section 1.4 of the report (added at the batch-36 write) credits
them:

- **The weighted determinant identity** `det J_F = det[[−2p, p_t, p_v],
  [−q, q_t, q_v], [r, r_t, r_v]]` (Proposition 2.2), with the same
  chain-rule proof in the localization at `x`, the lift, the polynomiality
  conditions and the normalization to determinant −1 are
  `Algebra/JacobianConjecture/Research/README.md:188-208`.
- **The collision mechanism** `F(1,t0,v0) = F(0, q, p − αq²)` when
  `r(t0,v0) = 0`, `α = [t²]p`, is `Algebra/JacobianConjecture/Research/README.md:210-224`;
  the report's collision (6.6) is its case `t0 = 0`, `v0 = −1/γ` (for
  `a = b = 1` it gives `(0,−9,71)`, checked at the write).

Relative to the project the new material is the all-degree classification
and everything after it. The project's sparsity certificate
(`Algebra/JacobianConjecture/Research/verify_equivariant_sparsity.py`,
described at `Algebra/JacobianConjecture/Research/README.md:240-248`) covers
ordinary degree at most seven, leaves `q40 = 0` as the "remaining branch",
and is "deliberately not advertised as a global sixteen-monomial theorem".
Corollary 6.1 sharpens it to all degrees, inside the class only, and does
not contradict that caution. The report's tame branch (A) proves tameness
for constant `r` in all degrees without Moh's plane theorem, but only for
`p, q` affine in `v`; the project's Moh argument
(`Algebra/JacobianConjecture/Research/README.md:232-238`) covers a class with
`v²` terms up to degree six. The two stand side by side. The sparsity
script's comment that `(q21−4)²` "records a harmless nonreduced structure"
(`verify_equivariant_sparsity.py:129-132`) is what Theorem 8.1 upgrades to
an exact scheme statement.

Part II credits all of this and Part I itself correctly: its normal forms,
tame inverse, source shear, core support and degree spectrum are Part I's
(the source's `STATUS.md`, "Attribution and scope"), and it reuses Part I's
weighted identity with the project's credit. The manuscript restates these
items; they are printed once (Section 12.4). The project did not change
between Part II's pin `9b24a3a8d` and the placement commit.

## Gao's "degree-four" three-dimensional map

Part I cites Shuhong Gao (arXiv:2608.00222) for "a three-dimensional map
of degree four" (Section 1.3) and "a three-dimensional degree-four example"
(Section 10.6). **Gao's "degree" there is the geometric degree**, the number
of preimages of a generic point, as his abstract defines it. His
three-dimensional map `G_Gao` (Theorem 3.5; the subscript keeps it apart
from the report's coefficient `G(t)` of `v` in `r`) has components of ordinary degrees
**4, 11 and 12**, Jacobian determinant 2 and four generic preimages. This was
read from his Section 3.5 at the write and checked with SymPy 1.14.0 from his
printed formulas (degrees `(4,11,12)`, `det J_{G_Gao} = 2`). For Alpöge's map his
Theorem 3.3 gives ordinary degrees `(7,6,4)` and geometric degree three.

So Gao's `G_Gao` does **not** lower the ordinary degree of a three-dimensional
Keller counterexample below seven. The report's sentence that forced degree
seven "is compatible with examples outside this class of lower degree"
stays true as a compatibility statement, but `G_Gao` is not such an example.
The project's framing is unaffected: its notes say that its finite searches
"do not prove that ordinary degree seven or sixteen monomials is globally
minimal in dimension three", and that a simpler three-variable map would have
degree at least four and, below seven, would break the weighted symmetry
(`Algebra/JacobianConjecture/Research/README.md:12-15` and `:262-269`).
Whether a three-variable Keller counterexample of ordinary degree 4–6 exists
is not settled by any source cited here. Section 1.5 and a `[write]` note in
Section 10.6 of the report say this. Part II keeps ordinary and geometric
degree apart throughout; its Corollary 18.4 excludes ordinary degrees 4–6 only
for noninjective maps **in the affine-in-`z` class**.

## The formal project

`Algebra/JacobianConjecture` proves, with kernel-checked Lean 4 and Rocq/Coq,
these statements about `F_0` (Lean namespace
`LeanProofs.JacobianCounterexample`):

- the map `counterexample` (`Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean:95-101`)
  and its determinant `jacobianDet_counterexample` (`:134`, `−2` over every
  commutative ring);
- the collision (1.2) of the report: `collision₀`, `collision₁`,
  `collisionValue`, `collision`, `collision_points_distinct` (`:143-170`);
- the refutation `jacobianConjectureInDimensionThree_false` (`:201`);
- the weight-`(−1,1,2)` torus action `counterexample_scaling`
  (`Algebra/JacobianConjecture/Lean/JacobianConjecture/Scaling.lean:35`), the
  mirror symmetry `counterexample_equivariant` (`Equivariance.lean:47`) and
  the collision family (`CollisionFamily.lean`);
- in Coq (`Algebra/JacobianConjecture/Coq/`): `counterexample`
  (`Counterexample.v:110`), `jacobian_det_is_minus_two` (`:182`, at every
  point), `integral_collision_0_value`, `integral_collision_1_value`,
  `integral_collision_points_distinct` (`:249-265`),
  `counterexample_scaling` (`Scaling.v:32`),
  `jacobian_conjecture_dimension_three_is_false` (`:331`).

Part II's check group 4 (`original_map`) re-verifies in SymPy exactly the
determinant −2 and the integral collision, which are these kernel-checked
statements (verified at the write in the files at the placement commit), and
the normalization `F_* = diag ∘ F_0 ∘ diag`, which is not formalized.

**Nothing else in the report is formalized**: not the weighted determinant
identity (in the project only as a README calculation), not the
normalization, not the family `F_{a,b}`, not the normal forms (T)/(N), and
none of the theorems of either Part. Part II ships no Lean or Rocq file and
duplicates no declaration. The project's degree-bound and sparsity results
are SymPy certificates, not kernel proofs.

## What the report does not claim

- No new counterexample to the Jacobian conjecture; no classification of
  unrestricted Keller maps; not the construction of the known map; no
  minimum-degree theorem for all three-variable maps (both Parts).
- Excluded from the classification: `v²` terms in `p` or `q` (Sections 10.1,
  22.1). *Re-scoped in batch 44:* Part I also excluded a nonconstant
  coefficient `G(t)` of `v` in `r` (Sections 6.4, 10.2); Part II proves that
  it cannot occur when `p, q, r` are affine in `v`, so it is no longer an
  exclusion within the affine class.
- The double point and "torus × double point" concern the **degree-seven**
  coefficient scheme only; stabilization of the nonreduced structure at
  higher degree is not proved (Remark 8.5, Section 10.3), and Part II does not
  prove it either; the gluing at the axes is open (Section 10.4).
- Part II: slope constancy over reduced bases only, not a ring-wide
  two-branch normal form (a constant slope can be a zero divisor); the
  nilpotence indices, relations and full local algebra of `Λ_𝖣` are not
  determined; the formal flow is not a polynomial family in `ε` nor
  convergent, and no uniform `z`-degree bound is asserted; the cubic statement
  is about generic function-field degree, not about special fibers,
  finiteness or coverings; the `O(𝖣)` bound is an arithmetic-operation bound,
  not bit complexity or a SymPy timing; the classifier accepts rational
  coefficients only (a restriction of the software, not of the theorem); the
  sixteen-term assertion concerns the unsheared core.
- Characteristic zero is essential; nothing is claimed in positive
  characteristic (Sections 10.9, 22.7).
- Part I's script checks one ideal containment (`I ⊆` the displayed ideal, by
  substitution) and four sample shears `h = 1, t, t², t³`; Part II's checks
  finite examples and generic symbolic identities. The all-degree statements
  and the reverse containment rest on the proofs. No exhaustive search and no
  proof-assistant verification is claimed.
- Not peer-reviewed; priority not established; the comparisons with Shaska
  and Gao are targeted, not universal priority claims (Part II's source
  review is the delivered `02-affine-slope-SOURCES.md`). The research
  directions are proposals, not published problems.
- Added at the batch-36 write: the project's statements are those of the pin,
  which equal those of the placement commit; the credit for the determinant
  identity and the collision mechanism is the project's; Gao's degree four
  is geometric; Shaska and the Stacks Project references were not checked;
  the proofs were read at the write, which is not an independent review.
  Added at the batch-44 write: the same holds for Part II (proofs read, not
  independently reviewed; Shaska and Gao not re-read).

## Checks made at the write

Batch 36 (Part I):

- The reverse ideal containment, which the shipped script does not check:
  with SymPy 1.14.0 the 18 coefficient equations of `J(p,q,1+t+v) + 1` and
  the 12 generators of (A.1) have the same reduced grevlex Gröbner basis,
  and each set lies in the ideal of the other. So Theorem 8.1's ideal
  equality holds computationally over `Q`.
- The normalization `F_* = diag(−1/2,−3/2,1/2) ∘ F_0 ∘ diag(1,−2/3,−2)`, and
  `F_*(1,0,−1) = F_*(0,−9,71) = (−1,−9,0)` via the project's mechanism.
- Gao's `G_Gao`: ordinary degrees `(4,11,12)`, `det J_{G_Gao} = 2`.

Batch 44 (Part II), with SymPy 1.14.0, independently of the shipped script:

- the normal form (N) with symbolic `β, γ` and `e = 1 + βt + e₂t² + e₃t³` has
  Jacobian −1 identically; Proposition 18.2's points `X_1, X_2` have the
  stated common image; Example 18.3 (degrees `(10,9,7)`, collision
  `(1,0,−1), (0,−9,−10) ↦ (−1,−9,0)`);
- Theorem 20.2's identity `J = −1 + ε²v²O(G)`, the formulas (20.5)–(20.6)
  and the quadratic repair (20.14) modulo `ε³`, for `G = t^m`, `0 ≤ m ≤ 4`;
- the cubic `RT³ − 2T² + QT − 2P` vanishes at `τ = y + 1/x` on `F_0`, its
  discriminant is (19.3), and (19.3) equals the sibling report's (2.9);
- the Part I remark 15.3 identity: (N) with `e = 1 + βt`, `γ = 1` is Part I's
  (5.11).

## Relation to the neighbouring reports

- [arithmetic-local-global-fibers](../arithmetic-local-global-fibers/)
  (`alg:`), batch 36 manuscript 03: the same map, studied arithmetically
  (integral, p-adic and 2-adic fibers). No theorem is shared with Part I and
  the two were not merged; their notation clashes (`t`, `h`, `p`, `q`, `u`,
  `k`, `ρ`). Its Remark 9.2 records a third integral point `(1,−2,8)` over the
  project's collision value `(0,−2,0)`, an observation made at the write. Its
  open question on Zariski density in `A³` mentions the weighted symmetry
  this report classifies. **Part II's cubic model** (Proposition 19.1:
  `τ = y + 1/x`, the cubic, `f′(τ) = 2/x` and the discriminant) is that
  report's cubic inverse model (its Section 2, equation (2.9)), which it
  credits to an archived note of `royvanrijn/jacobian-research` and, for the
  fiber law, to Gao's Theorems 3.3–3.4; the generic Galois group `S_3` is not
  stated there. A `[write]` note in Section 19 says so.
- [gao-f6-fiber-geometry](../gao-f6-fiber-geometry/): the fiber geometry of
  Gao's five-dimensional six-sheeted map `F6`, a **different** map, from the
  same Gao paper. "Six-sheeted" is again a geometric degree.

## Build

MiKTeX or TeX Live with lmodern, microtype, geometry, amsmath/amssymb/amsthm,
mathtools, booktabs, array, longtable, enumitem, xcolor, fancyhdr, hyperref,
bookmark, xurl and listings; no figures or bibliography database.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 54 pages, with no errors,
warnings, undefined references or citations, multiply defined labels,
duplicate destinations or overfull boxes. It has two underfull lines
(badness 1005 and 1472), both in Part I source paragraphs and both present
in a build of the committed batch-36 text (28 pages); Part II adds none.

## Rerunning the checks

### Part I

The script writes its JSON record to `--output`, whose default
`verification.json` is relative to the **current directory**. From the
report directory, pass a path outside the repository so that neither the
report root nor `data/` is written:

```sh
python code/verify_results.py --output <scratch>/verification.json
```

It needs Python 3.10 or later and SymPy (`data/requirements.txt` pins
`sympy==1.14.0`; `pip install -r data/requirements.txt`). At the write it was
run so with Python 3.13.5 and SymPy 1.14.0
(`uv run --no-project --with sympy==1.14.0 python`) in about 25 seconds: all
13 check groups passed, the JSON equals `data/verification.json` apart from
line endings, and the printed output equals `data/verification.txt` apart
from line endings and the certificate path in its last line. The JSON embeds
`platform.python_version()`, so a run under another Python version differs in
that field.

### Part II

**Do not run `code/02-affine-slope-verify_results.py` in place.** It does
`from weighted_keller import …`, a name that does not exist under the shipped
names, so it fails with `ImportError`; and if that import were satisfied it
would write `data/verification.json` and `data/verification.txt` beside
`code/`, which in this report are **Part I's records** (it has no output
option). Run it on a copy with the delivered names:

```sh
mkdir -p <scratch>/pkg/code
cp code/02-affine-slope-verify_results.py  <scratch>/pkg/code/verify_results.py
cp code/02-affine-slope-weighted_keller.py <scratch>/pkg/code/weighted_keller.py
cp code/02-affine-slope-__init__.py        <scratch>/pkg/code/__init__.py
cp data/02-affine-slope-requirements.txt   <scratch>/pkg/requirements.txt
cd <scratch>/pkg && python code/verify_results.py
```

It writes `data/verification.json` and `data/verification.txt` inside the
copy; compare them with `data/02-affine-slope-verification.json` and `.txt`.
At the write this was done from the shipped files with
`uv run --no-project --with-requirements requirements.txt python` (Python
3.13.5, SymPy 1.14.0) in about 11 seconds: all 12 groups passed ("12 check
groups passed.") and both records equal the shipped ones apart from line
endings. The JSON embeds the Python version. The randomized examples use the
fixed seed 20260929.

## Discrepancies and delivery names

- Part I: the script's docstring and last line, `data/verification.txt`, and
  Appendix C of `article.tex` use the delivered root layout
  (`python verify_results.py --output verification.json`,
  `Certificate: verification.json`, `requirements.txt`, `article.pdf` at the
  root); a `[write]` note in Appendix C gives the shipped names. Section 8.1
  says the complete equations are "supplied in `verification.json`": that
  file is `data/verification.json`. The delivered PDF typeset `--output` as a
  single dash; the report prints two hyphens (a typographic change only).
- Part II, shipped files that still use delivery names:
  `code/02-affine-slope-verify_results.py` (docstring "Run from the package
  root: python code/verify_results.py"; imports `weighted_keller`; writes
  `data/verification.json`/`.txt`, see "Rerunning");
  `02-affine-slope-STATUS.md` (names `code/verify_results.py`, and says the
  PDF was compiled and rendered — that PDF is not shipped);
  `02-affine-slope-SOURCES.md` (its "Files read: `README.md` … `article.tex`"
  are this report's). The delivered README's example
  `from code.weighted_keller import …` (also printed in Section 21.2) works
  only in a copy with the delivered names; the package's `code/__init__.py`
  makes `code` a package that shadows Python's standard module `code`.
  Sections 21.3 and 25 print the delivered paths, with `[write]` notes giving
  the shipped ones.
- `02-affine-slope-SOURCES.md` says Section 10.2 appears "in the source range
  beginning at line 1280"; at the pin it is at `article.tex:1336-1345` (the
  range the source read began at Section 9.3). It also says the article
  "answers that exact question negatively" (no nonconstant `G`); the report
  phrases the same result as an affirmative answer to "must `G` be constant?".
  Its note that Shaska's weight sign convention is the simultaneous opposite
  of this report's is kept only there.
- The manuscript's bibliography entry for Part I ("prior", at the pin
  `9b24a3a8d`) is replaced by internal references to Part I; its entry for the
  project is `[repo-9b24]`; its Shaska and Gao entries (same versions, v2 and
  v1) are merged with Part I's.

## Provenance

Appendix D of `article.tex` records Part I's manuscript, the pin
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`, the arrival (`e13affd32`) and
placement (`1a1396d4d`) commits, and every editorial change of the batch-36
write; at that placement the manuscript was made a new report, not merged
with manuscript 03 (`arithmetic-local-global-fibers`). Section 12 records Part
II: batch 44 manuscript 04, pin `9b24a3a8d545af9624f6ac455f5b548be62818b6`,
arrival `ae28ea2db`, placement `203016015` as an **addition** (it answers
Section 10.2 and restates Part I's normal forms, so a separate report would
have duplicated them). Where the merge had to choose: Part II goes after Part
I's Conclusion and before its appendices, so no Part I number moves; the
eight manuscript items that duplicate Part I are printed once, in Part I; the
manuscript's letters are kept and disambiguated by Table 1 rather than
renamed, except the renamings listed under "Setting and notation" (the
field, and four groups of letters that clash inside the manuscript
itself); the degree-spectrum proof refers to Part I's; the reconstruction of
branch (N) is kept in full as a second proof. No mathematical statement of
either manuscript was changed.
