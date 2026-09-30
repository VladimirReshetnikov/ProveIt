# Arithmetic Local–Global Dichotomies for ProveIt's Three-Variable Keller Map

**Split integral Hasse failures, a dense parameter family, and exact p-adic
fiber laws** — with Part II, **Zariski-dense integral Hasse failures:
complete split-fiber criteria and sharp target-height asymptotics**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, whose map it studies. It is built from two
manuscripts: Part I, dated 24 September 2026, author line "Research draft
prepared for Vladimir Reshetnikov" (the delivered PDF metadata names the
author as "Research draft prepared with ChatGPT"); and Part II, dated
29 September 2026 and added on 30 September 2026, author line and PDF
metadata "AI-assisted research draft prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | batch 36, manuscript 03 | `ProveIt_Arithmetic_Local_Global` (inner directory `proveit_arithmetic_fibers`, main file `arithmetic_fibers.tex`, 26-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` (new report) | Sections 1–13 and Appendices A–C.3 of `article.tex`, apart from text marked `[write]` |
| Part II | batch 58, manuscript 01 | `ProveIt_Dense_Integral_Hasse` (inner directory of the same name, main file `article.tex`, 20-page US-Letter PDF; delivered in `b2b626d85`) | `1085b506d` | `b30441a8c` (addition, prefix `02-dense-hasse-`) | Sections 15–27 of `article.tex`, apart from text marked `[write]`; Section 14 and Appendices C.4–C.5 are new |

Every host passage Part II cites (Sections 2, 4 and 12 and Research
questions 12.2–12.4) is unchanged from its pin `1085b506d` to the placement
commit. Every result, proof, example, table, question and limitation of
both manuscripts is printed; nothing was merged across the Parts. **Status:
AI-assisted and unrefereed. None of the report's own results is formalized
in Lean or Rocq.** Placement beside the Lean/Rocq development of the
Jacobian project confers no formal status on it (see "The formal project"
below).

```
README.md                                  this guide (replaces both delivered READMEs)
SOURCE_REVIEW.md                           Part I's review of prior work and novelty boundaries, as delivered
02-dense-hasse-SOURCES.md                  Part II's source and attribution ledger, as delivered
02-dense-hasse-STATUS.md                   Part II's proof, novelty and computation boundaries, as delivered
article.tex                                the report: both manuscripts, labels prefixed, with [write] additions
article.pdf                                the compiled report, 56 pages (unnumbered title page,
                                           contents pages 1–4, Part I pages 5–27, Part II pages 28–49,
                                           appendices pages 50–54, references page 55)
code/rational_inverse.py                   Part I: complete exact rational inverse of F (SymPy; prints JSON)
code/verify_finite.py                      Part I: finite local certificates (standard library only)
code/verify_split_plane.py                 Part I: split-plane gcd and parameter counts (standard library only)
code/verify_symbolic.py                    Part I: 27 exact symbolic identities (SymPy)
code/02-dense-hasse-Makefile               Part II's delivered Makefile (names delivered paths)
code/02-dense-hasse-count_heights.py       Part II: exact height counts and constants (NumPy, mpmath)
code/02-dense-hasse-split_fibres.py        Part II: exact split fibers, local tests, exceptions, witnesses (standard library)
code/02-dense-hasse-verify_results.py      Part II: twelve groups of exact checks (SymPy, NumPy)
data/build_review.json                     Part I's build and review record for its 26-page PDF
data/finite_checks.json                    recorded output of verify_finite.py --output
data/finite_checks.txt                     recorded stdout of verify_finite.py
data/inverse_example.json                  recorded stdout of rational_inverse.py 0 -4 2
data/split_plane_checks.json               recorded JSON written by verify_split_plane.py
data/split_plane_checks.txt                recorded stdout of verify_split_plane.py
data/symbolic_checks.json                  recorded JSON written by verify_symbolic.py
data/symbolic_checks.txt                   recorded stdout of verify_symbolic.py
data/02-dense-hasse-build_review.json      Part II's build and review record for its 20-page PDF
data/02-dense-hasse-example.json           recorded stdout of split_fibres.py 1 1 3 --modulus 18144000
data/02-dense-hasse-height_counts.json     recorded output of count_heights.py (c = 1,2,3,4,8; T = 10^3,10^4,10^5)
data/02-dense-hasse-height_counts.txt      the same table as text
data/02-dense-hasse-requirements.txt       sympy==1.14.0, numpy==2.3.5, mpmath==1.3.0
data/02-dense-hasse-verification.json      recorded output of verify_results.py (12 groups PASS)
data/02-dense-hasse-verification.txt       a captured console log of verify_results.py (another run)
```

Delivered names, Part I: `arithmetic_fibers.tex` is shipped as the
rewritten `article.tex`; the delivered `certificates/` directory is shipped
as `data/` with unchanged file names; `code/` keeps its name. Part II: its
`article.tex` is printed as Part II of `article.tex`; `SOURCES.md`,
`STATUS.md`, `Makefile`, `requirements.txt`, `code/*.py` and `data/*` are
shipped with the prefix `02-dense-hasse-` (the Makefile under `code/`, the
requirements file under `data/`). Neither delivered README nor delivered PDF
(`arithmetic_fibers.pdf`, Part II's `article.pdf`) is shipped; `article.pdf`
is a build of this text. No checksum manifest was delivered. Every file
under `code/` and `data/`, `SOURCE_REVIEW.md` and the two `02-dense-hasse-*.md`
files are byte-identical to the deliveries.

## Labels

Every label in `article.tex` carries the prefix `alg:`. Part I's source had
77 labels, kept unchanged after the prefix; six were added at its write
(`alg:sub:attribution`, `alg:rem:collisionfiber`, `alg:app:report`,
`alg:app:onesource`, `alg:app:pinned`, `alg:app:rerun`). Part II's labels
carry the sub-prefix `alg:dh:`: its 70 labels, unchanged after the prefix,
and 20 added at its write (Section 14 and its subsections, the notation
table, the seven research questions, the Conclusion and two appendix
sections of Part II, and Appendices C.4–C.5). Five labels were added to
existing subsections of Part I's Section 12 (`alg:sub:q-dyadic`,
`alg:sub:q-split`, `alg:sub:q-height`, `alg:sub:q-density`,
`alg:sub:q-library`). 178 in all (83 before Part II); no label was renamed
or removed, and no Part I number moved. No label has a Lean or Rocq mapping.

## Setting and notation

`F = (P, Q, R)` is literally the project's map (`u = 1+xy`,
`h = u²z + y²(1+3u)`, `F = (uh, y+3xh, x(5−3u−x²z))`, `det JF = −2`, no
rescaling). The inverse coordinate is `t = y + 1/x`, a root of the cubic
`g_{A,B,C}(T) = CT³ − 2T² + BT − 2A` with `g′(t) = 2/x`; a target is
`b = (A, B, C)`. Watch for these readings:

- The report's `t = y + 1/x` is **not** the `t = xy` of
  `Algebra/JacobianConjecture/Research/README.md` (and of the sibling
  report `weighted-keller-rigidity`), nor the family parameter `t` of the
  project README (written `τ` in the report's Remark on the collision
  fiber).
- Its `p` is a prime and `q` a finite-field size, **not** the project's
  `p = xy²`, `q = x²yz` of the stable shear.
- Density `27/(4π²)` counts **ordered root parameters** `(a, b)`, not
  targets; Zariski density is in the **plane** `C = 2`, not in `A³`
  (Part I; Part II extends it to every plane `C = c ≠ 0` and so to `A³`);
  `F_{2^m}` (finite fields) is not `Z/2^m`; rational preimages are not
  integral preimages; Python/SymPy checks are not kernel proofs (the
  source's own list of confusions, `SOURCE_REVIEW.md`).
- **Part II keeps its manuscript's letters**, fixed against Part I in
  Table 1 (Section 14.4). Above all: Part II's `c` is the **fixed third
  target coordinate**, whereas Part I's `c` is the third integer root
  (`a+b+c = 1`); Part II's `a, b, r` are **numerators** of the roots
  (`a+b+r = 2`, roots `a/c, b/c, r/c`); its `Φ(c,s,t)` is three-parameter,
  and `Φ(2,a,b)` is Part I's `Φ(a,b)`; its `ρ(c)` is a density of numerator
  pairs, not Part I's image measure `ρ_p`; its `T` is both the height bound
  and the indeterminate of `g`. The manuscript's sum `S` (of two roots or
  half-numerators) is printed `Σ`, because `S` is the finite set of primes;
  nothing else was renamed.

## What the report claims

Theorem numbers are those of the built `article.pdf`.

**Part I.**

- **An explicit integral Hasse failure (Theorem 3.1).** For every `n ≥ 2`,
  `b_n = (0, −2n(n−1), 2)` has a preimage in `Z_p³` for every prime `p`, and
  in `Q³`, but none in `Z³`; the complete geometric fiber is three rational
  points with denominators `n(n−1)`, `n(2n−1)`, `(n−1)(2n−1)` (up to sign).
  At `n = 2`: `F⁻¹(0,−4,2) = {(−1/2,2,36), (1/6,−4,−288), (1/3,−4,0)}`.
  Every congruence is solvable (Corollary 3.4).
- **The split plane (Theorem 4.1).** For distinct integers `a, b, c` with
  `a+b+c = 1`, the target `(abc, 2(ab+ac+bc), 2)` has no integral preimage,
  and is locally soluble everywhere iff `gcd(a−b, 3a−1) = 1`; the gcd of the
  three denominators is `g²`. Locally soluble parameters have density
  `27/(4π²) ≈ 0.683918` (Theorem 4.3) and their targets are Zariski dense in
  `C = 2` (Corollary 4.4).
- **Persistence.** Over every `Z[S⁻¹]` (Theorem 5.1, Corollary 5.2), under
  integral stable equivalence (Proposition 5.3), and in the profinite
  closure `F(Ẑ³) = ∏ F(Z_p³)` (Theorem 5.4).
- **Rational Hasse principle (Theorem 6.2)** over every number field, via
  qualitative Chebotarev; an exact rational inverse algorithm
  (`code/rational_inverse.py`).
- **Exact inverse ball (Lemma 8.1, Corollary 8.2)** at every precision, and
  the odd-prime image measure `ρ_p` (7/9 at `p = 3`).
- **Dyadic law (Theorem 9.1).** The integral 2-adic fiber size is determined
  modulo 8, with law `(21, 7, 3, 1)/32` for sizes 0–3 and image measure
  `11/32`; modulo 4 does not suffice. Over `(Z/2^m)³`, `m ≥ 3`, the fiber
  sizes are 0, 2, 4, 6 with the same proportions.
- **Sparse images.** `F(Ẑ³)` has Haar measure zero yet contains the Zariski
  dense split-plane family (Theorem 10.1); integral targets in `F(Q³)` have
  density zero, with `A(H) ≪ H³ exp(−c√log H)` (Theorem 10.3).
- **Proposed work.** A four-layer formalization plan (Section 11.3) and
  nine research questions (Section 12).

**Part II** (Research question 12.4 answered; 12.3 and 12.2 in the
completely split sector only; Section 14.2 states the scope).

- **Density in every nonzero slice (Theorem 15.2).** For every nonzero
  integer `c`, the integral Hasse failures are Zariski dense in the plane
  `C = c`, hence in `A³`. The plane `C = 0` has none:
  `F(0, B, A−4B²) = (A, B, 0)`. The dense family can be chosen globally
  insoluble over any prescribed `Z[S⁻¹]` (Theorem 19.3).
- **An explicit family (Theorem 19.1).** For `c ≠ 0`, odd `n > 0` and
  `k ≡ 2 (mod 4)`, `k ≥ 6`, the target `Φ(c, nk, n(k−1))` is an integral
  Hasse failure with exactly three rational preimages, none with integral
  first coordinate; its Jacobian in the parameters is nonzero, which gives
  the density. Example 19.2: `Φ(1,1,3) = (−3,−5,1)`, fiber
  `(−1/3,4,81)`, `(1/5,−2,−45)`, `(2/15,−19/2,−765/8)`.
- **Complete local criterion for split fibers (Theorem 18.2).** For distinct
  numerators with integral coefficients, local solubility everywhere means:
  at odd primes, the coefficient integrality (Lemma 17.1: three residue
  classes modulo `p^ν`) and one gcd condition, `gcd(a−b, 3a−2)` has no odd
  prime factor outside `c` (Proposition 17.2); at 2, a condition depending on
  `v₂(c)` (residues `{1,2,3}` mod 4 for odd `c`; exactly one odd
  half-numerator for `v₂(c) = 1`; none for `v₂(c) ≥ 2`), with dyadic density
  `σ(v₂(c))`.
- **Finitely many integral split fibers per slice (Theorem 20.1)**, found by
  a divisor enumeration over the divisors of `2|c|`; the printed table has
  one each for `c = 1, 3, 4, 12` and none for `c = 2, 8, 16`.
- **Sharp counting (Theorem 15.3).** In square boxes `|A|, |B| ≤ T`, the
  completely split integral Hasse failures on `C = c` number
  `#H^sp_c(T) ~ κ(c) T^{2/3}`, with `κ(c) = I (2c²)^{2/3} ρ(c)`,
  `I = Γ(1/3)²/(2Γ(2/3))` and `ρ(c)` an explicit Euler product;
  `κ(2) = 27Γ(1/3)²/(8π²Γ(2/3)) ≈ 1.81235`. The proof uses a lattice sieve
  in bounded regions (Lemma 21.1) and a cusp bound (Lemma 22.1).
- **Consistency with Part I** (checked at the write; Section 14.3):
  `Φ(2,a,b)` is Part I's `Φ(a,b)`; `ρ(2) = 27/(16π²)` is a quarter of Part I's
  `27/(4π²)` and the integer-root density `δ(2)` equals it; at `c = 2` the
  two local criteria coincide; `176/512 = 11/32`; `C = 0` agrees with Part I's
  boundary point; no integral split fiber on `C = 2`.
- **Proposed work.** Seven research questions (Section 24; two of them
  overlap Part I's 12.1 and 12.9 and say so) and a Lean/Rocq order
  (Section 23.3).

## What is prior work, and whose

The delivered README of Part I said that "the map, its Jacobian
determinant, its complex fiber stratification, and its finite-field
histograms are prior results", which can be read as saying that ProveIt
contains all four. It does not. Section 1.3 of the report (added at the
write) states the attribution precisely:

- **The map** is Alpöge's. ProveIt formalizes it, its determinant and its
  collisions (next section).
- **The complex fiber stratification** (sizes 3, 1, 0; Corollary 2.4) is
  Shuhong Gao, arXiv:2608.00222v1, Theorems 3.3–3.4. It is **not** in
  ProveIt. At the write it was checked on arXiv that Gao's Theorem 3.3
  concerns this very map (component degrees 7, 6, 4, determinant −2, three
  generic preimages) and that his `c₃` is `−Δ/4` for the report's
  discriminant.
- **The cubic inverse model and the finite-field histograms**
  (Theorem 7.1, the count (7.4)) are from the archived note
  `research/archive/legacy-notes/FINITE_FIELD_VALUE_DISTRIBUTION.md` of
  `royvanrijn/jacobian-research` at `caf5685d`. They are **not** in ProveIt.
  At the write the pinned note was checked to state the same `t = y + 1/x`,
  the same cubic and the formulas (7.1)–(7.2). The report reproves them.
- **Candidate new in Part I** (priority not established; the source's
  searches were targeted, not a worldwide audit): the split family, the gcd
  criterion, the density `27/(4π²)`, the S-integer persistence, and the
  dyadic law.
- **Part II** claims no priority for the map, the inverse cubic, or Part I's
  `C = 2` family and its density; its candidate new contributions (relative
  to the sources it inspected, `02-dense-hasse-SOURCES.md`; worldwide
  priority not certified) are the all-slice density, the split-fiber local
  criteria, the finiteness of integral split fibers, and the counting
  theorem. Its restatements of Part I (map, chart, complete inverse,
  determinant) are marked as such in Section 14.5.

## The formal project

`Algebra/JacobianConjecture` proves, with kernel-checked Lean 4 and
Rocq/Coq, statements about exactly this map. In Lean (namespace
`LeanProofs.JacobianCounterexample`):

- the map `counterexample` (`Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean:95-101`);
- `jacobianDet_counterexample` (`:134`, `det = −2` over every commutative
  ring);
- the integral collision `collision₀ = (−1,1,5)`, `collision₁ = (0,−2,−16)`,
  `collisionValue = (0,−2,0)`, `collision`, `collision_points_distinct`
  (`:143-170`);
- `counterexample_not_injective`, `counterexample_has_no_polynomial_inverse`,
  `jacobianConjectureInDimensionThree_false`, `jacobianConjecture_false`
  (`:178-217`);
- the mirror symmetry and the rational triple collision over `(−1/4,0,0)`
  (`Equivariance.lean`: `counterexample_equivariant`,
  `counterexample_triple_collision`);
- the torus action `counterexample_scaling`,
  `F(x/s, sy, s²z) = (s²P, sQ, R/s)` (`Scaling.lean:35`), and the collision
  family `collisionFamily` (`CollisionFamily.lean:77`);
- the stabilization and the kernel-checked degree-six stable map
  (`Stabilization.lean`, `SimplerCounterexample.lean`).

The Coq development (`Algebra/JacobianConjecture/Coq/`) proves the
corresponding statements (`counterexample` at `Counterexample.v:110`,
`jacobian_det_is_minus_two`, `counterexample_scaling`,
`jacobian_conjecture_dimension_three_is_false`). The project's lower-degree
stable representatives (degrees 5, 4, 3) have SymPy certificates only
(`Algebra/JacobianConjecture/Research/README.md:97-178`); Proposition 5.3
transports the report's obstruction to them with that status.

**None of the report's theorems is formalized**, in either Part. The
project has nothing on fiber stratification, finite fields, p-adic or dyadic
fibers, Hasse principles or counting. The report uses the project's
definition of `F` and restates its determinant and collision only as
inherited inputs. Part II cites `Counterexample.lean` as a file only (its
bibliography entry, pinned to `1085b506d`), names no declaration, and
relies on none; it reproves the determinant (Proposition 16.2). Its
Lean/Rocq route (Section 23.3) is a proposal.

## An intake observation: a third integral point over the project's collision value

This is **not** a claim of the manuscript; it was observed and checked at
the write, and is printed as Remark 9.2 (marked `[write]`). By the
report's complete inverse (Theorem 2.2) the fiber over the project's
collision value `(0,−2,0)` is

```
F⁻¹(0,−2,0) = {(−1,1,5), (0,−2,−16), (1,−2,8)},
```

three integral points, so `F` has an integral **triple** collision. The
project records and formalizes only the first two. Checked with SymPy
1.14.0: all three evaluate to `(0,−2,0)`, and a lex Gröbner basis of
`{P, Q+2, R}` is zero-dimensional with `x`-polynomial `x(x−1)(x+1)`, so there
is no fourth geometric point; the delivered `code/rational_inverse.py 0 -2 0`
returns the same three points, all integral. Along the project's family,
whose parameter (`t` in the project README) the remark writes `τ` to keep it
apart from the report's root `t = y + 1/x`,
`F(τ,−1/τ,5/τ²) = F(0,2/τ,−16/τ²) = (0,2/τ,0)` and the third point is
`(−τ, 2/τ, 8/τ²)`. The torus action at `s = −1/2` carries the three points
to the fiber over `(0,1,0)` that the report prints in Section 9.2,
`(2,−1/2,5/4)`, `(0,1,−4)`, `(−2,1,2)`, whose two integral points have
largest coordinate 4, against 16 for the project's collision. A Lean or Rocq
statement of the triple collision would be a small follow-up in the
project; nothing here formalizes it.

## What the report does not claim

- No new disproof of the Jacobian conjecture, no solution of the plane
  Jacobian problem, no claim to the map.
- The integral counterexamples **have rational preimages**: they are not
  rational Hasse failures and do not contradict the degree-five examples of
  `royvanrijn/jacobian-research` with no rational point (a different map,
  used only for comparison). No general Hasse theorem for polynomial maps.
- The parameter density is not a density in target space (Remark 4.5).
  Zariski density in all of `A³` was open at the pin (Research question
  12.4); Part II proves it (every plane `C = c ≠ 0`), and shows that the
  plane `C = 0` has no integral Hasse failure.
- The rational Hasse theorem uses Chebotarev as an external theorem
  (Milne, Theorem 8.31); the quantitative sieve uses Bertrand; the
  explicit family uses neither. The thin-image bound is not advertised as
  optimal.
- The dyadic law has a finite computational component (the 512-class
  table, checked pointwise) plus the analytic inverse-ball lemma.
- The scripts check finite ranges only; the universal statements rest on
  the proofs. Stable representatives keep the proof status the project
  documents; SymPy certificates are not upgraded to kernel proofs.
- The formalization plan is a proposal; the research questions are
  proposals, not published problems; no priority is certified.
- Added at the write: the project's statements are those of the pin, which
  equal those of the placement commit (the project did not change in
  between); the attribution checks of Gao and the royvanrijn note were
  made from their arXiv and GitHub texts; Milne was not re-checked; the
  proofs were read at the write, which is not an independent review.
- **Part II** does not count fibers with one rational point and an
  irreducible quadratic pair; its asymptotic is for **square** boxes
  `|A|, |B| ≤ T` only (Research question 12.3 asks for boxes
  `|A| ≤ H_A`, `|B| ≤ H_B`; unequal sides remain open), for each fixed `c`,
  with no uniformity in `c` and no power-saving error term. The
  manuscript's own sentence "This settles the completely split sector of the
  prior report's Research Question 12.3" omitted the square-box restriction;
  the report prints it with the restriction, marked `[write]`.
- Part II's decimals (the `ρ(c)`, `κ(c)` table and the ratios in the count
  table) are illustrative, not interval-certified. Convergence is visibly
  slow: at `T = 10⁵` the normalized count for `c = 2` is 1.534 against
  `κ(2) ≈ 1.812`, since the cusp cutoff `T^{1/2}` is only `T^{1/6}` below
  `T^{2/3}`. The finite counts are not used to infer the asymptotic.
- Part II claims nothing about the map, the inverse cubic or Part I's
  `C = 2` density; it certifies no priority; it is not a Lean or Rocq
  formalization, and its SymPy and NumPy checks are not kernel proofs; the
  existing formal developments were not rebuilt for it. Its proofs were read
  at the write, and its ten counts for `T = 10³, 10⁴` were reproduced by an
  independent enumeration (Section 14.3); that is not an independent review.

## Relation to the neighbouring reports

- [weighted-keller-rigidity](../weighted-keller-rigidity/) (`wkr:`), batch
  36 manuscript 01 with a batch-44 Part II: the same map `F`, studied in
  coefficient space (an all-degree classification of its weight-`(−1,1,2)`
  class and a double-point coefficient scheme). No theorem is shared; the
  two were not merged, and their notation clashes (`t`, `h`, `p`, `q`, `u`,
  `k`, `ρ` mean different things). Part II of this report read its README
  (`02-dense-hasse-SOURCES.md`) and shares no theorem with it either.
- [gao-f6-fiber-geometry](../gao-f6-fiber-geometry/): the fiber geometry of
  Gao's five-dimensional six-sheeted map `F6`, a **different** map. It
  cites the same Gao paper; this report's Corollary 2.4 is Gao's result for
  the three-dimensional map `F`.

## Build

MiKTeX or TeX Live with newtx, microtype, booktabs, longtable, aliascnt,
cleveref, enumitem, listings, fancyhdr, needspace, xurl and hyperref; no
shell escape, figures or bibliography database.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX, US Letter) has 56 pages, with no errors,
warnings, undefined references or citations, multiply defined labels,
duplicate destinations, or overfull or underfull boxes. Every Part I label
keeps its number (compared with a build of the committed text); Part I's
text moved two pages later because the contents grew from two pages to
four, and its appendices now follow Part II. The delivered Part I text built to 26 pages with one
duplicate `page.1` destination (the title page), fixed at its write.

## Rerunning the checks

**Part I.** Run on a copy with the **delivered** layout, never in the
report: `code/verify_split_plane.py` and `code/verify_symbolic.py` always
write `split_plane_checks.json` and `symbolic_checks.json` into
`../certificates/` relative to their own directory, and fail with
`FileNotFoundError` (after passing their checks) if it does not exist.

```sh
mkdir <scratch>                      # outside the repository
cp -r code <scratch>/code
cp -r data <scratch>/certificates
cd <scratch>
python code/verify_finite.py --output certificates/finite_checks.json > certificates/finite_checks.txt
python code/verify_split_plane.py > certificates/split_plane_checks.txt
python code/verify_symbolic.py > certificates/symbolic_checks.txt
python code/rational_inverse.py 0 -4 2 > certificates/inverse_example.json
python code/rational_inverse.py 0 1 0
python code/rational_inverse.py 4/27 4/3 1      # an empty geometric fiber
```

`verify_finite.py` and `verify_split_plane.py` need only the standard
library (Python 3.10 or later); `verify_symbolic.py` and
`rational_inverse.py` need SymPy. No requirements file was delivered with
Part I; the recorded runs used Python 3.13.5 and SymPy 1.14.0
(`data/build_review.json`). At its write these commands were run on such a
copy with Python 3.13.5 and SymPy 1.14.0
(`uv run --no-project --with sympy==1.14.0 python`): all exit 0, and every
regenerated file equals the shipped one apart from Windows line endings.
`data/build_review.json` is a static record, not regenerated.
`verify_finite.py` also exports `congruence_preimage(n, modulus)`, the CRT
construction of Corollary 3.4 (trial-division factoring, for moderate moduli).

**Part II.** Run on a copy with the **delivered** names, never in the
report: `count_heights.py` does `from split_fibres import …`, which fails
under the shipped prefixed name, and `verify_results.py` and
`count_heights.py` write `verification.json`, `example.json` and
`height_counts.{json,txt}` into `../data/` relative to their own directory
(Appendix C.5 of the article).

```sh
W=/path/to/scratch; mkdir -p "$W/code" "$W/data"     # outside the repository
for f in count_heights split_fibres verify_results; do cp "code/02-dense-hasse-$f.py" "$W/code/$f.py"; done
cd "$W"
uv run --no-project --with sympy==1.14.0 --with numpy==2.3.5 --with mpmath==1.3.0 python code/verify_results.py
uv run --no-project --with numpy==2.3.5 --with mpmath==1.3.0 python code/count_heights.py
py code/split_fibres.py 1 1 3 --modulus 18144000
```

At the write (30 September 2026; Python 3.13.5 under `uv`, SymPy 1.14.0,
NumPy 2.3.5, mpmath 1.3.0) all twelve groups passed (1.5 s); the
regenerated `verification.json` and `height_counts.json` equal
`data/02-dense-hasse-verification.json` and
`data/02-dense-hasse-height_counts.json` apart from their `elapsed_seconds`
fields and Windows line endings (`Path.write_text` writes CRLF on Windows;
compare modulo CR), and `height_counts.txt` is identical apart from line
endings. The regenerated `example.json` is `data/02-dense-hasse-example.json`
without its `"modular_witness"` block; the third command prints exactly the
shipped file. `count_heights.py --c … --heights …` overwrites the default
`../data/height_counts.json`; pass `--output` to keep a table elsewhere.
`split_fibres.py` needs only the standard library; its positional arguments
are `c`, `a`, `b` (root numerators), not target coordinates.

## Discrepancies and delivery names

- `SOURCE_REVIEW.md` is Part I's review, as delivered: it lists what was
  read at the pin (the root README, the project README and
  `Algebra/JacobianConjecture/Research/README.md`), Gao, the two royvanrijn
  notes and Milne. Its statements are accurate at the pin and at the
  placement commit.
- `data/build_review.json` describes the delivered 26-page PDF (not shipped)
  and a rendering tool outside ProveIt; it records
  `"new_Lean_or_Rocq_proofs_compiled": false`.
- Appendix A of `article.tex` and Section 11.1 still name
  `arithmetic_fibers.tex`, `arithmetic_fibers.pdf` and `certificates/`, as
  delivered; `[write]` notes there give the shipped names.
- The articles' replay commands use `python3` (Part I) and `python`
  (Part II); on this Windows machine use `py` or `uv run --no-project python`.
- `02-dense-hasse-SOURCES.md` and `02-dense-hasse-STATUS.md` are as
  delivered: they name `article.tex`, `code/verify_results.py`,
  `code/count_heights.py` and `data/` by their delivery names (the article
  they mean is Part II here). `02-dense-hasse-STATUS.md` says the counting
  result "resolves the completely split sector of the target-height
  question, for fixed `c`" without the square-box restriction (see above).
  Both call this report's Part I "the prior repository arithmetic report"
  and cite its Section 12.4 as open, which it was at their pin.
- `code/02-dense-hasse-Makefile` names the delivered `article.tex`,
  `code/verify_results.py` and `code/count_heights.py` and runs bare
  `python`; do not run it in the report: its `verify` and `counts` targets
  name unshipped paths, and its default target would rebuild `article.pdf`
  (now the whole report) with bare `pdflatex`, leaving auxiliary files
  beside it.
- `data/02-dense-hasse-example.json` is not what `verify_results.py`
  writes: it is the standard output of `split_fibres.py 1 1 3 --modulus
  18144000` (identical at the write), with a `"modular_witness"` block that
  `verify_results.py`'s `example.json` lacks.
- `data/02-dense-hasse-verification.txt` is a captured console log
  ("0.524 seconds") of a different run from the one that wrote
  `data/02-dense-hasse-verification.json` (`"elapsed_seconds": 0.511`); no
  program writes the `.txt` file.
- `data/02-dense-hasse-build_review.json` describes the delivered 20-page
  PDF (not shipped); it records `"formalization_status": "No new Lean or
  Rocq formalization; original repository proofs not rebuilt"`.

## Provenance

Appendix C of `article.tex` records both manuscripts. Part I (C.1–C.3): the
pin `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`, the arrival (`e13affd32`)
and placement (`1a1396d4d`) commits, and every editorial change; at
placement it was made a new report, not merged with manuscript 01
(`weighted-keller-rigidity`): the two share the map but no theorem, and
their notation clashes. Part II (C.4–C.5): the pin
`1085b506d65e207a05b7e9c861bb1fe88432fe38`, the arrival (`b2b626d85`) and
placement (`b30441a8c`) commits, the mapping of delivered to shipped files,
every editorial change and the choices made: it became Part II of this
report, not a new report, because it studies the same map through the same
chart and cubic and extends Part I's `C = 2` family; its restatements of
Part I are kept in place and marked; its sum `S` was renamed `Σ` rather than
renaming the height `T`; and its counting claim is printed with the
square-box restriction. No mathematical statement of either manuscript was
changed. Dated notes (30 September 2026, batch 58) were added after Part I's
Research questions 12.2, 12.3 and 12.4, on the title page and in
Appendices A and C.1.
