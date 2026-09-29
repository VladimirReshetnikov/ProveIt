# Arithmetic Local–Global Dichotomies for ProveIt's Three-Variable Keller Map

**Split integral Hasse failures, a dense parameter family, and exact p-adic fiber laws**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, whose map it studies. It is dated 24 September
2026 and built from one manuscript. Author line: "Research draft prepared for
Vladimir Reshetnikov"; the delivered PDF metadata names the author as
"Research draft prepared with ChatGPT".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| — (single source) | batch 36, manuscript 03 | `ProveIt_Arithmetic_Local_Global` (inner directory `proveit_arithmetic_fibers`, main file `arithmetic_fibers.tex`, 26-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` | the whole of `article.tex`, apart from text marked `[write]` |

Every result, proof, example, table, question and limitation of the
manuscript is printed. **Status: AI-assisted and unrefereed. None of the
report's own results is formalized in Lean or Rocq.** Placement beside the
Lean/Rocq development of the Jacobian project confers no formal status on
it (see "The formal project" below).

```
README.md                         this guide (replaces the delivered README)
SOURCE_REVIEW.md                  the source's review of prior work and novelty boundaries, as delivered
article.tex                       the report: the manuscript, labels prefixed, with [write] additions
article.pdf                       the compiled report, 29 pages (unnumbered title page,
                                  contents pages 1–2, text pages 3–28, references on page 28)
code/rational_inverse.py          complete exact rational inverse of F (SymPy; prints JSON)
code/verify_finite.py             finite local certificates (standard library only)
code/verify_split_plane.py        split-plane gcd and parameter counts (standard library only)
code/verify_symbolic.py           27 exact symbolic identities (SymPy)
data/build_review.json            the source's build and review record for its 26-page PDF
data/finite_checks.json           recorded output of verify_finite.py --output
data/finite_checks.txt            recorded stdout of verify_finite.py
data/inverse_example.json         recorded stdout of rational_inverse.py 0 -4 2
data/split_plane_checks.json      recorded JSON written by verify_split_plane.py
data/split_plane_checks.txt       recorded stdout of verify_split_plane.py
data/symbolic_checks.json         recorded JSON written by verify_symbolic.py
data/symbolic_checks.txt          recorded stdout of verify_symbolic.py
```

Delivered names: `arithmetic_fibers.tex` is shipped as the rewritten
`article.tex`; the delivered `certificates/` directory is shipped as `data/`
with unchanged file names; `code/` keeps its name. The delivered README and
the PDF `arithmetic_fibers.pdf` are not shipped (`article.pdf` is a build of
this text). No checksum manifest was delivered. Every file under `code/` and
`data/` and `SOURCE_REVIEW.md` is byte-identical to the delivery.

## Labels

Every label in `article.tex` carries the prefix `alg:`. The source's 77
labels are kept, unchanged after the prefix; six were added at the write
(`alg:sub:attribution`, `alg:rem:collisionfiber`, `alg:app:report`,
`alg:app:onesource`, `alg:app:pinned`, `alg:app:rerun`), 83 in all. The one
new numbered item, Remark 9.2, is the last of its section, so no source
number moved. No label has a Lean or Rocq mapping.

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
  targets; Zariski density is in the **plane** `C = 2`, not in `A³`;
  `F_{2^m}` (finite fields) is not `Z/2^m`; rational preimages are not
  integral preimages; Python/SymPy checks are not kernel proofs (the
  source's own list of confusions, `SOURCE_REVIEW.md`).

## What the report claims

Theorem numbers are those of the built `article.pdf`.

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

## What is prior work, and whose

The delivered README said that "the map, its Jacobian determinant, its
complex fiber stratification, and its finite-field histograms are prior
results", which can be read as saying that ProveIt contains all four. It
does not. Section 1.3 of the report (added at the write) states the
attribution precisely:

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
- **Candidate new** (priority not established; the source's searches were
  targeted, not a worldwide audit): the split family, the gcd criterion,
  the density `27/(4π²)`, the S-integer persistence, and the dyadic law.

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

**None of the report's theorems is formalized.** The project has nothing on
fiber stratification, finite fields, p-adic or dyadic fibers or Hasse
principles. The report uses the project's definition of `F` and restates
its determinant and collision only as inherited inputs.

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
- The parameter density is not a density in target space (Remark 4.5);
  Zariski density in all of `A³` is open (Research question 12.4).
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

## Relation to the neighbouring reports

- [weighted-keller-rigidity](../weighted-keller-rigidity/) (`wkr:`), batch
  36 manuscript 01: the same map `F`, studied in coefficient space (an
  all-degree classification of its weight-`(−1,1,2)` class and a
  double-point coefficient scheme). No theorem is shared; the two were not
  merged, and their notation clashes (`t`, `h`, `p`, `q`, `u`, `k`, `ρ`
  mean different things).
- [gao-f6-fiber-geometry](../gao-f6-fiber-geometry/): the fiber geometry of
  Gao's five-dimensional six-sheeted map `F6`, a **different** map. It
  cites the same Gao paper; this report's Corollary 2.4 is Gao's result for
  the three-dimensional map `F`.

## Build

MiKTeX or TeX Live with newtx, microtype, booktabs, longtable, aliascnt,
cleveref, enumitem, listings, fancyhdr, xurl and hyperref; no shell escape,
figures or bibliography database.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 29 pages, with no errors, warnings,
undefined references or citations, multiply defined labels, duplicate
destinations, or overfull or underfull boxes. The delivered text built to 26
pages with one duplicate `page.1` destination (the title page), fixed at the
write.

## Rerunning the checks

Run on a copy with the **delivered** layout, never in the report:
`code/verify_split_plane.py` and `code/verify_symbolic.py` always write
`split_plane_checks.json` and `symbolic_checks.json` into `../certificates/`
relative to their own directory, and fail with `FileNotFoundError` (after
passing their checks) if it does not exist.

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
`rational_inverse.py` need SymPy. No requirements file was delivered; the
recorded runs used Python 3.13.5 and SymPy 1.14.0 (`data/build_review.json`).
At the write these commands were run on such a copy with Python 3.13.5 and
SymPy 1.14.0 (`uv run --no-project --with sympy==1.14.0 python`): all exit 0,
and every regenerated file equals the shipped one apart from Windows line
endings. `data/build_review.json` is a static record, not regenerated.
`verify_finite.py` also exports `congruence_preimage(n, modulus)`, the CRT
construction of Corollary 3.4 (trial-division factoring, for moderate moduli).

## Discrepancies and delivery names

- `SOURCE_REVIEW.md` is the source's review, as delivered: it lists what was
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
- The article's replay commands use `python3`; on this Windows machine use
  `py` or `uv run --no-project python`.

## Provenance

Appendix C of `article.tex` records the manuscript, the pin
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`, the arrival (`e13affd32`) and
placement (`1a1396d4d`) commits, and every editorial change. At placement
the manuscript was made a new report, not merged with manuscript 01
(`weighted-keller-rigidity`): the two share the map but no theorem, and
their notation clashes. No mathematical statement was changed and no symbol
renamed.
