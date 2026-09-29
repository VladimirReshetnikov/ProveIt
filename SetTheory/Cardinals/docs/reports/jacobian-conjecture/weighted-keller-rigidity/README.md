# All-Degree Rigidity of a Weighted Keller Class

**Classification, degenerations, and an obstructed double point**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, and in particular that project's research notes
on the weighted class of its map (`Algebra/JacobianConjecture/Research/README.md:180-248`).
It is dated 24 September 2026 and built from one manuscript. Author line:
"Prepared for Vladimir Reshetnikov"; the delivered PDF metadata names the
author as "ChatGPT; prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| — (single source) | batch 36, manuscript 01 | `ProveIt_Weighted_Keller_Rigidity` (inner directory of the same name, main file `article.tex`, 23-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` | the whole of `article.tex`, apart from text marked `[write]` |

Every result, proof, example, table, question and limitation of the
manuscript is printed. **Status: AI-assisted and unrefereed. None of the
report's own results is formalized in Lean or Rocq.** Placement beside the
Lean/Rocq development of the Jacobian project confers no formal status on
it (see "The formal project" below).

```
README.md                    this guide (replaces the delivered README)
article.tex                  the report: the manuscript, labels prefixed, with [write] additions
article.pdf                  the compiled report, 28 pages (unnumbered title page, contents
                             pages 1–2, text pages 3–27, references on pages 26–27)
code/verify_results.py       exact companion checks, 13 groups (SymPy)
data/requirements.txt        the source's pin, sympy==1.14.0
data/verification.json       recorded JSON certificate: equations, matrix, orderings, tangent,
                             rank minor, obstruction vector, cokernel functional
data/verification.txt        recorded output of the run: 13 PASS lines
```

Delivered names: the package had every file at its root. `verify_results.py`
is shipped as `code/verify_results.py`; `verification.json`,
`verification.txt` and `requirements.txt` are shipped under `data/` with
unchanged names; `article.tex` keeps its name and is rewritten. The delivered
README and PDF are not shipped (`article.pdf` is a build of this text). No
checksum manifest was delivered and there was no audit markdown. The files
under `code/` and `data/` are byte-identical to the delivery.

## Labels

Every label in `article.tex` carries the prefix `wkr:`. The source's 96
labels are kept, unchanged after the prefix; six were added at the write
(`wkr:sub:project`, `wkr:sub:gao`, `wkr:app:report`, `wkr:app:onesource`,
`wkr:app:pinned`, `wkr:app:rerun`), 102 in all. The two new subsections
(1.4, 1.5) end Section 1 and Appendix D is new, so no source number moved.
No label has a Lean or Rocq mapping.

## Setting and notation

`K` is a field of characteristic zero. Source weights `(−1,1,2)`, target
weights `(2,1,−1)`; invariants `t = xy`, `v = x²z`; a weighted map is the
lift `L(p,q,r) = (p(t,v)/x², q(t,v)/x, x·r(t,v))`. `F_0` is the project's map
(determinant −2); the report **normalizes** `p_v(0) = q_t(0) = r(0) = 1`,
which makes the determinant **−1**, and writes `r = 1 + βt + γv`. The
normalized representative is
`F_* = F_{1,1} = diag(−1/2, −3/2, 1/2) ∘ F_0 ∘ diag(1, −2/3, −2)`, and
`F_{a,b}` (a two-parameter family) is its diagonal orbit. Watch for these
readings:

- `t = xy` agrees with the project's research notes but **not** with the
  sibling report [arithmetic-local-global-fibers](../arithmetic-local-global-fibers/),
  where `t = y + 1/x`, nor with the family parameter `t` of the project
  README.
- `u` is `1 + xy` in (1.1) but a **tangent vector** from Section 8 on; `h`
  is the project's `h = u²z + y²(1+3u)` in (1.1) but a **source-shear
  polynomial** `h(t)` in `T_h`; `ρ` is the torus parameter; `k` is the
  coefficient in `E = 1 + kt`.
- `a, b` are **family parameters** (`a = β²/γ`, `b = γ/β`), not the
  project's coefficient `a = [t²]p` (Research README line 210; the added
  notes write `α` for it) nor its stable variables `a, b`.
- `A, B, C, D` are coefficient polynomials in `t` (Section 5), not target
  coordinates.

## What the report claims

Theorem numbers are those of the built `article.pdf`.

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

## What the project already had, and whose it is

The manuscript cites the project's research notes for its baseline, but
presents two of their ingredients in its own words without saying so.
Section 1.4 of the report (added at the write) credits them:

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

## Gao's "degree-four" three-dimensional map

The report cites Shuhong Gao (arXiv:2608.00222) for "a three-dimensional map
of degree four" (Section 1.3) and "a three-dimensional degree-four example"
(Section 10.6). **Gao's "degree" there is the geometric degree**, the number
of preimages of a generic point, as his abstract defines it. His
three-dimensional map `G` (Theorem 3.5) has components of ordinary degrees
**4, 11 and 12**, Jacobian determinant 2 and four generic preimages. This was
read from his Section 3.5 at the write and checked with SymPy 1.14.0 from his
printed formulas (degrees `(4,11,12)`, `det J_G = 2`). For Alpöge's map his
Theorem 3.3 gives ordinary degrees `(7,6,4)` and geometric degree three.

So Gao's `G` does **not** lower the ordinary degree of a three-dimensional
Keller counterexample below seven. The report's sentence that forced degree
seven "is compatible with examples outside this class of lower degree"
stays true as a compatibility statement, but `G` is not such an example.
The project's framing is unaffected: its notes say that its finite searches
"do not prove that ordinary degree seven or sixteen monomials is globally
minimal in dimension three", and that a simpler three-variable map would have
degree at least four and, below seven, would break the weighted symmetry
(`Algebra/JacobianConjecture/Research/README.md:12-15` and `:262-269`).
Whether a three-variable Keller counterexample of ordinary degree 4–6 exists
is not settled by any source cited here. Section 1.5 and a `[write]` note in
Section 10.6 of the report say this.

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
  (`Counterexample.v:110`), `jacobian_det_is_minus_two`,
  `counterexample_scaling` (`Scaling.v:32`),
  `jacobian_conjecture_dimension_three_is_false`.

**Nothing else in the report is formalized**: not the weighted determinant
identity (in the project only as a README calculation), not the
normalization `F_* = diag ∘ F_0 ∘ diag`, not the family `F_{a,b}`, and none of
the report's theorems. The project's degree-bound and sparsity results are
SymPy certificates, not kernel proofs.

## What the report does not claim

- No new counterexample to the Jacobian conjecture; no classification of
  unrestricted Keller maps; not the construction of the known map; no
  minimum-degree theorem for all three-variable maps.
- Excluded from the classification: `v²` terms in `p` or `q`, and a
  nonconstant coefficient `G(t)` of `v` in `r` (Sections 6.4, 10.1–10.2).
- The double point and "torus × double point" concern the **degree-seven**
  coefficient scheme only; stabilization of the nonreduced structure at
  higher degree is not proved (Remark 8.5, Section 10.3);
  the gluing at the axes is open (Section 10.4).
- Characteristic zero is essential; nothing is claimed in positive
  characteristic (Section 10.9).
- The script checks one ideal containment (`I ⊆` the displayed ideal, by
  substitution) and four sample shears `h = 1, t, t², t³`; the all-degree
  statements and the reverse containment rest on the proofs. No exhaustive
  search and no proof-assistant verification is claimed.
- Not peer-reviewed; priority not established; the comparison with Shaska
  and Gao is not a universal priority claim. The research directions are
  proposals, not published problems.
- Added at the write: the project's statements are those of the pin, which
  equal those of the placement commit; the credit for the determinant
  identity and the collision mechanism is the project's; Gao's degree four
  is geometric; Shaska and the Stacks Project references were not checked;
  the proofs were read at the write, which is not an independent review.

## Checks made at the write

- The reverse ideal containment, which the shipped script does not check:
  with SymPy 1.14.0 the 18 coefficient equations of `J(p,q,1+t+v) + 1` and
  the 12 generators of (A.1) have the same reduced grevlex Gröbner basis,
  and each set lies in the ideal of the other. So Theorem 8.1's ideal
  equality holds computationally over `Q`.
- The normalization `F_* = diag(−1/2,−3/2,1/2) ∘ F_0 ∘ diag(1,−2/3,−2)`, and
  `F_*(1,0,−1) = F_*(0,−9,71) = (−1,−9,0)` via the project's mechanism.
- Gao's `G`: ordinary degrees `(4,11,12)`, `det J_G = 2`.

## Relation to the neighbouring reports

- [arithmetic-local-global-fibers](../arithmetic-local-global-fibers/)
  (`alg:`), batch 36 manuscript 03: the same map, studied arithmetically
  (integral, p-adic and 2-adic fibers). No theorem is shared and the two
  were not merged; their notation clashes (`t`, `h`, `p`, `q`, `u`, `k`,
  `ρ`). Its Remark 9.2 records a third integral point `(1,−2,8)` over the
  project's collision value `(0,−2,0)`, an observation made at the write.
  Its open question on Zariski density in `A³` mentions the weighted
  symmetry this report classifies.
- [gao-f6-fiber-geometry](../gao-f6-fiber-geometry/): the fiber geometry of
  Gao's five-dimensional six-sheeted map `F6`, a **different** map, from the
  same Gao paper. "Six-sheeted" is again a geometric degree.

## Build

MiKTeX or TeX Live with lmodern, microtype, geometry, amsmath/amssymb/amsthm,
mathtools, booktabs, array, longtable, enumitem, xcolor, fancyhdr, hyperref,
bookmark and xurl; no figures or bibliography database.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 28 pages, with no errors,
warnings, undefined references or citations, multiply defined labels,
duplicate destinations or overfull boxes. It has two underfull lines
(badness 1005 and 1472), both in source paragraphs and both present in a
build of the delivered text, which had 23 pages and one duplicate `page.1`
destination (the title page), fixed at the write.

## Rerunning the checks

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

## Discrepancies and delivery names

- The script's docstring and last line, `data/verification.txt`, and
  Appendix C of `article.tex` use the delivered root layout
  (`python verify_results.py --output verification.json`,
  `Certificate: verification.json`, `requirements.txt`, `article.pdf` at the
  root); a `[write]` note in Appendix C gives the shipped names.
- Section 8.1 says the complete equations are "supplied in
  `verification.json`": that file is `data/verification.json`.
- The delivered PDF typeset `--output` as a single dash; the report now
  prints two hyphens (a typographic change only).

## Provenance

Appendix D of `article.tex` records the manuscript, the pin
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`, the arrival (`e13affd32`) and
placement (`1a1396d4d`) commits, and every editorial change. At placement
the manuscript was made a new report, not merged with manuscript 03
(`arithmetic-local-global-fibers`), and not an addition: the project's
research notes are the project's own documentation, not a report. No
mathematical statement was changed and no symbol renamed.
