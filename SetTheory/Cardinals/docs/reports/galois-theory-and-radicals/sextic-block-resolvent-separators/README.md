# Finite Separators and Discriminant Factorizations for Sextic Block Resolvents

**A sharp 196-point guarantee and a bounded replacement for ProveIt's separating-invariant search; Part II: radical-solvability tests without separating sextic resolvents; Part III: the missing zero-parameter test**

A research report of ProveIt's research-report collection, dated 28–30
September 2026, built from three manuscripts, all "prepared for Vladimir
Reshetnikov". Part I is the original report. Part II shows that the Boolean
radical-solvability decision for an irreducible sextic needs no separating
parameter at all: one triple test at any parameter, or matching tests at
three distinct parameters, decide it. Part III reduces the matching tests to
one, the compressed test at `t = 0`, or to two at any distinct parameters,
and shows that a nonsolvable sextic has at most one
false-positive matching parameter, never zero. The report continues the
formal project `Algebra/PolynomialFormulas` (the Lean/Rocq sextic
radical-solvability decision), but it is not part of that development.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batches 40–41 intake, batch 41, manuscript 03 | `ProveIt_Finite_Sextic_Separators` (main file `article.tex`, 24-page Letter PDF, 11 files) | `e2b1f016a` | `9754e8360` | `eaf787d50` | Part I: Sections 1–17 and Appendices A–B |
| 02 | batch 57, manuscript 03 (*Three Plus One: Radical-Solvability Tests Without Separating Sextic Resolvents*, 29 September 2026, 22-page Letter PDF, 11 files) | `ProveIt_Three_Plus_One_Resolvents` (inner directory of the same name, main file `article.tex`) | `e47ed8547` | `6ad01e9c8` | `70b39943a` (prefix `02-three-plus-one-`) | Part II: Sections 19–31 and Appendices C–E (Section 18 is the write's) |
| 03 | batch 70, manuscript 04 (*The Missing Zero-Parameter Test: Collision certificates, affine-rank rigidity, and a two-resolvent sextic criterion*, 30 September 2026, 20-page Letter PDF, 16 files) | `ProveIt_Zero_Parameter_Sextics` (inner directory of the same name, main file `article.tex`) | `1156651a9` | `1b3960d8a` | `51c6943bf` (prefix `03-zero-parameter-`) | Part III: Sections 33–45 and Appendices F–G (Section 32 is the write's) |

Source 01's pin is the full commit `e2b1f016a94102663f12b970e6dd434229f90d01`
(the article's `\snapshot` macro). `Algebra/PolynomialFormulas` has no commit
between that pin and its placement commit, so every repository statement of
Part I was checked against the tree it describes.

Source 02's pin is `e47ed8547bd021f9bd85bdcf767c94a2fcb41001`, the arrival
commit of batch 56. There Part I's `article.tex` had the blob `3f52dc51`,
unchanged at placement, so the manuscript's "predecessor report" is Part I
as printed (before the dated notes of this write). The five Lean files it
cites (`SexticRadicalDecision.lean`, `SexticSeparatingSearch.lean`,
`SexticSparseSymmetricSearch.lean`, `SexticSeparatingInvariants.lean`,
`SexticReducibleDecision.lean`) have the same blobs at both pins and at the
placement commit; every blob named in `data/02-three-plus-one-sources.json`
resolves to that content, except the SymPy test-seed file, which is external
to ProveIt and was not checked. The manuscript did not see the other
batch-57 deliveries.

Source 03's pin is `1156651a9417231a9a54442b420f099ee85ae7fe` (2026-09-30
17:12 −07:00, before its arrival commit). There this report's `article.tex`
had the blob `efcff1403` and its `README.md` the blob `54d7469ae`, the blobs
they still had at the placement commit, so the manuscript's "predecessor"
and "inspected report" are Parts I and II as printed, before the dated notes
of its write. The one Lean file it cites, `SexticRadicalDecision.lean`, has
the blob `c19d91c58` at all three pins and at placement. The blobs in
`data/03-zero-parameter-sources.json` resolve to that content and its three
code hashes match the shipped programs; its SymPy seed-file hash is external
and was not checked. The manuscript did not see the other batch-70
deliveries.

**Status: AI-assisted, unrefereed, not formalized.** No statement of any
part has a Lean or Rocq proof; that the report sits next to a formal project
confers no formal status on it.

```
article.tex                                the report, standalone LaTeX with an internal bibliography
article.pdf                                the compiled report, 81 pages, US Letter (unnumbered title
                                           page, contents pages 1–3, Part I pages 4–30, Part II
                                           pages 30–54, Part III pages 54–78, references pages 78–80)
README.md                                  this guide
03-zero-parameter-SOURCES.md               Part III: the delivered source map, repository delta and
                                           verification boundary (delivery names; see below)
code/verify.py                             Part I: exact checks (SymPy 1.14.0 for four symbolic
                                           identities; the rest integer arithmetic): counts,
                                           discriminant identities, symmetry, the 462-subset sample,
                                           fixed-parameter counterexamples
code/sharpness_certificate.py              Part I: standard-library generator and checker of the
                                           modular Bézout certificate for the roots (1, 4, 10, 23, 51, 109)
code/build.sh                              Part I: the delivered PDF build script (does not work
                                           from code/; see below)
code/02-three-plus-one-sextic_resolvents.py  Part II: exact coefficient-only evaluator of both
                                           resolvents and the decision function (SymPy)
code/02-three-plus-one-verify.py           Part II: verifier (symbolic identities, split-root
                                           comparisons, 48 irreducible inputs against SymPy's
                                           Galois classifier); see "Rerunning" before running it
code/02-three-plus-one-build.sh            Part II: the delivered PDF build script (does not work
                                           from code/)
code/03-zero-parameter-sextic_resolvents.py  Part III: exact coefficient-only evaluator (M_f by the
                                           trace recurrence, T_f by traces or the Pfaffian, the zero
                                           matching resolvent) and the decision function (SymPy)
code/03-zero-parameter-verify.py           Part III: verifier (symbolic identities, seven split-root
                                           tuples, 48 irreducible inputs against SymPy's Galois
                                           classifier, Pfaffian checks); see "Rerunning"
code/03-zero-parameter-check_certificate.py  Part III: standard-library checker of the integer
                                           certificate (36.3) (prints; writes no file)
code/03-zero-parameter-build.sh            Part III: the delivered PDF build script (does not work
                                           from code/)
data/verification.json                     Part I: recorded output of code/verify.py
data/sharpness_certificate.json            Part I: recorded certificate: E mod 1000003 (degree 195)
                                           and cofactors A, B
data/environment.json                      Part I: the delivery's record of its software versions and runs
data/requirements.txt                      Part I: the pin sympy==1.14.0
data/02-three-plus-one-requirements.txt    Part II: the pin sympy==1.14.0 (same bytes as Part I's)
data/02-three-plus-one-sources.json        Part II: repository pin, Git blobs of the inspected
                                           sources, SymPy seed file, primary literature
data/02-three-plus-one-verification.json   Part II: recorded output of its verifier (Python 3.13.5,
                                           SymPy 1.14.0, elapsed_seconds 38.643, all_checks_passed)
data/02-three-plus-one-verification.log    Part II: recorded console transcript (51 lines)
data/03-zero-parameter-requirements.txt    Part III: the pin sympy==1.14.0 (same bytes as Part I's)
data/03-zero-parameter-verification.json   Part III: recorded output of its verifier (Python 3.13.5,
                                           SymPy 1.14.0, elapsed_seconds 15.044, all_checks_passed,
                                           48 cases: 36 solvable, 12 not)
data/03-zero-parameter-verification.log    Part III: recorded console transcript (18 lines)
data/03-zero-parameter-certificate-check.txt  Part III: recorded output of the certificate checker
                                           (PASS, 0 remaining coefficients)
data/03-zero-parameter-sources.json        Part III: repository pin, Git blobs of the inspected
                                           sources, primary sources, SHA-256 of the three programs,
                                           environment and status flags
data/03-zero-parameter-build_record.json   Part III: record of the delivered PDF build (20 pages,
                                           hashes of the delivered PDF and source; see below)
data/03-zero-parameter-pdf-fonts.txt       Part III: pdffonts listing of the delivered PDF
```

Every file under `code/` and `data/`, and `03-zero-parameter-SOURCES.md`,
is byte-identical to its delivery. The delivered READMEs and PDFs are not
shipped: this README replaces them, and `article.pdf` is a build of the
written text. No delivered checksum file `SHA256SUMS` is shipped (10 of 10
verified at each of the first two placements, 15 of 15 at the third). The
LaTeX sources of sources 02 and 03 are not shipped either; they are printed
as Parts II and III. Each source's unshipped files survive in its arrival
commit (`9754e8360` for source 01, `6ad01e9c8` for source 02, `1b3960d8a`
for source 03). Delivery names:

- Source 01 (flat layout with a `checks/` directory): `build.sh` →
  `code/build.sh`, `requirements.txt` → `data/requirements.txt`, and
  `checks/X` → `data/X` for its three JSON files.
- Source 02: `code/sextic_resolvents.py` →
  `code/02-three-plus-one-sextic_resolvents.py`, `code/verify.py` →
  `code/02-three-plus-one-verify.py`, `build.sh` →
  `code/02-three-plus-one-build.sh`, `requirements.txt` →
  `data/02-three-plus-one-requirements.txt`, and `data/X` →
  `data/02-three-plus-one-X` for `sources.json`, `verification.json` and
  `verification.log`. **Its delivered names `code/verify.py`,
  `data/verification.json` and `requirements.txt` collide with Part I's
  files here** (see "Rerunning").
- Source 03: `code/X` → `code/03-zero-parameter-X` for
  `sextic_resolvents.py`, `verify.py` and `check_certificate.py`;
  `build.sh` → `code/03-zero-parameter-build.sh`; `requirements.txt` →
  `data/03-zero-parameter-requirements.txt`; `data/X` →
  `data/03-zero-parameter-X` for `verification.json`, `verification.log`,
  `certificate-check.txt`, `sources.json`, `build_record.json` and
  `pdf-fonts.txt`; `SOURCES.md` → `03-zero-parameter-SOURCES.md`. Its
  delivered names `code/verify.py`, `data/verification.json` and
  `requirements.txt` collide with Part I's files here as well.

## Labels and numbering

Part I's labels carry the prefix `sbr:`, Part II's the prefix `tpo:`.

- `sbr:` (77, unchanged): the 73 delivered labels of source 01 plus the four
  added at its write, `sbr:sec:notation`, `sbr:sec:provenance`,
  `sbr:sec:formal`, `sbr:sec:nonclaims`. Every theorem, equation and section
  number of Part I is that of the delivered 24-page PDF; at this write the
  `.aux` numbers of all 77 were compared with a build of the committed text
  and none changed.
- `tpo:` (70, new): source 02's 61 delivered labels under the prefix; five
  for the write's Section 18 (`tpo:sec:write`, `tpo:sec:provenance`,
  `tpo:sec:notation`, `tpo:sec:formal`, `tpo:sec:nonclaims`); three on Part
  I's Research questions 16.3, 16.7, 16.8 (`tpo:q:sbr-irreducible`,
  `tpo:q:sbr-circuits`, `tpo:q:sbr-primrec`), which were unlabelled; and
  `tpo:q:smaller` on Part II's Question 30.6. 147 labels in total.
- `zpt:` (92, new at the Part III write): source 03's 75 delivered labels
  under the prefix; five for the write's Section 32 (`zpt:sec:write`,
  `zpt:sec:provenance`, `zpt:sec:notation`, `zpt:sec:formal`,
  `zpt:sec:nonclaims`); eight on the manuscript's research questions, which
  were unlabelled (`zpt:q:nonzero`, `zpt:q:rank-two`, `zpt:q:nonzero-safe`,
  `zpt:q:witness`, `zpt:q:smaller`, `zpt:q:modular`, `zpt:q:char`,
  `zpt:q:formal`); three on Part II's Questions 30.1–30.3
  (`zpt:q:tpo-nonempty`, `zpt:q:tpo-fewer`, `zpt:q:tpo-classify`); and
  `zpt:rem:sbr-zero` on Part I's unlabelled Remark 3.3 (the zero parameter
  and the coordinate order). 239 labels in total; none of the 147 earlier
  labels was renamed or removed, and at this write the `.aux` numbers of all
  147 were compared with a build of the committed text and none changed.

Part III's numbering: the manuscript's Section `n` is Section `n + 32`, its
Appendices A–B are Appendices F–G, and its theorem and equation numbers
follow (its Theorem 2.1 is Theorem 34.1, its equation (2.1) is (34.1)). Its
Table 1 is Table 7 here. Its "Research questions 1–8", numbered by a counter
of their own, are Questions 44.1–44.8, because here questions share the
theorem counter.

The manuscript's Section `n` is Section `n + 18`, its Appendices A–C are
Appendices C–E, and its theorem and equation numbers follow (its Theorem 1.1
is Theorem 19.1, its equation (1.1) is (19.1)). Its one table, Table 1
there, is Table 4 here, because the report's three earlier longtables share
the table counter.

Corrections of form. At source 01's write: the title page's spacing was
tightened, and the environments sharing the theorem counter use alias
counters (`aliascnt`), because in the delivered build every `\cref` to a
lemma, proposition or corollary printed "theorem". At this write: the
manuscript's macros `\M`, `\T`, `\pin` are `\tpoM`, `\tpoT`, `\tpopin`, and
its `\E` is Part I's `\Edges` (same printed symbols); its four unused
operator declarations were dropped; `listings` was loaded for its two code
listings. At the Part III write: the manuscript's `\Q`, `\Z`, `\M`, `\T` are
`\QQ`, `\ZZ`, `\tpoM`, `\tpoT` and its `\pin` is `\zptpin` (same printed
symbols); its unused `\C`, `\E`, `\diag` were dropped; its `\Gal`, `\Rtwo`,
`\Rthree` have the report's identical definitions; its own `\Ares`,
`\Tres`, `\code`, `\roots`, `\Roots`, `\pf`, `\tr`, `\aff` were added, and
`needspace` was loaded for its one `\Needspace`. Its question
"Classify the affine-rank-two locus" said "Question 1"; that is now a
cross-reference to Question 44.1.

## Setting and notation

`f` is a sextic with distinct roots `α_1, …, α_6` in a characteristic-zero
field; `P` ranges over the 15 pair partitions (matchings), `T` over the 10
triple partitions. The complete descriptors are
`D_B(u, v) = ∏_{B ∈ 𝓑} (v − p_B(u))` with `p_B(u) = ∏_{i ∈ B} (u − α_i)`.
On the curve `(u, v) = (t, 2t²)` they become
`D_P = K_2(t) − 2t² h_P(t)` and `D_T = K_3(t) − 2t² k_T(t)`, with
`h_P = A_P t² + B_P t − C_P` and `k_T = a_T t − b_T`.

Section 1.3 of the article tabulates Part I's overloaded letters, Section
18.2 Part II's, and Section 32.2 Part III's. The readings most likely to
mislead:

- **Lean's coordinate order.** Lean's parameter is a pair `x : Fin 2 → ℕ`;
  in `bivariateDescriptor`, `X 0` is the block variable `v` and `X 1` the
  root variable `u`. True: `x(0) = 2t²`, `x(1) = t`. False: the reverse.
  Checked at source 01's write against the definitions and by a separate
  script.
- **Code versus parameter.** Lean's `Nat.find` runs over `Primcodable`
  codes decoded by `parameterAt`, not over `t`; 196 bounds `t`.
- **196 versus `N_int`.** 196 is sharp for arbitrary sets of distinct
  nonzero complex test values; for the initial integer interval only
  `8 ≤ N_int ≤ 196` is proved.
- **Argument order of the resolvents.** Part I writes `R_{2,f}(Z, t)`,
  `R_{3,f}(Z, t)`; Part II writes the same polynomials `R_{2,f}(t, Z)`,
  `R_{3,f}(t, Z)`, parameter first. In Part II's Table 4, `R_3(1)` means
  `R_{3,f}(1, Z)`.
- **Fields.** Part II's `K` is the base field over which `f` is irreducible
  and does not contain the roots; `L` is its splitting field (Part I calls it
  `M`), not Part I's triple collision factor `L_f`. Part II's `𝓔` is the
  edge set of `K_6` (Part I's `𝓔` too), not the obstruction `E_f`.
- **Edge-disjoint = block-disjoint.** A matching's blocks are edges, so
  Part II's edge-disjoint matchings are Part I's block-disjoint ones. A
  *pentad* (five pairwise edge-disjoint matchings, a one-factorization of
  `K_6`) is new in Part II; `𝓑_f` there is a set of parameters, not a
  partition.
- **Matrices.** In Part II Section 26, `C, S, P, Q, H, U, V, D, F` are
  matrices or the scalar `f(u)`, not `C_P`, a matching `P`, `Q_f`, the
  height `H`, `U_f`, the variables `u, v`, or descriptors. `H` and
  `R = 1 + H` of Part II Section 27 agree with Part I Section 11.
- `p_B` is a block's root polynomial, `p_b = α_i α_j` a pair product, `p`
  the prime 1000003. `R_{2,f}`, `R_{3,f}` are resolvents, `R = 1 + H` a
  root bound; neither is the sibling report's `R_{p,k,f}`, and `h_P` is not
  its `h_A(u)`. In Lemma 5.1 the letters `a, …, f` are root values. Degrees
  30, 120, 45, 195 are degrees in `t`; 30, 240, 90, 360 are homogeneous
  degrees in roots and `t`.
- **Part III's constant resolvents.** `M_f = ∏_P (Z − A_P)` and
  `T_f = ∏_T (Z − b_T)` are new. `M_f` is not the set `𝓜` of matchings nor
  Part I's splitting field `M`; `T_f` is not the set `𝓣`. `M_f` is not
  `R_{2,f}(0, Z) = ∏_P (Z + C_P)`, and `R_{3,f}(0, Z) = ∏_T (Z + b_T)` has
  the roots of `T_f` with opposite signs (root existence in `K` is the
  same). The safe zero test is the *compressed* `R_{2,f}(0, Z)`: the
  descriptors on the curve collapse at `t = 0` (`D_P(0, 0) = −e_6` for every
  `P`).
- **Part III's matrices and letters.** In Section 39, `J` is a 20×20
  pairing matrix (not `J_f`), `D = ∧³C` (not Part II's `(uI − C)^{∧3}`),
  and `H = D + D†` (the manuscript also uses `H` for the coefficient height
  in Section 41). In Section 40, `S`, `P` are Part II's compounds, `E_j` its
  `r_j`, `V`, `W` its `U`, `V`, and `Q(Z)` a cubic matrix polynomial. In the
  proof of Theorem 38.1, `D` and `E_j` are a product and elementary
  symmetric functions of five roots; in Section 36, `F_i`, `H_i` are
  certificate polynomials and `a, b, c, d` normalized roots; in Section 42,
  `u, v` are cube roots and `F` a number field. `s_j` in (40.7) are power
  sums, not edge sums `s_b`.

No symbol was renamed in print and no normalization changed, in any part.

## What the report claims

Theorem numbers are those of `article.pdf` (for Part I also those of the
delivered PDF).

**Part I.**

- **Propositions 3.1, 3.2 (compression).** Pair descriptors are determined
  by the quadratic `h_P(t)`, triple descriptors by the linear `k_T(t)`, and
  the curve `(t, 2t²)` transports them affinely (common multiplier `−2t²`).
- **Lemmas 4.1, 5.1, 5.2.** Of the 105 pairs of matchings, 45 share a block
  and differ by a scalar times `q_e(t) = t² + s_e t − p_e`; 60 are
  block-disjoint. The 45 pairs of triple partitions correspond to pairs of
  disjoint root pairs, with linear factor `ℓ_{e,e'}`.
- **Proposition 6.2 (exact failure test).** `Q_f`, `U_f`, `L_f` are
  symmetric with integer coefficients, of `t`-degrees 30, ≤ 120, ≤ 45, and
  `E_f(t) = Q_f U_f L_f (t) ≠ 0` iff both `P ↦ h_P(t)` and `T ↦ k_T(t)` are
  injective (sign argument, Lemma 6.1).
- **Theorem 7.1.** `disc_Z R_{2,f} = disc(f)^6 Q_f^6 U_f^2` and
  `disc_Z R_{3,f} = disc(f)^3 L_f^2` as polynomial identities;
  Corollary 7.2 on square classes.
- **Theorem 8.4 (generic three-factor theorem).** Over
  `Q(e_1, …, e_6)`, `Q`, `U`, `L` are irreducible of exact `t`-degrees 30,
  120, 45, pairwise nonassociate; `E` is squarefree of degree 195 with
  nonzero constant term.
- **Theorem 9.1.** Among any 196 distinct nonzero test values, in
  particular `1, …, 196`, one separates both families and both original
  descriptors on the curve (151 suffice for pairs alone, 46 for triples).
- **Theorem 9.2 (sharpness).** Some split integer sextics have exactly 195
  distinct nonzero bad complex parameters; the roots
  `(1, 4, 10, 23, 51, 109)` are a certified example (Section 9.1, modular
  Bézout identity modulo 1000003).
- **Proposition 9.3.** `8 ≤ N_int ≤ 196`, the lower bound from the roots
  `(−3, 0, 1, 2, 3, 4)`. **Proposition 9.4.** No single positive integer
  separates the pair family of every split sextic.
- **Theorem 10.3.** For an irreducible rational sextic and a simultaneous
  separator `t`, `f` is solvable by radicals iff one of the two specialized
  resolvents has a rational root (classical criterion, reproved). Part II's
  Theorem 19.1 removes the separation hypothesis for the decision, and Part
  III's Theorem 34.1 and Corollary 38.4 reduce the tests further (dated
  notes after Theorem 10.3 say so).
- **Theorem 11.1.** A bounded coefficient-only procedure (monicization,
  bounded factor boxes, the quintic branch, a scan of `t = 1, …, 196`,
  bounded integer-root tests) has a primitive-recursive realization and
  decides all-roots radical solvability of integer sextics.
- **Theorem 12.1.** `t_* = 4^15 6^165 (1 + H)^360 + 2` separates without
  any search.
- **Section 14** (a plan for three new Lean modules), **Proposition 15.1**
  (Kronecker-curve separation, standard), and **Section 16**: twelve
  research questions (16.1–16.12). Question 16.3 is answered for the
  decision (not for separation) by Part II, with four fixed tests, and by
  Part III with two; 16.7 is partly addressed by Parts II and III, and 16.8
  by Part II; dated notes after them say how.

**Part II** (irreducible `f` over a characteristic-zero field `K`, Galois
group `G`).

- **Theorem 19.1 (three plus one).** For any distinct `t_1, t_2, t_3 ∈ K`
  and any `u ∈ K`, `f` is solvable by radicals iff `R_{3,f}(u, Z)` has a
  root in `K`, or each `R_{2,f}(t_j, Z)` has one; over `Q`, `u = 1`,
  `t = 1, 2, 3` work for every irreducible sextic. Repeated resolvent roots
  are allowed. *Sharpened by Part III* (Theorem 34.1, Corollary 38.4): one
  matching test at `t = 0`, or two at any distinct parameters, suffice.
- **Lemma 21.2.** A transitive subgroup of `S_6` preserving a regular graph
  of degree 1–4 is solvable, so a nonsolvable transitive group is
  edge-transitive. **Lemma 22.1, Theorem 22.2.** If `G` is nonsolvable, the
  shifted pair products are distinct and the ten values `k_T(u)` are
  distinct at every `u ∈ K`, with no root of `R_{3,f}(u, Z)` in `K`.
- **Lemma 23.2, Lemma 23.4, Theorem 23.5.** In the nonsolvable case no
  `q_e(t)` vanishes at `t ∈ K`; there are exactly six pentads, each matching
  in two, any two meeting in one; a base-field root of `R_{2,f}(t, Z)` has
  as fiber a `G`-invariant pentad, multiplicity exactly five, is the only
  such root, and `G` fixes at most one pentad. **Lemma 23.6, Corollary
  23.7.** Pentad sums are `e_2`, `3e_3`, `e_4`, so such a root equals
  `μ_f(t) = (e_2 t² + 3e_3 t − e_4)/5`.
- **Theorem 24.1.** The false-positive parameters are the zeros in `K` of a
  canonical `J_f ∈ K[t]` of degree ≤ 2 (empty without an invariant pentad),
  so there are at most two. *Sharpened by Part III* (Theorem 38.3):
  `deg J_f ≤ 1` and `J_f(0) ≠ 0`, so at most one, never `t = 0`.
- **Proposition 25.1 (orbit budget)**, early-exit certificates (Section
  25.1).
- **Theorems 26.1, 26.2.** `det(Z I_45 − B_2(t)) = R_{2,f}(t, Z)^3` for
  every separable monic sextic and every `t`, and
  `det(Z I_20 − B_3(u)) = R_{3,f}(u, Z)^2` when `f(u) ≠ 0`, from compound
  matrices of the companion matrix; exact cube and square roots by a
  triangular recurrence (Section 26.4).
- **Proposition 27.1.** The criterion for monic irreducible integer sextics
  has a primitive-recursive realization (explicit root boxes
  `|h_P(t)| ≤ 66R⁴`, `|k_T(1)| ≤ 8R³`), and irreducibility can be checked by
  a bounded search.
- **Section 28**: exact checks, including all sixteen transitive group
  types in three coordinate variants each (22 triple-positive,
  14 matching-positive, 12 negative, all agreeing with SymPy's classifier);
  **Section 29**: source map and formalization order; **Section 30**: ten
  research questions (30.1–30.10). Part III answers 30.3 (degree two cannot
  occur) and 30.2 for a universal single parameter and for every choice of
  two, narrows 30.1 and partly addresses 30.6; dated notes there say how,
  and one at the end of Section 30 lists what bears on 30.5, 30.7, 30.8 and
  30.10.
- Reproved from Part I and printed again, with notes: Lemma 20.1 (= Lemma
  2.1), Proposition 20.2 (= Propositions 3.1–3.2), Lemma 21.1 (= Lemma 10.1
  with Proposition 10.2), Lemma 23.1 (= Lemma 4.1).

**Part III** (irreducible `f` over a characteristic-zero field `K`, as in
Part II).

- **Theorem 34.1 (two resolvents, safe zero parameter).** `f` is solvable
  by radicals iff `M_f` or `T_f` has a root in `K`, iff `R_{2,f}(0, Z)` or
  `R_{3,f}(u, Z)` (any prescribed `u ∈ K`) has one. Each positive test is
  individually safe but need not identify a fixed partition.
- **Theorem 36.1 (pentad noncollapse).** For distinct roots in a field of
  characteristic ≠ 2, the five `A_P` of a pentad are not all equal; the
  proof is the integer certificate (36.3), `Σ H_i F_i = 2c(c−1)d(d−1)`.
  **Corollaries 36.3, 36.4.** A root in `K` of `M_f`, or of
  `R_{2,f}(0, Z)` (by reciprocal transport, `C_P = e_6 A_P(1/α)`), forces
  `G` solvable.
- **Theorem 38.1 (pentad affine rank).** The five points `(A_P, B_P, C_P)`
  of a pentad span an affine space of dimension ≥ 2, over any field.
  **Corollary 38.2**, **Theorem 38.3**: `deg J_f ≤ 1`, `J_f(0) ≠ 0`,
  `|𝓑_f| ≤ 1`, `0 ∉ 𝓑_f`. **Corollary 38.4.** Any two distinct matching
  parameters with one triple test decide.
- **Theorems 39.1, 39.2.** `T_f(Z) = pf(J(ZI − H))/pf(J)` with
  `H = ∧³C + J⁻¹(∧³C)ᵀJ`, denominator-free and valid at singular and
  nonseparable inputs, `det(ZI − H) = T_f²`; the same for every odd middle
  exterior degree. **Theorem 40.2.** `det Q(Z) = M_f(Z)³` for a 15×15 cubic
  matrix polynomial `Q`, with a trace recurrence for the coefficients.
- **Proposition 41.1** (bounded realization, second route to Proposition
  27.1), the exact checks of Section 41 with Table 7, the example
  `x⁶ + x³ + 2` of Section 42 (a rational root of `M_f` with no fixed
  matching; Galois group of order 36), a formalization route (Section 43)
  and eight research questions (44.1–44.8).
- Reproved from Part II and printed again, with notes: Lemmas 35.1, 35.2,
  35.4 and (35.2) (= Lemmas 21.1, 21.2, 23.4, 23.6), Lemma 37.1 and
  Proposition 37.2 (= Lemma 22.1, Theorem 22.2), the fiber argument of
  Section 38 (= Lemmas 23.1–23.2, Theorem 23.5, Corollary 23.7), and the
  collapse of the descriptors at zero (Part I's Remark 3.3, Part II after
  (20.6)).

## What the report does not claim

The article's Sections 1.6, 18.4 and 32.4 collect these. In brief:

- **Not formalized.** No statement is formalized, and no `sbr:`, `tpo:` or
  `zpt:` label has a Lean or Rocq counterpart. The modules proposed in Section 14
  (`SexticCompressedDescriptors.lean`, `SexticCollisionFactors.lean`,
  `SexticBoundedSeparatingSearch.lean`) do not exist.
- **Source 01's non-claims.** Unrefereed; not run in Lean or Rocq; no
  repository rebuild or modification; no benchmark against production
  Galois software. Decidability of radical solvability, even in polynomial
  time (Landau–Miller 1985), and the sextic block criterion are classical;
  the contributions are relative to the inspected repository and consulted
  sources, without an exhaustive priority search. The Python files are an
  exact verifier and a root-level prototype, not a coefficient-only solver
  and not an extraction of a formal proof; the expanded universal
  coefficient tables are specified, not supplied. 196 is sharp for
  arbitrary complex test sets only; `N_int` is bracketed, not determined.
  The fixed-parameter counterexamples are reducible. Theorem 11.1 is a
  mathematical realization, not a changed Lean function or an accepted
  `Primrec` proof, and claims no polynomial bit complexity. The height
  separator is not a practical method. Proposition 15.1 is standard.
- **Source 02's non-claims.** Unrefereed, not formalized, repository not
  modified or rebuilt; proofs are written proofs, not imported Lean
  theorems; priority not certified and novelty not inferred from absence in
  the repository. General and polynomial-time decidability are classical,
  and Proposition 27.1 is not a new decidability result, claims no bit
  complexity and no speed advantage; its boxes are a coarse termination
  bound. **No claim that three matching tests are optimal**, and no example
  shows that two or one must fail; the *and* between the matching tests
  cannot be replaced by *or*. **No false positive is exhibited or claimed to
  exist**: `|𝓑_f| ≤ 2` is an upper bound, not a maximum. **Part I's
  196-point separation bound is neither improved nor contradicted**: Part II
  solves a weaker decision problem under a stronger irreducibility
  hypothesis, which is essential. The triple test is safe but not complete.
  The implementation is an exact rational prototype, not a verified
  extraction; it rejects reducible input, does not implement the
  multiplicity shortcut, and the reducible extension (with a quintic
  criterion) is not included. The checks are finite; the classifier shares
  SymPy's arithmetic; 48 examples are not exhaustive and contain no
  nonsolvable false positive; no benchmark; the running time is an
  environment observation. Its questions are open within the article only.
  (Part III later reduced the three matching tests and the bound two, as
  above; Part II's text is kept, with dated notes.)
- **Source 03's non-claims.** AI-assisted, unrefereed, not formalized;
  repository inspected at the pin, not modified or rebuilt; the programs
  are exact implementations and checkers, not extracted Lean proofs, and no
  Lean file is supplied as if checked. No priority claim and no exhaustive
  priority search: the matching invariant (Boswell–Glasser's is `e_6 A_P`
  after relabeling) and the two-resolvent idea are classical; the claimed
  contributions are the collision certificate, the selected-zero result for
  this family, the affine-rank bound and the matrix realizations. No general
  radical construction, no new decidability theorem, no optimal count of
  root-finder calls, no optimal separator bound, no classification of
  exceptional sextics, **no nonzero exceptional example** (one is an upper
  bound, not an existence theorem; existence is open), no recovery of a
  matching from a rational matching value. Part I's 196-point theorem is
  neither refuted nor improved. **Corollary 38.4 does not make an arbitrary
  prescribed nonzero single parameter safe** (Question 44.3). The
  descriptors on the curve still collapse at zero; dropping a zero check
  while keeping the uncompressed formula would be an error. The Pfaffian
  formula is denominator-free but the supplied elimination divides by
  rational pivots; Pfaffian theory is standard; nothing is deduced in higher
  degree; the 15×15 realization is a cubic matrix polynomial, not a linear
  pencil or an optimal circuit. The procedure rejects reducible input and
  does not replace the repository's reducible branch; Proposition 41.1 is
  not a Lean `Primrec` theorem, its boxes are not a practical method and are
  exponential in bit length; no bit complexity or speed claim; the run time
  is an observation; the classifier shares SymPy's arithmetic; the finite
  checks are regression tests. The example of Section 42 is not a
  counterexample to any theorem. The delivered README adds that its
  checksum file was not a theorem certificate or a signature.
- **Review.** AI-assisted and unrefereed. At source 01's write both of its
  scripts were rerun on a copy and reproduced the recorded outputs exactly
  (modulo line endings); a separate script (not shipped) checked the Lean
  coordinate convention on 300 random integer root tuples at
  `t = 1, …, 11` (no disagreement), the first separator 8 of
  `(−3, 0, 1, 2, 3, 4)`, and, over the integers, that `E_f` for
  `(1, 4, 10, 23, 51, 109)` has degree 195, a nonzero constant term and
  `gcd(E_f, E_f') = 1`. At this write Part II's verifier was rerun on a copy
  (below), and at placement a separate script (not shipped) recomputed the
  pentad incidences, the pentad sums symbolically, the 45 shared-edge
  factorizations and the descriptor expansion, and found numerically (60
  digits, not a proof) no invariant pentad for the `A_6` seed and exactly one
  for the `PSL_2(5)` and `PGL_2(5)` seeds, consistent with `J_f = 1` there.
  At Part III's placement its certificate checker and verifier were rerun on
  a copy of the delivered package (Python 3.13.5, SymPy 1.14.0, Windows; see
  "Rerunning"), and a separate script (not shipped) found the certificate
  residual zero, checked the pentad sums, the reciprocal identity and the
  coordinates of the rank proof symbolically, found exhaustively over
  `F_7`, `F_11`, `F_13` (720, 30 240 and 95 040 translation-normalized root
  tuples, all six pentads) no collapse of the `A_P` on a pentad and no
  affine rank below two, and over `F_7`, `F_11` with nonzero roots no
  collapse of the `C_P`; verified on five split tuples (with zero and with
  repeated roots) `det(ZI − H) = T_f²`, `D^T J D = det(C) J`,
  `det Q(z) = M_f(z)³` at 46 points, the zero transport (41.1) where
  `e_6 ≠ 0` and `D_P(0, 0) = −e_6`; and reproduced (42.2), (42.3) from
  60-digit numerical roots (not a proof). None of that is an independent
  proof review.
- **An editorial consequence.** Section 18.4 notes, as the write's own
  observation (in neither manuscript), that for a nonsolvable irreducible
  sextic and `t ∈ K`, Part II's Theorem 22.2 and Lemma 23.2 give
  `L_f(t) ≠ 0` and `Q_f(t) ≠ 0`, so `E_f(t) = 0` iff `U_f(t) = 0`. It does
  not settle Question 16.3. Section 32.3 notes, likewise as the write's own
  observation, that with the existing descriptor definitions Part III would
  let Lean test the two curve points for `t = 1, 2` plus one triple test,
  and the dated note after Question 30.2 that its adaptive version needs no
  more than its universal one.

## Relation to the formal project `Algebra/PolynomialFormulas`

Nothing in the project is refuted or changed. The project has formalized
**none** of this report's statements, in any of the three parts. What it does prove,
in namespace `LeanProofs.PolynomialFormulas`, under
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/` (article Section 1.5):

- `SexticSeparatingInvariants.lean`: `rootPolynomial_injective` (l.115),
  `pairDescriptor_injective` / `tripleDescriptor_injective` (l.422, 428)
  — together Lemma 2.1; `bivariateDescriptor` (l.618),
  `pairBivariateDescriptor_injective` / `tripleBivariateDescriptor_injective`
  (l.668, 677); `pairDescriptorValue` / `tripleDescriptorValue` (l.790,
  794); `exists_nat_eval_injective` (l.1048, via `exists_nat_eval_ne_zero`,
  l.1019, the combinatorial Nullstellensatz);
  `exists_pairDescriptor_separating_evaluation` /
  `exists_tripleDescriptor_separating_evaluation` (l.1074, 1083);
  `exists_pairDescriptorValue_injective` /
  `exists_tripleDescriptorValue_injective` (l.1092, 1102). All purely
  existential: no bound is stated, and the point is not on a curve.
- `SexticSeparatingSearch.lean` — **not cited by source 01; cited by
  source 02**: `pairSeparatesB` / `tripleSeparatesB` (l.536, 539), the
  unbounded searches `pairSeparatingCode` / `tripleSeparatingCode` (l.604,
  608; `Nat.find` at l.606, 610) over codes decoded by `parameterAt`
  (l.517), `pairSeparatingParameter` / `tripleSeparatingParameter` (l.612,
  616) and their `_injective` correctness theorems (l.620, 629). This is the
  search Part I bounds and Part II bypasses on paper.
- `SexticIrreducibleDecision.lean`: the guarded total searches
  `pairTotalCode` / `tripleTotalCode` (l.87, 90; `Nat.find` at l.88, 91)
  and `pairTotalCode_computable` (l.101). Source 01 cites this file as
  where the `Nat.find` happens; source 02 does not cite it.
- `SexticRadicalDecision.lean`: `sexticRadicalDecision_correct` (l.34),
  `allRootsRadical_computablePred` (l.49),
  `has_verified_sextic_radical_turing_machine` (l.56); its docstring
  (l.8–9) disclaims primitive recursiveness because of the unbounded search.
- Rocq: the `Coq/SexticMuRec*.v` route also selects the parameters "by
  genuine unbounded minimization" (`Algebra/PolynomialFormulas/README.md:240-243`);
  source 01 mentions it only in passing, source 02 not at all.

**Formalization targets, not claims.** A Lean proof of Theorem 9.1 for the
root tuple of an irreducible monic sextic, with the affine relations (3.3),
(3.6) and the convention `x = (2t², t)`, would bound the Lean search:
`pairSeparatingCode` would be at most the largest `encodeParameter` of the
points `(2t², t)`, `t ≤ 151` (`t ≤ 46` for triples), or the search could be
replaced by a fixed scan of `t = 1, …, 196`. That bounds the parameter
selector only. Two further unbounded searches remain: `linearTotalCode`
(`SexticReducibleDecision.lean:72`, `Nat.find` at l.73), which source 01
notes, and `elementaryCode` (`SexticSparseSymmetricSearch.lean:634`,
`Nat.find` at l.637), the elementary-symmetric certificate search behind
`elementarySparse` (l.671), `pairElementarySparse` /
`tripleElementarySparse` (l.1133, 1138) and `pairCollisionElementary` /
`tripleCollisionElementary` (`SexticSeparatingSearch.lean:282, 286`), which
source 01 does not mention. Part II needs no separating parameter at all on
the irreducible branch: a Lean proof of its Theorems 22.2, 23.5, 24.1 and
19.1 against the existing descriptor definitions would let that branch test
the fixed points `x = (2t², t)`, `t = 1, 2, 3`, instead of calling
`pairSeparatingCode` / `tripleSeparatingCode` (or `pairTotalCode` /
`tripleTotalCode`). `elementaryCode` would remain unless Part II's matrix
Theorems 26.1–26.2 were also formalized as the coefficient evaluator, and
`linearTotalCode` remains on the reducible branch in any case. Part II's
Proposition 27.1 is a written argument, not a `Primrec` proof.

Part III (Section 32.3) would reduce the four fixed tests to two: one
triple test and the *compressed* matching test at `t = 0`. That test needs a
new evaluator of `∏_P (Z + C_P)` (or of `M_f`): the existing bivariate
descriptors collapse at `x = (0, 0)`. With the existing descriptors on the
curve, Corollary 38.4 would allow the points `x = (2, 1)`, `x = (8, 2)`
(`t = 1, 2`) with one triple test. Part III's matrix Theorems 39.1 and 40.2
are further candidates for the coefficient evaluator; Proposition 41.1 is
again a written argument. The manuscript cites only
`SexticRadicalDecision.lean` (its docstring's disclaimer of primitive
recursiveness, l.7–9, is quoted correctly) and proposes a formalization
order in Section 43; no Lean file of it exists.

## Relation to neighbouring reports

[`specialization-safe-radical-solvers`](../specialization-safe-radical-solvers/README.md)
(batch 36, with a Part II from batch 52), the other report in this
category, is a sibling: its separating repair (Theorem 7.2) compresses
`k`-subsets of the roots of a prime-degree polynomial by `h_A(u)` with an
unsharpened bound (1191 values for septic triples), and its Research
question 14.3 asks for a smaller number for `(n, k) = (7, 3)` by counting
collision orbits. Part I here does that kind of orbit count for sextic
block partitions and reaches a sharp bound; Part II's Proposition 25.1 is a
general orbit-collapse budget of the same kind, and its pentad argument
shows that classifying invariant fibers can beat it. No part answers a
question of that report, and none of the three manuscripts cites the other
report. A dated `[write]` note in that report (after its Theorem 7.2)
points here. No other report of the collection shares a theorem with this
one.

## Building

From a scratch copy of this directory (keeps auxiliary files out of the
repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (`newtx`, `tcolorbox`, `cleveref`, `aliascnt`, `listings`,
`needspace`), no external bibliography or figures. The committed build: 81
pages, 0 errors, 0 undefined references or citations, 0 multiply defined
labels, 0 duplicate destinations, 0 overfull or underfull boxes, no Type 3
fonts. Do not use `code/build.sh`, `code/02-three-plus-one-build.sh` or
`code/03-zero-parameter-build.sh`: each changes to its own directory
(`code/`), which has no `article.tex`.

## Rerunning the checks

Run every script on a copy, never in the report directory.

**Part I.** Its scripts write into a directory `checks/` next to the
`code/` directory that contains them (`Path(__file__).resolve().parents[1] / 'checks'`),
so in place they would create a stray `checks/` in the report directory:

```
mkdir <tmp> && cp -r code <tmp>/ && cd <tmp>
uv run --no-project --with sympy==1.14.0 python code/verify.py
py code/sharpness_certificate.py
```

(`cp -r code` also copies Part II's scripts; these commands do not run them.)

Compare `<tmp>/checks/verification.json` and
`<tmp>/checks/sharpness_certificate.json` with the files of the same names
in `data/` after removing carriage returns (on Windows `write_text` emits
CRLF). At source 01's write both commands exited 0 in about 6 s together,
and both files matched their shipped counterparts modulo CR.
`sharpness_certificate.py` imports `verify.py` from its own directory
(without importing SymPy or running its checks), so keep the two together.
Do not run Python with `-O`: the checks are `assert` statements.

**Part II — do not run its verifier in place.**
`code/02-three-plus-one-verify.py` imports `sextic_resolvents` under the
delivered name (l.13) and always writes
`Path(__file__).resolve().parents[1]/'data'/'verification.json'`
(l.226–227). Under its shipped name the import fails before anything is
written; but a copy that restores the delivered names inside this directory
would **overwrite Part I's `data/verification.json`** (and `code/verify.py`
itself is Part I's). Restore the names only in a scratch directory:

```sh
W=/path/to/scratch; mkdir -p "$W/02/code" "$W/02/data"
cp code/02-three-plus-one-verify.py "$W/02/code/verify.py"
cp code/02-three-plus-one-sextic_resolvents.py "$W/02/code/sextic_resolvents.py"
cd "$W/02" && uv run --no-project --with sympy==1.14.0 python code/verify.py
```

Compare `$W/02/data/verification.json` with
`data/02-three-plus-one-verification.json` after removing carriage returns,
and the console with `data/02-three-plus-one-verification.log`. At this
write (Python 3.13.5, SymPy 1.14.0, Windows) the run exited 0 in about 62 s;
the JSON was CRLF and, after removing CR, equal to the record except
`elapsed_seconds` (60.078 against 38.643); the console, after removing CR,
equal to the log except the final `wrote <path>` line. The evaluator imports
nothing local and writes nothing, so it can be run in place:

```
uv run --no-project --with sympy==1.14.0 python code/02-three-plus-one-sextic_resolvents.py 'x**6+x+1'
```

(it prints `"solvable": false` after the triple test and the first matching
test, as Section 28.3 states).

**Part III.** The certificate checker (standard library only) and the
evaluator import nothing local and write nothing, so they run in place
under their shipped names:

```
py code/03-zero-parameter-check_certificate.py
uv run --no-project --with sympy==1.14.0 python code/03-zero-parameter-sextic_resolvents.py 1 0 0 1 0 0 2
```

The first prints exactly `data/03-zero-parameter-certificate-check.txt`;
the second takes seven rational coefficients, highest degree first, and
prints `"solvable": true` for `x⁶ + x³ + 2` (checked at this write, on a
copy). **Do not run the verifier in place.** `code/03-zero-parameter-verify.py`
imports `sextic_resolvents` under the delivered name (l.13), so under its
shipped name it fails at once; and its default output is
`Path(__file__).resolve().parents[1]/'rerun'/'verification.json'` (l.200),
which with restored names inside this directory would create a stray
`rerun/` in the report. It never writes into `data/`. Restore the names
only in a scratch directory:

```sh
W=/path/to/scratch; mkdir -p "$W/03/code"
cp code/03-zero-parameter-verify.py "$W/03/code/verify.py"
cp code/03-zero-parameter-sextic_resolvents.py "$W/03/code/sextic_resolvents.py"
cd "$W/03" && uv run --no-project --with sympy==1.14.0 python code/verify.py
```

(`--output FILE` changes the destination.) Compare
`$W/03/rerun/verification.json` with
`data/03-zero-parameter-verification.json` after removing carriage
returns, and the console with `data/03-zero-parameter-verification.log`.
At placement (Python 3.13.5, SymPy 1.14.0, Windows) the run exited 0 in
about 80 s; the JSON was CRLF and, after removing CR, equal to the record
except `elapsed_seconds` (74.763 against 15.044); the console equalled the
log except the final `Written: <path>` line.

## Discrepancies and delivery names

- Source 01's text uses its delivery layout: Section 9.1 and the Appendix B
  ledger name `checks/…` (with a `[write]` footnote and an inline `[write]`
  remark respectively), and Appendix A describes an archive with the PDF, a
  README and a checksum file and runs `./build.sh` and
  `python code/verify.py` from the package directory (a `[write]` note there
  gives the shipped layout).
- Source 02's text uses its delivery layout: Section 28 names
  `code/sextic_resolvents.py`, `code/verify.py`, `data/verification.json`,
  `data/verification.log`, and Appendix D runs `pdflatex`,
  `python -m pip install -r requirements.txt` and `python code/verify.py`
  from the package root and describes its build script; `[write]` notes in
  both places give the shipped names. Its delivered README (not shipped)
  said to run `./build.sh` "from any directory".
- `code/build.sh` and `code/02-three-plus-one-build.sh` run `pdflatex`
  after `cd`-ing to their own directory (l.3 of the latter), which is
  `code/` here; both fail there, and the source the second one built is not
  shipped.
- `code/verify.py` (l.183) and `code/sharpness_certificate.py` (l.115)
  write to `parents[1]/checks/`, a directory that is `data/` in the shipped
  layout; they never write into `data/` itself.
  `code/02-three-plus-one-verify.py` (l.226–227) writes to
  `parents[1]/data/verification.json`, Part I's recorded output here, with
  CRLF on Windows (`write_text` without `newline=`); see "Rerunning".
- `data/environment.json` records source 01's run (Python 3.13.5, SymPy
  1.14.0, report date 2026-09-28) and names the commands
  `python code/verify.py` and `python code/sharpness_certificate.py`; it
  is not regenerated by the scripts.
  `data/02-three-plus-one-verification.json` records source 02's run
  (Python 3.13.5, SymPy 1.14.0, `elapsed_seconds` 38.643, the pin).
- The last line of `data/02-three-plus-one-verification.log` names the
  packager's path `/mnt/data/ProveIt_Three_Plus_One_Resolvents/data/verification.json`.
  The file is tracked although the root `.gitignore` ignores `*.log`
  (l.61); it was added with `git add -f` at placement.
- The delivered READMEs asked for `python -m pip install -r
  requirements.txt`; here the files are `data/requirements.txt`,
  `data/02-three-plus-one-requirements.txt` and
  `data/03-zero-parameter-requirements.txt` (all three the same blob
  `1ca5fd06`), and the `uv --with sympy==1.14.0` form above needs no
  install.
- Source 03's text uses its delivery layout: Section 41.3 says the verifier
  writes `rerun/verification.json` and does not overwrite the delivered
  record, and Appendix F lists `article.tex`, `article.pdf`, `README.md`,
  `build.sh`, `code/…`, `data/…` and `SOURCES.md` under delivered names and
  runs `python -m pip install -r requirements.txt`, `python
  code/check_certificate.py`, `python code/verify.py`, `python
  code/sextic_resolvents.py 1 0 0 1 0 0 2` and `bash build.sh` from the
  package directory; `[write]` notes in both places give the shipped names.
  Its `article.tex`, `article.pdf` and `README.md` are not shipped (the
  source is printed as Part III), and its `build.sh`
  (`code/03-zero-parameter-build.sh`) `cd`s to its own directory (l.3) and
  fails from `code/`.
- `03-zero-parameter-SOURCES.md` uses delivery names (`code/verify.py`, l.57)
  and calls the report's questions "its merged Section 30" (correct here).
  `data/03-zero-parameter-sources.json` keys its `code_sha256` by the
  delivered names `code/check_certificate.py`, `code/sextic_resolvents.py`,
  `code/verify.py`; the three hashes match the shipped
  `code/03-zero-parameter-*.py`. Its `platform` (Linux) and the recorded
  run are the packager's.
- `data/03-zero-parameter-build_record.json` and
  `data/03-zero-parameter-pdf-fonts.txt` describe the **delivered** 20-page
  PDF and source, which are not shipped (they survive in `1b3960d8a`): its
  `pdf_sha256` and `tex_sha256` match those delivered files, and its
  `verification_record_sha256` and `certificate_check_sha256` match the
  shipped `data/03-zero-parameter-verification.json` and
  `data/03-zero-parameter-certificate-check.txt` (all four checked at this
  write). Neither describes this report's `article.pdf`.
- The last line of `data/03-zero-parameter-verification.log` names the
  packager's path `/mnt/data/ProveIt_Zero_Parameter_Sextics/data/verification.json`
  (l.18), although the verifier's default output is `rerun/…`; the log is
  tracked with `git add -f`, as Part II's is. The recorded
  `elapsed_seconds` (15.044) is the packager's environment.
- The delivered README (not shipped) required Python 3.10 or later, ran
  `python code/verify.py` from the package root, and noted that
  `matching_resolvent` computes `M_f`, not `R_{2,f}(0, Z)`, that
  `zero_matching_resolvent` computes the latter and requires a nonzero
  constant term, and that `triple_resolvent` computes `T_f`, whose roots are
  those of `R_{3,f}(0, Z)` with opposite signs. `decide_irreducible_sextic`
  in this file tests `M_f` and then `T_f` (Theorem 34.1 (ii)), returns a
  Boolean, and rejects reducible input.
- Bibliography keys: source 01's key `repo-search` points to
  `SexticIrreducibleDecision.lean`; source 02's key `repo-search` points to
  `SexticSeparatingSearch.lean`, which Part I cites only through the
  `[write]` entry `repo-separating-search`. In the merged bibliography Part
  II's citations of that file use `repo-separating-search`, and its
  `repo-sparse` uses `repo-sparse-search`; the shared entries
  (Landau–Miller, Boswell–Glasser, three Lean files) are printed once.
  Source 03's `repo-lean` is `repo-decision` (same file and blob), its
  `sympy-tests` is Part II's `tpo:sympy-tests`, and Boswell–Glasser is
  shared by all three; each gains a note. Its `repo-report`, `wimmer` and
  `sympy-docs` are `zpt:repo-report`, `zpt:wimmer` and `zpt:sympy-docs`.
