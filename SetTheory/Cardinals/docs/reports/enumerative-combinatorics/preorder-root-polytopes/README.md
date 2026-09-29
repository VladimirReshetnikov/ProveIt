# A Reflexive Root-Polytope Model for Preorder h-Polynomials

**Simplicial-polytopal realization for all finite preorders; for height two, matching supports, nonreal-root families and crown obstructions; and cactus rigidity for matching-support determinants**

This is a research report in three parts. Part I is the original report of
20 September 2026. Part II was added on 28 September 2026 in batch 39 of
ProveIt's incoming-report intake, from a later manuscript that addresses the
three questions Part I left open in its Section 10 ("What remains unresolved"):
Conjectures 5.3, 5.2 and 5.1(d) of Athanasiadis–Chapoton. Part III was added
on 29 September 2026 in batch 42, from a further manuscript that answers
Part II's Research question 4, "Beyond the sixth-root cactus matrices". All
three were prepared for Vladimir Reshetnikov and are AI-assisted (the article
credits ChatGPT for Parts I and II; manuscript 05 calls itself AI-assisted).

> **Priority.** Part II's headline counterexample to Conjecture 5.3 (real
> roots) is **not new**. The first counterexample known to this report, the
> eight-element height-two poset `P_{Theta_3}`, was posted earlier by
> **Shivam Patel** on MathDB
> (https://mathdb.com/p/374962/real-rootedness-conjecture-for-preorder-polytope-h-polynomia).
> The manuscript found that posting during its own source audit, revised its
> claims, and credits it throughout; it claims only the extension to all
> `Theta_m`. The posting's exact calendar date was not established (the page
> showed a relative date of about one month before 28 September 2026 and
> marked the claim unverified).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*A Reflexive Root-Polytope Model for Preorder h-Polynomials*) | (Cardinals-era delivery, not committed as an archive) | (none) | sorted in `f0f61b70d`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 5–17) and Appendices A–C (pp. 71–73) |
| 02 | batch 39, manuscript 02 (*Height-Two Preorder Polynomials: Matching supports, nonreal-root families, and crown obstructions*, 28 Sep 2026, 26-page PDF as delivered) | `ProveIt_Height_Two_Preorder_Research.zip` (inner `Preorder_Matching_Research/`, main file `article.tex`) | no commit; blob `4c350f5652096b7db91d4a10075eb7905910f647` of Part I's `article.tex` | `e2b1f016a` (prefix `02-height-two-`) | Part II: Sections 11–25 (pp. 18–45) |
| 03 | batch 42, manuscript 05 (*Cactus Rigidity for Matching-Support Determinants: Exact classification, a sharp approximation gap, and stability beyond vertex determinants*, 29 Sep 2026, 24-page US-Letter PDF as delivered) | `ProveIt_Cactus_Rigidity.zip` (inner `ProveIt_Cactus_Rigidity/`, main file `article.tex`) | commit `9754e83603e223811b7515eb892f22c847144593`; blob `8739a224fa8956adab5d8df9f2d5012a6a220959` of this report's `article.tex` | `3609d0473` (prefix `03-cactus-`) | Part III: Sections 26–45 (pp. 46–70) |

Manuscript 02 names no ProveIt commit. It records the Git blob of the
`article.tex` it consulted; that blob is Part I exactly as printed here
(unchanged from `f0f61b70d` through the placement commit `e2b1f016a`), so
Part II's statements about "the ProveIt report" refer to Part I. The archive
arrived in `74f7f5bdb`. Its manuscript, PDF and delivery README are not
shipped; they survive in the arrival commit. Its `SHA256SUMS.txt` was verified
(13/13) at placement and retired. Part II prints every result, proof, example,
remark, limitation, question and non-claim of the manuscript, plus its
abstract, status box and audit box; its Section k is Section k+11 here.
Section 11.4 of the article lists where the merge had to choose.

Manuscript 05 (batch 42) is pinned to commit `9754e8360` (the batch-41
arrival) and records the blob of this report's `article.tex`; that blob is
Parts I and II exactly as printed here (last changed by the batch-39 write
`6a354f52f`, unchanged at the pin and at the placement commit `3609d0473`), so
its "Section 19", "Section 24" and "Theorem 13.2" are this article's Sections
19 and 24 and Theorem 13.2. The archive arrived in `8315d24e3`. Its
manuscript, PDF and delivery README are not shipped; they survive in the
arrival commit. Its `SHA256SUMS.txt` was verified (10/10) at placement and
retired. Part III prints every result, proof, remark, limitation, question
and non-claim of the manuscript, plus its abstract and status note; its
Section k is Section k+26 here, its Appendices A and B are Sections 44 and 45,
and its nine research questions are Research questions 11–19. Section 26.4
of the article lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The
programs check finite instances; they do not prove the all-`n`, all-`m`,
all-`r` or all-graph statements.

## Results

For a finite preorder `tau` on `[n]`, `h_tau(t)` counts the integer points of
its preorder polytope by the number of nonzero coordinates (the support
polynomial of Athanasiadis–Chapoton, arXiv:2605.26916v1, Section 5).

**Part I** (unchanged apart from dated pointers) gives a proposed general proof
of Conjecture 5.1(c), hence (a) and (b):

1. The explicit n-dimensional lattice polytope
   `C_tau = conv({±e_i} ∪ {e_i − e_j : j ≤_tau i, i ≠ j})` is reflexive and
   `h*(C_tau, t) = h_tau(t)` (Theorem 1.1), by a unique integer-fiber
   decomposition of the augmented bipartite root polytope `B_tau`
   (Theorem 4.1, Corollary 4.2).
2. Every pulling triangulation of `∂C_tau` is the boundary of an
   n-dimensional simplicial polytope `S_tau` with `h(S_tau, t) = h_tau(t)`;
   hence palindromicity, unimodality and the full g-theorem conditions.
3. A second route through a diagonal special simplex and an exact interior
   translation of `B_tau` (Section 6), an exact gauge (4.4), Ehrhart and volume
   formulas (Section 7), and a hypertree reconstruction of the known root
   identity (Appendix A).

The higher-dimensional identity `h*(B_tau) = h_tau` and the duality
`h_(tau*) = h_tau` are prior results of Dai, Hou, Liu, Thawinrak and Wang
(arXiv:2608.16037v2); Part I credits them and does not claim them.

**Part II** (manuscript 02; unchanged apart from dated pointers to Part III)
works with posets of height at most two, written `P_G` for a bipartite
comparability graph `G` on `n` vertices. It proves:

1. **Matching-support formula** (Theorem 13.2): `h_{P_G}(t) = (1+t)^n p_G(t/(1+t)^2)`,
   where `p_G` counts perfectly matchable *vertex sets* (not matchings). Hence
   **gamma-positivity (Conjecture 5.2) for all posets of height ≤ 2**, with
   `gamma_k = |M_k(G)|`; real-rootedness of `h_{P_G}` is equivalent to that of
   `p_G` (Proposition 15.1).
2. **The Theta_m family** (Theorem 13.3, Section 16): a closed form for
   `p_{Theta_m}` and an exact real-root count — for `m ≥ 3`, `h_{P_{Theta_m}}`
   has exactly 2 real roots (m even) or 4 (m odd), so the nonreal proportion
   tends to one, at treewidth two. `m = 3` is **Patel's** eight-element
   counterexample (1,281 lattice points), checked here, not claimed.
3. **A 17-element counterexample** (Theorem 13.4, Section 17), transferred from
   the classical Stembridge–Ohsugi–Tsuchiya polynomial, with an exact Laguerre
   certificate `-5680 < 0` and a direct count of all 8,408,566 lattice points;
   neither first nor minimal.
4. **A height-two orthant proof** that `h*(C_{P_G}) = h_{P_G}` and that the
   one-sided model `D_G` is reflexive (Theorem 18.2) — a second route to
   Part I's Corollary 4.2 in height two.
5. **Bipartite cacti** (Section 19): a sixth-root-of-unity matrix `K` with
   `p_G(u) = det(I + u K K*)`, a real-stable multivariate refinement, weighted
   real-rootedness and deletion interlacing. Univariate real-rootedness is
   Ohsugi–Tsuchiya's (Theorem 7.2 of arXiv:2008.08621) and is credited.
6. **Crowns** (Sections 20–21): closed forms with all roots simple and
   negative; yet an induced crown on `2r ≥ 6` elements forces a minimal
   nonface of size `r` in **every lattice triangulation** of `C_tau` or of its
   boundary, and an indispensable toric binomial of degree `r`.

**Part III** (manuscript 05) asks when a bipartite graph `G` carries a
*faithful* matrix: unit complex entries on the edges, zeros elsewhere, and
every square minor of squared modulus exactly 1 or 0 according as its vertex
support is perfectly matchable or not (Part II's cactus matrix is one). It
proves:

1. **Classification** (Theorem 29.1): `G` has a faithful matrix iff it is a
   **cactus**; equivalently one with sixth-root entries; equivalently the
   signed support polynomial `Phi_G` equals `det(diag(z) − H)` for some
   Hermitian vertex-indexed `H`; equivalently `G` carries a support-exact
   matrix over `F_3` (no structurally nonzero minor vanishes). Over `F_2` the
   class is the forests (Theorem 35.1); real faithful matrices exist only on
   forests (Corollary 30.4); `K_{2,m}` is support-exact over `F_q` iff
   `m ≤ q − 1` (Proposition 35.3). The proof reduces an induced theta
   (Lemma 31.1) by a support-preserving Schur compression (Lemma 32.1) to
   three cores, `K_{2,3}`, `theta(1,3,3)` and `theta(3,3,3)` (= Part II's
   `Theta_3`).
2. **Rigidity** (Theorem 30.3): on a cactus of cycle rank `beta`, every
   faithful matrix is gauge-equivalent to exactly one of `2^beta` sixth-root
   matrices (both `(-1)^r zeta` and `(-1)^r zeta-bar` are allowed on each
   cycle); over `F_3` the gauge class is unique.
3. **Sharp gap** (Theorem 36.3): on every noncactus, every unit-phase matrix
   has a matchable minor whose squared modulus is off by at least
   `(sqrt(17) − 3)/2 = 0.5615…`, attained on `K_{2,3}`; the cores
   `theta(1,3,3)` and `theta(3,3,3)` are off by at least 3/5 (Lemmas 36.5,
   36.6); `d(theta(1,3,3)) = (sqrt(5) − 1)/2` exactly (Proposition 44.1).
4. **Strictly stronger than stability** (Theorem 37.1, Corollary 37.4):
   `Phi_{K_{2,3}} = abxyz − (a+b)(xy+xz+yz) + (x+y+z)` is real stable (three
   exact sums-of-squares Rayleigh certificates, via Brändén's Theorem 5.6),
   and so is `Phi_G` for every graph obtained from `K_{2,3}` by attaching
   trees — infinitely many connected noncacti with real-rooted `p_G` and no
   faithful matrix.
5. **No bounded-order test** (Theorem 38.1): for every `r` there is a
   connected subcubic treewidth-two noncactus (an odd theta of girth > 2r) on
   which every phase matrix passes all minor tests of order ≤ r.

**What Parts II and III do to the open questions** (Sections 11.3 and 26.3;
Part II's dated pointers are in the abstract, the scope box, Sections 8 and
10 and Appendix C; Part III's in the title block, the abstract, the
reading-route box, Section 19 and Research questions 3 and 4 of Section 24):

- Conjecture 5.3 (real roots) is **false** — first counterexample credited to
  Patel. Part I never asserted it, so nothing is retracted.
- Conjecture 5.2 (gamma-positivity) is **proved in height ≤ 2 only**; open in
  general, including height-two posets blown up by nontrivial equivalence
  classes (Research question 1).
- Conjecture 5.1(d) (a flag polytope) **remains open**. For every preorder
  with an induced crown on at least six elements, Part I's polytope `S_tau` is
  not flag, since its boundary is a pulling (hence lattice) triangulation;
  Part I's six-element crown is the smallest case. Some other flag polytope
  with the same h-vector is not excluded.
- Part II's Research question 4 ("Beyond the sixth-root cactus matrices") is
  **answered** by Part III: exactly the cacti, and strictly stronger than
  stability. Research question 3 (which graph structures preserve
  real-rootedness) is **re-scoped, still open**: Part III's `K_{2,3}` tree
  attachments are noncacti with real-rooted `p_G`.

## Not claimed

From Part I (see also `STATUS.md`, `PROOF_AUDIT.md`): no new proof of the
already settled duality (Conjecture 5.4); no claim that the support
polynomial is `h*(Q_tau)` (it is `h*(B_tau)` and `h*(C_tau)`); nothing about
arbitrary reflexive nontransitive relations (Section 8.5 gives a
nonpalindromic example); the finite computations are not size records.

From Part II (see also `02-height-two-STATUS.md`, `02-height-two-sources.md`):

- No first disproof of Conjecture 5.3 and no minimum-size claim: the
  eight-element example is Patel's; the 17-element example is a transfer of a
  classical graph polynomial. Minimality of the eight-element example is not
  claimed beyond the authors' reported small-size tests (Research question 9).
- No gamma-positivity beyond height two, or for nontrivial block blowups.
- No disproof of Conjecture 5.1(d); the crown obstruction concerns lattice
  triangulations and the toric configuration of `C_tau` only. Chordal
  bipartiteness is shown necessary for a flag lattice triangulation of `D_G`,
  not sufficient.
- No canonical bijection in the counting lemma (Lemma 14.1 equates
  cardinalities through two imported root-polytope theorems).
- Part II itself gave no characterization of graphs admitting a cactus-style
  matrix (Part III now does); no claim that every noncactus graph fails
  real-rootedness (Part III shows some do not); no limiting root measure for
  `Theta_m`; no weighted preorder-polytope interpretation of the weighted
  cactus polynomial.
- No novelty for the univariate cactus theorem, the crown formula, or the
  matrix technique; no absolute publication priority for any extension (the
  source audit was targeted, not exhaustive). A withdrawn SSRN listing for an
  eight-element counterexample (abstract 7385158) was noted by the manuscript
  and is not used as evidence.
- No Lean verification; the staged formalization plan (Section 23) has not
  been started.

From Part III (see also `03-cactus-STATUS.md`, `03-cactus-SOURCES.md`):

- No novelty for the cactus sixth-root construction, its determinant
  factorization or cactus stability (Part II's), for univariate cactus
  real-rootedness (Ohsugi–Tsuchiya's), or for the height-two transform
  (Part II's); the binary (forest) observation and the general phenomenon of
  stability without a determinant representation (for example Vámos-type
  polynomials, Burton–Vinzant–Youm) are not claimed as new.
- No worldwide publication priority for the classification, the finite-field
  reformulations, the gauge count, the quantitative refinements or the
  stability formulations; the source audit was targeted, and a related earlier
  characterization of binary fundamental transversal matroids (Nakamura 1989,
  publisher abstract only) deserves further review.
- No general characterization of real-stable or real-rooted matching-support
  polynomials (Research question 11), and no claim that the containment
  "stable `Phi_G` ⇒ real-rooted `p_G`" is strict.
- No nonexistence theorem for larger determinantal pencils, auxiliary
  variables, sums of determinants or powers (Research question 15); only the
  vertex-indexed diagonal pencil is excluded.
- No extension of the sharp gap to non-unit edge magnitudes (Research
  question 16); no claim that `d(theta(3,3,3))` equals its lower bound 3/5
  (Research question 12).
- No fixed-size minor test (Theorem 38.1 shows none can work); no
  gamma-positivity or flag-realization result for preorders; no exhaustive
  survey of the repository.
- The `K_{2,3}` stability proof imports Brändén's multiaffine Rayleigh
  criterion (Theorem 5.6 of *Adv. Math.* 216 (2007)); the classification,
  gauge count, gap and bounded-order results use no unproved repository
  theorem.

## Labels

Part I's 60 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`app:`) and are unchanged, with unchanged numbers. Part II's 87 labels carry
the prefix `htwo:` ("height two"): the manuscript's 76 labels, prefixed, plus
11 new ones (its conclusion and build subsection, two previously unlabelled
corollaries, and the provenance section's seven). Part III added **70**
labels, all with the prefix `cac:` ("cactus"): 60 of manuscript 05's 64
labels, prefixed (the other four labelled the displays that repeat Part II's
formulas, which are printed once, in Part II), plus 10 new ones (the
provenance section's six, the build subsection, the conclusion, the
dependency ledger, and `cac:q:beyond` on Part II's Research question 4).
Total: 217. No label was renamed or removed; the numbers of all 147 earlier
labels are unchanged (compared in the `.aux` files of the committed and the
new build). Part III begins at Section 26, after Part II and before Part I's
appendices, whose letters and numbers are unchanged.

## Notation

Table 1 (Section 11.2) fixes Part II's symbols against Part I's; Table 2
(Section 26.2) fixes Part III's against both. Watch in particular:

- `P_G`, `P_0`, `P_r`, `P_{Theta_m}` are **posets**; Part I's `P_tau` is a
  **lattice-point set**, which Part II writes `Q(P) ∩ Z^V`. With `tau = P`,
  Part II's `h_P`, `Q(P)`, `C_P` are Part I's `h_tau`, `Q_tau`, `C_tau`.
- `G = (A ⊔ B, E)` is the n-vertex comparability graph, **not** Part I's
  doubled 2n-vertex graph `G_tau` (and `E` is its edge set, not Part I's ground
  set). Remark 11.1, a merge note, shows that Part I's and Part II's imported
  inputs agree: `h_tau(t) = p_{G_tau}(t)` for every preorder, whereas
  `p_G` is the **gamma**-polynomial of `h_{P_G}`. (Checked by direct
  enumeration for all 390 labeled preorders with `n ≤ 4` in the batch-39
  write phase; that check is not shipped.)
- `p = |A|`, `q = |B|` are not Part I's `p(y)`, `q(y)`; `m` indexes `Theta_m`,
  not a dilation; `K` is the cactus matrix, not a triangulation; `S` is a
  subset or a random support size, not `S_tau`; `I` in Section 18 is an
  independent set, not an order ideal.
- **Part III renames one symbol:** manuscript 05's theta `Θ(a,b,c)` (three
  paths of lengths a, b, c) is printed `ϑ(a,b,c)`, because Part II's `Theta_m`
  has `m` paths of length three. Only `Theta_3 = ϑ(3,3,3)` is both — it is
  Part III's core `T`. No normalization was changed.
- Part III defines `Phi_G` for **every** bipartite graph by the signed
  support sum; Part II's `Phi_G = det(diag(z) − H_G)` is the same polynomial
  for cacti only. Part III's cores `E`, `D`, `T` (sans-serif) are not the edge
  set `E` or Part II's `D_G`, `T_G`; its defect `d(G)` is not the vertex `d`
  of `Theta_m`; its `p, q, r` in Lemma 36.6 are inner products and `q` in
  Proposition 35.3 is a field size, not shore sizes.

## Files

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 74 pages, A4 (title p. 1, scope box and contents pp. 2–4,
                                             Part I pp. 5–17, Part II pp. 18–45, Part III pp. 46–70,
                                             Part I's appendices pp. 71–73, references pp. 73–74)
README.md                                    this guide
STATUS.md                                    Part I: literature and claim status, 20 Sep 2026
PROOF_AUDIT.md                               Part I: independent-review checklist
build.py                                     Part I: two-pass pdfLaTeX script (builds into build/ here; see below)
code/verify.py                               Part I: exact standard-library verifier
data/preorders_through_5.csv                 Part I: all 7,332 labeled preorders through n = 5 and their h-vectors
data/verification_results.json               Part I: detailed exact results and sample certificates
data/verification_log.txt                    Part I: console transcript of the recorded run
data/runtime.txt                             Part I: observed runtime and environment of that run
02-height-two-STATUS.md                      Part II: claim and verification status (delivered STATUS.md)
02-height-two-sources.md                     Part II: sources and priority audit (delivered sources.md)
code/02-height-two-verify.py                 Part II: graph, preorder, crown and cactus checks (standard library)
code/02-height-two-verify_theta.py           Part II: Theta_m formulas, direct enumeration, exact Sturm counts
code/02-height-two-direct_counterexample.cpp Part II: independent C++17 enumeration of the 17-element example
code/02-height-two-Makefile                  Part II: the delivered Makefile (do not run here; see below)
data/02-height-two-verification.json         Part II: recorded output of verify.py
data/02-height-two-theta_verification.json   Part II: recorded output of verify_theta.py (m = 1..20)
data/02-height-two-direct_counterexample.json  Part II: recorded C++ counts (8,408,566 points)
data/02-height-two-board_certificate.csv     Part II: all 90 polynomial states of the board recurrence (CRLF)
03-cactus-STATUS.md                          Part III: proof, priority and computational status (delivered STATUS.md)
03-cactus-SOURCES.md                         Part III: pinned repository source and literature audit (delivered SOURCES.md)
code/03-cactus-verify.py                     Part III: exact finite checks (standard library; Z[zeta], F_3, Q(sqrt 17))
code/03-cactus-Makefile                      Part III: the delivered Makefile (do not run here; see below)
data/03-cactus-verification.json             Part III: recorded output of verify.py (Python 3.13.5)
data/03-cactus-verification_log.txt          Part III: console output of that run (byte-identical to the JSON)
data/03-cactus-build_status.json             Part III: the manuscript's record of its own 24-page PDF build
```

The ten `02-height-two-` files were staged in the placement commit
`e2b1f016a`, and the seven `03-cactus-` files in `3609d0473`, all
byte-identical to their deliveries. The board-certificate CSV is all-CRLF as
delivered (Python's `csv` writer) and is protected by a `-text` line in
`SetTheory/Cardinals/.gitattributes`; the `03-cactus-` files are LF text.

## Data conventions

**Part I.** The CSV fields are `n`, `principal_ideal_bitmasks` and
`h_coefficients`; the two vector fields use semicolons. Bit positions are
zero-based (row value 5 means {0,2}); row i is the set of j with
`j ≤_tau i` (a principal **ideal**, not a filter); coefficients are in
increasing degree; the `n = 0` row has an empty ideal field and polynomial 1.
Graph certificates in the JSON index both shores 0,…,n with 0 the added
universal vertex, offset by one from the bitmask indices. The run checks all
7,332 preorders through `n = 5` (symmetry, unimodality, duality, endpoints,
the `h_1` formula, special-simplex slacks) and all 35 through `n = 3`
independently (18,009 spanning trees, 399 matching-tree certificates); it
does not build a convex realization, test flagness or certify real roots.

**Part II.** Graphs are stored as bitmask neighbourhoods of the upper
vertices. The board CSV has columns `i`, `j`,
`coefficients_in_ascending_degree` (a JSON list) for the 90 cells
`0 ≤ i ≤ 9`, `0 ≤ j ≤ 8` of the recurrence (17.1). The recorded checks: all
512 labeled 3-by-3 bipartite graphs and 24 random 4-by-3 graphs (seed
20260928); crowns `2 ≤ r ≤ 8` (direct lattice checks `r ≤ 4`); 936 exact
square minors in six cactus configurations; `Theta_m` support enumeration
through `m = 9`, direct lattice enumeration through `m = 4`, exact Sturm
counts through `m = 20`; two graph-polynomial computations and a C++ count of
all 8,408,566 lattice points for the 17-element example. No floating-point
root finder is used.

**Part III.** Graphs with fixed labeled shores are binary edge masks;
sixth-root values are integer pairs `a + b·zeta` with `zeta^2 = zeta − 1`.
`data/03-cactus-verification.json` records: all 512 labeled 3-by-3 bipartite
graphs (460 cacti: 328 forests, 132 one-cycle) against 5,872 normalized
sixth-root assignments (7,792 ambiguous minors evaluated; 9,200 canonical
cactus minor checks); all 4,096 labeled 3-by-4 graphs (3,122 cacti: 1,856
forests, 1,248 one-cycle, 18 two-cycle) against 10,576 normalized ternary
assignments (14,717 ambiguous minors; 109,270 canonical cactus minor checks),
118,470 canonical checks in all; the three cores (36 sixth-root and 4 ternary
normalized assignments each, none valid); 3 Rayleigh identity classes
covering 10 pairs, 5 leaf attachments and 2 identities in `Q(sqrt 17)`; 100
augmented-minor norm/support comparisons on the thetas (2,2,4), (1,3,5),
(3,3,5); `"all_passed": true`. These are finite checks: enumerating sixth-root
phases does not exclude arbitrary complex phases, which the proofs do.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy of `article.tex` so that no auxiliary files land here
(`build.py` writes a `build/` directory beside the source before copying
`article.pdf` back). The preamble needs Part I's packages (newpxtext,
newpxmath, tcolorbox, titlesec, fancyhdr, listings, hyperref, …) plus TikZ
and needspace for Part II; Part III adds only macros. No image or font files
are needed. The shipped PDF (74 pages) was built on 29 September 2026 with
MiKTeX (pdfTeX 1.40.26): no errors, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull boxes; one
underfull box (badness 1817) in Part II's provenance-ledger table, which the
committed build before Part III and the delivered manuscript 02's own build
also show.

## Rerun the checks

**Part I.** Its verifier needs no third-party packages; do not use `-O`.
Without `--output` it rewrites `data/preorders_through_5.csv` and
`data/verification_results.json` here, so pass a scratch directory:

```sh
py code/verify.py --output /path/to/scratch/part1      # or python3; ends with ALL CHECKS PASSED
```

Run this way on 28 September 2026 (Python 3.14.4, about 17 s), it passed, and
both outputs equal the shipped files apart from Windows line endings.

**Part II.** Its programs still use the delivered names. Run in this
directory, `02-height-two-verify_theta.py` fails with `ImportError`, because
its `from verify import …` loads Part I's different `code/verify.py`;
`02-height-two-verify.py` would write new unprefixed files
`data/verification.json` and `data/board_certificate.csv` here; and
`make -f code/02-height-two-Makefile verify` would run **Part I's**
`code/verify.py` and overwrite Part I's shipped data. Restore the delivered
layout in a scratch copy instead (Git Bash or another POSIX shell, from this
directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code" "$W/02/data"
for f in code/02-height-two-*; do cp "$f" "$W/02/code/${f#code/02-height-two-}"; done
for f in data/02-height-two-*; do cp "$f" "$W/02/data/${f#data/02-height-two-}"; done
mv "$W/02/code/Makefile" "$W/02/Makefile"
cd "$W/02"
py code/verify.py          # writes data/verification.json, data/board_certificate.csv
py code/verify_theta.py    # imports code/verify.py of the copy; writes data/theta_verification.json
g++ -O3 -std=c++17 -Wall -Wextra -pedantic code/direct_counterexample.cpp -o direct_counterexample
./direct_counterexample > data/direct_counterexample.json
```

(`make verify` in the copy does the same with `python3`.) Run this way on
28 September 2026 (Python 3.14.4, g++ 16.1.0): all three passed; the board
CSV is byte-identical to the shipped file, the theta and C++ outputs are
identical apart from Windows line endings, and `verification.json` differs
only in its recorded run time (`seconds`) and line endings. Each run takes
about a second.

**Part III.** `03-cactus-verify.py` writes `data/verification.json` under the
parent of its own directory, so run in this directory it would add a new
unprefixed `data/verification.json` beside Part I's files (no file is
overwritten, but the tree is dirtied). `make -f code/03-cactus-Makefile`
would rebuild this whole article in place with `pdflatex` (leaving auxiliary
files here), its `verify` target would run **Part I's** `code/verify.py`,
which rewrites Part I's shipped data, and its `clean` target deletes
`article.aux`, `.log`, `.out` and `.toc` here. Use a scratch copy with the
delivered names:

```sh
W=/path/to/scratch
mkdir -p "$W/03/code" "$W/03/data"
for f in code/03-cactus-*; do cp "$f" "$W/03/code/${f#code/03-cactus-}"; done
for f in data/03-cactus-*; do cp "$f" "$W/03/data/${f#data/03-cactus-}"; done
mv "$W/03/code/Makefile" "$W/03/Makefile"
cd "$W/03"
py code/verify.py          # or python3; prints the JSON and rewrites data/verification.json of the copy
```

(`make verify` in the copy runs the same with `python3`.) Run this way on
29 September 2026 (Python 3.14.4, about 3 s): all checks passed, and
`data/verification.json` differs from the shipped file only in `python`
(3.14.4 vs 3.13.5) and `elapsed_seconds`. The program needs Python 3.10 or
later and only its standard library.

## Discrepancies and delivery names

- **Delivery names.** Part II's programs, Makefile and status notes use the
  delivered paths (`code/verify.py`, `code/verify_theta.py`,
  `code/direct_counterexample.cpp`, `data/*.json`, `data/board_certificate.csv`,
  `article.tex`, "the package"); the recipe above recreates them in a copy.
  The C++ source's header comment suggests running a binary at
  `/tmp/direct_preorder`. The article quotes the shipped names
  (Section 22.4). Likewise Part III's program says "Run from the package
  root" and writes `data/verification.json`, its Makefile names
  `code/verify.py` and `article.tex` in the package root, and
  `03-cactus-STATUS.md` / `03-cactus-SOURCES.md` speak of "this manuscript",
  "the article" and "this package" — the delivered 24-page manuscript and
  archive, which are not shipped (their content is Part III of
  `article.pdf`); the article quotes the shipped names (Section 40.3).
- **Unshipped files.** `02-height-two-STATUS.md` and `02-height-two-sources.md`
  speak of "the article" and "the package", meaning the delivered 26-page
  manuscript and archive, which are not shipped; their content is Part II of
  `article.pdf`. The delivered Makefile's `pdf` and `clean` targets name
  `article.tex` in the package root and a `build/` directory. Part III's
  delivery README (not shipped) lists `SHA256SUMS.txt` (verified and retired)
  and does not list `data/build_status.json`, which is shipped as
  `data/03-cactus-build_status.json`.
- **Part III's recorded outputs.** `data/03-cactus-verification_log.txt` is
  byte-identical to `data/03-cactus-verification.json` (the program prints the
  JSON it writes). `data/03-cactus-build_status.json` describes the delivered
  24-page US-Letter PDF ("final_compile_warnings": 0), not this article's
  build.
- **Stale delivered notes.** `02-height-two-STATUS.md` lists "A
  characterization of all graphs admitting the cactus-style matrix" as not
  established; Part III now gives it (Theorem 29.1). The file is delivered
  text and is left unchanged.
- **Part I's own files.** `STATUS.md` ("A proof of flag realizability,
  gamma-positivity, or real-rootedness" not claimed) and `PROOF_AUDIT.md`
  describe Part I at 20 September 2026 and are unchanged; for Conjectures
  5.2, 5.3 and 5.1(d) read Section 11.3 of the article. Part I's Appendix C
  describes Part I's original archive layout (with `build.py`).
- **Part I's equation numbers.** Part I prints two displays numbered (1.1)
  (a manual tag on the preorder polytope and the automatic number of the
  support polynomial); this predates the additions and is left as it was.
- **Self-citation.** Manuscripts 02 and 05 cited this report as an external
  repository report; those citations became internal references
  (Sections 11.4 and 26.4). Two of manuscript 05's section headings keep its
  wording "the repository".
- **Layout changes in the front matter.** Part III's abstract paragraph
  pushed Part I's scope box to page 2, so the page break between that box
  and the table of contents was removed (the contents now follow the box).
  Manuscript 05's equations, numbered (1)–(26) consecutively, are numbered by
  section here; its dependency ledger's second column is set ragged-right.

## Relation to neighbouring reports and to the formal projects

Three other preorder reports in `enumerative-combinatorics/` concern the same
paper of Athanasiadis–Chapoton but different polynomials and questions:
`preorder-polytope-reciprocity` (reciprocity and matrix duality),
`preorder-shellability` (a shelling for Question 4.6) and
`preorder-q-zeta-reciprocity` (support reciprocity and the q-zeta
polynomial). Each lists real-rootedness and gamma-positivity only as not
addressed, and none addresses Conjectures 5.1(d)–5.3 for the support
polynomial `h_tau` (the q-zeta report states that its `H_tau` is a different
polynomial), so no reciprocal note was written. Part III concerns bipartite
graphs and matrices only; none of those reports treats cactus matrices or
stability. Batch 42's manuscript 04, placed in
`ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets`,
also speaks of "height two" and of (uniquely restricted) matchings, but it
concerns ordinal heights of downsets and shares no theorem with this report.

The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration in ProveIt formalizes any statement of Parts I–III (a search of
the repository's `.lean` and `.v` files for Ehrhart, root-polytope,
matchable-set, support-polynomial, gamma-positivity and real-rootedness terms
finds nothing about preorder polytopes, and a search of the tracked `.lean`
and `.v` files for cactus, superregular, real-stable and matchable finds
nothing). Sections 23 and 41.3 record the formalization plans the manuscripts
propose; none of them has been started.

## Sources and attribution

- C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to
  preorders*, arXiv:2605.26916v1 — the conjectures (Section 5).
- Z. Dai, Q. Hou, Z. Liu, W. Thawinrak and H. Wang, arXiv:2608.16037v2 — the
  support-enumerator/root-polytope identity and duality (credited in Part I).
- T. Kálmán and A. Postnikov, arXiv:1602.04449 — hypertrees and root polytopes.
- H. Ohsugi and A. Tsuchiya, arXiv:1810.12258 and arXiv:2008.08621; R. Davis
  and F. Kohl, arXiv:2207.14759 — the matching-support Ehrhart numerator, the
  classical nonreal-rooted graph polynomial, univariate cactus
  real-rootedness and the cycle formula (credited in Parts II and III).
- J. R. Stembridge, Trans. AMS 359 (2007) — the width-two poset behind the
  17-element example.
- **S. Patel, MathDB posting — the eight-element counterexample to
  Conjecture 5.3** (credited in Part II; see the box at the top).
- P. Brändén, Adv. Math. 216 (2007), arXiv:math/0605678 — the multiaffine
  Rayleigh criterion (Theorem 5.6) behind Part III's `K_{2,3}` stability.
- P. J. Almeida, D. Napp and R. Pinto, arXiv:1601.02960 (superregular
  matrices); M. Baker, C. Ding and X. Zhuang, arXiv:2308.11760 (sixth-root
  matroids); S. Burton, C. Vinzant and Y. Youm, arXiv:1411.2038 (stability
  without determinants); M. Nakamura, Graphs Combin. 5 (1989) (binary
  fundamental transversal matroids) — terminology and context for Part III.

No third-party papers or font files are included.
