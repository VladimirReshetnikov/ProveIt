# A Reflexive Root-Polytope Model for Preorder h-Polynomials

**Simplicial-polytopal realization for all finite preorders; and, for height two, matching supports, nonreal-root families and crown obstructions**

This is a research report in two parts. Part I is the original report of
20 September 2026. Part II was added on 28 September 2026 in batch 39 of
ProveIt's incoming-report intake, from a later manuscript that addresses the
three questions Part I left open in its Section 10 ("What remains unresolved"):
Conjectures 5.3, 5.2 and 5.1(d) of Athanasiadis–Chapoton. Both were prepared
for Vladimir Reshetnikov and are AI-assisted (the article credits ChatGPT).

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
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*A Reflexive Root-Polytope Model for Preorder h-Polynomials*) | (Cardinals-era delivery, not committed as an archive) | (none) | sorted in `f0f61b70d`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 4–16) and Appendices A–C (pp. 45–47) |
| 02 | batch 39, manuscript 02 (*Height-Two Preorder Polynomials: Matching supports, nonreal-root families, and crown obstructions*, 28 Sep 2026, 26-page PDF as delivered) | `ProveIt_Height_Two_Preorder_Research.zip` (inner `Preorder_Matching_Research/`, main file `article.tex`) | no commit; blob `4c350f5652096b7db91d4a10075eb7905910f647` of Part I's `article.tex` | `e2b1f016a` (prefix `02-height-two-`) | Part II: Sections 11–25 (pp. 17–44) |

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

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and neither source claims otherwise. The
programs check finite instances; they do not prove the all-`n`, all-`m` or
all-`r` statements.

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

**Part II** (manuscript 02) works with posets of height at most two, written
`P_G` for a bipartite comparability graph `G` on `n` vertices. It proves:

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

**What this does to Part I's open questions** (Section 11.3; dated pointers in
the abstract, the scope box, Sections 8 and 10 and Appendix C):

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
- No characterization of graphs admitting a cactus-style matrix; no claim that
  every noncactus graph fails real-rootedness; no limiting root measure for
  `Theta_m`; no weighted preorder-polytope interpretation of the weighted
  cactus polynomial.
- No novelty for the univariate cactus theorem, the crown formula, or the
  matrix technique; no absolute publication priority for any extension (the
  source audit was targeted, not exhaustive). A withdrawn SSRN listing for an
  eight-element counterexample (abstract 7385158) was noted by the manuscript
  and is not used as evidence.
- No Lean verification; the staged formalization plan (Section 23) has not
  been started.

## Labels

Part I's 60 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`app:`) and are unchanged, with unchanged numbers (compared in the `.aux`
files of the committed and the new build). Part II added **87** labels, all
with the prefix `htwo:` ("height two"): the manuscript's 76 labels, prefixed,
plus 11 new ones (its conclusion and build subsection, two previously
unlabelled corollaries, and the provenance section's seven). Total: 147. No
label was renamed or removed. Part II begins at Section 11 and precedes
Part I's appendices, whose letters and numbers are unchanged.

## Notation

Table 1 (Section 11.2) fixes Part II's symbols against Part I's. No symbol of
the manuscript was renamed and no normalization changed. Watch in particular:

- `P_G`, `P_0`, `P_r`, `P_{Theta_m}` are **posets**; Part I's `P_tau` is a
  **lattice-point set**, which Part II writes `Q(P) ∩ Z^V`. With `tau = P`,
  Part II's `h_P`, `Q(P)`, `C_P` are Part I's `h_tau`, `Q_tau`, `C_tau`.
- `G = (A ⊔ B, E)` is the n-vertex comparability graph, **not** Part I's
  doubled 2n-vertex graph `G_tau` (and `E` is its edge set, not Part I's ground
  set). Remark 11.1, a merge note, shows that Part I's and Part II's imported
  inputs agree: `h_tau(t) = p_{G_tau}(t)` for every preorder, whereas
  `p_G` is the **gamma**-polynomial of `h_{P_G}`. (Checked by direct
  enumeration for all 390 labeled preorders with `n ≤ 4` in the write phase;
  that check is not shipped.)
- `p = |A|`, `q = |B|` are not Part I's `p(y)`, `q(y)`; `m` indexes `Theta_m`,
  not a dilation; `K` is the cactus matrix, not a triangulation; `S` is a
  subset or a random support size, not `S_tau`; `I` in Section 18 is an
  independent set, not an order ideal.

## Files

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 47 pages (title p. 1, contents pp. 2–3, Part I pp. 4–16,
                                             Part II pp. 17–44, Part I's appendices pp. 45–47, references p. 47)
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
```

The ten `02-height-two-` files were staged in the placement commit
`e2b1f016a`, byte-identical to the delivery. The board-certificate CSV is
all-CRLF as delivered (Python's `csv` writer) and is protected by a `-text`
line in `SetTheory/Cardinals/.gitattributes`.

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

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy of `article.tex` so that no auxiliary files land here
(`build.py` writes a `build/` directory beside the source before copying
`article.pdf` back). The preamble needs Part I's packages (newpxtext,
newpxmath, tcolorbox, titlesec, fancyhdr, listings, hyperref, …) plus TikZ
and needspace for Part II; no image or font files are needed. The shipped
PDF was built with MiKTeX (pdfTeX 1.40.26): no errors, no undefined or
multiply defined references, no duplicate destinations, no overfull boxes;
one underfull box (badness 1817) in Part II's provenance-ledger table, which
the delivered manuscript's own build also shows.

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

## Discrepancies and delivery names

- **Delivery names.** Part II's programs, Makefile and status notes use the
  delivered paths (`code/verify.py`, `code/verify_theta.py`,
  `code/direct_counterexample.cpp`, `data/*.json`, `data/board_certificate.csv`,
  `article.tex`, "the package"); the recipe above recreates them in a copy.
  The C++ source's header comment suggests running a binary at
  `/tmp/direct_preorder`. The article quotes the shipped names
  (Section 22.4).
- **Unshipped files.** `02-height-two-STATUS.md` and `02-height-two-sources.md`
  speak of "the article" and "the package", meaning the delivered 26-page
  manuscript and archive, which are not shipped; their content is Part II of
  `article.pdf`. The delivered Makefile's `pdf` and `clean` targets name
  `article.tex` in the package root and a `build/` directory.
- **Part I's own files.** `STATUS.md` ("A proof of flag realizability,
  gamma-positivity, or real-rootedness" not claimed) and `PROOF_AUDIT.md`
  describe Part I at 20 September 2026 and are unchanged; for Conjectures
  5.2, 5.3 and 5.1(d) read Section 11.3 of the article. Part I's Appendix C
  describes Part I's original archive layout (with `build.py`).
- **Part I's equation numbers.** Part I prints two displays numbered (1.1)
  (a manual tag on the preorder polytope and the automatic number of the
  support polynomial); this predates the addition and is left as it was.
- **Self-citation.** The manuscript cited Part I as an external repository
  report; those citations became internal references (Section 11.4).

## Relation to neighbouring reports and to the formal projects

Three other preorder reports in `enumerative-combinatorics/` concern the same
paper of Athanasiadis–Chapoton but different polynomials and questions:
`preorder-polytope-reciprocity` (reciprocity and matrix duality),
`preorder-shellability` (a shelling for Question 4.6) and
`preorder-q-zeta-reciprocity` (support reciprocity and the q-zeta
polynomial). Each lists real-rootedness and gamma-positivity only as not
addressed, and none addresses Conjectures 5.1(d)–5.3 for the support
polynomial `h_tau` (the q-zeta report states that its `H_tau` is a different
polynomial), so no reciprocal note was written.

The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration in ProveIt formalizes any statement of Parts I–II (a search of the
repository's `.lean` and `.v` files for Ehrhart, root-polytope, matchable-set,
support-polynomial, gamma-positivity and real-rootedness terms finds nothing
about preorder polytopes). Section 23 records the formalization plan the
manuscript proposes; none of it has been started.

## Sources and attribution

- C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to
  preorders*, arXiv:2605.26916v1 — the conjectures (Section 5).
- Z. Dai, Q. Hou, Z. Liu, W. Thawinrak and H. Wang, arXiv:2608.16037v2 — the
  support-enumerator/root-polytope identity and duality (credited in Part I).
- T. Kálmán and A. Postnikov, arXiv:1602.04449 — hypertrees and root polytopes.
- H. Ohsugi and A. Tsuchiya, arXiv:1810.12258 and arXiv:2008.08621; R. Davis
  and F. Kohl, arXiv:2207.14759 — the matching-support Ehrhart numerator, the
  classical nonreal-rooted graph polynomial, univariate cactus
  real-rootedness and the cycle formula (credited in Part II).
- J. R. Stembridge, Trans. AMS 359 (2007) — the width-two poset behind the
  17-element example.
- **S. Patel, MathDB posting — the eight-element counterexample to
  Conjecture 5.3** (credited in Part II; see the box at the top).

No third-party papers or font files are included.
