# Open-query games on ordinal spaces

**An explicit negative answer to the topological-sum problem, with a finite Cantor–Bendixson classification; its extension to finite output alphabets: sharp synchronization and a complexity dichotomy; and filter profiles: an exact classification for finite derived sets, ultrafilter thresholds and a three-color separation**

This is a research report in three parts. Part I is the original report of
19 September 2026. Part II was added on 29 September 2026 in batch 52 of
ProveIt's incoming-report intake, from a later manuscript that replaces
Part I's membership bit by one of `q` output labels. Part III was added on
29 September 2026 in batch 56, from a manuscript that answers Part II's
Research question 1 for spaces with a finite nonempty derived set. All three
are AI-assisted; the manuscripts of Parts II and III were "prepared for
Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Open-query games on ordinal spaces: a negative solution to the topological-sum problem, with an exact Cantor–Bendixson classification*) | `ordinal_membership_games.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–13 (pp. 4–18) and Appendices A–B (pp. 66–67) |
| 02 | batch 52, manuscript 12 (*Finite-Output Open-Query Games: Sharp Synchronization and a Complexity Dichotomy*, 29 Sep 2026, 22-page US Letter PDF as delivered) | `ProveIt_Finite_Output_Open_Query_Games.zip` (inner `finite_output_open_query_games/`, main file `article.tex`), arrived in `11e1e9001` | `5c695cfdf` | `a701d9098` (prefix `02-finite-output-`) | Part II: Sections 14–28 (pp. 19–42) and Appendix C (pp. 67–68) |
| 03 | batch 56, manuscript 05 (*Filter Profiles and Open-Query Complexity: Exact finite-derivative classification, ultrafilter thresholds, and a three-color separation*, 29 Sep 2026, 20-page US Letter PDF as delivered) | `ProveIt_Filter_Profiles_Open_Query_Complexity.zip` (inner `proveit_filter_games/`, main file `article.tex`), arrived in `e47ed8547` | `2d4919838` (blob `75f0c4d7` of this `article.tex`, Parts I–II) | `ae718a441` (prefix `03-filter-profiles-`) | Part III: Sections 29–42 (pp. 43–66) and Appendix D (pp. 68–69) |

The pin `5c695cfdf` is ProveIt commit
`5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864`. At that commit Part I's
`article.tex` was the blob `5e5ed2a806…` and this README the blob
`a8e024d1e3…`; both were unchanged at the placement commit, so every
statement of Part II about "the ProveIt report" refers to Part I as printed
here. (Its source audit, `02-finite-output-SOURCES.md`, says it read that
README and lines 1–160 of the article.) The manuscript, its PDF and its
delivery README are not shipped; they survive in the arrival commit. Part II
prints every result, proof, example, remark, limitation and question of the
manuscript, and its title block, abstract and status paragraph (Section 14.2).
Section 14.1 lists where the merge had to choose; Section 14.3 is the
notation table; Section 14.4 checks Part II against Part I at `q = 2`.

The pin `2d4919838` is ProveIt commit
`2d49198382cc068f46747d1b3d9067d47cee4f24`, which is later than Part II's
write (`f11edd3c5`). At that commit this `article.tex` was the blob
`75f0c4d7ba…` (Parts I–II, including the batch-52 note under Research
question 1) and this README the blob `3357ea6820…` (the manuscript records
the article blob only); both were unchanged at the placement commit. The
manuscript read them through the GitHub connector
(`03-filter-profiles-SOURCES.md`), so its "Part II, Section 27, Research
question 1" is Section 27 and Research question 1 here. Its manuscript, PDF,
delivery README and checksum ledger (`SHA256SUMS`, 12 entries under the
delivery names, verified 12/12 at intake and retired) are not shipped; they
survive in the arrival commit. Part III prints every result, proof, example,
remark, limitation and question of the manuscript, and its title block,
abstract and status paragraph (Section 29.2). Section 29.1 lists where the
merge had to choose; Section 29.3 is the notation table; Section 29.4 checks
Part III against Parts I and II.

**Status.** AI-assisted and unrefereed. Nothing in any part is formalized in
Lean, Rocq or any other proof assistant, and no source claims otherwise.
Part II's NP-completeness theorem imports the modified-SCS hardness theorem
of Lagoutte and Tavenas (arXiv:1309.0422, Corollary 6) as an external input;
Part III's NP-completeness proposition imports the NP-completeness of
directed feedback vertex set (Göke–Marx–Mnich, arXiv:2003.02483). Part III
uses free ultrafilters, whose existence is a theorem of ZFC. The finite
computations check finite posets and finite graphs only; every
infinite-space statement rests on the written proofs.

## Files

```
article.tex                                    the report, standalone LaTeX with an internal bibliography
article.pdf                                    the compiled report, 71 pages, US Letter (unnumbered title
                                               page, contents pages 1–3, Part I pp. 4–18, Part II
                                               pp. 19–42, Part III pp. 43–66, appendices pp. 66–69,
                                               references pp. 69–70)
README.md                                      this guide
RESEARCH_STATUS.md                             Part I's scope, source identification and limitations, as delivered
Makefile                                       Part I's build and verification targets, as delivered (see below)
code/verify.py                                 Part I's verifier: standard library, minimax, closure
                                               profiles, alternating chains, strategy synthesis
data/verification.json                         Part I's recorded run through six points
data/verification.log                          its console output
data/finite_poset_checks.csv                   posets and targets checked at each size
data/ordinal_values.csv                        exact formula values for last derivative ranks 0–128
data/sharp_family.csv                          sharp duplication examples for levels 1–16
data/strategy_certificate.json                 an optimal three-query tree for two oppositely colored
                                               four-element chains
02-finite-output-RESEARCH_STATUS.md            Part II's claim boundaries, as delivered
02-finite-output-SOURCES.md                    Part II's source audit, as delivered
code/02-finite-output-verify.py                Part II's verifier: standard library, exact minimax,
                                               ideal-state search, chain words, greedy feasibility,
                                               closure elimination, constructions
code/02-finite-output-Makefile                 Part II's delivered Makefile (do not use here; see below)
data/02-finite-output-verification.json        Part II's recorded run (--max-n 5 --brute-n 4)
data/02-finite-output-verification.log         its console output
data/02-finite-output-poset_counts.csv         enumeration counts (CRLF, as delivered)
data/02-finite-output-sharp_families.csv       universal-family examples (CRLF, as delivered)
data/02-finite-output-restricted_start_families.csv  restricted-start examples (CRLF, as delivered)
data/02-finite-output-strategy_certificate.json      an optimal three-question strategy on the
                                               twelve-point six-chain ternary example
data/02-finite-output-pdf_build.log            the pdfTeX log of the delivered 22-page PDF (not shipped)
03-filter-profiles-SOURCES.md                  Part III's source audit and novelty boundary, as delivered
code/03-filter-profiles-verify.py              Part III's verifier: standard library, digraphs against
                                               reduced-word search, positive-cell and capacity checks,
                                               extremal thresholds, strategy certificates
code/03-filter-profiles-Makefile               Part III's delivered Makefile (do not use here; see below)
data/03-filter-profiles-verification.json      Part III's recorded run (default --max-q 4)
data/03-filter-profiles-verification.log       its console output (the same JSON)
data/03-filter-profiles-capacity_checks.json   the 98 capacity-attainment cases
data/03-filter-profiles-strategy_certificates.json   optimal words and balanced suffix-query trees
                                               for the two three-color examples
data/03-filter-profiles-extremal_thresholds.csv      least arc counts T(q,r) and equality-graph
                                               counts for q ≤ 4 (CRLF, as delivered)
data/03-filter-profiles-query_jump_thresholds.csv    first component counts forcing an extra
                                               question, q = 2–64 (CRLF, as delivered)
```

Every file other than `article.tex`, `article.pdf` and this README is
byte-identical to its delivery. Part II's delivery was laid out as
`code/verify.py`, `results/X`, `Makefile`, `RESEARCH_STATUS.md` and
`SOURCES.md`; the mapping is `code/verify.py` →
`code/02-finite-output-verify.py`, `results/X` → `data/02-finite-output-X`,
and the other three → the `02-finite-output-` names above. Part III's
delivery was laid out as `code/verify.py`, `results/X`, `Makefile` and
`SOURCES.md`; the mapping is `code/verify.py` →
`code/03-filter-profiles-verify.py`, `results/X` →
`data/03-filter-profiles-X`, `Makefile` → `code/03-filter-profiles-Makefile`
and `SOURCES.md` → `03-filter-profiles-SOURCES.md`. The five CSV files of
Parts II and III were delivered with CRLF line endings and are kept byte for
byte by `-text` lines in `SetTheory/Cardinals/.gitattributes`; the `.log`
files of Parts II and III (their two verification logs and Part II's PDF
build log) were added past the repository's `*.log` ignore rule.

## Labels and numbering

Part I's 54 labels are bare (`thm:height`, `eq:question`, …) and unchanged;
none was renamed or removed, and a comparison of the `.aux` files of this
build and of a build of the committed Part I text shows every Part I number
unchanged. Every label of Part II carries the prefix `fo:` (finite output):
the manuscript's 57 labels keep their names after the prefix, and the write
added seven (`fo:sec:provenance`, `fo:sec:source`, `fo:sec:abstract`,
`fo:sec:notation`, `fo:sec:crosswalk`, `fo:sec:three-colors`,
`fo:app:certificates`), 118 labels in all. The manuscript's Section *n* is
Section *n* + 14 here and every numbered statement and equation keeps its
position (its Theorem 2.2 is Theorem 16.2); this was checked label by label
against a build of the delivered text. Its Research questions 1–10 keep their
numbers, and its Appendix A is Appendix C, after Part I's appendices.
(Corrected 29 September 2026, batch 56: this sentence and Section 14.1 said
"1–9" when Part II was written in; Part II prints ten research questions, as
did its delivered manuscript.)
Text added at the write is marked **[Added 29 September 2026, batch 52]**:
five notes in Part I (Section 1, after Remark 4.4, after Corollary 8.2, after
the example of Section 11, in Section 12), a paragraph of the abstract and one
of the title page, and in Part II Section 14 and seven notes (Sections 15, 20,
22, 25, 26, 27, Appendix C).

Every label of Part III carries the prefix `fp:` (filter profiles): the
manuscript's 46 labels keep their names after the prefix (the prefix also
removes two collisions, `sec:normal` and `thm:normal`, with Part I), and the
write added sixteen: `fp:sec:provenance`, `fp:sec:source`,
`fp:sec:abstract`, `fp:sec:notation`, `fp:sec:crosswalk`,
`fp:sec:conclusion`, `fp:app:certificates` and the nine research-question
labels `fp:q:next-level` … `fp:q:choice`. Part II's Research question 1
gained the label `fo:q:invariants`, which prints nothing. The report now has
181 labels (118 before). The manuscript's Section *n* is Section *n* + 29 here
and its Appendix A is Appendix D; every theorem keeps its position (its
Theorem 4.4 is Theorem 33.4), and its equations, numbered (1)–(14)
consecutively in the manuscript, are numbered within sections here (its
equation (2) is (30.2)). Its Research questions 1–9 are Research questions
11–19, because the counter continues after Part II's ten. All of this was
checked label by label against a build of the delivered text, and a
comparison of the `.aux` files of this build and of a build of the committed
Parts I–II text shows every number of the 118 earlier labels unchanged (only
page numbers moved). Text added at this write is marked **[Added 29 September
2026, batch 56]**: in Part II, notes after Research question 1, after the
remark following Theorem 20.3 and after the proof of Theorem 22.4, and a note
in Section 14.1 correcting its count of research questions (with the two
corrected sentences); a paragraph of the abstract and one of the title page;
and in Part III, Section 29 and five notes (Sections 30, 39 twice, 40,
Appendix D).

## Results

**Part I.** The selected question is Problem 1.3 of Chiozini, Csernák and
Soukup, arXiv:2510.05754v3: is the set-membership number of a topological sum
the supremum of the component values? No: two copies of `[0, ω]` each have
value 1, and their sum has value 2. More generally, for every nonempty
Hausdorff space of finite Cantor–Bendixson height, with `h` the index of the
last nonempty derivative, the value is `ceil(log2(h+1))` when that derivative
is a singleton and `ceil(log2(h+2))` otherwise. The report proves this through
a finite normal form (depth = `ceil(log2 L)` for the least number `L` of
alternating closed layers) and canonical oriented closure profiles; it
derives sharp one-extra-move examples `K_k = [0, ω^(2^k − 1)]` at every level,
product and bounded-height sum formulae, an `ω` upper bound for sums of finite
values, the value `ω` on countable scattered spaces of infinite height, and a
quadratic-time alternating-chain formula on finite posets.

**Part II.** A coloring `c : X → Σ` with `q` labels is to be determined by
open questions.

- *Normal form* (Theorem 16.2): the least number of ordered layers with open
  suffixes, `L(X, c)`, equals the least number of nonempty leaves of a correct
  tree, and the optimal depth is `ceil(log2 L(X, c))`; a fixed-word closure
  test (Proposition 16.3).
- *Posets* (Theorem 17.1): `L` is the shortest common supersequence length of
  the reduced color words of chains; a linear-time least-map feasibility test.
- *Compact realization* (Theorem 18.2): an iterated convergent-sequence tower
  `𝖪_m` (the manuscript's `K_m`) realizes every reduced word with exactly its
  supersequence profile; every finite colored poset has a compact countable
  metrizable model.
- *Universal words* (Theorem 19.1): reduced words of length `m` with first
  letter in an `s`-set need exactly `s + (q−1)(m−1)` letters.
- *Cantor–Bendixson* (Theorem 20.1): `L ≤ (q−1)h + s`, sharp, where `s` is the
  number of colors on the last derivative; *towers* (Theorem 20.3): the worst
  case over `q`-colorings of `t` towers of rank `m − 1` is
  `ceil(log2((q−1)(m−1) + min(q, t)))`.
- *Sums* (Theorems 21.2, 21.3): components with at most `m` layers need at most
  `(q−1)m + 1` jointly, sharply; the exact extra cost is `ceil(log2 q)`
  questions, attained by fixed colorings of compact countable metrizable
  spaces. Six two-point chains `01, 02, 10, 12, 20, 21` go from one question
  each to three jointly (Section 21.1).
- *Complexity* (Proposition 22.1, Theorem 22.4): polynomial for two labels;
  NP-complete for three, even on disjoint chains and on succinct tower lists,
  with an exact common-prefix padding to power-of-two budgets.
- *Algorithms* (Theorem 23.1, Proposition 23.2): a cyclic algorithm within
  `ceil(log2(q−1))` questions of optimal (one for three labels, optimal in the
  integer-additive sense unless P = NP); exact search on order ideals.
- *Obstructions* (Theorem 24.1): a failed `m`-layer budget has a witness of at
  most `(m+1)q^m` points; exact optimization is fixed-parameter tractable in
  the joint parameters `(q, d)`.
- Ten research questions (Section 27). (Corrected 29 September 2026, batch
  56: this line said "Nine" when Part II was written in.)

**At `q = 2` Part II reproduces Part I** (Section 14.4, checked at the write):
its normal form and closure test are Part I's Theorems 4.2 and 5.2; its binary
chain formula is Part I's Theorem 11.1 read from the other end of each chain;
by Part I's Theorem 6.2, `⊔_t 𝖪_m` has value `ceil(log2 m)` for `t = 1` and
`ceil(log2(m+1))` for `t ≥ 2`, which is Part II's tower formula at `q = 2`;
`m = 2, t = 2` is the counterexample `sm(S ⊔ S) = 2`, and since
`𝖪_m ≅ [0, ω^(m−1)]` (proved in item 4 there), `K_k ≅ 𝖪_(2^k)` and `m = 2^k`
gives Part I's sharp family. The formula was compared with all 129 rows of
`data/ordinal_values.csv` and all 16 of `data/sharp_family.csv`: all agree.
The `q = 2` rows of `data/02-finite-output-sharp_families.csv` with word
lengths 2 and 4 are finite analogues of `S ⊔ S` and Part I's eight-point
example. Part I also answers Part II's Research question 1 at `q = 2` (the
bound `h + s` is attained on every Hausdorff space of finite height); a note
after the question re-scopes it to `q ≥ 3`. Part III (batch 56) answers it
for every `q` on spaces with a finite nonempty derived set; heights `h ≥ 2`
and infinite derived sets remain open.

**Part III.** `X` is a Hausdorff space whose derived set
`X' = {p_1, …, p_t}` is finite and nonempty (so `h = 1`, but not every
`h = 1` space is of this kind), and `c` a coloring using `q_c` colors.

- *Filter model* (Lemma 32.1, Lemma 32.2): `X` splits into a clopen discrete
  part and clopen neighborhoods `N_i` of the `p_i`, each a one-point space on
  a free filter; a finite union of color cells is a neighborhood exactly when
  it contains every positive cell.
- *Exact profile* (Theorems 33.1, 33.4): a word is admissible iff it contains
  every used color and every arc `ab` of a digraph `G_c` on the colors (arcs
  from each center color to the colors accumulating at that point) as a
  subsequence; hence `L(X, c) = q_c + τ(G_c)` with `τ` the directed feedback
  vertex number, and depth `ceil(log2(q_c + τ(G_c)))` (Lemma 33.3:
  `ℓ(G) = |V| + τ(G)`); a weighted version (Corollary 33.5).
- *Capacities* (Proposition 34.2, Theorem 34.4): the partition capacity `b_i`
  of the neighborhood filter at `p_i` (1 exactly for an ultrafilter; finite
  `b` exactly for an intersection of `b` ultrafilters) determines
  `sm_q(X)` through `min(b_i, q−1)` alone.
- *Attainment* (Theorem 34.5): `L = q + s − 1`, the bound `(q−1)h + s` at
  `h = 1`, is attained with exactly `s` colors on `X'` iff the points split
  into `s` nonempty bins each of total capacity at least `s − 1`.
- *Three labels* (Theorem 35.1): `sm_3(X) = 3` iff `v + floor(u/2) ≥ 3`
  (`u` points of capacity 1, `v` of capacity ≥ 2), else 2. Three one-point
  free-ultrafilter spaces give 2, three convergent sequences 3, with equal
  derivative cardinalities (equation (35.1)); the ultrafilter space is not
  locally compact and has no convergent injective sequence (Proposition 35.2).
- *Regular points* (Proposition 36.1, Corollary 36.2): first countable or
  locally compact points have infinite capacity, so then
  `sm_q(X) = ceil(log2(q − 1 + min(q, t)))`, Part II's tower value at `m = 2`
  for all such spaces.
- *Extremal graphs* (Lemma 37.1, Theorem 37.2): the least number of arcs of a
  digraph on `q` vertices with acyclic number at most `r` is
  `T(q, r) = ra(a−1) + 2as` (`q = ar + s`, `0 ≤ s < r`), attained exactly by
  balanced unions of complete bidirected graphs.
- *Ultrafilter sums* (Theorem 38.1, Corollary 38.2, Corollary 38.3): for `t`
  one-point ultrafilter spaces the worst layer count is `2q − r_*(q, t)`; the
  extra question over `ceil(log2 q)` appears exactly from `t_q` components
  (2 when `q` is a power of two, `q(q−1)` when `q = 2^(k−1) + 1`; table
  through 64 labels in the data).
- *Algorithms* (Section 39): an exact `O(2^q(q + |E|))` algorithm on supplied
  profiles (not on arbitrary infinite presentations); NP-completeness of
  `L ≤ M` and `D ≤ d` for profile-graph input with unbounded alphabet
  (Proposition 39.1), by directed feedback vertex set.
- Nine research questions (Section 41, numbered 11–19).

**Part III against Parts I and II** (Section 29.4, checked at the write): at
`q = 2` it gives value 1 for `t = 1` and 2 for `t ≥ 2`, Part I's Theorem 6.2
at `h = 1`; its bound (34.3) is Part II's Theorem 20.1 at `h = 1`; for sums of
convergent sequences its Corollary 36.2 is Part II's Theorem 20.3 at
`m = 2`. Part II's remark after Theorem 20.3 never asserted that every space
of a given height has the same invariant, so the separation refutes nothing.
An independent script written at intake and rerun at this write (not
shipped) confirmed `ℓ(G) = |V| + τ(G)` on all 4,165 loopless digraphs on at
most four labelled vertices, `T(q, r)` and its equality graphs for `q ≤ 4`,
the ternary formula and the bin criterion on 172 capacity lists (and Part
II's tower formula for infinite capacities), the ultrafilter layer formula
for `q ≤ 4`, and all 63 rows of the jump table.

## Notation

Part II's notation table (Section 14.3) lists every letter used differently
in Parts I and II; Part III's (Section 29.3) does the same for Part III. The
readings most likely to mislead:

- **`K_k` vs `𝖪_m`.** True: Part I's `K_k = [0, ω^(2^k−1)]` has
  `sm(K_k) = k`; Part II's tower `𝖪_m` (printed in sans-serif; the
  manuscript's `K_m`) has last derivative rank `m − 1` and
  `sm_2(𝖪_m) = ceil(log2 m)`, so `K_k ≅ 𝖪_(2^k)`. False: `𝖪_k = K_k`. This is
  the only renamed symbol of Part II.
- **Layer direction and outer color.** Part I indexes closed layers from the
  outer (open) one, with outer color `c ∈ {0, 1}`; Part II numbers positions
  from the bottom, and `c` is the coloring. Part I's outer color is the *last*
  letter of a Part II word.
- **`h`.** The last derivative rank in all parts, except Part II's `h_c`
  (Corollary 19.2, the supremum of reduced chain-word lengths) and the column
  `h` of `data/02-finite-output-sharp_families.csv`, which is the word length.
  Part III's class (finite nonempty derived set) is a proper subclass of
  `h = 1`: `[0, ω²)` has `h = 1` and an infinite derived set. False: "Part III
  settles `h = 1`".
- **`sm` vs `sm_q`.** Part I's `sm(X)` is an ordinal (a least winning length);
  Part II's and Part III's `sm_q(X)` is a supremum of finite depths, or `∞`.
  At `q = 2` they agree whenever either is finite. The manuscript of Part III
  defined its own macro `\smq` (plain `sm`), which clashes with Part II's
  (`sm_q`, subscript included); it is set with Part I's `\sm`, and the printed
  symbol is unchanged.
- **`L`, `D` in Part III.** The manuscript printed layer count and depth as
  sans-serif `𝖫`, `𝖽`; Part III prints them as Part II's `L`, `D` (same
  numbers). Its `D_i` is the isolated part of a neighborhood, not the depth.
- **`s`, `a`, `b` in Part III.** `s` is the number of colors on `X'` (as in
  Part II), but in `T(q, r)` with `q = ar + s` it is a remainder and `a` a
  quotient, not a color; `b_i` is a partition capacity, not Part II's
  coloring `b_(a,m)`.
- **Fixed coloring vs supremum over colorings.** Part II's sharp
  synchronization examples are fixed colorings; its tower formula is a
  supremum over colorings. For towers `𝖪_m` with `m ≥ 2` the supremum
  increases by at most one under sums, even though fixed colorings can lose `ceil(log2 q)` questions.

## Not claimed

- Part I refutes Problem 1.3 as printed in v3 of the arXiv paper; it does not
  resolve the paper's other questions (large countable point-separation
  ordinals, finite membership values on crowded spaces) or classify games of
  arbitrary uncountable length. No transfinite version of the logarithm
  formula is asserted; `∞` in a finite profile is not an ordinal rank.
- No part claims to introduce difference hierarchies, canonical
  difference chains, multi-valued partition hierarchies (Selivanov) or the
  three-letter modified-SCS hardness (Lagoutte–Tavenas); Part II credits
  typed-DAG fusion (Darte) through Lagoutte–Tavenas without a direct audit.
- Part II does not claim Part I's binary counterexample, binary chain
  algorithm or binary Cantor–Bendixson results anew. It announces no named
  longstanding published problem as solved and does not assert the word
  "breakthrough". Its uniform bound `(q−1)h + s` is not claimed to be attained
  by every coloring or every space for `q ≥ 3`; its compact sharpness
  constructions concern specified colorings, not `sm_q`. It makes no claim
  about transfinite determinacy, countable stopping times or the full
  point-separating invariant.
- Part III does not classify spaces of height `h ≥ 2` or with infinite
  derived sets, transfinite play or expected-cost optimization, and does not
  address Part II's Research question 2 (minimum synchronization families):
  its ultrafilter thresholds count components while permitting every label
  at finitely many isolated exceptions, a specific input model. It makes no
  priority claim for the supersequence/feedback-set lemma, the random-order
  bound or the balanced-clique arc extremum, and its literature search was
  targeted, not exhaustive. It does not refute Part II's upper bound. Free
  ultrafilters are used in ZFC; the finite checks construct none. Its
  algorithm takes the positive-cell sets as input; computing them from an
  arbitrary presentation is not claimed (Research question 16). Its
  NP-completeness is for explicit profile encodings with an unbounded
  alphabet.
- No priority is certified by any part. Targeted searches found no earlier
  resolution; that is a search statement only.
- The finite checks do not establish the infinite-space theorems, the general
  NP-hardness reductions, or novelty. Part II's six-point verifier option was
  not run; the three-color optimality of its approximation guarantee is
  conditional on P ≠ NP, and no such claim is made for `q ≥ 4`.
- Part I's computations were not rerun in the repository. The batch-52
  intake reran Part II's full suite on a copy (59 s): CSV files identical,
  JSON files equal after CRLF → LF except `python` and `elapsed_seconds`. The
  batch-56 write reran Part III's suite on a copy (about 4 s, Python 3.14.4):
  both CSV files byte-identical, JSON files and console log equal after
  CRLF → LF.

## Build the article

Build in a scratch copy so that no auxiliary files land here:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three
times. The shipped PDF was built with MiKTeX (pdfTeX, MiKTeX 26.2): 71 pages,
no errors or warnings, no undefined or multiply defined references, no
duplicate destinations, no overfull or underfull boxes, no Type 3 fonts (the
build of the committed Parts I–II text was equally clean at 45 pages). The
bibliography is internal; Latin Modern is used as an installed TeX font, and
no font files are included. Part I's `Makefile`
runs three pdfLaTeX passes in this directory and leaves `.aux`, `.log`,
`.out` and `.toc` files here. Do not use `code/02-finite-output-Makefile`: it
is written for the delivery's layout, runs only two passes, and from this
directory its `verify` and `smoke` targets would call Part I's
`code/verify.py`, which rejects `--brute-n`. Do not use
`code/03-filter-profiles-Makefile` either: from this directory its `verify`
target would run Part I's `code/verify.py` without `--output`, replacing
Part I's recorded files in `data/`, and write its console output to a new
`results/verification.log`; its `pdf` target runs two passes in place and
its `clean` target deletes this report's auxiliary files.

## Rerun the checks

All three verifiers use only the Python standard library (3.10 or later). Do
not use Python's `-O` option: the assertions are the checks. Use `py` or
`python3` as your system provides; the three Makefiles call bare `python3`.

**Part I.** Without `--output` it writes into `data/` and replaces the
recorded files. Pass a scratch directory:

```sh
py code/verify.py --max-n 6 --output ../scratch-part1   # about 13 s recorded; --max-n 4 is a smoke test
```

This repeats 320,866 poset-and-target tests on 5,231 naturally labelled
posets: for every target it compares exhaustive minimax over all legal open
questions, canonical alternating-closure profiles and an alternating-chain
dynamic program, and it checks a synthesized balanced query tree on every
point. Without options it checks through five points, not six; the allowed
maximum of seven is substantially more expensive. The tables
`ordinal_values.csv` and `sharp_family.csv` evaluate the proved formulae in
exact integer arithmetic; they are not experiments on infinite spaces. Its
JSON output has the platform's line endings and its CSV files
CRLF on every platform, whereas the recorded files are LF: compare after
CRLF → LF (a `--max-n 4` run on a copy gave the recorded
`ordinal_values.csv`, `sharp_family.csv` and `strategy_certificate.json` after
normalization).

**Part II.** Without `--output` it creates a `results/` directory in this
report directory, with unprefixed names. Pass a scratch directory:

```sh
py code/02-finite-output-verify.py --max-n 5 --brute-n 4 --output ../scratch-part2
py code/02-finite-output-verify.py --max-n 3 --brute-n 3 --output ../scratch-smoke
```

The first is the recorded run: 102,331 colored-poset checks on 407 naturally
labelled posets, 4,156 chain-language checks, 416,432 fixed-word checks, 36
restricted-start triples (15 cross-checked by brute force) and 1,176 padding
checks (`data/02-finite-output-verification.json`; 12.19 s recorded, 59 s on
this machine). Compare `verification.json` → `02-finite-output-verification.json`
and so on: its JSON files are written with the platform's line endings (CRLF
on Windows) and differ from the record in `python` and `elapsed_seconds`; its
CSV files are CRLF everywhere, like the recorded ones. The counts are not
counts of isomorphism classes: every finite poset has a natural labelling, so
every type through the stated size is covered, possibly repeatedly. The
finite posets carry the Alexandrov upper-set topology and are not finite
Hausdorff approximations of the ordinal spaces.

**Part III.** Without `--output` it too creates a `results/` directory here,
with unprefixed names. Pass a scratch directory and capture the console:

```sh
W=../scratch-part3
mkdir -p "$W"
py code/03-filter-profiles-verify.py --output "$W/results" > "$W/verification.log"
for f in verification.json capacity_checks.json strategy_certificates.json; do
  diff <(tr -d '\r' < "$W/results/$f") "data/03-filter-profiles-$f"; done
for f in extremal_thresholds.csv query_jump_thresholds.csv; do
  cmp "$W/results/$f" "data/03-filter-profiles-$f"; done    # CRLF on both sides
diff <(tr -d '\r' < "$W/verification.log") data/03-filter-profiles-verification.log
```

This is the recorded default run (`--max-q 4`): 4,165 loopless digraphs on
one to four labelled vertices against 4,472 reduced words, 11,515
positive-cell word checks, 98 capacity cases, 10 extremal arc thresholds
with every equality graph, and threshold tables and balanced constructions
through 64 labels (not an exhaustive digraph check at that size). Its JSON
files and console output have the platform's line endings (CRLF on Windows),
whereas the recorded ones are LF; its CSV files are CRLF on every platform,
like the recorded ones. The JSON records no Python version or time, so a
rerun agrees exactly after CRLF → LF (checked on 29 September 2026).

**Strategy certificates.** In the certificate files of Parts I and II, bit
`i` of a mask is point `i` (zero-based). At an internal node ask membership
in `open_mask` and follow `yes` or `no`. Part I's leaves record `color` and a
closed-layer index; its eight-point example has two disjoint four-element
chains, profile `(5,5)`, depth 3, and "strict-upper" rows. Part II's leaves
record `color` and a one-based `layer`; its predecessor masks hold strict
predecessors, the chains are `01, 02, 10, 12, 20, 21` in that order, and the
word is `01201`. Part III's file holds two examples, `ultrafilter_three`
(arcs `0→1, 1→2, 2→0`, word `0120`, four layers, depth 2) and
`convergent_three` (all six arcs, word `01210`, five layers, depth 3); a node
`ask_suffix_from_position: j` asks for the union of the zero-based word
positions `j, j+1, …`, and leaves record `leaf_position` and `label`. That
these suffixes are open sets is proved in the article (Theorem 33.1); the
JSON does not encode an ultrafilter.

## Discrepancies and delivery names

- `RESEARCH_STATUS.md` is Part I's delivered status record and is not edited:
  it describes Part I only. Part II's claim boundaries are in
  `02-finite-output-RESEARCH_STATUS.md` and in the article (Section 14.1);
  Part III's in `03-filter-profiles-SOURCES.md` and in the article
  (Section 29.1).
- `02-finite-output-RESEARCH_STATUS.md` and `02-finite-output-SOURCES.md`
  describe "this archive", its PDF and its compile, which are not shipped.
  The status record's sentence that a repository search for `supersequence`
  returned no matches was true at the pin; the repository now contains
  Part II.
- `03-filter-profiles-SOURCES.md` names `results/verification.json` (shipped
  as `data/03-filter-profiles-verification.json`), "Section 11 of the article"
  (Section 40 here) and "the README and article", meaning the delivery
  README (not shipped) and the manuscript (printed as Part III).
- `code/02-finite-output-Makefile` names `article.tex` and `code/verify.py`
  (in the delivery: its own article and verifier) and
  `/tmp/open-query-smoke`; `code/03-filter-profiles-Makefile` names
  `article.tex`, `code/verify.py` and `results/`; see "Build the article".
- `code/02-finite-output-verify.py` and `code/03-filter-profiles-verify.py`
  default to `results/` beside `code/` and write unprefixed names (see "Rerun
  the checks").
- `data/02-finite-output-pdf_build.log` is the log of the delivered PDF, which
  is not shipped; the shipped `article.pdf` is a build of the merged text.
- The verification sections and certificate appendices of Parts II and III
  are printed with the shipped names and an explicit `--output`; the
  delivered commands (`code/verify.py`, `/tmp/open-query-smoke`, Part III's
  `python3 code/verify.py` without an output option) and Part III's delivered
  file table are quoted in the notes there.
- Part I's own texts name `python3 code/verify.py --max-n 6` without
  `--output` (Section 12, `Makefile`): that command replaces the files in
  `data/`.
- When Part II was written in, Section 14.1 and this README said "nine"
  research questions and "1–9"; Part II prints ten. Corrected at the batch-56
  write, with a dated note in Section 14.1.

## Research status

Part I's counterexample directly refutes the question as printed in the
retrieved v3; Part II extends Part I's finite normal form and Cantor–Bendixson
analysis from a membership bit to `q` output labels, with sharp constants and
a two-versus-three-label complexity dichotomy, and reproduces Part I's values
at `q = 2`. Part III answers Part II's Research question 1 on Hausdorff spaces
with a finite nonempty derived set, through local filter capacities, and
shows by a three-label separation that rank and derivative sizes do not
determine the finite-output invariant; heights `h ≥ 2` and infinite derived
sets remain open (Research questions 11, 12 and 14). No part claims a
resolution of all the paper's open questions, independent peer review, or
proof-assistant formalization. No priority conclusion follows merely from
not finding an earlier resolution. Classical difference-hierarchy machinery,
the multi-valued partition literature, the modified-SCS hardness theorem and
the directed-feedback-vertex-set literature are explicitly credited in the
article.

## Relation to neighbouring reports and to the formal project

Two other reports in `games-on-ordinals/` study games on ordinal spaces:
[`point-separating-game-values`](../point-separating-game-values) answers
Problem 1.2 of the same Chiozini–Csernák–Soukup paper (point-separating game
values), a different question from the one Part I answers, and
[`ordinal-chomp-transition-at-two`](../ordinal-chomp-transition-at-two)
studies ordinal Chomp. Parts II and III bear on neither, so no reciprocal
note was written. The report sits in the research-report collection of the
`SetTheory/Cardinals` Lean project, whose library is about large cardinals
(it uses ultrafilters for that purpose, not for these games). That placement
confers no formal status: no Lean or Rocq declaration anywhere in ProveIt
formalizes any statement of Parts I–III (a search of the repository's
`.lean` and `.v` files for open-query games, set-membership numbers,
cut-and-choose games, supersequences, feedback vertex sets and partition
capacities finds none). Section 26.3 records the Lean formalization plan
manuscript 12 proposes (words and greedy embeddings, query trees and suffix
openness, the chain-language equivalence, a certified checker, then the
towers), and Section 39.3 the route manuscript 05 proposes (normal form,
digraphs and the feedback-set word, the filter partition lemma, then the
decomposition, capacities and the extremal theorem); none of it has been
started.

## Sources and attribution

Lucas Chiozini, Tamás Csernák, Lajos Soukup, *Gamification of the
T0-pseudoweight via cut-and-choose games on topological spaces*,
arXiv:2510.05754v3 (earlier title *Cut-and-choose games in topological
spaces*), Problem 1.3 and Theorem 3.4. https://arxiv.org/abs/2510.05754

Aurélie Lagoutte, Sébastien Tavenas, *The complexity of Shortest Common
Supersequence for inputs with no identical consecutive letters*,
arXiv:1309.0422v2, Corollary 6. https://arxiv.org/abs/1309.0422

Alexander Göke, Dániel Marx, Matthias Mnich, *Parameterized Algorithms for
Generalizations of Directed Feedback Vertex Set*, arXiv:2003.02483 — the
NP-completeness of directed feedback vertex set used by Part III.
https://arxiv.org/abs/2003.02483

Célia Borlido, Mai Gehrke, Andreas Krebs, Howard Straubing, *Difference
hierarchies and duality with an application to formal languages*, Topology
and its Applications 273 (2020), 106975; Borys Álvarez-Samaniego, Andrés
Merino, *Some properties related to the Cantor–Bendixson derivative on a
Polish space*, New Zealand J. Math. 50 (2020), 207–218; Victor Selivanov,
*Towards a Descriptive Theory of cb_0-Spaces*, arXiv:1406.3942; Saeed Akbari,
Amir Hossein Ghodrati, Afrouz Jabalameli, Morteza Saghafian, *Chromatic
Number and Dichromatic Polynomial of Digraphs*, arXiv:1711.06293; Shamil
Asgarli, Donald Falkenhagen, Kaya Hoshi, *Improved lower bounds for the
maximum order of an induced acyclic subgraph*, arXiv:2511.02819v3 — cited as
background, not as sources of the new game computations. No third-party
papers or font files are bundled.
