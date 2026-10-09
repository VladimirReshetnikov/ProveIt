# Sparse Graph Moments: Closed Tree Walks (OEIS A094149)

**Part I: fixed collision orders and smooth inverse centers. Part II: the
full sparse graph moment equivalent. Part III: dominant vertices. Part IV:
larger tree walk lower bounds. Part V: a shifted Bell lower bound. Five
successive studies of one sequence.**

**Part VI (added 9 October 2026): general mean degree `c`.** For the moments
`m_k(c)` of `G(N, c/N)` (`m_k(1) = M_{2k}`), uniformly for `c` in any compact
subset of `(0, ∞)`: all fixed collision orders,
`m_k(c)/(2H_k(c)) = 1 + Σ_{j≤p} A_j(k,c) + O(log^{10p+6}k/k^{p+1})`,
`H_k(c) = E(X+c)^k`, `X ~ Pois(c)` (`2B_{k+1}` at `c = 1`), with
`log(m_k(c)/2H_k(c)) = c w²(w+2+2c)/(2k) + c w⁵/(6k²) + O(w⁴/k²)`,
`w = W(k/c)`; a signed Poisson–Charlier law for the maximum-departure deficit
with sharp total-variation constants `√(c/2π) w^{5/2}/k` (against `Pois(cw)`)
and `φ(1) w²/k` (optimal over all Poisson means); and a growing-degree
transition `m_k(c)/(2H_k(c)) = e^{c²w²/k}(1 + O(k^{−1/4} log^{13/4} k))` when
`cw/√k` stays in a compact set. It answers Section 56's item `meandegree`, and
`suborders` in part; not `growing`.

A report in six Parts. Parts I–V were built from five manuscripts of one
external research session (the session bundle of Reports 1–243, arrival
commit `60f54ea06`), placed by `f79c9bef1` (batch 112) and written on
7 October 2026; none names an author, a tool or an addressee, and every PDF
author field is empty. Part VI is a manuscript of 8 October 2026, "Research
manuscript prepared with OpenAI assistance for the ProveIt project" (title
page and PDF author), written into the report on 9 October 2026.

**The object.** `M_{2k}` (written `a_k` in Parts I–II) counts the closed walks
`(v_0, …, v_{2k−1}, v_0)` whose traversed edges form a tree, up to relabelling
of vertices, with time zero distinguished. For `k ≥ 1` this is OEIS A094149
and the `2k`-th moment of the limiting expected spectral measure of the
unscaled adjacency matrix of `G(N, 1/N)` (`k` fixed before `N → ∞`). `B_n`
are the Bell numbers and `W` the principal Lambert function.

**The Parts are one chain**, written in the order 209, 210, 212, 213, 214 and
printed newest first. Each later manuscript proves something an earlier one
left open; every superseded statement is printed as delivered with a dated
note.

| Source | Bundle report | Archive | Placed | Printed as |
|---|---|---|---|---|
| *Fixed collision orders and smooth inverse centers for A094149* (title block "Report214", 4 October 2026); the base | 214 | `Report214-reproducibility.zip` (615,513 bytes, 21 files; `Report214.tex`, 1051 lines, 25 pp.) | `f79c9bef1` | Part I, Sections 1–13, Appendices A–B |
| *The full sparse graph moment equivalent* ("Report213") | 213 | `Report213-reproducibility.zip` (579,496 bytes, 20 files; 831 lines, 20 pp.) | `f79c9bef1` | Part II, Sections 14–27, Appendix A |
| *Dominant vertices in sparse graph moments* ("Report212") | 212 | `Report212-reproducibility.zip` (555,569 bytes, 36 files; 578 lines, 16 pp.) | `f79c9bef1` | Part III, Sections 28–38, Appendix A |
| *Larger tree walk lower bounds for sparse graph moments* ("Report210") | 210 | `Report210-reproducibility.zip` (431,307 bytes, 9 files; 438 lines, 12 pp.) | `f79c9bef1` | Part IV, Sections 39–48 |
| *A shifted Bell lower bound for sparse graph moments* ("Report209") | 209 | `Report209-reproducibility.zip` (415,540 bytes, 12 files; 440 lines, 13 pp.) | `f79c9bef1` | Part V, Sections 49–55 |
| *Sparse graph moments: sharp corrections, optimal Poisson laws, and a growing-degree transition* (8 October 2026; batch 138, group OEIS, manuscript 04) | — | `sparse_graph_moments_research.zip` (2,095,612 bytes, 33 files in one wrapper directory; `article.tex` + 5 section files + `references.tex`, 3,006 lines, 40 pp.), arrival `b28d0850b` | `803f4d937` (23 files, prefix `06-meandeg-`) | Part VI, Sections 57–64 (Section 57 added by the write) |

Reports 209–214 are dated 4 October 2026 and record no ProveIt commit, so no
pin is recorded for them. Part VI is pinned to ProveIt `9570aaede2`
(7 October 2026, 21:31 PDT), where this report's `article.tex` is Parts I–V
as merged and checked, and to `openai/math` `adc7f1241b42` (not checked).

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

**Part I (Report 214).** Explicit finite Bell transforms `A_j(k)`, built from
child-return rows through half-length `j + 1`, with, for every fixed `p ≥ 1`,
- **Theorem 1.1:** `a_k/(2B_{k+1}) = 1 + Σ_{j≤p} A_j(k) + O_p(log^{10p+6}k / k^{p+1})`
  and `A_j(k) ~ W(k)^{3j}/(2^j j! k^j)`; in particular the first relative
  correction is `(1/2 + o(1)) W(k)³/k` (6), and after the exact first
  transform `T_k/B_{k+1}` the next is `(1/8 + o(1)) W(k)⁶/k²` (7);
- Proposition 9.1: a finite smooth Poisson interpolation `𝒯_j` of the
  transforms; **Theorem 11.1:** `⌈x − δ_p⌉ ≤ N(L) ≤ ⌈x + δ_p⌉` with
  `x = x_p(L)`, `δ_p = C_p log^{10p+5}x / x^{p+1}` (existential constant);
  Corollary 11.3: displacements of the centres;
- Appendix B: the complement estimate inherited from Report 213, with proof.

**Part II (Report 213).** **Theorem 14.1:** for every window `S_k` with
`S_k/log k → ∞`, `S_k = o(k^{1/3})`, the walks without a vertex of at least
`k − S_k` departures, and the weighted middle-return sum `R_{k,S}`, are
`o(k^{−p} B_{k+1})` for every fixed `p`; hence **`M_{2k} ~ 2B_{k+1}`**.
Theorem 14.2 (the dominant window, printed here once), Proposition 25.1 (a
two-ceiling inverse of radius `o(1/log x)`).

**Part III (Report 212).** **Theorem 28.1** (= Theorem 14.2): the dominant
class has size `(2 + o(1)) B_{k+1}`; Proposition 33.1: `M_{2k} ~ 2B_{k+1}`
follows from `R_{k,S_k} = o(B_{k+1})`, a premise Report 212 does not prove and
Part II does; **Theorem 35.1:** a truncated Poisson-neighbourhood expectation
equals `B_{k+1}[1 + (1/2 + o(1)) W(k)³/k]` (a scalar statement, not about
`M_{2k}`), and two counterexamples to untruncated averaging; finite
diagnostics through `k = 256`.

**Part IV (Report 210).** **Theorems 39.1–39.2:** two disjoint
rotation-closed families counted exactly, `G_k` (all walks whose repeated
edges share a vertex) and `J_k` (a recoverable hub and one repeated secondary
edge), `M_{2k} ≥ G_k + J_k` with equality exactly for `k ≤ 4`,
`G_k = 2B_{k+1}[1 + (1 + o(1)) W(k)²/k]`, `J_k ~ W(k)² B_k`.

**Part V (Report 209).** **Theorem 50.1:** the coefficientwise bound
`I(k,ℓ) ≥ 2Σ_s C(k−1,s) S(k−s,ℓ−s) − C(2k−ℓ, ℓ−1)` and
`M_{2k} ≥ 2(B_{k+1} − B_k) − F_{2k}` (`F` Fibonacci), with equality exactly
for `k ≤ 3`; Corollary 51.2 (`liminf M_{2k}/B_{k+1} ≥ 2`), the weighted
Corollary 52.1, the quantified star estimate Proposition 53.1.

**The write** proves, from Part IV's Theorem 39.2 and Part I's (6)
(**Remark 46.1**):

    0 ≤ (M_{2k} − G_k − J_k)/(2B_{k+1}) = o(W(k)³/k),

so the first relative correction is carried by `J_k` alone, at the
coefficient `1/2` of Part III's scalar Theorem 35.1. It also quotes the OEIS
entry (Remark 1.2) and classifies the inverses (Remark 11.4).

**Part VI (general mean degree, 8 October 2026).** `m_k(c) = Σ c^{e(ω)}`
over normalized closed tree walks (the moment of `G(N, c/N)`, graph-size limit
first), `T_n(c) = E X^n`, `H_k(c) = E(X+c)^k`, `X ~ Pois(c)`, `w = W(k/c)`;
`K` a compact subset of `(0, ∞)`.
- **Theorem 60.4:** the weighted complement and rotation reduction,
  uniformly on `K`; **Theorem 60.6:** for every fixed `p`,
  `m_k(c)/(2H_k(c)) = 1 + Σ_{j≤p} A_j(k,c) + O_{K,p}(log^{10p+6}k/k^{p+1})`,
  `A_j(k,c) ~ c^j w^{3j}/(2^j j! k^j)` (at `c = 1` Part I's Theorem 1.1);
  **Corollary 60.7:** `A_1 = c w²(w+2+2c)/(2k) + O(w⁴/k²)`,
  `m_k/(2H_k) = 1 + P_1 + (c²/8 + o(1)) w⁶/k²`, and
  `log(m_k/2H_k) = P_1 + c w⁵/(6k²) + O(w⁴/k²)`.
- **Theorem 61.1:** for the deficit `D_k = k − max_v d_ω(v)` of the
  moment-weighted walk, a signed Poisson–Charlier expansion about
  `Pois(cw)`; `TV(ν, Pois(cw)) ~ √(c/2π) w^{5/2}/k` and
  `TV(ν, Pois(cw + cw³/k)) ~ φ(1) w²/k`; **Theorem 61.2:** the
  latter is optimal over all Poisson means, with the profile
  `F(t) = ½ E|(Z²−1)/2 − tZ|`; **Corollary 61.6:** a two-jump compound
  Poisson law with error `o(w²/k)`.
- **Theorem 62.1:** uniformly for `a ≤ cw/√k ≤ b`,
  `m_k(c)/(2H_k(c)) = exp(c²w²/k)(1 + O(k^{−1/4} log^{13/4} k))`; `c_k =
  β√k/log k` gives `e^{β²/4}`; the factor is the exact Catalan quotient
  `Q(k,s) = Π_{j<s}(k+j)/(k−j)`; **Corollary 62.6:** simple off-hub edges
  carry all but `O(k^{−1/4} log^{13/4} k)` of the weight.
- Section 63: exact checks (recurrence to `k = 128` at `c = 1/2, 1, 2`,
  brute force `k ≤ 7`, symbolic `d_h`, `P_h`), Table 9, two illustrative
  figures; Section 64: twelve research questions.

The write adds (9 October 2026), with proofs: at `c = 1`,
`(M_{2k} − G_k)/(2B_{k+1}) = W³/(2k) + (1 + o(1))W²/k` (note after Remark
46.1; the remark itself is not sharpened), and Part V's weighted lower bound
equals `2(H_k(c) − cH_{k−1}(c)) − P_k(c)`, hence is asymptotic to
`μ_{2k}(c)` for each fixed `c` (note at the end of Section 56).

(Section, statement and equation numbers are those of the committed PDF.)

## Printed once: the repeated proofs

Reports 212, 213 and 214 repeat whole proof blocks. Each is printed once, at
its first place in the order of the Parts:
- the elementary Bell estimates (Report 213's Appendix A word for word, the
  lemma of Report 212's Appendix A in other words) and Report 213's
  complement proof (its Sections 6–9 and the first part of Section 10, word
  for word up to four named differences) — in **Part I, Appendices A and B**;
- the dominant-window proof (Report 212's Sections 2–5 = Report 213's
  Sections 2–5) — in **Part II, Sections 15–18**.

The omitted blocks keep their section headings, with notes mapping every
numbered object they contained to its printed counterpart (57 labels: 33 of
Report 213, 24 of Report 212); the 8 references to them from the printed
text point to the printed copies. Differently worded or differently stated
proofs are kept (Part II's Sections 14.1–14.2, the Bell-ratio lemmas of
Parts IV and V, the Bell convolution proved in Parts II, IV and V).

## What the report does not claim

- Part I: every order fixed before `k → ∞`; no effective constant or onset;
  the two-ceiling enclosure is existential, not a certified finite-threshold
  procedure, and does not identify a single ceiling; no growing-order
  expansion, exponential resummation or evaluated logarithmic suborders; the
  complement theorem is inherited, the recurrence and the coefficientwise
  comparison are Bauer–Golinelli's.
- Part II: the superpolynomial strength applies to the two tails, not to
  `M_{2k}/(2B_{k+1}) − 1`; no first correction, expansion or effective onset
  (supplied or left open by Part I as recorded); the inverse is existential.
- Part III: the scalar theorem does not identify `M_{2k}` with its
  expectation; the spectral deductions (Section 36.2) are heuristic, and the
  counterexamples refute untruncated averaging, not the cited theorem; no
  monotonicity beyond `k = 256`.
- Parts IV–V: lower bounds only; equivalences there concern the selected
  families.
- Credited, not claimed: Bauer–Golinelli (tree-walk moments, the first-edge
  recurrence, the Stirling–Catalan comparison, the bi-star decomposition, the
  fixed-edge star theorem); Hainzl–de Panafieu (Catalan decorations, kernels);
  Hiesmayr–McKenzie (context only). Every source comparison is bounded; no
  Part claims priority or that a question is globally open. Nothing was
  submitted to the OEIS.
- Part VI (collected in Section 57.4): limiting moments only, graph-size
  limit first, nothing asserted "for a simultaneous limit of finite matrices
  with `k = k_N`"; the growing-degree error "not claimed sharp"; no
  uniformity for growing order; `D_k` is "not the degree of a typical vertex
  of a finite graph"; Bauer–Golinelli the one external input; the `c = 1`
  construction "not claimed anew", and "Merely improving a displayed
  logarithmic exponent in that way is a corollary of the earlier method";
  the source audit "cannot certify worldwide priority"; no peer review or
  formalization; the figures plot labelled models, not the full walk law.

## Further questions, and the standing rule

Section 56 gathers, under Vladimir's standing rule of 4 October 2026, the
open questions and unproved claims of all five Parts (13 items, labels
`sgm:q:`): effective constants and onsets, smaller logarithmic powers,
evaluated suborders, growing order, general mean degree (Parts I–II); a
larger dominant window, canonical hubs, the weighted spectral transfer with
its four missing tasks (Part III's heuristic); exact counts of larger
families, edge-count coefficients near `ℓ ≍ k/W(k)`, bivariate generating
functions (Parts IV–V); monotonicity of `M_{2k}/(2B_{k+1})` after `k = 19`;
the unresolved source comparisons (the 2026 journal version of Hainzl–de
Panafieu, which no Part read, among them). No claim of any Part was found to
be false, so nothing is refuted. Answered within the report, and marked
there: Part III's premise and its questions 1 and 5, Part II's first two
further directions, Part IV's and Part V's statements that the equivalent
does not follow from them, Part IV's leading-scale question and Part V's
first question.

**After Part VI** (dated note at the end of Section 56; the earlier notes
are kept): `meandegree` **answered** for compact `c` (Theorem 60.6; its own
complement Theorem 60.4); `suborders` **answered in part** (the whole scale
`1/k`, at `c = 1` `W³/(2k) + 2W²/k`, and the `w⁶`, `w⁵` terms at `k^{−2}`;
the lower suborders open); `growing` **not answered** — the intake's triage
read Part VI's growing *mean degree* as item `growing`, which is a growing
*collision order*; the transition is a new direction. `window`, `hubs`: not
answered. Part VI's own twelve research questions (`sgm:md:q:*`: the
critical first correction, a uniform passage from compact to growing `c`,
beyond the critical window, vanishing `c`, sharper positive approximations,
local laws at critical degree, joint hub statistics, several dominant
vertices, finite-graph transfer, spectral tails, weighted edges and other
offspring laws, effective bounds and formalization) stay open; no claim of
Part VI was found wrong.

## The OEIS entry

A094149 (revision #10, 13 July 2025; Alexey Spiridonov, 4 May 2004) lists 13
terms and records "Asymptotically between A_k (the k-th Bell number, A000110)
and choose(2k, k)*A_k." Remark 1.2: the 13 terms were recomputed; the formula
line is a correct pair of bounds (`B_k ≤ M_{2k} ≤ Cat_k B_k`), neither of
which is sharp, by Part II. The entry has no conjecture, so none is settled.
Read again at Part VI's write (9 October 2026): revision #10, unchanged.
The quoted sentence is the middle one of the formula line. The full line is
"See [link:1] for a complex recurrence relationship. Asymptotically between
A_k (the k-th Bell number, A000110) and choose(2k, k)*A_k. (see [ref:1])."
Remark 1.2 carries a dated correction to that effect.

## The inverses and the transseries volume

Remark 11.4, against
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
Part I's Theorem 11.1 and Part II's Proposition 25.1 bracket the integer
staircase (`p0:def:three-inverses`(1)) around the inverse of a smooth
comparison function that is not an interpolation of `a_k`, proved directly at
the integers — analogues of `p0:thm:staircase`(2), not instances; the centres
are implicit inverses, the Bell scale is outside `p0:def:model`, and they are
not shown to be instances of `p0:thm:lambert-core`,
`p0:thm:lambert-centered` or `plt:thm:lw-template`; the correction scale
`W(k)^{3j}/k^j = r^{2j} e^{−jr}` uses the transmonomial `e^{−r}` of the
volume's Bell chapter (`q2:rem:bell-scale`), whose expansion the Parts do not
use.

## Relation to the repository

`a064856-stirling-catalan-transforms` (same directory) proves
`B_k ≤ M_{2k} ≤ a_k` for the Stirling transform of the Catalan numbers and
names the relative asymptotics of `M_{2k}` as open (item `stc:q:moments`),
listing these five archives as unchecked leads. Part II answers that item,
and its conditional remark (`M_{2k}/a_k → 0` if `M_{2k} ~ 2B_{k+1}`) becomes
unconditional; a reciprocal note there is a separate commit (`f8f9eb33b`,
checked with this report, see below). Neighbours by
method: `a277364-bell-asymptotics`, `a088714-bell-scale-growth`. No Lean or
Rocq development treats these sequences.

Part VI: its account of Parts I–V (the `c = 1` dominant-vertex reduction and
all fixed collision orders; general mean degree listed as a further
question) is correct; it credits them as the "direct repository precursor".
No other report treats `G(N, c/N)` moments for general `c`, so no reciprocal
note is needed. Its proposal of a sibling report
`a094149-weighted-moments-and-critical-transition/` was declined at
placement (one report per A-number).

## Labels and numbering

All labels carry the prefix `sgm:`: Part I `sgm:co:` (Report 214's 129
labels), Part II `sgm:eq:` (62 of Report 213's 95 printed), Part III `sgm:dv:`
(37 of Report 212's 61), Part IV `sgm:lw:` (Report 210's 39, with its table
label, plus the write's `sgm:lw:sec:what`), Part V `sgm:sb:` (Report 209's
33, with its table labels), and the write's (`sgm:sec:guide`,
`sgm:sec:questions`, `sgm:q:*`, the Part labels, `sgm:co:rem:oeis`,
`sgm:co:rem:transseries`, `sgm:lw:rem:union`); 324 in all. The delivered
labels were prefixed before anything cited them.

| Part | Manuscript | Sections | Statements | Equations | Tables |
|---|---|---|---|---|---|
| I | Report 214 | 1–13, A, B, unchanged | unchanged | (1)–(89), unchanged | 1–2 |
| II | Report 213 | `k + 13` (14–27), A | `(k + 13).j` | `(k + 89)` (90–155) | 3 |
| III | Report 212 | `k + 27` (28–38), A | `(k + 27).j` | `(k + 155)` (156–194) | 4–5 |
| IV | Report 210 | `k + 38` (39–48) | `(k + 38).j` | `(k + 194)` (195–227) | 6 |
| V | Report 209 | `k + 48` (49–55) | `(k + 48).j` | `(k + 227)` (228–250) | 7–8 |
| VI | manuscript of 8 October 2026 | `k + 57` (58–64; 57 the write's) | `(k + 57).j` | `(k + 57).j`, within sections | 9 |

The equations not printed again keep their places in the count. Every
printed delivered number was checked against the `.aux` files of separate
builds of the five delivered sources (300 labels, 0 differences). Part VI
(9 October 2026): its 158 labels carry `sgm:md:` and its 192 references (144
`\eqref`, 48 `\ref`) were updated; from Part VI on equations are numbered
within sections, as delivered (`\counterwithin`), so Parts I–V keep their
consecutive numbers; its research questions are `(k + 57).j` too; its Table 1
is Table 9 and its Figures 1–2 keep their numbers (Parts I–V have none). The
write added 19 labels (`sgm:md:part`, `sgm:md:sec:front` and five
subsections, twelve `sgm:md:q:*`). Against builds of the committed text, of
the delivered manuscript (40 pp.) and of this one: all 324 earlier labels
unchanged; all 158 Part VI labels at the stated shift; 501 labels in all. Report 210
names its own Sections 1, 4 and 5–7 by number in its text; they are Sections
39, 42 and 43–45 here (stated in its Part header).

## Notation

No symbol was renamed. Many letters differ in meaning across the Parts:
`F` (root-return rows versus Part V's Fibonacci numbers), `C`/`Cat`
(Catalan numbers, Part II's complement count, Part IV's partition count),
`A`, `E`, `G`, `H`, `J`, `T` (Part I's `T_k` and Part IV's `T_k` are
different numbers), `R`, `S` (window versus Stirling numbers versus Part IV's
`S_k`), `L`, `P`, `Q`, `D`, `U`, `N`, `δ` (Part III's `δ_k` is Part IV's
`η_k`, not its `δ_k`), `η`, `r`, `x`, `Z`, `d`, `h`, `q`, `λ`, `μ`. The
front-matter table "Reading conventions" lists them with the tempting false
readings.

Part VI keeps its letters (table in Section 57.5). The dangerous ones: its
`T_n(c)` is a Touchard polynomial (Part I's `T_k` is a transform sum); `H_k(c)
= E(X+c)^k`; `D_k` the deficit (Parts I–III's two-hub count); `Q(k,s)` a
Catalan quotient (Parts II–IV's `Q_k = B_{k+1}`); `P_1(k,c)` versus Bell
polynomials `P_h`; `w = W(k/c)` (Parts III–IV write `r = W(k)`); `v_t` has two
meanings within Part VI; its weighted `E^c_{t,q}`, `R_c`, `γ_h`, `d_h`, `P_h`,
`G_j`, `A_j(k,c)` are Part I's at `c = 1`. Five macros differ in typography
and are switched at Part VI's start: `\Poi` (Pois), `\Stir`, `\Part`
(`𝒫[n]`), `\fall` (`x^{\underline h}` = Part I's `(x)_h`), `\rise`; its `\P`
is `ℙ`.

## The write's additions

The front matter (Guide with the chain, the duplication and numbering rules,
provenance, what was checked, the collected non-claims, the notation table),
the `\partsource` blocks, Remarks 1.2, 11.4 and 46.1, the notes under the 11
omitted blocks and 13 further dated notes in the Parts, Section 56, the label prefixes, a
label for Report 210's Section 8, one merged bibliography (the five Parts use
the same keys; each entry keeps every variant's details, with a bracketed
note; `TSvol` added), and the references from printed text to the omitted
blocks (8, pointed to the printed copies). The preamble is the union of the
five delivered preambles plus `xcolor`, `xurl` and `longtable`. Everything
else is delivered text.

Part VI's write (9 October 2026): Section 57 (provenance, merge, what it
answers, checks, non-claims, notation), the Part header and source block,
a note in the Guide and the Guide table's Part VI row, notes after Remark
46.1 and at the end of Section 56, four notes inside Part VI (Sections 58.2,
60.7, 63 and 64), labels on its twelve questions, eight bibliography entries
marked [Part VI] and Part VI's details added to `bg`, `hdp`, `khor1`, `oeis`;
`graphicx`, a `definition` style, a `question` environment and `\TV`,
`\normone`, `\Var` added to the preamble; title, author, date, running head
and PDF fields extended.

## Files

```text
README.md                                            this guide (replaces Report 214's delivered README.txt)
article.tex                                          the merged report (delivered Report214.tex, merged with Reports 213, 212, 210, 209)
article.pdf                                          compiled report, 135 pages
06-meandeg-source_audit.txt                          Part VI: bounded source and priority audit (delivered source_audit.txt)
209-shifted-SOURCES.txt                              Part V: source ledger (delivered SOURCES.txt)
210-walks-SOURCES.txt                                Part IV: source ledger
212-hubs-CODE_README.md                              Part III: computation guide (delivered CODE_README.md)
212-hubs-SOURCES.txt                                 Part III: source ledger
213-equiv-SOURCES.txt                                Part II: source ledger
213-equiv-SOURCE_FILES.txt                           Part II: delivered source inventory
213-equiv-code-README.md                             Part II: finite-check guide (delivered code/README.md)
214-orders-SOURCES.txt                               Part I: source ledger
214-orders-SOURCE_FILES.txt                          Part I: delivered source inventory
214-orders-code-README.md                            Part I: finite-check guide (delivered code/README.md)
code/06-meandeg-Makefile                             Part VI: pdf/verify/clean targets (delivered Makefile)
code/06-meandeg-build.sh                             Part VI: PDF build script (delivered build.sh)
code/06-meandeg-numerical_diagnostics.py             Part VI: floating diagnostics, figures and the moment table
code/06-meandeg-verify_exact.py                      Part VI: first-child recurrence (c = 1/2, 1, 2), brute force k <= 7
code/06-meandeg-verify_symbolic.py                   Part VI: rows with indeterminate c, d_h, P_h, Catalan products
code/209-shifted-reproduce.py                        Part V: data/PDF/ZIP driver (delivered reproduce.py)
code/209-shifted-verify_lower_bound.py               Part V: exhaustive walk DFS (k <= 8), coefficient checks
code/209-shifted-verify_recurrence.py                Part V: Bauer-Golinelli recurrence (k <= 16)
code/210-walks-reproduce.py                          Part IV: data/PDF/ZIP driver
code/210-walks-verify_families.py                    Part IV: exact family audits
code/212-hubs-code-reproduce.py                      Part III: finite workflow (delivered code/reproduce.py)
code/212-hubs-common.py                              Part III: shared routines (delivered code/)
code/212-hubs-diagnostics.py                         Part III: table diagnostics (delivered code/)
code/212-hubs-independent_audit_checks.py            Part III: enumeration and recurrence audits (delivered code/)
code/212-hubs-make_tables.py                         Part III: table generator (delivered code/)
code/212-hubs-moments.cpp                            Part III: C++/GMP row generator (delivered code/)
code/212-hubs-reproduce.py                           Part III: outer driver (delivered reproduce.py)
code/212-hubs-reproduce.sh                           Part III: shell wrapper (delivered reproduce.sh)
code/212-hubs-verify_cli_guards.py                   Part III: CLI guard tests (delivered code/)
code/212-hubs-verify_guard_failures.py               Part III: corruption tests (delivered code/)
code/213-equiv-code-reproduce.py                     Part II: finite harness (delivered code/reproduce.py)
code/213-equiv-common.py                             Part II: shared routines (delivered code/)
code/213-equiv-finite_checks.py                      Part II: finite checks (delivered code/)
code/213-equiv-reproduce.py                          Part II: outer driver (delivered reproduce.py)
code/214-orders-code-reproduce.py                    Part I: finite harness (delivered code/reproduce.py)
code/214-orders-common.py                            Part I: shared routines (delivered code/)
code/214-orders-finite_checks.py                     Part I: finite checks (delivered code/)
code/214-orders-reproduce.py                         Part I: outer driver (delivered reproduce.py)
data/06-meandeg-claim_ledger.json                    Part VI: claims, regimes, proof locations (delivered at the root)
data/06-meandeg-collision_polynomials.tex            Part VI: generated P_2..P_4 (not input by the article)
data/06-meandeg-critical_diagnostics.json            Part VI: 28 critical-window cases (Figure 2)
data/06-meandeg-deficit_diagnostics.json             Part VI: 21 first-collision model cases (Figure 1)
data/06-meandeg-exact_checks.json                    Part VI: counts of the exact checks
data/06-meandeg-exact_rows.json                      Part VI: exact scaled rows and moments to k = 128 (2,888,373 bytes)
data/06-meandeg-moment_diagnostics.json              Part VI: 12 finite-moment rows
data/06-meandeg-moment_table.tex                     Part VI: Table 9, input by the article
data/06-meandeg-numerical_summary.json               Part VI: scope and stability metadata
data/06-meandeg-provenance.json                      Part VI: pins and environment (delivered at the root)
data/06-meandeg-requirements.txt                     Part VI: requirements (delivered at the root)
data/06-meandeg-symbolic_checks.json                 Part VI: symbolic-check output
data/06-meandeg-verification_report.json             Part VI: build and review record (delivered at the root)
data/209-shifted-exact_checks.json                   Part V: recorded verifier output
data/209-shifted-recurrence_reference.json           Part V: recorded recurrence rows and checks
data/209-shifted-requirements.txt                    Part V: requirements
data/209-shifted-tables-coefficients.tex             Part V: Table 8 as delivered (printed inline)
data/209-shifted-tables-exact.tex                    Part V: Table 7 as delivered (printed inline)
data/210-walks-exact_checks.json                     Part IV: recorded verifier output
data/210-walks-requirements.txt                      Part IV: requirements
data/210-walks-tables-exact.tex                      Part IV: Table 6 as delivered (printed inline)
data/212-hubs-CODE_INVENTORY.txt                     Part III: delivered code inventory
data/212-hubs-fixture32-moments_exact.tsv            Part III: fixture, moments through k = 32
data/212-hubs-fixture32-root_counts_exact.tsv        Part III: fixture, root-return rows through k = 32
data/212-hubs-generation256_reference.json           Part III: digest reference of the k <= 256 generation
data/212-hubs-reference_totals_k16.tsv               Part III: edge-resolved reference totals, k <= 16
data/212-hubs-requirements.txt                       Part III: requirements
data/212-hubs-tables-numeric_table.tsv               Part III: table values
data/212-hubs-tables-numeric_table_log_squared.tex   Part III: Table 5 as delivered (printed inline)
data/212-hubs-tables-numeric_table_quarter.tex       Part III: Table 4 as delivered (printed inline)
data/212-hubs-tables-table_values.json               Part III: exact table values
data/212-hubs-verification-audit_fixture32.json      Part III: recorded audit (fixture)
data/212-hubs-verification-audit_regenerated256.json Part III: recorded audit (k <= 256)
data/212-hubs-verification-cli_guard_checks.json     Part III: recorded CLI guard checks
data/212-hubs-verification-diagnostics_fixture32.json      Part III: recorded diagnostics (fixture)
data/212-hubs-verification-diagnostics_regenerated256.json Part III: recorded diagnostics (k <= 256)
data/212-hubs-verification-full_replay_metadata.json  Part III: recorded full replay
data/212-hubs-verification-guard_failure_checks.json  Part III: recorded corruption tests
data/212-hubs-verification-package_metadata.json      Part III: recorded package metadata
data/212-hubs-verification-quick_replay_metadata.json Part III: recorded quick replay
data/212-hubs-verification-table_regeneration256.json Part III: recorded table regeneration
data/213-equiv-code-results-checks.json              Part II: recorded finite-check counts
data/213-equiv-code-results-moments.csv              Part II: exact moments, k <= 32
data/213-equiv-code-results-selected_table.csv       Part II: selected table values
data/213-equiv-code-results-table.tex                Part II: generated table
data/213-equiv-code-verification-guard_checks.json   Part II: recorded guard checks
data/213-equiv-code-verification-reproduction.json   Part II: recorded reproduction receipt
data/213-equiv-code-verification-two_mode_verification.json Part II: recorded normal/-O comparison
data/213-equiv-requirements.txt                      Part II: requirements
data/213-equiv-tables-table.tex                      Part II: Table 3 as delivered (printed inline)
data/214-orders-code-results-checks.json             Part I: recorded finite-check counts
data/214-orders-code-results-polynomials.json        Part I: exact d_h, P_h and transform data
data/214-orders-code-results-rows.tex                Part I: generated rows table
data/214-orders-code-results-selected_table.csv      Part I: selected table values
data/214-orders-code-results-table.tex               Part I: generated corrections table
data/214-orders-code-verification-guard_checks.json  Part I: recorded guard checks
data/214-orders-code-verification-reproduction.json  Part I: recorded reproduction receipt
data/214-orders-requirements.txt                     Part I: requirements
data/214-orders-tables-rows.tex                      Part I: Table 1 as delivered (printed inline)
data/214-orders-tables-table.tex                     Part I: Table 2 as delivered (printed inline)
figures/06-meandeg-critical_transition.pdf           Part VI: Figure 2, included
figures/06-meandeg-critical_transition.png           Part VI: its raster preview
figures/06-meandeg-deficit_profiles.pdf              Part VI: Figure 1, included
figures/06-meandeg-deficit_profiles.png              Part VI: its raster preview
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery (106 files in the directory). Within-package equal pairs are kept as
delivered records: each `tables/*.tex` of Reports 213 and 214 equals the
corresponding `code/results/` file, and Report 214's `requirements.txt` equals
Report 213's. Not shipped (retrievable from `60f54ea06`): the five delivered
PDFs; the texts and delivered READMEs of Reports 209, 210, 212 and 213 (the
texts are Parts V, IV, III and II; Report 214's README.txt was staged and is
replaced by this guide); and the three checksum manifests `MANIFEST.json` of
Reports 212, 213 and 214 (35, 19 and 20 entries), verified at the write.
Part VI, not shipped (retrievable from `b28d0850b`): `article.tex` (20,981 bytes),
the five section files and `references.tex` (printed in the article), `article.pdf`
(597,839 bytes, 40 pages), the delivery `README.md` (6,595 bytes; summarized in
Section 57 and above) and `SHA256SUMS` (2,855 bytes).

```sh
for R in 209 210 212 213 214; do
  git show 60f54ea06:docs/incoming/Report$R-reproducibility.zip > <scratch>/r$R.zip
done
```

**Delivered text that names the delivery layout or files not shipped.** The
programs import their siblings and read their baselines by delivered names
(`code/common.py`, `code/results/…`, `tables/…`, `data/…`); the outer drivers
(`*-reproduce.py` without `code-`, `212-hubs-reproduce.sh`) check the closed
delivered inventory, including the manuscripts, PDFs and `MANIFEST.json`, so
they run only in a re-extracted archive; the source ledgers, the code guides
and `SOURCE_FILES.txt` use delivered paths; and the Parts' sections on
reproduction describe the delivered archives.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
T=$(mktemp -d)
for P in 214-orders 213-equiv; do
  mkdir -p "$T/$P/code/results"
  cp "code/$P-common.py" "$T/$P/code/common.py"
  cp "code/$P-finite_checks.py" "$T/$P/code/finite_checks.py"
  for f in data/$P-code-results-*; do b=$(basename "$f"); cp "$f" "$T/$P/code/results/${b#$P-code-results-}"; done
  (cd "$T/$P" && py -B code/finite_checks.py --out "$T/$P-out" --compare code/results) && echo "same $P"
done
mkdir -p "$T/210" && cp code/210-walks-verify_families.py "$T/210/verify_families.py"
(cd "$T/210" && py -B verify_families.py | tail -n 1)
mkdir -p "$T/209" && cp code/209-shifted-verify_recurrence.py "$T/209/verify_recurrence.py" \
  && cp code/209-shifted-verify_lower_bound.py "$T/209/verify_lower_bound.py"
(cd "$T/209" && py -B verify_recurrence.py >/dev/null && py -B verify_lower_bound.py | tail -n 1)
```

At the write (7 October 2026, Windows, Python 3.14.4) these ran this way:
Report 214's and Report 213's finite checks reproduced all five and four
recorded results (the `--compare` option requires byte agreement with the
shipped results); Report 210's verifier printed "PASS: 419450 explicit
guards; no floating-point checks"; Report 209's verifiers passed. Report
212's workflows (`212-hubs-CODE_README.md`) need its fixture layout, and the
full one a C++17 compiler with GMP; they were not rerun by the write, which
recomputed the rows independently for `k ≤ 128` instead (Part III's
Section 34.1 note). The outer drivers and PDF/ZIP builders were not run.

**Part VI** (standard library for the exact checks; SymPy, NumPy, SciPy,
Matplotlib for the others), on a copy with the delivered names:

```sh
V=$(mktemp -d); mkdir -p "$V/code" "$V/data"
for f in verify_exact verify_symbolic numerical_diagnostics; do cp "code/06-meandeg-$f.py" "$V/code/$f.py"; done
cd "$V" && py -B code/verify_exact.py --order 128 --enumerate-through 7   # writes data/exact_rows.json, data/exact_checks.json
py -B code/verify_symbolic.py && py -B code/numerical_diagnostics.py
```

At the write (9 October 2026) the shipped programs were not rerun: the
intake's own recurrence (`k ≤ 48`) and the write's own integer-scaled
recurrence (`k ≤ 128`, all three `c`) reproduce every scaled moment of
`data/06-meandeg-exact_rows.json`, and the write's SymPy rows reproduce the
symbolic polynomials and Table 9 (Section 57.3).

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`e4199e04f`) recomputed every
number the write added, with its own code. It used a different method wherever
one was available. The check is recorded in a dated note at the end of
Section 56.

- **Brute force for `k ≤ 9`** (467,963 walks at `k = 9`). It confirmed the rows
  `F_{k,m}`, the coefficientwise Bauer–Golinelli comparison, `G_k` (by the
  geometric predicate) and `J_k` (by the defining conditions on a centre)
  against (197)–(198), including `J_8 = 360` and `J_9 = 9180`. It also
  confirmed `U_{k,S}` against the two-hub formula (116) for every admissible
  `S`.
- **Own recurrence for `k ≤ 256`**, one step beyond the write's 128. The
  maximum of `M_{2k}/(2B_{k+1})` is `4.7128100813441074388…` at `k = 19`, and
  the decrease is strict through 256. Every entry of Tables 3–7 agrees,
  including the `k = 256` rows of Tables 4–5, which nobody had recomputed
  before. The equality set of (234) is `{1, 2, 3}`.
- **`A_1`, `A_2` from the definitions (26)–(27).** Marked blocks were counted
  directly, not through the EGF (35). All 28 entries of Table 2, `T_k`, `d_2`,
  `d_3`, `P_2` and `P_3` agree.
- **Remarks 1.2, 11.4 and 46.1.** The bounds of Remark 1.2 and the strict
  increase of `a_k` hold for `k ≤ 256`. The classifications of Remark 11.4
  were re-read against the volume: `p0:def:model`, `p0:def:three-inverses`,
  `p0:thm:staircase` and `q2:rem:bell-scale`. Remark 46.1 was re-derived. As a
  finite illustration only, `((M−G−J)/(2B_{k+1}))/(W³/k)` is 4.46, 0.89 and
  0.23 at `k = 16`, 64 and 256.
- **Provenance and numbering.** Archive sizes, file and line counts, and
  delivered page counts are confirmed. The three manifests verify. All 80
  staged files are byte-identical to the delivery. The 57 number mappings in
  the notes under the omitted blocks name the right objects. The `.aux`
  files of the five delivered builds give 300 printed labels, each with its
  number unchanged up to the stated shifts; 324 labels in all. The named
  differences between the repeated blocks were confirmed by word diff.
- **Reciprocal note in `a064856-stirling-catalan-transforms` (`f8f9eb33b`).**
  `M_{2k}/B_k ~ 2k/W(k) → ∞`, and `M_{2k}/a_k → 0` because
  `log(a_k/B_k) ~ (log 4)k/log k` is superlogarithmic. On `k ≤ 32`,
  `B_k ≤ M_{2k} ≤ a_k` holds, and `M_{2k}/a_k` is 1 for `k ≤ 3`, then
  decreases strictly to `5.065e-5`. All confirmed.
- **Corrected by a dated note.** Remark 1.2 quoted one sentence of the OEIS
  formula line as the whole line. Its "no asymptotic formula" means no
  asymptotic equivalent: the bounds sentence is the entry's only asymptotic
  statement.

Nothing else was found wrong. Rebuilt: 87 pages (86), label numbers unchanged.

## Build

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
geometry, microtype, xcolor, hyperref, xurl, fancyhdr, lmodern, graphicx).
Part VI inputs `data/06-meandeg-moment_table.tex` and the two
`figures/06-meandeg-*.pdf`. In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; mkdir "$B/data" "$B/figures"
cp data/06-meandeg-moment_table.tex "$B/data/"; cp figures/06-meandeg-*.pdf "$B/figures/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (three passes) on
9 October 2026, at Part VI's write: 135 pages; no errors or warnings, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes; changed pages rendered and
inspected. The delivered Part VI manuscript builds to 40 pages without
warnings. At the first write (7 October 2026; rebuilt after the independent
check, three passes): 87 pages (86 at the write); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered sources, built the same way, give 25, 20, 16,
12 and 13 pages (Report 209's with one underfull box in its bibliography).

## Provenance

- Batch 112 of `docs/incoming`, cluster SGM: bundle Reports 214, 213, 212,
  210 and 209 (arrival `60f54ea06`), placed by `f79c9bef1` with the prefixes
  `214-orders-`, `213-equiv-`, `212-hubs-`, `210-walks-` and `209-shifted-`;
  written 7 October 2026.
- Merge decisions: one report, since the five manuscripts are one chain on
  one object; Report 214 the base (the most general, and it restates Report
  213's complement proof in full); newest first; each repeated proof block
  printed once; one bibliography.
- Sources cited by the Parts: OEIS A094149; Bauer–Golinelli (2001);
  Khorunzhy–Vengerovsky (2000); Spiridonov's thesis; Hainzl–de Panafieu
  (2024, journal 2026); Hainzl (hypergraph Catalan numbers);
  Janson–Jonsson–Stefánsson; Janson; Hiesmayr–McKenzie;
  Bhattacharya–Bhattacharya–Ganguly; Addario-Berry–Lugosi–Oliveira;
  Heydenreich–Müller–Terveer; Bordenave; Valigi et al.; two papers of
  Khorunzhiy; and the repository's transseries volume (added by the write).
- Part VI: batch 138 of `docs/incoming`, group OEIS, manuscript 04 (arrival
  `b28d0850b`), placed by `803f4d937` with the prefix `06-meandeg-` (Part
  number as for `a373271`'s `03-fluct-`); written 9 October 2026, appended
  after Section 56 as Sections 57–64. Sources it cites besides those above:
  Khorunzhy–Shcherbina–Vengerovsky (2004), Khorunzhiy (2020/2022), Pittel
  (1997), Arratia–Goldstein–Gordon (1990, listed only), Semerjian–Cugliandolo
  (2002), Rodgers–Bray (1988), this report at `9570aaede2`, `openai/math` at
  `adc7f1241b42`.
