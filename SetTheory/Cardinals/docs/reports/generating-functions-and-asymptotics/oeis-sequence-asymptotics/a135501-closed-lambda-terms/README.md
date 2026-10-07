# Closed Lambda Terms

**All logarithmic orders, a controlled threshold inverse, and the random binding geometry of a closed term, for OEIS A135501 and A220894**

This is a research report built on 5 October 2026 (write batch 103) from
two manuscripts of one external research session, Reports 110 and 109 of
the session bundle of Reports 1–243, both dated 2 October 2026. Both count
the closed lambda terms of size `n` up to alpha-equivalence, `A_s(n)`, when
abstractions and applications have size one and variable occurrences size
`s ∈ {0, 1}`: `A_1` is [A135501](https://oeis.org/A135501)
(`0, 0, 1, 2, 4, 13, 42, 139, …`) and `A_0` is
[A220894](https://oeis.org/A220894) (`0, 1, 3, 14, 82, 579, …`).
Throughout `r = s + 1`, `N = n + 1`, `t = W(4eN e^{−r/2})` and
`M_r(N) = (N/r)(t − 2 + 1/t) + N/2`.

- **Part I** (Report 110, the base): `M_r(N) − O(log N) ≤ log A_s(n) ≤ M_r(N) + O(R_r(N))`,
  `R_r(N) = N^{1−1/(3r)} (log N)^{−2/3+1/(3r)}`, hence every fixed
  inverse-logarithmic order of `log A_s(n)` (polynomials `P_j`, a recurrence
  for all orders), in particular the coefficient `1/2 − (log 4)/r` of
  `n/log n`; a controlled threshold inverse with an asymmetric bracket.
- **Part II** (Report 109): the weaker four-scale form
  `log A_s(n) = (N/r)(w − 2 + 1/w) + O(N/log N)`, `w = W(4eN)`, as a second
  route, with a weaker inverse; the skeleton sandwich; and a joint
  large-deviation principle at speed `n` for the scaled number of abstractions
  `T_n = U_n log N/N` and maximum unary height `X_n = H_n log N/N` of a
  uniform random closed term, rate `(t − 1 − log x)/r` on `0 < x ≤ t`, with
  `L^p` convergence of both to 1 and the deficit rate `d/r`.
- **Added by the write**: Remark 18.1, which shows from Part I's estimates
  that Part II's open ratio `R(b,u) = A(b,u)/(C_b u^{b+1})` satisfies
  `log R(b,u)/u → 1/2` at the moving saddle; and, after the independent check
  of 5 October 2026, Proposition 18.2, which extends its lower bound to
  `b ≥ (u/2)(H_u − 1) − Ku` and the limit to `α − ½ log log u → ∞`, covering
  Part I's whole saddle window.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *All logarithmic orders for closed lambda terms: Uniform counting bounds and a controlled threshold inverse* (base); author line "Report 110" | 110 | `Closed_Lambda_Terms_All_Logarithmic_Orders_Source.zip` (415,377 bytes, 24 files; `report110.tex`, 589 lines, 16 pp.) | none | `9c995cefe` | Part I, Sections 1–10 |
| *Unrestricted closed lambda terms: Logarithmic growth and random binding geometry*; author line "Report 109" | 109 | `Closed_Lambda_Terms_Growth_and_Binding_Geometry_Source.zip` (469,757 bytes, 20 files; `report109.tex`, 647 lines, 16 pp.) | none | `9c995cefe` | Part II, Sections 11–19, plus the write's Section 20; the proof of its Section 3 in Part I, Section 3 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `9c995cefe` (batch 103, cluster closed lambda terms) removed them from
`docs/incoming/`. The write is batch 103's "Write batch 103
(a135501-closed-lambda-terms): new report, closed lambda terms". Report 109
was written about fifteen minutes before Report 110 (index times 08:01:33Z
and 08:17:00Z); Report 110 never names it, but says that it "does not repeat
separate large-deviation results for binding geometry".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author or a tool, says it is
AI-assisted, or carries "prepared for private review" wording. Each package's
`checker_audit.md` is the delivering session's audit of its own finite
checker, not an assessment by a referee or by this repository. Every result,
proof, example, remark, question and limitation of the two manuscripts is
printed, with one proof printed once (see "Labels and numbering").

## Files

The directory holds 39 files: 5 at the root, 14 in `code/`, 20 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 110, prefix `110-orders-`**: 20 files besides the article (1 at the
root, 7 in `code/`, 12 in `data/`; corrected 7 October 2026, this line said
18 and 10, against the listing below); its `report110.tex` is the base of
`article.tex`. Root: the delivering session's audit of its finite checker.
`code/`: the exact checker, the separately coded auditor probes, the
integrity, corruption, build, replay and sealing scripts. `data/`: the four
exact fixtures (counts through size 30, reduced-height counts, series
coefficients, check summary) and the recorded validation runs.

```
110-orders-validation-checker_audit.md
code/110-orders-build.py
code/110-orders-check.py
code/110-orders-corruption_test.py
code/110-orders-integrity.py
code/110-orders-replay.py
code/110-orders-seal.py
code/110-orders-validation-auditor_probes.py
data/110-orders-check_results.json
data/110-orders-coefficients.json
data/110-orders-counts.json
data/110-orders-height_counts.json
data/110-orders-validation-auditor_probes_normal.log
data/110-orders-validation-auditor_probes_optimized.log
data/110-orders-validation-build.log
data/110-orders-validation-check_normal.log
data/110-orders-validation-check_optimized.log
data/110-orders-validation-corruption.json
data/110-orders-validation-corruption_optimized.json
data/110-orders-validation-pdf_qa.json
```

Two pairs are **byte-identical**: `data/110-orders-validation-check_normal.log`
= `check_optimized.log`, and `data/110-orders-validation-corruption.json` =
`corruption_optimized.json`. They are records of two runs (normal and
`python -O`) whose output happens to be the same, as delivered, not shipped
copies; both are kept. The two `auditor_probes_*.log` records differ in one
line (`optimized=False`/`True`).

**Report 109, prefix `109-binding-`**: 16 files (1 at the root, 7 in `code/`,
8 in `data/`). Root: the delivering session's audit of its finite checker.
`code/`: the exact checker, the de Bruijn enumeration probes, the integrity,
corruption, build, replay and sealing scripts. `data/`: the computed counts
`A_s(n)` and the sums of abstraction counts for `n ≤ 200` in both models (not
OEIS b-files; only the first 16 terms per model were compared with OEIS), the
check summary, and the validation records.

```
109-binding-validation-checker_audit.md
code/109-binding-build.py
code/109-binding-check.py
code/109-binding-corruption_test.py
code/109-binding-integrity.py
code/109-binding-replay.py
code/109-binding-seal.py
code/109-binding-validation-auditor_probes.py
data/109-binding-A135501_computed.txt
data/109-binding-A135501_unary_moment.txt
data/109-binding-A220894_computed.txt
data/109-binding-A220894_unary_moment.txt
data/109-binding-check_results.json
data/109-binding-validation-auditor_results.json
data/109-binding-validation-build_and_visual_results.json
data/109-binding-validation-corruption_results.json
```

`code/109-binding-build.py` and `code/110-orders-build.py` differ only in the
report number; so do the two `seal.py` scripts.

**Not shipped** (all retrievable from `60f54ea06`): both PDFs; both
`manifest.json` files (checksum manifests of 19 and 23 entries, verified at
placement with no mismatch; repository policy drops checksum manifests); the
delivered `README.md` of Report 110 (staged at placement and replaced by this
guide) and of Report 109 (not staged); `report109.tex` (printed as Part II).

## Labels and numbering

Label prefix **`lam:`**: Part I uses `lam:ao:` (Report 110's 68 labels, and the
8 labels of Report 109's Section 3 proof printed there), Part II `lam:bg:` (50
of Report 109's 62 labels). Report 109's other 4 labels name its copies of
Report 110's identities `(2.1)–(2.3)` and of the display after them
(`eq:biv-gf`, `eq:B0`, `eq:Bk`, `eq:coefficient`); they are printed once, in
Part I. The front matter uses `lam:` (`lam:sec:guide`, `lam:sec:status`,
`lam:sec:notation`, `lam:sec:provenance`, `lam:sec:neighbours`), and the write
added `lam:ao:part`, `lam:bg:part`, `lam:ao:sub:further`,
`lam:bg:sec:further`, `lam:bg:rem:ratio` and its three equations
`lam:bg:eq:ratio-upper`, `-lower`, `-saddle`. 139 labels in all, all
distinct. After the independent check (5 October 2026) the write added
`lam:bg:prop:tilt` and its equation `lam:bg:eq:ratio-tilt` (Proposition 18.2,
equation (18.5)): 141 labels, all distinct. The six label names that occur in both manuscripts (`eq:B0`,
`eq:G`, `eq:size`, `eq:uniform`, `sec:inverse`, `thm:inverse`) are distinct
under the prefixes; `eq:G` and `eq:uniform` name different mathematics in the
two (front matter, "Notation across the two Parts").

| Part | Manuscript | Section here | Statement / equation `k.j` |
|---|---|---|---|
| I | Report 110 | `k` (unchanged, 1–10); Section 9.2 added | `k.j` (unchanged) |
| I, Section 3 | Report 109, Section 3 (proof only) | 3.1–3.3 | Lemmas 3.2, 3.3 and Remark 3.4 unchanged; equations (3.6)–(3.11) become (3.2)–(3.7) |
| II | Report 109 | `k + 10` (11–19); Section 20 added | `(k+10).j` |

Report 110's Lemma 3.1 and the upper half of Report 109's Theorem 3.1 are one
theorem with one proof. The proof is printed once, in Report 109's fuller
wording, as Part I's Sections 3.1–3.3; Report 110's condensed proof, which
takes the same steps in the same order, is not reprinted. Part II's Section 13
keeps the statement of Report 109's Theorem 3.1 (Theorem 13.1) and a pointer.
Report 109's (3.2)–(3.5) are Part I's (2.1)–(2.3) and the display after them.
The write's Remark 18.1 is the last statement of Section 18, so no delivered
number moved; Proposition 18.2, added after the independent check, follows it,
and the `.aux` of the rebuild, compared with that of a build of the committed
text, keeps all 139 earlier labels at their numbers. A check of the build's `.aux` against separate builds of the
two delivered `.tex` files confirmed every label's number under these
offsets. The delivered READMEs, audits and code use the manuscripts' own
numbers.

## Notation

One symbol was renamed: in the Report 109 text moved into Part I, the
variable `t` of the shape series `D(t)` is written `z`, as in Report 110,
because `t` is Part I's Lambert value. Report 109's citation keys `bci`,
`david`, `restricted` are Report 110's `bggj2013`, `david2013`, `bggg2018`.
Otherwise each Part keeps its manuscript's letters; the front matter lists
every letter whose meaning changes, and each Part opens with a reading
table. The most dangerous is **`u_*`**: Part I's `u_* = N/t` with
`t = W(4eN e^{−r/2})` maximizes `F_N(u) + u/2`, Part II's `u_* = N/w` with
`w = W(4eN)` maximizes `F_N(u)`; Part II's is smaller by about
`(r/2) N/(log N)²`, and the two maxima differ by `N/(2 log N)(1 + o(1))`,
exactly the gap between the two counting theorems. Others: **`t`** (Part I's
Lambert value near `log N`; Part II's scaled abstraction count near 1),
**`G_N`** (Part I's coarse envelope `F_N + cu − log 2`; Part II's placement
envelope `F_N + u log(2eN/u)`), `L`, `ℓ`, `k` (Part I: `log N`, `log log N`;
Part II's inverse: `log y`, `log log y`, which Part I calls `Y`, `v`), `K_r`
(a constant in Part I, a rate function `K_r(d)` in Part II), `H` (harmonic
number, envelope, random height), `T`, `z`, `J`, `I`, `R`, `Q`, `D`, `d`,
`h`, `q`, `a`, `α`, `M`.

## What the report claims

**Part I (Report 110).**
- Theorem 1.1: `M_r(N) − O(log N) ≤ log A_s(n) ≤ M_r(N) + O(R_r(N))`, with
  constants depending at most on `r`; since `R_r(N)/(N/(log N)^k) → 0` for every
  `k`, every fixed inverse-logarithmic order of `log A_s(n)` follows: (1.7)
  with the polynomials `P_1, …, P_6` printed and a recurrence for all `P_j`; the
  `n/log n` term is `(n/r)(log log n − log 4 + r/2)/log n`.
- Theorem 1.2: the threshold inverse `ν_s(y) = min{n : A_s(n) ≥ y}`:
  `N_0 − O(R_r(N_0)/log N_0) ≤ ν_s(y) + 1 ≤ N_0 + O(1)` with `M_r(N_0) = log y`,
  the parametric form `N_0 = rY t_y/Π_r(t_y)`, the explicit form with error
  `O(Y(1 + k)²/v⁴)` (`Y = log y`, `v = log Y`, `k = log v`), and a recurrence
  for every inverse order.
- Lemma 2.1 (reduced shape counts `C_q binom(u+q−1, 2q)`), Lemma 3.1 (the coarse
  majorant `A(b,u) ≤ 2uK^u(4u)^b`, `K = e(2 + √3)`), Lemma 4.1 (a height-sensitive
  bound evaluated beyond the unrestricted radius), Proposition 4.2
  (`log A(b,u) ≤ b log(4u) + u/2 + E(b,u) + O(log(u+1))`,
  `E = 3·2^{1/3} u (1+α)^{1/3} e^{−α/3}`), Section 5 (the exact single-spine
  series `L_u = B_{u,0} Q_u`, `Q_u(1/(4u)) = √(u^u/u!)`, a negative-binomial
  law and Cantelli), Section 6 (two-stage localization), Lemma 7.1 (analytic
  remainder of the reversion).

**Part II (Report 109).**
- Theorem 11.1 (second route; superseded): `log A_s(n) = (N/r)(w − 2 + 1/w) + O(N/log N)`,
  the four-scale form, `(log n/n) A_s(n)^{r/n} → 4/e`.
- Theorem 11.2 (superseded): `ν_s(y) = rL/(ℓ − 2 log ℓ + log r + c_0 + 4 log ℓ/ℓ) + O(L/ℓ³)`,
  `L = log y`.
- Theorem 11.3: the joint large-deviation principle for `(T_n, X_n)`, rate
  `J_r(t,x) = (t − 1 − log x)/r` on `0 < x ≤ t`, marginal rates
  `I_r(x) = (x − 1 − log x)/r`, `L^p` convergence to 1, `E U_n ~ E H_n ~ n/log n`.
  Corollary 11.4: the deficit `(U_n − H_n) log N/N` has rate `d/r`; a longest
  unary path carries all but `o(n/log n)` abstractions in probability.
- Lemma 12.1: the skeleton sandwich `C_b u^{b+1} ≤ A(b,u) ≤ C_b binom(u+2b, u) u^{b+1}`
  and the exact weight formula; the size recurrence; the table of `A_s(n)`,
  `n ≤ 10`; Lemmas 3.2–3.3 and Remark 3.4 (printed in Part I).

**Added by the write** (marked `[write]`, dated 5 October 2026): **Remark
18.1** with a complete proof — for all `u ≥ 1`, `b ≥ 0`,
`0 ≤ log R(b,u) ≤ u/2 + E(b,u) + log(2u(u+1)(2b+1)(b+1))`; for
`b ≥ (u/2)(H_u − 1) + au`, `log R(b,u) ≥ u/2 − (1/4) log u − 1/2 − log(1 + a^{−2})`;
hence `log R(b,u)/u → 1/2` along such pairs with `log(b+1) = o(u)`, and at the
moving saddle (admissible `u` with `(u − u_*) log N/u_* → 0`)
`−O(log u) ≤ log R(b,u) − u/2 ≤ O(u^{1−1/(3r)}(log u)^{1/3})`. It uses only
Part I's Proposition 4.2, its single-spine inequality (5.6), and Part II's
Catalan bound and Lemma 12.1. It answers Part II's ratio frontier at the scale
it names; it does not reprove Theorem 1.1, whose upper bound needs Part I's
localization away from the saddle. Dated notes: Part I determines the
coefficient of `n/log n` that Part II leaves undetermined (`1/2 − (log 4)/r`:
`1/2 − log 2` for A135501, `1/2 − log 4` for A220894); Part II's Lambert
expression is lower by `N/(2 log N)(1 + o(1))`, so its residual factor
`exp{O(n/log n)}` is attained, with constant `1/2` against the Lambert form
and `1/2 − (log 4)/r` against the four-scale form (the second added after the
independent check); Part II's inverse omits the constant
`[1 + r/2 − 2 log(4r)]/ℓ` of the denominator, nonzero, so its error
`O(L/ℓ³)` is of exact order and its approximation lies below `ν_s(y)`. Also:
the front matter, two further-questions sections, the merged bibliography.

**Added after the independent check** (marked `[write]`, dated 5 October
2026): **Proposition 18.2** with a complete proof. With `κ_K` the least
positive integer with `H_κ ≥ 2K + 3` (`κ_K ≤ e^{2K+3}`; `κ_0 = 11`,
`κ_1 = 83`), `log R(b,u) ≥ u/2 − 2κ_K(1 + log u)` for all `u ≥ 1`, `b ≥ 0`
with `b ≥ (u/2)(H_u − 1) − Ku`. Hence `log R(b,u)/u → 1/2` whenever
`α − ½ log log u → ∞` and `log(b+1) = o(u)` (including `α ≥ δ log u`), and,
for `N ≥ N_0(r)`, the two-sided bound of Remark 18.1(4) holds for every
admissible `u` in Part I's window `|u/u_* − 1| < 1/log N`, `r = 1, 2`. The
proof tilts the single-spine law by `θ = 1 − κ/u` before Cantelli's
inequality; the idea is the independent check's, the write wrote out the
proof, sharpened its mean estimate and made the constant explicit, and
checked every step numerically (the note after the proposition lists the
checks). After the second check (below), consequence (2) states the range
`N ≥ N_0(r)` that its proof gives; it first claimed the bound for every `N`,
which fails at `r = 2`, `N = 3`, `u = 1` and at `r = 1`, `N = 2`, `u = 1`
(there `b = 0`, `R = 1` and `log R − u/2 = −1/2`). Its last clause now says
that the hypothesis of Remark 18.1(4) excludes part of the window for both
`r`; for `r = 1` that part is covered by Remark 18.1(2), for `r = 2` it is
not, since the margin `α − ½(H_u − 1)` tends to
`log 2 − ½ − γ/2 ≈ −0.0955` at the upper edge. A dated note after the proof
keeps the first wording. *[Dated note, 7 October 2026: the note after the
proposition said its checks covered "the range `4κ_K ≤ u ≤ 600`, where (18.5)
does not follow from `R ≥ 1`". That is false: the right side of (18.5) is
negative for `u < 4κ_K(1 + log u)` (at `u = 4κ_K` it is `−2κ_K log(4κ_K)`;
`K = 0`, `u = 44`, `b = 1936` is an admissible example), and the bound says
more than `R ≥ 1` only for `u ≥ 295`, `978`, `2989` (`K = 0, ½, 1`). Of those
cells only `K = 0`, `295 ≤ u ≤ 600` test more than `R ≥ 1`. A dated note in
place says so; the proposition is unaffected.]*

- *[Independent check, 5 October 2026.]* An adversarial check of the write
  made by the intake after it (`b432720bf`) found all eleven items it examined
  valid, with no counterexample and no gap in any proof chain: Remark 18.1
  (1)–(4) with their proofs, the note after it, the coefficient
  `1/2 − (log 4)/r` with `M_r − (N/r)(w − 2 + 1/w) = N/(2 log N)(1 + o(1))`,
  the attained residual factor, the inverse constant `1 + r/2 − 2 log(4r)`
  with the order and side of Part II's error, the gap between the two `u_*`,
  the front-matter row on the ratio, and Part II's further-questions item 5.
  Three sentences are corrected where they stand, each with a dated note
  keeping the first wording: the note after Part II's Remark 14.1 now says
  that the residual constant is `1/2` against the Lambert form and
  `1/2 − (log 4)/r` (−0.193 for `r = 2`, −0.886 for `r = 1`) against the
  four-scale form that the remark displays (exact data: −0.901 at `n = 600`,
  `s = 0`); the evidence sentence after Remark 18.1 no longer calls the full
  ratios decreasing (0.737, 0.738, 0.732 are not monotone; overall the ratio
  rises to 0.754 at `N = 72` and falls to 0.664 at `N = 740`); and the
  front-matter row no longer claims two-sided bounds for all `(b,u)`, since
  the lower bound `u/2 − O(log u)` needs `b ≥ (u/2)(H_u − 1) + au`. The check
  also proposed the exponential tilt of Proposition 18.2, and
  further-questions item 5 is re-scoped with a dated note. The tests, none of
  which used the delivered or the write's programs: its own recurrence for
  `A_s(n)`, equal to the OEIS b-files of A135501 for `n ≤ 300` and A220894 for
  `n ≤ 200`, run to `n = 600`; the sum of `A(b,u)` over `u` equal to `A_s(n)`
  for `n ≤ 24`; `A(b,u)` exactly for `u ≤ 8`, `b ≤ 400` and `u ≤ 24`,
  `b ≤ 44`, and in floating point for `u ≤ 120`, `b ≤ 400`, against (4.7),
  (18.2) and (18.3) (29,160 cells); a re-derivation of Remark 18.1 and of
  Proposition 4.2; the Cantelli margin at the saddle for `N ≤ 740` (0.197 to
  0.43 for `r = 2`; negative at `u = 136, 138` inside the window at
  `N = 740`); and 160-digit checks of the coefficient and of the inverse
  constant out to `L = 10^16` and `v = 10^15`. The record is an unlabelled
  dated paragraph at the end of Section 20. This was a careful reading with
  numerical tests, not a formal verification.
- *[Second independent check, 5 October 2026.]* A second adversarial check,
  of Proposition 18.2 alone and with its own programs, found (18.5), the
  constants `κ_K` and consequence (1) valid, and consequence (2) valid for
  large `N`, with the two wording fixes described above. It tested (18.5) at
  `b ≥ ⌈μ − Ku⌉` for `K = 0, ½, 1, 2`: in exact integers for `u ≤ 12`,
  `b ≤ 60` (the totals recover A135501 and A220894), on the full ratio `R` in
  scaled floating point to `u = 140`, and on the single-spine ratio, which is
  at most `R`, to `u = 3000`, with no failure and large slack (202, 562, 1498
  and 11,086 for `K = 0, ½, 1, 2` at `u = 3000`). Over the window of
  consequence (2) the margin `α − ½(H_u − 1)` is at least 0.71 for `r = 1`
  (at `N = 10`) and grows like `½ log u_*`; for `r = 2` its least value,
  always on the upper side of the window, is −0.234 at `N = 20`, −0.043 at
  `N = 100`, −0.058 at `N = 10^6` and −0.063 at `N = 10^12`, with limit
  `log 2 − ½ − γ/2 ≈ −0.0955` at the upper edge. So for `r = 2` the
  hypothesis of Remark 18.1(2) fails on part of the window for all large `N`,
  and the proposition is needed there. The record is a dated sentence
  appended to the Section 20 paragraph.

## What the report does not claim

Every limitation is printed in place. In short: **no multiplicative
equivalent, amplitude, power-of-`n` factor, ratio limit between subclasses or
multiplicative transseries** in either Part; Theorem 1.1 allows a
stretched-exponential discrepancy `exp{O(R_r(N))}` above `e^{M_r(N)}`, and
**the exponent `1 − 1/(3r)` of `R_r` is an upper-bound exponent from a
shape-entropy majorant, not a proved scale** (Report 110 says so; the write
repeats it after Theorem 1.1); the polynomial recurrences say nothing about
truncation orders growing with `n`; no constants or onsets are explicit; no
central limit theorem or fluctuation law for `U_n`, `H_n`; the
path-concentration statement concerns a root-to-leaf path, not a consecutive
root chain; natural-size, linear, affine, typed, beta-normal, bounded-index
and bounded-height classes are not substitutes; Part II's comparison with
David et al. does not subsume their normalization or head-abstraction
theorems. Both packages: finite exact checks prove no asymptotic statement;
only 16 OEIS prefix terms per model (Report 109) and 22 prefix entries
(Report 110) were compared with OEIS; the literature comparisons are bounded,
and neither manuscript claims global priority. **The literature statements
(Bodini–Gardy–Gittenberger–Jacquot 2013, Theorem 22 and Remark 23; David et
al. 2013, Theorem 5.4; the 2015 preprint of Bodini–Gardy–Gittenberger–
Gołębiewski; Gittenberger–Larcher 2019; Grygiel–Larcher 2021;
Bendkowski–Bodini–Dovgal 2019) were not checked against the papers** at the
placement or at the write; the article says so in both Parts and in the
bibliography.

## Further questions, and the standing rule

Each Part closes with "Further questions and research" (Sections 9.2 and 20).
Under Vladimir's standing rule of 4 October 2026 the write moved there every
claim stated without proof, with source, sketch and what is missing:

- Part I (Section 9.2): (1) an equivalent, amplitude, multiplicative
  transseries; (2) the first scale of `log A_s(n) − M_r(N)` beyond all fixed
  orders (known only between `−O(log N)` and `O(R_r(N))`; residuals from the
  shipped tables at `n ≤ 200` given as evidence); (3) uniform asymptotics of
  the enriched spine class, **merged** with Report 109's question 4 on the
  weighted-placement sum (partly answered for the total count); (4) an
  organized multiplicative expansion; (5) explicit constants and onsets; (6)
  the unchecked literature statements.
- Part II (Section 20): (1) fluctuation scales and limit laws of `U_n`, `H_n`
  (with the shipped first moments, `E U_n log N/N = 1.25` for `s = 1` at
  `n = 200`, as evidence); (2) the typical size of `U_n − H_n`, **merged** from
  Report 109's and Report 110's question 2; (3) the consecutive-root-chain
  fraction of a longest unary path; (4) pointer to Part I's item 3; (5) the
  ratio frontier beyond Remark 18.1 (second order at the saddle; bounded
  `α = b/u`; the part of the saddle window not covered for `r = 2`),
  re-scoped after the independent check (dated note): Proposition 18.2 closes
  the window and gives the limit 1/2 whenever `α − ½ log log u → ∞`, so the
  second order and the limit for smaller `α`, in particular bounded `α`,
  remain open. *[Dated note, 7 October 2026: for `α → ∞` the limit 1/2 is
  now proved outside this report, under `log(b+1) = o(u)` alone, by a note
  committed in `a8455335c`
  (`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/closed_lambda_tilt_entropy_aristotle.md`):
  it bounds Proposition 18.2's tilt loss by `½ log C(u+κ, κ)` instead of
  `(κ/2) H_u`. Open: the second order and bounded `α`. A dated note at
  item 5 says so.]*

Superseded statements stay as printed with dated notes: Report 109's Theorem
1.1 ("the coefficient of the next scale `n/log n` is not determined"), its
Section 4 constant `−log 4/q` and remark on the residual factor
`exp{O(n/log n)}`, its Theorem 1.2 and Section 5 ("a constant divided by `ℓ`
… would change the answer at the unresolved error scale"), its Section 8.2
("Nothing here determines the actual weighted-placement enhancement"), and its
delivered README's "coefficient of n/log n … remain unresolved here" (README
not shipped; the note is in Part II, Section 19). **Nothing in either
manuscript was found to be wrong.**

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`.
No other report counts lambda terms or mentions A135501 or A220894 (searched
5 October 2026); the Bodini and Gittenberger papers cited elsewhere (for
example by `a082161-airy-amplitudes`) concern other objects.
`a088714-bell-scale-growth` and `a277364-bell-asymptotics` also solve
Lambert-`W` saddle equations; they share no theorem with this report. The
threshold inverse `ν_s` is the integer staircase of Definition
`p0:def:three-inverses` of the transseries volume
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`);
neither Part uses that volume's staircase theorem. This write edits no other
report.

## Relation to the formal project

`Computability/CombinatoryLogic/Lean/CombinatoryLogic/Lambda.lean` (line 15)
defines `inductive Term : Nat → Type` (intrinsically scoped de Bruijn terms:
`var (index : Fin n)`, `app`, `lam (body : Term (n + 1))`); **`Term 0` is
exactly the set of closed alpha-classes counted here**, and its constructor
recursion is the binder-context recursion `T_m = m + z T_{m+1} + x T_m²` of
Part I, Section 2. The Rocq development has the equivalent `term V` with
`lam : term (option V) -> term V`
(`Computability/CombinatoryLogic/Coq/Lambda.v`, line 16). Neither defines a
size or counts terms, and **no statement of this report is formalized**;
placement in the collection confers no formal status. *[Dated note,
7 October 2026: "neither defines a size" is false of the Rocq development.
`Lambda.v` lines 232–237 define `UntypedLambda.size`, with every variable,
application and abstraction of size one: A135501's convention (`s = 1`).
The Lean `Term` has no size function. Neither development counts terms, so
the conclusion stands: nothing here is formalized. The article's front
matter ("Relation to neighbouring reports and to the formal project") has
the same dated note.]*

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 36 staged delivered files other
  than `article.tex` and `README.md` checked against fresh extractions of the
  arrival archives at the write: 0 differences; the two replaced files were
  also identical as placed); only names changed (tables at the end). The delivered code and
  markdown use delivery paths (`check.py`, `data/counts.json`,
  `data/A135501_computed.txt`, `validation/…`, `manifest.json`,
  `report109.tex`, `report110.pdf`, `report1xx_source_checks.zip`,
  `FINAL_SHA256.txt`), which are shipped under other names or not at all. The
  scripts resolve paths relative to their own location, and `integrity.py`
  requires the delivered inventory and `manifest.json`, so **none runs in this
  directory**.
- **In-place writes.** `build.py` writes `report1xx.pdf` beside itself and
  recreates `build/`; `check.py --write-data` (Report 110) and
  `check.py --generate` (Report 109) rewrite the data fixtures;
  `integrity.py --generate` rewrites `manifest.json`; `seal.py` writes the
  ZIP and `FINAL_SHA256.txt`; `replay.py` writes into its `--out` directory.
  The corruption campaigns and probes work on temporary copies. Run all of
  them only on a copy.
- **Recorded runs.** The `data/*validation*` records are the delivering
  session's captured outputs; no shipped script writes them. On Windows,
  Report 110's probe output equals the delivered `auditor_probes_*.log` up to
  CRLF line ends (placement check).
- **PDF reproducibility.** Both `build.py` scripts require a byte-identical
  rebuild of the delivered PDF with TeX Live 2025 pdfTeX 1.40.26; this was not
  rerun (the PDFs are not shipped, and MiKTeX produces different bytes).
- `replay.py` defaults to `report1xx_source_checks.zip`, which is not in the
  delivery; the arrival archive has the same `report1xx/` layout and might be
  passed with `--archive` (not tried; the replay also rebuilds the PDF, see
  above). Extracting it and running the suites, as below, is the tested route. Both delivered READMEs show output paths under `/tmp/`;
  use a scratch directory outside the repository.
- Report 109's `check.py --fixtures-only` is a prefix check through `n = 20`
  only, as its README says.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. The simplest
route recreates the delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Closed_Lambda_Terms_All_Logarithmic_Orders_Source.zip > s110.zip
git show 60f54ea06:docs/incoming/Closed_Lambda_Terms_Growth_and_Binding_Geometry_Source.zip > s109.zip
mkdir r110 r109 && unzip -q s110.zip -d r110 && unzip -q s109.zip -d r109
cd r110/report110
py integrity.py && py -O integrity.py
py check.py && py -O check.py
py validation/auditor_probes.py && py -O validation/auditor_probes.py
py corruption_test.py                      # about 2 minutes, on temporary copies
cd ../../r109/report109
py integrity.py && py -O integrity.py
py check.py && py -O check.py
py validation/auditor_probes.py && py -O validation/auditor_probes.py
py corruption_test.py                      # about 5 minutes, on temporary copies
```

Python 3.9 or later and its standard library suffice (`python3` on POSIX).

Results: at placement (5 October 2026, on copies, recorded in the batch-103
dossier) every suite passed — Report 110: `check.py` (normal and `-O`; 17,643
exact checks, four fixtures, forward orders 1–8 and inverse orders 1–6
agreeing), `auditor_probes.py` (output equal to the delivered logs up to
CRLF), `integrity.py` (23 files), `corruption_test.py` (34 cases, 68
rejections, about 114 s); Report 109: `check.py` (5,457 checks, snapshots
matched), `auditor_probes.py` (105,723 guards: 105,711 mathematical and 12
inventory), `integrity.py` (19 files), `corruption_test.py` (26 cases, 52
rejections, about 273 s); copies unchanged after every run. `build.py` was not
run. At the write (5 October 2026, Python 3.14.4, Windows, fresh extractions
of both archives): `check.py` normal and `-O` and `integrity.py` passed for
both packages (about 2 s and 9 s per checker run; 17,643 and 5,457 checks; 23
and 19 files).

## Rights

Repository contents are MIT-0. The sequence terms printed in the article and
contained in the data and code (`A_s(n)` of A135501 and A220894, reduced-height
counts, abstraction sums) are recomputed by the shipped programs; Report 109's
checker embeds the first 16 OEIS terms of each sequence and Report 110's
checker 22 published-prefix entries, as fixtures. OEIS data are available under
CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are
credited for the sequences; Bodini–Gardy–Gittenberger–Jacquot, David et al.,
Bodini–Gardy–Gittenberger–Gołębiewski, Gittenberger–Larcher, Grygiel–Larcher
and Bendkowski–Bodini–Dovgal for the cited prior work. No third-party code or
PDF is shipped. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 42 pages, no errors, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull or underfull boxes; every
one of the 139 labels resolves, and the delivered labels keep the numbers
stated under "Labels and numbering" (`.aux` compared with builds of the two
delivered `.tex` files, each 16 pages and warning-free). The log carries one
"Infinite glue shrinkage found in box being split" message, from the
notation longtable breaking across a page, as in other reports with
longtables.

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 45 pages, no errors, no undefined or multiply defined
references, no duplicate destinations, no overfull or underfull boxes, and the
same single infinite-glue message; the 141 labels resolve, and the 139 earlier
ones keep their numbers (`.aux` compared with a build of the committed text).

Rebuilt again on 5 October 2026 after the second check, the same way: 46
pages (the appended record runs onto a new page before the references), no
errors, no undefined or multiply defined references, no duplicate
destinations, no overfull or underfull boxes, and the same single
infinite-glue message; all 141 labels keep their numbers and pages (`.aux`
compared with a build of the committed text).

Rebuilt on 7 October 2026 (cleanup pass: the dated notes on the Rocq size
function, the test range after Proposition 18.2 and further-questions item
5), with three pdfLaTeX passes: 46 pages, equally clean, the same single
infinite-glue message; all 141 labels keep their numbers, and only
`lam:bg:sec:further` (Section 20) moves, from page 42 to 43 (`.aux`
compared with a build of the committed text). Pages 7–8, 40 and 43
rendered and inspected.

## Delivered path → shipped path

Report 110 (`110-orders-`; `README.md` replaced by this guide):

| Delivered | Shipped |
|---|---|
| `report110.tex` | `article.tex` (Part I) |
| `<name>.py` (build, check, corruption_test, integrity, replay, seal) | `code/110-orders-<name>.py` |
| `validation/auditor_probes.py` | `code/110-orders-validation-auditor_probes.py` |
| `data/<name>.json` (check_results, coefficients, counts, height_counts) | `data/110-orders-<name>.json` |
| `validation/<name>` (auditor_probes_normal.log, auditor_probes_optimized.log, build.log, check_normal.log, check_optimized.log, corruption.json, corruption_optimized.json, pdf_qa.json) | `data/110-orders-validation-<name>` |
| `validation/checker_audit.md` | `110-orders-validation-checker_audit.md` |
| `README.md`, `report110.pdf`, `manifest.json` | not shipped |

Report 109 (`109-binding-`):

| Delivered | Shipped |
|---|---|
| `report109.tex` | not shipped; printed as Part II of `article.tex` (the proof of its Section 3 in Part I) |
| `<name>.py` (build, check, corruption_test, integrity, replay, seal) | `code/109-binding-<name>.py` |
| `validation/auditor_probes.py` | `code/109-binding-validation-auditor_probes.py` |
| `data/<name>` (A135501_computed.txt, A135501_unary_moment.txt, A220894_computed.txt, A220894_unary_moment.txt, check_results.json) | `data/109-binding-<name>` |
| `validation/<name>.json` (auditor_results, build_and_visual_results, corruption_results) | `data/109-binding-validation-<name>.json` |
| `validation/checker_audit.md` | `109-binding-validation-checker_audit.md` |
| `README.md`, `report109.pdf`, `manifest.json` | not shipped |

## Provenance

Two manuscripts (bundle Reports 110 and 109) → one report; base 110. Arrival
`60f54ea06`, placement `9c995cefe`, write batch 103 (5 October 2026). Neither
manuscript pins a ProveIt commit. Merge choices (base and order, the one proof
printed once in Report 109's wording, the shape variable renamed in the moved
text, the merged questions, the merged bibliography, the write's Remark 18.1 and,
after the independent check, Proposition 18.2)
are listed in the article's front matter, "Provenance and merge decisions".
