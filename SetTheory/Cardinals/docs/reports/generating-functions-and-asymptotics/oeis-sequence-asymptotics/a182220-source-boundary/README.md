# The Source Boundary of Extensional Acyclic Digraphs

**Part I: an OEIS conjecture (A182220), finite-defect enumeration of the source
triangle A182162, and dyadic non-holonomicity. Part II: natural boundaries of
the fixed-defect generating functions, at the source edge and at the source
extremum**

A two-part report built from three manuscripts. Part I (3 October 2026) is a
single manuscript. Its title block reads "Prepared for Vladimir Reshetnikov / In
the mathematical research context of the ProveIt repository", and its PDF
author field "Research prepared for Vladimir Reshetnikov": it names no human
author and no tool. Part II (added 5 October 2026) merges two independent
manuscripts that answer Part I's first research question. Their title pages
and PDF author fields name ChatGPT ("Research manuscript prepared with
ChatGPT"; "Research prepared with ChatGPT").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 07 | `OEIS_A182220_Source_Boundary_Research.zip` (wrapper `oeis_source_boundary/`, 864,793 bytes), arrival `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, the bibliography entry for ProveIt and `SOURCES.md`) | `ddf8df5d5` (batch 85C) | Part I, Sections 1–13 and Appendices A–B |
| 02 | batch 98, manuscript 01: *Natural Boundaries at the Source Edge of Extensional Acyclic Digraphs: Dense singularities, universal radial limits, and logarithmic growth for OEIS source-count diagonals* (5 October 2026; 22-page PDF) | `OEIS_EAD_Natural_Boundaries.zip` (wrapper `ead-natural-boundary/`, 1,061,332 bytes), arrival `2172df76a`; main file `ead_natural_boundaries.tex` | `d18416ec7` (`d18416ec7e187a0948248cb3077e37d7b089a8f9`, in its `PROVENANCE.md`, Section 1.1 and bibliography) | `b50febf79` (batch 98C) | Part II, merge member: files prefixed `02-source-edge-`, labels `sbd:edge:` |
| 03 | batch 98, manuscript 05: *Natural Boundaries at the Source Extremum: Fixed deficits, dyadic radial limits, and local L^p growth* (5 October 2026 UTC; 23-page PDF) | `OEIS_Source_Boundaries.zip` (wrapper `oeis_natural_boundaries/`, 1,073,601 bytes), arrival `2172df76a`; main file `article.tex` | `d18416ec7` (same commit, in its `SOURCE_NOTES.txt`, Appendix B and bibliography) | `b50febf79` (batch 98C) | Part II, merge base: files prefixed `03-source-extremum-`, labels `sbd:xtm:` |

At the pin `d18416ec7` this report consisted of Part I alone, unchanged from
its batch-85 write (`eab47e330`) to the batch-98 placement; both Part II
manuscripts read exactly that text. They are independent of each other (their
shared word 8-grams are 2.7 % of 02's text and 2.3 % of 03's), not editions.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs; the exact integer computations check finite
statements on recorded ranges, and the floating-point computations (Decimal in
Part I, mpmath in Part II) are numerical diagnostics, not interval bounds.

## What it proves

An *extensional acyclic digraph* (EAD) is a finite acyclic digraph whose
vertices have pairwise distinct out-neighbourhoods. `u_m` = A001192(m) counts
EAD isomorphism classes on `m` vertices (`u_0 = 1`), `u(n,k)` those with `k`
sources (the labelled count `n! u(n,k)` is A182162), `q = ⌈log₂ n⌉`, and
`b_n^(d) = u(n, n−q−d)` is the boundary diagonal at defect `d`, with
generating function `B_d(z) = Σ b_n^(d) z^n`.

### Part I

- **Theorem 3.1 (complete source support).** An EAD on `n` vertices with
  exactly `k ≥ 1` sources exists iff `k ≤ n ≤ 2^(n−k)`; hence
  **`A182220(n) = n − ⌈log₂ n⌉`**, and A182162 has no holes in any row. The
  upper bound is Tomescu's (2011, see below); the construction for every
  admissible `k` is the manuscript's.
- Proposition 3.2: the lacunary generating function of `a(n)`, with the unit
  circle as natural boundary. Lemma 2.1, Corollary 2.2, Lemma 2.3: finite
  (Mostowski) collapse onto transitive sets, rigidity (`n!` labelled copies
  per class), `1 ≤ u_m ≤ 2^C(m,2)` (classical; proofs included).
- **Theorem 4.2 (classification of extremizers):** extremal classes ↔ pairs
  (transitive core of size `q`, `(n−q)`-subset of `P(C) \ C`), so
  `b_n^(0) = u_q C(2^q − q, n − q)`; Corollary 4.3: `b_{2^m−r}^(0) =
  u_m C(2^m − m, r)`.
- Proposition 5.1, Corollary 5.2: the marked-source identity, its binomial
  inversion (the known source sieve) and the total recurrence, re-proved in
  this normalization and credited. **Theorem 5.3:** the exact `(d+1)`-term
  finite-defect formula for `b_n^(d)` (a short consequence of the sieve, as
  the article says).
- **Theorem 6.1:** `0 ≤ u_m C(M,k) − u(m+k,k) ≤ m 2^(−k) u_m C(M,k)`,
  `M = 2^m − m`, with an exact rejection sampler and a core-law
  total-variation bound `m 2^(−k)`.
- **Theorem 7.1 (entropy profile):** `log b_n^(d) = n Φ_d(ρ_n) +
  O_d((log n)²)` uniformly on each dyadic block, `ρ_n = n/2^q`; **Theorem
  7.2:** the subsequential limits of `(b_n^(d))^(1/n)` fill exactly
  `[e^(λ_d), e^(λ_(d+1))]`, `λ_d = 2^d H(2^(−d))`; for `d = 0` this is
  `[1, 4]`.
- **Lemma 8.1 (exponential-jump obstruction)** and **Theorem 8.2:** no
  `b^(d)` and no `n! b^(d)` is P-recursive; `B_d` is not D-finite and has
  radius `R_d = e^(−λ_(d+1))` (`1/4` for `d = 0`).
- Theorem 9.1: an all-orders expansion of `log b_n^(d)` away from `p = 1`,
  with `u_m` kept exact (Stirling and Bernoulli terms), and the exact
  fixed-deletion series near complete layers.
- **Theorem 10.1, Corollary 10.2:** the arc deficit of a uniform extremizer at
  `n = 2^m − r` is within total variation `(rm + C(r,2))/2^m` of
  `Bin(rm, 1/2)`, hence a central limit law; exact conditional moments.
- Section 11: the exact checks (Tables 1–2); Section 12: a formalization
  route (a plan only) and ten research questions; Appendix A: **draft**
  OEIS-facing statements (see below); Appendix B: a proof-status ledger.

### Part II (Sections 14–25)

With `c = 2^(d+1)`, `a = c − 1`, `R = R_d = a^a/c^c`, `L = log(1/t)`:

- **Theorem 14.2 (both manuscripts; answers Part I's Question 1):** for every
  fixed `d ≥ 0` the circle `|z| = R_d` is a **natural boundary** of `B_d`, and
  at every root of unity `ζ` of power-of-two order
  `B_d(R e^(−t) ζ)/B_d(R e^(−t)) = ζ(1 − aR)/(1 − aRζ) + O(t)` (the rate is
  manuscript 03's; for `d = 0` the limits at `−1` and `i` are `−3/5` and
  `(−3+12i)/17`).
- **Theorem 14.3 (both):** `log B_d(R e^(−t)) = L²/(2 log 2) + L log L/log 2 +
  O_d(L)`, also in modulus at every dyadic root; `B_d` grows faster than every
  power of `1/t` along those radii, so no meromorphic continuation either.
- **Theorem 14.4 (03; its log-level law also 02):** for every `p > 0` and
  every open arc `I`, `∫_I |B_d(R e^(−t+iθ))|^p dθ` is within constant
  factors of `B_d(R e^(−t))^p`: a strong natural boundary in Breuer–Simon's
  sense, quantitatively.
- Section 15: what Part II takes from Part I (a correspondence table), the
  **chain lower bound** `2^C(m−1,2) ≤ u_m` (new to the report) and a
  **bijective proof of Tomescu's deletion recurrence** (Proposition 15.4),
  which Part I only quotes.
- Sections 16–17 (03, with 02's versions as second routes): the uniform
  geometric block profile (Lemma 16.1), the amplitude envelope and its
  Stirling form, the discrete Laplace estimate and concentration of block
  mass. Section 18: the proofs, and **02's abstract transfer lemma for
  coherent dyadic blocks** (Lemma 18.1) with its second proof of the main
  theorem.
- Section 20: `B_d` is neither algebraic nor D-finite (a second route to Part
  I's Theorem 8.2), finite combinations and transforms keep the boundary, and
  **no bidisk**: for every real `v > 0`, `Σ_n (Σ_d b_n^(d) v^d) z^n` has
  radius zero (03).
- Section 21: **every residue class of power-of-two step** `2^s` has a natural
  boundary, with explicit radial ratios (02, Theorem 21.1); and, by the
  writing step (marked [write], proofs included; found valid by the intake's
  adversarial check after the write, not externally reviewed), a
  single-dominant-block Lemma 21.4 and **Theorem 21.5: every arithmetic
  section, of any step `r ≥ 1`, has a natural boundary**, so every arithmetic
  subsequence of `b^(d)` is non-P-recursive. Corollary 21.7 (the intake's,
  derived from Theorem 21.5): at a dyadic root `ζ` the radial ratio of a
  section has a limit exactly when `ζ^(j_q)` is eventually constant, and
  otherwise the distinct subsequential limits
  `ζ^(1+j) (1 − (aR)^r) / (1 − (aRζ)^r)` (for `d = 0`, `r = 3`, `r₀ = 0`,
  `ζ = −1` the ratio jumps between `−63/65` and `63/65`; for `r = 6`,
  `r₀ = 0` the limit exists at `−1` but not at `i`).
- Section 22: the two packages' computations and diagnostics (Tables 4–5 and
  the tables of Section 22.4–22.6, Figures 1–4); Section 23: first block and
  amplitude corrections (03, Table 6); Section 24: thirteen merged further
  questions, and the writing step's **Proposition 24.1**: the `O(L)` term
  lies between `(−3 + φ)L` and `(−2 + φ)L` up to `o(L)`, where
  `φ = 1 + y − 2^y` at `y = y₀(L)`, the fractional offset of `(L + log L)/log 2`;
  if `log u_m = (log 2/2) m² + α m + o(m)`, the coefficient of `L` oscillates
  between `α/log 2 − 3/2` and that plus `0.0861…`, so it has no limit (the
  exact `u_m` for `m ≤ 64` suggest `α ≈ −0.744`; a numerical observation, not
  a proof). Section 25: the mechanism, the source audits and Part II's
  ledger.

## What is not claimed

- **The formula `a(n) = n − ⌈log₂ n⌉` is not presented as new.** Its upper
  half is in Tomescu's thesis *Sets as Graphs* (Udine, December 2011),
  printed p. 29, credited in the manuscript; the intake read that page (the
  count of classes with `s` sources vanishes unless `2^(n−s) ≥ n`, "by
  extensionality and the pigeonhole principle"). The matching construction
  for every admissible source count is supplied here, without a priority
  claim. OEIS still labels the formula a conjecture, but an OEIS label is not
  a priority certificate or evidence that the problem was open in the
  literature.
- Not new either: the collapse to transitive sets, rigidity, the source sieve
  and total recurrence (Johnston's 2012 Maple program in A182162;
  Policriti–Tomescu; Tomescu), Tomescu's source-deletion recurrence, and the
  covering estimate and source maximum that Part II re-proves from Part I.
  The exact boundary formulas are short consequences of the sieve, and the
  article says so.
- No historical priority is established for the boundary refinements of
  Part I or for the natural-boundary results of Part II; all searches were
  limited. Wagner's ANALCO 2012 paper and its Algorithmica 2013 version,
  Peddicord's 1962 paper and Policriti–Tomescu were not read in full; no
  unchecked theorem from them is used. Breuer–Simon is used for terminology
  only; its bounded-coefficient theorem is not applied.
- Part I makes no natural-boundary claim for `B_d` (its Remark 8.3, Question
  1 and ledger say so; dated notes there now point to Part II). Part II makes
  no claim about radial behaviour at non-dyadic angles or at almost every
  angle, about nonlinear differential algebraicity, about complex defect
  fugacity, or about a further universal term in the phase law; nothing in
  either Part is proved for defects growing with `n`, and there is no
  asymptotic expansion of `u_m`. The expansion of Theorem 9.1 excludes the
  complete-layer edge `p → 1`; the sampler is conditional on sampling the
  core.
- Part II's [write] results (Lemma 21.4, Theorem 21.5, Proposition 24.1) are
  the writing step's own, with proofs. The intake's adversarial check after
  the write found them valid (below); that is a careful reading with
  computations, not a formal verification or an external review.
  Proposition 24.1(ii) is conditional.
- Manuscript 03 says "independent internal reviews" checked its proofs. The
  intake could not verify that statement about its preparation; it is not
  evidence of review (Part II, Section 24, item 13).
- No Lean, Rocq or interval-arithmetic certification; Section 12.1 is a
  development plan, not a claim about existing declarations. The finite
  checks are tests, not proofs.
- **Appendix A is draft OEIS text and stays so.** Nothing was submitted to
  OEIS by the packages' authors (`STATUS.md`: "No GitHub mutation, OEIS
  submission, or external publication"; the Part II packages likewise made
  "no repository commit, OEIS submission, or message") or by the intake; a
  dated `[write]` note at the appendix says so. The intake did not search
  OEIS for the boundary sequence `1, 1, 2, 1, 20, 20, 10, 2, 7128, …`, which
  the appendix proposes as a possible new entry only after such a search.

## Checks made at intake

Batch 85 (Part I). On 3 October 2026 the intake read A182220 on `oeis.org`:
its formula section lists four conjectural expressions (Karttunen 2013, Hurt
2014, Barry 2017, Krivilev August 2026), each equal to `n − ⌈log₂ n⌉`
(checked for `n < 600`), and its 30 displayed terms agree. It read printed
pages 26–29 of Tomescu's thesis (the PDF linked in the bibliography): the
source bound is on p. 29, rigidity (Lemma 2.1.3) on p. 27, the deletion
recurrence (Corollary 2.1.7) on p. 28, as the manuscript cites them. The
delivered programs passed on scratch copies.

Batch 98 (Part II). The placement read the main proofs of both manuscripts
line by line and found no gap; independent mpmath checks confirmed the
initial counts `U_0..8`, the first sixteen `b_n^(0)`, manuscript 03's first
block and amplitude corrections (bounded scaled residuals), the agreement of
the two manuscripts' leading amplitudes, and the example ratios `−3/5` and
`(−3+12i)/17`; the three `u(n,k)` tables (Part I's and both packages') agree
on all 1,759 positive cells with `n ≤ 64`. No claim of either manuscript was
found false, and no repository claim was refuted. The write reran both
suites on scratch copies (below) and checked its own Lemma 21.4, Theorem 21.5
and Proposition 24.1 numerically (Part II, Section 22, last note).

After the write (5 October 2026). An independent adversarial check by the
intake reread the three proofs and found Lemma 21.4, Theorem 21.5 and
Proposition 24.1 valid. Its computations: the bounds behind Lemma 21.4 exactly
for `m ≤ 63`; Theorem 21.5's asymptotic against exact coefficients (`n` up to
`2^52`) for `d = 0, 1`, steps `r = 2, 3, 5, 6`, every residue and five dyadic
roots, with the largest absolute error inside the bracket falling to
`2.4·10⁻⁴` at `q_t = 46`; an adversarial probe at the crossover radii
(`d = 0`, `r = 3`, `ζ = −1`) where the section changes sign near
`y₀ ≈ 0.06`, showing the theorem's restriction on `y₀` is necessary; and
Proposition 24.1 and Remark 24.2 against the exact `u_m` (`m ≤ 64`). It is
recorded in a dated note in Part II's item 13 of Section 24. It found no
error in a proof; it led to Corollary 21.7 (Remark 21.6 and item 5 of
Section 24 had listed the radial-ratio limit as unproved, though Theorem
21.5 decides it; both keep their original wording in dated notes), and to
two corrected labels in the Section 22 note (`L ≈ 16.3` and `L ≈ 11.7` give
`q_t = 29` and `22`, not `27` and `20`).

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
no formal development in ProveIt treats extensional digraphs, transitive-set
enumeration or this triangle, and the report's place in the collection
confers no formal status. The hereditarily-finite-set codings in
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean` and
`Logic/Interpretability/PAHF/Coq/PAHF.v` are syntax codings, unrelated. No
manuscript uses a repository theorem as a premise.

**Neighbouring reports** (related, no shared theorem):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a003407-dyadic-scaling-rigidity`,
  Part II: its Corollary `dsr:nh:cor:jumps` (from the local-growth rigidity
  theorem `dsr:nh:thm:rigidity`) says an integer, exponentially bounded
  P-recursive sequence without an `n`th-root limit must have exponentially
  large upward jumps. Lemma 8.1 here (`sbd:lem:jump`) is the complementary,
  elementary sufficient condition: a jump after a plateau of every fixed
  length excludes P-recursiveness. The boundary sequences here do jump, so
  a003407's criterion cannot apply to them; a dated note after Lemma 8.1
  explains this, with a003407's example `3^n + (−3)^n + 2^n` showing why the
  plateau hypothesis is needed. Its Question `dsr:nh:q:boundary` asks for a
  natural boundary of the 3AP-free permutation series; Part II's transfer
  Lemma 18.1 (`sbd:edge:lem:transfer`) is a general sufficient criterion
  (coherent dyadic blocks with a common nonvanishing profile), which bears on
  that question by method only: nothing is proved there for A003407.
- `Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets`:
  its `hset:lem:collapse` is the same classical Mostowski collapse as
  Lemma 2.1, for rooted codes.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a116379-bounded-identity-trees`:
  rooted identity trees, the other classical coding of hereditarily finite
  sets.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a089479-fixed-permanent-matrices`
  (batch 108): proves Robinson's strong-component transform (its Section 4,
  (19), `fpm:eq:robinson`) by the component form of the marked-source sieve
  of Proposition 5.1 (`sbd:prop:marked`), for all labelled digraphs weighted
  by the permanent; its permanent-one case is the classical acyclic-digraph
  asymptotic (A003024), a class that contains the extensional ones counted
  here. A dated `[write]` note of 7 October 2026 after Proposition 5.1 says
  so; no theorem is shared.

**Stale claims.** The manuscripts' repository statements are true at their
pins and stay as dated provenance: Part I's (Section 1.3 and `SOURCES.md`: no
treatment of A182220 found; the Mahonian growing-powers alternative rejected
because `oeis-sequence-asymptotics/a380274-mahonian-growing-powers` exists)
and Part II's (Part I's Question 1 open and its ledger saying "not proved").
Part I's sentences that the natural boundary is open — Remark 8.3, Question 1
of Section 12.2, the Conclusion and the ledger row — keep their text and gain
dated `[write]` notes (5 October 2026). The delivered `STATUS.md` still says
"No proof of a natural boundary for the extremizer generating functions B_d";
it describes Part I's package and stays byte-identical.

## Notation

Part I reuses several letters with local meanings (`d` as defect and in
`d/dp`; `B_d` vs the Bernoulli numbers `B_{2j}`; `T = 2^m` vs the labelled
count `T(n,k)` of Appendix A; `C`, `L`, `N`, `p`, `R`, `M`, `A`). The labelled
count `E(n, a(n))` in eq. (11) is not defined in the text; it is
`n! u(n, a(n))`. A table in the first `[write]` note (end of Section 1) fixes
each meaning, with the tempting false reading that the phase
`p = n/2^(q+d)` of Section 9 equals `ρ_n = n/2^q` (true only for `d = 0`).

Part II writes everything in manuscript 03's letters and translates manuscript
02's; its notation table (second note after the Part II heading) gives, for
each symbol, its meaning in Part II, manuscript 02's symbol, and Part I's
meaning. The clashes: `a` is `2^(d+1) − 1` (02's `a − 1`; not `a(n)`); 02's
`a` is `c = 2^(d+1)`; 02's `ρ_d` is written `aR` (not the dyadic phase
`ρ_n`); `K = 2^(q−1)` (02's `N`; not Part I's `N = 2^m`); `A_q = u_m C_q
R^(K+1)` is 02's `c_q` (02's `A_q` is `u_m C_q`; not Part I's `A`); 02's
`P_q(w)` is `P_q(Rw)`; `t` and `L = log(1/t)` are 02's `ε` and its `L`
(which 02 also used for a source family); 02's `T(L)` is `𝒯(L)` (`T` is a
real radius; Part I's `T = 2^m`); `h` is always `log 2` (02 also used `h` for
the step `2^s`, now `r = 2^s`); 02's `H_{d,h,r0}` is `B_d^(r,r0)` (not the
entropy `H`); 03's `λ_d` (coefficients of a combination) is `γ_d` (not
Part I's `λ_d`); 03's `U_m` is `u_m`. No symbol of Part I was renamed.

## Labels

Every label carries the prefix `sbd:`. Part I's 68 labels (63 delivered
labels prefixed at the batch-85 write, plus five section labels) are
unchanged: none lost or renumbered (checked against a build of the committed
text). Part II adds 128 labels in `article.tex` — `sbd:xtm:` (76, manuscript
03's and the merged statements), `sbd:edge:` (33, manuscript 02's), `sbd:wr:`
(17: the writing step's results and Section 21.2, and the intake's
Corollary 21.7, `sbd:wr:cor:ratio`), and `sbd:part:one`, `sbd:part:two` — for
196 labels in the source. Three more,
`sbd:xtm:tab:computed-block-profiles`, `sbd:xtm:tab:computed-radial-errors`
and `sbd:xtm:tab:computed-first-corrections`, come from the shipped table
files, which `\sbdinput` reads with the prefix added to every label and
`\eqref` name in them (the files themselves are unchanged); the build defines
199 labels. Corollary 21.7 was added at the end of Section 21 with unnumbered
displays, so no earlier label changed number (checked against a build of the
previous text).

The batch-98 write also:

- added a `\part` heading for Part I (`sbd:part:one`) and a dated note before
  the contents on the two Parts; dated `[write]` notes at Remark 8.3, Question
  1, after Question 10, in the Conclusion, after the ledger, and a bracketed
  note in Section 11.1 pointing to the deletion-recurrence proof;
- added an unnumbered heading "Appendices to Part I" before Appendix A, and a
  `\clearpage` before Appendix B so that the ledger does not break across
  pages (a breaking longtable makes the current LaTeX kernel log "Infinite
  glue shrinkage found in box being split");
- added macros `\C`, `\e`, `\ii`, `\dd` (as in the Part II manuscripts) and
  `\sbdinput` to the preamble, and three bibliography entries (Wagner's
  Algorithmica version, Breuer–Simon, DLMF).

No statement, proof or number of any manuscript was changed, except that
manuscript 02's symbols are translated as listed above.

## Files

```text
README.md                                    this guide (replaces the delivery READMEs)
article.tex                                  the report (Part I as delivered with labels prefixed and dated notes; Part II merged by the writes)
article.pdf                                  compiled report, 63 pages
SOURCES.md                                   Part I package: source and provenance notes (as delivered)
STATUS.md                                    Part I package: proof and verification status (as delivered)
manifest-entry.tex                           Part I package: suggested catalogue paragraph (as delivered)
02-source-edge-PROVENANCE.md                 manuscript 02: provenance and attribution (as delivered)
03-source-extremum-SOURCE_NOTES.txt          manuscript 03: source and novelty audit (as delivered)
code/verify.py                               Part I: exact checks and brute-force enumeration
code/check_asymptotics.py                    Part I: Decimal diagnostics of the first correction (imports verify.py)
code/02-source-edge-verify.py                02: exact checks, full-set generation, mpmath profile and radial diagnostics, figures
code/02-source-edge-make_article_tables.py   02: writes data/article_tables.tex from data/validation.json
code/02-source-edge-Makefile                 02: PDF build and regeneration targets (delivery names)
code/03-source-extremum-verify.py            03: exact checks, DAG enumeration, diagnostics, tables, figures
code/03-source-extremum-build.sh             03: two-pass pdflatex build (delivery names)
data/verification.json                       Part I: recorded exact run
data/source_triangle.csv                     Part I: u(n,k), n! u(n,k), n <= 64 (1759 rows; CRLF)
data/boundary_counts.csv                     Part I: a(n), b_n^(0..2), n! b_n^(0), n <= 64 (CRLF)
data/asymptotic_checks.csv                   Part I: first-correction diagnostics (12 rows; CRLF)
data/asymptotic-output.txt                   Part I: transcript of check_asymptotics.py
data/02-source-edge-requirements.txt         02: mpmath 1.3.0, matplotlib 3.10.8, numpy 2.3.5 (Python >= 3.11)
data/02-source-edge-source_triangle.csv      02: u(n,k), n <= 64 (2080 rows; CRLF)
data/02-source-edge-boundary_counts.csv      02: b_n^(d), n <= 128, d <= 3 (512 rows; CRLF)
data/02-source-edge-core_counts.csv          02: u_m with the chain and upper bounds, m <= 64 (CRLF)
data/02-source-edge-exhaustive_counts.csv    02: full sets by direct generation, n <= 7 (CRLF)
data/02-source-edge-profiles.csv             02: complex block-profile evaluations (140 rows; CRLF)
data/02-source-edge-profile_summary.csv      02: per-block coefficient l1 bounds (CRLF)
data/02-source-edge-endpoint_amplitudes.csv  02: amplitudes c_q against the Stirling main term (CRLF)
data/02-source-edge-radial_growth.csv        02: radial magnitudes with truncation bounds (CRLF)
data/02-source-edge-radial_ratios.csv        02: radial ratios at dyadic roots (300 rows; CRLF)
data/02-source-edge-validation.json          02: machine-readable run report
data/02-source-edge-run-output.txt           02: run transcript (six progress lines, then the JSON report)
data/02-source-edge-article_tables.tex       02: generated tables, input in Section 22
data/03-source-extremum-requirements.txt     03: mpmath 1.3.0, matplotlib 3.10.8
data/03-source-extremum-source_triangle.csv  03: u(n,s), n <= 64, including n = 0 (CRLF)
data/03-source-extremum-core_counts.csv      03: U_m with the chain and upper bounds, m <= 64 (CRLF)
data/03-source-extremum-block_profiles.csv   03: Q_q(R_d) for d <= 2, q = 5, 8, 11, 14 (CRLF)
data/03-source-extremum-radial_ratios.csv    03: radial ratios at roots of order 4 and 8 (CRLF)
data/03-source-extremum-extremal_scaled_coefficients.csv  03: b_n^(0) and log(b_n^(0) R^n) (CRLF)
data/03-source-extremum-first_correction_checks.csv       03: first-correction residuals (CRLF)
data/03-source-extremum-verification.json    03: machine-readable run report
data/03-source-extremum-verification.txt     03: human-readable run report
data/03-source-extremum-diagnostic_tables.tex       03: Tables 4-5, input in Section 22.2
data/03-source-extremum-first_correction_tables.tex 03: Table 6, input in Section 23
figures/02-source-edge-profile_convergence.pdf            02: Figure 3
figures/02-source-edge-profile_convergence.png            02: PNG preview of Figure 3
figures/02-source-edge-radial_behavior.pdf                02: Figure 4
figures/02-source-edge-radial_behavior.png                02: PNG preview of Figure 4
figures/03-source-extremum-dyadic_scaled_coefficients.pdf 03: Figure 1
figures/03-source-extremum-dyadic_scaled_coefficients.png 03: PNG preview of Figure 1
figures/03-source-extremum-radial_phase_convergence.pdf   03: Figure 2
figures/03-source-extremum-radial_phase_convergence.png   03: PNG preview of Figure 2
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Part I's placement moved `verify.py` and
`check_asymptotics.py` to `code/`. Part II's placement (`b50febf79`) staged
39 files (21 of manuscript 02, 18 of manuscript 03; 1,863,648 bytes) under
their prefixes: scripts in `code/`, records and requirements in `data/`,
figures in `figures/`, source notes at the root. Delivery name → shipped name
is the prefix plus the base name, with these moves: 02's `Makefile` →
`code/02-source-edge-Makefile`, 02's root `requirements.txt` →
`data/02-source-edge-requirements.txt`, 03's root `verify.py` and `build.sh` →
`code/03-source-extremum-…`, 03's `requirements.txt` →
`data/03-source-extremum-requirements.txt`. 03's `requirements.txt` is
byte-identical to the generic requirements files of two other collection
reports (`a082528-rounding-extinction`, `a277364-bell-asymptotics`).

Not shipped, and recoverable from the archives
(`git show 9d6968c8a:docs/incoming/OEIS_A182220_Source_Boundary_Research.zip`,
`git show 2172df76a:docs/incoming/OEIS_EAD_Natural_Boundaries.zip`,
`git show 2172df76a:docs/incoming/OEIS_Source_Boundaries.zip`, each
redirected into a scratch file):

- Part I: the delivered 21-page `article.pdf` (437,459 bytes); `SHA256SUMS`
  (14 of 14 verified at placement); `data/verification-output.txt` (2,127
  bytes), a **byte copy of `data/verification.json`** (`verify.py` prints
  the JSON report it writes).
- Manuscript 02: `ead_natural_boundaries.tex` (56,207 bytes), its 22-page PDF
  (490,952 bytes) and `README.md` (5,040 bytes).
- Manuscript 03: `article.tex` (61,075 bytes), its 23-page PDF (520,252
  bytes), `README.txt` (4,995 bytes) and `SHA256SUMS.txt` (21 of 21 verified
  at placement; repository policy ships no checksum manifests).

Nothing was excluded as heavy; the largest Part II file,
`data/03-source-extremum-source_triangle.csv` (386,435 bytes), is regenerated
byte for byte in seconds.

**Delivered text that names the delivery layout or a file not shipped.**
`SOURCES.md`, `STATUS.md` and `manifest-entry.tex` as described for Part I
below. `code/02-source-edge-Makefile` builds `ead_natural_boundaries.tex` and
runs `code/verify.py` and `code/make_article_tables.py`;
`02-source-edge-PROVENANCE.md` points to `README.md` and
`data/validation.json`; `code/02-source-edge-make_article_tables.py` reads
`data/validation.json` and writes `data/article_tables.tex` relative to its
parent directory; `code/03-source-extremum-build.sh` builds `article.tex`
into `article.pdf`; `data/03-source-extremum-verification.txt` names
`diagnostic_tables.tex` and `first_correction_tables.tex`. All of these mean
the delivered package layout. The Part I files: `SOURCES.md` and `STATUS.md`
are unchanged (`STATUS.md`'s "The final PDF was compiled with pdfLaTeX"
describes the delivered 21-page PDF); `manifest-entry.tex` calls itself "not
uploaded or committed"; `code/verify.py`'s docstring says `python verify.py`
from the package root; both Part I programs default their output to a
`data/` directory next to the script. Part I's mentions of "the accompanying
program" mean `code/verify.py`.

**Third-party data.** `code/verify.py` embeds, as test fixtures, the first
17 terms of A001192 and the first 25 flattened terms of A182162, copied from
The On-Line Encyclopedia of Integer Sequences (https://oeis.org). OEIS
content is published by The OEIS Foundation Inc. under the Creative Commons
Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); those fixture lists are
third-party data under that licence, not MIT-0 like the rest of the
repository. The Part II packages ship no OEIS data: every count is computed
by their own code. No program contacts OEIS or the network.

**Byte-level notes.** Every CSV file is CRLF throughout (Python's `csv`
module); `-text` lines in `SetTheory/Cardinals/.gitattributes` (three for
Part I, fifteen for Part II) keep their bytes. The JSON, text and `.tex`
outputs are written in text mode, so on Windows a rerun emits them with CRLF
where the shipped files are LF; compare after stripping `\r`. Runtime fields
(`elapsed_seconds`, the Python version) and figure metadata change between
runs; byte identity of those is not a reproducibility criterion (as
manuscript 02's README says).

## Rerun the checks (on scratch copies only)

**Never run the programs in place.** Part I's `verify.py` defaults `--out` to
`code/data/`, and `check_asymptotics.py` writes to `data/` next to the
script. Manuscript 02's `verify.py` defaults `--out-dir` to the parent of
`code/`, i.e. **this report's root**: run here, it would overwrite Part I's
`data/boundary_counts.csv` and `data/source_triangle.csv` with files of the
same names but different content, and write further unprefixed files into
`data/` and `figures/`; its `make_article_tables.py` has no option and would
look for `data/validation.json` here. Manuscript 03's `verify.py` writes
`data/` and `figures/` beside itself, inside `code/`. Each recipe below
rebuilds the delivered layout in a temporary directory (Git Bash, from this
directory).

Part I (standard library only, Python 3.10 or later):

```sh
T=$(mktemp -d); X="$T/oeis_source_boundary"; mkdir -p "$X"
cp code/verify.py code/check_asymptotics.py "$X/"
cd "$X"
py verify.py --max-n 64 --brute-n 7 > "$T/verify.out"   # about 7 s
py check_asymptotics.py > "$T/asym.out"                 # about 4 s
cd - >/dev/null
for f in "$X"/data/*; do
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/$(basename "$f")") \
    && echo "same  $(basename "$f")" || echo "DIFF  $(basename "$f")"; done
tr -d '\r' < "$T/verify.out" | cmp - data/verification.json && echo "stdout = verification.json"
tr -d '\r' < "$T/asym.out"   | cmp - data/asymptotic-output.txt && echo "transcript matches"
```

At intake (3 October 2026, Windows, Python 3.14.4) this printed `same` for
all four files and both matches. The run checks 2,080 triangle cells by two
recurrences, 2,080 covering inequalities, 64 extremizer counts and 354
finite-defect entries (`d ≤ 5`), the 17 + 25 OEIS fixture terms, and an
exhaustive enumeration through `n = 7` (75,598 classes at `n = 7`);
`check_asymptotics.py` confirms at `n = 192, 768, 3072, 12288` and
`d = 0, 1, 2` that the first correction improves all 12 leading
approximations.

Part II (needs mpmath 1.3.0 and Matplotlib 3.10.8, and for 02 NumPy 2.3.5 and
Python 3.11 or later):

```sh
U="uv run --no-project --python 3.12 --with mpmath==1.3.0 --with matplotlib==3.10.8 --with numpy==2.3.5 python"
T=$(mktemp -d)
E="$T/ead-natural-boundary"; mkdir -p "$E/code" "$E/data" "$E/figures"
cp code/02-source-edge-verify.py "$E/code/verify.py"
cp code/02-source-edge-make_article_tables.py "$E/code/make_article_tables.py"
(cd "$E" && $U code/verify.py > "$T/02-run-output.txt" && $U code/make_article_tables.py)
X="$T/oeis_natural_boundaries"; mkdir -p "$X"
cp code/03-source-extremum-verify.py "$X/verify.py"
(cd "$X" && $U verify.py --max-n 64 --brute-n 6 > "$T/03-stdout.txt")
for f in "$E"/data/*; do b=$(basename "$f")
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/02-source-edge-$b") && echo "same  02 $b" || echo "DIFF  02 $b"; done
for f in "$X"/data/*; do b=$(basename "$f")
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/03-source-extremum-$b") && echo "same  03 $b" || echo "DIFF  03 $b"; done
```

At the batch-98 write (5 October 2026, Windows, Python 3.12.13) manuscript
02's run took about 77 s and manuscript 03's about 44 s (recorded: 15 s and
10 s). All fifteen CSV files were reproduced byte for byte and the three
`.tex` table files after stripping `\r`; `validation.json`, `run-output.txt`,
`verification.json` and `verification.txt` printed `DIFF` only for the
Python patch version and the elapsed time, and the figures were re-rendered
(their bytes differ). Manuscript 02's run checks 2,080 triangle cells by two
recurrences, 2,080 support and covering assertions, 242 finite-defect
entries, 64 core bounds, 112 binomial spot checks and full sets through
`n = 7` (75,598), and evaluates 140 profile points and 300 radial ratios at
100 digits; manuscript 03's checks both triangles through `n = 64` (2,080
cells), 242 finite-defect entries, 1,040 + 80 first-order coefficient
identities, and enumerates 32,768 ordered graphs on six vertices (3,240
extensional, 1,802 classes).

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
enumitem, xcolor, graphicx, fancyhdr, hyperref, lmodern, microtype; expl3 for
`\sbdinput`); the bibliography is embedded. The three table files and the four
figure PDFs are inputs. Build in a scratch copy:

```sh
B=$(mktemp -d); mkdir -p "$B/data" "$B/figures"
cp article.tex "$B/"; cp data/*_tables.tex "$B/data/"; cp figures/*.pdf "$B/figures/"
cd "$B"; latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 63 pages (Part I's 23
pages before batch 98; rebuilt on 7 October 2026 after the batch-108
reciprocal note, still 63 pages, every label keeping its number); no errors
or warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. (Until 5 October 2026 the uncaptioned notation
longtable of Part II and Table 3 shared the PDF destination `table.3`, which
pdfTeX reported as a duplicate; the longtable's counter step now has its own
hyperref name.) Every table (1–6) and figure (1–4) appears;
a missing input stops the build (manuscript 03's `\IfFileExists` guards,
which would drop them silently, are not used).

## Provenance

- Sources cited by Part I: OEIS A182220, A182162, A001192, A182161; Tomescu,
  *Sets as Graphs* (PhD thesis, Udine, 2011); Policriti–Tomescu, Inform.
  Process. Lett. 111 (2011) 787–791; Wagner, ANALCO 2012, 1–8; Peddicord,
  Proc. AMS 13 (1962) 825–828. Added by Part II: Wagner, Algorithmica 66
  (2013) 829–847; Breuer–Simon, Adv. Math. 226 (2011) 4902–4920; NIST DLMF
  §5.11.
- Repository inputs: the pins `6bf7f30d0` (3 October 2026; Part I) and
  `d18416ec7` (4 October 2026; both Part II manuscripts), used for
  non-duplication searches and as the text continued; no repository theorem
  is used.
- Part I: batch 85 of `docs/incoming`, manuscript 07; arrival `9d6968c8a`,
  placement `ddf8df5d5` (batch 85C), written in `eab47e330` (3 October 2026).
- Part II: batch 98, manuscripts 01 and 05; arrival `2172df76a`, placement
  `b50febf79` (batch 98C), written by the batch-98 write (5 October 2026).
  The merge chose manuscript 05 as base (same hypotheses, stronger on every
  shared theorem); shared theorems are printed once and credited to both,
  with manuscript 01's different proofs as marked second routes; everything
  only in manuscript 01 is printed in full; the statements both re-prove
  from Part I are printed as a correspondence table with the differing
  routes; the question lists and ledgers are merged. The provenance notes at
  the start of Part II give the details.
