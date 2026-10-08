# Distinct Multiplicity Values in Integer Partitions (OEIS A373271 and A373273)

**Part I: the mean number of distinct multiplicity values of a partition of
`n` is `(6n)^{1/4} − 23/16 + K n^{−1/4} + O(n^{−1/2})`,
`K = (π/6^{1/4})(12365/82944 + 15/(8π²))`, where `−23/16` needs an exact
telescoping tail `−1/2`; total counts, eventual increase and a shrinking
two-ceiling inverse. Part II: the mean sum of the distinct multiplicity
values has the five scales `√n log n`, `√n`, `n^{1/4}`, `log n`, `1` with error
`O(n^{−1/4})`, leading term `√(6n) log n/(4π)`, the constant involving a
delta square and a finite-difference tail in which `ζ′(−1)` cancels; absolute
expansion, eventual increase and a shrinking two-ceiling inverse. One exact
identity `Σ a_n qⁿ = P(q) Σ_m w(m)(1 − Q_m(q))` with `w = 1` and `w(m) = m`.
Part III: the fluctuations of `D_α = Σ_m m^α 1{N_m > 0}` for every `α ≥ 0`;
Gaussian below `α = 1/2` with an explicit kernel, so that
`Var_n D_0 ~ v_0 n^{1/4}`, `v_0 = 6^{1/4}(√2 − 3/4 − (3√2/8) log(1+√2)) =
0.3080002444…`, with a central limit theorem; a `log n` variance factor at
`1/2` with a Gaussian window field; non-Gaussian series of exponentials above
`1/2`, among them a Gumbel law for the sum `D_1` with `Var_n D_1 ~ n`; the
three regimes mutually independent**

A research report bound from two manuscripts dated 4 October 2026 ("Report
197" and "Report 198" of a session bundle) and a continuation manuscript
dated 7 October 2026 (Part III, added the same day). The author lines and PDF
author fields of the first two read "Report 197" and "Report 198": they name
no person, tool or addressee. Neither package carries a "prepared for private
review" line, an e-mail address or personal data. Part III's title page reads
"Research draft prepared with ChatGPT" and "Prepared for Vladimir
Reshetnikov's research programme", its PDF author field "ChatGPT"; it names
ChatGPT as the tool and no human author, and carries no e-mail address or
personal data.

| Part | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | Report 197 (batch 111, base) | `Report197_TeX_and_Reproducible_Code.zip` (14 files, no wrapper directory, 793,611 bytes, SHA-256 `192aeca1a0b8…bc038875d653adc`), arrival commit `60f54ea06`; main file `Report197.tex` (759 lines, 18 pp.) | none | `d451ef3d8` (batch 111) | Part I, Sections 1–11, labels `dmv:cnt:` |
| II | Report 198 (batch 111) | `Report198_TeX_and_Reproducible_Code.zip` (17 files, no wrapper directory, 909,536 bytes, SHA-256 `8d10255b48c3…8eacce24e871492`), arrival commit `60f54ea06`; main file `Report198.tex` (663 lines, 17 pp.) | none | `d451ef3d8` (batch 111) | Part II, Sections 12–24, labels `dmv:sum:` |
| III | none (continuation of Part I) | `ProveIt_Research_2026-10-07.zip` (32 files in one wrapper directory, 1,527,416 bytes, SHA-256 `49c8000eea95…07b2b5b4c07`; holds this manuscript and an independent sensitivity note), arrival commit `7b8ed30e7`; main file `partitions/article.tex` with ten section files (2,346 lines, 35 pp.) | ProveIt `1210e9d3a` (Part I alone); `math` `adc7f1241b42` | `9a10a617f` (non-Gowers intake NG1) | Part III, Sections 25–34, labels `dmv:fl:` |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## How the merge was made

- **Base and order.** Report 197 is the base: its `Report197.tex` was staged
  as `article.tex`, it arrived first, and Report 198's package was adapted
  from it. Report 198 is printed second. Neither Part cites the other, and
  Report 198's README says that "No A373271 theorem or coefficient is used as
  a mathematical premise"; the merge claims no result relating the two
  statistics beyond the shared identity.
- **What binds them.** The same identity with weights `1` and `m`; the same
  whole-circle bound through the positive products `P_m = P Q_m`; the same
  local saddle transfer; and Part II answers Part I's Question 4 (weighted
  occupied values) for `w(m) = m`, leaving `m^α` open (Part II's Question 2).
  A373271's OEIS entry itself points to A373273.
- **Duplication.** Part II re-derives the sector estimates (its Section 14,
  against Part I's Sections 3–4), the whole-circle bound (Section 19, against
  Section 6) and the monomial transfer (Section 20, against Lemma 7.1); each
  is kept with a dated note naming Part I's counterpart, because Part II's
  later statements cite them by their own labels, the circle bound carries
  the weight's factor `n(n+1)`, and the transfer is a second route proved for
  complex `s`.
- **Numbering.** Sections are continuous. Part I keeps every delivered
  number; Report 198's Section `k` is Section `k + 11` here and its equation
  `(k.m)` is `(k+11.m)`; its Table 1 keeps its number.
- **Bibliography.** Merged; the two OEIS keys (both delivered as `oeis`) are
  `oeisA373271` and `oeisA373273`; the four shared works are printed once
  with each Part's own inspection note.
- **Part III (second write, 7 October 2026).** The continuation manuscript
  *Fluctuations of Distinct Multiplicities in Random Integer Partitions* was
  written from Part I alone (its ProveIt pin `1210e9d3a` precedes Part II's
  write `0064d11e6` by three hours) as the answer to Part I's Questions 2 and
  4. It is printed after Part II as Part III: a new Section 25 (provenance,
  what it answers, checks, non-claims, reading conventions), then its
  Sections 1–9 as Sections 26–34 (shift `k ↦ k + 25`; Figures 1 and 2 keep
  their numbers); its title page and table of contents are not printed, and
  its reference list is merged (six new entries marked [Part III]; its notes
  added to Ralaivaosaona, Corteel–Pittel–Savage–Wilf and the two OEIS
  entries, its single `oeis` key cited as both). Parts I and II keep every
  number. The write also extended the title, the abstract, the running head
  and the Guide (a Part III row, a Part III paragraph, a pointer note), and
  added dated notes to the question lists of Parts I and II; the earlier
  notes there that call `m^α` open are kept as written.
- **What Part III re-proves.** Its means at `α = 0` and `α = 1` are weaker
  forms of Part I's radial expansion and of the first two terms of Part II's
  (the same constant `c = 3/2 − γ/2 = (3 − γ)/2`), by another route; its
  forbidden-pair identity extends Part I's `P_m = P Q_m`. Kept, with a dated
  note at the end of Section 30, because its later statements cite them and
  its proofs are not Parts I and II's.

## Trust boundaries

- **What is proved by hand.** Both Parts' exact identities, uniform sector
  expansions with summed matched remainders (Part I Proposition 4.2,
  Theorem 5.1; Part II Lemma 15.1, Proposition 18.1), whole-circle
  localization, local saddle transfer (Part I Lemma 7.1; Part II Section 20,
  including differentiation in `s`), the means and totals, monotonicity and
  the inverses. No proof uses a computation.
- **What rests on computation.** Nothing in the proofs; the packages check
  the rational identities in exact `Fraction` arithmetic.
- **What is diagnostic.** Part I's table of `T(n)` and Part II's Table 1, the
  floating diagnostics of Part II, and all finite agreements. Remainder
  constants and onsets are existential.
- **What is prior.** Ralaivaosaona's multiplicity limit theorems (the
  `n^{1/4}` transition that "naturally suggests" Part I's leading mean),
  the Grabner–Knopfmacher–Wagner transfer scheme, the modular identity,
  Corteel–Pittel–Savage–Wilf and Lugo (overlap not excluded: abstract-level
  and targeted reading only).
- **Part III.** Proved by hand: the localization of the occupied set
  (Lemma 28.2), the reservoir local limit theorem and moment transfer
  (Lemma 28.3, Proposition 28.4), the cumulant bound and Gaussian field
  (Lemma 29.1, Theorem 29.2), the collision estimates (Lemmas 31.1, 32.1), the
  window (Lemma 32.2) and the independence theorem (33.1). No proof uses a
  computation; the exact moments to `n = 40`, the 55-digit constants and the
  6,000 unconditioned finite-row Boltzmann samples are diagnostics, not
  interval-certified. Prior: Fristedt's geometric model and conditioning
  strategy, the Erdős–Lehner Gumbel law for the number of summands,
  Ralaivaosaona's one-value transition; Corteel–Pittel–Savage–Wilf read only
  at the abstract. Convergence in the window is finite-dimensional only.

## What it proves

`M_j` is the multiplicity of the size `j`; `A = π²/6`, `τ = √(A/(n − 1/24))`.
Statement and equation numbers are those of this file (Part II shifted by
eleven sections).

**Part I** (`D(λ)` = number of distinct positive values of the `M_j`;
`a(n) = Σ D`, A373271):

- **Proposition 2.1 (`dmv:cnt:prop:gf`)**: `Σ a(n)qⁿ = P(q) Σ_m (1 − Q_m(q))`.
- **Theorem 5.1 (`dmv:cnt:thm:radial`)**: `g(t) = √π t^{−1/2} − 23/16 +
  √π d t^{1/2} + O(|t|)` in a sector, `d = 12365/82944`; the constant needs
  the telescoping `Σ δ_m = −1/2` (3.9).
- **Theorem 1.1 (`dmv:cnt:thm:mean`)**: the three-term mean (1.3)–(1.4),
  `K = 0.68058214956683591885…`.
- **Theorem 1.2 (`dmv:cnt:thm:total`)**: `a(n) = C e^{Bx} x^{−3/2}(1 + b_1
  x^{−1/2} + b_2 x^{−1} + O(x^{−3/2}))`, `x = √(n − 1/24)`; eventual strict
  increase.
- **Theorem 1.3 (`dmv:cnt:thm:inverse`)**: `⌈Z(Y) − C_1 x_0^{−1/2}⌉ ≤ N(Y) ≤
  ⌈Z(Y) + C_1 x_0^{−1/2}⌉`, `x_0` a Lambert `W_{−1}` root.

**Part II** (`W(λ)` = sum of the distinct positive values; `a_n = Σ W`,
A373273):

- **(13.3)**: `Σ a_n qⁿ = P(q) Σ_m m(1 − Q_m(q))`.
- **Proposition 18.1 (`dmv:sum:prop:radial`)**: `w(t) = (½ log(1/t) + c)/t −
  7√π/(16√t) + (1/24) log(1/t) + K + O(√|t|)`, `c = 3/2 − γ/2`,
  `K = 9607/20736 − γ/24`.
- **Theorem 12.1 (`dmv:sum:thm:mean`)**: the five-scale mean (12.3)–(12.4).
- **Theorem 12.2 (`dmv:sum:thm:absolute`)**: `a_n = C_N[…]` (12.5); eventual
  strict increase.
- **Theorem 12.3 (`dmv:sum:thm:inverse`)**: two ceilings for the first
  crossing `ν(Y)`, unrounded endpoints `v_Y + O((log Y)^{−1/2}/log log Y)`.

**Part III** (`D_α = Σ_m m^α 1{N_m > 0}`, `D_0 = D`, `D_1 = W`;
`τ_n = π/√(6n)`; the delivered numbers have 25 less in the section number):

- **Theorem 26.1 (`dmv:fl:thm:phase`)**: for `0 ≤ α < 1/2`,
  `Var_n D_α ~ V_α τ_n^{−α−1/2}` and a Gaussian limit, `V_α` given by (26.4) and
  (26.5); at `α = 1/2`, `Var_n D_{1/2} ~ (c_*/(2τ_n)) log(1/τ_n)`,
  `c_* = 1 − π/4`, Gaussian; for `α > 1/2`, `τ_n^α(D_α − E_n D_α) → Z_α =
  Σ_j (E_j^α − Γ(α+1))/j^α` (non-Gaussian), with
  `τ_n^{2α} Var_n D_α → [Γ(2α+1) − Γ(α+1)²] ζ(2α)`, and uncentered limits for
  `α > 1`.
- **Corollary 26.2 (`dmv:fl:cor:unweighted`)**: `Var_n D_0 ~ v_0 n^{1/4}`,
  `v_0 = 0.308000244403717957…`, and `(D_0 − (6n)^{1/4})/(√v_0 n^{1/8}) → N(0,1)`.
- **Corollary 26.3 (`dmv:fl:cor:gumbel`)**: `τ_n D_1 − ½ log(1/τ_n) −
  (3 − 3γ)/2 → Gumbel`, `Var_n D_1 ~ n`.
- **Corollary 26.4 (`dmv:fl:cor:quadratic`)**: `D_2/n → (6/π²) Σ E_j²/j²`, mean
  2, variance 8.
- **Theorem 26.5 (`dmv:fl:thm:window`)**: at `α = 1/2 + θ/log(1/τ_n)` jointly
  Gaussian with covariance `c_*(e^{θ+φ} − e^{(θ+φ)/2})/(θ+φ)`.
- **Proposition 30.1 (`dmv:fl:prop:weightedmeans`)** and **(31.8)**: the
  means `M_α τ^{−(α+1)/2} + Γ(α+1)ζ(α) τ^{−α} + o(τ^{−α})` (`0 < α < 1`,
  `M_α = Γ((1−α)/2)/(1+α)`), `(1/(2τ)) log(1/τ) + (3−γ)/(2τ) + o(1/τ)` at
  `α = 1`, `~ Γ(α+1)ζ(α) τ^{−α}` for `α > 1`.
- **Theorem 33.1 (`dmv:fl:thm:independence`)**: the subcritical, window and
  supercritical limit vectors are mutually independent.
- **(33.12)**: `p(n)B_α(n) − A_α(n)² = p(n)² Var_n D_α`, so for example
  `p(n)B_0(n) − a(n)² ~ v_0 p(n)² n^{1/4}`.

Added by the write (7 October 2026), marked `[write]`:

- **Guide to this report** (`dmv:sec:guide`, before Part I): the Parts, the
  comparison table, the merge choices, provenance, sources read, checks,
  relation to the repository, collected non-claims of both Parts, and a
  two-column table of reading conventions.
- **Remark 1.4 (`dmv:cnt:rem:oeis`)** and **Remark 12.4
  (`dmv:sum:rem:oeis`)**: the OEIS entries (next section).
- **Remark 9.1 (`dmv:cnt:rem:transseries`)**: (a) **instance**: `N(Y)` is the
  staircase of `p0:def:three-inverses`, so `p0:thm:staircase`(1) applies;
  (b) **instance**: `x_0(Y)` is `p0:thm:lambert-core`(3), `b < 0`, in
  `X_vol = x` (`a_vol = B`, `b_vol = −3/2`, `L_vol = log(Y/C)`);
  (c) **formal instance**: the envelopes are exactly exponential–power with
  `δ_vol = 1/2`, and the centre of (9.3) is `p0:prop:two-grid` with
  `δ = 1/2`; the volume's analytic reversion is for `δ = 1` only, so the
  remainder is the source's, whose residual-over-slope step is
  `p0:thm:backward-error`; (d) **analogues**: (1.10) and (9.5) of
  `p0:thm:staircase`(2).
- **Remark 21.1 (`dmv:sum:rem:transseries`)**: (a) **instance** of
  `p0:thm:staircase`(1); (b) **not shown to be an instance**: `log Φ` contains
  `log log x`, outside `p0:def:model`; it is an admissible core of
  `p0:def:core` only by definition, and the initializer (21.4) is not shown to
  be an instance of `p0:thm:flattening`; (c) **instance**: the root error
  (21.3) is `p0:thm:backward-error`; (d) **analogue**: (12.9) of
  `p0:thm:staircase`(2).
- Notes: the three Part I counterparts in Part II (end of Sections 14, 19,
  20); the question notes at the ends of Part I's Questions and Part II's
  Section 24; the merged-bibliography note.

Added by the Part III write (7 October 2026), marked `[write]` or bracketed
"[Added 7 October 2026.]":

- **Section 25** (`dmv:fl:sec:front`): 25.1 the manuscript (archive, pins,
  author lines, how it was merged, the numbering map, what it says about the
  repository); 25.2 a table of what Part III answers in Parts I and II, what
  it proves again and what is new; 25.3 what the intake and the write
  checked; 25.4 the non-claims; 25.5 reading conventions against Parts I and
  II.
- **Dated notes in Part III**: after Corollary 26.2 (`v_0`'s printed digits
  are rounded, the truncation is `0.308000244403717957…`; the fixed-`n`
  variances to `n = 300`); after Corollary 26.3 (its mean is the first two
  terms of Part II's Theorem 12.1); after the review table of Section 27.1
  (the Gowers–Szemerédi ledger count 113/7 is stale, now 114/6; the Keller
  row checked; the `math` rows not checked); after the packaging paragraph of
  Section 27.2 (true at the pin, stale since Part II was written); at the end
  of Section 30 (Parts I and II's counterparts, and the geometric-law means
  of all three Parts evaluated); after (33.12) (the OEIS names and
  revisions); in Section 34 after the exact table (own enumeration, the
  identity as Part I's, the rerun), after the samples (covariance and sample
  tables recomputed), after the reproduction commands (the shipped names) and
  after the eight questions (standing rule).
- **Notes in Parts I and II**: after Part I's questions and after Part II's
  (Section 24), what Part III answers; in the Guide, a Part III paragraph and
  a pointer note after the independent check; in the bibliography, a Part III
  merge note.

## The OEIS entries (Remarks 1.4 and 12.4)

Read on 7 October 2026 in the internal format.

- **A373271** (revision #15, 2 June 2024; _Olivier Gérard_, 29 May 2024),
  offset 1: "a(n) = sum for all integer partitions of n of the number of
  distinct multiplicities in each partition."; row sums of A373269 and
  A373270; "If all distinct multiplicities of all parts of all integer
  partitions are summed, one gets A373273 (1, 3, 5, 11, 18, 29, 48, 74, 107,
  161, ...)."; b-file by Alois P. Heinz (`1 ≤ n ≤ 200`). No formula,
  asymptotic or conjecture. Report 197 could not open the b-file; the write
  fetched it (SHA-256 `b30df65d4321…ae401d`): all 200 terms agree with the
  shipped table, as do the 45 data terms. The bibliography's quoted name
  ("Sum of number of distinct multiplicities over all partitions of n.") is a
  paraphrase; kept, and Remark 1.4 says so.
- **A373273** (revision #14, 1 June 2024, the revision Report 198 read;
  _Olivier Gérard_): "a(n) = sum of all distinct multiplicities in every
  integer partition of n."; 43 terms; "Sum of the rows of triangle A373272.".
  The live text is identical to the shipped `data/198-sum-A373273.seq`. No
  formula, asymptotic or conjecture.
- The write enumerated all partitions of `n ≤ 55` by multiplicity vectors and
  computed both statistics: all agree with the shipped tables. Nothing was
  submitted to the OEIS.
- Read again at the Part III write (7 October 2026, plain-text format):
  A373271 still revision #15 and A373273 still #14, names as above. Part III
  cites both under one key with A373271's paraphrased name, and could not
  retrieve A373273; its first ten values of each agree with the live data
  (dated notes after (33.12) and after the exact table of Section 34.1).

## What is not claimed

From Parts I and II, kept in the article (collected in the Guide):

- **Part I**: finite order only; no explicit constants or onset; no variance,
  fluctuation or central limit theorem; no exact single-ceiling inverse (no
  values of `C_1`, `Y_0`); no interpolation assumed; no absolute novelty,
  complete coverage or priority (Corteel–Pittel–Savage–Wilf read only at
  abstract level, Lugo at targeted passages); no b-file comparison by the
  source.
- **Part II**: no explicit onset or certified constant, no all-orders
  expansion, no distributional theorem, no single exact ceiling for every
  `Y`, no numerical `X, M, n_0`, no exponentially small final remainder, no
  new general transfer theorem, no novelty; comparisons with Archibald et
  al., Fill–Janson–Ward, Corteel–Pittel–Savage–Wilf and Lugo are not
  exclusion certificates; diagnostics and the inverse root calculation are
  not interval-certified.

The write adds: its checks are floating, finite or hand computations; the
transseries remarks claim no novelty for any inversion; the merge claims no
relation between the two statistics beyond the shared identity.

- **Part III** (collected in Section 25.4): finite checks and 55-digit
  constants are implementation evidence, not interval-certified; the samples
  are unconditioned finite-row Boltzmann samples, not fixed-`n` partitions;
  the critical finite-size discrepancy is "deliberately retained", with no
  onset or finite-`t` error; window convergence is finite-dimensional only
  ("No tightness statement … is used or claimed"); no effective Kolmogorov or
  Wasserstein bound; the regularly varying variance formula of its Question
  4 "is a proposed extension, not a theorem"; nothing formalized; no global
  priority (Corteel–Pittel–Savage–Wilf full text not obtained). The write
  adds that its fixed-`n` variances to `n = 300` are consistent with `v_0`
  but do not decide it.

## Further questions

Part I's Section 11.2 keeps its five questions (one further matched order;
variance and fluctuations; effective error bounds; weighted occupied values;
the literature comparison) and Part II's Section 24 its five (the next matched
order; other weights `m^α`; explicit inverse certification; weighted
fluctuations; a fuller source comparison). Dated notes record that Part II
answers Part I's Question 4 for `w(m) = m` only, that `α = 0` and `α = 1` are
the two Parts and the family `m^α` stays open, that both tables increase
strictly from `n = 1` (no onset proved), and that under Vladimir's standing
rule of 4 October 2026 nothing was moved or refuted. **No claim of either
source was found to be wrong or unproved.**

Part III (Section 34.5) keeps its eight questions open: an effective
Gaussian approximation for `D_0`; the next variance term and the critical
finite-size correction; functional convergence of the window; regularly
varying weights; the largest occupied values as a point process;
conditioning corrections and universality; formalization and a faster exact
second-moment algorithm; the historical comparison (the same task as
Questions 5 of Parts I and II). Dated notes of the Part III write (after
both question lists and in Section 25.2) record the re-scoping:

- Part I, Question 2 (variance, fluctuations, conditioning): **answered** by
  Corollary 26.2 with Theorem 26.1(i), Lemmas 28.2–28.3 and Proposition 28.4.
- Part I, Question 4 (weighted occupied values): **answered for `m^α`,
  `α ≥ 0`**, as to fluctuation laws (Theorems 26.1, 26.5, 33.1) and leading
  means (Proposition 30.1, (31.8)); other weights, and mean expansions of
  Part I's precision for `α ≠ 0, 1`, open.
- Part II, Question 2 (other weights `m^α`): **partly answered**: the
  leading scale for every `α`, and the next term for `0 < α ≤ 1` (the write
  said "for every `α`"; for `α > 1` Part III proves the leading term only,
  as the independent check records in a dated note in Section 25.2); the
  matched expansion of Part II's precision for `α ≠ 1`, and any second term
  for `α > 1`, open.
- Part II, Question 4 (variance and law of `W`): **answered** by Corollary
  26.3.
- Questions 1, 3, 5 of both Parts untouched. The earlier notes that call
  `m^α` open were written before Part III and are kept as written.

Under the standing rule the Part III write found no claim of Part III wrong
or unproved as stated; nothing was moved or refuted. Two of its statements
about the repository were true at its pin and are stale now (dated notes in
Section 27).

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; both delivered suites reproduce
  their outputs on copies (failures only Windows artifacts).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  all four checksum manifests verified (13 + 7, 16 + 9 entries); every proof
  of both Parts read line by line (the Guide lists the steps rechecked by
  hand); the two regularized integrals of Part II (`∫ y b′² = −13/72 −
  2ζ′(−1) − γ/6 = 0.05408412102842415943…`, `R_D = −ζ′(−1) − γ/12 =
  0.11731983829198985749…`) and `∫ y b″(2y) dy = −1/8` numerically; `K` of
  Part I (the printed digits are a truncation); every entry of Part I's
  `T(n)` table and of Part II's Table 1 (all printed digits agree); bounded
  residuals of both mean expansions and of the absolute expansions; the
  brute force to 55; partition numbers to 2500 by Euler's recurrence; both
  b-files. Rerun from the shipped files (routes below): Part I `verify.py`
  (≈ 30 s) and `symbolic_checks.py`, Part II `verify.py` (≈ 30 s),
  `symbolic_checks.py` and `diagnostics.py`: receipts and term tables
  byte-identical to the shipped records, except the sector Boltzmann rows of
  Part II's floating diagnostics, whose 15 residual values agree with the
  record only to about ten significant digits (floating library and platform;
  the delivered README promises no cross-platform floating identity; the
  other diagnostic rows are identical).
- Sources read by the write: the OEIS entries; the transseries volume
  (labels in the Guide). Not read: the cited literature.

**Part III.**

- At placement (NG1 dossier, 7 October 2026): the 12 staged files
  byte-identical to a fresh extraction; the exact part of the delivered
  `verify.py` rerun on a copy without simulations (moments CSV byte-identical;
  `checks.json` equal up to the skipped simulations, versions and seven
  last-digit floats); the intake's own fixed-`n` moments to `n = 300`; `v_0`,
  `V_0`, the Gumbel centering and the `D_2` constants re-derived; no claim
  found wrong.
- At the Part III write (7 October 2026; Python 3.14.4, mpmath 1.3.0, NumPy
  2.4.4; own code, kept with the intake records):
  - the archive (bytes, SHA-256, 32 files, `SHA256SUMS` 31/31), the 12 staged
    files byte-identical, the delivered text rebuilt (35 pages) and its 118
    labels compared with this file's;
  - every proof of Sections 28–33 read line by line (the steps rechecked by
    hand are listed in Section 25.3); no error found;
  - constants at 40 digits: `V_0`, `v_0` (closed form; one-dimensional
    formula to 40 digits; two-dimensional quadrature in `1/y, 1/z` to
    `10^{−14}`), `V_{1/4} = 0.600519279618463641…`, `(1 − 2α)V_α → c_*`,
    `M_α` and `Γ(α+1)ζ(α)` as integrals, `C_reg = 1`, the Gumbel
    characteristic function, the constants 2, 8, `2π⁴/9`, 1, `K_crit`, and
    Part I's `K` in Part III's form. Finding: the printed
    `v_0 = 0.308000244403717958…` is rounded; the truncation is
    `0.308000244403717957…` (dated note);
  - all 215,308 partitions of `n ≤ 40` enumerated by multiplicity vectors:
    all 41 rows and nine columns of the moments CSV agree; exact moments
    extended to `n = 300` by forbidden-value products (a range extension of
    the same identity): `Var_n D_0/n^{1/4}` = 0.2119, 0.2343, 0.2458, 0.2516 at
    `n` = 40, 100, 200, 300 and `Var_n D_1/n` = 0.751, 0.828, 0.872, 0.894,
    consistent with `v_0` and 1, not deciding them;
  - the covariance table (three rows, all ten digits) and the twelve sample
    variances (from the raw columns) recomputed;
  - geometric-law means at `t = 10^{−2} … 10^{−5}` against Part I's radial
    expansion, Part III's two-term means at `α = 1/2, 1` and Part II's
    five-term expansion: all residuals as required (table in the note at the
    end of Section 30);
  - the delivered `verify.py --skip-simulations` rerun on a copy (≈ 20 s):
    moments CSV byte-identical; `checks.json` differs only in the skipped
    simulation block, the versions and seven last-digit floats;
  - the repository at the pin (blob `77a379cfb`, the ledger
    `Combinatorics/Ramsey/gowers-proof-status.json` 113/7 then, 114/6 since
    `456b6e3ad`/`c05c2f73e`; the Keller README); A373271 and A373273 live.
- Not read by the write: Fristedt, Erdős–Lehner, the `math` repository and
  its family-132 manuscript.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`0064d11e6`), with
its own code, after fetching again A373271 (#15) and its b-file, A373273
(#14), A373272 and A373269. It covers Parts I and II as written; Part III
(the `03-fluct-` files, placed later) is not part of that write; its check
is the next section.

- **OEIS remarks (1.4, 12.4).** Revisions, dates, author, offsets, names,
  comments, the b-file credit and SHA-256, and the A373273 record (line for
  line equal to the shipped `.seq`) confirmed; all 200 b-file terms and the
  43 A373273 terms agree.
- **Exact tables.** Both statistics by brute force over all partitions for
  `n ≤ 50`, and by the identity `P(q) Σ_m w(m)(1 − Q_m(q))` with the check's
  own product code through `n = 2000` (Part I) and `n = 2500` (Part II); the
  `p(n)` columns; strict increase from `n = 1`.
- **Constants and tables.** The rational constants `−23/16`,
  `12365/82944`, `9607/20736`, `19/144`; Part I's `K` in both forms (printed
  digits a truncation); every entry of Part I's `T(n)` table and of Part II's
  Table 1; the residuals of the Guide; the two regularized integrals to 25
  digits by quadrature, and `∫_0^∞ y b''(2y) dy = −1/8`.
- **Numbering and merge.** Part I's 89 labels unchanged; Part II's 78 shifted
  by eleven sections, Table 1 unchanged; 7 labels added, 174 in all; 50 and
  44 references. The merged bibliography keeps every delivered detail; the
  counterpart correspondences named in Part II's three duplication notes
  hold display by display.
- **Transseries remarks (9.1, 21.1).** Re-derived against the volume: the
  Lambert core of Part I, the two-grid coefficients `c_{0,1} = −ℓ_1/B`,
  `c_{1,0} = 0`, `c_{0,2} = −ℓ_2/B`, the restriction of the volume's analytic
  reversion to `δ = 1` (`p0:rem:alpha-one`), the residual-to-root steps, and
  Part II's `log log x`, which keeps its template outside `p0:def:model`.
  One precision, in a dated note after Remark 9.1: `p0:thm:staircase`(1)
  needs `Y ≥ a(n_1)` and `Y > max_{n<n_1} a(n)`, which hold for all large `Y`
  (the early values the proof excludes are a different set).
- **Provenance and reruns.** Archive bytes, SHA-256, file counts, lines,
  delivered pages, manifest entries and the not-shipped sizes; the file list;
  both verifiers and symbolic checks rerun from the shipped files (four `cmp`
  silent, `PASS`), Part II's diagnostics differing only in the 15 sector
  residuals at about the tenth significant digit.
- The check read the proofs of both Parts as well and found no error.

The check is recorded in the Guide, after the collected non-claims.

## Independent check of the Part III write (7 October 2026)

An adversarial check of the Part III write (`b0ad11d15`), with its own code,
after fetching A373271 (#15) and A373273 (#14) again and extracting the
archive from `7b8ed30e7` afresh.

- **Provenance.** Archive bytes and SHA-256, 32 files, 2,225,214 bytes
  unpacked, `SHA256SUMS` 31/31, the 12 staged files byte-identical, 2,346
  lines and 99,736 bytes, 35 delivered pages, the title-page and PDF-author
  quotations, the pin times, blob `77a379cfb`, the side-branch tree, the
  not-shipped sizes and the file list (36 files) confirmed.
- **Numbering.** All 174 earlier labels unchanged; all 118 delivered labels
  shifted by 25 sections, figures unchanged; 7 added, 299 in all. The 127
  updated references (83 `\eqref`, 44 `\ref`) are those of the manuscript's
  Sections 1–9; its reference list has one more `\eqref` (Erdős–Lehner),
  also updated, and the title page's `\ref` is printed in the quotation of
  Section 25.1.
- **Constants.** `V_0`, `v_0` (the printed `0.308000244403717958…` is
  rounded; truncation `…957`, next digits `652`; the package's `checks.json`
  has the right digits), `V_{1/4}` (also by a second two-dimensional
  reduction, to `10^{−14}`), the `r`-integral, `(1 − 2α)V_α → c_*`, `M_α`,
  `Γ(α+1)ζ(α)`, `C_reg = 1`, the singular part, the mean constant
  `(3 − γ)/2` (Part II's `c`), `Z_1 = G − γ` in law and so the centering
  `(3 − 3γ)/2 = 0.634176502647700709…` (Part II's constant minus `γ`, no
  conflict), 2, 8, `2π⁴/9`, 1, `K_crit` and its Brownian form, Part I's `K`.
- **Tables.** Brute force over all partitions to `n = 45`; all 41 rows of the
  moments CSV; the check's own forbidden-pair products to `n = 300` reproduce
  the write's variances; the covariance table (36 and 71 bins), the kernel
  limit `0.275589612433705…` and the twelve sample variances; the geometric
  means of the Section 30 note (same digits). The delivered `verify.py
  --skip-simulations` rerun by the README recipe: CSV byte-identical, seven
  `moving_window` floats differ in the last digit.
- **Independent of the kernel.** Geometric-law variances from the exact one-
  and two-value absence products: `t^{1/2} Var_t D_0` = 0.348901 … 0.348890
  for `t = 10^{−2} … 10^{−4}` against `V_0 = 0.348809…`; `V_{1/4}`, the
  `α = 3/4`, `1`, `2` limits likewise; `(t/H) Var_t D_{1/2}` consistent with
  `c_*/2` plus an `O(1/H)` term. The gap between the exact `Var_n D_0/n^{1/4}`
  (0.2343, 0.2458, 0.2516 at `n` = 100, 200, 300) and `v_0` is the
  size-conditioning correction: `Var_t − Cov_t(D_0, N)²/Var_t N` at the
  saddle gives 0.2323, 0.2445, 0.2505, and that correction falls like
  `t_n^{1/2}` (24 % at `n = 100`, 0.78 % at `n = 10^8`); the same for `D_1`.
  Floating evidence, not proof (note after Corollary 26.2).
- **Precision.** The write's "leading scale and next term for every `α`"
  (Section 25.2, Part II's question note, this README) holds for
  `0 < α ≤ 1`; for `α > 1` Part III proves the leading term only. The check's
  geometric means at `α = 3/2` suggest a second term `M_{3/2} t^{−5/4}`
  with `M_α` continued; an observation, not a theorem (dated notes in
  Section 25.2 and after Part II's questions).
- **Correction.** The parent of the write is `2bac1ea07`, not `76eca179c`
  (an earlier merge); the ledger count 114/6 holds at both (dated note in
  Section 27.1).
- No claim of Part III was found wrong or unproved as stated.

The check is recorded at the end of Section 25.3.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remarks
9.1(a) and 21.1(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these sequences is formalized.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a239964-sizes-equal-max-multiplicity` (batch 111; kept apart at placement
because `D = M` is not an occupied-value functional and no source cites
another) and `a239950-maximal-schreier-supports` (batch 111). They share the
Boltzmann occupancy setting and the damping argument, not a result; no
reciprocal note is proposed.

**Part III's companion.** The archive of Part III also held an independent
note on sensitivity and block sensitivity, placed as
`Combinatorics/BooleanFunctions/Research/sensitivity-block-sensitivity`
(`5476940ed`); it shares no mathematics with this report. Part III's review
table surveys other repository threads (Gowers–Szemerédi, Keller maps, the
`math` families 159 and 132) as context only.

**Stale claims.** Before batch 111 no file of the repository named A373271 or
A373273. Part III, pinned at `1210e9d3a`, says this file "contains the
unweighted report" (true then; Part II was written three hours later) and
that the Gowers–Szemerédi ledger records 113 exact companions and seven open
statements (114 and six since the Lemma 16.10 repair); dated notes in Section
27 record both.

## Notation

The Guide's table puts the two Parts side by side: `a(n)`, `a_n`; `D`
(Part I's statistic, Part II's delta correction), `W` (Part II's statistic)
and Lambert's `W_{−1}`; the two `K` and the two `d`; `c`, `k`; `B` and the
Bose factor (`𝓑` in Part I, `B(z)` in Part II); `C`, `C_N`, `C_0`; `ν` and `N`
swapped between the Parts (`ν = n − 1/24` and `N(Y)` in Part I,
`N = n − 1/24` and `ν(Y)` in Part II); `ℓ`; `Φ` (a template for `log a(n)` in
Part I, for `a_n` in Part II) and `H_±`; `x`; `Z`; `L`; `E`; `G`, `F`; `T`;
`M`, `X`; `a = s + 1/2` and `β`. No symbol was renamed.

Part III keeps its own letters; Section 25.5 reads them against Parts I and
II. The main clashes: `D_α` (`D_0 = D`, `D_1 = W`); `τ_n = π/√(6n)` against
`τ = √(A/(n − 1/24))`; `t`, the exact saddle and the free parameter of the
geometric law `𝐐_t`; `g(u) = e^u/(e^u − 1)²` (Part I's `g` is the mean,
Part II's `F` is this function); `M_α` against the multiplicities `M_j`;
`W(θ)`, the window variance; `c_* = 1 − π/4`; `H_n`, `H`, `H(u)`, `H_k`;
`K_crit`, `𝒦` and an integer `K`; `A` (an error exponent), `A_J`, `B_J`,
`A_α(n)`, `B_α(n)`; `G` (Gumbel), `𝒢(θ)`; `E_j` (exponentials); `N` (the
total size); `λ_m`; `Z_α`, `Y_α`, `Z_m`; `ε = √t` (Parts I–II: `h`); `J`,
`L`, `R`, `R_t`; `T_f`; `S_{α,J}`, `C_{α,J}`; `P_S`, `p_{jm}`.

## Labels

Report 197's 89 labels (`eq:` 69, `sec:` 11, `thm:` 4, `lem:` 3, `prop:` 2) carry
`dmv:cnt:` and Report 198's 78 (`eq:` 59, `sec:` 13, `thm:` 3, `lem:` 1,
`prop:` 1, `tab:` 1) carry `dmv:sum:`; the 50 and 44 references to them
(36 and 38 `\eqref`, 14 and 6 `\ref`) were updated. The write added 7:
`dmv:sec:guide`, `dmv:cnt:part`, `dmv:sum:part`, `dmv:cnt:rem:oeis`,
`dmv:cnt:rem:transseries`, `dmv:sum:rem:oeis`, `dmv:sum:rem:transseries`.
The report had 174 labels after the first write. Builds of the two delivered
texts and of this one were compared: all 89 Part I labels keep their numbers,
and all 78 Part II labels keep theirs up to the shift of eleven sections
(Table 1 unchanged).

Part III (second write): the manuscript's 118 labels (`eq:` 89, `sec:` 9,
`lem:` 8, `thm:` 4, `cor:` 3, `prop:` 2, `fig:` 2, `subsec:` 1; prefixes as
delivered, all now under `dmv:fl:`) and its 127 references (83 `\eqref`, 44
`\ref`) were prefixed; 7 labels were added (`dmv:fl:part`,
`dmv:fl:sec:front`, `dmv:fl:sec:provenance`, `dmv:fl:sec:answers`,
`dmv:fl:sec:checks`, `dmv:fl:sec:nonclaims`, `dmv:fl:sec:notation`). The
report has 299 labels. Against builds of the committed text before this write
and of the delivered manuscript: all 174 earlier labels keep their numbers,
and all 118 Part III labels are the delivered numbers shifted by 25 sections
(Figures 1 and 2 unchanged).

## Files

```text
README.md                                          this guide (replaces Report 197's delivery README)
03-fluct-code-README.txt                           Part III: the delivered code/README.txt (verify.py, make_figures.py, outputs, quick replay)
article.tex                                        the merged report (Report197.tex, Report198.tex and Part III's manuscript; labels prefixed, [write] additions)
article.pdf                                        compiled report, 83 pages
code/03-fluct-verify.py                            Part III exact moments to n = 40, constants, moving-window products, seeded samples (delivered code/verify.py)
code/03-fluct-make_figures.py                      Part III figure generator (delivered code/make_figures.py; needs Matplotlib)
code/03-fluct-build.py                             package-level builder of the delivered partitions/ and sensitivity/ (delivered build.py; does not run here)
code/197-count-verify.py                           Part I exact checks: Q-product to 2000, positive DP to 400, Ferrers gaps to 45 (delivered verify.py)
code/197-count-symbolic_checks.py                  Part I Fraction identities (delivered symbolic_checks.py)
code/197-count-build.py                            Part I deterministic builder (delivered build.py)
code/197-count-guard_tests.py                      Part I guard and rebuild tests (delivered guard_tests.py)
code/198-sum-verify.py                             Part II exact checks: Q-product to 2500, positive DP to 450, Ferrers gaps to 43 (delivered verify.py)
code/198-sum-symbolic_checks.py                    Part II Fraction identities, 35 checks (delivered symbolic_checks.py)
code/198-sum-diagnostics.py                        Part II floating diagnostics (delivered diagnostics.py)
code/198-sum-build.py                              Part II deterministic builder (delivered build.py)
code/198-sum-guard_tests.py                        Part II guard and rebuild tests (delivered guard_tests.py)
data/03-fluct-exact_partition_moments.csv          Part III exact totals p(n), sums of D0, D0^2, D1, D1^2, D2, D2^2, D0*D1 for n = 0..40 (CRLF, kept by .gitattributes)
data/03-fluct-checks.json                          Part III recorded checks: exact, analytic (55 digits), moving window, simulation summaries
data/03-fluct-boltzmann_samples.csv                Part III 6,000 seeded finite-row samples at t = 1e-4, 1e-5, 1e-6 (CRLF, kept by .gitattributes)
data/03-fluct-boltzmann_histograms.json            Part III fixed-bin histograms of the samples
data/03-fluct-requirements.txt                     Part III mpmath 1.3.0, numpy 2.3.5, matplotlib 3.10.8 (delivered code/requirements.txt)
data/03-fluct-BUILD_ENVIRONMENT.json               package-level build environment of both manuscripts of the archive (delivered BUILD_ENVIRONMENT.json)
data/197-count-exact_A373271.txt                   n, a(n), p(n) for n = 0..2000 (delivered data/)
data/197-count-generated-exact_terms.txt           recorded terms (delivered generated/; byte-identical to the previous file)
data/197-count-generated-verification.json         recorded verification (delivered generated/)
data/197-count-generated-guard_results.json        recorded guard results (same)
data/197-count-generated-BUILD_INFO.json           recorded build parameters (same)
data/198-sum-exact_A373273.txt                     n, a_n, p(n) for n = 0..2500 (delivered data/)
data/198-sum-A373273.seq                           OEIS internal record of A373273, revision #14 (delivered data/)
data/198-sum-generated-exact_terms.txt             recorded terms (delivered generated/; byte-identical to exact_A373273.txt)
data/198-sum-generated-verification.json           recorded verification (delivered generated/)
data/198-sum-generated-diagnostics.json            recorded floating diagnostics (same)
data/198-sum-generated-guard_results.json          recorded guard results (same)
data/198-sum-generated-BUILD_INFO.json             recorded build parameters (same)
figures/03-fluct-variance_transition.pdf           Part III Figure 1 (delivered figures/)
figures/03-fluct-boltzmann_ecdfs.pdf               Part III Figure 2 (delivered figures/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Within Parts I and II, the exact table and
the recorded `exact_terms.txt` are byte-identical; both are shipped as
delivered records. The 12 `03-fluct-` files were confirmed byte-identical at
the Part III write.

**Not shipped**, recoverable from the arrival commit: `Report197.pdf` (18
pages, 388,482 bytes) and `Report198.pdf` (17 pages, 386,127 bytes); the
checksum manifests (Report 197: `MANIFEST.json` 1,962 bytes, 13 entries;
`SOURCE_MANIFEST.json` 1,098 bytes, 7 entries; Report 198: 2,379 bytes, 16
entries; 1,369 bytes, 9 entries), verified at the write; Report 198's
`Report198.tex` (44,640 bytes; it is Part II of `article.tex`) and its
delivered `README.txt` (12,013 bytes); and Report 197's `README.txt` (10,387
bytes), staged at placement as `README.md` and replaced by this guide (both
READMEs summarized below). From Part III's archive (recoverable from
`7b8ed30e7`): `partitions/article.tex` and `partitions/sections/*.tex` (99,736
bytes in all; they are Part III of `article.tex`), `partitions/article.pdf`
(35 pages, 628,861 bytes), `partitions/README.txt` (1,676 bytes), the
package `README.txt` (6,894 bytes) and `SHA256SUMS` (3,012 bytes, 31
entries, verified at the write); the `sensitivity/` manuscript belongs to
the separate report named above.

**Delivered text that names the delivery layout or files not shipped.** The
programs (under their delivered names, with `data/` beside them; the
builders and guard tests require the manifests, README and TeX of their
package), and Sections 10 and 22 of the article ("See its `README.txt`", "The
code archive contains the TeX source…", "The accompanying README gives exact
commands"). In Part III: Section 34.4's commands (`python3 code/verify.py`,
`code/make_figures.py`, `latexmk … article.tex`, `code/requirements.txt`,
`code/README.txt`; dated note there), `03-fluct-code-README.txt` (the same
paths, and `/tmp/partition-checks` as an example output directory), and
`code/03-fluct-build.py`, which builds the delivered `partitions/` and
`sensitivity/` directories and cannot run here.

## Retrieving the delivered packages

```sh
T=$(mktemp -d); cd "$T"
for r in 197 198; do
  git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report${r}_TeX_and_Reproducible_Code.zip > $r.zip
  mkdir $r && (cd $r && unzip -q ../$r.zip)
done
sha256sum 197.zip 198.zip
# 192aeca1a0b861c1394c06845b1c542aa0292b8623e69dde4bc038875d653adc  (793,611 bytes)
# 8d10255b48c353ec3f9d203348e91c5e9e78f47281a13f2238eacce24e871492  (909,536 bytes)
git -C /path/to/ProveIt show 7b8ed30e7:docs/incoming/ProveIt_Research_2026-10-07.zip > p3.zip
sha256sum p3.zip
# 49c8000eea95c5c7259e9c4a03347a92772e4c4dd65bf125d5f2a07b2b5b4c07  (1,527,416 bytes)
mkdir p3 && (cd p3 && unzip -q ../p3.zip && cd ProveIt_Research_2026-10-07 && sha256sum -c SHA256SUMS)
```

## Rerun the checks (on a scratch copy)

Python 3.9 or later, standard library only. Never run anything in the
repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a373271-distinct-multiplicity-values
B=$(mktemp -d)
for r in 197-count 198-sum; do
  mkdir -p "$B/$r/data"
  for f in "$R"/code/$r-*.py; do n=$(basename "$f"); cp "$f" "$B/$r/${n#$r-}"; done
done
cp "$R/data/197-count-exact_A373271.txt" "$B/197-count/data/exact_A373271.txt"
cp "$R/data/198-sum-exact_A373273.txt" "$B/198-sum/data/exact_A373273.txt"
cp "$R/data/198-sum-A373273.seq" "$B/198-sum/data/A373273.seq"
(cd "$B/197-count" && python -I -S -B verify.py --output "$B/v197.json" --terms-output "$B/t197.txt" && python -I -S -B symbolic_checks.py)
(cd "$B/198-sum" && python -I -S -B verify.py --output "$B/v198.json" --terms-output "$B/t198.txt" && python -I -S -B symbolic_checks.py && python -I -S -B diagnostics.py > "$B/d198.json")
cmp "$B/v197.json" "$R/data/197-count-generated-verification.json"
cmp "$B/t197.txt" "$R/data/197-count-generated-exact_terms.txt"
cmp "$B/v198.json" "$R/data/198-sum-generated-verification.json"
cmp "$B/t198.txt" "$R/data/198-sum-generated-exact_terms.txt"
diff "$B/d198.json" "$R/data/198-sum-generated-diagnostics.json"
```

At the write the four `cmp` were silent and both symbolic checks printed
`"status": "PASS"`; the `diff` showed only the sector Boltzmann residuals,
equal to about ten significant digits (and line endings on Windows). Use `py` where `python` is not on
the path. The builders and guard tests were not rerun by the write; take
their packages from the archives.

Part III's exact and analytic checks (mpmath and NumPy, versions in
`data/03-fluct-requirements.txt`; the simulations are skipped, and the
program writes only into the directory given):

```sh
B=$(mktemp -d); mkdir -p "$B/code"
cp "$R/code/03-fluct-verify.py" "$B/code/verify.py"
(cd "$B" && python -O code/verify.py --skip-simulations --output-dir "$B/out")
cmp "$B/out/exact_partition_moments.csv" "$R/data/03-fluct-exact_partition_moments.csv"
```

At the Part III write (NumPy 2.4.4, Python 3.14.4, ≈ 20 s) the `cmp` was
silent; `out/checks.json` differed from `data/03-fluct-checks.json` only in the
skipped simulation block, the software versions and seven `moving_window`
floats in the last digit. The full run (simulations) and `make_figures.py`
(Matplotlib) were not rerun; for them, copy the `03-fluct-` data files into
`$B/data/` under their delivered names.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, xcolor, enumitem, fancyhdr, hyperref,
longtable for the Guide and Section 25, and graphicx for Part III's two
figures); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cp -r figures "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (41
pages; rebuilt the same day after the independent check's notes, still 41
pages): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered texts also build without any, 18 and 17
pages). With Part III (three pdflatex passes, same day): 82 pages, with the
same result; Part III's delivered text builds to 35 pages. Rebuilt the same
day after the notes of the Part III check: 83 pages, with the same result,
every label number kept.

## From the delivery READMEs

Report 197's README (replaced by this guide) defined the statistic, said that
exact computations "check definitions, coefficient algebra, and
reproducibility; they do not replace the analytic proof" and that "No central
limit theorem, proved variance asymptotic, all-fixed-orders theorem,
effective onset/error constant, exact single-ceiling inverse, or exhaustive
worldwide novelty claim is made"; gave the commands; described the
Q-product algorithm, the positive DP through 400, the Ferrers-gap check
through 45 and the pentagonal check through 2000; said the 45 displayed OEIS
terms were compared and "No comparison with the linked OEIS b-file is
claimed"; and described the manifests, deterministic builds and guard tests.
Report 198's README (not shipped) did the same for the weighted sum (Q-product
through 2500, positive DP through 450, Ferrers gaps through 43, 35 exact
symbolic checks, floating diagnostics "never" supplying a remainder constant,
the pinned `A373273.seq` record) and stated that its infrastructure was
"adapted from the preceding Report197 reproducibility package" and that "No
A373271 theorem or coefficient is used as a mathematical premise."

Part III's package `README.txt` (not shipped) describes both manuscripts of
its archive, lists the partition results, says the sensitivity note is
"independent", gives the build and check commands, and proposes that "The
partition article is a continuation of Report 197" which "can be added as a
separate continuation, with a link from the earlier report" (it was added as
Part III, the repository's rule for an answer to a report's own questions);
it records the two pins and that "No repository files were modified or pushed
by the preparation of this package." Its `partitions/README.txt` (not
shipped) names the key results in the delivered numbering (Theorem 1.1,
Corollaries 1.2–1.4, Theorem 1.5, Theorem 8.1, Proposition 3.4: here 26.1,
26.2–26.4, 26.5, 33.1, 28.4) and says "The critical finite-size discrepancy
is deliberately retained." Its `code/README.txt` is shipped as
`03-fluct-code-README.txt`.

## Rights

Repository contents are MIT-0. The article and this README quote OEIS entries
A373271 and A373273, and `data/198-sum-A373273.seq` is the OEIS internal
record of A373273 (Olivier Gérard); OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that
content remains under that licence. No third-party PDF is shipped. Nothing
was submitted to the OEIS.

## Provenance

- Sources cited by the manuscripts: OEIS A373271, A373273, A373272;
  Ralaivaosaona, Ann. Comb. 16 (2012); Grabner–Knopfmacher–Wagner, CPC 23
  (2014); Corteel–Pittel–Savage–Wilf, RSA 14 (1999); Lugo, PhD thesis (2010);
  Archibald et al., AJC 66 (2016); Fill–Janson–Ward, EJC 19 (2012). Nothing
  added by the write. Part III adds Fristedt, Trans. AMS 337 (1993);
  Erdős–Lehner, Duke Math. J. 8 (1941); the ProveIt and `math` snapshots and
  `math` family 132.
- Batch 111 of `docs/incoming`, bundle Reports 197 and 198; arrival
  `60f54ea06`, placement `d451ef3d8`, written 7 October 2026.
- Part III: non-Gowers intake NG1, manuscript 01; arrival `7b8ed30e7`,
  placement `9a10a617f` (recorded in the batch notes by its side-branch copy
  `119d8d35d`), written 7 October 2026.
