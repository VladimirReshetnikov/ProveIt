# Gamma Constants and Scaling Limits for Rounding Extinction

**Cloitre's power-rounding conjecture (OEIS A082528) for every real `m > 0`,
smooth-weight universality, and the limits of regular variation; Part II:
quantitative thresholds, inverses and global mass profiles; Part III:
microscopic schedules and averaged ceiling laws**

A research report in three Parts, built from three manuscripts. Part I is
dated 3 October 2026; Parts II and III were added on 7 October 2026
(batch 110). Parts I and III have the author line, and PDF author field,
"Research report prepared for Vladimir Reshetnikov with OpenAI" (Part III:
"Research article …"): the packages name OpenAI as the tool that prepared
them and no human author. Part II's source, Report 188, names no author; its
PDF author field reads "Research report".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 05 | `Rounding_Extinction_OEIS.zip` (wrapper directory `Rounding_Extinction/`, 1,632,826 bytes), arrival commit `317c1ce2e`; main file `article.tex` with its `\input` files `body.tex`, `extensions.tex`, `computation.tex`, `questions.tex`, `bibliography.tex` | `ce37e13f4` (`ce37e13f4aa16819c87c3ccc611362d15758f2ac`, quoted in Section 2.3 and in the bibliography entry for ProveIt) | `713149ded` | Part I (Sections 1–10, Appendices A–B) |
| 02 | batch 110, bundle Report 188 | `Sequential_Power_Rounding_Gamma_Constants_and_Inverses_Source.zip` (20 files, 564,257 bytes), arrival commit `60f54ea06` (session bundle of Reports 1–243); main file `Report188.tex` (709 lines, dated 4 October 2026) | none (names no ProveIt commit and does not cite this report) | `8622ca7e5` | Part II (Sections 11–23), `rates.tex` |
| 03 | batch 110 (held from batch 114) | `Periodic_Rounding_Extinction.zip` (23 files in `periodic_rounding_extinction/`, 1,681,098 bytes), arrival commit `e4d5dcf9e`; main file `periodic_rounding_extinction.tex` (1,901 lines, dated 5 October 2026) | `52d8ca404` (`52d8ca404b076c38eb7c513569592ebd8c479115`, quoted in its Section 25.2 and in `03-schedules-SOURCE_AUDIT.txt`) | `8622ca7e5` | Part III (Sections 24–39), `schedules.tex` |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. Part I says its proofs
were reviewed twice internally, which "are not a substitute for peer review
or formal verification"; Part III's manuscript "has not been peer reviewed or
formally verified"; Report 188 says its finite checks "do not constitute a
formal proof of the asymptotic theorems". Exact integer computations check
the finite definitions on recorded ranges; Gamma values, plots and decimal
displays are numerical diagnostics, not interval bounds, except the exact
rational certificates stored as fractions.

## What it proves

Fix a real `m > 0`. From an integer `n ≥ 0` set `x_1 = n` and
`x_k = k^m ⌊x_{k−1}/k^m⌋` for `k ≥ 2`; `τ_m(n)` is the first `k` with
`x_k = 0` (`τ_m(0) = 1`). For `m = 1, 2, 3` these are OEIS A073047, A082527 and
A082528. `T_m(K)` is the least initial value that survives through stage `K`.

### Part I (Sections 1–10, Appendices A–B)

- **Theorem 1.1 (power-rounding extinction).**
  `τ_m(n) ~ (c_m n)^(1/(m+1))` and `T_m(K) ~ L_m K^(m+1)`, with
  `c_m = m Γ(m/(m+1))^(m+1)` and `L_m = 1/c_m`. This proves the real-`m`
  conjecture recorded by Benoit Cloitre in A082528 and identifies the
  numerically conjectured constants `c_2 = 2Γ(2/3)³ = 4.965917162430455473…`
  (A082527) and `c_3 = 3Γ(3/4)⁴ = 6.764822981008760234…` (A082528).
- **Theorem 1.2 (full extinction trajectory).** With `J = τ_m(n)`, the
  rescaled path `x_{⌊Jt⌋}/n` converges uniformly on `[0,1]` to
  `F_m(t) = c_m t^m y_m(t)`, where `y_m` is the explicit piecewise-linear
  profile with slopes `−1, −2, −3, …` between the crossing times
  `t_j = ∏_{r ≤ j}(1 − 1/((m+1)r)) = Γ(j+a)/(Γ(a)Γ(j+1))`, `a = m/(m+1)`.
- **Theorem 1.3 (smooth-weight universality).** For weights `w_1 = 1`,
  `w_k > 0` with `k(w_k/w_{k−1} − 1) → m`: `T_w(K) ~ L_m K w_K`,
  `L_m τ_w(n) w_{τ_w(n)} ~ n`, and the same limiting trajectory `F_m`.
- Section 3: the backward quotient array (Definition 3.1), survival duality
  (Lemma 3.2), the exact inverse `τ_m(n) = 1 + max{K : T_m(K) ≤ n}`
  (Corollary 3.3), and the two rounding-error estimates; Section 4:
  compactness (Lemma 4.1), passage through the ceiling discontinuities
  (Lemma 4.2), the explicit profile and its uniqueness (Proposition 4.3);
  Section 5: the beta-integral asymptotic of `t_j` and the small-time
  weighted limit (Lemma 5.1).
- **Proposition 6.1:** rational product certificates bracketing `c_m`, with
  upper/lower ratio exactly `1 + m/((m+1)j)`; **Corollary 6.2:** the limiting
  distribution of rounding losses (density `c_m t^m [C(my_m/t) − my_m/t]`);
  **Proposition 6.3:** `c_m` strictly increasing, `c_m → 1` as `m ↓ 0`,
  `log c_m = log m + γ + Σ_{r≥2} ζ(r)/(r(m+1)^(r−1))`, and
  `c_m = e^γ m (1 + π²/(12(m+1)) + O(m^(−2)))`.
- Lemma 7.1 (regular variation from the ratio hypothesis), Corollary 7.2
  (logarithmic modifiers `w_k = A k^m (log k)^b`), Corollary 7.3 (regular
  variation of the stopping index).
- **Proposition 8.1 (repeating each modulus):** block weights
  `w_k = ⌈k/r⌉^m` are regularly varying of index `m` but give
  `T_w(K)/(K w_K) → L_m/r`, so regular variation alone does not determine the
  constant.
- Section 9: exact integer and rational-exponent algorithms, the recorded
  checks, Tables 1–2 and Figures 1–3; Section 10: nine research questions;
  Appendix A: proof dependencies and source audit; Appendix B: a **draft** of
  OEIS update text (see below).

### Part II (Sections 11–23; Report 188, in its own letters `p = m`, `B_p(k) = T_m(k)`, `A_p(n) = τ_m(n)`, `K_p = L_m`)

- **Theorem 12.1:** `B_p(k) = K_p k^(p+1) + O_p(k^((p+1)²/(p+2)))` and
  `A_p(n) = (c_p n)^(1/(p+1)) + O_p(n^(1/((p+1)(p+2))))`, with implied constants
  uniform for `p` in a compact subset of `(0,∞)`. The leading terms are
  Part I's Theorem 1.1 by a **second route** (a monotone integral coordinate
  `I_p` and dyadic telescoping instead of compactness); the remainders are
  new and **answer Part I's Research question 1** (`δ_m = (m+1)/(m+2)`,
  uniform on compact sets). At `p = 1` the remainder is the classical
  `O(k^(4/3))`, not improved.
- Lemma 14.1 (drift sandwich), Lemma 15.1 and Theorem 15.2 (uniform ratio
  bounds; `|I_p(u_J) − log(k/J)| ≤ E_p/J` without a logarithmic loss);
  Proposition 16.1 and Lemma 16.2 (Gamma products and two-sided Gamma
  bounds); Proposition 16.3 (`0 ≤ K_p − H_p(t) ≤ t^(p+1)/(p+1)`).
- **Theorem 17.1:** an explicit enclosure of `B_p(k)` at every pair
  `1 ≤ J ≤ k`, and finite inverse tests.
- **Theorem 18.1:** the minimal reverse path follows the profile `H_p`
  uniformly with error `O_p(k^(−(p+1)/(p+2)))`, and `O(1/k)` on `[εk, k]`.
- **Theorem 19.1:** thresholds `B_p(k,h)` for a terminal quotient `h ≥ 1`:
  `k^(p+1) Φ_p(h/k) + O(k^((p+1)²/(p+2)))` uniformly in `h ≤ Vk`, the inverse
  curve `Φ_p^(−1)` in closed form on each cell, the retention limit (19.8),
  and the `h = 0` boundary discontinuity.
- Section 21: the series for `log(c_p/p)`, one more term at `p → ∞`, and
  `c_p = 1 + p(log(1/p) + 1 − γ) + O(p² log² p)` at `p ↓ 0`.
- The write's identifications (Remarks 16.4 and 19.2, with proofs):
  Report 188's products `P_r` are Part I's crossing times `t_r`, its
  `t U_p(t)` is `y_m(t)`, its `H_p` is `f_m`, Proposition 16.3 is the
  integral of Part I's (5.4) at every `t`, and the retention limit follows
  from Part I's Theorems 1.1 and 1.2.

### Part III (Sections 24–39; the manuscript *Microscopic Schedules in Rounding Extinction*)

For nondecreasing weights with `w_1 = 1`, scaled increments
`β_k = k(w_k/w_{k−1} − 1) ∈ [0, B]` and activity flags
`σ_k = 1{w_k > w_{k−1}}` whose joint empirical law converges to `μ` with mean
slope `m > 0`:

- **Theorem 27.2 (averaged extinction law):** the backward profile, the
  constant `L(μ) = lim z t(z)^(m+1)` with `t(z) = exp(−∫_0^z du/(u + D(u)))`
  and the averaged drift `D(z) = ∫ σ C(βz) dμ` (ceiling before averaging),
  `T_w(K) ~ L K w_K`, `n ~ L τ_w(n) w_{τ_w(n)}`, the forward trajectory,
  rational certificates `(z + η/(m+1)) t^(m+1) ≤ L ≤ (z + ρ/(m+1)) t^(m+1)`,
  and `η/(m+1) < L < ρ/(m+1)`. The law `δ_(m,1)` gives Part I's Theorem 1.3
  for nondecreasing weights (Remark 24.1).
- **Theorem 30.1:** a finite Gamma product for commensurable slopes;
  two unequal phases give `L = 0.3318976736…`, not `1/π`;
  **Corollary 30.2:** the activation family, with Part I's block constant
  `L_m/r` at `a = 0`.
- **Theorems 31.1–31.2, Proposition 31.3, Theorem 32.1:** for
  `w_{2j−1} = j`, `w_{2j} = j + ε/j` the constant jumps from `1/(2π)` at
  `ε = 0` to `π/8` for every `0 < ε < 1`; perturbations smaller than every
  inverse power of the index give every constant in `[1/(2π), π/8]`; a
  schedule with periodic limiting slopes has no limiting constant.
- **Theorem 33.1:** the loss measure marked by the increment state; in the
  jump example a fraction `2/π` of the mass is lost at steps whose weight
  increments tend to zero. **Theorem 34.1, Corollary 34.2:** continuity in the
  augmented law; bounded changes on a set of density zero change nothing.
- **Theorem 35.2:** for fixed `m` the constants are exactly
  `(0, 1/(m+1))`, realized by finite types, also with `w_K ~ K^m` (real
  weights; the increment bound may depend on the constant).
  **Theorem 35.4:** a finite Möbius inversion recovers `μ` from `D`.
- It **answers Part I's Research question 4** (microscopic schedules) for
  this class and the **bounded form of Research question 5** (sparse
  exceptions); outside the class the questions stay open, re-scoped as
  Part III's Research questions 14, 15 and 17.

(Section and theorem numbers are those of the committed PDF.)

## What is not claimed

- **The case `m = 1` is classical and credited, not claimed:** `c_1 = π`,
  `T_1(K) ~ K²/π` (A002491, the Tchoukaillon or Mancala sieve) and
  `τ_1(n) ~ √(πn)` are due to Erdős and Jabotinsky (1958), who also proved
  `T_1(K) = K²/π + O(K^(4/3))`; the increment-regime method is theirs (Brown's
  and Lehéricy's related work is cited). Part I's new claims are the case
  `m ≠ 1`, the square and cube constants, and the extensions; Part II's
  remainder at `m = 1` is the classical one.
- **Part II's leading law is not new relative to Part I.** Report 188 was
  written without Part I; its sentences "identifies the constant in the
  all-real-power conjecture" and "Targeted source checks found no directly
  matching square- or cube-power theorem" are stale relative to this
  repository, and dated notes in Sections 11 and 20 say so. Its two
  diagnostic decimals `c_2 ≈ 4.965917162430456` and `c_3 ≈ 6.764822981008765`
  are wrong in the last digit (Remark 12.2 gives
  `4.96591716243045547322…` and `6.76482298100876023357…`); nothing uses them.
- No bounded error: `τ_1(n) = √(πn) + O(1)`, recorded as presumptive in
  A073047, is **not** proved, in any Part. Part I's compactness argument gives
  no rate; Part II's rates concern exact powers only and are not claimed
  sharp; no rate is proved for the forward trajectories, the loss measures
  or any schedule of Part III. The Broline–Loeb sharpening is not used,
  because of Knuth's 2021 criticism recorded in A002491.
- All limits are for fixed `m`; nothing is uniform in a moving `m = m(n)`
  (Part II: uniform on compact `m`-sets only).
- Part I's Theorem 1.3 needs the local ratio hypothesis; Proposition 8.1
  shows that regular variation alone is not enough. Part III needs
  nondecreasing weights, uniformly bounded scaled increments and a convergent
  augmented law; its spectrum theorem is for real weights, with dormant
  phases and a bound depending on the constant, not for integer weights or
  strictly increasing schedules; its recovery theorem is for exact data.
- The exact-arithmetic programs handle positive rational `m` (and rational
  schedule data) only; the theorems are broader than the code. The exact
  checks cover only the recorded finite ranges; the rational certificates of
  record are the exact fractions in `data/constant_certificates.json` and
  `data/03-schedules-certificates.json`.
- Priority rests on targeted, not exhaustive, searches in all three sources.
  The intake confirmed the absence of any other repository treatment, but did
  not search the external literature for earlier theorems.
- **Appendix B is a draft OEIS update, marked "not posted" in the article,
  and it stays so.** Nothing was submitted to OEIS by any package author
  (Part I's `VERIFICATION_NOTES.txt`: "No OEIS updates or repository
  modifications have been submitted"; Part III's source audit: "no OEIS entry
  was submitted or edited") or by the intake. On 7 October 2026 A082528 still
  records the general-`m` law as a conjecture. Any submission is a human
  editor's decision after review.

## Checks made at intake

On 3 October 2026 the intake read the OEIS entries on `oeis.org` and
confirmed Part I's statements about them: A082528 records Cloitre's
conjecture for real `m > 0` with the constant 6.76…; A082527 records 4.96…,
and its `n = 10` example prints the intermediate value 2 where
`4⌊10/4⌋ = 8` is meant (the stopping index 3 is right), the slip Section 2.1
reports; and A002491 carries Knuth's 2021 comment on the accumulating error
terms of Broline and Loeb. An independent integer implementation reproduced
`T_1(1..10) = 1, 2, 4, 6, 10, 12, 18, 22, 30, 34` (A002491), all 79/105/105
fixture terms of A073047/A082527/A082528, and
`c_m T_m(3000)/3000^(m+1) = 0.999998, 1.00048, 1.00052` for `m = 1, 2, 3`.

For batch 110 (6–7 October 2026): an independent backward recursion
reproduced Report 188's first ten thresholds for `p = 2, 3`, its table
values `B_2(1000) = 201388916`, `B_2(10^4) = 201457639236`,
`B_3(1000) = 148522784144`, `B_3(10^4) = 1478758856906056`, and bounded
normalized remainders `(B − K k^s)/k^(s²/(s+1))` between 0.003 and 0.18 for
`p = 1, 2, 3`; Part III's exact thresholds give `T/(K w_K) = 0.1591535`
(`ε = 0`) and `0.3927036` (`ε = 10^−4`) at `K = 10^5`, against `1/(2π)` and
`π/8`; the two-phase constant lies in an independently computed certificate
`[0.33185619, 0.33193915]` at `z = 2000`. The write evaluated `c_2`, `c_3`,
the two- and three-phase Gamma products and the expansion (35.8) to forty
digits, checked the small- and large-`p` expansions of Section 21
numerically, confirmed the five Git blob identities of
`03-schedules-SOURCE_AUDIT.txt` at the pin and at HEAD, and read the live
A082528 and A002491 entries (7 October 2026). Report 188's quoted OEIS
revision numbers were not re-checked. The delivered programs passed on
scratch copies (see "Rerun the checks").

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
no formal development in ProveIt treats the subject, and the report's place in
the collection confers no formal status. No Part uses a repository theorem
outside this report.

**Within the report.** Part II re-proves Part I's leading law and answers its
Research question 1; Part III answers its Research question 4 for a large
class and question 5 in bounded form, and contains its Theorem 1.3 for
nondecreasing weights. The three Parts meet in one object: Part II's
coordinate `I_p` is Part III's integral `H` for the one-type law `δ_(p,1)`,
and Part III's certificate for that law is Part II's Proposition 16.3 and, at
the crossing times, Part I's bracket (6.1) (Remarks 16.4 and 24.1). Dated
notes in Sections 1, 2, 5, 6, 8 and 10 of Part I point to the later Parts.

**Neighbouring reports.** None. A search of the whole tracked tree at
placement (batch 85: all reports; the `Oeis`, number-theory and combinatorics
projects; the Lean and Rocq developments) found no treatment of A073047,
A082527, A082528, A002491, Tchoukaillon, Mancala, Jabotinsky or Broline, as
Part I's own bounded search at the pin had found; batch 110 brought its two
continuations here as Parts II and III. Its batch-85 sibling on OEIS A306631
(`Analysis/Transseries/docs/series-and-transseries/Partition_Function_Exact_Inversion_OEIS_A306631/`)
also speaks of "rounding", but of an inverse of the partition function:
unrelated mathematics, no shared notation.

**Stale claims.** Part I's repository statements (Section 2.3: "Exact
searches … returned no matching treatment", the 59-entry
`oeis-sequence-asymptotics` and 58-entry `series-and-transseries` directories)
are true at its pin and stay as dated provenance. Report 188's novelty
wording is stale relative to Part I (above). Part III's statements about the
repository are true at its pin and at HEAD.

## Notation

Each Part keeps its source's letters; no symbol was renamed.

- Part I reuses some letters with local meanings (`y_K` vs `y_m`; `q_k^(K)`,
  `Q_k`, and `q` as the denominator of `m = p/q`; `a = m/(m+1)` vs the
  increments `a_k`; `b_k` vs `b`; `t` vs the crossing times `t_j`; the
  positive ceiling `C(u)` vs the constant `c_m`; `r` as block length and as an
  index; `δ`, `δ_u`, `δ_m`; `z`, `ρ_m`, `J`). A table in the first `[write]`
  note (end of Section 2) fixes each one, with the tempting false readings.
- Part II writes `p` for Part I's `m`, indexes stages by `j` up to a terminal
  level `k` (Part I: `k` up to `K`), and uses `a = 1/(p+1)` (Part I's `1 − a`),
  `K_p` (Part I's `L_m`), `β` (a cutoff exponent), `Q_p`, `E_p`, `H_p`, `U_p`,
  `A`, `B` with other meanings than elsewhere. Table 4 (Section 11.3) lists
  every such letter with its Part I counterpart and false readings.
- Part III shares Part I's `w_k`, `x_k`, `τ_w`, `T_w`, `q_k^(K)`, `b_k`, `C`;
  its `z(t)` is `y(t)/t`, where Part I's is `m y(t)/t`; its `β_k`, `μ`, `ρ`,
  `E(z)`, `H(z)`, `t(z)`, `a`, `s`, `p`, `h`, `A`, `B` collide with Parts I
  and II. Table 6 (Section 24.3) lists them.

## Labels

Part I's labels carry the prefix `rex:` (99 labels from batch 85, all kept
and none renumbered, checked against the `.aux` of a build of the committed
text). Batch 110 added `rex:part:one` and the question labels `rex:q:fluct`,
`rex:q:sparse`, `rex:q:moving`, `rex:q:trajectory` to Part I (no existing
label changed), and Parts II and III carry the prefixes `rex:qt:` (103
labels: Report 188's 88, prefixed before anything cited them, and 15 of the
write) and `rex:sch:` (139: the manuscript's 119 and 20 of the write). The
report has 346 labels. `article.tex` and `bibliography.tex` define none.

The writing steps also:

- batch 85: added three dated `[write]` notes to Part I, the `writenote`
  environment and six `\crefalias` hooks (MiKTeX's current kernel otherwise
  prints every environment sharing the theorem counter as "theorem"), and set
  the two `--` of `python reproduce.py --exact-only --out replay_exact` in
  Section 9.6 as `-{}-` so that they print as hyphens;
- batch 110: added the editorial note after the abstract, the `\part` line
  before Section 1, sixteen dated notes in Part I (Sections 1, 2, 5, 6, 8 and
  10), the Part II and III macros (`\OO`, `\eps`, `\dd`, `\ind`, `\weak`,
  `\supp`) and the `placeins` package to the preamble, the `averaging`
  reference to `bibliography.tex`, and the two `\input` lines for `rates.tex`
  and `schedules.tex` before Appendix A. In Parts II and III it mapped the
  sources' citation keys to this bibliography (Erdős–Jabotinsky's two papers
  are one entry; Report 188's `mse` is `lehericy`; Part III's two citations of
  this report became a reference to Part I), prefixed the figure paths, gave
  Part III's notation table a caption, set one command line of Part III in a
  smaller font, and printed the manuscripts' abstracts and scope paragraphs
  as quotations in Sections 11.1 and 24.1. Part III's two appendices are its
  Sections 38–39.

No statement, proof or number of any manuscript was changed; the write's
corrections are dated notes and `[write]` remarks.

## Files

```text
README.md                         this guide
article.tex                       preamble, title, abstract, editorial note (delivered main file of Part I)
body.tex                          Part I, Sections 1-5, \input by article.tex
extensions.tex                    Part I, Sections 6-8, \input by body.tex
computation.tex                   Part I, Section 9, \input by body.tex
questions.tex                     Part I, Section 10 and Appendices A-B; \inputs rates.tex and schedules.tex before Appendix A
rates.tex                         Part II (Report 188), Sections 11-23, written by the batch-110 write
schedules.tex                     Part III (Periodic_Rounding_Extinction), Sections 24-39, written by the batch-110 write
bibliography.tex                  the twelve references, \input by body.tex
article.pdf                       compiled report, 80 pages
VERIFICATION_NOTES.txt            Part I: the package's review and build notes (as delivered)
02-rates-DATA_SOURCES.md          Part II: sources and attribution (delivered DATA_SOURCES.md)
02-rates-README_REPRODUCIBILITY.md Part II: reproduction and packaging (delivered README_REPRODUCIBILITY.md)
02-rates-code-README.md           Part II: the exact replay code (delivered code/README.md)
02-rates-data-README.md           Part II: the OEIS fixtures (delivered data/README.md)
03-schedules-SOURCE_AUDIT.txt     Part III: source audit with the pin and five blob ids (delivered SOURCE_AUDIT.txt)
03-schedules-VERIFICATION_NOTES.txt Part III: scope of the finite checks (delivered VERIFICATION_NOTES.txt)
code/reproduce.py                 Part I: all exact checks, tables and figures (delivered at the package root)
code/02-rates-check_exact.py      Part II: mandatory exact checker (delivered code/check_exact.py)
code/02-rates-exact_rounding.py   Part II: exact rational-power maps, imported by the checker (delivered code/exact_rounding.py)
code/02-rates-diagnose_float.py   Part II: optional floating diagnostics (delivered code/diagnose_float.py)
code/02-rates-reproduce.py        Part II: replay in normal and -O modes (delivered reproduce.py)
code/02-rates-test_build.py       Part II: adversarial package tests (delivered test_build.py)
code/02-rates-build.py            Part II: offline release builder (delivered build.py)
code/02-rates-verify_manifest.py  Part II: release-manifest verifier (delivered verify_manifest.py)
code/03-schedules-verify.py       Part III: exact thresholds, certificates, diagnostics, figures (delivered code/verify.py)
data/requirements.txt             Part I: mpmath==1.3.0, matplotlib==3.10.8 (delivered at the package root)
data/verification.json            Part I: recorded run (delivered at the package root)
data/oeis_prefixes.json           Part I: OEIS fixture terms, A073047/A082527/A082528 (third-party, CC BY-SA 4.0)
data/gamma_constants.json         Part I: c_m for m = 1/2, 1, 2, 3, 5 at 60 digits (numerical)
data/threshold_table.csv          Part I: exact T_m(K), m = 1/2, 1, 2, 3, 5, K = 10 ... 100000 (25 rows; CRLF)
data/threshold_table.tex          Part I: Table 1 (K <= 10000), \input by computation.tex
data/threshold_convergence.csv    Part I: exact thresholds behind Figure 1 (1842 rows; CRLF)
data/constant_certificates.json   Part I: exact rational products and endpoints (the certificates of record)
data/constant_intervals.csv       Part I: numerical display of the intervals (CRLF)
data/constant_intervals.tex       Part I: Table 2 (j = 1000, outward rounding), \input by computation.tex
data/backward_profiles.csv        Part I: exact backward q_k, m = 3, K = 20, 100, 1000 (CRLF)
data/limiting_profile.csv         Part I: breakpoints of y_3 on [0.12, 1] (CRLF)
data/forward_profiles.csv         Part I: exact forward x_k, m = 3, n = 10^3, 10^6, 10^9 (CRLF)
data/limiting_forward_profile.csv Part I: F_3 on a grid of [0, 1] (numerical; CRLF)
data/02-rates-oeis_fixtures.json  Part II: 342 OEIS terms of A002491/A073047/A082527/A082528 (third-party, CC BY-SA 4.0)
data/02-rates-generated-exact_checks.json   Part II: recorded output of the exact checker
data/02-rates-generated-verification.json   Part II: recorded replay summary
data/02-rates-generated-BUILD_INFO.json     Part II: recorded build metadata
data/02-rates-generated-build_guards.json   Part II: recorded build guards
data/03-schedules-thresholds.csv            Part III: 310 exact thresholds, ten models (311 lines; CRLF)
data/03-schedules-profile_samples.csv       Part III: exact backward quotients behind Figure 7 (CRLF)
data/03-schedules-limiting_profiles.csv     Part III: limiting profiles on grids (numerical; CRLF)
data/03-schedules-certificate_bounds.csv    Part III: rounded displays of the certificate endpoints (22 rows; CRLF)
data/03-schedules-certificates.json         Part III: exact rational certificates (the certificates of record)
data/03-schedules-gamma_products.json       Part III: exact Gamma arguments and numerical constants
data/03-schedules-verification.json         Part III: recorded summary of the finite checks
data/03-schedules-run_log.txt               Part III: console output of the recorded run
figures/normalized_thresholds.png Part I: Figure 1
figures/backward_profiles.png     Part I: Figure 2
figures/forward_paths.png         Part I: Figure 3
figures/03-schedules-constant_discontinuity.pdf  Part III: Figure 4 (PNG preview beside it)
figures/03-schedules-weak_phase_density.pdf      Part III: Figure 5 (PNG preview beside it)
figures/03-schedules-normalized_thresholds.pdf   Part III: Figure 6 (PNG preview beside it)
figures/03-schedules-drift_and_profiles.pdf      Part III: Figure 7 (PNG preview beside it)
```

Every file except `README.md`, `article.tex`, `body.tex`, `extensions.tex`,
`computation.tex`, `questions.tex`, `bibliography.tex`, `rates.tex`,
`schedules.tex` and `article.pdf` is byte-identical to its delivery. Part I:
placement moved `reproduce.py` to `code/` and `requirements.txt` and
`verification.json` to `data/`; not shipped is the delivered 25-page PDF
(941,186 bytes) and `README.txt`. Parts II and III: the delivered paths map to
the shipped ones as listed above; not shipped are the manuscripts
(`Report188.tex`, `periodic_rounding_extinction.tex`, whose text is Parts II and
III), their PDFs (17 and 29 pages), the delivered `README.md` and `README.txt`,
and the checksum manifests `SHA256SUMS.json` (19 entries) and `SHA256SUMS.txt`
(22 entries), all verified at intake with full coverage. Everything not
shipped survives in the arrival commits:

```sh
git show 317c1ce2e:docs/incoming/Rounding_Extinction_OEIS.zip > <scratch>/Rounding_Extinction_OEIS.zip
git show 60f54ea06:docs/incoming/Sequential_Power_Rounding_Gamma_Constants_and_Inverses_Source.zip > <scratch>/r188.zip
git show e4d5dcf9e:docs/incoming/Periodic_Rounding_Extinction.zip > <scratch>/Periodic_Rounding_Extinction.zip
```

**Third-party data.** `data/oeis_prefixes.json` and
`data/02-rates-oeis_fixtures.json` hold initial terms of OEIS sequences
(A073047, A082527, A082528; and A002491 in the second), copied from The On-Line
Encyclopedia of Integer Sequences (https://oeis.org; each record gives its
source and retrieval date). OEIS content is published by The OEIS Foundation
Inc. under the Creative Commons Attribution-ShareAlike 4.0 licence
(CC BY-SA 4.0); these files are third-party data under that licence, **not**
MIT-0 like the rest of the repository. The sequence definitions and the
conjectures are due to Benoit Cloitre (A002491: N. J. A. Sloane), as
attributed in the entries; `02-rates-data-README.md` gives Report 188's
attribution text. The programs read the files and never contact OEIS.

Delivered text that names the delivery layout or a file not shipped:
`code/reproduce.py` (sets `ROOT` to its own directory, reads
`ROOT/data/oeis_prefixes.json`, and defaults `--out` to `ROOT`); Section 9.6
of the article (a dated note there says so); `data/verification.json`
(figure paths relative to the package root); `VERIFICATION_NOTES.txt` ("Final
PDF: 25 A4 pages …"); Report 188's programs, which import each other by their
delivered names (`check_exact.py` imports `exact_rounding`, `reproduce.py`
imports `verify_manifest` and `build`) and check the closed delivered
inventory, including `Report188.tex` and `SHA256SUMS.json`; the four
`02-rates-*.md` files (delivered paths such as `code/check_exact.py`,
`data/oeis_fixtures.json`, `Report188.tex`, `README.md`); Section 22 of the
article ("The top-level `README.md`"; a dated note there says so);
`code/03-schedules-verify.py` (writes `data/` and `figures/` with delivered
names under `--output`, by default the report directory itself);
`03-schedules-VERIFICATION_NOTES.txt` and `03-schedules-SOURCE_AUDIT.txt`
(`data/…`, `figures/…`, `code/verify.py`, `README.txt`, a 29-page PDF); and
Section 36 of the
article (a dated note there says so).

**Byte-level notes.** Part I's seven CSV files and Part III's four CSV files
are CRLF throughout (Python's `csv` module); eleven lines
`docs/reports/…/a082528-rounding-extinction/data/<name>.csv -text` in
`SetTheory/Cardinals/.gitattributes` keep their bytes. The programs write
JSON and `.tex` files in text mode, so on Windows a rerun emits them with
CRLF where the shipped ones are LF; compare after stripping `\r`.

## Rerun the checks (on a scratch copy)

Never run the programs in place: Part I's `code/reproduce.py` cannot find its
fixtures from `code/` and overwrites the files beside it without `--out`, and
Part III's `code/03-schedules-verify.py` writes into the report directory
without `--output`. Rebuild each delivered layout on a copy (Git Bash, from
this directory).

**Part I.**

```sh
T=$(mktemp -d); X="$T/Rounding_Extinction"
mkdir -p "$X/data" "$X/figures"
cp code/reproduce.py data/requirements.txt data/verification.json "$X/"
for f in data/*; do case ${f#data/} in
  requirements.txt|verification.json|02-rates-*|03-schedules-*) ;; *) cp "$f" "$X/data/";; esac; done
cp figures/backward_profiles.png figures/forward_paths.png figures/normalized_thresholds.png "$X/figures/"
cd "$X"
py reproduce.py --exact-only --out "$T/replay_exact"     # standard library only
py reproduce.py --threshold 1000 --m 2/3                # T_{2/3}(1000) = 39828
py reproduce.py --stop 12345 --m 3/2                    # tau_{3/2}(12345) = 75
uv run --no-project --with mpmath==1.3.0 --with matplotlib==3.10.8 \
  python reproduce.py --out "$T/replay_full"            # full replay, K up to 100000
for f in "$T"/replay_full/data/*; do
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/$(basename "$f")") \
    && echo "same  $(basename "$f")" || echo "DIFF  $(basename "$f")"; done
```

(On a POSIX host use `python3` for `py`.) At intake (3 October 2026, Windows)
the exact-only replay printed `Exact verification: PASS` in about 1 s and
reproduced `data/constant_certificates.json` up to CRLF; the two queries
returned 39828 and 75. The full replay (Python 3.12.13, mpmath 1.3.0,
matplotlib 3.10.8) passed in 92.5 s on a loaded machine (the package recorded
6.2 s): all eleven data files matched the shipped ones (seven CSV files byte
for byte, the two JSON and two `.tex` files after CRLF stripping),
`verification.json` differed only in `elapsed_seconds` and `python_version`,
and the three PNG figures differed only in rendering. The recorded run checks
90,009 integer-root cases, 27,555 rational-root cases, the forward/backward
agreement for `m = 1, 2, 3` and `n ≤ 2000` and for `m = 1/2, 2/3, 3/2, 5/3`
and `n ≤ 200`, the three OEIS prefixes, the block identities for `r = 3`, and
the twelve certificate intervals (`m = 1, 2, 3, 5`; `j = 10, 100, 1000`).

**Part II** (exact checker, standard library only):

```sh
T=$(mktemp -d); mkdir -p "$T/r188/code" "$T/r188/data"
cp code/02-rates-check_exact.py "$T/r188/code/check_exact.py"
cp code/02-rates-exact_rounding.py "$T/r188/code/exact_rounding.py"
cp data/02-rates-oeis_fixtures.json "$T/r188/data/oeis_fixtures.json"
py -I -B "$T/r188/code/check_exact.py" --output "$T/exact.json" > /dev/null
py -I -B -O "$T/r188/code/check_exact.py" --output "$T/exact-O.json" > /dev/null
cmp "$T/exact.json" "$T/exact-O.json"
tr -d '\r' < "$T/exact.json" | cmp - <(tr -d '\r' < data/02-rates-generated-exact_checks.json) && echo same
```

At the write (7 October 2026, Windows, Python 3.14.4) the checker ran in
about 5 s and its output equalled the recorded
`data/02-rates-generated-exact_checks.json` after CR stripping; the intake
dossier found the normal and `-O` outputs byte-identical to each other and to
the record. The package's `reproduce.py`, `test_build.py` and `build.py` need
the complete delivered archive: extract `<scratch>/r188.zip` (above) and
follow `02-rates-README_REPRODUCIBILITY.md` there. On Windows `reproduce.py`
reports "exact checker stdout differs" only because the checker's text-mode
stdout has CRLF line ends; its stdout equals the output file after stripping
`\r` (intake dossier). `build.py` needs a pdfLaTeX installation and was not
run.

**Part III:**

```sh
T=$(mktemp -d); mkdir -p "$T/per/code"
cp code/03-schedules-verify.py "$T/per/code/verify.py"
py "$T/per/code/verify.py" --no-figures --output "$T/out" > "$T/run.txt"
for f in thresholds profile_samples limiting_profiles certificate_bounds; do
  cmp -s "$T/out/data/$f.csv" "data/03-schedules-$f.csv" && echo "same  $f" || echo "DIFF  $f"; done
for f in certificates gamma_products verification; do
  tr -d '\r' < "$T/out/data/$f.json" | cmp -s - <(tr -d '\r' < "data/03-schedules-$f.json") \
    && echo "same  $f" || echo "DIFF  $f"; done
```

At the write (7 October 2026) this ran in 14 s: the four CSV files were
byte-identical, the three JSON files equal after CR stripping, and the console
output equal to `data/03-schedules-run_log.txt` apart from its line "Wrote four
vector PDF figures and PNG previews." (figures are skipped with
`--no-figures`; regenerating them needs NumPy and Matplotlib). The recorded
run checks 3,200 inverse boundaries, 2,847 exhaustive small-survival cases,
310 exact thresholds and 22 rational certificates.

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, longtable, graphicx,
xcolor, enumitem, fancyhdr, placeins, hyperref, xurl, cleveref, lmodern,
microtype). The article inputs `data/threshold_table.tex`,
`data/constant_intervals.tex`, `figures/*.png` and `figures/03-schedules-*.pdf`
relative to this directory. Build in a scratch copy:

```sh
B=$(mktemp -d); cp -r *.tex data figures "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026: 80 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes.
A build of the batch-85 text gives 27 pages, also without warnings.

## Provenance

- Sources cited: OEIS A073047, A082527, A082528, A002491; Erdős–Jabotinsky,
  Indag. Math. 20 (1958) 115–128; Broline–Loeb, arXiv:math/9502225; Brown,
  "Rounding up to π" (MathPages); Lehéricy, Math. Stack Exchange answer
  4705436 (2023); Li, arXiv:2608.17517 (2026); DLMF Chapter 5 (Sections 5.6,
  5.7, 5.11(iii), 5.15); Fečkan, Pačuta, Pospíšil and Vidlička, AIMS
  Mathematics 4 (2019) 1466–1487 (Part III, background only).
- Repository inputs: Part I's pin `ce37e13f4` (3 October 2026), used for a
  bounded non-duplication search; Part III's pin `52d8ca404` (5 October 2026),
  at which it read Part I; Report 188 has no pin.
- Batch 85 of `docs/incoming`, manuscript 05; arrival `317c1ce2e`, placement
  `713149ded` (batch 85A), written in the batch-85 write (3 October 2026,
  `2b3b69b4b`).
- Batch 110: bundle Report 188 (arrival `60f54ea06`) and
  `Periodic_Rounding_Extinction.zip` (arrival `e4d5dcf9e`, held from batch 114),
  placed in `8622ca7e5` with the local prefixes `02-rates-` and
  `03-schedules-`, written on 7 October 2026. They are additions, not a merge:
  they answer different questions of Part I and share no new theorem. The
  write's choices: Parts in arrival order before Part I's appendices; each
  Part printed in full in its source's letters; statements already in Part I
  kept in place and marked as second routes rather than removed.
