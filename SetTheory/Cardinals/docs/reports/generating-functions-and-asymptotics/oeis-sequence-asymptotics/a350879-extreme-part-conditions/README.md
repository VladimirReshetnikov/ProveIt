# Extreme-Part Conditions in Integer Partitions (OEIS A350879, A237753, A237751, A118096, A117086)

**Part I: for fixed `k ≥ 2`, `b ≥ 0`, partitions with largest part `M` and
length `L` satisfying `M = kL + b` or `M ≥ kL + b` have expansions to every
fixed order, `E_{k,b}(n) ~ k!(π/√(6n))^k p(n)`, `T_{k,b}(n) ~
k!(π/√(6n))^{k−1} p(n)`, with explicit coefficients and a Lambert `W_{−1}`
inverse. Part II: partitions with largest part twice the smallest (A118096)
have every fixed order on the scale `C n^{−1/2} e^{π√(2n/15)}`, four explicit
corrections in `Q(√5)`, inverses, eventual strict increase and log-concavity.
Part III: the deficit of partitions whose largest part is divisible by the
smallest (A117086) is `D(n) ~ (π/(2√(6n))) p(n)` to every fixed order, with
residue equidistribution, a stretched-exponential comparison and a rational
certificate. And a refutation: A350879's alternative form with
`exp(√(2πn/3))` is false; the rate is `exp(π√(2n/3))`**

A research report bound from three manuscripts dated 4 October 2026
("Report 216", "Report 217", "Report 218" of a session bundle). Report 216's
author line and PDF author field are empty; Reports 217 and 218 read "Report
217" and "Report 218". None names a person, tool or addressee; none carries a
"prepared for private review" line, an e-mail address or personal data.

| Part | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | Report 216 (batch 111, base) | `Report216-reproducibility.zip` (20 files in `Report216/`, 567,001 bytes, SHA-256 `ca858cb05b9b…ea13edb9ec180c7`), arrival `60f54ea06`; `Report216.tex` (738 lines, 20 pp.) | none | `d451ef3d8` | Part I, Sections 1–10 and Appendix A, labels `xpc:sl:` |
| II | Report 217 (batch 111) | `Report217-source-v2.zip` (21 files in `Report217/`, 409,022 bytes, SHA-256 `96812623e011…abcc67943772177`), arrival `60f54ea06`; `article.tex` (594 lines, 14 pp.); edition mark "v2" in the archive name | none | `d451ef3d8` | Part II, Sections 11–21, labels `xpc:r2:` |
| III | Report 218 (batch 111) | `Report218-reproducibility.zip` (17 files in `Report218/`, 544,706 bytes, SHA-256 `f688cd814dde…7e4377cbbb2b09f`), arrival `60f54ea06`; `report218.tex` (976 lines, 22 pp.) | none | `d451ef3d8` | Part III, Sections 22–33 and Appendix A, labels `xpc:dv:` |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## How the merge was made

- **Base and order.** Report 216 is the base (staged as `article.tex`): the
  most general statement (a two-parameter family), the first to arrive, and
  the carrier of the batch's OEIS correction. Reports 217 and 218 follow. No
  Part cites another.
- **What binds them.** Conditions coupling the extreme parts; Part II's
  generating function is the `L = 2` summand of Part III's (104): A118096
  counts the partitions of A117086 with ratio exactly 2. Parts I and III share
  the machinery (a finite sieve or polynomial reduction bounded on the whole
  Cauchy circle, then a finite-shift Rademacher transfer with the same
  polynomials `Q_ℓ`) and the same triangular inverse reversion. Part II uses a
  discrete two-variable saddle at the golden-ratio point.
- **Duplication.** Part III's Section 27 (Rademacher gap, `Q_ℓ`, Lemma 27.1)
  repeats Part I's Lemmas 4.1–4.2 and Proposition 4.3, and its inverse
  reversion (160) is Part I's (54) with `d_j = (2A)^j c_j`; kept with dated
  notes, because Part III's later statements cite them by their own labels.
- **Numbering.** Sections continuous; statements within sections; equations
  global, as delivered. Part I keeps every number (Tables 1–2, Appendix A).
  Report 217's Section `k` → `k + 10`, equation `(k)` → `(k + 65)`; Report 218's
  Section `k` → `k + 21`, equation `(k)` → `(k + 103)`, appendix letter A kept.
- **Inlined tables.** Report 216's two and Report 218's four generated tables
  (read by `\input` in the deliveries) are printed inline; the shipped copies
  under `data/` are the delivered files. Report 216's table labels were
  prefixed too.
- **Bibliography.** Merged: Part II's `oeis`, `dlmf` → `oeisA118096`,
  `dlmfBessel`; Part III's `oeis` → `oeisA117086`, `nr` → `ngorhoades`;
  `dlmf` (§23.18) and `johansson` printed once for Parts I and III.
- **Layout.** Each Part header restores the delivery's paragraph and list
  spacing (Part I: no indent, 4 pt skip; Part II: tight lists; Part III:
  looser lists, display breaks allowed).

## Trust boundaries

- **What is proved by hand.** All theorems of the three Parts. The inputs
  quoted, not proved: the Dedekind eta transformation (DLMF §23.18) and the
  Rademacher series in Johansson's normalization (Parts I, III); classical
  Bessel asymptotics (DLMF §10.40, §10.17) and dilogarithm identities proved
  in the text (Part II); the Andrews–Freitas specialization is re-proved
  directly in Part III.
- **What rests on computation.** Part III's finite certificate (171) at
  `n = 1000` (Section 31) (exact rational arithmetic, run by its program); the explicit
  constants and the onset `n ≥ 90` of Theorem 29.1 are checked by rational
  endpoint tests, with the monotonicity arguments in the text. The explicit
  coefficient lists (Part I (45)–(48), Part II (70), Part III's `c_0..c_5`) are
  finite exact computations of the stated rules.
- **What is diagnostic.** Part I's Tables 1–2, Part II's numerical errors at
  `n = 10000`, all floating values; all inverse constants and onsets are
  existential.
- **What is prior.** Kotěšovec's leading laws (A350879/A237753, 2024;
  A118096, 2025); Jovovic's generating function; McIntosh's and Zhou's
  radial machinery; Szekeres, Jiang–Wang, Melczer–Panova–Pemantle, Richmond,
  Hwang, Ngo–Rhoades (Part I); Bridges–Franke–Garnowski, Ngo–Rhoades,
  Cesana–Craig–Males, Andrews–Freitas/Gupta (Part III).

## What it proves

Statement and equation numbers are those of this file.

**Part I** (`E_{k,b}`: `M = kL + b`; `T_{k,b}`: `M ≥ kL + b`):

- **Proposition 2.1 (`xpc:sl:prop:sieve`)**: the finite-product sieves
  (19)–(20).
- **Theorem 1.1 (`xpc:sl:thm:forward`)**: `X_{k,b}(n) = k! B(n) t^s
  (Σ_{m≤R} c_m t^m + O(t^{R+1}))` for every fixed `R` (12); first coefficients
  (15)–(16); A237751 `~ (2π/√(6n)) p(n)` (17); the literal form (18).
- **(45)–(48)**: radial series and `c_0..c_3` for A237753 and A237751.
- **Theorem 6.4 (`xpc:sl:thm:inverse`)**: two ceilings about the inverse centre
  `x_M(y)` with width `O(w_0^{−M})` (65); triangular reversion
  (Proposition 6.1), eventual increase (Lemma 6.3).

**Part II** (A118096):

- **Theorem 11.1 (`xpc:r2:thm:coeff`)**: `a(n) = C n^{−1/2} e^{B√n}(Σ_{r≤M} d_r
  n^{−r/2} + O(n^{−(M+1)/2}))`, `B = π√(2/15)`, `C = 1/√(5+√5)` (68); the
  finite rule (88) and transfer (69); `c_1..c_4` (70).
- **Theorem 17.1 (`xpc:r2:thm:inverse`)**: log-log inverse polynomials `P_j`
  (97), two-ceiling brackets (100) and about `Z_J(Y)`.
- **Corollary 18.1 (`xpc:r2:cor:shape`)**: eventual strict increase and strict
  log-concavity.

**Part III** (A117086 and its deficit `D = p − a`):

- **Theorem 22.1 (`xpc:dv:thm:main`)**: `D(n) = (B(n)t/2)(Σ_{m≤R} c_m t^m +
  O(t^{R+1}))` (107), `D(n)/p(n) ~ π/(2√(6n))`; `c_0..c_5`; (137).
- **Theorem 25.2 (`xpc:dv:thm:residues`)**: fixed-minimum residue
  equidistribution with exponentially small error (117).
- **Corollary 28.1, Theorem 29.1**: `D − W = O(p(n) n^{−L})` (138) for the
  reciprocal-minimum weighted count `W`, and an explicit stretched-exponential
  bound for `n ≥ 90` (143).
- **Theorem 26.1, Section 31**: finite-`n` enclosure; the rational certificate
  at `n = 1000` (171).
- **Theorem 30.1, Proposition 30.2**: two-ceiling inverse brackets (163); the
  exact two-index shortcut `ν_p ≤ ν_a ≤ ν_p + 1` (166).

Added by the write (7 October 2026), marked `[write]`:

- **Guide to this report** (`xpc:sec:guide`): the Parts, a comparison table,
  the merge choices, provenance, sources read, checks, relation to the
  repository, collected non-claims of the three Parts, a four-column table of
  reading conventions.
- **Remark 1.2 (`xpc:sl:rem:oeis`)**, **Remark 11.2 (`xpc:r2:rem:oeis`)**,
  **Remark 22.2 (`xpc:dv:rem:oeis`)**: the five OEIS entries (below).
- **Remark 1.3 (`xpc:sl:rem:a350879`)**: **A350879's alternative form refuted,
  with proof** (below).
- **Remark 6.5 (`xpc:sl:rem:transseries`)**: (a) **instance** of
  `p0:thm:staircase`(1); (b) **instance**: `w_0` (51) is
  `p0:thm:lambert-core`(3), `b < 0`, with `a_vol = 1`, `b_vol = −d`;
  (c) **formal instance**: the reversion (54) is the formal-exactness identity
  of `p0:thm:lambert-centered`(4) with `Q_vol(τ) = log H(2Aτ)`, so `u_m` is the
  volume's `c_m`; (d) **instance**: the root estimate behind (60) is
  `p0:thm:lambert-centered`(5) in `w` (the truncated model is exactly
  exponential–power), its residual step `p0:thm:backward-error`;
  (e) **analogue**: Theorem 6.4 of `p0:thm:staircase`(2).
- **Remark 17.2 (`xpc:r2:rem:transseries`)**: (a) **instance** of
  `p0:thm:staircase`(1); (b) **formal instance**: (97) is
  `p0:thm:flattening`(4) with `a = 1`, `b = −1`, `q_r = α_r`, `H = log T`
  (`P_1`, `P_2` reproduced), residual step `p0:thm:backward-error`;
  (c) **instance, not used by the source**: `H_J` is exactly
  exponential–power, so `p0:thm:lambert-centered`(5) also applies;
  (d) **analogues**: (100) and the `Z_J` bracket.
- **Remark 30.3 (`xpc:dv:rem:transseries`)**: (a) **instances** of
  `p0:thm:staircase`(1), with a **proof that A117086 is strictly increasing for
  every `n ≥ 0`** (`a(n+1) ≥ p(n) = a(n) + D(n)` and `D(n) ≥ 1` for `n = 5` and
  all `n ≥ 7`, witnessed by `(n−2, 2)` for odd `n` and `(n−5, 3, 2)` for even
  `n ≥ 8`); (b) **instance** of `p0:thm:lambert-core`(3); (c) **formal
  instance** of `p0:thm:lambert-centered`(4), the same equation as Part I's
  (54); the smooth root an instance of (5); (d) **analogue**: Theorem 30.1;
  (e) **not shown to be an instance**: Proposition 30.2.
- Notes: the check of Part II's finite rule (end of Section 15), the
  recomputed diagnostics (end of Section 19), Part I's counterparts in Part III
  (end of Section 27), question notes in Sections 10, 21 and 33, the merged
  bibliography note; labels on five unlabelled sections.

## The OEIS entries and the refuted form (Remarks 1.2, 1.3, 11.2, 22.2)

Read on 7 October 2026 in the internal format.

- **A350879** (#51, 18 October 2024; _Seiichi Manyama_, 21 January 2022):
  triangle `T(n,k)`, partitions with `k*(greatest part) = (number of parts)`;
  columns `k = 1..7` are A047993, A237753, A237756, A348163, A348164, A377107,
  A377108. Kotěšovec (17 October 2024): "Column k > 1 is asymptotic to k! *
  Pi^k * exp(sqrt(2*Pi*n/3)) / (2^((k+4)/2) * 3^((k+1)/2) * n^((k+2)/2)).
  Equivalently, for fixed k > 1, T(n,k) ~ k! * Pi^k * A000041(n) / (6^(k/2) *
  n^(k/2))."
- **Refuted, with proof (Remark 1.3).** The first form is false for every
  `k ≥ 2`; the second is true. By conjugation `T(n,k) = E_{k,0}(n)`, and (18)
  gives `T(n,k) ~ k!π^k e^{π√(2n/3)}/(4√3·6^{k/2} n^{1+k/2})`; since
  `2^{(k+4)/2}3^{(k+1)/2} = 4√3·6^{k/2}`, the posted first form divided by this
  is `exp(−(π − √π)√(2n/3)) → 0`. Only the rate is wrong (a factor `π`
  missing under the root), as Report 216 itself observed. Numerically
  (illustration), A237753(3000) is `0.7274…` times the correct equivalent
  and `2.84…·10^26` times the posted first form. No OEIS edit was made.
- **A237753** (#32, 11 July 2026; Kimberling): Kotěšovec's `a(n) ~ Pi^2 *
  exp(Pi*sqrt(2*n/3)) / (4 * 3^(3/2) * n^2)` is correct (it is (18) at
  `k = 2`). **A237751** (#11, 24 January 2022; Kimberling): no asymptotic
  formula; (17) is not recorded there.
- **A118096** (#57, 18 March 2026; _Emeric Deutsch_, 12 April 2006):
  Kotěšovec's `a(n) ~ exp(Pi*sqrt(2*n/15)) / (5^(1/4)*sqrt(2*phi*n))` (13 June
  2025) is the case `M = 0` of Theorem 11.1; it also links a 2025 preprint by
  McKean, not cited by Report 217 and not read by the write.
- **A117086** (#19, 3 September 2017; _Vladeta Jovovic_, 17 April 2006): the
  generating function (104); no asymptotic formula; cross-references
  A118096.
- The write's own computations agree with every b-file term checked: A237753
  and A237751 to `n = 3000` (sieve), all columns `k ≥ 2` of A350879's 50-row
  b-file, A118096 to 3000 (its generating function), A117086 to 1000, and
  brute force to `n = 40` for all four statistics. Nothing was submitted to
  the OEIS.

## What is not claimed

From the three Parts, kept in the article (collected in the Guide):

- **Part I**: fixed slope, offset and order only; no convergence, numerical
  error bound, effective onset, `k = 1` conclusion or growing-offset sum;
  existential inverse constants; no historical priority (Kotěšovec's leading
  law; bounded comparison with the cited literature); no clean-room or
  independent-proof claim for the checks.
- **Part II**: no novelty claim and no solution of a known open problem; the
  comparison with Pittel (2007) is unresolved; no uniformity in the order, no
  explicit threshold or last exception; standard inversion mechanisms; `H(q)`
  not identified with a mock theta function.
- **Part III**: no historical priority, no uniform growing-order expansion,
  no convergence; the stretched-exponential bound is an upper bound proving
  no `exp(−c√n)` rate, optimal only within its two-term majorant; no global
  monotonicity of `D`; ineffective inverse constants; no quantum-modularity
  claim; the A117086 revision history not inspected.

The write adds: its checks are floating, finite or symbolic computations;
the transseries remarks claim no novelty for any inversion; the merge claims
no connection between the Parts beyond the shared summand and machinery.

## Further questions

Part I's Section 10 (five directions: effective bounds; growing `k`, `b`;
coefficient growth and resummation; the `k = 1` rank boundary; other coupled
boundaries), Part II's Section 21 (Pittel's paper; effective constants and
last exceptions; ratio `m ≥ 3`; identities for `H(q)`; growth of `c_j`) and
Part III's Section 33 (explicit inverse constants; sharper twist bounds;
other minimum weights) are kept. Dated notes: under Vladimir's standing rule
of 4 October 2026 nothing in the three manuscripts was found unproved as
stated or wrong; the one wrong claim met in their sources is the OEIS form
refuted in Remark 1.3. **Pittel 2007 stays open**: the write's attempt to read
it at the publisher (7 October 2026) was refused (HTTP 403); by the source's
account its parameter `w^k + w = 1` has, at `k = 2`, the root `φ^{−1}`, which is
Part II's saddle point. Finite observations recorded: `E_{2,0}` and `T_{2,1}`
increase strictly from `n = 15` and `n = 5` through 3000; A118096's last
non-increase is at `n = 42` and its last log-concavity failure at `n = 445`
(b-file to 9999); `D` increases strictly for `18 ≤ n < 1000`.

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): staged files
  byte-identical to fresh extractions; the A350879 discrepancy confirmed
  against the live entry; the three delivered suites reproduce on copies
  (failures only Windows artifacts).
- At the write (7 October 2026; same machine; Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0): all manifests verified (Report 216 19/19; Report 217 20/20
  and `generated/SHA256SUMS.json` 5/5; Report 218 15/15 and `SHA256SUMS`
  16/16); every proof read line by line; the counts above; Part I's radial
  series, `c_0..c_3` for A237753 and A237751, the general (15)–(16) for
  `2 ≤ k ≤ 6`, `0 ≤ b ≤ 3`, `u_1..u_3` by solving (54), and (62); Part II's
  saddle data, `c_1..c_4` from the finite rule (88) to better than `10^{−43}`,
  `d_1..d_4` (printed digits are truncations), the `n = 10000` errors and the
  implicit inverse, `P_1`, `P_2`; Part III's `g_1..g_8` by both formulas,
  `c_0..c_5`, `ρ_1..ρ_3`, `d^{(D)}_{1..3}`, `v_1..v_3`, the inverse centres
  and the half-index, `s_3(1000)`, `u_3(1000)` and both certificate bounds
  from the printed `E` (the certificate's `E` itself not recomputed), the
  rational inequalities of Section 29, `D(17) = 44`, `D(18) = 43`,
  `D(1000)`. Part I's Tables 1–2 were not recomputed. Rerun from the shipped
  files (routes below): Report 216 `reproduce.py --exact` (outputs differ from
  the records only in the recorded Python version), Report 217 `selftest.py`
  and `build.py --order 4 --max-n 10000` (all five generated files equal the
  records up to line endings), Report 218 `reproduce.py --N 1000` (all seven
  generated files equal up to line endings) and `uniform_certificates.py`.
- Sources read by the write: the five OEIS entries and b-files; the
  transseries volume (labels in the Guide). Not read: the cited literature
  (Pittel's paper attempted, refused).

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of the three
transseries remarks is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these sequences is.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a239950-maximal-schreier-supports` (batch 111; least part equal to the
number of distinct sizes, another extreme-part condition on a different
scale) and `a239964-sizes-equal-max-multiplicity` (batch 111). No shared
result, so no reciprocal note is proposed.

**Stale claims.** Before batch 111 no file of the repository named A350879,
A237753, A237751, A118096 or A117086.

## Notation

The Guide's table puts the three Parts side by side: `A` (`π²/6`, `π²/30`,
`𝖠`), `B` (Part I's `B(n)`, Part II's `2√A`, Part III's `𝓑(n)`), `C`, `D`
(Part I's sieve exponents and inverse constant, Part II's `2A − ax_0²`, Part
III's deficit), `a(n)`, `X`, `t`, `s`, the coefficient families, `d`, `G`,
`H`, `Q`, `T`, `L`, `w`, `ν`, `N`, the inverse coefficients `u_j`/`v_j`, `k`,
`b`, `M`, and the volume's `X_vol`, `a_vol`, `b_vol`, `L_vol`. No symbol was
renamed.

## Labels

Report 216's 92 labels (90 in its text: `eq:` 65, `sec:` 12, `lem:` 6, `prop:`
4, `thm:` 2, `app:` 1; and two table labels in its generated tables) carry
`xpc:sl:`; Report 217's 54 (`eq:` 38, `sec:` 8, `lem:` 5, `thm:` 2, `cor:` 1)
carry `xpc:r2:`; Report 218's 90 (`eq:` 68, `sec:` 10, `thm:` 5, `lem:` 3,
`cor:` 2, `prop:` 1, `app:` 1) carry `xpc:dv:`; the 83, 57 and 86 references
were updated. The write added 16: `xpc:sec:guide`, three Part labels, seven
remarks, and five section labels (`xpc:r2:sec:scope`, `radial`, `questions`;
`xpc:dv:sec:result`, `limitations`). The report has 252 labels. Builds of the
three delivered texts and of this one were compared: every delivered label
keeps its number up to the stated section and equation shifts.

## Files

```text
README.md                                         this guide (replaces Report 216's delivery README)
article.tex                                       the merged report (Report216.tex, Report217 article.tex, report218.tex; labels prefixed, [write] additions)
article.pdf                                       compiled report, 64 pages
216-slope-SOURCES.txt                             Report 216's source references and scope cautions (delivered SOURCES.txt)
216-slope-SOURCE_FILES.txt                        Report 216's source inventory (delivered SOURCE_FILES.txt)
216-slope-code-README.md                          Report 216's code guide (delivered code/README.md)
217-ratio2-SOURCE_NOTES.md                        Report 217's source notes (delivered SOURCE_NOTES.md)
217-ratio2-code-README.md                         Report 217's code guide (delivered code/README.md)
218-divisible-code-README.md                      Report 218's code guide (delivered code/README.md)
code/216-slope-reproduce.py                       Report 216's root build/rebuild driver (delivered reproduce.py)
code/216-slope-code-reproduce.py                  Report 216's exact and diagnostic reproduction (delivered code/reproduce.py)
code/216-slope-extremes.py                        Report 216's sieve, coefficients, inverse (delivered code/)
code/216-slope-independent.py                     Report 216's independent counting and coefficient paths (delivered code/)
code/216-slope-test_package_guards.py             Report 216's package guard tests (delivered at the root)
code/217-ratio2-exact.py                          Report 217's exact coefficients and counts (delivered code/)
code/217-ratio2-inverse.py                        Report 217's inverse polynomials (delivered code/)
code/217-ratio2-oracle.py                         Report 217's second coefficient route (delivered code/)
code/217-ratio2-numerical.py                      Report 217's optional mpmath diagnostics (delivered code/)
code/217-ratio2-selftest.py                       Report 217's self-tests (delivered code/)
code/217-ratio2-build.py                          Report 217's table generator (delivered code/)
code/217-ratio2-rebuild.py                        Report 217's offline rebuild (delivered at the root)
code/217-ratio2-archive.py                        Report 217's archive builder (delivered at the root)
code/218-divisible-reproduce.py                   Report 218's exact reproduction (delivered code/)
code/218-divisible-test_reproduce.py              Report 218's tests (delivered code/)
code/218-divisible-uniform_certificates.py        Report 218's rational certificates for Section 29 (delivered code/)
code/218-divisible-rebuild.py                     Report 218's rebuild (delivered at the root)
data/216-slope-code-results-coefficients.json     recorded coefficients (delivered code/results/)
data/216-slope-code-results-exact_checks.json     recorded exact checks (same)
data/216-slope-code-results-selected_counts.json  recorded selected counts (same)
data/216-slope-code-results-diagnostics.json      recorded diagnostics (same)
data/216-slope-tables-forward_table.tex           Table 1 source (delivered tables/)
data/216-slope-tables-inverse_table.tex           Table 2 source (same)
data/216-slope-PACKAGE_GUARD_CHECKS.json          recorded package guard checks (delivered at the root)
data/216-slope-requirements.txt                   mpmath pin (delivered at the root)
data/217-ratio2-MANIFEST.json                     manifest with claim and source-comparison fields (delivered at the root)
data/217-ratio2-generated-exact_counts.tex        generated table (delivered generated/)
data/217-ratio2-generated-exact_tables.json       generated exact tables (same)
data/217-ratio2-generated-inverse_polynomials.tex generated table (same)
data/217-ratio2-generated-radial_coefficients.tex generated table (same)
data/217-ratio2-generated-numerical_diagnostics.json  recorded diagnostics (same)
data/217-ratio2-generated-selftest.txt            recorded self-test (same)
data/218-divisible-generated-exact_values.csv     n, p, a, D for n = 0..1000 (delivered generated/)
data/218-divisible-generated-receipt.json         recorded receipt (same)
data/218-divisible-generated-exact_counts.tex     generated table (same)
data/218-divisible-generated-radial_coefficients.tex  generated table (same)
data/218-divisible-generated-forward_coefficients.tex generated table (same)
data/218-divisible-generated-finite_enclosure.tex generated table (same)
data/218-divisible-generated-verification_summary.tex generated table (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit: the three delivered
PDFs (`Report216.pdf` 393,986 bytes, 20 pp.; `Report217.pdf` 369,929 bytes,
14 pp.; `Report218.pdf` 459,389 bytes, 22 pp.); Report 217's `article.tex`
and Report 218's `report218.tex` (Parts II and III of `article.tex`); the
delivered READMEs of Reports 217 (4,781 bytes) and 218 (4,272 bytes) and
Report 216's `README.txt` (5,298 bytes), staged at placement as `README.md`
and replaced by this guide (all three summarized below); the pure checksum
manifests (Report 216 `MANIFEST.json` 1,882 bytes; Report 217
`generated/SHA256SUMS.json` 464 bytes; Report 218 `MANIFEST.json` 1,622 bytes
and `SHA256SUMS` 1,416 bytes), verified at the write.

**Delivered text that names the delivery layout or files not shipped.** The
code READMEs and programs (delivered names and directories, the manifests,
`Report21x.tex`/`article.tex`, `tables/`, `generated/`); Part I's Sections 7
and 9, Part II's Section 19, and Part III's Section 32 and Appendix A ("The
accompanying archive contains…", "included from files written by the exact
reproduction program"). Use the
routes below.

## Retrieving the delivered packages

```sh
T=$(mktemp -d); cd "$T"
for z in Report216-reproducibility Report217-source-v2 Report218-reproducibility; do
  git -C /path/to/ProveIt show 60f54ea06:docs/incoming/$z.zip > $z.zip && unzip -q $z.zip
done
sha256sum *.zip
# ca858cb05b9b99923e69634f423ac8b2477aab67e3cbdd0e6ea13edb9ec180c7  Report216-reproducibility.zip (567,001 bytes)
# 96812623e0111ebc3883a474406e75858d30d6bc136441ad7abcc67943772177  Report217-source-v2.zip (409,022 bytes)
# f688cd814ddeacf8fb6a1abbcbcb1c7611c7291620e9706807e4377cbbb2b09f  Report218-reproducibility.zip (544,706 bytes)
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only for the exact checks. Never run
anything in the repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a350879-extreme-part-conditions
B=$(mktemp -d)
# Report 216
mkdir -p "$B/Report216/code/results" "$B/Report216/tables"; cd "$B/Report216"
cp "$R/code/216-slope-code-reproduce.py" code/reproduce.py
cp "$R/code/216-slope-extremes.py" code/extremes.py; cp "$R/code/216-slope-independent.py" code/independent.py
for f in coefficients diagnostics exact_checks selected_counts; do cp "$R/data/216-slope-code-results-$f.json" code/results/$f.json; done
python -B code/reproduce.py --exact --out "$B/out216"
diff "$B/out216/results/exact_checks.json" code/results/exact_checks.json   # only the recorded "python" version differs
# Report 217
mkdir -p "$B/Report217/code"; cd "$B/Report217"
for f in build exact inverse numerical oracle selftest; do cp "$R/code/217-ratio2-$f.py" code/$f.py; done
python -B code/selftest.py && python -B code/build.py --out build-new --order 4 --max-n 10000
for f in exact_counts.tex exact_tables.json inverse_polynomials.tex radial_coefficients.tex selftest.txt; do cmp build-new/$f "$R/data/217-ratio2-generated-$f"; done
# Report 218
mkdir -p "$B/Report218/code"; cd "$B/Report218"
for f in reproduce test_reproduce uniform_certificates; do cp "$R/code/218-divisible-$f.py" code/$f.py; done
python code/reproduce.py --output "$B/out218" --N 1000 && python code/uniform_certificates.py
for f in "$B"/out218/*; do cmp "$f" "$R/data/218-divisible-generated-$(basename "$f")"; done
```

At the write (Windows) every comparison agreed up to line endings (Report
216: up to the recorded Python version). Use `py` where `python` is not on
the path. The builders, the optional diagnostics and the package guard tests
were not rerun by the write.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, amsmath, amssymb, amsthm, mathtools,
booktabs, array, longtable, geometry, xcolor, hyperref, fancyhdr, enumitem);
the bibliography and the generated tables are embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (64
pages): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered texts build with 20, 14 and 22 pages; Report
217's has one underfull box in its bibliography, which the merged
bibliography's ragged setting removes).

## From the delivery READMEs

Report 216's README (replaced by this guide) stated the result and scope
("There is no global historical novelty, k=1, growing-parameter,
growing-order, effective-constant, or resummation claim"), credited
Kotěšovec's 2024 leading law, gave the exact-check commands (98 count cases
to `n = 160`, 72 algebra cases, `Q` through `ℓ = 20`, 690 depth checks, 23 + 26
rejection controls) and the optional diagnostics ("NON-CERTIFIED
diagnostics"). Report 217's README (not shipped) described the proof and
the rebuild and said "This is an independently derived refinement, not a
claim of novelty or a solution of a known open problem" and that the Pittel
comparison is unresolved. Report 218's README (not shipped) gave the
reproduction commands and the scope of its finite checks and certificates.

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A350879, A237753, A237751, A118096 and A117086; OEIS content is
published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and that content remains under that licence. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscripts: the five OEIS entries; Szekeres (1990);
  Jiang–Wang, JNT 201 (2019); Melczer–Panova–Pemantle, SIDMA 34 (2020);
  Richmond (2018); Hwang, Acta Arith. 78 (1997); Ngo–Rhoades, RMS 4 (2017);
  Johansson, LMS JCM 15 (2012); Rademacher (1937); DLMF §23.18, §10.40,
  §10.17; Dyson (1969); Berkovich–Garvan; McIntosh, CJM 50 (1998); Zhou
  (2017); Pittel, JCTA 114 (2007); Andrews–Dixit–Yee, RNT 1 (2015); the ProveIt
  repository; Bridges–Franke–Garnowski, RMS 9 (2022); Cesana–Craig–Males, JNT
  256 (2024); Andrews–Freitas, Ramanujan J. 10 (2005); Gupta, JCTA 184 (2021).
  Nothing added by the write.
- Batch 111 of `docs/incoming`, bundle Reports 216, 217 and 218; arrival
  `60f54ea06`, placement `d451ef3d8`, written 7 October 2026.
