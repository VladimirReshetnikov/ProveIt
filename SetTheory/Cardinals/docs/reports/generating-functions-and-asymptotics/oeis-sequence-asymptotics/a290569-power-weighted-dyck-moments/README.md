# Power Weighted Dyck Moments (OEIS A290569, A216966, A218221, A227887, A338634, A291333)

**Dyck moments `Z_n(λ) = Σ_D ∏_h λ_h^{N_h(D)}` with descent weights of size
`h^p`, the array A290569. Part I: `Z_n(h^p) ~ 𝒞_p d_p^n (n!)^p n^{−1/2}` with
relative error `O_p((log n)^{−2})` for every fixed `p > 0` (Kotěšovec's
posted formula, proved relative to a cited Freud coefficient theorem), exact
harmonic and parity-harmonic amplitude transfer, and absolute amplitudes for
every positive polynomial weight. Part II: `p = 4`, first correction
`−(1+π)/(16n)` for the moments and their free cumulants A338634, and a proof
of A338634's parity conjecture. Part III: first relative corrections in
three regimes and a cumulative transfer; a conditional general-`p`
coefficient `C_p` recorded as an open question. Part IV: the diagonal
`p = τn + σ` to every fixed order, uniformly, with A291333 at `τ = 1`**

A research report bound from four manuscripts dated 4 October 2026
("Report 201", "Report 199", "Report 202", "Report 204" of a session
bundle). Their author lines read "Report 201/199/202/204" (Report 204's PDF
author field is empty); none names a person, tool or addressee. No package
carries a "prepared for private review" line, an e-mail address or personal
data.

| Part | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | Report 201 (batch 111, base) | `Report201.zip` (21 files in `Report201/`, 3,546,920 bytes, SHA-256 `571a7cad97c6…fedb07da95c77a6`), arrival `60f54ea06`; `Report201.tex` (1382 lines, 35 pp.) | none | `d451ef3d8` | Part I, Sections 1–18, labels `pwd:hm:` |
| II | Report 199 | `Report199.zip` (12 files in `Report199/`, 2,872,519 bytes, SHA-256 `3d8a699b123f…a7bc6ca27ead5d9`); `Report199.tex` (773 lines, 22 pp.) | none | `d451ef3d8` | Part II, Sections 19–33, labels `pwd:qt:` |
| III | Report 202 | `Report202.zip` (18 files in `Report202/`, 726,805 bytes, SHA-256 `2b83e3588e25…2fde19fb05c8187`); `Report202.tex` (1088 lines, 27 pp.) | none | `d451ef3d8` | Part III, Sections 34–43 and Appendices A–B, labels `pwd:rc:` |
| IV | Report 204 | `Report204.zip` (16 files, no wrapper, 555,616 bytes, SHA-256 `c6b5724246f1…3c60d087a8d972a`); `Report204.tex` (652 lines, 16 pp.) | none | `d451ef3d8` | Part IV, Sections 44–54, labels `pwd:dg:` |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## How the merge was made

- **Base and order.** Report 201 is the base (greatest generality; Report 202
  builds on it). Order: 201, 199 (`p = 4`), 202 (cites 201 and 199), 204 (the
  diagonal, independent method).
- **Duplication kept with notes.** Part I's endpoint estimate and deletion
  (Sections 2–3) recur in Part II's Section 24 (the `p = 4` case with the
  explicit constant 15552) and Part III's Appendix A (verbatim apart from the
  added log-convexity `Z_j² ≤ Z_{j−1}Z_{j+1}`, which Lemma 35.2 uses); Part I's
  arch concentration (Section 6) recurs in Part II's Section 26 and Part III's
  Appendix B (adapted to the scaled family, plus the free-energy evaluation
  `Φ_p(y_*) = log d_p − p`). The placement proposed printing 202's appendices
  once; they are kept because those additions are used, each with a note. The
  Berg–Valent quartic normalization appears in Sections 12, 23 and 40.2; Part
  III's (40.2) is a second route to Part II's correction.
- **Numbering.** Sections continuous; statements and equations within
  sections. Part I unchanged; Report 199's Section `k` → `k + 18`, Report 202's
  → `k + 33` (appendices A, B kept), Report 204's → `k + 43`.
- **Bibliography.** Merged; Part II's `oeis` → `oeisA338634`, Part IV's `AD`
  → `avdoshkin`; shared entries printed once with each Part's notes.

## Trust boundaries

- **The Freud input (Part I).** Theorem 1.1 rests on the leading-coefficient
  asymptotic for the fixed Freud weight `exp(−|A_F x|^β)`, all `β > 0`, of
  Kriecherbauer–McLaughlin (1999, Theorem 1.5), **read only as restated by
  Claeys–Krasovsky–Minakov (2023, Eq. (2.3))**; the original was read neither
  by the source nor by the write. Theorem 1.1, the absolute parts of Theorem
  1.6 and Corollary 15.2, and Part III's references to the general-power
  baseline are proved relative to it (note at the end of Section 5). The
  relative theorems 1.2–1.5 do not use it; the cubic and quartic constants
  are checked independently (Sections 11–12).
- **Other cited inputs.** Berg–Valent's quartic moment asymptotic (Parts
  I–III), the Dixon/analytic-urn results (Part I, Section 11), Stirling and
  DLMF formulas.
- **What is proved by hand.** Everything else, in all four Parts.
- **Conditional, not proved.** Part III's `C_p` (42.1).
- **What is diagnostic.** All decimals and tables (declared rounded), the
  numerical files, and the write's numerical test of `C_3`.

## What it proves

Statement and equation numbers are those of this file.

- **Part I (Report 201):** Theorem 1.1 `Z_n(h^p) = 𝒞_p d_p^n (n!)^p n^{−1/2}
  (1 + O_p((log n)^{−2}))`, `d_p = 4/I_p^p`, `𝒞_p = √(2p/π) I_p^{−p/2}` (1.6);
  Theorems 1.2–1.3 harmonic and parity-harmonic transfer `Z_n(λ)/Z_n(h^p) ~
  n^a e^{aK_p} P_f` (1.7); Theorem 1.4 uniform endpoint occupation; Theorem 1.5
  summable stability; Theorem 1.6 absolute amplitudes for positive polynomial
  weights (1.14); Theorem 15.1 and Corollary 15.2 two-ceiling inverses.
- **Part II (Report 199):** Theorem 19.1 `m_n/F(n) = 1 − (1+π)/(16n) +
  o(n^{−1})`, same for the cumulants `a_n` (19.5); Theorem 19.2 every fixed
  order in shifted moments (19.7); Proposition 20.1 matching quadruples;
  Theorem 24.1 occupation; Theorem 26.1 limit shape; **Theorem 28.1 parity**:
  `a_n` odd iff `n` is a power of two; Theorem 29.1 inverse.
- **Part III (Report 202):** Theorem 34.1 three regimes (34.4), (34.7),
  (34.8); Theorem 34.2 cumulative transfer (34.11); Theorem 38.1 local
  occupation; Corollaries 40.1–40.2 zero-harmonic quartics and quadratics
  (40.7), (40.10); Theorem 41.1 relative inverse displacements (41.4).
- **Part IV (Report 204):** Proposition 45.1 staircase-partition bijection;
  Theorem 46.1 uniform expansion (46.3); diagonal series (47.7); Theorem 48.1
  Gevrey remainder; Proposition 49.1 total variation (49.2); Proposition 50.1
  cutoff bounds; Theorems 51.2–51.3 inverses (51.5), (51.15).

Added by the write (7 October 2026), marked `[write]`:

- **Guide to this report** (`pwd:sec:guide`): the Parts, a comparison table,
  the merge choices, provenance, sources read, checks, relation to the
  repository, collected non-claims of the four Parts, and reading conventions.
- **Remark 1.7 (`pwd:hm:rem:oeis`)**, **Remark 19.3 (`pwd:qt:rem:oeis`)**,
  **Remark 44.1 (`pwd:dg:rem:oeis`)**: the OEIS entries (below).
- **Remarks 15.3, 29.2, 41.2, 51.4** (`…:rem:transseries`): the inverses
  against the transseries volume, statement by statement. Part I: `N(Y) =
  ⌈x_Y⌉` with the piecewise-linear interpolation is an **instance** of
  `p0:thm:staircase`(1), the brackets its (2) setting; the centre `t` is an
  **instance** of `p0:prop:factorial-core` (`κ = p`, `d = p log R − p`); the
  displacement `ξ − t` is the first coefficient of a **formal instance** of
  `p0:thm:core-reversion`; the final step `p0:thm:backward-error`. Part II:
  staircase(1) **instance**; `t` a factorial-core **instance** (`κ = 4`);
  `δ_0 = −B/D` the first core-reversion coefficient (formal); Theorem 29.1 an
  **analogue** of staircase(2). Part III: `Ñ(Y) = ⌈x̃⌉` a staircase(1)
  **instance**; Theorem 41.1 an **analogue** of `p0:thm:backward-error`
  (secant slopes); the base inverse **not compared** (not an explicit core
  solution). Part IV: staircase(1) **instance** (`n_1 = 1`); Theorem 51.2
  an **analogue** of staircase(2); `t` a factorial-core **instance** after
  `X = t²` (`κ = 1/2`, `d = −1`); the recurrence (51.14) a **formal instance**
  of `p0:thm:core-reversion` (first coefficient `α_0 = −A/H` checked).
- Notes: the Freud trust boundary (end of Section 5); Part I's counterparts
  in Sections 24, 26 and Appendices A, B; the second route in 40.2; **the
  conditional `C_p` as an open question with a numerical test at `p = 3`**
  (end of Section 42); question notes in Sections 18, 33, 54; the merged
  bibliography note; labels on two sections of Part IV.

## The OEIS entries and the conjecture proved

Read on 7 October 2026 in the internal format.

- **A290569** (#31, 22 August 2017; Gutkovskiy): the array; column `k` is the
  S-fraction with coefficients `1, 2^k, 3^k, …`.
- **A216966** (#29; Hanna), column 3, and **A227887** (#28), column 4:
  Kotěšovec's general comment (24 September 2020) "a(n,s) ~ c(s) * d(s)^n *
  (n!)^s / sqrt(n), where d(s) = (2*s*Gamma(2/s) / Gamma(1/s)^2)^s, c(s) =
  sqrt(s*d(s)/(2*Pi))", not labelled conjectural; Theorem 1.1 proves it
  (relative to the Freud input). `d_p`, `𝒞_p` equal `d(s)`, `c(s)` at `p = 3, 4`
  to 25 digits.
- **A218221** (#23, 16 March 2024; Hanna), weights `C(h+2,3)`: Kotěšovec's
  `d = 0.241821816937867322064…`, `c = 0.60382458700655692263…`; Theorem 1.6
  with `Q(x) = x(x+1)(x+2)/6` gives both to twenty digits.
- **A338634** (#9, 12 November 2020; Hanna): the unsigned (by OEIS
  convention Hanna's; "unattributed" in the write, corrected by the
  independent check) formula line **"For n > 0, a(n) is odd iff n is a power of 2 (conjecture)."
  is proved** by Theorem 28.1 (mod 2 the S-fraction is `1/(1 − z)`, and
  `A² + A = x` over `F_2`); Kotěšovec's leading formula is Theorem 19.1's leading
  term. The b-file (`0 ≤ n ≤ 130`), not retrieved by Report 199, agrees in all
  131 terms with the write's computation; the odd terms for `1 ≤ n ≤ 130` are
  exactly at the powers of two.
- **A291333** (#12, 21 July 2018; Gutkovskiy): Kotěšovec's `c =
  1/QPochhammer(exp(−1)) = 1.98244090741287370368…`; b-file (`n ≤ 30`, Israel)
  agrees with the write's computation.
- All b-file terms of A216966, A218221, A227887 agree with the write's own
  moment computations. (Independent check: A216966 and A227887 have no
  b-file; the OEIS synthesizes one from their 15 and 14 displayed terms, so
  the agreement covers those terms only. A218221's b-file, `0 ≤ n ≤ 198`, is
  real.) Nothing was submitted to the OEIS.

## What is not claimed

From the four Parts, kept in the article (collected in the Guide):

- **Part I**: no effective onset, uniformity in `p`, all-orders expansion or
  first-proof claim; the Freud input read only as restated; harmonic and
  polynomial equivalents only `o(1)`; no transfer for arbitrary `ℓ¹` or
  periodic perturbations; fixed-neighbourhood concentration only; inverses not
  certified; formal saddle geometry is Avdoshkin–Dymarsky's.
- **Part II**: no effective onset, `O(n^{−2})` remainder, all-orders raw
  expansion, single-ceiling inverse or absolute priority; Berg–Valent's model;
  Bender–Richmond-type shifted expansion; bounded source review.
- **Part III**: no first-proof, effective onset, all-orders or new
  unconditional general-power coefficient; `C_p` conditional on an unverified
  envelope; zero coefficients give only little-`o`.
- **Part IV**: no convergence, Borel summability, optimal truncation or
  transseries; no `τ → 0, ∞`; Gevrey bound an upper bound; decimals not
  certified; existential inverse constants; Kotěšovec's leading equivalent.

The write adds: its checks are floating, finite or hand computations; the
`p = 3` agreement of `C_3` is evidence, not proof; no novelty for any
inversion.

## Further questions

Kept: Part I's five (Section 18), Part II's five (Section 33), Part III's six
(Section 42), Part IV's five (Section 54). Under Vladimir's standing rule of 4
October 2026: **moved/recorded open** — Part III's conditional coefficient
`C_p = (p² − 6p + 2)/(24p) + ((p−1)/12) J_p` (42.1), which needs a Freud envelope
`|f_h| = O(h^{−2})` with a cumulative expansion that no one has verified in a
primary source. It reproduces the proved values at `p = 2` (`−1/8`) and `p = 4`
(`−(1+π)/16`); at `p = 3` it gives `C_3 = −0.19798885356…`, and the write's exact
`Z_n(h^3)` to `n = 400` give `n(Z_n/F_3 − 1) = −0.19776…, −0.19787…, −0.19793…`
at `n = 100, 200, 400` with Richardson values `−0.1979892…`, `−0.1979889…`:
agreement to about six digits, evidence only. **Proved**: A338634's parity
conjecture. Reading the original Kriecherbauer–McLaughlin theorem remains an
open verification task (note at the end of Section 18). No claim of any
source was found wrong.

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): staged files
  byte-identical to fresh extractions; A338634's parity checked for
  `n ≤ 130`; the two large data files regenerated byte for byte; the four
  suites reproduce on copies (failures only Windows artifacts).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  all manifests verified (Report 201 package 20/20 and source 11/11; Report
  199 11/11 and 6/6; Report 202 17/17 and 11/11; Report 204 15/15); every proof
  read line by line (the Guide lists the hand checks); own exact computations
  of `Z_n(h^3)` (to 400), `Z_n(h^4)` (to 500), A218221 (to 198), Part II's
  comparison moments (to 500), A338634 (to 130) and A291333 (to 30), with the
  b-file agreements above; every entry of Part II's diagnostic table;
  `Q(1)`, `c_1`, the TV constant and `E_0(10), E_0(20), E_0(40)` of Part IV
  (the tables print roundings, as declared); `d_p`, `𝒞_p` at `p = 3, 4`; the
  conditional `C_p` at `p = 2, 3, 4`. The delivered suites were **not rerun by
  the write** (the intake reran all four).
- Sources read by the write: the OEIS entries and b-files; the transseries
  volume. Not read: the cited literature (in particular KM, CKM, Berg–Valent,
  Mastroianni–Milovanović).

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`fb9602e55`), with
its own code, after fetching again A290569 (#31), A216966 (#29), A227887
(#28), A218221 (#23), A338634 (#9), A291333 (#12) and their b-files.

- **A338634's parity conjecture (Remark 19.3, Theorem 28.1).** The proof's
  reduction modulo 2 re-derived (`1 = A − x/A`, so `A² + A = x`,
  `A = 1 + Σ x^{2^j}`). A338634 recomputed for `n ≤ 130` by Lagrange
  inversion of `x = u M(u)²` (from `A = M(x/A²)`, derived from the defining
  relation) with the check's own `m_n`: all 131 b-file terms agree, odd terms
  exactly at the powers of two; the truncated continued fraction returns 1
  through `x⁴⁰`. Confirmed. **Precision:** the parity line is unsigned, so by
  OEIS convention Hanna's, not "unattributed" (dated note after Remark 19.3;
  the bullet above).
- **Correction:** A216966 and A227887 have no b-file of their own; the
  agreement claimed for their "b-files" covers their 15 and 14 displayed terms
  (dated note after Remark 1.7; the bullet above). The check's own height-state
  walk reproduces the write's moments to `n = 400` and `500`.
- **Constants.** `d_p`, `𝒞_p` equal Kotěšovec's `d(s)`, `c(s)` at `p = 3, 4`;
  (1.14) gives A218221's closed forms to 50 digits (with `I_3` by the beta
  function; quadrature alone loses digits near 27); A218221 (`n ≤ 198`) and
  A291333 (`n ≤ 30`) agree with their b-files; ratios to the asymptotic
  1.0293, 1.0147 at `n = 100, 198`.
- **Part II.** `r = 8√π/Γ(1/4)² = r_4`; every entry of the diagnostic table
  (`n = 20, 80, 160, 500`) reproduced from the check's own `m_n`, `b_n`.
- **Part III.** `J_2 = 0`, `J_4 = −π/4`, `J_3 = −0.6045997880…`,
  `C_3 = −0.1979888535…`; `e(n)` at 100, 200, 400 and both Richardson values
  reproduced; a three-point extrapolation gives `−0.19798885…`, about nine
  digits of agreement: still evidence for the conditional formula, not a
  proof of its premise, which stays open.
- **Part IV.** `Q(1)`, `E_0(10)`, `E_0(20)`, `E_0(40)`, the total-variation
  constant; `c_1` to about five digits by extrapolating exact `E_0(n)`,
  `n ≤ 160`.
- **Numbering and merge.** Shifts 0, 18, 33, 43 with appendix letters kept:
  all 431 delivered labels keep their numbers; 14 added, 445 in all; 126,
  65, 92, 66 references. The duplication notes (the constant 15552, the class
  `¾h⁴ ≤ w_h ≤ h⁴`, the log-convexity, the free energy `log d_p − p`) and the
  merged bibliography confirmed.
- **Transseries remarks (15.3, 29.2, 41.2, 51.4).** Factorial cores with
  `κ = p`, `4`, `½` (after `X = t²`), the core-reversion forms and first
  coefficients, the analogues: re-derived.
- **Provenance.** Archive bytes, SHA-256, file counts, lines, delivered
  pages, author lines and PDF author fields, the two regenerable data-file
  sizes, the file list. The delivered suites were not rerun (by the write
  either; the intake reran them).
- The check read the four Parts' proofs as well and found no error.

The check is recorded in the Guide, after the collected non-claims.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of the
transseries remarks is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these moments is.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a292692-weighted-dyck-newton-diagonal` (Dyck paths with peak weights
`k + a/b`, the "nearby peak-weight Newton-edge problem" of Part I's source
screen; a different model). No shared result, so no reciprocal note is
proposed.

**Stale claims.** Before batch 111 no file of the repository named A290569,
A216966, A218221, A227887, A338634 or A291333.

## Notation

The Guide's table lists the letters used differently across the Parts: `p`,
`k`; `m_n`, `b_n`, `a_n`; `I_p`, `H_p`, `r_p`, `d_p`, `𝒞_p`; `K_p`, `K_0`, `K`;
`C_p` (conditional) against `𝒞_p` (amplitude); `F`; `Q`; `J`, `J_p`; `A`,
`A_0`; `B`; `D`, `d`; `c_r`, `ℓ_r`; `t`, `L`; `N(Y)`, `N_h`; and the volume's
`X_vol`, `Λ_vol`, `h_vol`. No symbol was renamed.

## Labels

Delivered labels: Report 201 150 (`eq:` 117, `sec:` 18, `thm:` 7, `lem:` 4,
`cor:` 2, `prop:` 2) → `pwd:hm:`; Report 199 81 (`eq:` 57, `sec:` 15, `thm:` 6,
`lem:` 2, `prop:` 1) → `pwd:qt:`; Report 202 105 (`eq:` 78, `sec:` 12, `lem:` 5,
`thm:` 4, `app:` 2, `cor:` 2, `prop:` 2) → `pwd:rc:`; Report 204 95 (`eq:` 74,
`sec:` 12, `thm:` 4, `prop:` 3, `cor:` 1, `lem:` 1) → `pwd:dg:`; references
updated (126, 65, 92, 66). Added 14: `pwd:sec:guide`, four Part labels,
seven remarks, `pwd:dg:sec:model`, `pwd:dg:sec:questions`. Total 445. Builds
of the four delivered texts and of this one were compared: every delivered
label keeps its number up to the section shift.

## Files

```text
README.md                                              this guide (replaces Report 201's delivery README)
article.tex                                            the merged report (Report201/199/202/204.tex; labels prefixed, [write] additions)
article.pdf                                            compiled report, 107 pages
201-harmonic-repro-README.md                           Report 201's reproduction guide (delivered repro/README.md)
202-relcorr-repro-README.md                            Report 202's reproduction guide (delivered repro/README.md)
code/201-harmonic-build.py                             Report 201's builder (delivered build.py)
code/201-harmonic-test_guards.py                       Report 201's guard tests (delivered test_guards.py)
code/201-harmonic-repro-check.py                       Report 201's exact checks (delivered repro/check.py)
code/201-harmonic-repro-freud_check.py                 Report 201's Freud companion (delivered repro/freud_check.py)
code/199-quartic-build.py                              Report 199's builder (delivered build.py)
code/199-quartic-exact.py                              Report 199's exact computations (delivered code/exact.py)
code/199-quartic-diagnostics.py                        Report 199's diagnostics (delivered code/)
code/199-quartic-test_guards.py                        Report 199's guard tests (delivered code/)
code/202-relcorr-build.py                              Report 202's builder (delivered build.py)
code/202-relcorr-test_guards.py                        Report 202's guard tests (delivered test_guards.py)
code/202-relcorr-repro-check.py                        Report 202's exact checks (delivered repro/check.py)
code/202-relcorr-repro-diagnostics.py                  Report 202's diagnostics (delivered repro/)
code/202-relcorr-repro-test_guards.py                  Report 202's repro guard tests (delivered repro/)
code/204-diagonal-build.py                             Report 204's builder (delivered build.py)
code/204-diagonal-coefficients.py                      Report 204's coefficient algorithms (delivered code/)
code/204-diagonal-exact_checks.py                      Report 204's exact checks (delivered code/)
code/204-diagonal-inverse.py                           Report 204's inverse (delivered code/)
code/204-diagonal-manuscript_checks.py                 Report 204's manuscript checks (delivered code/)
code/204-diagonal-numerical_diagnostics.py             Report 204's diagnostics (delivered code/)
code/204-diagonal-tables.py                            Report 204's table generator (delivered code/)
data/201-harmonic-requirements.txt                     pins (delivered requirements.txt)
data/201-harmonic-manifests-source_manifest.json       source manifest with engine banner and epoch (delivered manifests/)
data/201-harmonic-repro-REPRODUCTION_RECEIPT.json      receipt (delivered repro/)
data/201-harmonic-repro-FREUD_REPRODUCTION_RECEIPT.json receipt (same)
data/201-harmonic-repro-data-oeis_displayed_terms.json OEIS fixtures (delivered repro/data/)
data/201-harmonic-repro-generated-exact_checks.json    recorded checks (delivered repro/generated/)
data/201-harmonic-repro-generated-manifest.json        run parameters and hashes (same)
data/201-harmonic-repro-generated-numerical_diagnostics.json  recorded diagnostics (same)
data/201-harmonic-repro-freud_generated-exact_checks.json     Freud companion checks (delivered repro/freud_generated/)
data/201-harmonic-repro-freud_generated-manifest.json         (same)
data/201-harmonic-repro-freud_generated-numerical_diagnostics.json  (same)
data/199-quartic-exact_checks.json                     recorded checks (delivered data/)
data/199-quartic-shifted_polynomials.json              shifted-moment polynomials (delivered data/)
data/199-quartic-manifests-source_manifest.json        source manifest with engine banner and epoch (delivered manifests/)
data/202-relcorr-requirements.txt                      pins (delivered requirements.txt)
data/202-relcorr-repro-requirements.txt                pins (delivered repro/; byte-identical to the previous)
data/202-relcorr-manifests-source_manifest.json        source manifest with engine banner and epoch (delivered manifests/)
data/202-relcorr-repro-data-fixtures.json              fixtures (delivered repro/data/)
data/202-relcorr-repro-generated-exact_checks.json     recorded checks (delivered repro/generated/)
data/202-relcorr-repro-generated-exact_data.json       recorded exact data (same)
data/202-relcorr-repro-generated-numerical_diagnostics.json  recorded diagnostics (same)
data/204-diagonal-requirements.txt                     pins (delivered requirements.txt)
data/204-diagonal-tables.tex                           generated coefficient table macro (delivered tables.tex)
data/204-diagonal-code-results-exact_checks.json       recorded checks (delivered code/results/)
data/204-diagonal-code-results-manuscript_checks.json  (same)
data/204-diagonal-code-results-numerical_diagnostics.json  (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit: the four PDFs
(481,252, 393,485, 389,440 and 418,021 bytes); the texts of Reports 199, 202
and 204 (Parts II–IV of `article.tex`); the delivered READMEs of Reports 199
(8,056 bytes), 202 (5,706) and 204 (7,308), and Report 201's (11,150),
staged at placement as `README.md` and replaced by this guide; the package
manifests of Reports 199, 201, 202 (1,757, 3,288, 2,721 bytes) and Report
204's `MANIFEST.sha256` (1,301 bytes), verified at the write; and Report 199's
`data/exact_values.json` (2,257,761 bytes) and Report 201's
`repro/generated/moments.json` (2,605,540 bytes), regenerated byte for byte at
intake by `code/exact.py --output` and `repro/check.py --out`.

**Delivered text that names the delivery layout or files not shipped.** The
programs and the two shipped reproduction READMEs (delivered names and
directories, manifests, the two large data files), and the reproducibility
sections of the four Parts (Sections 16, 30, 43 and 52, which describe "the
companion archive" and refer to its README). Rebuild the delivered layout
from the archives to rerun.

## Retrieving the delivered packages

```sh
T=$(mktemp -d); cd "$T"
for r in 199 201 202 204; do
  git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report$r.zip > R$r.zip && mkdir R$r && (cd R$r && unzip -q ../R$r.zip)
done
sha256sum R*.zip
# 3d8a699b123fb7554691cf0f7ca03530e5d4cd41d2cbbacfaa7bc6ca27ead5d9  R199.zip
# 571a7cad97c6387f0a202aeb213268ee4bbcb44901468273cfedb07da95c77a6  R201.zip
# 2b83e3588e251e3a3c275ccec937d62afd73d8369cdae5cbe2fde19fb05c8187  R202.zip
# c6b5724246f1a9c4f0d31cc3604b0cefe0acfcbe3e06268063c60d087a8d972a  R204.zip
```

Each extraction runs with its own README's commands (Python 3 with the pinned
packages; the two large data files are regenerated by
`Report199/code/exact.py --output` and `Report201/repro/check.py --out`).

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, xcolor, enumitem, fancyhdr, hyperref, longtable);
the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (107
pages after the independent check's notes; 106 at the write): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered texts build with 35, 22, 27 and 16 pages;
Reports 199 and 202 each have two underfull boxes in their bibliographies,
which the merged ragged bibliography removes).

## From the delivery READMEs

- **Report 201** (replaced as `README.md`): the package, the exact and Freud
  companions, the deterministic build, and the trust boundary in its own
  words: "The original 1999 theorem text was not directly inspected."
- **Report 199**: raw and comparison moments through 500 and cumulants
  through 160 (in the unshipped `exact_values.json`); comparison with
  fourteen displayed A338634 coefficients (indices 0–13), the b-file "not
  successfully retrieved and … not claimed checked"; finite checks are
  "consistency tests".
- **Report 202**: no new unconditional general-`p` coefficient, effective
  onset or first-proof claim; diagnostics "not proofs or certified error"
  bounds.
- **Report 204**: the reference toolchain (Python 3.12.14, pdfTeX of TeX Live
  2025), the files, exact checks against diagnostics, deterministic packaging;
  the leading A291333 equivalent is prior work.

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A290569, A216966, A218221, A227887, A338634 and A291333, and
`data/201-harmonic-repro-data-oeis_displayed_terms.json` holds displayed
OEIS terms; OEIS content is published by The OEIS Foundation
Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains
under that licence. No third-party PDF is shipped. Nothing was submitted to
the OEIS.

## Provenance

- Sources cited by the manuscripts: the OEIS entries; Claeys–Krasovsky–Minakov
  (2023); Kriecherbauer–McLaughlin (1999); Berg–Valent (1994); Conrad–Flajolet
  (2006); Flajolet–Gabarró–Pekari (2005); Avdoshkin–Dymarsky (2020);
  Dymarsky–Smolkin (2021); Flajolet (1980); Deb–Sokal (2024); DLMF; Askey–Wimp
  (1984); Drake (2007); Mastroianni–Milovanović (2008); Chen–Ismail (1998);
  Dai–Ismail–Wang (2014); Bender (1975); Bender–Richmond (1984); Borinsky
  (2018); Młotkowski (2009); Bożejko–Hasebe (2013); Defant–Lee (2025);
  Monteil–Nurligareev (2026); Mogul'skii (1976); Disanto–Munarini (2019); the
  ProveIt repository. Nothing added by the write.
- Batch 111 of `docs/incoming`, bundle Reports 199, 201, 202 and 204; arrival
  `60f54ea06`, placement `d451ef3d8`, written 7 October 2026.
