# Planar Eulerian Orientations: Exact Lambert Sectors, Logarithmic Corrections and Inverses (OEIS A324312, A277493, A324314)

**For `m = n + 2`, `L = log m`, `T = log L + C + γ`:
`a_n = κ₀ μ^m/(m² L²) {Σ_{j≤J} Q_j(T)/L^j + O_J((log L)^{J+1}/L^{J+1})}` with
six universal polynomials `Q_0, …, Q_5`; `a_n = κ₀ μ^m {h_m − k_m/2 +
O(m⁻⁴L⁻³)}` for the coefficients `h_m`, `k_m` of exact analytic Lambert
models, and every fixed number of such sectors; a relative correction
`2/(mL)` that no logarithmic truncation sees; smooth inverse charts with a
two-ceiling threshold bracket. All conditional on the published
`Δ`-continuation of Bousquet-Mélou and Elvey Price, whose proof for the
general family is only indicated.**

A research article dated 3 October 2026 ("Report 171" of a session bundle),
built from one manuscript. Its author line and PDF author field are empty
and its title block reads "Report 171": it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 171 (batch 109) | `Planar_Eulerian_Orientations_Lambert_Expansions_and_Inverses_Source.zip` (25 files, no wrapper directory, 3,455,433 bytes, SHA-256 `f0b45e63f38b…482a01cf2c7d1`), arrival commit `60f54ea06`; main file `Report171.tex` (564 lines, 14 pp.) | none: the package names no ProveIt commit and no repository path | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository's formal developments concerns planar maps or their
orientations. **Every statement about the counts is conditional** on
Propositions 8.2–8.3 of Bousquet-Mélou and Elvey Price (JCTA 2020); see
"The analytic input" below.

## Trust boundaries

- **The conditional input.** The global `Δ`-continuation of the inverse
  series `R` and its leading singular equivalent (BMEP Proposition 8.2,
  quartic; 8.3, general). For the general family, which carries A324312 and
  A277493, BMEP say the proof "closely follows the proof of Proposition 8.2
  given in [17, Sec. 8.3], and we will not give any details". The source
  says so itself (Section 3) and takes the proposition as input; the write
  adds Question 6.
- **What is proved by hand, granted the input.** Theorem 4.1, Theorem 5.1
  (the joint analytic reversion, branch identification and the
  absolute-value contour argument), Lemma 6.1 (a finite Hankel derivative
  transfer for the model coefficients alone, which needs no input),
  Theorem 6.2 and Theorem 7.1; the Lambert branch on the slit disk by a
  contraction argument. No proof uses a computation.
- **What rests on computation.** The explicit `U_1, U_2, U_3` (5.7),
  Appendix A, and `Q_0, …, Q_5` (6.9)–(6.11) are outputs of finite
  generators, computed by the shipped programs and checked there by
  substitution and by a second reversion; the write rederived all of them
  with its own code.
- **What is diagnostic.** Table 2, the "about 165% and 185%" leading
  overestimates, the chart values `x_J(y) − 1000`, all 110-digit numerics:
  no interval arithmetic. No effective constant or starting index exists.
- **What is prior.** The enumeration, the generating functions and the
  leading equivalents (BMEP Theorems 1.1–1.2), the quartic continuation
  (Bousquet-Mélou–Courtiel), and the inverse-log and reciprocal-Gamma
  transfer tools (Elvey Price–Guttmann). "The particular explicit formulas
  were not located in the inspected primary sources; this bounded
  inspection is not a claim of universal priority."

## What it proves

Planar maps with an Eulerian orientation, rooted with the root edge
oriented as the rooting (A324312, by edges; A324314, quartic, by vertices),
and A277493 (either root orientation, `= 2·A324312` for `n ≥ 1`). With `R`
the compositional inverse of the hypergeometric `Ω` (2.1),
`a_n = −r_{n+2}/d_0`, `d_0 = 4, 2, 3` (2.3); `μ = 4π`, `4√3π`;
`κ₀ = 1/16, 1/8, 1/18`; `C = 1 + log 4`, `1 + log 6` (Table 1). Statement
and equation numbers are the delivered ones.

- **Section 3 (`peo:sec:analytic`)**: the local singular equation (3.5)
  from the zero-balanced hypergeometric continuation, with
  `H = 1 + 4 log 2` or `1 + 3 log 3`, `δ = 3/2 − 1/α` (3.6).
- **Section 4 (`peo:sec:models`)**: the Lambert branch `v − Log v = Λ`,
  `Λ = C − Log s`, on the slit disk `D_s` (4.1)–(4.2); the models
  `F_0 = (1−z)/v`, `F_1` (4.4). **Theorem 4.1 (`peo:thm:two`)**:
  `r_m ρ^m = −A h_m + (A/2) k_m + O(m⁻⁴(log m)⁻³)` (4.5), with
  `h_m ~ 1/(m² log² m)`, `k_m ~ −4/(m³ log³ m)` (4.6) and so (1.3).
- **Theorem 5.1 (`peo:thm:fixed`)**: for each fixed `K`,
  `r_m ρ^m = −r_0 Σ_{j≤K} α^{-j} [z^m] M_j + O_K(m^{−K−2}(log m)^{−K−1})`,
  `M_j = (1−z)^j U_{j−1}(v)`, from the joint analytic reversion (5.1) and
  the triangular generator (5.6).
- **Lemma 6.1 (`peo:lem:Hankel`)** and **Theorem 6.2
  (`peo:thm:logarithms`)**: the finite derivative transfer with
  `c_j = [w^j] 1/Γ(−1−w)` (6.1) and the expansion (1.1) with
  `Q_0, …, Q_5` (6.9)–(6.11), leading coefficient `(−1)^j (j+1)`.
- **Theorem 7.1 (`peo:thm:inverse`)**: the chart `x_J(y)` (7.4), within
  `O(log q/q)` of the smooth comparison root (7.6), and
  `⌈x_J − ε_J⌉ ≤ N(y) ≤ ⌈x_J + ε_J⌉` (7.8) for `N(y) = min{n : a_n ≥ y}`.
- **Section 8 (`peo:sec:companion`)**: the ODE recurrence (8.1)–(8.2), the
  Lagrange formula (8.3), the model ODE `h h'' = −(h')³` (8.4),
  `F_1 = h² − ((δ+1)/3)(h³)'` (8.5), and Table 2.

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.1 (`peo:rem:oeis`)**: the OEIS entries quoted (next section).
- **Remark 3.1 (`peo:rem:input`)**: the analytic input as published, and a
  citation note (the section after next).
- **Remark 7.2 (`peo:rem:transseries`)**: the inversions against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `N(y)` is the staircase of
  `p0:def:three-inverses`; `p0:thm:staircase`(1) applies. (b) Theorem 7.1 is,
  **as stated and proved, an analogue** of `p0:thm:staircase`(2) (a direct
  bracket about an explicit chart); the write adds a **second route**: with
  `log 𝒜 = Li_J(x+2) + Ẽ`, `Ẽ` the piecewise-linear interpolation of the
  integer errors, `|ν_𝒜 − x_J| ≤ ε_J`, and `p0:thm:staircase`(1) gives (7.8).
  (c) **Instance on the real axis**: the Lambert equation (4.2) is
  `p0:thm:lambert-core` with `a_vol = 1`, `b_vol = −1`; its threshold
  `L_c = 1` is the source's `ℜΛ > 1`, its large root the source's
  `−W_{−1}(−e^{−C}s)`. (d) **Formal instance**: the large-`Λ` expansion of
  `v` behind (6.7) is `plt:thm:lw-template` with data `(1, −1, 0, 0)`, the
  pure Lambert case. (e) **Formal instance after `q = 1 + E`**: the joint
  equation (5.1) is `p0:thm:core-reversion` with `Λ_vol = 1 − w` over
  `Q[w, (1−w)⁻¹]`, which gives the rationality of `q_ℓ` with poles only at
  `w = 1`. (f) The comparison equation `Li_J(m) = log y` has the
  `p0:thm:lambert-core` core `bm − 2 log m`, but in the chart `Z_vol = m` its
  `log log m` terms break (H3) of `plt:thm:lw-template`: **not shown to be
  an instance**, and not claimed to be outside every chart.
- Section 1.1 (`peo:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); labels on Sections 1, 5.1, 6.2, 9 and
  Appendix B; notes after the abstract and at the ends of Sections 6, 8
  and 9; Question 6 in Section 9.

## The OEIS entries (Remark 1.1)

Read again on 6 October 2026 in the internal format; quoted verbatim.

- **A324312** (revision #18, 2 October 2025), offset 1: "Expansion of the
  generating function of rooted planar Eulerian orientations, counted by
  edges."; data `1, 5, 33, 252, 2108, …` (22 terms); "G.f.:
  (1/(4t^2))*(t-2t^2-R(t)) where R(t) is A324311." and "a(n) = A277493(n)/2.
  - _Andrew Elvey Price_, Dec 12 2024".
- **A277493** (revision #53, 21 December 2024), offset 0: "Number of planar
  rooted Eulerian orientations (i.e., planar directed Eulerian maps with
  in-degree and out-degree equal for each vertex) with n edges."; data
  `1, 2, 10, 66, 504, …` (23 terms); "G.f.: (1/(2*t^2))*(t-R(t)) where R(t)
  is the g.f. of A324311." and "a(n) = 2*A324312(n) for n>0."
- **A324314** (revision #7, 22 February 2019), offset 1: "Expansion of the
  generating function of quartic rooted planar Eulerian orientations,
  counted by vertices."; data `4, 35, 402, 5334, …` (20 terms); "G.f.:
  (1/(3t^2))*(t-3t^2-R(t)) where R(t) is A324313."

No entry states an asymptotic formula. The write's own exact Lagrange
inversion (`m ≤ 40`) reproduces every printed term (22, 22 positive-index,
20) and makes the ODE residual (8.1) vanish through `t^38`; the shipped
fixture transcribes 22, 5 and 20 of these terms, all agreeing. Nothing was
submitted to the OEIS.

## The analytic input (Remark 3.1)

Read in arXiv:1803.08265v2, the version the source names as inspected.
Section 8.2 defines the `Δ`-domain as in (3.1). **Proposition 8.2**
(quartic): radius `√3/(12π) = 1/(4√3π)`, `Δ`-analyticity, and
`R(t) − 1/27 ~ (1/6)(1 − t/ρ)/log(1 − t/ρ)`; "the first part of the
following result is the case u = −1 of [17, Prop. 8.4]" (Bousquet-Mélou–
Courtiel). **Proposition 8.3** (general): radius `1/(4π)` and
`R(t) − 1/16 ~ (1/4)(1 − t/ρ)/log(1 − t/ρ)`, then "The proof closely
follows the proof of Proposition 8.2 given in [17, Sec. 8.3], and we will
not give any details." The source's account is accurate and its
amplitudes `A = 1/4, 1/6` agree with these forms.

**Citation note (dated, not a mathematical correction).** The source
attributes the differential equations (8.1) to "[BMEP, Section 7]" (Section
8 and Appendix B). In arXiv:1803.08265v2 they are in Section 8.1, "Nature of
the series"; Section 7 ("Solution for general Eulerian orientations")
contains no such equation. The published version was not read. The
equations are right (checked by the write to `t^38`, by the companion to
`t^1001`).

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- The leading equivalents and the global continuation are BMEP's and are
  not re-proved; the general proposition's proof details are omitted there.
- The analytic tools (inverse-log corrections, reciprocal-Gamma transfer,
  the DLMF continuation formula, Lambert branches) are not new; no
  universal-priority claim.
- No general-weight phase diagram; the refined preprint (arXiv:2503.15046v3,
  Section 6.4, "Predicted singular behaviour") is motivation only.
- Fixed `K` only: no convergence of the sector sum, no uniformity in growing
  `K`, no optimal truncation, no complete transseries with exponentially
  small terms.
- No effective constants or starting indices; no uniform `o(1)`
  approximation of `N(y)`; no `N(y) = ⌈x_J(y)⌉`; exact identification needs
  exact counts.
- Universality of `Q_j` only across the two families; diagnostics not
  interval-certified; finite checks do not certify the analytic remainders;
  the OEIS observations are dated.

The write adds: its checks are floating or finite; Remark 3.1 corrects one
citation and no mathematics; Remark 7.2 claims no novelty for any
inversion.

## Further questions

Section 9 of the article (`peo:sec:questions`) keeps the source's five
directions (effective error constants; large sector order; higher
coefficient accuracy; parameter-dependent models; certified inversion) and
adds, under Vladimir's standing rule of 4 October 2026:

6. **Continuation for the general family** (`peo:q:continuation`): write out
   the proof of BMEP Proposition 8.3 (the quartic argument of
   Bousquet-Mélou–Courtiel, Section 8.3, with `Ω_g`; BMEP name the
   nonnegativity of the coefficients of `t − R(t)` as one key ingredient).
   Until then the count statements for A324312 and A277493 are
   conditional.

**Nothing in the source was found to be wrong**; one citation is corrected
by a dated note (above). No claim was refuted and none moved, other than
the conditional input made a question.

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 24/24. The
  dossier read the manuscript and found no error, checked (1.3) from (4.6)
  and the contour argument, and reran the companion on copies: `exact`
  (50 s) byte-identical to the delivered `outputs/exact.json`, `symbolic`,
  `diagnostics` and the three `inverse` runs identical, the
  `test_companion.py` receipt equal as JSON; `test_build.py` fails on
  Windows (its synthetic tree is written with CRLF, then hash-compared).
- At the write (6 October 2026; same machine; Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0), with its own code: Table 1 (`ρ = Ω(r_0)` at 40 digits);
  `H`, `C`, `δ_1, …, δ_4` (both families) from the digamma definition; the
  Lagrange inversion, ODE residual and OEIS comparison above; `Q_0, …, Q_5`
  from the generator (6.7) and `c_j`; `U_1, U_2, U_3` of both families from
  (5.6); (8.4) and (8.6) against direct Taylor coefficients of `F_0`
  (agreement to `10⁻⁵²`); Table 2 to its printed digits, the leading
  overestimates `+1.6475`, `+1.8500`, and `x_J(y) − 1000 = −0.39135215,
  −0.0026443594, +0.030087643` at `y = A324312(1000)` from its own
  60-digit model coefficients; `m L (a_n/(κ₀μ^m h_m) − 1) = 1.0177`,
  `0.9082` at `n = 1000` (the `(1+o(1))` of (1.3) is slow; the exact first
  sector gives `1.0180`, `0.9085`). Every proof was rechecked line by line.
  The companion rerun from the shipped files (Route B below): `exact` (18 s,
  byte-identical to the archive's `outputs/exact.json`), `symbolic`,
  `diagnostics`, the three `inverse` runs, all byte-identical to the shipped
  outputs; `test_companion.py` receipt equal as JSON.
- Sources read by the write: the OEIS entries; BMEP arXiv:1803.08265v2
  (Theorems 1.1–1.2, Section 2, Sections 7 and 8); the refined preprint's
  abstract page (v1 19 March 2025, v2 1 June 2026, v3 2 June 2026) and the
  title and opening of v3 Section 6.4; the transseries volume. Not read: the
  published BMEP, Bousquet-Mélou–Courtiel, Elvey Price–Guttmann, the DLMF
  pages.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
7.2(a)–(b) applies is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these sequences is.

**The transseries volume.** Remark 7.2: the threshold a staircase instance;
Theorem 7.1 an analogue of `p0:thm:staircase`(2) as proved and a
consequence of (1) with the write's interpolation; the Lambert branch an
instance of `p0:thm:lambert-core`; its large-`Λ` expansion a formal
`plt:thm:lw-template` instance; the joint reversion a formal
`p0:thm:core-reversion` instance. The source expressly proves no
transseries ("does not establish … a complete transseries including
exponentially small terms"), which is why it is filed here and not in
`Analysis/Transseries/`.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a110058-square-contingency-tables` and `a380592-tied-football-seasons`
cite a cumulant expansion for counting Eulerian orientations of a fixed
graph, a different object; no shared result, so no reciprocal note is
proposed.

**Stale claims.** Before batch 109 no file of the repository named A324312,
A277493 or A324314, and no report counted planar Eulerian orientations.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `a` (family parameter), `a_n`, `a_j`;
`h_m`, `h_j`, `h`; `q` (`Y/b`) against the reversion unknown `q(η,w)`;
`C`, `c_j`, `c`; `δ`, `δ_j`; `A`, `α`, `κ₀`; `T`, `t`, `T_q`; `L`, `Li_J`,
`L_q`; the three `w`; `D`, `D_s`; `M_j`, `M_J`; `E_K`, `E_j`; `K`, `K_J`,
`k`, `k_m`; `ρ`, `μ`, `r`, `r_m`. No symbol was renamed; the volume's
colliding letters carry the subscript "vol" in Remark 7.2.

## Labels

Every label carries the prefix `peo:` (none existed in the repository). The
manuscript's 58 labels (`eq:` 43, `sec:` 7, `thm:` 4, `tab:` 2, `lem:` 1,
`app:` 1) were prefixed before anything cited them, and the 45 references
to them (33 `\eqref`, 12 `\ref`) updated. The write added 10:
`peo:sec:scope`, `peo:sec:joint`, `peo:sec:generator`, `peo:sec:questions`,
`peo:app:sources`, `peo:sec:provenance`, `peo:rem:oeis`, `peo:rem:input`,
`peo:rem:transseries`, `peo:q:continuation`. The report has 68 labels;
builds of the delivered text and of this one give all 58 delivered labels
the same numbers (aux files compared). The added statements are the last of
their sections, the added subsection follows the last delivered text of
Section 1, and nothing was inserted before a delivered display, table or
statement.

## Files

```text
README.md                                   this guide (replaces the delivery README)
article.tex                                 the report (delivered Report171.tex; labels prefixed, [write] additions)
article.pdf                                 compiled report, 20 pages
code/companion.py                           exact, symbolic, diagnostics and inverse commands (delivered code/)
code/test_companion.py                      positive and deliberate-failure tests (delivered code/)
code/test_build.py                          build-guard tests; fail on Windows (delivered code/)
code/build.py                               clean-tree PDF and ZIP builder, TeX Live (delivered at the root)
data/BUILD-INFO.json                        fixed epoch and tool versions (delivered at the root)
data/requirements.txt                       sympy==1.14.0, mpmath==1.3.0 with comments (delivered at the root)
data/fixtures-SHA256.json                   fixture hashes, read by the companion (delivered fixtures/)
data/fixtures-oeis_prefixes.json            OEIS terms transcribed 3 October 2026 (same)
data/fixtures-eulerian_coefficients.json    frozen Q_0..Q_5 and related formulas (same)
data/fixtures-local_sector_coefficients.json  frozen U_0..U_3 and deltas (same)
data/fixtures-provenance.json               primary sources and versions (same)
data/outputs-symbolic.json                  recorded output (delivered outputs/)
data/outputs-diagnostics_110d.json          recorded 110-digit diagnostics (same)
data/outputs-inverse_A324312_logy1000.json  recorded chart at log y = 1000 (same)
data/outputs-inverse_A277493_logy1000.json  (same)
data/outputs-inverse_A324314_logy1000.json  (same)
data/outputs-tests.json                     test receipt, normal Python (same)
data/outputs-tests_optimized.json           test receipt, python -O (same)
data/outputs-build_tests.json               build-test receipt, normal Python (same)
data/outputs-build_tests_optimized.json     build-test receipt, python -O (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next sections):
`Report171.pdf` (the delivered 14-page PDF, 313,658 bytes);
`SHA256SUMS.json` (2,338 bytes, 24 entries, verified at placement; repository
policy ships no checksum manifests); `outputs/exact.json` (3,024,729 bytes,
regenerable, see below); and the delivery `README.md` (10,420 bytes), staged
at placement and replaced by this guide (summarized below).

## Reconstructing the excluded data

`outputs/exact.json` (1000 exact terms per family, the inverse coefficients
through `r_1002`, the Lagrange and ODE checks) is not shipped: no shipped
program reads it, and it regenerates byte for byte. In the delivered layout
(Route A or B below):

```sh
python code/companion.py exact --n 1000 --lagrange-m 81 --output NEW-exact.json
sha256sum NEW-exact.json   # d22f06b79d604556021c54802b8cc2011a968efc8730073cd665d731bc5af023, 3,024,729 bytes
```

Standard library only; 18 s at the write (about 50 s at placement). Or
extract it from the archive:

```sh
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Planar_Eulerian_Orientations_Lambert_Expansions_and_Inverses_Source.zip > a.zip
unzip -p a.zip outputs/exact.json > exact.json
```

**Delivered text that names the delivery layout or files not shipped.** The
delivery README (summarized below) lists `outputs/exact.json`;
`code/companion.py` reads `fixtures/` at `../fixtures` from its own
directory (`ROOT = Path(__file__).resolve().parent.parent`);
`code/build.py` expects `Report171.tex`, `README.md`, `requirements.txt`,
`code/`, `fixtures/` at the package root and writes `outputs/`;
`code/test_build.py` and `code/test_companion.py` use the delivered names;
`data/fixtures-provenance.json` lists five upstream working files
(`check_exact_independent.py`, `check_eulerian.py`, `derive_eulerian.py`,
`derive_local_sectors.py`, `check_lambert_models.py`) by SHA-256 that were
never in the package; `data/BUILD-INFO.json` describes `SHA256SUMS.json`;
and Section 8.3 of the article ("The distribution contains this source and
PDF, … checksums", "The README"). So no program runs under the shipped
names; use one of the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Planar_Eulerian_Orientations_Lambert_Expansions_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # f0b45e63f38bc04b29e3185a854da8f97fbd4c9514d066a8389482a01cf2c7d1, 3,455,433 bytes
cd "$T" && unzip -q a.zip
```

The delivery README gives a Python snippet that checks `SHA256SUMS.json`
(24 entries).

## Rerun the checks (on a scratch copy)

Python 3.10 or later with SymPy 1.14.0 and mpmath 1.3.0. Never run anything
in the repository. Each `--output` must be a new file.

**Route A, delivered layout**, from `$T`:

```sh
python code/companion.py verify --n 1000 --lagrange-m 81
python code/companion.py symbolic --output NEW-symbolic.json
python code/companion.py diagnostics --n 1000 --digits 110 --prefix 60 --output NEW-diagnostics.json
python code/companion.py inverse --sequence A324312 --log-y 1000 --digits 110 --output NEW-inverse.json
python code/test_companion.py
python -O code/test_companion.py
python code/test_build.py          # POSIX only
python build.py --output /new/path/Report171-rebuilt.zip   # TeX Live, POSIX
```

**Route B, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a324312-planar-eulerian-orientations
B=$(mktemp -d); mkdir -p "$B/code" "$B/fixtures" "$B/outputs"; cd "$B"
cp "$R"/code/companion.py "$R"/code/test_companion.py "$R"/code/test_build.py code/; cp "$R/code/build.py" .
for f in "$R"/data/fixtures-*; do n=$(basename "$f"); cp "$f" "fixtures/${n#fixtures-}"; done
for f in "$R"/data/outputs-*; do n=$(basename "$f"); cp "$f" "outputs/${n#outputs-}"; done
cp "$R/data/BUILD-INFO.json" "$R/data/requirements.txt" .; cp "$R/article.tex" Report171.tex
```

then the commands of Route A. At the write, in this layout, `exact` gave the
archive's `outputs/exact.json` byte for byte (18 s); `symbolic` (about 15 s
together with the three `inverse` runs), `diagnostics` (22 s) and the
`inverse` runs gave the shipped outputs byte for byte; `test_companion.py
--output` gave a receipt equal as JSON to `outputs/tests.json` (19 s; the
bytes differ by CRLF on Windows). `test_build.py` fails on Windows (CRLF in
its synthetic files, then a hash mismatch); `build.py` (TeX Live, POSIX)
was not run. Use `py` where `python` is not on the path.

## Build the PDF

pdfLaTeX (geometry, fontenc, lmodern, microtype, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, hyperref, enumitem,
fancyhdr); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 20
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 14 pages). The
delivered byte-identity claims (`SOURCE_DATE_EPOCH`, suppressed PDF dates)
apply to `Report171.tex` under the delivering toolchain (pdfTeX, TeX Live
2025/dev), not to this build.

## From the delivery README

The delivery README (replaced by this guide) said that "The programs do not
independently prove the published global continuation theorem or turn
asymptotic big-O constants into finite-index bounds"; listed the contents,
including `outputs/exact.json` ("1000 exact positive-index terms for each
family, inverse coefficients through `r_1002`, Lagrange checks through
`r_81`, and full ODE residual checks through `t^1001`"); described the
conventions (index origins, root convention, `m = n + 2`) and the OEIS
fixture ("a dated transcription of the retrieved pages … 22 A324312 terms,
20 A324314 terms, and the five A277493 terms"); gave the requirements, the
archive rebuild (`python build.py --output …`, new destinations only,
`SOURCE_DATE_EPOCH` 1790985600, `ZIP_STORED`), a Python snippet verifying
`SHA256SUMS.json`, the individual commands (`exact`, `symbolic`, `verify`,
tests, and the optional `diagnostics` and `inverse`, whose `--log-y` is the
natural logarithm of the target); and said that "Neither numerical command
uses interval arithmetic" and that "Retaining the exact Lambert model is
essential for resolving the next algebraic sector".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A324312, A277493 and A324314, and the fixture transcribes some of
their terms; OEIS content is published by The OEIS Foundation Inc. under
CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains under
that licence. Short quotations of Bousquet-Mélou and Elvey Price are for
attribution. No third-party PDF is shipped. Nothing was submitted to the
OEIS.

## Provenance

- Sources cited by the manuscript: Bousquet-Mélou–Elvey Price, JCTA 172
  (2020) (arXiv:1803.08265v2); Bousquet-Mélou–Courtiel, JCTA 135 (2015)
  (arXiv:1306.4536v1); Elvey Price–Guttmann (arXiv:1707.09120v3);
  Bousquet-Mélou–Elvey Price, refined enumeration (arXiv:2503.15046v3);
  DLMF 15.8.10 and 4.13; OEIS A277493, A324312, A324314.
- Batch 109 of `docs/incoming`, bundle Report 171; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report171.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
