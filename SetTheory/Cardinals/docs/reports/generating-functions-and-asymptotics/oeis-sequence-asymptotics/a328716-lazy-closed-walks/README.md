# Lazy Closed Walks in Growing Dimension: All Fixed Orders, Parity-Conditioned Poisson Laws and Occupied-Axis Fluctuations (OEIS A328716, A328718); Part II: Uniform Lattice-Bridge Asymptotics and a Gaussian Return Bound Disproved

**For the number `a_n` of `n`-step closed walks in `ℤ^n` with steps `0`,
`±e_i` (A328716): `a_n = C_ε (dn)^n {Σ_{ℓ≤M} c_{ε,ℓ} n^{−ℓ} + O(n^{−M−1})}`,
`ε = (−1)^n`, for every `M`, with Bessel definitions of Kotěšovec's constants
`d = F(r)/(er)` and `C_±` and explicit `c_{ε,1}, c_{ε,2}, c_{ε,3}`; an absolute
complex-uniform marked expansion, valid at the zeros of its amplitude; the
zero-step count to every order in a weighted `ℓ¹` norm about a
parity-conditioned Poisson law; occupied axes Gaussian on scale `√n`,
asymptotically independent of the zero steps, with a parity-dependent mean
offset; parity inverse brackets with an eventual global width at most one; a
compact proportional `N/D` extension.**

**Part II (added 7 October 2026): an exact counterexample to the universal
Gaussian return bound `p_{2n}^{(d)}(0,0) ≤ 2(d/(4πn))^{d/2}` (Ball–Sterbenz
2005, display (1.3), a conjecture of Lyons; Felker–Lyons 2003, (2.3)) at
`d = 16`, `2n = 26`, confirmed by the write with its own exact count; a
scalar saddle expansion for weighted closed walks with steps `0, ±e_i`,
uniform in the dimension and in all nonnegative activities, to every fixed
order, with leading relative error at most `24/m` (`N = 2m + ε`); the dense
Gaussian threshold `D³/N² → 0`, with missing factor `exp(1/(48s²))` at
`N/D^{3/2} → s` and last-failure thresholds `~ D²/12` (nonlazy) and `~ D²/9`
(lazy); and, for `m²/D = O(1)`, a joint Poisson law of repeated axes and
parity-conditioned idle steps with error `O(1/m)` in weighted `ℓ¹`. It
answers Part I's Question 2 for the counts at both ends of `N/D`.**

Two Parts. Part I is a research article dated 3 October 2026 ("Report 179"
of a session bundle), built from one manuscript. Its author line and PDF author field read
"Research report 179": it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data. Part II is a research manuscript dated 7 October 2026,
"Prepared for Vladimir Reshetnikov" (title page; PDF author "Research
manuscript prepared for Vladimir Reshetnikov"); it names no person or tool
as author and has no AI-assistance line.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 179 (batch 109) | `Lazy_Closed_Walks_Asymptotics_and_Inverses_Source.zip` (26 files, no wrapper directory, 617,713 bytes, SHA-256 `e433f40b68ba…e5473b44f613`), arrival commit `60f54ea06`; main file `Report179.tex` (701 lines, 16 pp.) | `83befe707` (ProveIt, 3 October 2026, "Transfer macro continuation sharing to the complete projective compiler"; exists), the commit of the source's bounded repository comparison | `f7e9e5c2f` (batch 109) | Part I (Sections 1–12) |
| 02 | *Uniform Lattice-Bridge Asymptotics* (non-Gowers intake NG1, manuscript 04) | `uniform-lattice-bridges-research.zip` (24 files in one wrapper directory, 838,687 bytes, SHA-256 `f736b7f99454…3eaff7bb6`, no checksum manifest), arrival commit `fe7165a3c`; main file `article.tex` + 9 section files (2,139 lines, 31 pp.) | `136e70702` (ProveIt, 7 October 2026, 17:07:16 UTC; after Part I's write and check) and `adc7f1241b42` of the `math` repository (not checked) | `3cf0a2758` (12 files, prefix `02-bridges-`) | Part II (Sections 13–21; Section 13 added by the write) |

**Status:** Part I is AI-assisted (as its status note records); Part II
carries no statement either way. Both Parts are unrefereed and not
formalized: no Lean or Rocq declaration exists for any statement of this
report.

## Trust boundaries

Part I:

- **What is proved by hand.** Proposition 2.1, Lemma 3.1 and Theorems 4.1,
  6.1, 7.1, 8.1 and 9.1: the Bessel-product count, a two-arc saddle analysis
  with an absolute integrated remainder, Cauchy estimates on a larger disk,
  an analytic moving saddle with Lévy's continuity theorem, and monotone
  parity brackets.
- **What rests on computation.** `c_{ε,2}`, `c_{ε,3}` (22)–(23) and higher
  orders come from the finite algorithm of Section 4, checked by the shipped
  programs (exact `Fraction` arithmetic and two independent routes).
- **What is diagnostic.** Every decimal, including the table of Section
  10.3: high-precision, not interval-certified.
- **What is prior.** The exact formula (Gutkovskiy) and the numerical leading
  equivalent (Kotěšovec), both in the OEIS; the Bessel walk generating
  function (Gessel–Weinstein–Wilf 1998, equation (2)); the large-powers method
  with full expansions, compact-ratio uniformity and vanishing multipliers
  (Flajolet–Sedgewick, Theorem VIII.8).

Part II:

- **What is proved by hand.** Theorem 15.1 by an exact finite certificate
  (integer arithmetic and a rational lower bound for `π`); Theorems 16.2,
  17.1, 18.1, 18.2 and 19.1, Corollaries 16.3, 16.5, 19.2–19.4 and
  Proposition 17.3: a parity reduction to entire functions with negative real
  zeros, the Poisson–binomial representation with `m/2 ≤ B ≤ m`, a uniform
  local Edgeworth expansion with explicit leading constant `12/B`, a
  coefficient-transfer lemma for the sparse range, and the large-argument
  Bessel expansion for the dense range. The fixed-dimension coefficients of
  Subsection 19.1 are derived with the remainder in outline.
- **What rests on computation.** The counterexample's integers (two exact
  routes in the shipped verifier, a third by the write); the 1,303 endpoint
  comparisons and 444 exact checks of the shipped programs.
- **What is diagnostic.** The tables of Section 20 (the 24 dense entries are
  saddle evaluations through `E_2`, not enumerations) and the figures; no
  interval arithmetic.
- **What is prior.** The Bessel walk generating function
  (Gessel–Weinstein–Wilf); real zeros and Bernoulli representations (Bender,
  Pitman); local Edgeworth theory (Dolgopyat–Hafouta); the fixed-`d` eventual
  bound of Ball–Sterbenz.

## What Part I proves

`F(z) = I_0(2z)`, `𝒟 = z d/dz`; `r` solves `2rI_1(2r)/I_0(2r) = 1`,
`b = 4r² − 1`; `d = F(r)/(er)`, `C_ε = E_ε(r)/√b`, `E_ε(t) = e^t + εe^{−t}`.
Equation and statement numbers are the delivered ones (the article numbers
equations consecutively).

- **Proposition 2.1 (`lcw:prop:exact`)**: `A_{N,D}(u) = N![z^N] e^{uz} F(z)^D`
  (2), the joint law (3), and `a_{n+1} > a_n` for `n ≥ 1` (an injection).
- **Lemma 3.1 (`lcw:lem:saddle`)** and (7)–(9): the saddle, the constants and
  the cumulants as polynomials in `b`.
- **Theorem 4.1 (`lcw:thm:absolute`)**: (14)–(15), uniformly for complex
  `|u| ≤ R`, with an absolute remainder; Remark 4.2 at the zeros of
  `E_ε(ru)`.
- Section 5: `c_{ε,1}`, `c_{ε,2}`, `c_{ε,3}` (21)–(23) and their table.
- **Theorem 6.1 (`lcw:thm:weighted`)**: the weighted `ℓ¹` expansion (26) about
  `J_ε` = Poisson(`r`) conditioned on parity `ε`, with `Q_{ε,1}` (27).
- **Theorem 7.1 (`lcw:thm:occupation`)**: `(K_n − np)/√n ⇒ 𝒩(0, τ²)` (31),
  jointly with `J_n` (32), and `E K_n = np − (q/b)(v_ε + (b−1)/2 − 1/b) +
  O(1/n)` (33).
- **Theorem 8.1 (`lcw:thm:inverse`)**: parity brackets (40) about the roots of
  the carriers (38) and `L_M ≤ ν(X) ≤ U_M`, `U_M − L_M ∈ {0, 1}` (41); the
  closed form `t_{ε,0} = Y_ε/W_0(dY_ε)` (42).
- **Theorem 9.1 (`lcw:thm:ratio`)**: the compact proportional extension
  (43)–(44).
- Section 10: three finite counting descriptions (45)–(51) and the
  diagnostics table.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.1 (`lcw:rem:oeis`)**: the OEIS entries quoted and the b-file
  compared (next section).
- **Remark 8.2 (`lcw:rem:transseries`)**: the inversions against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `ν(X)` is the staircase `N_*` of
  `p0:def:three-inverses`, and `ν = min_ε ν_ε` is `p0:thm:staircase`(4) with
  `r = 2` (`p0:rem:parity-instances`). (b) The parity brackets of Theorem 8.1
  are, **as stated and proved, an analogue** of `p0:thm:staircase`(2) inside
  each class; the write adds a **second route** through part (4) with class
  interpolations; the width-one statement is the source's own. (c)
  **Instance**: the closed form (42) is `p0:prop:factorial-core` with
  `κ = 1`, `d_vol = log d`; its large-`Y` expansion a **formal**
  `plt:thm:lw-template` instance `(1, 1, 0, log(1 + t log d))` in the chart
  `Z_vol = log t`. (d) **Formal instance after `t = t_{ε,0}(1+E)`**: the
  carriers for `M ≥ 1` are `p0:thm:core-reversion` with `Λ_vol = 1 + 1/L`.
  (e) The full carrier equation for `M ≥ 1` is **not shown to be an
  instance** of `plt:thm:lw-template` ((H3) fails in the chart of (c)); not
  claimed to be outside every chart.
- **Remark 9.2 (`lcw:rem:rows`)**: a proof of the A328718 row conjecture
  (section after next).
- Section 1.1 (`lcw:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); notes after the abstract, at the end of
  Section 3 (three rounded constants), in Section 10 (the diagnostics
  rechecked, the shipped layout), at the end of Section 11 and at the end of
  Section 12.

## What Part II proves

`N = 2m + ε`, `ε ∈ {0, 1}` (Part II's `ε` is a parity remainder, Part I's a
sign); `F(t) = Σ t^k/k!² = I_0(2√t)`, `H_0(t) = cosh √t`,
`H_1(t) = sinh √t/√t`; activities `a_i, b_i` (`c_i = a_i b_i`) and `λ`
(idle). Statement and equation numbers are those of the written report; the
manuscript's Section `k` is Section `k + 13`.

- **Theorem 15.1 (`lcw:ulb:thm:lyons-counterexample`)**: `p_{26}^{(16)}(0,0)
  = 5630493790109507827003978475/2^{118} > 2(4/(13π))^8`, with ratio
  `> 4001/4000`: an exact counterexample to (15.1), the universal bound of
  Ball–Sterbenz's display (1.3) (Lyons's conjecture; Felker–Lyons (2.3)).
- **Proposition 16.1, Theorem 16.2 (`lcw:ulb:thm:global`)**: `W_N =
  N! λ^ε [t^m] H_ε(λ²t) Π F(c_i t)`, and `W_N/L_N = Σ_{s≤K} E_s +
  O_K(m^{−K−1})` uniformly in `D` and in all nonnegative activities, with
  `m/2 ≤ B ≤ m` (16.8); **Corollary 16.3**: `|W_N/L_N − 1| ≤ 12/B ≤ 24/m`
  for every `m > 0`; **Corollary 16.5**: the same for prescribed endpoints.
- **Theorem 17.1, Proposition 17.3**: the uniform Poisson–binomial local
  expansion and the explicit bound `|√(2πB) P(S = m) − 1| ≤ 12/B`.
- **Theorems 18.1–18.2 (`lcw:ulb:sp:thm:count`, `lcw:ulb:sp:thm:law`)**: for
  `θ = m²/D ≤ K` and `β = λ√(m/D) ≤ B`, the count (18.2) with the first
  correction (18.3), the joint law of idle steps and repeated axes in
  weighted `ℓ¹` (18.5), `E U = θ²/(36m) + O(m^{−2})` (18.6) and the
  occupied-axis deficit in total variation (18.7).
- **Theorem 19.1 (`lcw:ulb:thm:dense-gaussian`)**: `log(R_{N,D}/G_{N,D}) =
  −3D/(16N) + D³/(48N²) + O(D²/N² + D⁴/N³ + 1/N + e^{−N/(4D)})`, uniformly for
  `N/D ≥ ρ_0`; the Gaussian estimate is relatively correct iff `D³/N² → 0`.
  **Corollaries 19.2–19.4**: the nonlazy version (19.9), no constant repairs
  the bound (`N ~ D^{4/3}`), the signs at `N/D² → s`, and the thresholds
  `T_0(D) ~ D²/12`, `T_1(D) ~ D²/9`. Subsection 19.1: for fixed `D`,
  `R/G = 1 − 3D/(16N) + D(32D² − 21D − 8)/(1536N²) + O_D(N^{−3})`.

Added by the second write (7 October 2026), marked `[write]`:

- Section 13 (`lcw:ulb:sec:front`: the manuscript, what Part II answers in
  Part I, what the write checked, non-claims, reading conventions).
- Dated notes at the end of each of Sections 14–21; in Part I, an editorial
  note after the status note and notes at the ends of Sections 9 and 12.
- **Computed by the write**: a third exact count of the counterexample and an
  interval-arithmetic decision; a finite scan of the conjecture for
  `d ≤ 40`, `n ≤ 200` (and `d ≤ 16`, `n ≤ 500`): `d = 16` fails only at
  `2n = 26`, each `17 ≤ d ≤ 40` on one run of `n`, no failure for `d ≤ 15` in
  that range (no minimum dimension claimed); exact `R/G` at `D = 100`; the
  fixed-`D` second coefficient from exact counts. **Drawn by the write**:
  on a compact ratio with a real marker, Part II's leading term and Part I's
  Theorem 9.1 agree to relative `O(1/D)`; Theorem 19.1(i) at fixed `D` gives
  Part I's Remark 9.2 by a second route.

## The OEIS entries (Remark 1.1)

Read on 7 October 2026 in the internal format; quoted verbatim.

- **A328716** (revision #38, 27 October 2019), offset 0, by Seiichi Manyama:
  "Constant term in the expansion of (1 + x_1 + x_2 + ... + x_n + 1/x_1 +
  1/x_2 + ... + 1/x_n)^n."; Heinz's walk comment; "a(n) = n! * [x^n] exp(x) *
  BesselI(0,2*x)^n. - _Ilya Gutkovskiy_, Oct 26 2019"; "a(n) ~ c * d^n * n^n,
  where d = 0.8047104059195202206625458331930618795... and c =
  2.12946224998808159475495497... if n is even and c =
  1.4189559976544232606562785... if n is odd. - _Vaclav Kotesovec_, Oct 27
  2019"; b-file `n = 0..398` (Manyama; terms 0–199 from Heinz).
- **A328718** (revision #35, 30 October 2019), the array `T(n,k)` (dimension
  `n`, `k` steps): "Conjecture: Row r is asymptotic to (2*r+1)^(n + r/2) /
  (2^r * (Pi*n)^(r/2)). - _Vaclav Kotesovec_, Oct 27 2019", and column
  polynomials.

Kotěšovec's `d` and both `c` agree to every printed digit with the article's
`d`, `C_+`, `C_−` (his decimals are truncations); Theorem 4.1 at `M = 0`
proves his equivalent, for which the entry gives no proof. The write compared
all 399 b-file terms with the exact integer convolution of Section 10, and 44
of them with a direct rational power of `F`: all agree; `a_n` is strictly
increasing from `n = 1`, `a_0 = a_1`. Nothing was submitted to the OEIS.

## The rows of A328718 (Remark 9.2)

For fixed dimension `D`, `A_{N,D}(1) ~ (2D+1)^{N+D/2}/(2^D (πN)^{D/2})` as
`N → ∞`: Kotěšovec's conjecture in A328718 is true. The write proves it as
the local central limit theorem for the lazy walk: Fourier inversion with
`φ(θ) = (1 + 2Σcos θ_i)/(2D+1)`, which equals `1` only at `θ = 0` and never
`−1`, and Laplace's method at `θ = 0`. Exact counts give
`N(ratio − 1) = −0.1875, −0.3747, −0.5614` at `N = 400` for `D = 1, 2, 3`.
Row 1 is A002426 (central trinomial coefficients). The argument is classical,
no novelty is claimed, and it is a fixed-dimension statement: Theorem 9.1's
compact-ratio regime excludes fixed `D`, and the source's "not an unresolved
problem being solved by this proportional-dimensional argument" stays
accurate. (Added after the independent check of 7 October 2026: the proof
re-derived and correct; the `1/N` term is `−3D/16`, from the quartic term of
`log φ` averaged against the Gaussian, and Richardson extrapolation of the
exact counts from `N = 200, 400` gives `−0.1875002, −0.375001, −0.562508`.
Numerical corroboration of the standard Edgeworth term, not a proved
second-order theorem.)

## What is not claimed

Part I, from the source, kept in the article (collected in Section 1.1):

- The exact formula and numerical leading equivalent are in the OEIS; the
  Bessel walk generating function and the large-powers machinery are
  classical; no open-problem resolution and no historical priority ("bounded
  evidence, not an absence certificate"); priority for the individual
  probability refinements "remains unestablished".
- Poincaré expansions at fixed order only: no convergence, no growing order,
  no computable constants or onsets, no certified finite-input inverse
  calculator.
- The weighted expansion is signed; the occupation limits are weak limits,
  not total-variation convergence to a Gaussian.
- Nothing treats `ρ → 0`, `ρ → ∞` or fixed `D`; diagnostics are not
  interval-certified; no OEIS record or external repository edited.

The write adds: its checks are floating or finite; Remark 9.2 proves a
classical fixed-dimension statement with no novelty claimed; Remark 8.2
claims no novelty for any inversion.

Part II, from the manuscript (collected in Section 13.4):

- No historical priority for the counterexample or the combined conclusions,
  and no minimum dimension or length ("No claim that this is the smallest
  possible dimension or the shortest possible counterexample is needed"); the
  final Ball–Sterbenz journal PDF not inspected.
- The real-zero, Bernoulli and Edgeworth methods are classical; Poincaré
  expansions at fixed order with existential constants `C_K`; only the
  leading constant `12/B` is explicit.
- The dense large-dimension table entries are saddle evaluations, not
  enumerations; no interval arithmetic; the sign corollary asserts no
  uniqueness of crossings; `D_eff` is "a proposed organizing parameter".
- The review of ProveIt and of the `math` repository was bounded; nothing
  formalized; no external review.

The write adds: its checks are exact finite computations, floating
evaluations or hand computations; its scan of the conjecture is finite and
settles no minimum dimension; nothing was submitted anywhere.

## Further questions

Section 12 of the article (`lcw:sec:further`) keeps the source's four
questions (effective constants and a certified inverse; sparse and dense
ratios `N/D → 0, ∞`; a lattice local theorem or joint Edgeworth expansion for
the occupancy; comparison with conditional-occupancy and Bessel-distribution
literature). A dated note (Vladimir's standing rule of 4 October 2026)
records that no unproved claim of the source lies outside them and none is
wrong, and that Remark 9.2 settles, for its leading term, the extreme case of
question 2 in which `D` stays fixed; `N/D → ∞` with `D → ∞`, and `N/D → 0`,
stay open. **Nothing in the source was found to be wrong.** Recorded with a
dated note: the printed `r`, `b` and `p` are rounded, not truncated, in their
last digit (truncations `r = 0.804139735863439633472418654…`,
`b = 1.586562859178089847374174938…`, `p = 0.431494883273705551403382959…`).
(Scope clarified after the independent check of 7 October 2026: the note's
"every printed digit except these three is a truncation" concerns the seven
values printed with "…"; the six table entries of Section 5 and the two mean
offsets of Theorem 7.1, printed without it, are correctly rounded, five of
them not truncations.)

**Part II and Part I's questions** (dated note at the end of Section 12;
table in Section 13.2; the earlier note, which calls both ends of question 2
open, is kept):

- **Question 2: answered for the counts at both ends** (Theorem 16.2 for every
  ratio; Theorem 19.1 and Corollaries 19.2–19.4 for `N/D → ∞`; Theorem 18.1 for
  `m²/D = O(1)`), **and for the laws in the sparse critical range**
  `m²/D = O(1)` (Theorem 18.2). Open: the laws of zero steps and occupied axes
  for `N/D → ∞` with `D → ∞`, and for `N/D → 0` with `N²/D → ∞`.
- **Question 3: advanced only in the sparse critical range** (a discrete joint
  law, not Gaussian); the compact-range local theorem and joint Edgeworth
  expansion stay open.
- **Question 1: advanced in part**: `|a_n/L_n − 1| ≤ 24/⌊n/2⌋` for every
  `n ≥ 2` with Part II's leading term; effective constants for Theorem 4.1,
  interval evaluation and a certified inverse stay open.
- **Question 4**: untouched.

**Part II's own questions** (Section 21): nine subsections (a corrected
universal Gaussian upper bound and the onsets of the thresholds; the window
near the quadratic crossing; effective high-order bounds and a verified
evaluator, and the sharp constant in the `12/B` bound; occupation laws for
`m/D → 0`, `m²/D → ∞`; anisotropic collision laws and `D_eff`; a moving idle
activity in the dense range; prescribed endpoints and other step sets; a
staged formalization; spanning-tree entropy), all kept as questions. Under
Vladimir's standing rule of 4 October 2026 the write found no claim of Part II
unproved as stated outside them and none wrong; nothing moved or refuted.
Recorded by dated notes: Ball–Sterbenz display (1.3) for `n ≥ 0` (the
manuscript writes `n ≥ 1`; immaterial); Felker–Lyons display (2.3) only for
`1 ≤ d ≤ 6` (all `k`) and `d ≥ 7` (large `k`), after the sentence that the
inequality appears to hold for all `d` and `k`, so the counterexample refutes
that belief and Ball–Sterbenz's (1.3), not the qualified display, and leaves
their rigorous `h_3,…,h_6` bounds untouched; the Gowers–Szemerédi ledger
count (113/7 at the pin, 114/6 since `456b6e3ad`); the delivered layout.

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 25/25; the
  pin `83befe707` exists. The dossier read the manuscript and found no error;
  with its own exact polynomial power at `n = 120, 121` it reproduced `r`,
  `d`, `C_±` and residuals consistent with `c_{ε,1}`, `c_{ε,2}`; it checked
  the audit's statements about the repository (the A039831, A047909, A108242
  reports and Report 169's packed matrices exist as described); and it reran
  the programs on copies: `code/verify.py` passing (summary equal to
  `generated/verification.json` as JSON), `regenerate.py --compare` and both
  optional `--compare` checks exiting 0, `guard_tests.py` failing on Windows
  (text regenerated with CRLF).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  every proof line by line (the list is in Section 1.1), with no mathematical
  error found; with its own code, the constants at 60 digits (three rounded
  last digits, above; `d`, `C_±`, `τ²` truncations), `c_{ε,1..3}` against
  the table of Section 5, the diagnostics table of Section 10.3 to every
  printed digit, `E K_n − np = −0.07093, −0.31307, −0.07109, −0.31237` at
  `n = 60, 61, 120, 121` (offsets `−0.071243`, `−0.311664`), the b-file, the
  row conjecture. The programs rerun from the shipped files (Route B below):
  `code/verify.py` passing with the delivered and with the written
  `article.tex` (the verified-prefix block is unchanged), its summary equal to
  `data/generated-verification.json` as JSON; `regenerate.py --compare` and
  both optional `--compare` checks exit 0; `guard_tests.py` fails on Windows
  as at intake.
- Sources read by the write: the OEIS entries and the A328716 b-file; the
  transseries volume. Not read: Gessel–Weinstein–Wilf, Flajolet–Sedgewick.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`f3fb85cb6`), with
its own code, after fetching again A328716 (#38), A328718 (#35), A002426 and
the A328716 b-file.

- **Remark 9.2, checked hardest**: the reduction to `P(S_N = 0)`, the
  Fourier inversion, `φ = 1` only at `0`, `φ > −1` (`1 + 2Σcos θ_i ≥ 1 − 2D`),
  the local bound and the Gaussian integral re-derived; the conjecture's row
  index is the dimension. Exact counts at `N = 400` by Miller's power
  recurrence for `F^D` (a route distinct from the source's two) give the three
  printed values; row 1 = A002426 on all its data terms. **Strengthened**:
  the `1/N` coefficient is `−3D/16` (dated note above).
- **Remark 1.1**: quotations, revisions and dates confirmed; all 399 b-file
  terms agree with Miller's recurrence modulo two primes, 45 of them exactly;
  Kotěšovec's `d` and both `c` are truncations.
- **Constants note (Section 3)**: at 70 digits `r`, `b`, `p` end in rounded
  digits with the stated truncations and next digits; `d`, `C_±`, `τ²` are
  truncations. **Scope clarified** (dated note; see above).
- **Section 10 notes**: every diagnostics-table entry reproduced;
  `E K_n − np = n(1 − A_{n,n−1}(1)/a_n) − np = −0.070931, −0.313069,
  −0.071086, −0.312368` at `n = 60, 61, 120, 121`, as stated.
- **Remark 8.2**: (a)–(e) re-derived against the volume (staircase (4) with
  `p0:rem:parity-instances`, `p0:prop:factorial-core` with `κ = 1`,
  `d_vol = log d`, the template chart, the core-reversion form).
- Provenance, the pin `83befe707`, the neighbouring reports named, and the 72
  delivered label numbers and 65 references confirmed. Apart from the scope
  of one sentence, **no defect was found in the write.**

The check is recorded at the end of Section 12.


## Checks of Part II

- **At placement** (NG1 dossier, 7 October 2026): the staged 12 files
  byte-identical to a fresh extraction; `verify_lyons.py` and
  `verify_endpoints.py` (1,303 comparisons) and `reproduce.py` rerun on a copy
  (record equal except the Python version, table file equal apart from CRLF,
  figures differing in bytes only); the counterexample confirmed by batch
  133's own exact count; no claim found wrong.
- **At the write** (7 October 2026; Python 3.14.4, mpmath 1.3.0, SymPy
  1.14.0; own code in the intake work area, not shipped):
  - every proof of Sections 15–19 read line by line, with no error found;
    by hand: Lemma 16.4's three formulas, `B ≤ m`, the `F_ν` integral
    representation, every constant of Proposition 17.3 (`13/120 < 1/8`,
    `cos³(1/4) > 1/2`, `a = 15/32`, `45927/24576`, suprema `π^{5/2}/√(2e)`
    and `8/√(2πe)`, `2 + 8 + 2 = 12`), the sparse expansion
    `D log F_w(t_0 z)` and the corrections (18.3), the triple coefficient,
    the dense parity conversion and Corollaries 19.3–19.4;
  - with SymPy (an unknown `w^{−3}` coefficient kept): (19.6), (19.8), the
    prefactor expansion, the totals `−3/(16ρ)` and
    `(D/48 − 1/32 − 3/(64D))ρ^{−2}` (`−1/(4ρ)`, `(D/48 − 1/16)ρ^{−2}`
    nonlazy) and the logarithm `D(4D² − 6D − 1)/192` of the fixed-`D` expansion;
  - the counterexample by a third exact route (the 101 partitions of 13,
    axis assignments, multinomials): count
    `23,062,502,564,288,544,059,408,295,833,600`, `C_{13,16}`, `A`, the
    positive difference and the `4001/4000` comparison; `π > 333/106` by
    Machin's four terms and by `6 arcsin(1/2)`; ratio in mpmath interval
    arithmetic `1.000559383382871717665…`; the three displayed decimals;
  - the finite scan of the conjecture (above);
  - Table 4 (all 16 entries) from exact rational counts; further sparse cases
    (`θ = 4, β = 2`; `θ = 1/4, β = 0`) with corrected errors of order `m^{−2}`;
    `m E U → θ²/36`;
  - exact `R/G` at `D = 100`, `N = 500, 501, 1000, 1001, 2000, 2001`: equal to
    the `D = 100` rows of Table 3 to every printed digit; all 24 entries of
    Table 3 by the write's own saddle code;
  - fixed `D = 1, 2, 3`: Richardson from exact counts at `N = 400, 800` gives
    `0.0019530…`, `0.1015622…`, `0.4238214…` for the `1/N²` coefficient
    (formula `0.0019531…`, `0.1015625`, `0.4238281…`);
  - the envelope `12/B` on an exact anisotropic example (`D = 3`,
    `c = (1, 1/7, 5)`, `λ = 1/3`): errors `1.2·10^{−3}`–`8.1·10^{−3}` against
    `12/B` from 4.1 to 0.76;
  - Part I's Theorem 9.1 against Part II's leading term at `N = D = 40, 41,
    100, 101` (relative differences `−1.86·10^{−3}` to `−1.86·10^{−4}`);
  - the three shipped programs rerun on a copy in the delivered layout:
    `verify_lyons.py` and `verify_endpoints.py` pass; `reproduce.py` (Python
    3.13.5 under `uv`, mpmath 1.3.0, matplotlib, 85 s) passes, its
    `verification.json` equal to the shipped one except the recorded Python
    version, its table file equal apart from line ends;
  - Part I's `code/verify.py` (Route B) passes with the written `article.tex`
    as `Report179.tex`, its output identical to that with the previous text
    (the verified-prefix block is unchanged);
  - sources read: the Ball–Sterbenz preprint (display (1.3) p. 2,
    Proposition 1 p. 3, Remark 1 pp. 3–4, checks for `d = 3, …, 6`) and the
    Felker–Lyons version of 6 November 2003 (p. 4, (2.1)–(2.3)); the
    repository at the pin `136e70702`. Not read: the journal versions, the
    erratum, Bender, Pitman, Dolgopyat–Hafouta, the DLMF, the `math`
    repository.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
8.2(a)–(b) applies is formalized generically in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`
(`Fabius.staircase_ceil`, and the residue-class identity of part (4) as
`Fabius.isLeast_residue_class`); nothing about these sequences is.

**The transseries volume.** Remark 8.2: the threshold and its parity
decomposition instances of `p0:thm:staircase`(1) and (4); the parity
brackets analogues of (2) as proved and consequences of (4) with the write's
interpolations; the closed form a `p0:prop:factorial-core` instance, its
expansion a formal `plt:thm:lw-template` instance; the higher carriers formal
`p0:thm:core-reversion` instances; the full carrier equation not shown to be
a template instance.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
the source's audit read the A039831 report (`a039831-two-fourier-peaks`) and
set aside A047909, A108242 and Report 169 as covered
(`a047909-beta-renewal-subsequences`, `a108242-regular-cyclic-word-covers`,
Part IV of `a261781-matrix-compositions`). None shares a result with this
report, so no reciprocal note is proposed.

**Stale claims.** Before batch 109 no file of the repository named A328716
or A328718; the audit's bounded comparison at `83befe707` found no A328716
treatment, which was true.

**Part II and Part I.** Part II names Part I as its immediate predecessor
and uses it only for the questions it answers. Its Proposition 16.1 contains
Part I's count (2); its `E_s` are Part I's `𝒯_s 1` with `(B, κ_j)`; on a
compact ratio with a real marker its Theorem 16.2 and Part I's Theorem 9.1
are two expansions of the same counts whose leading terms agree to relative
`O(1/D)`, and neither contains the other (no complex marker or absolute
remainder at zeros in Part II; no uniformity in `ρ` or anisotropy in Part I);
its Theorem 19.1(i) at fixed `D` gives Part I's Remark 9.2 by a second route,
and its Subsection 19.1 obtains the `1/N` term of Remark 9.2's dated note by
the same Edgeworth computation.

**Part II's review of the repository** (Section 14, pinned at `136e70702`):
the lattice-walk row is correct; the Gowers–Szemerédi row's ledger count
(113 exact companions, 7 open) was true at the pin and is 114/6 since
`456b6e3ad`; the Boolean row refers to reports 65 and 69 of
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/`;
the `math` rows were not checked. Before the placement no file of the
repository mentioned Felker or Sterbenz. No neighbouring report shares a
result with Part II, so no reciprocal note is proposed.

## Notation

Part I: a table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `H(v,t)`, `H(s)`, `H_ℓ(j)`; `h`, `h(w)`;
`R`, `R'`, `R_2(n)`, `R_{k,m}`; `q`, `Q_{D,k}`, `Q_{ε,ℓ}`; `K_n`, `K`; `D`,
`𝒟`; `ρ`, `r`, `r_ρ`, `r(w)`; `𝒯_ℓ`, `T(n,k)`; `d`, `d_TV`; `E_ε`,
`E_{ε,u}`, `𝔼`; `v_ε`, `v`; `s_j`, `s`; `ℓ`, `ℓ_{ε,j}`; `A`, `A_n(u)`,
`A_M`; `F`, `𝓕_{ε,M}`; `X`, `X_r`, `x`, `x(s)`; `I`, `I_0`, `I_1`; `κ_h`,
`Λ`, `L_M`. No symbol was renamed; the volume's colliding letters carry the
subscript "vol" in Remark 8.2.

Part II keeps its letters; a table in Section 13.5 gives their Part I
readings: `ε` (parity remainder `0, 1` there, sign `±1` in Part I); `m`, `N`;
`F` (`F(t) = I_0(2√t)` there, `F(z) = I_0(2z)` in Part I); `𝒟` (`t d/dt`
there, `z d/dz` in Part I); `r`, `κ_j`, `B` (the saddle, cumulants and
variance of `G_ε` in `t`; Part I's `r`, `κ_h`, `b`); `E_s` (Part I's `𝒯_s 1`;
Part I's `E_ε` is another object); `H_0`, `H_1`, `h`; `λ` (Part I's marker
`u`), `J`; `K_occ` (Part I's `K_n`), `R`, `U`, `K`; `θ`, `β`; `C`, `c`; `ρ`
(the same), `q`; `R_{N,D}`, `G_{N,D}`; `Q` (`Q_{n,D}` is Part I's `Q_{D,n}`);
`T`, `L`; `𝒫_{ε,β}`; `a`, `b`, `d` (a dimension in Section 15), `s`, `p`;
`X`, `x`, `ν`. No symbol was renamed.

## Labels

Every label carries the prefix `lcw:` (none existed in the repository). The
manuscript's 72 labels (`eq:` 51, `sec:` 13, `thm:` 5, `prop:` 1, `lem:` 1,
`rem:` 1) were prefixed before anything cited them, and the 65 references to
them (52 `\eqref`, 13 `\ref`) updated. The write added 4: `lcw:rem:oeis`,
`lcw:sec:provenance`, `lcw:rem:transseries`, `lcw:rem:rows`. The report has
76 labels; builds of the delivered text and of this one give all 72
delivered labels the same numbers (aux files compared; the article numbers
equations consecutively, so the write added no numbered display). The added
statements are the last of their sections, the added subsection follows the
last delivered text of Section 1, and nothing was inserted before a
delivered display, table or statement.

Part II's 76 delivered labels (`eq:` 48, `sec:` 7, `thm:` 6, `cor:` 5,
`tab:` 3, `prop:` 2, `fig:` 2, `subsec:` 2, `lem:` 1) carry the prefix
`lcw:ulb:`: `ulb:X` and unprefixed `X` became `lcw:ulb:X`, and the sparse
section's `newsp:X` became `lcw:ulb:sp:X` (both sections use `eq:exact`);
the 75 references to them (41 `\eqref`, 34 `\ref`) were updated. The three
table labels sit in the shipped `data/02-bridges-numerical_tables.tex`, which
is input unchanged through a wrapper that adds the prefix (`\inputprefixed`
in the preamble; it sets amsmath's `\ltx@label` too, since amsmath restores
`\label` inside floats). The write added 9 labels: `lcw:part:one`,
`lcw:ulb:part`, `lcw:ulb:sec:front`, `lcw:ulb:sec:provenance`,
`lcw:ulb:sec:answers`, `lcw:ulb:sec:checks`, `lcw:ulb:sec:nonclaims`,
`lcw:ulb:sec:notation` and `lcw:ulb:sp:sec:sparse` (the delivered sparse
section has none). The report has 161 labels. Aux files of builds of the
committed text, of the delivered Part II manuscript (31 pages) and of this
text: all 76 Part I labels keep their numbers; every Part II label is its
delivered number shifted by 13 sections (Theorem 2.1 → 15.1, Theorem 3.2 →
16.2, Theorems 5.1–5.2 → 18.1–18.2, Theorem 6.1 → 19.1, equation `(k.m)` →
`(k+13.m)`), and Tables 2–4 and Figures 1–2 keep their numbers (the
uncaptioned survey table takes number 1, as delivered; the write's two
longtables give theirs back). Part II's equations are numbered within
sections (`\counterwithin{equation}{section}` at the start of Part II), Part
I's consecutively as before.

## Files

```text
README.md                              this guide (replaces the delivery README)
article.tex                            the report (Part I: delivered Report179.tex; Part II: the 02 manuscript; labels prefixed, [write] additions)
article.pdf                            compiled report, 61 pages
README_CODE.md                         the programs' documentation (delivered at the root)
SOURCE_AUDIT.md                        the source's attribution and overlap audit (delivered at the root)
optional-README.md                     the optional checks' documentation (delivered optional/README.md)
code/exact.py                          exact counting and coefficient algebra (delivered code/)
code/verify.py                         core verifier; reads the manuscript's prefix block (delivered code/)
code/regenerate.py                     regenerates or compares data/certificates.json (delivered code/)
code/guard_tests.py                    corruption and guard tests; fail on Windows (delivered at the root)
code/test_build.py                     build rejection tests (delivered at the root)
code/verify_manifest.py                release-inventory check (delivered at the root)
code/build.py                          isolated PDF and ZIP builder, TeX (delivered at the root)
code/optional-check_walks.py           SymPy/mpmath walk checks (delivered optional/)
code/optional-independent_check.py     SymPy/mpmath independent checks (delivered optional/)
code/optional-utility.py               shared helper of the optional checks (delivered optional/)
data/certificates.json                 exact certificates (delivered data/)
data/walk_checks.json                  recorded optional output (delivered data/)
data/independent_checks.json           recorded optional output (delivered data/)
data/PROVENANCE.json                   hashes and regenerators of the two records (delivered data/)
data/optional-requirements.txt         sympy==1.14.0, mpmath==1.3.0 (delivered optional/)
data/generated-verification.json       verifier summary (delivered generated/)
data/generated-verification_guards.json  guard-test summary (delivered generated/)
data/generated-build_guards.json       build-test summary (delivered generated/)
data/generated-BUILD_INFO.json         build receipt (delivered generated/)
code/02-bridges-walks.py              Part II: exact counts, parity saddle, cumulants, Edgeworth corrections (delivered code/walks.py)
code/02-bridges-verify_lyons.py        Part II: standard-library certificate of the counterexample (delivered code/verify_lyons.py)
code/02-bridges-verify_endpoints.py    Part II: 1,303 exact prescribed-endpoint comparisons (delivered code/verify_endpoints.py)
code/02-bridges-reproduce.py           Part II: full rerun; writes the record, the table file and the figures (delivered code/reproduce.py)
data/02-bridges-verification.json      Part II: verification record (delivered data/verification.json)
data/02-bridges-numerical_tables.tex   Part II: Tables 2-4, generated, input by article.tex (delivered data/numerical_tables.tex)
data/02-bridges-requirements.txt       Part II: mpmath>=1.3.0, matplotlib>=3.8 (delivered requirements.txt)
data/02-bridges-source_provenance.json Part II: pins and literature locators (delivered source_provenance.json)
figures/02-bridges-uniform_errors.pdf  Part II: Figure 1, included by article.tex (delivered figures/)
figures/02-bridges-uniform_errors.png  Part II: preview of Figure 1 (delivered figures/)
figures/02-bridges-dense_transition.pdf  Part II: Figure 2, included by article.tex (delivered figures/)
figures/02-bridges-dense_transition.png  Part II: preview of Figure 2 (delivered figures/)
```

There are 37 files. Every file except `README.md`, `article.tex` and
`article.pdf` is byte-identical to its delivery (Part II's 12 rechecked at
the write).

**Not shipped**, recoverable from the arrival commit (next section):
`Report179.pdf` (the delivered 16-page PDF, 402,088 bytes);
`SHA256SUMS.json` (2,333 bytes, 25 entries, verified at placement;
repository policy ships no checksum manifests); and the delivery `README.md`
(5,031 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`code/verify.py` reads `Report179.tex` and `data/` from the package root (its
`--manuscript` and `--data` options override them); `code/build.py`,
`code/test_build.py` and `code/verify_manifest.py` expect `Report179.tex`,
`README.md`, `build.py`, `guard_tests.py`, `optional/`, `generated/` and
`SHA256SUMS.json` at the root; `code/guard_tests.py` and the optional scripts
use the delivered names; `optional-README.md` and `README_CODE.md` give
commands for the delivered layout; `data/PROVENANCE.json` names
`optional/check_walks.py` and `optional/independent_check.py` as
regenerators; Section 10.4 of the article describes the delivered ZIP. So
no program runs under the shipped names; use one of the routes below.

**Part II, not shipped**, recoverable from its arrival commit (next
section): the manuscript sources `article.tex` and `sections/*.tex` (2,139
lines, 88,397 bytes; printed as Part II), `article.pdf` (the delivered
31-page PDF, 583,332 bytes) and the delivery `README.txt` (5,440 bytes,
summarized below). The archive has no checksum manifest.

**Part II's delivered text that names the delivery layout.** Section 20
names `code/verify_lyons.py`, `code/verify_endpoints.py`, `code/walks.py`,
`code/reproduce.py`, `data/verification.json`, `requirements.txt` and
`latexmk -pdf article.tex` (the manuscript, not this report);
`code/02-bridges-reproduce.py` imports `walks` and writes `data/` and
`figures/` under the package root by the delivered names, overwriting the
records there. Dated note at the end of Section 20.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Lazy_Closed_Walks_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # e433f40b68bae06759f38828c5acff277112cd034a6dd978654fe5473b44f613, 617,713 bytes
cd "$T" && unzip -q a.zip
```

Part II:

```sh
T2=$(mktemp -d)
git -C /path/to/ProveIt show fe7165a3c:docs/incoming/uniform-lattice-bridges-research.zip > "$T2/b.zip"
sha256sum "$T2/b.zip"  # f736b7f99454080a8a5d14709af8bd057bb34865106f033fdd2cf3d3eaff7bb6, 838,687 bytes
cd "$T2" && unzip -q b.zip   # creates uniform-lattice-bridges/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later; the core uses only the standard library, the optional
checks SymPy 1.14.0 and mpmath 1.3.0. Never run anything in the repository.

**Route A, delivered layout**, from `$T`:

```sh
python -S -B code/verify.py
python -S -B -O code/verify.py
python -S -B code/regenerate.py --compare data/certificates.json
python -B optional/check_walks.py --compare
python -B optional/independent_check.py --compare
python -S -B guard_tests.py        # POSIX (compares LF output)
python -S -B test_build.py         # POSIX
python -S -B build.py --output ../rebuild-one   # TeX, POSIX
```

**Route B, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a328716-lazy-closed-walks
B=$(mktemp -d); mkdir -p "$B/code" "$B/data" "$B/generated" "$B/optional"; cd "$B"
cp "$R"/code/exact.py "$R"/code/regenerate.py "$R"/code/verify.py code/
cp "$R"/code/build.py "$R"/code/guard_tests.py "$R"/code/test_build.py "$R"/code/verify_manifest.py .
cp "$R"/data/PROVENANCE.json "$R"/data/certificates.json "$R"/data/independent_checks.json "$R"/data/walk_checks.json data/
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
for f in check_walks independent_check utility; do cp "$R/code/optional-$f.py" "optional/$f.py"; done
cp "$R/optional-README.md" optional/README.md; cp "$R/data/optional-requirements.txt" optional/requirements.txt
cp "$R/README_CODE.md" "$R/SOURCE_AUDIT.md" .; cp "$R/article.tex" Report179.tex
```

then the commands of Route A. At the write, in this layout, `code/verify.py`
passed (its JSON summary equal to `generated/verification.json`), with the
written `article.tex` as `Report179.tex` too; `regenerate.py --compare` and
both optional checks exited 0 (a few seconds each); `guard_tests.py` failed
on Windows ("regenerated bytes differ": CRLF). The manifest check and the
build need the delivered `README.md` and `SHA256SUMS.json` (Route A). Use
`py` where `python` is not on the path.

**Part II, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a328716-lazy-closed-walks
C=$(mktemp -d); mkdir -p "$C/code" "$C/data" "$C/figures"; cd "$C"
for f in walks verify_lyons verify_endpoints reproduce; do cp "$R/code/02-bridges-$f.py" "code/$f.py"; done
for f in verification.json numerical_tables.tex; do cp "$R/data/02-bridges-$f" "data/$f"; done
cp "$R/data/02-bridges-requirements.txt" requirements.txt
python code/verify_lyons.py        # standard library, under a second
python code/verify_endpoints.py    # standard library, 1,303 comparisons
uv run --no-project --with mpmath==1.3.0 --with matplotlib --with pillow python code/reproduce.py   # about 90 s
```

`reproduce.py` overwrites `data/` and `figures/` in `$C`; compare them with
the shipped `data/02-bridges-*` and `figures/02-bridges-*` (at the write:
the record equal except `software/python`, the table file equal apart from
line ends).

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, xcolor, xurl, hyperref, enumitem, fancyhdr,
graphicx, longtable); the bibliography is embedded. Part II inputs
`data/02-bridges-numerical_tables.tex` and the two `figures/02-bridges-*.pdf`.

```sh
B=$(mktemp -d); mkdir -p "$B/data" "$B/figures"; cp article.tex "$B/"
cp data/02-bridges-numerical_tables.tex "$B/data/"; cp figures/02-bridges-*.pdf "$B/figures/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026, after
the second write (Part II): 61 pages (Part I alone: 22); no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes (pdfLaTeX, three
passes). Part I's delivered text builds without any, 16 pages; Part II's
delivered text builds to 31 pages, with six underfull boxes in its survey
table, which the write set ragged right. The
delivered byte-identity claims (fixed source date, suppressed PDF metadata)
apply to `Report179.tex` under the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) said that the package contains
"the PDF, editable LaTeX source, exact standard-library verification,
optional SymPy/mpmath diagnostics, and an offline deterministic builder" and
that "No open problem resolution, worldwide priority, or certified
finite-input inverse calculator is claimed"; listed the mathematical content
(as above); said that "Constants and onsets are non-effective here" and
that no convergence, extreme-ratio uniformity, fixed-dimensional
implication or Gaussian total-variation limit is asserted; gave the quick
verification commands (the manifest check "applies to the complete release
ZIP"), the rebuild procedure and its isolation and determinism; and
summarized the evidence: 52 exact count cases including `n = 0..41` and
selected sizes through `n = 201`, joint zero-step/occupation counts, and
optional programs whose "residual stabilization is supporting evidence, not
a proof of the analytic remainders or an effective starting threshold".

## From Part II's delivery README

The delivery `README.txt` (not shipped) lists the package contents and the
four main results (as above), the build (`latexmk -pdf article.tex`, or two
or three pdfLaTeX passes; "The supplied figure PDFs and table file permit
compilation without running Python"), the standalone verifiers (the
counterexample "by two independent exact coefficient methods", "No
floating-point approximation of pi is used in the decision"; 1,303 endpoint
comparisons), the full rerun (Python 3.12.14, mpmath 1.3.0, 60 digits; 444
exact comparisons, 84 saddle cases, 24 dense illustrations, 8 sparse
comparisons, two activity-rescaling checks; "The script overwrites the
generated tables, figures, and JSON data"); suggests a sibling directory
`a328716-uniform-lattice-bridges/` (declined at placement: the manuscript
answers this report's question, so it is a Part here); and states that the
literature audit "does not establish historical priority or a minimum
dimension" and that the manuscript "does not rely on the unverified claims
reviewed in the two repositories as assumptions".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A328716 and A328718; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that
content remains under that licence. Short quotations of the cited works are
for attribution. No third-party PDF is shipped (the write read the
Ball–Sterbenz and Felker–Lyons PDFs at their public URLs and keeps no copy
in the repository). Nothing was submitted to the
OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A328716 (entry and official source
  record) and A328718; Gessel–Weinstein–Wilf, Electron. J. Combin. 5 (1998),
  R2; Flajolet–Sedgewick, *Analytic Combinatorics* (2009), Theorem VIII.8.
- Batch 109 of `docs/incoming`, bundle Report 179; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report179.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
- Part II: non-Gowers intake NG1, manuscript 04 (routed here by batch 133);
  arrival `fe7165a3c` (7 October 2026), placement `3cf0a2758` (12 files,
  prefix `02-bridges-`, archive retired), written 7 October 2026 (second
  write). Sources cited by the manuscript: Felker–Lyons, J. Phys. A 36 (2003)
  and its 2012 erratum; Ball–Sterbenz, J. Theoret. Probab. 18 (2005);
  Gessel–Weinstein–Wilf; Bender (1973); Pitman (1997); Dolgopyat–Hafouta
  (2022); DLMF 4.22, 10.21, 10.32, 10.40; ProveIt and `math` at their pins.
