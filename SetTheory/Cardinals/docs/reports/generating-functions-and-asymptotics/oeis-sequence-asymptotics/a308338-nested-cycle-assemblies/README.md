# Assemblies of Nested Cycles (OEIS A308338, A392471, A007838); Part II: Sharp Gumbel Errors and Optimal Continuous Calibration for the Largest Outer Component

**`a_n ~ C n! n^{c/2−3/4} e^{2√(cn)}` with `c = e^{−γ}` and an explicit `C`;
a complex-uniform expansion to every fixed order in `n^{−1/2}` with
polynomials in `log n`; the mean and variance of the number of components
with their logarithmic and constant corrections; a two-ceiling inverse; and,
from the write, Riedel's conjecture `E[X] ~ N√n` proved with
`N = e^{−γ/2}`, and a corrected covariance display of Erlihson and
Granovsky**

**Part II (added 9 October 2026): for the size `M_n` of the largest outer
component (a nested cycle of maximal size, not the longest single cycle),
and for every assembly with weights `p_k = c + O(1/k)`: with `τ` the exact
size saddle and `L = log(c/τ)`, the ordinary Gumbel error is
`d_K(F_n, G) ~ κ τL²/(4c)`, `κ = (2+√5)e^{−(3+√5)/2}`; no affine
normalization removes this order; an explicit increasing calibration
`G∘h_τ` has error `τ/(2e) + O(τ/L)`, and `τ/(2e)` (half the largest atom) is
optimal among all continuous distribution functions; a lattice law with error
`O(τ/L)` and an exponential-integral refinement with error `O(τ^{3/2}L³)`;
integer quantiles with bounded error. For nested cycles the raw error is
`(e^{γ/2}κ/16) log²n/√n`. It answers none of Part I's questions.**

Two Parts. Part I is a research article ("Report 167" of a session bundle),
built from one manuscript dated 3 October 2026. Its author line reads
"Report 167" and its PDF author field is empty: it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data (the word "private" occurs only in the
delivered README's "private fresh format", a TeX format file). Part II is a
research manuscript dated 8 October 2026, "Research manuscript prepared for
Vladimir Reshetnikov" (title page and PDF author); its README calls it "an
AI-assisted, unrefereed manuscript", and a source comment names an agent,
`proveit_scout`, as the author of its Fourier section.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 167 (batch 108) | `Nested_Cycle_Assemblies_Asymptotics_and_Inverses_Source.zip` (21 files at the archive root and in `companion/` and `data/`, 938,156 bytes, SHA-256 `ef59faff…eaebc0b63`), arrival commit `60f54ea06`; main file `Report167.tex` (908 lines, 15 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | Part I (Sections 1–11) |
| 02 | *Sharp Gumbel Errors and Optimal Continuous Calibration for Random Assemblies* (batch 138, group OEIS, manuscript 03) | `sharp_gumbel_assemblies.zip` (24 files in one wrapper directory, 987,801 bytes), arrival commit `b28d0850b`; main file `article.tex` + 2 section files + a generated table file (1,926 lines, 27 pp.) | blob `07022425b718` of Part I's `article.tex` at ProveIt `2bac1ea07b98` (7 October 2026, 21:26 PDT; Part I before this write) and `adc7f1241b42` of `openai/math` (not checked) | `803f4d937` (18 files, prefix `02-gumbel-`) | Part II (Sections 12–23 and Appendices A–B; Section 12 added by the write) |

**Status:** Part I is AI-assisted, as is Part II (its README). Both Parts
are unrefereed and not formalized: no Lean or Rocq declaration exists for any
statement of this report, and nothing in the repository formalizes these
assemblies. No proof uses a computation.

## Trust boundaries

Part I:

- **What rests on an external theorem.** Every analytic statement rests on
  the component estimate `p_m = B_m/m! = c + c/m + O(log m/m²)` (`(1.4)`,
  `ncy:eq:prior`), which Flajolet, Fusy, Gourdon, Panario and Pouyanne
  (Electron. J. Combin. 13 (2006) R103, Section 3, eq. (22)) attribute to
  Greene and Knuth. It is cited, not reproved; the source read the hybrid
  paper's Section 3 and Proposition 1, not the book. The A007838 entry states
  the same formula and cites the book.
- **What is proved by hand, given it.** The fixed-order expansion, the
  all-arc suppression, the Gaussian Taylor lemma, the explicit `R_1`, `R_2`,
  the moment expansions, the CLT (a known regime, re-proved with this
  normalization) and the two-ceiling inverse. No implied constant or onset is
  made effective; every decimal is an uncertified floating evaluation.
- **The companion** computes `B_n`, `a_n` and the triangle `T(n,k)` exactly
  for `n ≤ 100` by four independent routes (integer cycle product and Bell
  recurrence, rational EGF recurrences, rational powers through `n = 30`,
  literal enumeration through `n = 7`), checks the 100 published terms, and
  (optionally, with SymPy) the finite symbolic identities behind `R_1`, `R_2`,
  `B`, `B_3`, `m_0`, `v_0`, `M_1`, `V_1`. It proves nothing asymptotic.

Part II:

- **What is proved by hand.** Every theorem of Sections 14–21 from the
  stated weight hypothesis `p_k ≥ 0`, `p_k = c + O(1/k)`: conditioned Poisson
  identities, Fourier inversion on the circle with a common block of
  positive weights bounding the whole circle (Lemma 15.2), a paired Fourier
  difference that keeps a cancellation the separate estimates would lose
  (Theorem 15.4), Taylor estimates and elementary sums. The `E_1` refinement
  (Theorem 20.1) and the explicit saddle (Proposition 21.2) need the refined
  hypothesis `p_k = c + a_*/k + O(log(k+1)/k²)`.
- **What rests on an external theorem.** For nested cycles only: Part I's
  credited component estimate `(1.4)` (`ncy:eq:prior`, Greene–Knuth through
  Flajolet–Fusy–Gourdon–Panario–Pouyanne), quoted as `(13.2)`; it is the
  refined hypothesis with `c = a_* = e^{−γ}`. No statement of Part I enters a
  proof.
- **What is prior.** The first-order Gumbel laws (Panagiotou–Ramzews,
  arXiv:2208.00925, Theorem 1.2, for expansive assemblies; Bousquet-Mélou–
  Weller, FPSAC 2013, Proposition 9, for forests of paths) and the
  component asymptotics.
- **What is diagnostic.** Tables 1–2, both figures and every decimal:
  floating point, no interval arithmetic; the large path-forest errors are
  sampled maxima. The nested-cycle errors are still far from their proved
  constants at `n ≤ 10⁵` (below).

## What Part I proves

`P(z) = Π_{m≥1}(1 + z^m/m)` is the EGF of permutations with distinct cycle
lengths (A007838, `B_m`); a nested cycle is such a set of cycles in its
unique decreasing nesting order; `F(z,u) = exp(u(P(z)−1))` counts sets of
them, `a_n = n![z^n]F(z,1)` is A308338 and `T(n,k)` (the coefficient of
`u^k`) is A392471. Statement numbers are the delivered ones.

- **Theorem 2.1 (`ncy:thm:main`)**: for every fixed `J`,
  `f_n(u) = C(u) n^{cu/2−3/4} e^{2√(cun)} {1 + Σ_{j≤J} n^{−j/2} R_j(log n; u) + E_{n,J}(u)}`,
  `deg R_j ≤ 2j`, `E_{n,J} = O(n^{−(J+1)/2}(1+log n)^{2J+2})`, uniformly on a
  small disc about `u = 1`, with every fixed derivative.
- **(2.3) (`ncy:eq:equivalent`)**:
  `a_n ~ C n! n^{c/2−3/4} e^{2√(cn)}`,
  `C = e^{c(1/2−log 2)−1} c^{1/4−c/2}/(2√π) ≈ 0.0947779253874791584`.
- **Sections 3–5**: the local expansion of `log P(e^{−t})` in a right
  half-plane with the constants `B`, `B_3` (`ncy:eq:logP`), the all-arc
  bound (`ncy:eq:globalP`) controlling every secondary arc without crossing
  the natural boundary, and Lemma 5.1 (`ncy:lem:gaussian`).
- **Section 6**: `R_1`, `R_2` explicitly (`ncy:eq:R1`, `ncy:eq:R2`) and a
  formal Bessel-type coefficient calculator (`ncy:eq:calculator`).
- **Theorem 7.1 (`ncy:thm:moments`)**: for the number `K_n` of components,
  `E K_n = √(cn) + (c/2) log n + m_0 + O(n^{−1/2}(1+log n)²)` and
  `Var K_n = √(cn)/2 + (c/2) log n + v_0 + O(…)`, with explicit `m_0`, `v_0`
  and next terms `M_1`, `V_1` (`ncy:eq:explicitM1`, `ncy:eq:explicitV1`); in
  particular `E K_n/√n → e^{−γ/2} = 0.749306…` (`ncy:eq:meanlimit`).
- **Corollary 7.2 (`ncy:cor:clt`)**: `(K_n − E K_n)/σ_n ⇒ N(0,1)`,
  `σ_n² = √(cn)/2` (credited regime: Erlihson–Granovsky 2008, Corollary 4.5,
  attributing it to their 2004 paper).
- **Theorem 8.1 (`ncy:thm:inverse`)**: for `N(y) = min{n : a_n ≥ y}`,
  `⌈x_J − ε_J⌉ ≤ N(y) ≤ ⌈x_J + ε_J⌉` with `x_J` the root of the order-`J`
  model; starting value `x_0* = L/W(L/e)`, `L = log y`, and one Newton step.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 7.3 (`ncy:rem:riedel`)**: Riedel's conjecture, proved, and what
  his fitted constants missed (next section).
- **Remark 8.2 (`ncy:rem:transseries`)**: Section 8 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  The starting value `x_0*` is an **instance**, verbatim, of
  `p0:prop:factorial-core` with `(κ_vol, d_vol, L_vol) := (1, −1, log y)`;
  `N(y)` is the staircase `N_*` of `p0:def:three-inverses` with `n_1 = 1`
  for `y > 1`; Theorem 8.1 is **not an instance, only an analogue** of
  `p0:thm:staircase`(2): it compares the model `G_J` with `log a_n` at the
  integers and uses monotonicity directly, with no admissible interpolation.
- **Remark 10.1 (`ncy:rem:eg`)**: the Erlihson–Granovsky covariance display,
  refuted and corrected (next-but-one section).
- **Section 1.1 (`ncy:sec:provenance`)**: provenance, the sources as the
  write read them (including the OEIS changes since the source), what was
  checked, relation to the repository, collected non-claims, reading
  conventions; a note on the package at the end of Section 9; a note and
  Question 6 in Section 11.

## What Part II proves

Weights `p_k ≥ 0`, `p_k = c + O(1/k)`, `c > 0`; the law of the component
spectrum is `Z_n^{−1} Π p_k^{N_k}/N_k!`, and `M_n = max{k : N_k > 0}`. `τ`
solves `B_1(τ) = Σ k p_k e^{−τk} = n` (`τ ~ √(c/n)`), `L = log(c/τ)`
(`~ ½ log n`), `Y_n = τM_n − L`, `F_n` its distribution function,
`G(x) = exp(−e^{−x})`, `δ = τL²/(4c)`, `β = e^{−x}`, `q = L + x`. Part II's
Section `k` is the manuscript's Section `k − 12`; statement and equation
numbers below are those of this report.

- **Theorem 14.2 (`ncy:gb:thm:main`)**, summarizing:
  `F_n = G + δ G e^{−x}(1 − e^{−x}) + O(τL)` uniformly;
  `F_n = J_n + τ(½ − θ_n(x))G'(x) + O(τ/L)` with `J_n = G∘h_τ`,
  `h_τ(x) = x + (τ/(4c))[q² − q − 1 − β(q+1)²]`; `‖F_n − U_n‖ = O(τ/L)`.
- **Theorem 15.4 (`ncy:gb:thm:tailmoment`)**: `P(M_n ≤ m)` equals
  `e^{−S_0(m)}[1 + (S_2 − S_1²)/(2V) − B_3S_1/(2V²)] + O(τ^{3/2}L³)`
  uniformly in `m`, from the exact identity
  `P(M_n ≤ m) = e^{−S_0(m)} P(T_m = n)/P(T = n)` (`(14.13)`).
- **Theorem 16.2 (`ncy:gb:thm:lattice`)**: the lattice law `U_n` with error
  `O(τ/L)`.
- **Proposition 17.1 (`ncy:gb:prop:kappa`)**: `d_K(F_n, G) = κδ + O(τL)`,
  `κ = (2+√5)e^{−(3+√5)/2} = 0.309004785987675…`;
  **Theorem 17.2 (`ncy:gb:thm:affine`)**: the best affine normalization has
  error `E_*δ(1 + o(1))`, `1/(2(e²/2 + 2e + 2√e)) ≤ E_* ≤ κ`.
- **Theorem 18.1 (`ncy:gb:thm:atom`)**: the largest atom is `τ/e + O(τ²L²)`,
  and the best continuous approximation has error exactly half of it.
- **Theorem 19.1 (`ncy:gb:thm:optimal`)**: `h_τ` is an increasing bijection
  for `τ/c ≤ 1/4`, and `‖F_n − J_n‖ = τ/(2e) + O(τ/L)`, the optimal leading
  constant; **Corollary 19.2**: integer quantiles with `O(1)` error.
- **Theorem 20.1 (`ncy:gb:thm:e1`)**: under the refined hypothesis,
  `F_n = U_n − a_* G(x) E_1(max{1, L+x}) + O(τ^{3/2}L³)`, and
  `‖F_n − U_n‖ ~ |a_*|τ/(ceL)` when `a_* ≠ 0`.
- **Corollary 21.1 (`ncy:gb:cor:nested`)**, nested cycles (`c = a_* = e^{−γ}`):
  raw error `~ (e^{γ/2}κ/16) log²n/√n`, calibrated `~ (e^{−γ/2}/(2e)) n^{−1/2}`
  (optimal), lattice `~ (2e^{−γ/2}/e)/(√n log n)`, refined
  `O(n^{−3/4} log³n)`; **Proposition 21.2**: `τ = √(c/n) + c/(2n) + O(n^{−3/2} log²n)`.
- Path forests (`c = 1/2`, `a_* = 0`) as a second model; Section 22: exact
  checks at `n = 50`, Fourier computations for `n = 10³…10⁵` (nested) and
  `10⁴…10¹²` (forests), Tables 1–2, Figures 1–2.

Added by the write (9 October 2026), marked `[write]`: Section 12
(`ncy:gb:sec:front`: provenance, how it was merged, what Part II answers in
Part I, what was checked, collected non-claims, reading conventions); the
editorial note after Part I's status note; notes at the end of Sections 1.1,
11 and 13, after Proposition 17.1 (a rounded constant) and Corollary 21.1
(the constants, the input), at the end of Sections 22 (the package, two
printed differences, the write's reproduction) and 23 (`E_*`, the questions),
and in Appendix B; labels on the eleven questions of Section 23.

## Riedel's conjecture, proved

Marko Riedel's note *Nested Cycle Partitions: a conjecture* (January 2026;
revised author-hosted version, page footers dated 24.01.26, and the original
linked from A392471, footers 13.01.26) has on p. 3 a paragraph "The
conjecture", identical in both versions. With `X` the number of components
of a uniformly random nested cycle partition on `n` nodes, the boxed
conjecture is `E[X] ~ N√n` with the constant `N` to be determined. He adds
that the asymptotics might instead involve `n^M` with `M` "close to but not
equal to 1/2", and that the numerical data suggest `M ≥ 0.4704567259` and
`N ≈ 0.7719351399`; the note states neither the range of `n` nor the fitting
method. Neither OEIS entry carries the conjecture. (The batch-108 placement
message paraphrased this as a conjecture `E[X] ~ N n^M` with fitted
`M ~ 0.4705`; the box says `N√n`, and the inequality sign is `≥`.)

- **Proved** (the source's Theorem 7.1; the source quotes Riedel's `N` as a
  "finite-data estimate" but does not say the conjecture is settled): his `X`
  is `K_n`, so `E[X] ~ e^{−γ/2} √n`, `N = e^{−γ/2} = 0.7493060…`. The
  alternative is false: `E K_n ~ N n^M` with `N > 0` holds only for
  `M = 1/2`. The printed inequality `M ≥ 0.4704567259` is satisfied by
  `M = 1/2`; the value `N ≈ 0.7719351399` is not the constant (it exceeds
  `e^{−γ/2}` by 0.0226).
- **What the fits missed** (`[write]`, proved from Theorem 7.1):
  `E K_n/√n = e^{−γ/2} + ((c/2) log n + m_0)/√n + O(n^{−1} log² n)` with
  `m_0 = −0.977132…`, so the ratio exceeds `e^{−γ/2}` for all large `n`; and
  for every fixed integer `ϱ ≥ 2`,
  `M_ϱ(n) = log(E K_{ϱn}/E K_n)/log ϱ = 1/2 − (1−ϱ^{−1/2})(c/2) log n/(√(cn) log ϱ) + O(n^{−1/2})`,
  below `1/2` for all large `n`. The additive `(c/2) log n` is read by a fit
  as a smaller exponent and a larger constant. Computed values
  (double precision, checked against exact and 256-bit values):
  `E K_n/√n = 0.821954, 0.786471, 0.771935, 0.766422, 0.762634` and
  `M_2(n) = 0.47781, 0.48628, 0.49089, 0.49285, 0.49428` at
  `n = 100, 1000, 4500, 10⁴, 2·10⁴`.
- **Where his numbers may come from**: `E K_4500/√4500 = 0.77193514015`
  agrees with his `N` to `2.5·10^{−10}`, and the ratio first drops below it at
  `n = 4501`. This suggests, but the note does not say, that his `N` is the
  ratio at `n = 4500`. The computation behind `M ≥ 0.4704567259` was not
  identified (slopes, two-point exponents and least-squares windows tried).

Recorded only: nothing was submitted to the OEIS and Riedel was not
contacted.

## Correction: the Erlihson–Granovsky covariance display

Erlihson and Granovsky, *Limit shapes of Gibbs distributions on the set of
integer partitions: the expansive case*, Ann. Inst. H. Poincaré Probab.
Statist. 44(5) (2008) 915–945, Theorem 4.3(i), for weights `a_k ~ C k^{p−1}`
(every `p, C > 0`), with `b_r(u) = C Γ(r+1, u)`:

    e_mk = b_{p−1}(u_s) − b_p(u_m) b_p(u_k) / Γ(p+2),   s = max(k, m)

(preprint arXiv:math/0507343v3 eq. (4.54); published eq. (4.18), p. 927;
both read at the write and identical). Corollary 4.5 applies it for all
`u ≥ 0`, `u = 0` being the total number of components.

- **Counterexample** (the source found it; Remark 10.1(a)): `p = 1`,
  `C = 3`, `u = 1`: `e_11 = 3/e − 18/e² = −1.3324 < 0`. At `u = 0` the
  display is `C Γ(p)(1 − Cp/(p+1))`, negative whenever `C > (p+1)/p`.
- **Correction** (`[write]`): the denominator must be `C Γ(p+2) = b_{p+1}(0)`,
  the limit of `r_N^{−p−2} Var Z` for the total mass `Z`; this is what
  conditioning the independent Poisson counts of the Boltzmann model on `Z`
  gives. The corrected value is positive by Cauchy–Schwarz (`0.29163` in the
  example) and equals the printed one only at `C = 1`.
- **Where the `C` is lost**: the published (5.62) (preprint (5.121)) gives
  `Var Z_N ~ Γ(p+2) δ^{−(p+2)}` where `a_k ~ C k^{p−1}` gives
  `C Γ(p+2) δ^{−(p+2)}`; `T_q` in (5.69) has the same factor, while the proof
  of (5.72) uses `Σ_j f_j(p+1) = C Γ(p+2)`. Theorem 4.1(ii)'s covariance
  (4.13) (preprint (4.49)) fails the same way (`−1.4956` at `q = 1`, `p = 1`,
  `C = 3`, `u_1 = 10`). Their own identity `f_0(p+1) + f_1(p+1) = C Γ(p+2)`
  and (5.73) give `det Θ*(1) = C T_1` for their matrix (5.74), so (5.72) as
  printed holds only for `C = 1`: the factor is lost with (5.62) and carried
  through `T_q`. The inversion that produces (4.13) was not checked. (Added
  after the independent check below; the write said that the step which first
  drops `C` was not traced.)
- **Against this report**: here `p = 1`, `C = c`, `r_N = (n/c)^{1/2}`. Read
  at `u = 0`, the printed display predicts the normalized component count to
  have limiting variance `c(1 − c/2) = 0.40384`, the corrected one `c/2 =
  0.28072`; Corollary 7.2 and (7.3), proved without the display, give `c/2`,
  and two normalizations differing by a deterministic shift cannot have
  Gaussian limits of different variances. So the printed display contradicts
  this report, and the corrected one agrees.

The source derived its variance independently and used the display for
nothing; no other report uses it. Not audited: the rest of Section 5 of the
paper (Question 6). Nothing was sent to the authors.

## The OEIS entries at the write (6 October 2026)

- **A308338** (live revision #21; the source froze #17 of 15 January 2026):
  revisions #18–#20 by Alois P. Heinz on 5 October 2026 add a Maple program
  and a b-file for `0 ≤ n ≤ 445` (#21 is the OEIS server installing that
  b-file; the write said "#18–#21 by Heinz"); the 22 data terms are
  unchanged.
- **A392471** (live #42; the source froze #37 of 25 January 2026): on
  5 October 2026 Heinz inserted the column `k = 0` (offset now 0, rows from
  `n = 0`), a Maple program and a b-file of rows `0..150`. The delivered
  sentence of Section 1 that the triangle "starts at n=1" describes #37; the
  entry now uses this report's extension `T(0,0) = 1`, `T(n,0) = 0`. Its
  link to Riedel's original note is titled "definitions and basic
  recurrences"; the PDF is titled "a conjecture".
- **A007838** (#74, unchanged) states (1.4) and cites Greene–Knuth.
- The three b-files agree with `data/exact_data_100.json` for `n ≤ 100`.
- At Part II's write (9 October 2026) A308338 was read again: revision #21,
  unchanged; Part II's 22 checked terms are its data. Part II names no
  revision.

## Part II: records of the write

- **A rounded constant.** Proposition 17.1 prints `κ = 0.309004785987676…`;
  `κ = 0.3090047859876757102…`, so the truncation is `0.309004785987675…`
  (dated note; nothing depends on the digit).
- **Two printed differences.** Section 22 prints maximum differences
  `1.83×10⁻¹⁴` (exact against Fourier, `n = 50`) and `1.85×10⁻⁹`
  (recurrence against Fourier, `n = 1000`); the delivered record has
  `1.824029208924438e-14` and `1.844130930914959e-9`. Neither rounding nor
  truncation; true as upper bounds (dated note).
- **The constants are not visible in the numerics.** At `n = 10³, 10⁴, 10⁵`
  the nested-cycle errors over their proved equivalents are `2.52, 1.87,
  1.57` (raw / `κδ`), `5.54, 4.69, 3.58` (calibrated / `τ/(2e)`) and
  `5.69, 5.92, 5.19` (lattice / `τ/(eL)`). The manuscript says the
  calibrated error "need not yet be close" to its constant; the tables
  neither contradict nor confirm the constants. Only the path-forest model
  (`a_* = 0`) gets close: calibrated ratio `1.0029` at `n = 10¹²`.
- **`E_*`** (Question 23.3; uncertified, the write's): `E_* ≈ 0.1024413800`
  at slope `α ≈ 1.0000000`, shift `b ≈ −0.2784645`, with three-point
  equioscillation at `x ≈ −1.265, 0, 2.164`; about `κ/3.02`. Whether `α = 1`
  exactly is open.
- **Stale or wrong statements:** none found. The proposal of a separate
  report `a308338-sharp-largest-components/` was declined at placement.

## What is not claimed

Part I, from the source, kept in the article (collected in Section 1.1):

- Every fixed order only: no convergence, optimal truncation, Stokes
  phenomenon or complete beyond-all-orders description; constants not
  uniform when the order grows; the calculator is formal.
- No effective constant or onset, no certified `M_J`, no interval enclosure
  of `C`; all decimals uncertified.
- The square-root law, the limit `e^{−γ/2}` and the normal fluctuations are
  the established expansive-assembly regime; the CLT is "not a new
  universality assertion"; no local limit theorem or distance bound.
- Finite and symbolic checks prove nothing asymptotic (the `B`, `B_3` checks
  verify the arithmetic pieces, not the tail summations).
- Bounded source coverage, no worldwide priority, "No claim is made that no
  other work contains overlapping results"; the Greene–Knuth book and the
  2004 Erlihson–Granovsky paper were not inspected; no OEIS amendment.
- Byte identity of rebuilds is toolchain-specific.

The write adds: the table and the `n = 4500` identification in Remark 7.3
are floating evaluations and an inference, not a statement of Riedel's; the
correction in Remark 10.1 rests on the conditioning computation, not on a
re-audit of the whole paper.

Part II, from the manuscript (collected in Section 12.4): the first-order
Gumbel laws and the component asymptotics are prior; the quantitative
refinements are "proposed new contributions", and the directed literature
audit "does not establish worldwide priority"; unrefereed, AI-assisted,
checked by agent derivations and audits that "are not human peer review",
not formalized; computations check finite arithmetic and coefficient ratios
and prove nothing asymptotic; no interval arithmetic, sampled maxima for the
largest path-forest sizes, node agreement does not bound the omitted arc;
no effective constant or finite threshold ("moderate sizes can be far from a
leading equivalent"); the refined result needs the refined hypothesis; `U_n`
need not be a distribution function; the `E_1` hierarchy is no convergent
series; no numerical value of `E_*` is used; the Potts coefficient met during
the selection is already in Mossel–Sly–Sohn. The write adds: its checks are
floating (positive terms only) or symbolic; its `E_*` is uncertified;
nothing was submitted anywhere.

## Further questions

Section 11 of the article (`ncy:sec:questions`) states every unproved claim
as an open question (Vladimir's standing rule of 4 October 2026). **Nothing
in the source was found to be wrong**; the two corrections above concern
outside literature.

1. **Effective constants** (`ncy:q:effective`): certified constants and
   onsets for the equivalent and the inverse (it would also give the onset of
   `E K_n/√n > e^{−γ/2}`, computed for `n ≤ 40000`).
2. **Beyond the small disc** (`ncy:q:local`): local limit theorem, moderate
   deviations, a normal-approximation rate.
3. **Periodic terms** (`ncy:q:periodic`): how the root-of-unity component
   corrections appear in exponentially small outer terms.
4. **Higher corrections** (`ncy:q:calculator`): complexity bounds and
   certified simplification.
5. **Faster exact counts** (`ncy:q:bell`).
6. **Erlihson–Granovsky** (`ncy:q:eg`, the write's): does their proof, with
   (5.62) and (5.69) corrected, give the corrected displays, and does
   anything else depend on the missing factor?

**Part II answers none of these** (dated note at the end of Section 11): it
treats a statistic Part I does not. Its own eleven questions (Section 23,
labels `ncy:gb:q:*`, the manuscript's, as delivered) stay open: the next
term of the calibrated error (`nextconst`); an optimal calibration beyond
first order (`calibration`); the value of `E_*` (`affine`; the write's
uncertified `0.10244`); a better discrete remainder (`remainder`); joint laws
of several largest components (`several`); weights `p_k ~ c k^{α−1}`,
`α ≠ 1` (`expansive`); arithmetic supports (`arithmetic`); effective finite
constants (`effective`, the analogue of Question 1); root-of-unity component
oscillations in the largest-component law (`periodic`, the analogue of
Question 3); moving quantiles and moments of `M_n` (`quantiles`);
formalization (`formal`).

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 19 staged files are byte-identical to a fresh extraction, and
  `SHA256SUMS` verified 20/20. The dossier read the manuscript in full and
  found no false claim; checked `p_100` against `c + c/100`, the counts,
  exact mean and variance at `n = 100` against the theorems, and `a_n` over
  the leading term at `n = 25, 50, 100`; read Riedel's conjecture paragraph
  and verified the literal substitution in the Erlihson–Granovsky preprint.
  On copies, `verify.py` (normal and `-O`), `verify.py --include-data`,
  `test_exact_nested.py` and `symbolic_checks.py` reproduced the four frozen
  outputs; the release tests errored on Windows (POSIX descriptor helpers).
- At the write (6 October 2026; same machine): the archive retrieved from the
  arrival commit again (`SHA256SUMS` 20/20); the companion rerun from a fresh
  extraction (route A) and from the shipped files (route B), reproducing the
  frozen outputs after converting line endings (SymPy 1.14.0); the three
  live OEIS entries, their histories and b-files; both versions of Riedel's
  note as page images; the Erlihson–Granovsky preprint and published text;
  a double-precision evaluation of `a_n/n!`, `E K_n`, `Var K_n` for
  `n ≤ 40000` (residuals consistent with Theorem 2.1 at `J = 1` and with
  `M_1`, `V_1`: at `n = 40000`, `9.682/9.344`, `12.92/12.69`, `16.97/16.53`
  for `√n` times the residual against the next coefficient), and a 256-bit
  fixed-point evaluation of `E K_n` near `n = 4500`.

**Independent check of the write (6 October 2026).** An adversarial check
made by the intake after the write (`399df8a49`) re-derived every `[write]`
statement. Riedel's note, fetched again in both versions (byte-identical),
is paraphrased exactly. The check's own computation (exact to `n = 120`, 320-bit
fixed point to 4501, double precision to 40000) gives
`E K_4500/√4500 = 0.771935140148`, and `n = 4501` is the first `n` with the
ratio below Riedel's `N = 0.7719351399`; the table, the margin above
`e^{−γ/2}` and the monotonicity claims were confirmed. The log-log exponent
`log E K_n/log n` comes closest to Riedel's `M` bound at `n = 7510` (off by
`6·10⁻⁸`), so his value is still not identified. Remark 10.1 was confirmed on
the published page images and in this very model: exact finite-`n`
variances at `n = 20000` give `Var/r_N = 0.10799, 0.05448, 0.02976` for
`u = 0.5, 1, 2`, against corrected `0.10817, 0.05458, 0.02971` and printed
`0.21008, 0.12122, 0.05000`; and from their (5.73)–(5.74),
`det Θ*(1) = C T_1` (re-derived symbolically for this record), so their (5.72)
holds only for `C = 1`. Remark 8.2 and the b-files were confirmed. No
mathematical error was found. Corrected, with a dated note keeping the first
wording: the A308338 revision attribution (#18–#20 by Heinz, #21 the server);
strengthened, also with a dated note: the last sentence of Remark 10.1(c).

**Part II.** At placement (batch-138 dossier, 9 October 2026; own code):
`κ` as the larger stationary value; the three corollary constants; the six
exact rational distribution values at `n = 50` (integer recurrence, equal to
the recorded fractions); A308338 `a(0..16)`; the raw, smooth and lattice
columns of `data/02-gumbel-nested_errors.csv` at `n = 10³, 10⁴` by a
per-cutoff tilted recurrence (every printed digit at `10⁴`, within
`3·10⁻¹⁰` at `10³`). At the write (9 October 2026; Python 3.14.4, NumPy
2.4.4, SciPy 1.17.1, SymPy 1.14.0, mpmath 1.3.0; own code, not shipped):

- every proof of Sections 14–21 read line by line, no error found; by hand or
  SymPy: `R_1, R_2, R_3`, the exact geometric tail, the algebra (16.6) with
  the skewness term, the sign `−3bα = −B_3S_1/(2V²)`, the `L²` profile, both
  stationary values of `|H|` and their ratio `1.9178…`, the bound (17.5),
  `G'(x)(h_τ(x) − x)` = the smooth part of `U_n`, the derivative (19.4) and
  its four regions, the `E_1` profile, the saddle algebra of Proposition
  21.2, every decimal constant at 40 digits;
- a third numerical route (neither the delivery's Fourier quadrature nor the
  intake's recurrence): the whole law of `M_n` at `n = 10³, 10⁴, 10⁵` from
  the incremental product `Π_{k≤m} exp(a_k z^k) mod z^{n+1}` with positive
  terms only; all four error columns of `nested_errors.csv` (all twelve
  entries of Table 1) to `3.0·10⁻¹⁰`, `6.6·10⁻¹⁵`, `3.1·10⁻¹⁴`; largest atom
  over `τ/e` with `(atom − τ/e)/(τ²L²) = 0.342, 0.262, 0.229`; integer
  quantiles within `[−0.69, 1.59]` of the formula of Corollary 19.2; the
  exact saddle minus `√(c/n) + c/(2n)` at `n = 10³…10⁶` equal to `−0.032…
  −0.029` times `n^{−3/2} log² n`; `E_*` by numerical minimax;
- the shipped `nested_numerics.py` and `forest_numerics.py
  --recurrence-check` rerun on a copy (15 s and 23 s): the six fractions
  exactly, every error column of the three CSV files to relative
  `2·10⁻⁸`; only the noise columns (quadrature differences `~10⁻¹⁵`, saddle
  residual) differ;
- A308338 read again (#21). Not read: Panagiotou–Ramzews, Bousquet-Mélou–
  Weller, Mossel–Sly–Sohn, `openai/math`.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns these assemblies. Placement in
the collection confers no formal status.

**The transseries volume.** `x_0*` is an instance of
`p0:prop:factorial-core`; the two-ceiling inverse is an analogue of
`p0:thm:staircase` only (Remark 8.2). No novelty is claimed for the
inversion.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a064856-stirling-catalan-transforms` (Part II: cycle-weighted permutation
mixtures, a different model); `a301746-divisor-weighted-asymptotics`,
`a022629-distinct-partition-norms`, `a271619-strict-twice-partitions`
(Gibbs-partition background after Granovsky, Stark and Erlihson). None treats
these sequences, none uses the corrected display, and none needs a
reciprocal note.

**Stale claims.** Before batch 108 no file of the repository named these
sequences or Riedel's note; the source made no claim about the repository.

**Part II.** Its account of Part I (marked enumeration asymptotics and
component-count fluctuations) is correct; it read Part I at the blob
`07022425b718`, Part I's text before this write. Before its placement no
file of the repository cited Panagiotou–Ramzews or Bousquet-Mélou–Weller or
treated the largest component of an expansive assembly; no neighbouring
report shares a result, and no reciprocal note is needed. Part II's own
proposal of a sibling report `a308338-sharp-largest-components/` was
declined (one report per A-number).

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `B_m`, `p_m` against the constants `B`,
`B_3`, the calculator `𝓑_β` and Erlihson–Granovsky's `b_r`, `p`; `C(u)`, `C`
against `C_0`, `C_{j,k,m}` and their `C`; `u` against their scaled size `u`;
`L` (`log n` or `log y`) against `L_n(u)` and the volume's `L`; `Q`, `Q_j`,
`X_n` against Riedel's `Q(z,u) = F(z,u)` and `X = K_n`; `K_n`, `K`, `K_0`;
`H_{j,k}`, `H_j`; `ℓ`, `ℓ_c`, `ℓ_r`; `β`; `κ`, `κ'`, `h`, `d`, `δ` against
the volume's and their `δ`; `p`, `q` of Section 8; `N(y)`, `M_J`, `M_1`
against Riedel's `N`, `M` and the write's `M_ϱ(n)`. No symbol was renamed.

Part II keeps its letters; a table in Section 12.5 reads them against Part
I's. The dangerous ones: Part II's `a_k` are Poisson means (Part I's `a_n` is
A308338, Part II's `A_n`); `B_j` are tilted size moments (Part I's `B_m` is
A007838, Part II's `B_k^comp`); `L = log(c/τ) ~ ½ log n` (Part I: `log n` or
`log y`); `R_j(q)` are tail polynomials (Part I's `R_j(L;u)` correction
polynomials); `Q_n(m)`, `Q_n(p)`, `Q_m` (three objects); `M_n` the largest
component (Part I's `M_J`, `M_1`); `G` the Gumbel law (Part I's `G_J`);
`δ = τL²/(4c)`; `κ` the Gumbel constant; `T`, `T_m` Poisson totals (Part I's
`T(n,k)`); `β = e^{−x}`, `q = L + x`. No symbol was renamed.

## Labels

Every label carries the prefix `ncy:` (none existed in the repository). The
manuscript's 62 labels (`eq:` 46, `sec:` 11, `thm:` 3, `lem:` 1, `cor:` 1)
were prefixed before anything cited them, and the 60 references to them
updated. The write added 10: `ncy:sec:provenance`, `ncy:rem:riedel`,
`ncy:rem:transseries`, `ncy:rem:eg`, and the questions `ncy:q:effective`,
`ncy:q:local`, `ncy:q:periodic`, `ncy:q:calculator`, `ncy:q:bell`,
`ncy:q:eg`. Part I has 72 labels; builds of the delivered text and of
this one give all 62 delivered labels the same numbers (aux files compared).

Part II's 94 delivered labels (92 in the text, 2 in the shipped table file,
prefixed at input by a wrapper) carry `ncy:gb:`; 102 references (69
`\eqref`, 33 `\ref`) were updated; the two `FFGPP` citations were re-keyed to
Part I's `hybrid`. The write added 19: `ncy:part:one`, `ncy:gb:part`,
`ncy:gb:sec:front` and its five subsections (`provenance`, `answers`,
`checks`, `nonclaims`, `notation`), and the eleven questions
`ncy:gb:q:{nextconst, calibration, affine, remainder, several, expansive,
arithmetic, effective, periodic, quantiles, formal}`. Against builds of the
committed text, of the delivered manuscript and of this one: all 72 Part I
labels unchanged; every Part II label is the delivered number with its
section shifted by 12 (Theorem 2.2 → 14.2, Theorem 3.4 → 15.4, Proposition
5.1 → 17.1, Theorem 7.1 → 19.1, Corollary 9.1 → 21.1); Appendices A–B,
Tables 1–2 and Figures 1–2 unchanged. 185 labels in all.

## Files

```text
README.md                             this guide (replaces the delivery README)
article.tex                           the report: Part I (delivered Report167.tex) and Part II (delivered article.tex with its section files); labels prefixed, [write] additions
article.pdf                           compiled report, 56 pages
companion-README.md                   the companion's README (delivered companion/README.md)
companion-PROVENANCE.md               fixture and source provenance (delivered companion/PROVENANCE.md)
code/companion-exact_nested.py        exact integer/rational computations (delivered companion/exact_nested.py)
code/companion-verify.py              bounded verifier CLI (delivered companion/verify.py)
code/companion-test_exact_nested.py   eight regression groups (delivered companion/test_exact_nested.py)
code/companion-symbolic_checks.py     optional SymPy identities (delivered companion/symbolic_checks.py)
code/build_pdf.py                     deterministic PDF build (delivered at the root)
code/make_zip.py                      allowlist-verified source ZIP (delivered at the root)
code/release_tools.py                 descriptor-pinned output helpers (delivered at the root)
code/test_release.py                  11 tests of the release tools (delivered at the root)
data/SOURCE_PROVENANCE.json           sources, coverage and roles (delivered at the root)
data/verification_receipt.json        author-side receipt (delivered at the root)
data/published_fixtures.json          23 A007838, 22 A308338, 55 A392471 terms (delivered data/)
data/full_verification.json           verify.py output (delivered data/)
data/exact_data_100.json              verify.py --include-data output, all counts to n = 100 (delivered data/)
data/tests.normal.json                regression output (delivered data/)
data/symbolic.normal.json             symbolic-check output (delivered data/)
02-gumbel-PROVENANCE.txt              Part II: sources, pins, review boundary (delivered PROVENANCE.txt)
02-gumbel-VERIFICATION.txt            Part II: verification record and its scope (delivered VERIFICATION.txt)
code/02-gumbel-Makefile               Part II: build/numerics targets (delivered Makefile)
code/02-gumbel-nested_numerics.py     Part II: exact counts, n = 50 fractions, nested Fourier CDFs (delivered code/)
code/02-gumbel-forest_numerics.py     Part II: path-forest Fourier CDFs, 60-digit recurrence check (delivered code/)
code/02-gumbel-make_figures.py        Part II: figures and the table file from the CSVs (delivered code/)
data/02-gumbel-nested_errors.csv      Part II: nested errors, n = 10^3, 10^4, 10^5 (delivered data/)
data/02-gumbel-nested_profile.csv     Part II: lattice-point profiles at n = 10^5, 2,596 rows (delivered data/)
data/02-gumbel-forest_errors.csv      Part II: path-forest runs, n = 10^4 … 10^12 (delivered data/)
data/02-gumbel-forest_verification.txt  Part II: quadrature and recurrence log (delivered data/)
data/02-gumbel-verification.json      Part II: exact fractions and check results (delivered data/)
data/02-gumbel-numerical_tables.tex   Part II: Tables 1-2, input by the article (delivered numerical_tables.tex)
data/02-gumbel-requirements.txt       Part II: NumPy, SciPy, Matplotlib versions (delivered requirements.txt)
data/02-gumbel-MANIFEST.sha256        Part II: the delivered checksum list (delivered MANIFEST.sha256; not used)
figures/02-gumbel-error_profiles.pdf  Part II: Figure 1, included (delivered figures/)
figures/02-gumbel-error_profiles.png  Part II: its raster preview
figures/02-gumbel-forest_convergence.pdf  Part II: Figure 2, included (delivered figures/)
figures/02-gumbel-forest_convergence.png  Part II: its raster preview
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (38 files in the directory).

**Not shipped**, recoverable from the arrival commit (next section):
`Report167.pdf` (the delivered 15-page PDF, 406,435 bytes); `SHA256SUMS`
(1,746 bytes, 20 entries, verified at placement and at the write; repository
policy ships no checksum manifests); and the delivery `README.md` (5,076
bytes), staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-README.md` runs `verify.py` etc. "from this directory" and reads
`../data/published_fixtures.json`; `test_exact_nested.py` imports
`exact_nested` and `verify` by those names; so the programs do not run under
the shipped names. `companion-PROVENANCE.md` and `companion-README.md` cite
`../data/…` paths. `build_pdf.py` compiles `Report167.tex`; `make_zip.py`
checks an allowlist of the delivered names (`Report167.pdf`, `companion/…`)
against `SHA256SUMS`; `verification_receipt.json` records hashes of the
delivered source and PDF and of the `data/…` files under delivered names. Section 9
of the article refers to "the package README" for commands. The release
tools require POSIX.

**Part II, not shipped** (recoverable from `b28d0850b`): the manuscript
`article.tex` (43,680 bytes), `sections_fourier.tex` (12,317),
`sections_optimal.tex` (14,029) and `references.bib` (4,711), printed in the
article; its `article.pdf` (27 pages, 498,069 bytes); its `README.txt`
(7,656 bytes; summarized here: purpose, the five principal results, status
"AI-assisted, unrefereed", contents, build and reproduction commands, an
integration proposal as a separate report, theorem labels, the eleven
directions). **Part II delivered text that names its layout:** the
programs write `data/*.csv`, `data/verification.json`, `figures/*` and
`numerical_tables.tex` at the package root under the delivered names
(`make_figures.py` reads `data/nested_errors.csv` etc.); the Makefile
compiles `article.tex` with `latexmk` and BibTeX; `MANIFEST.sha256` lists
the delivered names; Section 22 and Appendix B name `data/verification.json`
and `PROVENANCE.txt`. Run the programs on a copy with the delivered names
(next sections).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Nested_Cycle_Assemblies_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # ef59faff7aba2b7dc9070b282abdf011f7c088dbe7e18f45a02b7d4eaebc0b63, 938,156 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # files at the archive root, plus companion/ and data/
```

Part II:

```sh
git -C /path/to/ProveIt show b28d0850b:docs/incoming/sharp_gumbel_assemblies.zip > "$T/g.zip"   # 987,801 bytes
mkdir "$T/gb" && cd "$T/gb" && unzip -q ../g.zip    # one wrapper directory sharp_gumbel_assemblies/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later; the core needs only the standard library, the symbolic
checks SymPy (1.14.0 used). Never run anything in the repository.

**Route A, delivered layout** (as the delivery README gives it; at the write
on Windows every line below was run except the `-O` variants and the release
tests, which the dossier ran at placement):

```sh
cd "$T/pkg"
python3 -B companion/verify.py > v.out                       # = data/full_verification.json
python3 -B companion/verify.py --include-data > vd.out        # = data/exact_data_100.json
python3 -B companion/test_exact_nested.py > t.out             # = data/tests.normal.json
python3 -B companion/symbolic_checks.py > s.out               # = data/symbolic.normal.json (needs SymPy)
python3 -B -O companion/verify.py
sha256sum -c SHA256SUMS
```

On Windows the outputs carry CRLF line endings and equal the frozen files
after conversion. The release tests (`python3 -m unittest test_release`) and
the PDF and ZIP rebuilds need POSIX and pdfTeX and were not run by the
intake on Windows.

**Route B, from the shipped files, any OS** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a308338-nested-cycle-assemblies
B=$(mktemp -d); mkdir "$B/companion" "$B/data"; cd "$B"
for f in exact_nested verify test_exact_nested symbolic_checks; do cp "$R/code/companion-$f.py" "companion/$f.py"; done
cp "$R/data/published_fixtures.json" data/
python3 -B companion/verify.py > v.out           # compare with $R/data/full_verification.json
python3 -B companion/test_exact_nested.py > t.out  # compare with $R/data/tests.normal.json
```

Use `py` where `python3` is not on the path. Route A took about 25 s on the
intake's loaded laptop.

**Part II, from the shipped files** (NumPy, SciPy, Matplotlib; tested at the
write with Python 3.14.4, NumPy 2.4.4, SciPy 1.17.1):

```sh
G=$(mktemp -d); mkdir "$G/code" "$G/data"; cd "$G"
for f in nested_numerics forest_numerics make_figures; do cp "$R/code/02-gumbel-$f.py" "code/$f.py"; done
python3 -I code/nested_numerics.py --out data                      # ~15 s; compare data/*.csv, verification.json with $R/data/02-gumbel-*
python3 -I code/forest_numerics.py --recurrence-check --output data/forest_errors.csv   # ~23 s
python3 -I code/make_figures.py                                    # needs Matplotlib; writes figures/ and numerical_tables.tex
```

The error columns agree with the shipped files to relative `2·10⁻⁸`; the
noise columns (quadrature differences of order `10⁻¹⁵`) differ from run to
run.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, array, microtype, hyperref, graphicx, longtable); the bibliography
is embedded. Part II inputs `data/02-gumbel-numerical_tables.tex` and the two
`figures/02-gumbel-*.pdf`, so build from a copy of the directory:

```sh
B=$(mktemp -d); cp article.tex "$B/"; mkdir "$B/data" "$B/figures"
cp data/02-gumbel-numerical_tables.tex "$B/data/"; cp figures/02-gumbel-*.pdf "$B/figures/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX (pdfLaTeX, three passes)
on 9 October 2026, at Part II's write: 56 pages (Part I alone: 22); no
errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes; changed pages rendered and inspected. The delivered Part II
manuscript builds to 27 pages, also without warnings. Part I's build at its
write and check (6 October 2026): 22 pages; no errors or warnings, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. The delivered source builds the same way to 15 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report167.tex` under the delivering toolchain (pdfTeX
1.40.26, TeX Live 2025/dev/Debian), not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the 15-page report
and the package (LaTeX, PDF, bounded exact code, frozen fixtures, outputs);
summarized the results as above, with "No worldwide priority claim or
complete beyond-all-orders transseries"; gave the quick checks of Route A
(normal and `-O`, release tests); said that exact finite checks "do not
certify an asymptotic remainder, error constant, onset threshold, decimal
transcendental constant, or distributional error"; gave POSIX build and
archive commands refusing existing destinations, with two clean builds
reproducing the PDF byte for byte under the same TeX installation; and ended
on sources and limits (the 2004 paper not inspected; "No external
publication, author contact, repository change, or OEIS edit accompanies
this package").

## Rights

Repository contents are MIT-0. The article and the frozen data quote OEIS
terms of A007838, A308338 and A392471; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. No third-party PDF is shipped. Nothing was
submitted to the OEIS. Part II's files carry no licence of their own and
fall under the repository's MIT-0.

## Provenance

- Sources cited by the manuscript: OEIS A007838, A308338 (Gutkovskiy,
  20 May 2019), A392471 (Riedel, January 2026); Riedel's note (both
  versions); Flajolet–Fusy–Gourdon–Panario–Pouyanne, Electron. J. Combin. 13
  (2006) R103 (Section 3 and Proposition 1); Erlihson–Granovsky, AIHP 44
  (2008) 915–945 (preprint and published numbering); Erlihson–Granovsky,
  Random Structures Algorithms 25 (2004) 227–245 (not inspected); Greene and
  Knuth (indirect). Read by the write: the three OEIS entries with
  histories and b-files, Riedel's note, the Erlihson–Granovsky preprint and
  published text, the transseries volume (`p0:def:core`,
  `p0:prop:factorial-core`, `p0:def:three-inverses`, `p0:thm:staircase`).
- Batch 108 of `docs/incoming`, bundle Report 167; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report167.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
- Part II: batch 138 of `docs/incoming`, group OEIS, manuscript 03;
  arrival `b28d0850b` (8 October 2026), placement `803f4d937` (9 October
  2026, 18 files with prefix `02-gumbel-`), written 9 October 2026 as Part II
  (Sections 12–23, Appendices A–B). Sources cited by the manuscript: OEIS
  A308338; Part I; Panagiotou–Ramzews (arXiv:2208.00925v1);
  Bousquet-Mélou–Weller (FPSAC 2013; CPC 23 (2014) 749–795);
  Flajolet–Fusy–Gourdon–Panario–Pouyanne (Part I's `hybrid`);
  Mossel–Sly–Sohn (arXiv:2212.03362v2); `openai/math` at `adc7f1241b42`.
