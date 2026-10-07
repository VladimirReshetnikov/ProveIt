# Tournament Score Sequences and Weighted Component Asymptotics

**Explicit corrections and uniform inverse models: every fixed order for all
and strong score sequences (OEIS A000571, A351822), a uniform half-power
expansion of the component-weighted count on a logarithmic window, and the
coexistence profile at `τ = ½ log n + 2 log log n + log(μ√π/2) + s`;
Part II: conditional phase coexistence, with giant blocks, Gamma laws and
stable fluctuations; Part III: beyond criticality, with pole–branch
expansions and tempered-stable crossovers on the supercritical side**

A research report in three Parts, built from three manuscripts. Part I is
dated 2 October 2026; it names no author and no tool (its title block reads
"Research report", and its PDF metadata had an empty Author field). Parts II
and III are dated 3 and 4 October 2026; their PDF metadata (and Part III's
title page) name the author as "Research manuscript prepared with AI
assistance".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 68 | `tournament-score-sequences-source.zip` (wrapper directory `tournament-score-sequences/`), arrival commit `096ee7b87`; main file `report.tex`, now the first half of `article.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | Part I, Sections 1–9 |
| 02 | batch 85, manuscript 04 | `tournament_coexistence_research.zip` (wrapper directory `tournament_coexistence/`), arrival commit `317c1ce2e`; main file `tournament_coexistence.tex` (1,687 lines, 25-page PDF) | `d68b65ea0` (`d68b65ea064084fb121df9bb431b21d086f7be81`); continues this report's `article.tex`, which did not change between the pin and the placement | `713149ded` | Part II, Sections 10–20 and Appendices A–B |
| 03 | batch 98, manuscript 03 | `tournament_supercritical.zip` (wrapper directory `tournament_supercritical/`), arrival commit `2172df76a`; main file `article.tex` (1,078 lines, 27-page PDF) | `106eb191a` (`106eb191a2a47ab6281e2c26c7f4fe3d28872b83`, a merge commit of 4 October 2026); continues this report, whose `article.tex` and `README.md` did not change between the pin and the placement | `9353a7171` | Part III, Sections 21–32 and Appendices C–E |

**Status:** AI-assisted (Parts II and III say so; Part I is presumed so,
naming neither an author nor a tool), unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. **Its inputs are prior
work, credited:** the exact generating function `S(z) = exp A(z)` and the
strong-block decomposition are Claesson–Dukes–Franklín–Stefánsson's (Proc.
AMS 151, 2023; divisor evaluation attributed there to Alekseyev), and the
leading asymptotics of `S_n`, `I_n` and each fixed component count are
Kolesnik's (Combinatorica 43, 2023; shorter proof by
Bassan–Donderwinkel–Kolesnik, ECP 31, 2026). The renewal and logarithmic
heavy-traffic/heavy-tail mechanisms are credited to Blanchet–Glynn (2007) and
Olvera-Cravioto–Blanchet–Glynn (2011); Part II credits the condensation,
Gibbs-partition and single-big-jump mechanisms to Białas–Bogacz–Burda–Johnston
(2000), Stufler (2024), Denisov–Dieker–Shneer (2008) and Armendáriz–Loulakis
(2011). Part III credits tempered stable laws to the literature (Grabchak,
arXiv:1109.1028) and exponential tilting, renewal conditioning, stable laws
and Lambert-W inversion to established methods; the batch-98 write added a
priority check against Banderier–Flajolet–Schaeffer–Soria (Random Structures
Algorithms 19, 2001) and Flajolet–Sedgewick's Section IX.11 (see "What is
not claimed"). Part I's contribution is the explicit local refinement; Part
II's is the proved conditional description in this size-dependent model;
Part III's is the supercritical specialization with its uniform correction
generator and crossover proofs. No exhaustive novelty search is claimed by
any of them.

## What it proves

`S_n` counts score sequences of tournaments on `n` vertices (A000571), `I_n`
the strong (irreducible) ones (A351822 without its empty object; A054946, which
counts strongly connected labeled tournaments, is a different problem), and
`W_n(u) = Σ_m S_{n,m} u^m` weights by the number of strong blocks. With the
CDFS split `A = F + R` (`R` analytic in `|z| < 1/2`), `ρ = 1/4`,
`λ = A(ρ) = 0.33023754398…`, `μ = ρA'(ρ) = 0.67395260185…`,
`p = 1 − e^(−λ)`:

### Part I (Sections 1–9)

- **Theorem 3.1.** For every fixed `K`, `T_n^σ = (e^(σλ)/(2√π)) 4^n n^(-5/2)
  (Σ_{m≤K} c_m^σ n^(-m) + O(n^(-K-1)))` for all (`σ = +`) and strong
  (`σ = −`) sequences, with `c_1^σ = −1/8 + σ(5/2)μ`, explicit `c_2^σ`
  (`c_2^+ ≈ −0.59217`, `c_2^− ≈ 4.58215`).
- **Proposition 3.2.** Fixed subcritical weights `0 < u < u_c = 1/p`, and
  the critical weight, where `4^(-n) W_n(u_c) = 1/a_c + (2/(3μ a_c √π)) n^(-1/2)
  + O(n^(-3/2))` with no `n^(-1)` term.
- **Theorems 4.1 and 5.1.** Uniformly on `0 ≤ τ ≤ C log n`,
  `4^(-n) W_n(u_n(τ)) = a_n(τ)^(-1) Σ_{m≤M} n^(-m/2) C_m(τ) + O(n^(-(M+1)/2))`,
  with `C_0 = e^(−τ)`, `C_1 = k H(τ)`, `H = ₁F₁(2; 1/2; −τ)/√π`, explicit
  `C_2`, and a finite generator in entire (regularized Kummer) kernels.
- **Corollary 6.1 (coexistence).** At `τ = b_n + s`,
  `a_c √n (log n)² 4^(-n) W_n → (2/(μ√π))(1 + e^(−s))`.
- **Section 7.** Inverses of specified models: fixed family size from `S_n`
  or `I_n` (explicit `W_{-1}` at order 0), size along a coexistence path, and
  the component weight when `n` is known.

### Part II (Sections 10–20, Appendices A–B)

Each score sequence `x` of length `n` gets probability `u^{K(x)}/W_n(u)`
(a law on score sequences, not on labeled tournaments), at the moving weight
`u_n = r_n/p`, `r_n = (1 + mτ_n/n)^(-1)`, `τ_n = b_n + s`, with `s` in a
compact interval. Here `m = 1.72234868…` is the mean critical block length
(Part I's `a_c`), `K_n` the number of blocks, `M_{1,n} ≥ M_{2,n} ≥ …` the
ranked block sizes, `δ_n = 1 − r_n`, and `C_n = {M_{1,n} > n/2}`.

- **Theorem 12.1 (logistic mixture).** `P(C_n) → π_s = 1/(1 + e^(−s))`, and
  `(mK_n/n, M_{1,n}/n) ⇒ π_s δ_(0,1) + (1 − π_s) δ_(1,0)`, uniformly for `s`
  in a compact interval. This answers Part I's first further question and
  identifies the factors `1` and `e^(−s)` of Corollary 6.1 as the weights of
  the giant event and its complement.
- **Theorem 12.2.** On `C_n` the two residual block strings around the giant
  are within total variation `O(1/τ_n)` of two independent geometric renewal
  strings; `(δ_n K_n, δ_n(n − M_{1,n})/m) ⇒ (G, G)` with `G ~ Gamma(2,1)`.
- **Theorem 12.3.** Off `C_n`, `m(K_n − n/m)/a_n ⇒ −Z` (spectrally positive
  `3/2`-stable `Z`) jointly with `M_{1,n}/a_n ⇒ V`, `P(V ≤ y) =
  exp(−1/(2√π y^(3/2)))`, `a_n = (κn/m)^(2/3)`; Section 16.3 adds the joint
  limit of the count and the point measure of large block sizes.
- **Theorem 12.4.** On `C_n`: stable residual fluctuations `(G, G^(2/3) Z)`,
  second-maximum law `(1 + x^(−3/2))^(−2)` and joint transform
  `(1 + t + x^(−3/2))^(−2)`; the large residual blocks form, given `G`, a
  Poisson point process with intensity `G (3/2) x^(−5/2) dx` (Section 17.3).
- **Theorem 14.2 (giant deletion)** for any block law `q_j = d j^(−1−α)(1 +
  O(1/j))`, `α > 1`, by an exact marked-block identity, with total variation
  `O(1/(nδ) + 1/n)`; **Corollary 14.3** (uniform split around the giant),
  **Corollary 15.1** (limits of `E K_n/n`, `Var K_n/n²`, `Cov(K_n, M_{1,n})/n²`),
  **Lemma 16.1** (lattice `3/2`-stable local limit, proved by Fourier inversion).
- **Proposition 17.1 and Corollary 17.2.** Every fixed order in `1/τ` for the
  giant weight, `Σ (j+1)(5/2)_j τ^(−j)`, and an explicit count-polynomial tilt
  approximating the residual law in total variation to `O(τ^(−M−1))`.
- **Proposition 18.1.** The implicit centre `b̂_n = −2 W_{-1}(−½ √(d/m) n^(−1/4))`,
  `b̂_n = b_n + (8 log L + 4c_0)/L + …` (`L = log n`), and
  `P(C_n) = π_s + O(1/log n)` at `τ_n = b̂_n + s` (`O(log log n/log n)` at
  `b_n + s`).

**Overlap with Part I, printed and credited.** Part II's Proposition 13.2 and
Corollary 13.3 re-prove Part I's Theorem 4.1 (`tss:thm:uniform`) and
Corollary 6.1 (`tss:cor:coexist`) in the same normalization (`rm = a_n(τ)`,
`κ/m = k`, `Z_n(r) = 4^(−n) W_n(u_n(τ))`); they are printed with their
statements' titles naming the Part I results and a dated note giving the
dictionary, and their proof is the manuscript's, which follows Part I's
Section 4 step for step (not a second route). Lemma 13.1's tail
re-derives Part I's `j^(−5/2)` mass tail with the constant `d` explicit; the
centre, split, recurrences and constant series are Part I's. The opening
coefficients `1, 5, 105/4` of Proposition 17.1 coincide with those of Part I's
`(tss:eq:Hlarge)`: both expand the same heavy-tail kernel. Everything else in
Part II is new to the repository.

### Part III (Sections 21–32, Appendices C–E)

Same law on score sequences, now at weights `u ≥ u_c`: with `r = up`,
`r(t) = 1/Q(e^(−t))`, `t ≥ 0` the excess growth rate (`log 4 + t` is the
growth rate of the weighted count), `h(t) = log r(t)`, `m_t = h'(t)`,
`v_t = −h''(t)`, the tilted law `q_t(j) = r(t) e^(−tj) q_j`, and
`a_n(t) = n(1 − 1/r)/m`, which equals `−τ` under Part II's parametrization
(so this is the side `τ ≤ 0` that Parts I and II exclude). `t_0 > 0` is not
made effective.

- **Proposition 23.1 (exact change of measure).** `Z_n(r(t)) = e^(nt) U_t(n)`,
  `U_t(n)` the probability that the `q_t`-renewal visits `n`; the block
  lengths are that renewal conditioned to visit `n`.
- **Theorem 24.1 (uniform pole–branch expansion).** For every fixed `J`,
  uniformly on `0 ≤ t ≤ t_0`: `Z_n(r(t)) = e^(nt)/m_t + κ/(π r m²) n^(−1/2)
  {Σ_{j<J} K_j(a_n(t)) n^(−j) + O(n^(−J)(1 + a)^(−2))} + O(R_0^(−n))`, with a
  finite generator for every kernel `K_j`; `K_0(a) = √π(1 + a) − π√a(a + 3/2)
  e^a erfc √a`. Lemma 24.2 separates the moving pole from the branch point;
  Corollary 24.3 gives `U_t(n) = 1/m_t + O(e^(−nt) n^(−1/2)(1 + nt)^(−2))`.
- **Section 25.** At `t = 0`, `Z_n(1) = 1/m + κ/(m²√π) n^(−1/2) + κK_1(0)/(πm²)
  n^(−3/2) + O(n^(−5/2))` (the first two terms are Part I's critical
  expansion; the `n^(−3/2)` coefficient, `K_1(0) = −0.22249…`, is new); the
  large-`a` series of `K_0`; at fixed `t > 0` the branch amplitude
  `r d/(r − 1)² n^(−5/2)` (Part I's subcritical amplitude continued).
- **Theorem 26.1** (convergent Puiseux inversion of `h`), the block density
  `θ(t) = 1/m_t` and its quadratic inverse `h = 4m³Δ²/(9κ²) + O(Δ³)`, a
  fixed-weight size inverse with a separation condition, and Lambert-`W_0`
  and incomplete-gamma centres for maxima.
- **Theorem 27.2 (tempered window).** If `t_n b_n → σ ∈ [0, ∞)`, `b_n =
  (κn/m)^(2/3)` (Part II's `a_n`), then `(m_t/b_n)(K_n − n/m_t)` converges to
  the law with characteristic function `exp{(σ + iξ)^(3/2) − σ^(3/2) −
  (3/2) iξ √σ}`, with an `O(n^(−1/3))` characteristic-function error on
  compacts. **Theorem 27.3:** Gaussian count when `n t_n^(3/2) → ∞`, `t_n → 0`.
- **Theorem 28.2.** The large blocks, scaled by `b_n`, converge to a Poisson
  process with intensity `e^(−σx) x^(−5/2) dx/Γ(−3/2)`, with the maximum law
  and an `O(n^(−1/3))` factorial-moment rate. **Theorem 29.1:** in the
  Gaussian regime `t_n M_n − w_n` has a Gumbel limit, `w_n = (5/2)
  W_0((2/5) B_n^(2/5))`.
- **Remark 29.2 (added by the write, with proof).** At a fixed `t > 0` no
  centring makes `t M_n − c_n` converge to a continuous strictly increasing
  law such as the Gumbel law (lattice of fixed span); the manuscript stated
  this without proof.

**Overlap with Parts I–II, printed and credited.** Section 22.1's block
decomposition is CDFS's (the same argument as Part II §11 and Part I §1);
Lemma 22.1's `m`, `κ`, `d` and tail re-derive Part II's Lemma 13.1 (its
`a_2` is Part I's `e_2`, its `β = −mℓ` with Part I's `ℓ = d_4`; `κ_1` is new);
the critical endpoint's first two terms are Part I's Proposition 3.2; the
large-`a` series and `r d/(r − 1)²` are Part I's `(tss:eq:Hlarge)` / Part II's
Proposition 17.1 series and Part I's `(tss:eq:subcritical)`, continued; at
`σ = 0` the count and maximum laws are those of Part II's Theorem 12.3
(proved there conditionally on `F_n` at the subcritical coexistence weight,
here unconditionally at `u ≥ u_c`); the Lambert centre and the separation
condition are instances of `p0:thm:lambert-core` (`a = 1`, `b = 5/2`,
branch `W_0`) and part (2) of `p0:thm:staircase`. Everything else is new to
the repository.

## What is not claimed

- Part I gives no result for `τ < 0` (supercritical moving pole), for
  truncation orders or component counts growing with `n` (in its fixed-weight
  setting), or convergence of the full series. Part III (unrefereed,
  AI-assisted, not formalized) treats the supercritical side `τ = −a_n(t) ≤ 0`
  for `0 ≤ t ≤ t_0` in its own parametrization; Part I's theorems themselves
  are not extended (dated `[write]` notes in the front matter, after
  Proposition 3.2 and after the questions of Section 9).
- Part I's coexistence statement, Corollary 6.1, is by itself a coefficient
  asymptotic, not a conditional mixture law. Part II (unrefereed,
  AI-assisted, not formalized) proves the mixture: the factors `1` and
  `e^(−s)` are the limiting relative weights of the giant event and of its
  complement (Theorem 12.1). Dated `[write]` notes at the end of Section 6
  and after the further questions of Section 9 say so.
- Inverses locate real model inverses; they do not certify integer rounding
  or finite-`n` confidence intervals; weight calibration assumes known `n`.
- All decimals (including high-precision ones) are non-interval checks; the
  remainders are proved analytically.
- Of the further questions of Section 9, question 1 (conditional component
  laws at coexistence) is answered by Part II for compact `s`; question 2
  (supercritical crossover), which Part II restated as its RQ6, is answered
  by Part III on the fixed small interval `0 ≤ t ≤ t_0` (pole residue plus a
  branch expansion to every fixed order, uniformly through coalescence), but
  the joint theory across `τ = 0` asked for by Part II's RQ6 remains open as
  Part III's RQ4 (dated notes at both questions); questions 3 (explicit
  constants) and 4 (growing orders, fixed weight) are unchanged; question 5
  (comparison with general renewal theorems) stays open, Part II's
  literature comparison being a bounded source check. Part II's RQ4
  (quantitative stable approximation on `F_n`) is not answered by Part III's
  `O(n^(−1/3))` rate, which concerns the unconditioned count at `u ≥ u_c`.
- **The inversions are instances of repository results; no novelty is claimed
  for the method.** Part I's explicit order-0 inverse is `p0:thm:lambert-core`
  (`a = log 4`, `b = −5/2`, branch `W_{-1}`), its three localization bounds are
  the residual-to-root conversion `p0:thm:backward-error`, and its bracketing
  remark is the separation condition, part (2) of `p0:thm:staircase`; Part II's
  implicit centre (eq. `tss:cx:eq:Wcenter`) is `p0:thm:lambert-core` with
  `a = 1`, `b = −2`, branch `W_{-1}`, for `x − 2 log x = ½ log n + log(m/d)`.
  All are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  Dated `[write]` notes at the end of Section 7 and after the implicit centre
  in Section 18.1 say so.
- Part II's own limits, kept: its law is on score sequences, not uniformly
  random labeled tournaments; uniformity holds only for `s` in compact
  intervals (growing `s_n` is its RQ5) and never for `τ < 0` (RQ6, now
  answered in part by Part III); the
  general-`α` statement of Section 18.2 is a deduction conditional on two
  analytic inputs, not a theorem; the point-process statements concern points
  bounded away from zero, and no functional limit keeping block positions is
  claimed (RQ1); Corollary 15.1 asserts no moment convergence for the
  unbounded stable or Gamma rescalings; the CDFS bijection is not reproved;
  no priority is claimed for general Gibbs-partition or heavy-tail mechanisms,
  and its literature comparison is a bounded source check, not a proof of
  publication priority.
- Part II's numerics are floating, non-interval diagnostics (the series-tail
  bounds on `λ`, `μ` are rigorous, their decimal evaluation is not
  outward-rounded); its exact checks verify the identities at `n ≤ 10` and
  prove no asymptotic theorem; finite-size corrections are large (`P(C_n)` at
  `s = 0` is 0.524, 0.534, 0.550 at `n` = 512, 2,000, 8,000, not monotone
  toward 1/2), so Figures 1–2 are not convergence evidence; Figure 3 plots
  theoretical limiting densities only.
- Part III's own limits, kept: novelty only relative to the inspected
  report (bounded search, no worldwide priority); the CDFS bijection is not
  reproved; Kolesnik's constants and component law, tilting, renewal
  conditioning, stable laws and Lambert W are prior; every expansion is at a
  **fixed** order, with no convergence of the `1/n` series (only the
  Puiseux inverse is convergent); `t_0` and `R_0` are not effective; the
  count and point-process theorems are **marginal** (no joint count–maximum
  convergence or independence); the characteristic-function estimate is not
  a Kolmogorov or total-variation bound; point processes are local away
  from 0; no continuous Gumbel law at fixed `t > 0`; no certified `O`
  constants, finite-size intervals or integer rounding (the size inverse
  only on `(0, t_0]`, with a separation condition); decimals not
  outward-rounded; finite checks are not proofs; the critical endpoint and
  heavy-tail constant are consistency checks; the law is on score sequences;
  finite-size convergence is slow (the Gumbel-core CDF is still 0.624 at
  `n = 4096`, against the limit 0.368).
- **Priority at the critical endpoint (checked at the batch-98 write).** At
  `u = u_c` the construction `1/(1 − uI(z))` is a critical composition
  scheme with inner singular exponent 3/2, the setting in which
  Banderier–Flajolet–Schaeffer–Soria (2001, Theorem 12, read through the
  account of Banderier–Kuba–Wallner, arXiv:2103.03751) identify the stable
  3/2 (map-Airy) law for the number of components. So the stable limit of
  the block count at the critical weight itself (`σ = 0`, `t_n = 0` in
  Theorem 27.2) is **not** claimed as new; within the repository it is also
  Part II's law of `−Z`. Whether the `σ = 0` maximum law is in that
  literature was not determined. Banderier–Kuba–Wallner and
  Banderier–Kuba–Wagner–Wallner (AofA 2024) work at fixed weights and do not
  perturb the weight near criticality; the uniform pole–branch expansion,
  the window with `t_n > 0` (including `n^(−1) ≪ t ≪ n^(−2/3)`), the
  tempered laws for `σ > 0`, the Gaussian side and the Gumbel regime were
  not found in the sources checked and stay "new relative to the
  repository". Limits of the check: Flajolet–Sedgewick's text was not
  consulted (only its section title), BFSS only through that account, and
  the announced companion paper on stable laws could not be checked
  (Part III's further question F8). [Independent check, 7 October 2026:
  Flajolet–Sedgewick's Section IX.11 was then read, in the authors' online
  edition (pp. 703–712 there). Its Theorem IX.16(ii), on semi-large powers,
  gives the `σ = 0` count law in local form (with `H = Q`, exponent 3/2,
  `h_1 = m`), so that law is in the textbook too; Section IX.11 has no
  law of the largest component, no weight moving with `n` and no tempered
  window. F8 stays open for BFSS's Theorem 12 and the companion paper.]
- **Unproved claims of Part III, recorded as further questions** (Section
  31.1, items F1–F8, under the standing rule of 4 October 2026): the full
  tail expansion of Lemma 22.1 (F1) and the complex sector bound of Lemma
  27.1 (F2), both sketched; the block density `θ(t) = 1/m_t` (F3: given a
  proof at the write, `E K_n = n/m_t + v_t/m_t² + O(e^(−nt/2))` at fixed
  `t`, conditional on Lemma 27.1); non-effective `t_0`, `R_0` and the generator's integrability
  (F4); the "required by analyticity" heuristic of Section 25.1 (F5, the
  cancellation itself verified); the continuation of Part I's expansion to
  `τ < 0` (F6: the identity `H(−a) = K_0(a)/π + e^a(a^(3/2) + (3/2)a^(1/2))`
  is proved at the write, and with it Part III's first two terms reproduce
  Part I's formally at `τ = −a`, numerically to `O(1/n)`; the every-order
  continuation is open, a case of RQ4 and of Part II's RQ6); RQ1 read
  against Part II's joint limit (F7); the bibliographic priority question
  (F8). The manuscript's RQ1–RQ9 are printed as delivered. No claim of the
  manuscript was found false; its unproved "no continuous Gumbel limit at
  fixed `t`" is proved in Remark 29.2.
- **Independent check of the batch-98 write (7 October 2026).** An
  adversarial check by the intake after the write (`a763feee1`) isolated
  every hand edit (by rebuilding the mechanical assembly from a fresh
  extraction) and re-derived each added statement with its own code:
  `N_n`, `S_n`, `I_n` to `n = 2000` agree with the OEIS b-files fetched
  again (A000571 #154, A351822 #49, A145855 #55, none revised since the
  manuscript's inspection) and a Landau enumeration gives the block-count
  polynomials for `n ≤ 11`; the identifications of the provenance note
  (`κ/m = 2/(3μ)`, `m = a_c`, `a_2 = e_2`, `β = −mℓ`, `d`, `Γ(5/2)/π`) hold
  at 60 digits; `K_1(0) = −0.222493573879597` by formula, quadrature and the
  check's own transfer expansion; the remainders `−0.0109`, `−0.0103`,
  `−0.0101`, `−0.0100` after Proposition 3.2 and the F6 values `7.31`,
  `7.09`, `6.95`, `6.84` were reproduced from exact coefficients; the F6
  identity and the `K_0` closed form hold to `2·10^(−36)`; F3's
  `E K_n = n/m_t + v_t/m_t² + O(e^(−nt/2))` holds with far smaller errors
  at `t = 0.2, 0.5`; Remark 29.2, the RQ6 note, the transseries instances,
  the provenance record and the accounts of Banderier–Kuba–Wallner and
  Banderier–Kuba–Wagner–Wallner were confirmed. No mathematical error.
  Corrected with the first wording kept: the front matter's "the rest is new
  to the repository", which omitted the overlaps listed in the provenance
  note. Dated additions: Flajolet–Sedgewick's Section IX.11 read (above);
  the last digits of `κ` and `d` in (143) are rounded, not truncated; the
  arXiv record of Grabchak's paper has a single version (v1, 5 September
  2011), not the "revised version" the manuscript's bibliography mentions.
  The check is recorded in a dated note at the end of Section 31.1.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; no manuscript
used a ProveIt theorem (Part II uses Part I, which it re-proves where it needs
it; Part III imports neither, re-deriving its analytic input from CDFS's
identity). The generic staircase arithmetic named in the Section 7 note (and
in the Section 26 note of Part III) is formalized as `Fabius.staircase_ceil`
and `Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `S_n` or `W_n`. Part II's
RQ9 and Part III's RQ9 propose formalization orders (equality-index
decomposition, marked-block identities, total-variation lemma, then the
local generator and the Puiseux inverse recursion); none of it exists.

**Neighbouring reports.** None: no other repository report treats tournament
score sequences or A000571, A351822, A145855, A054946 (searched at all
three placements and again at the batch-98 write; no other batch-98
manuscript concerns tournaments). Batch-77 manuscripts 13 and 14 (cluster P5, beta renewals) use
the word "renewal" for an unrelated object. The batch-77 report
`a116379-bounded-identity-trees` shares only the delivered PDF build script
(byte-identical `build_pdf.sh`), and `a380592-tied-football-seasons`
mentions this report as a different model that it does not use. Part II's
`data/02-coex-requirements.txt` is byte-identical to a requirements file first
added to the repository in `ce9b89f2b` (Fabius frontier tree), a coincidence of
pinned versions.

## Notation

Part I reuses letters: `s` is both the Hankel variable `nw` and the
coexistence shift; `b_j` are Puiseux coefficients and `b_n` the coexistence
centre; `W` is the weighted generating function and `W_{-1}` Lambert's
function; `t` is `√(1−4z)` and the free parameter of the weight model;
`c`, `C`, `D`, `d`, `E`, `H`, `h`, `k`, `K`, `M` have two or three meanings
each. A table in the first `[write]` note (after "Results and scope at a
glance") fixes each symbol by section, with the tempting false readings.

**Part II's symbols clash with Part I's**, and are printed as delivered: its
`m` is Part I's `a_c` (a mean block length, not a block count); its `κ/m` is
Part I's `k`; its `rm` is Part I's `a_n(τ)`, while its `a_n` is the stable
scale `(κn/m)^(2/3)`; its `r_n` is a normalized weight (Part I's `r_n` is its
`R_n`); its `k` is a block-count index and `K_n` a block count (not a
truncation order); its `d` is the tail amplitude; its `B_n(r)` is the giant
weight and `B_n` (no argument) the second-maximum scale; its `h_n`, `G`, `L`,
`c_0`, `δ`, `J`, `g`, `T` differ from Part I's letters too. A second table, in
the `[write]` note at the start of Part II, fixes every Part II symbol with
Part I's meaning beside it as the false reading; the manuscript's own symbol
list is Appendix A. No symbol of either manuscript was renamed.

**Part III's symbols clash with both**, and are printed as delivered: its
`b_n = (κn/m)^(2/3)` is Part II's `a_n` (not the coexistence centre); its
`a_n(t) = n(1 − 1/r)/m` equals `−τ` (not Part I's `a_n(τ)`); its `τ`, used
only in Lemma 27.1, solves `h(τ) = log r` and is close to `t ≥ 0`, opposite
in sign and scale to the `τ` of Parts I–II; `t` is the tilt, `h = log r`;
`H(v)`, `B(v)` are boundary factors on the cut, not Part I's kernel `H(τ)`
or odd series `B(t)`; `K_j(a)` (printed `𝒦_j`) are cut kernels, not Part I's
`𝒦_{α,b}`; `M_n` is the maximum block (Part II's `M_{1,n}`), `L`, `ℓ`, `s`,
`w`, `B_n`, `E`, `U_t`, `V_{k,t}`, `X_n`, `σ`, `N`, `J` differ too. A third
table, in the `[write]` note at the start of Part III, fixes every Part III
symbol with the Parts I–II meaning as the false reading; the manuscript's
own list is Appendix C. Its `\Pp` is typeset with Part II's `\Prob` (the same
`ℙ`); no symbol was renamed.

## Labels

Every label carries the prefix `tss:`; Part II's carry `tss:cx:`. Part I's 73
labels (prefixed in the batch-77 write) are unchanged, and a comparison of
the `.aux` files of the old and new builds confirms that every one of them
keeps its number: wrapping Part I in `\part` does not renumber sections in
the `article` class, and Part II's sections continue as 10–20. The batch-85 write added 101 labels (174 in all):
`tss:part:one`, `tss:cx:part`, Part II's 97 manuscript labels prefixed before
anything cited them (every `\ref`/`\eqref` updated), and
`tss:cx:fig:profiles`, `tss:cx:app:notation`. The batch-98 write added 113
labels (287 in all), all with the sub-prefix `tss:sc:`: `tss:sc:part`, Part
III's 107 manuscript labels prefixed before anything cited them, and
`tss:sc:sec:writequestions`, `tss:sc:sec:conclusion`, `tss:sc:rem:lattice`,
`tss:sc:eq:Hreflect`, `tss:sc:app:package`. A comparison of the `.aux` files
of builds of the committed and the new text shows all 174 earlier labels
present with unchanged numbers (only their page numbers moved): Part III's
sections 21–32 are placed before Part II's `\appendix`, so Appendices A–B
keep their letters and Part III's appendices follow as C–E.

The batch-77 write added three dated `[write]` notes to Part I (front
matter: provenance, credit, notation table; Section 7: the
transseries-instance note; Section 8.1: the shipped layout and the intake's
independent check), typeset the six binomial coefficients with `\binom`
instead of `\choose` (identical output; removes the delivered source's amsmath
"Foreign command \atopwithdelims" warning), and set the bibliography
ragged-right. The batch-85 write

- wrapped Sections 1–9 as Part I (`\part`, no renumbering) and appended
  Part II after them, moving the shared bibliography to the end;
- added a Part II line to the title block and a Part II paragraph to the
  abstract, three dated notes to Part I (front matter: the two Parts; end of
  Section 6: the mixture; after the questions of Section 9: question 1
  answered), and five to Part II (provenance and overlaps; notation table;
  the re-proof of Part I in Section 13.2; the transseries instance in
  Section 18.1; the shipped files and the intake rerun in Section 19.2);
- printed Part II's summary and "main result in one display" as unnumbered
  paragraphs, pointed the manuscript's references to "the pinned ProveIt
  report" (its abstract, Section 10.1 and its status table) to Part I, named
  the restated Part I results in the titles of Proposition 13.2 and
  Corollary 13.3, and merged the bibliographies (Part II's `Repo` entry is
  replaced by internal references, its pin and path recorded in the
  provenance note; four entries added; the OEIS entry notes Part II's access
  date);
- displayed the shipped phase-profile figure, which the manuscript ships but
  does not display, as Figure 3, with a caption taken from the delivered code
  README;
- added the packages `longtable`, `graphicx`, `xurl`, a `definition` theorem
  style and Part II's macros (`\E \Prob \R \N \TV \Law \ind \dto \pto \Cev
  \Fev \Cov`; Part I's `\ii \e \dd \Var` already had the same definitions).

The batch-98 write (5 October 2026)

- inserted Part III (`\part`, Sections 21–32) after Part II's further
  questions and before its `\appendix`, and its appendices after Part II's as
  C–E with "(Part III)" added to their titles; the running head reads
  "Part III: beyond criticality" on its pages and Part II's head is restored
  for Appendices A–B; the Part's table-of-contents entry is shortened to
  "… and tempered crossovers" (the full title would overflow the contents
  line);
- dropped the manuscript's title page and table of contents, printing its
  abstract as "Summary" and its title-page "Deliverable" and "Scope" lines as
  a paragraph; pointed its references to "the existing ProveIt report" and
  its `Repo` citation (pin and README lines recorded in the provenance note)
  to Parts I–II; mapped its three OEIS citations to the shared OEIS entry
  (with Part III's access date) and added Grabchak; typeset `\Pp` as
  `\Prob`; read the five table fragments from the shipped
  `data/03-supercrit-*_table.tex`; added the macros `\Kc`, `\Li`, `\PPP`
  (the manuscript's unused `\supp` is not defined);
- added a Part III line to the title block, a Part III paragraph to the
  abstract and to `pdfsubject`, dated notes in Part I (front matter: three
  Parts; after Proposition 3.2: the `n^(−3/2)` coefficient; after the
  Section 9 questions: question 2 answered), in Part II (after its further
  questions: RQ6 in part, RQ4 not; at the head of the appendices: which
  Part each appendix belongs to) and in Part III (provenance, dictionary and
  overlaps; notation table; priority at the critical endpoint; the
  transseries instances in Section 26.3; the shipped layout and the write's
  rerun in Section 30.7; the shipped package in Appendix E), Remark 29.2
  with its proof, and Section 31.1 (further questions F1–F8 under the
  standing rule, with the proofs of F3 and of the identity of F6);
- added four bibliography entries for the priority note (BFSS, Flajolet–
  Sedgewick, Banderier–Kuba–Wallner, Banderier–Kuba–Wagner–Wallner).

No statement, proof or number of any manuscript was changed.

## Files

```text
README.md                                     this guide (replaces the three delivery READMEs)
article.tex                                   the report (Part I delivered as report.tex; Part II as tournament_coexistence.tex; Part III as article.tex)
article.pdf                                   compiled report, 82 pages
02-coex-code-README.md                        Part II: delivered code README (algorithms, precision, outputs)
03-supercrit-SOURCE_NOTES.md                  Part III: delivered source and provenance notes (pin, bounded literature check)
code/run_checks.py                            Part I: one command for all checks; writes results/ beside scripts/ (see below)
code/check_exact_counting.py                  Part I: independent Landau enumeration through n = 10
code/check_scores.py                          Part I: exact integer recurrences through n = 1000 and constants
code/check_crossover.py                       Part I: normalized weighted recurrence and two-term models
code/check_higher_crossover.py                Part I: corrected third term and fixed second corrections
code/uniform_generator.py                     Part I: finite half-power generator through M = 4
code/check_weight_inverse.py                  Part I: known-size component-weight inverse checks
code/verify_manifest.py                       Part I: delivered SHA256SUMS check (the manifest is not shipped)
code/replay.sh                                Part I: delivered replay: run_checks.py, then build_pdf.sh
code/build_pdf.sh                             Part I: delivered PDF build (compiles report.tex beside it)
code/02-coex-verify_and_plot.py               Part II: exact checks (n <= 10), floating diagnostics to n = 8000, figures
code/02-coex-build.sh                         Part II: delivered PDF build (compiles tournament_coexistence.tex beside it)
code/03-supercrit-reproduce.py                Part III: exact checks (n <= 180, Landau n <= 10), constants, recurrences, diagnostics to n = 4096
code/03-supercrit-symbolic_audit.py           Part III: SymPy audit of the coefficients of h, the inverse, K_1, the density response
code/03-supercrit-make_tables.py              Part III: CSV-to-LaTeX formatting of the five tables (reads/writes data/ beside code/)
code/03-supercrit-build.sh                    Part III: delivered PDF build (three pdflatex passes on article.tex beside it)
code/03-supercrit-build.ps1                   Part III: the same in PowerShell
data/exact-counting-checks.json               Part I: Landau enumeration S_n, I_n, S_{n,m} for n <= 10
data/score-checks.json                        Part I: recurrence checks and scaled residuals
data/crossover-checks.json                    Part I: two-term crossover checks
data/higher-crossover-checks.json             Part I: third-term and fixed second-correction checks
data/allorders-crossover-checks.json          Part I: 21 crossover points through M = 4
data/weight-inverse-checks.json               Part I: 24 weight-inverse cases
data/verification.json                        Part I: status PASS, symbolic c_1, c_2, d_4, C_2, and source hashes
data/requirements.txt                         Part I: mpmath==1.3.0, sympy==1.14.0
data/02-coex-verification_summary.json        Part II: exact assertions, constants, floating diagnostics
data/02-coex-run_log.txt                      Part II: stdout transcript of the delivered run
data/02-coex-coexistence_diagnostics.csv      Part II: giant probabilities, 33 offsets x n = 512, 2000, 8000 (CRLF)
data/02-coex-component_count_distribution.csv Part II: joint law of block count and giant event, n = 1000, s = 0 (CRLF)
data/02-coex-normalized_counts.csv            Part II: selected normalized counts (CRLF)
data/02-coex-renewal_mass.csv                 Part II: the critical block law q_n for n <= 8000
data/02-coex-provenance.json                  Part II: pin, continued report, scope, validation record
data/02-coex-requirements.txt                 Part II: numpy==2.3.5, scipy==1.17.0, matplotlib==3.10.8, mpmath==1.3.0
data/03-supercrit-verification.json          Part III: exact checks, 60-digit constants, environment of the recorded run
data/03-supercrit-run.log                     Part III: stdout transcript of the delivered reproduce.py run
data/03-supercrit-symbolic_audit.json         Part III: six symbolic identities, all PASS
data/03-supercrit-symbolic_run.log            Part III: stdout transcript of the delivered symbolic audit
data/03-supercrit-oeis_exact_0_80.csv         Part III: exact S_n, I_n, N_n for n <= 80 (computed; equal to OEIS data)
data/03-supercrit-branch_errors.csv           Part III: pole/branch errors for U_t(n), n = 256, 1024, 4096, nt = 0, 1, 4 (CRLF)
data/03-supercrit-tempered_characteristics.csv Part III: tempered-window characteristic functions (CRLF)
data/03-supercrit-maximum_cdf.csv             Part III: maximum-block CDFs at x = 1, 2 (CRLF)
data/03-supercrit-gaussian_gumbel.csv         Part III: Gaussian-count and Gumbel diagnostics at t = n^(-1/4) (CRLF)
data/03-supercrit-inverse_errors.csv          Part III: errors of the free-energy inverse (CRLF)
data/03-supercrit-branch_table.tex            Part III: Table 3 fragment (input by article.tex)
data/03-supercrit-characteristic_table.tex    Part III: Table 4 fragment
data/03-supercrit-maximum_table.tex           Part III: Table 5 fragment
data/03-supercrit-gaussian_table.tex          Part III: Table 6 fragment
data/03-supercrit-inverse_table.tex           Part III: Table 7 fragment
data/03-supercrit-build_quality.json          Part III: delivered PDF build record (27 pages, SHA-256 of the delivered source and PDF)
data/03-supercrit-requirements.txt            Part III: numpy==2.3.5, mpmath==1.3.0, sympy==1.14.0
figures/02-coex-giant_probability.pdf         Part II: Figure 1 (and .png)
figures/02-coex-giant_probability.png
figures/02-coex-component_count_distribution.pdf  Part II: Figure 2 (and .png)
figures/02-coex-component_count_distribution.png
figures/02-coex-phase_profiles.pdf            Part II: Figure 3, theoretical densities (and .png)
figures/02-coex-phase_profiles.png
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. The three Part II figure PDFs and the five
Part III table fragments are inputs of `article.tex`; the PNGs are delivered
raster copies. The eight CRLF CSVs (three of Part II, five of Part III) keep
their delivered line endings through `-text` lines in
`SetTheory/Cardinals/.gitattributes`. Part III's two `.log` files are
tracked although `*.log` is ignored (force-added at placement).

**Part I** placement renamed `report.tex` to `article.tex`, `scripts/` to
`code/` and `results/` to `data/`, and moved `replay.sh`, `build_pdf.sh` (to
`code/`) and `requirements.txt` (to `data/`). Not shipped: the delivered
15-page PDF `report.pdf` and `SHA256SUMS` (a checksum ledger, verified 21/21
at placement and retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/tournament-score-sequences-source.zip > <scratch>/tournament-score-sequences-source.zip`.

**Part II** placement prefixed every file with `02-coex-` and moved
`code/README.md` to the report root (`02-coex-code-README.md`), `build.sh`
to `code/`, and `code/requirements.txt` and `provenance.json` to `data/`.
Not shipped: `tournament_coexistence.tex` (printed as Part II),
`tournament_coexistence.pdf` (25 pages), the delivery `README.txt`, and
`SHA256SUMS.txt` (a checksum ledger, verified 20/20 at placement and
retired). All survive in the archive:
`git show 317c1ce2e:docs/incoming/tournament_coexistence_research.zip > <scratch>/tournament_coexistence_research.zip`.

**Part III** placement prefixed every file with `03-supercrit-` and moved
`SOURCE_NOTES.md` to the report root, `build.sh`, `build.ps1` and the three
programs to `code/`, and `requirements.txt` and every `data/` file to
`data/`. Not shipped: `article.tex` (printed as Part III), `article.pdf` (27
pages), the delivery `README.md`, and `SHA256SUMS.txt` (a checksum ledger,
verified 26/26 at placement and retired). All survive in the archive:
`git show 2172df76a:docs/incoming/tournament_supercritical.zip > <scratch>/tournament_supercritical.zip`.
`data/03-supercrit-oeis_exact_0_80.csv` is computed by the program, not
copied, but its numbers are those of OEIS A000571, A351822 (without its
empty object) and A145855, whose data are licensed CC BY-SA 4.0; nothing was
submitted to the OEIS.
Nothing heavy was excluded from any Part (the largest file is
`data/02-coex-renewal_mass.csv`, 263 KB; Part III's largest is
`code/03-supercrit-reproduce.py`, 12.7 KB).

Delivered text that names the delivery layout or unshipped files:
`code/run_checks.py` (reads `scripts/`, writes `results/` under the package
root, and says the requirements are in `../requirements.txt`),
`code/check_*.py` and `code/uniform_generator.py` (write `../results/`),
`code/verify_manifest.py` (reads `SHA256SUMS`), `code/replay.sh` and
`code/build_pdf.sh` (`scripts/run_checks.py`, `report.tex`, `report.pdf` in
their own directory), and Section 8.1 of the article (dated note). The
delivery README of Part I began its replay with
`python3 scripts/verify_manifest.py`. For Part II:
`code/02-coex-verify_and_plot.py` writes `data/` and `figures/` beside
`code/` under the unprefixed names unless given `--output-root`;
`02-coex-code-README.md` says to run `python code/verify_and_plot.py` from the
archive's main directory and names `requirements.txt`, the unprefixed outputs
and the "adjacent `data/` and `figures/`"; `code/02-coex-build.sh` compiles
`tournament_coexistence.tex` beside itself; `data/02-coex-provenance.json`
records the delivered PDF's 25 pages and its LaTeX check; and Section 19.2
of the article describes the delivered package (dated note).
For Part III: `code/03-supercrit-reproduce.py` and
`code/03-supercrit-symbolic_audit.py` write unprefixed files into the
`data/` directory beside `code/` unless given `--output`;
`code/03-supercrit-make_tables.py` always reads and writes unprefixed names
there; `code/03-supercrit-build.sh` and `.ps1` compile an `article.tex`
beside themselves (the delivered one, not shipped);
`data/03-supercrit-build_quality.json` records the delivered PDF (27 pages,
"latex_warnings: []", though a rebuild of the delivered source gives one
pdfTeX duplicate-destination warning for `page.1` from its title page) and
the SHA-256 of the delivered `article.tex` and PDF; Sections 30.1 and 30.7
and Appendix E of the article describe the delivered package (dated notes in
Section 30.7 and Appendix E give the shipped names).

## Rerun the checks (on a scratch copy)

No Part's programs should be run in place: they write into `results/`,
`data/` or `figures/` beside their own directory and would overwrite the
recorded outputs or create unprefixed files.

**Part I.** `run_checks.py` also looks for its siblings in `scripts/`.
Rebuild the delivered layout on a copy (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir -p "$R/scripts" "$R/results" && cp code/*.py "$R/scripts/" && rm "$R/scripts/02-coex-verify_and_plot.py" && cd "$R"
export PYTHONUTF8=1
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python scripts/run_checks.py
for f in "$OLDPWD"/data/*-checks.json "$OLDPWD"/data/verification.json; do diff -q --strip-trailing-cr "results/$(basename "$f")" "$f"; done
```

It enumerates Landau sequences through `n = 10`, runs the integer recurrences
to `n = 1000`, asserts the symbolic `c_1`, `c_2`, `d_4`, `C_2` identities, and
checks the 21 crossover and 24 inverse cases against non-interval envelopes;
it also writes one `.log` per script into `results/`. At intake (2 October
2026, heavily loaded machine) it took about 165 s, reported status PASS, and
all seven JSON files equalled the recorded ones up to line endings (Windows
writes CRLF, hence `--strip-trailing-cr`); the recipe, run in the batch-77
write phase, passed in 79 s with the same result. `verification.json` records
source hashes of the scripts at their `scripts/` paths.

**Part II.** Run the program on a copy with an explicit output root:

```sh
R=$(mktemp -d) && cp code/02-coex-verify_and_plot.py "$R/" && cd "$R"
export PYTHONUTF8=1
uv run --no-project --python 3.12 --with numpy==2.3.5 --with scipy==1.17.0 \
  --with matplotlib==3.10.8 --with mpmath==1.3.0 python 02-coex-verify_and_plot.py --output-root out
diff --strip-trailing-cr <(head -n 270 out/data/verification_summary.json) <(head -n 270 "$OLDPWD/data/02-coex-verification_summary.json") && echo exact part identical
```

It enumerates all 125,476 nondecreasing candidate lists through `n = 10`,
asserts that both the block-count and the giant-event polynomials agree
coefficientwise with the recurrences and the marked-block identity, computes
the constants (series-tail bounds rigorous, decimals not outward-rounded) and
the normalized renewal masses to `n = 8000`, and redraws the three figures.
The floating diagnostics depend on the platform's `numpy.longdouble`. **On
Windows `longdouble` is ordinary double precision** (52 stored mantissa bits;
the recorded run had 63, on Linux), so a Windows rerun reproduces the exact
part, not the floating digits. At intake (3 October 2026, Windows, Python
3.12, the pinned packages; 33 s of script time on one run and 52 s on a
loaded machine in the write phase) the run exited 0; the first 270 lines of
`verification_summary.json` (all exact checks and constants) were identical
up to line endings, and the remaining 35 changed lines were all floating
diagnostics (for example the giant probability at `n = 8000`, `s = 0`:
0.5498246416912899 against the recorded 0.549824641691181). The CSVs agreed
to a relative 7.2e−13 (`coexistence_diagnostics`), 3.4e−15
(`normalized_counts`) and 4.6e−15 (`renewal_mass`), and
`component_count_distribution` to an absolute 6.4e−14 (relative differences
up to 1 occur only in entries of order 1e−39, FFT noise). On Windows the
program writes `renewal_mass.csv` and `verification_summary.json` with CRLF
line endings (the recorded files are LF), and the figure files differ in
bytes from the recorded ones. `elapsed_seconds` differs on every run.
`data/02-coex-run_log.txt` is the delivered run's stdout, which the program
prints but does not write. The delivered package's own instructions
(`python code/verify_and_plot.py` from the package root) apply only to a
re-extraction of the archive, never to this directory.

**Part III.** Rebuild the delivered `code/` + `data/` layout on a copy,
pass `--output` explicitly, and compare (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir -p "$R/code" "$R/data" && for f in reproduce symbolic_audit make_tables; do cp "code/03-supercrit-$f.py" "$R/code/$f.py"; done && cd "$R"
export PYTHONUTF8=1
U="uv run --no-project --with numpy==2.3.5 --with mpmath==1.3.0 --with sympy==1.14.0 python"
$U code/reproduce.py --max-n 4096 --dps 60 --output data > run.log && $U code/symbolic_audit.py --output data > symbolic_run.log && $U code/make_tables.py
for f in data/*; do b=$(basename "$f"); diff -q --strip-trailing-cr "$f" "$OLDPWD/data/03-supercrit-$b" >/dev/null && echo "same $b" || echo "DIFF $b"; done
```

It computes `N_n`, `S_n`, `I_n` with integers to `n = 180` and checks the
hard-coded OEIS initial terms, enumerates the Landau tuples for `n ≤ 10` and
compares the whole component-count polynomial, checks the float recurrence
against the exact values to `n = 30`, computes the constants at 60 digits,
the pole–branch, tempered, maximum, Gaussian/Gumbel and inverse diagnostics
to `n = 4096`, runs the six SymPy identities, and re-formats the five tables.
At the batch-98 write (5 October 2026; Windows, Python 3.13.5 under `uv`,
the pinned packages; 21 s) it exited 0, and so did the recipe above.
`oeis_exact_0_80.csv`, `symbolic_audit.json`, `inverse_errors.csv`, the
captured `symbolic_run.log` and four of the five `*_table.tex` were identical
to the shipped files up to line endings; `verification.json` differed only
in its `python`, `platform` and `seconds` fields (the recorded run was on
Linux); the floating CSVs agreed to an absolute 8e−15 (`branch_errors`),
7.4e−13 (`tempered_characteristics`), 9.0e−13 (`maximum_cdf`) and 5.5e−10
(`gaussian_gumbel`), so `branch_table.tex` changes four last digits (for
example 5.76e−14 to 6.56e−14 at `n = 4096`, `nt = 4`, an entry the article's
caption calls floating-point noise). The placement's earlier rerun (Python
3.13.5, NumPy 2.3.5, 61 s) had the same outcome. On Windows the programs
write CRLF line endings. `data/03-supercrit-run.log` is the stdout of the
delivered `reproduce.py` run, which the program prints but does not write,
and `build_quality.json` is written by no shipped program. The delivered
package's own instructions (`python code/reproduce.py …` and `./build.sh`
from the package root) apply only to a re-extraction of the archive, never to
this directory.

## Build the PDF

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, enumitem, longtable, graphicx, xcolor, hyperref, xurl,
fancyhdr; the preamble uses `\pdfmapfile`); no BibTeX. The Part II figures are
read from `figures/` and the Part III tables from `data/03-supercrit-*_table.tex`.
From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 82 pages
(title and front matter pages 1–3, contents 4–7, Part I pages 8–21, Part II
pages 22–48, Part III pages 49–77, Part II's Appendices A–B pages 78–79,
Part III's Appendices C–E pages 80–81, references pages 81–82; 81 pages
before the independent check of 7 October 2026), no errors,
no LaTeX warnings,
no undefined references or citations, no multiply defined labels, no
duplicate PDF destinations, no overfull or underfull boxes. The log's pdfTeX
notices "fontmap entry … already exists, duplicates ignored" (684 of them)
come from the `\pdfmapfile` lines and are identical in a build of the
batch-77 text, which had 17 pages, and of the batch-85 text (47 pages).
`code/build_pdf.sh`, `code/02-coex-build.sh` and `code/03-supercrit-build.sh`
/ `.ps1` are kept as delivered; each builds only its own manuscript's
delivered source, which is not shipped.

## Provenance

- Claesson–Dukes–Franklín–Stefánsson, Proc. Amer. Math. Soc. 151 (2023)
  3691–3704, Corollaries 12–13; Kolesnik, Combinatorica 43 (2023) 827–844;
  Bassan–Donderwinkel–Kolesnik, Electron. Commun. Probab. 31 (2026) 3;
  Blanchet–Glynn, Adv. Appl. Probab. 39 (2007); Olvera-Cravioto–Blanchet–Glynn,
  Ann. Appl. Probab. 21 (2011); Białas–Bogacz–Burda–Johnston, Nucl. Phys. B
  575 (2000); Stufler, Ann. Inst. H. Poincaré Probab. Statist. 60 (2024);
  Denisov–Dieker–Shneer, Ann. Probab. 36 (2008); Armendáriz–Loulakis, Stoch.
  Proc. Appl. 121 (2011); OEIS A000571, A351822, A145855, A054946 (checked
  2 October 2026 by manuscript 01; A000571, A351822, A145855 accessed
  3 October 2026 by manuscript 02 and 4 October 2026 by manuscript 03);
  Grabchak, arXiv:1109.1028 (cited by Part III); for the batch-98 priority
  check, Banderier–Flajolet–Schaeffer–Soria, Random Structures Algorithms 19
  (2001) 194–246, Flajolet–Sedgewick, *Analytic Combinatorics* (2009),
  Banderier–Kuba–Wallner, arXiv:2103.03751v3 (2024), and
  Banderier–Kuba–Wagner–Wallner, AofA 2024, doi:10.4230/LIPIcs.AofA.2024.7.
- Source 01 (Part I): batch 77 of `docs/incoming`, manuscript 68 (cluster
  P3); arrival `096ee7b87`, placement `34f1acd4b`, written in the batch-77
  write phase (2 October 2026). No pin.
- Source 02 (Part II): batch 85 of `docs/incoming`, manuscript 04; arrival
  `317c1ce2e`, placement `713149ded` (batch 85A), written in the batch-85
  write phase (3 October 2026). Pin `d68b65ea064084fb121df9bb431b21d086f7be81`;
  `git diff d68b65ea0 713149ded` on this report's `article.tex` is empty, so
  the manuscript continued exactly the text printed as Part I.
- Source 03 (Part III): batch 98 of `docs/incoming`, manuscript 03 (of
  eleven); arrival `2172df76a`, placement `9353a7171` (batch 98A), written in
  the batch-98 write phase (5 October 2026). Pin
  `106eb191a2a47ab6281e2c26c7f4fe3d28872b83` (a merge commit, an ancestor of
  the placement); `git diff 106eb191a 9353a7171` on this report's
  `article.tex` and `README.md` is empty, so the manuscript continued exactly
  the text printed as Parts I–II. Its `SOURCE_NOTES.md` records that it read
  the README at the pin (blob `63322ccbce51…`, lines 120–170) and parts of
  the article through a GitHub connector.
- Choices of the merge: Part II is appended as a Part, not interleaved;
  Part II's re-proof of Part I's Theorem 4.1 and Corollary 6.1 is printed as
  delivered with credit, not removed and not presented as a second route;
  Part II keeps its own notation, fixed by its own table, rather than being
  renamed into Part I's; the shipped but undisplayed phase-profile figure is
  displayed. Part III is likewise appended as a Part, before Part II's
  appendices (so no existing label is renumbered), with its own notation
  table; its re-derivations of Part I's critical expansion, Part II's tail
  lemma and the shared constants are printed as delivered with credit, not
  as second routes; the `σ = 0` coincidence with Part II's Theorem 12.3 is
  noted, not merged.
