# Fixed-Height Shifted Rectangles

**Part I: an unconditional proof of the A181199 asymptotic, all-order expansions, and an algebraicity dichotomy. Part II: rational diagonals and rare boundary phases — D-finiteness at every fixed height and a sharp exponential refinement. Part III: a proof of the height-four shifted rectangle conjecture (A181198, Kauers–Koutschan Conjecture 18). Part IV: a complete exact formula for height five (A181199, Conjecture 19). Part V: two earlier independent routes — all-order asymptotics, rational diagonals and transcendence**

A research report in five Parts, built from six manuscripts: Part I dated
3 October 2026, Part II dated 4 October 2026 and added on 5 October 2026,
Parts III and IV dated 5 October 2026 and Part V's two manuscripts dated 1
and 2 October 2026, all four added on 5 October 2026 (batch 101). The title
pages of the sources of Parts I–IV read "Prepared for Vladimir
Reshetnikov" and their PDF author fields "Research report prepared for
Vladimir Reshetnikov"; none of them names a human author or a tool. The
two manuscripts of Part V read "Research report prepared for Vladimir
Reshetnikov with OpenAI": they name a tool.

**Headline (5 October 2026).** Parts III and IV prove, from the array
definition and for every `n ≥ 1`, the recurrences that OEIS A181198 and
A181199 display as conjectural and Conjectures 18 and 19 of Kauers and
Koutschan (J. Integer Seq. 26 (2023) 23.4.5) — questions that Parts I and
II left open.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 09 | `Shifted_Rectangle_Asymptotics.zip` (wrapper directory `Shifted_Rectangle_Asymptotics/`, 343,338 bytes, 21 files), arrival commit `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, the ProveIt bibliography entry and `notes-SOURCES_AND_STATUS.md`) | `ddf8df5d5` (batch 85C) | Part I: Sections 1–13, Appendices A–B |
| 02 | batch 98, manuscript 02 | `Shifted_Rectangle_Boundary_Research.zip` (doubled wrapper directory `Shifted_Rectangle_Boundary_Research/Shifted_Rectangle_Boundary_Research/`, 390,943 bytes, 22 files), arrival commit `2172df76a`; main file `article.tex` | `db20eb379` (`db20eb37982abc0f163c6d308d392f5ac4c9bc62`, 4 October 2026, quoted in Section 14.2 and `02-boundary-phases-notes-SOURCES_AND_STATUS.md`) | `0fba5167f` (batch 98B) | Part II: Sections 14–25, Appendices C–D |
| 03 | batch 101, Research Report 231 of the session bundle | `Report231.zip` (doubled wrapper directory `Report231/Report231/`, 514,097 bytes, 20 files), arrival commit `60f54ea06`; `article.tex` plus eight section files | no commit; this report's source by Git blob `2b40ded9daa6549f786a52b880d5477de3b5adfc` (= `article.tex` of `6fef5383b`, Part I only); also a "user-held copy" of Part II's manuscript | `f7c612c72` (batch 101) | Part III: Sections 26–33 |
| 04 | batch 101, Research Report 233 | `Report233.zip` (doubled wrapper directory `Report233/Report233/`, 614,266 bytes, 22 files), arrival commit `60f54ea06`; `article.tex` plus eleven section files | the same blob `2b40ded9` | `f7c612c72` (batch 101) | Part IV: Sections 34–42, Appendix E |
| 05 | batch 101, Research Report 85 | `ProveIt_Fixed_Height_Shifted_Strips_Asymptotics.zip` (no wrapper, 357,992 bytes, 21 files), arrival commit `60f54ea06`; `article.tex` | none (no repository read) | `f7c612c72` (batch 101) | Part V: Section 43 |
| 06 | batch 101, Research Report 91 | `ProveIt_Shifted_Strips_Rational_Diagonals_and_Transcendence.zip` (no wrapper, 371,265 bytes, 12 files), arrival commit `60f54ea06`; `article.tex` | none; cites source 05 as an "unpublished project report" | `f7c612c72` (batch 101) | Part V: Section 44 |

The source numbers are this report's local sequence and the file prefixes
(`02-boundary-phases-`, `03-height-four-`, `04-height-five-`,
`05-strip-asymptotics-`, `06-strip-diagonals-`); the bundle report numbers
(231, 233, 85, 91) are the manuscripts' own.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. All six manuscripts
say their theorems have not been independently peer reviewed or
proof-assistant verified, and that historical priority is not certified.
The exact computations corroborate the proofs on finite ranges; the
numerical tables are decimal diagnostics, not interval enclosures. The
recurrence proofs of Parts III and IV are ordinary mathematical proofs whose
algebraic certificates are checked by exact standard-library programs; they
are not formal proofs.

## What Part I proves

Fix the number of rows `m`. `T_m(n)` counts `m × n` arrays of `1, …, mn`
increasing along rows, columns, diagonals and downward antidiagonals
(OEIS A181196; the rows `m = 3, 4, 5` are A181197, A181198, A181199). Put
`d = C(m,2)`, `J_m = ∏_{j<m} j!`, `M_m(n) = (mn)!/(n!)^m`,
`α_m = (m²−1)/2` and `K_m = √m J_m / (4^d (2π)^((m−1)/2))`.

- **Theorem 2.1 (all orders at fixed height).**
  `T_m(n) = M_m(n) J_m (4n)^(−d) (Σ_{j≤L} c_{m,j} n^(−j) + O(n^(−L−1)))` for
  every fixed `L`, with rational `c_{m,j}` given by the finite moment formula
  of Proposition 5.1; `c_{m,1} = m(m²−1)/12`,
  `c_{m,2} = m²(m²−1)(m²+2)/288`. Equivalently
  `T_m(n) = K_m m^(mn) n^(−α_m) (Σ b_{m,j} n^(−j) + …)`, with
  `b_{m,1} = (m²−1)²/(12m)` and `b_{m,2} = (m²−1)(m⁶+3m²−1)/(288m²)`.
- **Corollary 2.2 (A181199).**
  `T_5(n) = 9·5^(5n+1/2)/(2^17 π² n^12) · (1 + 48/(5n) + 5233/(100n²) +
  1028391/(5000n³) + 60248377/(100000n⁴) + 273939939/(250000n⁵) + O(n⁻⁶))`.
  The leading term is the asymptotic recorded in OEIS A181199 as Vaclav
  Kotesovec's conjecture (27 February 2023, based on Christoph Koutschan's
  guessed recurrence); the proof does not use that recurrence.
- **Theorem 2.3 (algebraicity dichotomy).** `Σ T_m(n) zⁿ` is algebraic over
  `ℚ(z)` (equivalently over `ℂ(z)`) if and only if `m = 1` or `m = 2`: a
  logarithmic singularity at odd `m ≥ 3`, a transcendental Puiseux amplitude
  at even `m ≥ 4` (Section 8).
- **Corollary 2.4.** `T_m(n)/f^(n^m) = 2^(−m(m−1)) (1 + m(m²−1)/(4n) +
  m²(m²−1)(m²−2)/(32n²) + O(n⁻³))`, where `f^(n^m)` counts ordinary standard
  Young tableaux of the `m × n` rectangle.
- **Theorem 4.1 (random-threshold cut):** the exact interior-sum identity
  with nonnegative boundary error at most `m(pⁿ + (1−p)ⁿ)` (at `p = 1/2`,
  `0 ≤ T_m(n) − M_m(n) I_m(n) ≤ 2m 2^(−n) M_m(n)`); Proposition 5.1 (finite
  coefficient formula); Section 6 (the two universal corrections through the
  binomial Vandermonde ensemble and Krawtchouk polynomials); Section 7 (the
  `m = 2` Catalan control, the A181197 and A181198 expansions through `n⁻²`,
  Table 1 of `c_{m,j}` for `m ≤ 6`, `j ≤ 5`, Table 2 of A181199 errors).
- **Theorems 9.1 and 9.2:** Gaussian-Vandermonde (GUE-type) limit laws for
  the intermediate row lengths, at a fixed numerical level and, on the
  trace-zero hyperplane, at a fixed fraction of the labels.
- Section 10: eventual strict monotonicity and log-convexity, and a
  `W_{−1}` inversion of the asymptotic profile with two corrections;
  Appendix A: a direct proof of the shifted hook product; Appendix B: an
  implementation-independent coefficient recipe; Section 12: seven research
  questions.

## What Part II proves

Part II keeps Part I's `T_m(n)`, `M_m(n)`, `J_k` and `α_m`. For `m ≥ 2` let
`B_i = a_{i,1}` and `D_i = a_{i,n}` (the labels at which row `i` is born and
completed), and let `R_m(n) = #{D_1 < B_m}` count the arrays in which the
first row is completed before the last row starts. Put `r = m − 2` and
`d_R = C(r,2)` (the manuscript's `d`, renamed because Part I's `d` is
`C(m,2)`).

- **Theorem 14.1 (rational diagonality at every fixed height).** For every
  fixed `m`, `F_m(z) = Σ T_m(n) zⁿ` is the diagonal of a rational power
  series over `ℚ`; hence it is D-finite and `T_m(n)` is P-recursive. The
  same holds for each fixed order of row births and completions (an event
  word). Proof: Theorem 16.1 cuts a prefix path at its `2m` births and
  completions; each intervening walk in the strict chamber is a reflection
  determinant (Lemma 15.1), so each event word contributes a multiple
  binomial sum with at most `m(m−1)` free indices, and Bostan–Lairez–Salvy
  (J. Symbolic Comput. 80 (2017), Theorem 3.5 and Corollary 3.6) finish the
  argument. With Part I's Theorem 2.3: `F_m` is algebraic for `m ≤ 2` and
  transcendental but D-finite for `m ≥ 3`.
- **Theorem 14.2 (sharp rare-boundary expansion).**
  `R_m(n) = 𝒦_m (m^m/4)ⁿ n^(−r²/2) (Σ_{j≤L} b^R_{m,j} n^(−j) + O(n^(−L−1)))`
  with `𝒦_m = √(m/2) (2π)^(−r/2) 4^(−d_R) 9^(−r) J_r`, effectively computable
  rational `b^R_{m,j}` (Section 20: `b^R_{m,j} = [z^j] A_m(z) 𝒬_{m−2}(z)`),
  and `b^R_{m,1} = r(6r³ − 52r² − 268r − 283)/(72(r+2))`; `R_2(n) = 1`.
- **Corollary 21.1 (height five).** `R_5(n) = √5/(93312 π^(3/2)) (3125/4)ⁿ
  n^(−9/2) (1 − 1393/(120n) + 656449/(28800n²) + 9833844689/(155520000n³)
  + O(n⁻⁴))`, with the analogous table for `m = 2, 3, 4`.
- **Corollary 21.2 (rare-event probability).** `R_m(n)/T_m(n) ~ √π
  4^(2m−3)/(9^(m−2)(m−2)!(m−1)!) n^(2m−5/2) 4^(−n)`; at `m = 5`,
  `1024√π/6561 n^(15/2) 4^(−n) (1 − 509/(24n) + O(n⁻²))`. This corollary uses
  Part I's Theorem 2.1 and Corollary 2.2 (`b_{5,1} = 48/5`); the other
  proofs of Part II do not.
- Theorem 17.1 (an event word occurs iff its Dyck height is at most `n − 1`;
  `T_m(3) = 2^(m−1)`, recovering Sun), Corollary 17.2 (marked rank totals
  and polynomial moment totals are rational diagonals / P-recursive; the
  rotation symmetry (17.6)), Propositions 18.1–18.2 (the shifted-hook core
  sum and two explicit separation bounds), Lemma 19.1 (an exact
  beta–binomial mixture identity), Section 20 (the all-order rule and the
  first correction), Theorem 21.3 (the middle rows, conditioned on the rare
  event, follow an ordered Gaussian-Vandermonde law plus an independent
  `N(0, 1/2)` common mode), Proposition 22.1 (a `W_{−1}` inversion of the
  rare profile with two corrections) and the staircase (22.5);
  Appendices C–D (a finite recipe for the exact sum and an
  implementation-independent coefficient algorithm); Section 24: eight
  research questions, numbered 8–15.
- **Added by the write (5 October 2026, unrefereed, with proof):**
  Proposition 18.3. For Part I's central cut, exactly,
  `E_{m,n}(1/2) = 2^(1−n)/(m−1)! · E[1_{I'} W'_n(X')] + D_{m,n}` with
  `0 ≤ D_{m,n} ≤ 2m(m−1) 4^(−n)`, where the expectation is over `m − 1`
  independent `Bin(n, 1/2)` rows (the stratum with the last row empty at the
  cut, or by symmetry the first row full); hence
  `E_{m,n}(1/2) ~ 2^(1−n) 3^(1−m) J_{m−1} (4n)^(−C(m−1,2))`, and
  `R_m(n) ≤ M_m(n) E_{m,n}(1/2)` with a ratio growing like
  `2ⁿ n^(−(2m−3)/2)`. The write also completed two sketched steps of
  Section 19: the joint convergence (19.6) and the tail bound (19.11), now
  with explicit constants `P(|Y_i| > t) ≤ 5 e^(−t²/8)`.

## What Part III proves (Report 231)

Height four: `a_n = T_4(n)` (A181198), `M_n = (4n)!/(n!)^4`, `b_n = a_n/M_n`.

- **The reduction.** The order-polytope volume `a_n/(4n)!` is an integral
  of `det[K(y_i, x_j)]`, `K = V^(n−1)` the Volterra transfer (27.4); a
  four-variable de Bruijn Pfaffian gives `a_n/(4n)! = (tr B)²/8 − tr(B²)/4`
  (27.10) with `B = EKEK*`; the rank-two identity `B = −4W + 1⊗e + 2α⊗β`
  and integrations by parts with every boundary term reduce this to
  `b_n = 4(n−1)/(4n−1) · Z_n − r_n` (28.21), with one period
  `Z_n = n² ∫_D u (uv(u+v−1))^(n−1)` over the triangle
  `D = {0<u,v<1, u+v>1}`.
- **Theorem 29.1.** `3(3n+1)(3n+2) Z_(n+1) + (n+1)² Z_n =
  (28n³+50n²+29n+5)/(2(2n+1))` for `n ≥ 1`, by a six-coefficient polynomial
  divergence certificate (29.4) with all three edges evaluated.
- **Theorem 26.1** (the inhomogeneous identity `A_n a_(n+1) + B_n a_n =
  D_n M_n`, `n ≥ 1`), **Theorem 30.1** (the literal order-two, degree-nine
  A181198 operator, `n ≥ 1`) and **Theorem 30.2** (Kauers–Koutschan
  Conjecture 18, the printed finite sum with its rising factorials, `n > 1`).
  The operator fails at `n = 0` under `a_0 = 1` (residual −2160).
- Section 31: every fixed order of `b_n` and `a_n` with computable error
  constants (Theorem 31.1, Corollary 31.2); `d_1, …, d_5` are Part I's
  `b_{4,1..5}`, and `d_6 = −79147528275/268435456` is new (Part I's engine
  at order six agrees). Section 32: a finite Lambert-`W_{−1}` model with an
  effective inverse error (Proposition 32.1) and a two-ceiling envelope for
  the integer threshold (Theorem 32.2).
- **Added by the write (5 October 2026, unrefereed, with proof):** Lemma
  33.1 (`Z_n` coincides with no rational function of `n` for all large `n`:
  a pole analysis of the period recurrence) and **Proposition 33.2**:
  A181198 has no recurrence of order zero or one (it is not
  hypergeometric), and every recurrence of order two is a polynomial
  multiple of the OEIS operator, which is primitive; so the order two is
  minimal, and degree nine is minimal among order-two recurrences.

## What Part IV proves (Report 233)

Height five: `a_n = T_5(n)` (A181199), `M_n = (5n)!/(n!)^5`, `F_n = a_n/M_n`.

- **The reduction.** The same transfer, now with an odd *augmented*
  Pfaffian (an atom adjoined); all 225 products are classified into four
  classes (15, 30, 60, 120), giving `a_n/(5n)! = q_0(T_1²/8 − T_2/4) −
  q_1T_1/2 + q_2` (35.8). The open chain of length four, which has no
  height-four analogue, is closed exactly: `q_2 = 16G − 12H/N² + 2/N⁵`
  (36.20). Proposition 37.1: `F_n = 16X_n + k(n)Z_n + ℓ(n)` with the same
  period `Z_n` as Part III and a second period `X_n`.
- Lemma 37.2 (ODEs with all endpoint data), Proposition 37.3 (explicit
  polynomial contiguity), a finite moment closure (38.8)–(38.11), the
  transport `X_(n+1) = ρ_nX_n + σ_nZ_n + τ_n`, and the first difference
  `a_(n+1) − a_n = 2M_n u(n)(Z_n − γ_n)` (34.14).
- **Theorem 34.1** (the nested finite sum of Kauers–Koutschan Conjecture 19,
  `n ≥ 1`) and **Theorem 34.2** (the literal order-three, degree-24
  A181199 operator, `n ≥ 1`, through the factorization
  `L = c_3(E − S)(E − R)(E − 1)`, with `c_3 > 0` for `n ≥ 1`). The operator
  fails at `n = 0` under `a_0 = 1` (residual 5621993879040000).
  Appendix E transcribes the four degree-24 coefficients in full.
- Section 40: every fixed order with rational certificates (Theorem 40.1),
  through a triangular contraction system; the receipt evaluates the
  constants at `K = 0` and `K = 6` (for example `|b_n − q_6(n)| ≤ 18 n⁻¹⁷`
  for `n ≥ 64`); `d_1, …, d_5` are Part I's Corollary 2.2, and the sixth
  correction `d_6 = −2709616559/3125000` is new (Part I's engine agrees).
  Section 41: the finite inverse and threshold envelope (Theorem 41.2).
  Research questions 16–19 are the manuscript's four questions.
- **Added by the write (5 October 2026, unrefereed, with proof):** Remark
  42.1 (Part IV's period and its recurrence (34.17) are Part III's, proved
  twice independently — by a divergence certificate in Part III, by
  contiguity and a moment closure in Part IV — and the transfer, rank-two
  and scalar identities coincide); **Proposition 42.2**: A181199 has no
  recurrence of order zero or one, so the minimal order is two or three.

## What Part V contains (Reports 85 and 91)

Both manuscripts predate Parts I and II by their date lines (1 and 2
October against 3 and 4 October 2026); neither side knew the other. They
are printed after Parts I–IV only because they were placed later.

- **Section 43 (Report 85, 1 October 2026).** Theorem 43.1: for every fixed
  `m ≥ 2`, `T_m(n) = C_m m^(mn) n^(−ν)(1 + Σ c_j(m) n^(−j) + …)` with
  `c_1(m) = (m²−1)²/(12m)` and `c_2(m) = (m²−1)(m⁶+3m²−1)/(288m²)` — the
  same statement as Part I's Theorem 2.1 (`c_j(m) = b_{m,j}`, `C_m = K_m`,
  `ν = α_m`), by another route: an ordinary-tableau comparison
  `T_m(n)/f^(n^m) → 2^(−2d)` (43.13) by bounded convergence, a cut at
  `k = n`, Poisson summation and cut independence. Also a loop-equation
  (Ward) recursion for trace-zero Gaussian–Vandermonde moments (43.19), a
  traceless-GUE Wick check, `c_2 − c_1²/2 = m²(m²−1)/96` (43.20), Sun's
  height-three recurrence in the form `g(3,n+1) + g(3,n) =
  (3n)!/(n!)³ · (7n+1)/(2(n+1)²(4n²−1))`, and an inverse with the rounding
  qualification (43.21)–(43.22). Three steps of Subsection 43.4 are argued
  in outline (item (F11)); Part I's proof is complete.
- **Section 44 (Report 91, 2 October 2026).** Theorem 44.1: `F_m` is a
  rational diagonal, hence D-finite, for every fixed `m` — Part II's
  Theorem 14.1 by the same route (Dyck event words, reflection
  determinants, everywhere-defined binomial products, Bostan–Lairez–Salvy),
  with `m²` coordinates per word where Part II counts `m(m−1)` free indices
  (the same count before the `m` saturation coordinates are fixed).
  Theorem 44.2: algebraic iff `m = 1, 2`, `F_2 = (3 − √(1−4z))/2` — Part I's
  Theorem 2.3, with the same two obstructions proved by elementary radial
  Abelian lemmas (Lemmas 44.8–44.10) instead of Puiseux expansions.
  Proposition 44.7 re-proves the leading equivalent (an edition of
  Report 85's Subsection 43.3).
- **Section 45 (the write).** The correspondence table, the chronology
  (within this report the earliest proofs by date line of Theorems 2.1, 2.3
  and 14.1 are Reports 85 and 91; this bears on item (F4), the priority of
  Theorem 14.1), Remark 45.1 (43.20 from Part I's (2.7)), and items
  (F11)–(F14).

## Corrections made at the write (standing rule)

- **W1.** Section 14.2 lists Part I's non-sharp boundary bound among "the
  two gaps addressed here", which suggests that Part I's Research question
  4 (the asymptotic of the boundary error `E_{m,n}(1/2)`) is answered. It is
  not: `R_m(n)` is a much smaller sector inside the boundary event. Exact
  values: at `m = 3` the boundary error is 4.9, 37, 357 and 3907 times
  `R_3(n)` at `n = 8, 12, 16, 20` (Remark 14.4, with a table to `n = 40` and
  at `m = 2, 4`). Question 4 stays open, re-scoped in a dated note there;
  Proposition 18.3 gives its leading term.
- **W2.** The abstract's "resolving an explicit question in the preceding
  ProveIt report" and the delivered README's "This resolves Question 7"
  hold for D-finiteness only. Question 7 also asks how the minimal
  annihilating order grows with `m`; that half stays open (Remark 14.3;
  Research question 11).
- **Moved to "Further questions and research" (Section 24.1).** (F1) the
  remark after Corollary 21.2 that other exponentially small structures may
  exist inside `Q_m`; (F2) an all-order expansion of the boundary error
  (the re-scoped Part I Question 4); (F3) the steps argued only in outline:
  moment convergence in Theorem 21.3, the last sentence of Proposition 22.1
  (the genuine real inverse has the formal expansion), and the existential
  constants of the staircase (22.5); (F4) the priority of Theorem 14.1,
  which the source audit did not search against the general literature on
  linear extensions of fixed-height posets and walks in Weyl chambers. The
  manuscript's own eight questions are Research questions 8–15.

No numerical value, coefficient or table entry of the manuscript was found
wrong (the intake recomputed the first correction by hand, `-1393/120`,
`-535/12`, `-509/24`, Part I's `48/5`, and spot values of `R_m/L` by an
independent program).

**Batch 101 (Parts III–V, 5 October 2026).** No claim of the four
manuscripts was found wrong: the intake checked the certificates of Parts
III and IV in SymPy (residual zero), every printed constant it tested
(the expansions at heights four and five, `Z_1, Z_2, Z_3 = 1/3, 13/45,
461/1680`, `X_1, X_2 = 2/15, 1322/14175`, both `n = 0` residuals, the
`(3,4)` table, Sun's height-three identity for `n ≤ 24`, `F_2`), and the
OEIS coefficients against the live entries. Recorded under the standing
rule:

- **Moved to "Further questions and research".** Part III (Section
  33.6): (F5) minimality of the A181198 recurrence — order and order-two
  degree settled by the write's Proposition 33.2, degree over all orders
  open; (F6) the constants `E_K, N_K, C_K, H_K, W_K, X_K` constructed but
  not evaluated; (F7) even heights six and more ("an analogous
  low-dimensional reduction would require new work"); (F8) the
  exponentially small content of the homogeneous mode (a non-claim). Part
  IV (Section 42.6): (F9) minimality of the A181199 recurrence — order one
  excluded by Proposition 42.2, order two against three open (the
  manuscript: the factorization "is not a proof that order three is
  minimal"); (F10) the inverse constants `H_K, W_K, X_K` and the envelope
  onset, not evaluated. Part V (Section 45.2): (F11) the three outline
  steps of Report 85's Subsection 43.4 (growing-window exponentiation,
  uniform Poisson summation, the passage to the rounding statement (43.22));
  (F12) Sun's height-three recurrence "simplifies to" the displayed form —
  checked numerically, not derived from Sun's printed statement; (F13)
  Report 85's growing-height scale `m³/n` ("a proposed scale, not a
  growing-height theorem"), smaller exponential sectors and effective
  inverse constants (= Research questions 3, 4, 6); (F14) Report 91's
  compact rational diagonal, its operator, minimal orders and subdominant
  sectors (= Research questions 9, 11). The four questions of Report 233
  are Research questions 16–19.
- **Stale statements corrected by dated notes** (none was wrong when
  written): listed under "Stale claims" below.

## What is not claimed

- **Neither guessed recurrence is proved:** not A181198's order-two,
  degree-nine recurrence, nor its conjectured finite-sum solution, nor
  A181199's order-three, degree-twenty-four recurrence, nor Conjectures
  18–19 of Kauers–Koutschan. Part II proves that *some* recurrence exists;
  it supplies no rational function, telescoper or minimal operator
  (Remark 16.2), ran no Maple or binomial-sum package, and `m(m−1)` counts
  summation indices, not diagonal variables or operator order. Both draft
  OEIS texts say explicitly not to mark either recurrence as proved.
  [Added 5 October 2026, batch 101: no longer true of the report. Part III
  proves the A181198 recurrence and Conjecture 18 (Theorems 26.1, 30.1,
  30.2), Part IV the A181199 recurrence and Conjecture 19 (Theorems 34.1,
  34.2), for every `n ≥ 1`. The sentence remains true of Parts I and II.
  The two OEIS drafts were right for their own manuscripts and stay
  byte-identical and unsubmitted; they have not been updated to say that
  the recurrences are now proved here.]
- The expansions are Poincaré expansions for fixed `m` and fixed truncation
  order: no growing-height theorem, no Borel summability, Stokes data or
  exponentially improved transseries. Part II's rare sector is a
  combinatorially defined beyond-all-orders refinement, not a Stokes
  multiplier, and the next boundary sector is not analysed; the bound of
  Proposition 18.2 is an upper rate, not the next sector. Error constants
  exist but are not computed, and no onset is certified. [Added 5 October
  2026, batch 101: at heights four and five, Parts III and IV construct
  effective constants and onsets from the recurrences; Part IV's receipt
  evaluates them at `K = 0` and `K = 6` (for example `|b_n − q_6(n)| ≤
  18 n⁻¹⁷` for `n ≥ 64`, and `(K, N, C_K) = (0, 512, 202), (6, 64,
  6100000)` for the logarithmic remainder). Part III's constants and Part
  IV's inverse constants are constructed but not evaluated (items (F6),
  (F10)); nothing is computed for `m ≥ 6`. Parts III–V assert no Borel
  summability, Stokes data or canonical transseries either.]
- Nonalgebraicity is not non-D-finiteness (Remark 8.1); whether `F_m` is
  D-finite for every `m` is Question 7. [Added 5 October 2026: Part II,
  Theorem 14.1, proves D-finiteness at every fixed `m`, the first half of
  Question 7; the growth of the minimal order, its second half, stays
  open.] [Added 5 October 2026, batch 101: on that second half, the minimal
  order is two at `m = 4` (Proposition 33.2) and two or three at `m = 5`
  (Proposition 42.2); the growth with `m` stays open.] Part II takes the
  nonalgebraicity from Part I and does not reprove it. P-recursiveness of
  expectations (quotients by `T_m(n)`) is not asserted.
- The boundary bound `2m 2^(−n)` is not claimed sharp. [Added 5 October
  2026: its rate `2^(−n)` is the true one, but not its constant or, for
  `m ≥ 3`, its power of `n` (Proposition 18.3).]
- Theorems 9.1, 9.2 and 21.3 are one-time laws, not process convergence;
  in Theorem 21.3 the variable `U` is an auxiliary coupling.
- The inverse-index approximations are not integer-threshold certificates,
  and the inversion method is standard (see below); the smallest `n` from
  which monotonicity and log-convexity hold is not identified. [Added 5
  October 2026, batch 101: Parts III and IV give two-ceiling envelopes for
  the integer threshold at `m = 4, 5` (Theorems 32.2, 41.2), with effective
  but unevaluated onsets; they leave at most two adjacent candidates near
  an integer and assert no unconditional rounding rule.]
- Parts III–V (batch 101): no minimality claim by any manuscript (the
  write's Propositions 33.2 and 42.2 are the only minimality statements);
  no claim at heights `m ≥ 6`; Report 85's `m³/n` is a proposed scale only;
  Report 91 supplies no explicit rational function or operator; Reports 231
  and 233 searched the literature in a bounded way (231 also inspected
  arXiv:2607.24832) and make no priority claim; the intake did not
  re-inspect the printed pages of Kauers–Koutschan (it verified the
  transcribed sums and operators against exact counts and the live OEIS
  entries).
- **Classical material, credited, not new:** the shifted hook product
  (a standard formula, cited from Sun's 2017 article and re-proved in
  Appendix A), the
  order-statistics/order-polytope interpretation (Sun), the A181197
  height-three leading term (Panova, in comments by Joel B. Lewis), the
  reflection principle (Lemma 15.1, proof included), the
  multiple-binomial-sum theorem of Bostan–Lairez–Salvy, Gaussian
  Vandermonde integrals, Krawtchouk polynomials, Lambert-W inversion and
  reversion, and the Catalan and fixed-width controls. Chan's periodic
  P-partitions concern the other orientation (fixed `n`, growing `m`).
  [Added 5 October 2026, batch 101: Parts III–V use further classical
  tools, as the manuscripts say: order-polytope volumes, the
  Andréief/Cauchy–Binet composition, de Bruijn's Pfaffian integration,
  Volterra operators, Ore-operator factorization, the positive-real
  Stirling remainder (DLMF 5.11), loop equations and Wick pairings for
  Gaussian ensembles, Abelian radial lemmas and Lindemann's theorem; their
  special cases are proved in the text.]
- The `n = 80` values are OEIS b-file inputs, not regenerated; the
  numerical tables are 90-digit (Part I) and 70-digit (Part II) decimals,
  not certified enclosures.
- Priority rests on the producers' inspected sources only ("not an
  exhaustive priority search"); an OEIS "conjecture" label "is not by itself
  proof that no published proof exists".
- **Nothing was submitted to OEIS**, by either package's author or by the
  intake. `data/notes-PROPOSED_OEIS_ADDITIONS.txt` is a draft marked "DRAFT
  ONLY — NOT SUBMITTED", and
  `data/02-boundary-phases-notes-PROPOSED_OEIS_NOTE.md` a draft headed "NOT
  SUBMITTED"; any submission is a human editor's decision after review. No
  OEIS identifier is proposed for `R_m`. [Added 5 October 2026, batch 101:
  both drafts tell editors not to mark the recurrences proved ("Do not mark
  either conjectured sequence recurrence as proved on the strength of this
  article"; "Do not remove the conjectural status of the displayed
  specific recurrences or finite-sum formulas on the basis of this result
  alone"). That was right for their manuscripts; Parts III and IV now prove
  the recurrences, but the drafts are not edited, not replaced and not
  submitted. The four batch-101 packages contain no OEIS draft, and
  nothing about Parts III–V has been sent to OEIS.]

## Checks made at intake

**Part I.** On 3 October 2026 the intake reran the delivered programs on
scratch copies (Python 3.14.4, Windows; see "Rerun the checks"):
`code/verify.py` passed all 471 checks (27 + 238 + 120 + 30 + 12 + 12 +
30 + 2) in 56 s on a loaded machine (the package recorded 3.9 s), and every
data file it writes matched the shipped one after CR stripping, except the
`seconds` field of `data/verification.json`; its standard output equals
`data/verification.txt` up to the same field.
`code/coefficients.py --height 5 --order 5` reproduced
`data/coefficients_m5.json`, and `code/numerics.py` (mpmath 1.3.0)
reproduced `data/numerics.csv` byte for byte and printed
`data/numerics.txt`. The delivered `SHA256SUMS.txt` verified 20/20. The
intake also checked symbolically that `K_5 = 9√5/(2^17 π²)` and, for
`m = 2, …, 7`, that `K_m = 2^(−m(m−1)) C` with the transseries volume's
rectangle constant `C` and that `(2.4)` and the hook product give both
printed corrections of Corollary 2.4.

**Part II.** At placement (5 October 2026) the delivered `SHA256SUMS.txt`
verified 21/21. At the write (5 October 2026) the delivered programs ran on
a scratch copy with the delivered names restored (Python 3.13.5 through
`uv`, SymPy 1.14.0, mpmath 1.3.0): `verify.py` passed all 1,954 checks in
66 s (the package recorded 23 s; the placing session's run took 334 s);
`numerics.py` (44 s), `coefficients.py --height 5 --order 3` and
`inverse_profile.py --index 60 --height 5` reproduced their shipped records
after CR stripping; the only differences were the timing fields of
`verification.json`, `verification.txt` and `numerics.json`. The intake
also recomputed `T_3(4) = 29`, `R_3(4) = 25` and `R_m/L` at `m = 3, 4` with
its own program, checked the Bostan–Lairez–Salvy theorem numbers and
conventions against arXiv:1510.07487, and computed the table of
Remark 14.4 and the checks of Proposition 18.3 (the exact identity (18.7)
with `0 ≤ 4ⁿ D_{m,n} ≤ 2m(m−1)` at `m = 2, 3, 4`, `n ≤ 80, 40, 20`) with
an exact program that is not shipped.

**Parts III–V.** At placement (5 October 2026) every delivered checksum
manifest verified (Report 231 19/19, Report 233 21/21, Report 85 20/20,
Report 91 11/11), and every suite passed on a copy (Python 3.14.4,
Windows): Report 231's verifier printed its receipt byte for byte, with
and without `-O` (2.6 s); Report 233's printed its receipt (status PASS,
58 named uniform certificates; 20 s); Report 85's `verify.py` (SymPy 1.14.0)
passed in 6 min 30 s on a loaded machine (the package recorded 0.6–6.8 s per program),
refreshing all seven records equal to the delivered ones after CR
stripping except the `seconds` fields; Report 91's `verify.py` passed with
`matches_distributed_data: true` (2.5 s). The intake also checked, with
programs of its own that are not shipped: the certificate (29.4), the edge
identities (29.6)–(29.8) of Part III and the `y`-contiguity
certificate (37.17) and γ-bridge (39.1) of Part IV in SymPy (residual zero); with
an independent row-state count, Theorems 26.1, 30.1, 30.2, the affine
formula (28.21) and the `Z` recurrence for `n ≤ 30`, and Theorem 34.1,
Proposition 37.1 and the first difference (34.14) for `n ≤ 20`, the
transcribed degree-24 operator annihilating the counts for `n = 1, …, 15`;
`p_0, p_1, p_2` and `c_0, …, c_3` against the live OEIS entries (fetched 5
October 2026, not shipped); and Part I's `code/coefficients.py --order 6`
on a copy, which gives `b_{4,6} = −79147528275/268435456` and
`b_{5,6} = −2709616559/3125000`, equal to the new sixth corrections of
Parts III and IV. At the write the verifiers of Reports 231, 233 and 91,
and two of Report 85's programs (`check_inverse.py`, `check_midpoint.py`),
were rerun with the shipped files on copies restored to the delivered
names (commands below), with the same results; the write also checked the
algebra of Lemma 33.1 and Proposition 33.2 in SymPy (the value −1/2 of the
forcing numerator at `n = −1/2`, `gcd(p_0, p_1, p_2) = 1`, all degrees 9)
and Remark 45.1.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats shifted tableaux, and the
report's place in the collection confers no formal status. The one formalized
neighbour is general: Theorem J.23 of the transseries volume (below), whose
real branch rules are proved in
`Analysis/FabiusFunction/Lean/FabiusFunction/LinLogCoreInversion.lean`
(rated "Partial" in that volume's register; nothing about shifted rectangles).
Part II's eighth question (Research question 15) proposes formalizing its
finite combinatorial components; that is a proposal only. Parts III–V add
no formal material: the exact verifiers of Reports 231 and 233 check
algebraic certificates in exact arithmetic, which is not a proof-assistant
verification of the analytic and combinatorial steps.

**Not new: the comparison constant and the inversions.** Dated `[write]`
notes record:

- the normalizer `f^(n^m)` of Corollary 2.4 is the classical rectangle hook
  count, equation (3.19), `t2:eq:tableaux`, of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/`
  (Section 3.5, written `T_d(n)` with `d` rows). With its constants (3.20)
  (`t2:eq:tableaux-constants`: `a = m log m`, `β = −α_m`,
  `C = √m (2π)^((1−m)/2) ∏ j!`), `K_m = 2^(−m(m−1)) C` exactly, which is the
  leading term of Corollary 2.4;
- the inversion (10.3) is an instance of Theorem J.23
  (`p0:thm:lambert-core`) of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`,
  with `a = m log m`, `b = −α_m` and its `b < 0` branch rule (`W_{−1}`,
  valid for `L > α_m(1 − log(α_m/(m log m)))`); the integer-threshold
  caution is its staircase theorem J.43 (`p0:thm:staircase`). The manuscript
  itself calls the method standard;
- Part II's inversion (22.2) is the same instance with `a = m log m − log 4`
  and `b = −(m−2)²/2`, and its staircase (22.5) the same separation
  condition;
- Parts III and IV invert by the same apparatus at `m = 4, 5` (the
  `W_{−1}` models (32.4) and (41.3), and two-ceiling envelopes, Theorems 32.2 and
  41.2, which are the staircase statement with explicit constants), and
  Report 85 by a logarithmic expansion (43.21) with the rounding
  qualification (43.22).

**Overlap of the two Parts.** Part II was written against Part I's text
(unchanged between its pin and its placement) and shares 1.98 % of its word
8-grams with it. It re-derives Part I's state space, imports the shifted
hook product that Part I's Appendix A proves, and uses Gaussian and binomial
Vandermonde identities of the same type as Part I's (6.1), (5.14), (6.6)
and (5.16), now mixed over a beta law; Lemma 19.1 is a random-cut variant
of Part I's Theorem 4.1 and Theorem 21.3 the rare-event analogue of
Theorem 9.1. The provenance note at the head of Part II lists them.

**Overlap of Parts III–V with Parts I–II and with each other.** Reports
231 and 233 read Part I only (blob `2b40ded9`, the text of `6fef5383b`);
Report 231 also saw Part II's manuscript, as "this private companion". They
share 0.0 % / 0.6 % (231) and 0.2 % / 0.5 % (233) of their word 8-grams
with Parts I / II. Their asymptotic Sections 31 and 40 recover Part I's
Theorem 2.1 at `m = 4, 5` from the recurrences, crediting Part I. Reports
231 and 233 bear the same date and do not cite each other; Part IV
re-derives the transfer, the rank-two identity, the scalar integrals and
the period recurrence of Part III (Remark 42.1: the same `Z_n`, two
independent proofs of its recurrence), sharing 4.3 % (233 → 231) and
5.7 % (231 → 233) of 8-grams. Reports 85 and 91 read no repository
material and predate Parts I and II by date line; they share 0.4 % / 1.1 %
(85) and 0.0 % / 1.1 % (91) with Parts I / II, and 7.1 % of Report 91's
8-grams recur in Report 85, whose leading-order argument Report 91
reproduces. Section 45.1 tabulates the correspondence.

**Neighbouring reports.**

- `oeis-sequence-asymptotics/a189281-path-forest-expansions`: the
  manuscript of Part I read its README (one report in three Parts, which the
  manuscript calls "the existing path-forest reports") as an editorial
  precedent; none of its theorems is used. It inverts by the same apparatus
  (`spf:thm:inverse-first`, `spf:thm:inverse-all`).
- Batch-85 siblings: `oeis-sequence-asymptotics/a047874-long-increasing-subsequences`
  (manuscript 08; it shares the rectangle tableau count, its (2.6), but no
  theorem, and proves D-finiteness of another tableau array in sectors by
  another route) and `oeis-sequence-asymptotics/a182220-source-boundary`
  (manuscript 07; unrelated).
- Other conjectures of Kauers and Koutschan's 2023 paper, whose Section 6.4
  discusses the guessed A181198/A181199 recurrences, are proved in
  `enumerative-combinatorics/a181280-binary-matrix-formula` (Conjecture 20),
  `enumerative-combinatorics/a195806-hexagonal-lattice` (Conjecture 11) and
  Part IV of `oeis-sequence-asymptotics/a215561-fixed-composition-excursions`
  (Conjecture 15). This report proves the D-finiteness of the Section 6.4
  sequences (Part II) but none of the section's recurrences or finite sums.
  [Added 5 October 2026, batch 101: Parts III and IV now prove the
  section's two guessed recurrences and its Conjectures 18 and 19, so this
  report too proves conjectures of that paper. The README of
  `a181280-binary-matrix-formula` and the collection manifest still say
  the recurrences are unproved; reciprocal notes are pending.]

**Stale claims.** Part I: "Identifier searches for A181198 and A181199
returned no matching repository report" is true at its pin and still true
of the tree outside this report. Part II's repository claims were checked
at placement and are true (its predecessor proves the all-order expansion
and nonalgebraicity, asks D-finiteness as Question 7, does not claim its
boundary bound sharp, and proves no recurrence); its framing of Questions
4 and 7 is corrected as above. Dated notes in Part I record what Part II
changes: before the table of contents, at the end of Section 4.1, after
Remark 8.1, and at Research questions 4 and 7.

Parts III–V (batch 101). The claims of Reports 231 and 233 that this
report "expressly leaves the specific height-four and height-five
recurrences unproved", and that Part II "leaves these particular
recurrences unresolved", were true at their pin and at placement; Report
231's description of Part II as a "private companion" is out of date
(it is Part II). Reports 85 and 91 make no repository claim. What the new
Parts make stale is recorded in dated notes (5 October 2026): before the
table of contents; at the end of Section 1.3 (the sentence that this
report "leaves the guessed recurrences of that section unproved"); after
the note following Remark 8.1; at Research questions 1 (answered), 6
(advanced at `m = 4, 5`) and 7; after the notes at the end of Sections
11.3 and 23.3 (the two OEIS drafts); after Remark 16.2; at Research
questions 8 (answered) and 11 (advanced); and after item (F4) of Section
24.1 (Report 91's earlier proof of Theorem 14.1). In this README the
bracketed notes of 5 October 2026 under "What is not claimed" and
"Neighbouring reports" do the same.

## Notation

Part I reuses several letters (`T_m(n)` against the volume's `T_d(n)` for
ordinary rectangles; `d = C(m,2)` against the volume's `d` = rows; `K_m`,
`K`, `K_j(X)`; `L`, `L_5(n)`; `h_r(q)` against the norms `h_j`; `λ`;
`R_n`, `R_m`, `R(z)`, `𝓡_{L,n}`; `p` against power sums `p_r`; `q_{ij}`, `q`;
`Z_m(n)`, `Z_i`; `A`, `B`, `𝒜`; `C(z)`, `C_{n−1}`, `C_{m,L}`, `𝒞_n`;
`E_{m,n}`, `𝔼`, `ℰ_z`; `H(λ)`, `H_j`, `H_{20}`; `β_j`). A table in the first
`[write]` note (Section 1.3) fixes each reading and the tempting false one,
notably that `T_m(n)` is **not** the ordinary rectangle count.

Part II's symbols clash with Part I's in many places: `R_m(n)` (the rare
count, not Part I's weight `R_n(x)` or radius `R_m`), `H_m(n)` and the
indicator `H(a)`, `𝒦_m` and the kernel `K_r(u,v)` (not `K_m`), `𝒞_r(n)`,
`𝓘` (`1 ≤ X_i ≤ n−2`), `X_i` (binomial counts mixed over a beta law),
`W_n`, `Y_i`, `ε = n^(−1/2)`, `𝒬_r` and `Q_m(n)`, `A_m(z)`, `S_1`, `S_2`,
`λ_m`, `β_m`, `p_i`, `q_i`, `B_i`, `D_i`, `r`, `L`. A table in the second
`[write]` note at the head of Part II fixes each against Part I's reading.
One symbol was renamed: the manuscript's `d = C(m−2, 2)` is `d_R`. Falling
factorials use Part I's typography (`n^{\underline k}`, the manuscript's
`(n)_{\underline k}`).

Parts III–V keep their manuscripts' symbols; no symbol was renamed and no
normalization changed. A notation table at the head of each Part fixes
every reading against the rest of the report. The traps: in Part III,
`a_n = T_4(n)`, `b_n = a_n/M_n` (not `b_{m,j}`), `Z_n` the triangle period
(not Part I's `Z_m(n)`), `J = 1⊗1` (not `J_m`), `K = V^(n−1)` (not
`K_m`), `E` the sign kernel, `N = n!` and later the threshold `N(y)`,
`F_n` a factorial prefactor (not `F_m(z)`), `(x)_j` rising, `R(n)`,
`S(n)` contraction coefficients, `c_j = (3/1024) c_{4,j}` and
`d_j = b_{4,j}`. In Part IV, `T_j = tr(B^j)` (**not** the count `T_m(n)`),
`C_m` the ordered simplex, `b = K1` against `b_n = F_n = a_n/M_n`, `q_j`
twice (open-chain integrals and polynomial coefficients), `V` and the
moments `V_j`, `E` the sign kernel and the shift, `R(n)`, `S(n)` ratios
different from Part III's, `c_0..c_3` the OEIS coefficients against
`c_j = β_{10+j}`, and Appendix E's integer arrays `b_j`, `d_j`. In Part V,
`g(m,n) = T_m(n)`, `C_m = K_m`, `ν = α_m`, and above all Report 85's
`c_j(m)`, which is Part I's **`b_{m,j}`, not `c_{m,j}`**; Report 91's
`G_m = F_m`, `A_m(t) = G_m(m^(−m)t)`, `R_m` a rational function with
`G_m = diag R_m`, and its `α_m`, an algebraic constant, **not**
`(m²−1)/2`. Typography only: Report 85's `\tr` (upright Tr) is set as
`\Tr`, and four command-line options in Section 33.3 as `-{}-option` so
that the report's typewriter font keeps two hyphens.

## Labels

Every label carries the prefix `shr:`; Part II's carry `shr:bp:`. Part I's
69 labels were prefixed in the batch-85 write before anything cited them.
The batch-98 write added 107 labels, so the report has 176: the
manuscript's 97, prefixed `shr:bp:` with every `\ref` and `\eqref`
updated; one on a delivered remark (`shr:bp:rem:constructive`); the two Part
labels `shr:part:one` and `shr:bp:part`; and seven for the write's own
material (`shr:bp:rem:q7`, `shr:bp:rem:q4`, `shr:bp:sec:boundary`,
`shr:bp:prop:boundary`, `shr:bp:eq:boundary-exact`,
`shr:bp:eq:boundary-lead`, `shr:bp:sec:further`). Checked against the
`.aux` files of builds of the committed text and of the delivered
manuscript: none of Part I's 69 labels changed its number, and every
manuscript label has its delivered number shifted by 13 sections
(Appendices A–B to C–D). Corollary 2.4 has no label and is cited by number.

The batch-101 write added 310 labels, so the report has 486: the
manuscripts' 293 (Report 231's 108 as `shr:h4:`, Report 233's 135 as
`shr:h5:`, including its `asy:`, `inv:`, `app:` and `tab:` labels, Report
85's 23 as `shr:sa:` and Report 91's 27 as `shr:sd:`), with every `\ref`
and `\eqref` updated; and 17 for the write's own material: the Part labels
`shr:h4:part`, `shr:h5:part` and `shr:sa:part`, the sections
`shr:sa:sec`, `shr:sd:sec` and `shr:sa:sec:chronology`, and
`shr:h4:sec:minimal`, `shr:h4:lem:Zirr`, `shr:h4:eq:zrat`,
`shr:h4:prop:minimal`, `shr:h4:sec:further`, `shr:h5:sec:write`,
`shr:h5:rem:sameZ`, `shr:h5:prop:nothyper`, `shr:h5:eq:Yrec`,
`shr:h5:sec:further` and `shr:sa:rem:logc2`. Checked against the `.aux`
files of a build of the committed text and of builds of the four
delivered manuscripts: none of the 176 earlier labels was lost or changed
its number; every label of Report 231 has its delivered number shifted by
25 sections, and every label of Report 233 by 33 sections (Appendix A to
E), except its table, Table 1 as delivered and Table 8 here (the table
counter also counts the uncaptioned notation tables). In Reports 85 and 91
equation `(k)` is `(43.k)` and `(44.k)`, and the theorem-like statements
are renumbered through Sections 43 and 44, in their delivered order.

The batch-85 write added four dated `[write]` notes to Part I (end of
Section 1.3, after Corollary 2.4, end of Section 10.2, end of Section 11.3)
and the title-page page anchors. The batch-98 write added the two `\part`
headings, five dated notes in Part I (named under "Stale claims"), and in
Part II: its opening (the manuscript's title-page material and two notes),
Remarks 14.3–14.4, Section 18.3 with Proposition 18.3, notes after (19.6),
after (19.11), at the end of Sections 22, 23 and 24 and before Appendix C,
Section 24.1, and the Bostan–Lairez–Salvy bibliography entry. The
manuscript's three citations of its predecessor now point to Part I. No
other statement, proof, number or table of either manuscript was changed.

The batch-101 write added: three `\part` headings; the title-page
material of Reports 231 and 233 and the titles, author lines, dates and
abstracts of Reports 85 and 91; a provenance note and a notation note at
the head of each Part; shipped-layout notes at the end of Sections 33.3
and 42.3 and of Sections 43 and 44; a note after Research questions 16–19
and notes at the heads of Sections 43, 44 and Appendix E; Sections
33.5–33.6, 42.5–42.6 and 45 (with Lemma 33.1, Propositions 33.2 and 42.2,
Remarks 42.1 and 45.1); twelve dated notes in Parts I and II (named under "Stale
claims"); three bibliography entries (`oeis198int`, `oeis199int`,
`Lindemann`) and the macros of the new Parts. The predecessor citations of
Reports 231 and 233 now point to Parts I and II, and Report 91's citation
of Report 85 to Section 43. No other statement, proof, number or table of
the four manuscripts was changed.

## Files

```text
README.md                                           this guide (replaces the six delivery READMEs)
article.tex                                         the report, Parts I-V
article.pdf                                         compiled report, 135 pages
notes-SOURCES_AND_STATUS.md                         Part I's source and status audit (delivered as notes/SOURCES_AND_STATUS.md)
02-boundary-phases-notes-SOURCES_AND_STATUS.md      Part II's source and status audit (delivered as notes/SOURCES_AND_STATUS.md)
code/build.sh                                       Part I: three pdflatex passes (delivered at the package root; see below)
code/coefficients.py                                Part I: exact rational coefficient engine, Proposition 5.1 (standard library)
code/tableaux.py                                    Part I: row-state and bitmask-poset enumerators, shifted hook product (standard library)
code/verify.py                                      Part I: the 471 finite checks (standard library; writes into data/)
code/numerics.py                                    Part I: 90-digit diagnostics of Table 2 (mpmath; writes into data/)
code/02-boundary-phases-build.sh                    Part II: three pdflatex passes (delivered as build.sh)
code/02-boundary-phases-tableaux.py                 Part II: prefix DP, poset enumerator, reflection kernel, event-skeleton evaluator, hook core sum
code/02-boundary-phases-coefficients.py             Part II: exact all-order rare coefficient engine (SymPy)
code/02-boundary-phases-verify.py                   Part II: the 1,954 finite checks (writes into data/)
code/02-boundary-phases-numerics.py                 Part II: exact rare counts and 70-digit diagnostics (mpmath; writes into data/)
code/02-boundary-phases-inverse_profile.py          Part II: inverse-profile diagnostic (mpmath; writes into data/)
data/requirements-numerics.txt                      Part I: mpmath==1.3.0 (delivered at the package root)
data/oeis_selected.json                             Part I: A181198/A181199 terms, n = 1..10, 20, 40, 80 (third-party, CC BY-SA 4.0; see below)
data/exact_regenerated.json                         Part I: A181198/A181199, n = 1..10, 20, 40, regenerated by the row-state program
data/coefficients_m1_to_m6.json                     Part I: c_{m,j} and b_{m,j}, m = 1..6, j = 0..5 (Table 1)
data/coefficients_m5.json                           Part I: m = 5 through order 5, both normalizations
data/numerics.csv                                   Part I: relative errors for A181198 and A181199 at n = 10, 20, 40, 80 (CRLF)
data/numerics.txt                                   Part I: standard output of numerics.py
data/verification.json                              Part I: recorded run of verify.py (471 checks, PASS)
data/verification.txt                               Part I: standard output of verify.py
data/pdf_preflight.json                             Part I: the producer's QA record of its delivered PDF (not regenerable)
data/notes-PROPOSED_OEIS_ADDITIONS.txt              Part I: draft OEIS text, NOT SUBMITTED (delivered as notes/PROPOSED_OEIS_ADDITIONS.txt)
data/02-boundary-phases-requirements.txt            Part II: sympy==1.14.0, mpmath==1.3.0 (delivered as requirements.txt)
data/02-boundary-phases-coefficients_m3.json        Part II: b^R_{3,j}, j = 0..3
data/02-boundary-phases-coefficients_m4.json        Part II: b^R_{4,j}, j = 0..3
data/02-boundary-phases-coefficients_m5.json        Part II: b^R_{5,j}, j = 0..3 (Corollary 21.1)
data/02-boundary-phases-exact_rare_counts.csv       Part II: exact R, H and M for m = 2..5, n = 2..20 (CRLF)
data/02-boundary-phases-numerics.csv                Part II: R, H, R/leading, H/R and errors of orders 0..3, m = 3, 4, 5, n = 10, 20, 40, 60 (CRLF)
data/02-boundary-phases-numerics.json               Part II: the same rows as strings, 70-digit run (its seconds field is the producer's)
data/02-boundary-phases-inverse_m5_n60.json         Part II: inverse-profile diagnostic at m = 5, n = 60
data/02-boundary-phases-verification.json           Part II: recorded run of verify.py (1,954 checks, PASS)
data/02-boundary-phases-verification.txt            Part II: standard output of verify.py
data/02-boundary-phases-notes-PROPOSED_OEIS_NOTE.md Part II: draft OEIS note, NOT SUBMITTED (delivered as notes/PROPOSED_OEIS_NOTE.md)
03-height-four-SOURCES.md                           Part III: Report 231's source and attribution record (delivered as SOURCES.md)
03-height-four-code-README.md                       Part III: Report 231's verifier README (delivered as code/README.md)
code/03-height-four-build.py                        Part III: inventory check and PDF/ZIP replay (delivered as build.py; needs unshipped files)
code/03-height-four-exact_algebra.py                Part III: sparse polynomials and rational functions over Fraction (standard library)
code/03-height-four-formal_series.py                Part III: formal series, Bernoulli numbers, the Stirling product (standard library)
code/03-height-four-verify_report231.py             Part III: 31 symbolic certificate checks, finite checks n <= 20 (prints JSON)
data/03-height-four-receipt.json                    Part III: the verifier's deterministic receipt (delivered as code/receipt.json)
04-height-five-SOURCES.md                           Part IV: Report 233's source and attribution record (delivered as SOURCES.md)
code/04-height-five-build.py                        Part IV: inventory check and PDF/ZIP replay (delivered as build.py; needs unshipped files)
code/04-height-five-asymptotic_certificate.py       Part IV: formal coefficients and effective constants at K = 0, 6 (standard library)
code/04-height-five-exact_algebra.py                Part IV: exact polynomial and rational ring (standard library; not Part III's file)
code/04-height-five-printed_coefficients.py         Part IV: the Conjecture 19 polynomials and the four OEIS coefficients (transcribed)
code/04-height-five-verify_certificate.py           Part IV: 58 uniform certificates, the 225 Pfaffian terms, finite checks n <= 20 (prints JSON)
data/04-height-five-receipt.json                    Part IV: the verifier's deterministic receipt (delivered as code/receipt.json)
code/05-strip-asymptotics-verify.py                 Part V, Report 85: runs the six programs below with -O (delivered as verify.py)
code/05-strip-asymptotics-check_midpoint.py         Report 85: 60 small rectangles, 30 OEIS terms, 121 interior hook identities
code/05-strip-asymptotics-gaussian_corrections.py   Report 85: matrix-entry Wick derivation of both corrections (SymPy)
code/05-strip-asymptotics-ward_corrections.py       Report 85: loop-equation derivation, check against Sun's height-three recurrence (SymPy)
code/05-strip-asymptotics-check_gaussian_integrals.py  Report 85: direct Gaussian integrals at heights 2, 3, 4 (SymPy)
code/05-strip-asymptotics-check_inverse.py          Report 85: formal inverse substitution, orders 0-2 (SymPy)
code/05-strip-asymptotics-generate_expansion.py     Report 85: the coefficient generator (43.17)-(43.19) (SymPy)
data/05-strip-asymptotics-check_midpoint.json       Report 85: output of check_midpoint.py
data/05-strip-asymptotics-gaussian_corrections.json Report 85: output of gaussian_corrections.py
data/05-strip-asymptotics-ward_corrections.json     Report 85: output of ward_corrections.py
data/05-strip-asymptotics-check_gaussian_integrals.json  Report 85: output of check_gaussian_integrals.py
data/05-strip-asymptotics-check_inverse.json        Report 85: output of check_inverse.py
data/05-strip-asymptotics-expansion_symbolic_2.json Report 85: output of generate_expansion.py --order 2 (symbolic height)
data/05-strip-asymptotics-verification.json         Report 85: recorded run of verify.py (its seconds fields are the producer's)
data/05-strip-asymptotics-CHECKS.json               Report 85: the producer's release checklist (describes its 7-page PDF)
code/06-strip-diagonals-verify.py                   Part V, Report 91: reruns check_exact.py and compares (delivered as verify.py)
code/06-strip-diagonals-check_exact.py              Report 91: cell-poset, row-state, event-sum and chamber-walk checks (standard library)
code/06-strip-diagonals-build_local.sh              Report 91: two-pass pdflatex with local font maps (delivered as build_local.sh)
data/06-strip-diagonals-check_exact.json            Report 91: deterministic output of check_exact.py
data/06-strip-diagonals-verification.json           Report 91: summary written by verify.py
data/06-strip-diagonals-CHECKS.json                 Report 91: the producer's checklist (with the SHA-256 of its unshipped PDF)
data/06-strip-diagonals-SOURCES.json                Report 91: primary-source pointers and their roles
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Part I's placement moved `build.sh` to
`code/`, `requirements-numerics.txt` and `notes/PROPOSED_OEIS_ADDITIONS.txt`
to `data/` (the latter as `notes-PROPOSED_OEIS_ADDITIONS.txt`), and
`notes/SOURCES_AND_STATUS.md` to the report root as
`notes-SOURCES_AND_STATUS.md`. Part II's placement gave every file the
prefix `02-boundary-phases-`, kept `code/` and `data/`, moved `build.sh` to
`code/`, `requirements.txt` and `notes/PROPOSED_OEIS_NOTE.md` to `data/`,
and `notes/SOURCES_AND_STATUS.md` to the report root.
`data/02-boundary-phases-requirements.txt` is a generic byte copy of a
requirements file shipped elsewhere in the collection. The batch-101
placement gave Report 231's files the prefix `03-height-four-`, Report
233's `04-height-five-`, Report 85's `05-strip-asymptotics-` and Report
91's `06-strip-diagonals-` (Part order, not archive order), put programs in
`code/`, receipts and records in `data/`, and source records and Report
231's code README at the report root; the tables in the shipped-layout
notes at the end of Sections 33.3, 42.3, 43 and 44 map every delivered
name. Report 233's `exact_algebra.py` is a different file from Report
231's.

Not shipped: Part I's delivered 22-page `article.pdf` (307,362 bytes) and
`SHA256SUMS.txt` (covering its 20 other files); Part II's `article.tex`,
`README.md`, 24-page `article.pdf` (345,561 bytes) and `SHA256SUMS.txt`
(covering its 21 other files). They survive in the archives:
`git show 9d6968c8a:docs/incoming/Shifted_Rectangle_Asymptotics.zip > <scratch>/Shifted_Rectangle_Asymptotics.zip`
and
`git show 2172df76a:docs/incoming/Shifted_Rectangle_Boundary_Research.zip > <scratch>/Shifted_Rectangle_Boundary_Research.zip`.
Of the batch-101 sources these are not shipped: the LaTeX sources
(Report 231's `article.tex` and `sections/01..09`, Report 233's
`article.tex` and `sections/01..11`, Reports 85 and 91's `article.tex`),
the four delivered READMEs, the PDFs (`Report231.pdf`, 25 pages;
`Report233.pdf`, 30 pages; the 7- and 9-page `article.pdf` of Reports 85
and 91), the checksum manifests (`MANIFEST.sha256` of Reports 231 and 233,
`SHA256.json` of Reports 85 and 91), the integrity checkers
`check_integrity.py` of Reports 85 and 91, and Report 85's
`build_local.sh` (the last two of Report 85 are byte copies of files
shipped elsewhere in the collection). They survive in the archives of the
arrival commit:
`git show 60f54ea06:docs/incoming/Report231.zip > <scratch>/Report231.zip`,
`git show 60f54ea06:docs/incoming/Report233.zip > <scratch>/Report233.zip`,
`git show 60f54ea06:docs/incoming/ProveIt_Fixed_Height_Shifted_Strips_Asymptotics.zip > <scratch>/ProveIt_Fixed_Height_Shifted_Strips_Asymptotics.zip`
and
`git show 60f54ea06:docs/incoming/ProveIt_Shifted_Strips_Rational_Diagonals_and_Transcendence.zip > <scratch>/ProveIt_Shifted_Strips_Rational_Diagonals_and_Transcendence.zip`.
Nothing was excluded as heavy.

**Third-party data.** `data/oeis_selected.json` holds terms of A181198 and
A181199 transcribed from The On-Line Encyclopedia of Integer Sequences
(https://oeis.org/A181198, https://oeis.org/A181199 and their b-files
`b181198.txt`, `b181199.txt`, inspected 3 October 2026 according to the
file), and `code/02-boundary-phases-verify.py` embeds the first ten terms of
A181198 and A181199 (`n = 1, …, 10`, inspected 4 October 2026) as reference
values. OEIS content is published by The OEIS Foundation Inc. under the
Creative Commons Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); those
terms are third-party data under that licence, **not** MIT-0 like the rest
of the repository. The b-files are by Christoph Koutschan, with earlier terms
by Alois P. Heinz, and the A181199 asymptotic conjecture is Vaclav
Kotesovec's, as attributed in the entries. Part I's `data/numerics.*` are
computed from these terms; Part II's counts are all computed by its own
programs. The draft `data/notes-PROPOSED_OEIS_ADDITIONS.txt` quotes the
A181199 formula with its attribution. No program contacts OEIS.
Batch 101 adds three more items of OEIS content under the same licence:
`code/05-strip-asymptotics-check_midpoint.py` embeds fifteen terms each of
A181198 and A181199 ("published initial terms"),
`code/04-height-five-printed_coefficients.py` transcribes the A181199
recurrence from the entry's internal record, and
`code/03-height-four-verify_report231.py` hard-codes the three A181198
coefficient polynomials. Report 233's `asymptotic_certificate.py` lists the
first eight A181199 terms as expected values of its own recurrence run.

Delivered text that names the delivery layout or a file not shipped:
Section 11.3 of the article ("From the archive's top-level directory",
`bash build.sh`; a dated note there gives the shipped names) and Sections
23.1–23.3 (`data/verification.json`, `data/numerics.csv`, "From the package
root" with unprefixed script names; a dated note at the end of Section 23
gives the shipped names); both delivery READMEs, replaced
by this guide; `code/build.sh` and `code/02-boundary-phases-build.sh` (each
runs `cd "$(dirname "$0")"`, so from `code/` it cannot find an
`article.tex`); `02-boundary-phases-notes-SOURCES_AND_STATUS.md` (it names
`verify.py` and the package layout); `data/pdf_preflight.json` (22 pages
and 307,362 bytes: Part I's delivered PDF, not this rebuild); and the
`seconds` fields of `data/verification.json`,
`data/02-boundary-phases-verification.*` and
`data/02-boundary-phases-numerics.json` (the producers' machines). The
check table of Section 23.1 merges some of the script's sixteen categories
(640 = 320 + 320, 21 = 20 + 1, 228 = 3 · 76, 7 = 4 + 3, 34 = 6 + 28); the
total, 1,954, agrees. Batch 101: Sections 33.1 and 33.3 (the file list,
"From the package directory", `build.py`, the manifest and "this PDF"),
42.1 and 42.3 (`code/verify_certificate.py`, `README.md`, the frozen PDF
and inventory) and Subsections 43.7 and 44.8 ("The source package", "The
accompanying ... checker") use delivery names; dated notes at the end of
Sections 33.3, 42.3, 43 and 44 give the shipped ones.
`03-height-four-code-README.md` says "Run from this directory" with
unprefixed names; `03-height-four-SOURCES.md` and
`04-height-five-SOURCES.md` name `code/printed_coefficients.py` and the
package; `data/05-strip-asymptotics-CHECKS.json` and
`data/06-strip-diagonals-CHECKS.json` describe the unshipped PDFs (the
latter with its SHA-256); `code/03-height-four-build.py` and
`code/04-height-five-build.py` need the unshipped manifests and PDFs, and
`code/06-strip-diagonals-build_local.sh` changes to its own directory and
needs `article.tex`.

**Byte-level notes.** `data/numerics.csv`,
`data/02-boundary-phases-exact_rare_counts.csv` and
`data/02-boundary-phases-numerics.csv` are CRLF throughout (Python's `csv`
module); three `-text` lines in `SetTheory/Cardinals/.gitattributes` keep
their bytes. Every other shipped file is LF, including all 36 batch-101
files. The programs write JSON in
text mode, so on Windows a rerun emits CRLF where the shipped files are LF;
compare after stripping `\r`.

## Rerun the checks (on a scratch copy)

Never run the programs in place: they set `ROOT` to the parent of `code/`
and overwrite the shipped records in `data/`, and only Part I's
`coefficients.py` and Part II's `coefficients.py` take an output option.

**Part I.** Copy `code/` and `data/` (the delivered layout of those two
directories) and run there (Git Bash, from this directory):

```sh
R=$(pwd); T=$(mktemp -d); cp -r code data "$T/"; cd "$T"
py code/verify.py > verify.out                             # standard library; ~1 min
py code/coefficients.py --height 5 --order 5 --output c5.json
uv run --no-project --with mpmath==1.3.0 python code/numerics.py > numerics.out
for f in data/*; do tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "$R/$f") \
  && echo "same  $f" || echo "DIFF  $f"; done                # only verification.json (seconds)
tr -d '\r' < c5.json | cmp - "$R/data/coefficients_m5.json" && echo same c5
```

(The copy also carries Part II's prefixed files, which Part I's programs
ignore.)

**Part II.** Its scripts import one another and read and write `data/`
under their delivered names, so restore those names in the copy:

```sh
R=$(pwd); T=$(mktemp -d); mkdir -p "$T/code" "$T/data"
for f in code/02-boundary-phases-*.py; do cp "$f" "$T/code/${f#code/02-boundary-phases-}"; done
for f in data/02-boundary-phases-*; do cp "$f" "$T/data/${f#data/02-boundary-phases-}"; done
cd "$T"; PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/verify.py > verify.out                            # ~1 min; 1,954 checks
$PY code/numerics.py > numerics.out                        # ~45 s
$PY code/coefficients.py --height 5 --order 3 --output c5.json
$PY code/inverse_profile.py --index 60 --height 5 > inverse.out
for f in data/*; do b=${f#data/}; tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "$R/data/02-boundary-phases-$b") \
  && echo "same  $b" || echo "DIFF  $b"; done             # only verification.*, numerics.json (seconds)
tr -d '\r' < c5.json | cmp - "$R/data/02-boundary-phases-coefficients_m5.json" && echo same c5
```

(On a POSIX host use `python3` for `py`. Do not use `python -O`: the checks
are assertions.) Intake results are under "Checks made at intake".

**Part III (Report 231).** The verifier imports its two modules under
their delivered names; it writes nothing unless given `--receipt` with a
new file name:

```sh
R=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"
for f in exact_algebra formal_series verify_report231; do cp code/03-height-four-$f.py "$T/code/$f.py"; done
cd "$T"; py -B code/verify_report231.py --self-test > out.json          # ~3 s, standard library
tr -d '\r' < out.json | cmp - "$R/data/03-height-four-receipt.json" && echo same receipt
py -B -O code/verify_report231.py --self-test | tr -d '\r' | cmp - "$R/data/03-height-four-receipt.json" && echo same -O
```

**Part IV (Report 233).** The same, with four modules; the verifier writes
no files:

```sh
R=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"
for f in exact_algebra printed_coefficients verify_certificate asymptotic_certificate; do cp code/04-height-five-$f.py "$T/code/$f.py"; done
cd "$T"; py -B code/verify_certificate.py > out.json                    # ~20 s, standard library
tr -d '\r' < out.json | cmp - "$R/data/04-height-five-receipt.json" && echo same receipt
```

(Report 233's README also runs it with `-O` and, for its builds, sets
`PYTHONINTMAXSTRDIGITS=640`. The `build.py` programs of Reports 231 and 233
need the unshipped manifests and frozen PDFs; re-extract the archive of
`60f54ea06` on a POSIX host to replay them.)

**Part V (Reports 85 and 91).** Restore the delivered layout (`verify.py`
at the root, programs and their JSON in `code/`):

```sh
R=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"; cp code/05-strip-asymptotics-verify.py "$T/verify.py"
for f in check_gaussian_integrals check_inverse check_midpoint gaussian_corrections generate_expansion ward_corrections; do cp code/05-strip-asymptotics-$f.py "$T/code/$f.py"; done
for f in check_gaussian_integrals check_inverse check_midpoint expansion_symbolic_2 gaussian_corrections ward_corrections; do cp data/05-strip-asymptotics-$f.json "$T/code/$f.json"; done
cd "$T"; uv run --no-project --with sympy==1.14.0 python verify.py      # several minutes
for f in code/*.json; do b=${f#code/}; tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "$R/data/05-strip-asymptotics-$b") \
  && echo "same  $b" || echo "DIFF  $b"; done                            # all six same (verification.json, at the root, differs in seconds)

R=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"; cp code/06-strip-diagonals-verify.py "$T/verify.py"
cp code/06-strip-diagonals-check_exact.py "$T/code/check_exact.py"; cp data/06-strip-diagonals-check_exact.json "$T/code/check_exact.json"
cd "$T"; py verify.py                                                  # ~2 s; matches_distributed_data: true
tr -d '\r' < verification.json | cmp - "$R/data/06-strip-diagonals-verification.json" && echo same
```

(Report 85's suite runs its programs with `-O`, harmlessly: they test with
`raise`. Report 91's `verify.py` uses `assert`; do not run it with `-O`.)

## Build the PDF

pdfLaTeX (fontenc, xcolor, amsmath, amsthm, newtx, geometry, microtype,
mathtools, booktabs, array, longtable, graphicx, enumitem, fancyhdr,
tcolorbox, hyperref). The article is self-contained. Build in a scratch copy
(neither `build.sh` works from its shipped place):

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 135 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The log
reports "ignored: Infinite glue shrinkage found in box being split" three
times, where a notation longtable breaks across a page (once for Part II's,
as before the batch-101 write, and once each for Parts III and IV); it is
TeX's notice, not a warning, and the output is correct. Before the
batch-101 write the report had 55 pages, and before the batch-98 write 24.
Reports 231, 233, 85 and 91, built the same way from their delivered
sources, give 25, 30, 7 and 9 pages. Part I's delivered source, built
the same way, gives 22 pages with one duplicate `page.1` destination (the
title page); Part II's gives 24 pages.

## Provenance

- Part I cites: OEIS A181196–A181199 and the b-files of A181198 and
  A181199; Kauers–Koutschan, *Some D-finite and some possibly D-finite
  sequences in the OEIS*, J. Integer Seq. 26 (2023) 23.4.5
  (arXiv:2303.02793); P. Sun, Electron. J. Combin. 24(2) (2017) P2.41;
  B. T. Chan, *Periodic P-partitions* (Eur. J. Combin. 2023); Flajolet–Sedgewick,
  *Analytic Combinatorics*; DLMF §§4.13, 5.11, 18.19.
- Part II cites: OEIS A181196–A181199 (inspected 4 October 2026);
  Kauers–Koutschan (arXiv v2, Section 6.4, Conjectures 18–19);
  A. Bostan, P. Lairez, B. Salvy, *Multiple binomial sums*, J. Symbolic
  Comput. 80 (2017) 351–386 (arXiv:1510.07487; Definition 1.1, Theorem 3.5,
  Corollary 3.6); Sun; and Part I at the pin `db20eb379`.
- Part III (Report 231) cites: Kauers–Koutschan (arXiv:2303.02793v2, 24
  April 2023, Section 6.4, Conjecture 18 on printed page 33); OEIS A181198
  and its internal record (retrieved 5 October 2026, revision 39 of 1
  January 2024); Sun; DLMF §5.11 (5.11.1, §5.11(ii)); Part I by blob
  `2b40ded9`; Part II's manuscript (a "user-held copy", 24 pages);
  arXiv:2607.24832 inspected in its source record without a matching proof.
- Part IV (Report 233) cites: Kauers–Koutschan (Conjecture 19, printed page
  34, the rising-factorial overbars checked on the page); OEIS A181199 and
  its internal record (5 October 2026); Sun (bibliography only); DLMF §§4.13,
  5.11; Part I by blob `2b40ded9`.
- Part V cites: Report 85 — OEIS A181198, A181199 (accessed 1 October
  2026), Kauers–Koutschan, Sun; Report 91 — Bostan–Lairez–Salvy (Definition
  1.1, equation (6), Proposition 3.12, Theorem 3.5, Corollary 3.6),
  Kauers–Koutschan, Sun, F. Lindemann, *Ueber die Zahl π*, Math. Ann. 20
  (1882) 213–225, OEIS A181196, A181198, A181199 (accessed 2 October 2026),
  and Report 85 ("unpublished project report").
- Repository input: Part I's pin `6bf7f30d0` (3 October 2026), for a bounded
  identifier search and the README of `a189281-path-forest-expansions`, with
  no repository theorem used; Part II's pin `db20eb379` (4 October 2026),
  for Part I (its Theorem 2.1, Corollary 2.2, Theorem 2.3 and Research
  question 7), used only in Corollary 21.2.
- Part I: batch 85 of `docs/incoming`, manuscript 09; arrival `9d6968c8a`,
  placement `ddf8df5d5` (batch 85C), written in the batch-85 write phase
  (3 October 2026). Part II: batch 98, manuscript 02; arrival `2172df76a`,
  placement `0fba5167f` (batch 98B), written in the batch-98 write phase
  (5 October 2026). Each Part is a single manuscript, so no merge choices
  were made; the write's choices were where to place Part II (after Part
  I's conclusion, its appendices after Part I's), the renaming of `d`, and
  the corrections listed above.
- Parts III–V: batch 101; Research Reports 231, 233, 85 and 91 of the
  session bundle; arrival `60f54ea06`, placement `f7c612c72`, written in the
  batch-101 write phase (5 October 2026). Reports 231 and 233 pin this
  report's source by blob `2b40ded9` (Part I only); Reports 85 and 91 read
  no repository material. The write's choices: Parts in the order of the
  placement prefixes (the new theorems first, Part V last although its
  manuscripts are the oldest); each new Part after the last section of the
  previous one and before the appendices, Report 233's appendix as
  Appendix E after Appendix D; Reports 85 and 91 as one section each, with
  Report 91's re-proof of the leading equivalent (Subsection 44.6) kept in
  full beside Report 85's (Subsection 43.3), because it adds detail; no
  symbol renamed; and the write's own Propositions 33.2 and 42.2.
