# Fixed-Height Shifted Rectangles

**Part I: an unconditional proof of the A181199 asymptotic, all-order expansions, and an algebraicity dichotomy. Part II: rational diagonals and rare boundary phases — D-finiteness at every fixed height and a sharp exponential refinement**

A research report in two Parts, built from two manuscripts: Part I dated
3 October 2026, Part II dated 4 October 2026 and added on 5 October 2026.
Both title pages read "Prepared for Vladimir Reshetnikov" and both PDF
author fields "Research report prepared for Vladimir Reshetnikov"; neither
package names a human author or a tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 09 | `Shifted_Rectangle_Asymptotics.zip` (wrapper directory `Shifted_Rectangle_Asymptotics/`, 343,338 bytes, 21 files), arrival commit `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, the ProveIt bibliography entry and `notes-SOURCES_AND_STATUS.md`) | `ddf8df5d5` (batch 85C) | Part I: Sections 1–13, Appendices A–B |
| 02 | batch 98, manuscript 02 | `Shifted_Rectangle_Boundary_Research.zip` (doubled wrapper directory `Shifted_Rectangle_Boundary_Research/Shifted_Rectangle_Boundary_Research/`, 390,943 bytes, 22 files), arrival commit `2172df76a`; main file `article.tex` | `db20eb379` (`db20eb37982abc0f163c6d308d392f5ac4c9bc62`, 4 October 2026, quoted in Section 14.2 and `02-boundary-phases-notes-SOURCES_AND_STATUS.md`) | `0fba5167f` (batch 98B) | Part II: Sections 14–25, Appendices C–D |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. Both manuscripts say
their theorems have not been independently peer reviewed or proof-assistant
verified, and that historical priority is not certified. The exact
computations corroborate the proofs on finite ranges; the numerical tables
are decimal diagnostics, not interval enclosures.

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

## What is not claimed

- **Neither guessed recurrence is proved:** not A181198's order-two,
  degree-nine recurrence, nor its conjectured finite-sum solution, nor
  A181199's order-three, degree-twenty-four recurrence, nor Conjectures
  18–19 of Kauers–Koutschan. Part II proves that *some* recurrence exists;
  it supplies no rational function, telescoper or minimal operator
  (Remark 16.2), ran no Maple or binomial-sum package, and `m(m−1)` counts
  summation indices, not diagonal variables or operator order. Both draft
  OEIS texts say explicitly not to mark either recurrence as proved.
- The expansions are Poincaré expansions for fixed `m` and fixed truncation
  order: no growing-height theorem, no Borel summability, Stokes data or
  exponentially improved transseries. Part II's rare sector is a
  combinatorially defined beyond-all-orders refinement, not a Stokes
  multiplier, and the next boundary sector is not analysed; the bound of
  Proposition 18.2 is an upper rate, not the next sector. Error constants
  exist but are not computed, and no onset is certified.
- Nonalgebraicity is not non-D-finiteness (Remark 8.1); whether `F_m` is
  D-finite for every `m` is Question 7. [Added 5 October 2026: Part II,
  Theorem 14.1, proves D-finiteness at every fixed `m`, the first half of
  Question 7; the growth of the minimal order, its second half, stays
  open.] Part II takes the nonalgebraicity from Part I and does not reprove
  it. P-recursiveness of expectations (quotients by `T_m(n)`) is not
  asserted.
- The boundary bound `2m 2^(−n)` is not claimed sharp. [Added 5 October
  2026: its rate `2^(−n)` is the true one, but not its constant or, for
  `m ≥ 3`, its power of `n` (Proposition 18.3).]
- Theorems 9.1, 9.2 and 21.3 are one-time laws, not process convergence;
  in Theorem 21.3 the variable `U` is an auxiliary coupling.
- The inverse-index approximations are not integer-threshold certificates,
  and the inversion method is standard (see below); the smallest `n` from
  which monotonicity and log-convexity hold is not identified.
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
  OEIS identifier is proposed for `R_m`.

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

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats shifted tableaux, and the
report's place in the collection confers no formal status. The one formalized
neighbour is general: Theorem J.23 of the transseries volume (below), whose
real branch rules are proved in
`Analysis/FabiusFunction/Lean/FabiusFunction/LinLogCoreInversion.lean`
(rated "Partial" in that volume's register; nothing about shifted rectangles).
Part II's eighth question (Research question 15) proposes formalizing its
finite combinatorial components; that is a proposal only.

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
  condition.

**Overlap of the two Parts.** Part II was written against Part I's text
(unchanged between its pin and its placement) and shares 1.98 % of its word
8-grams with it. It re-derives Part I's state space, imports the shifted
hook product that Part I's Appendix A proves, and uses Gaussian and binomial
Vandermonde identities of the same type as Part I's (6.1), (5.14), (6.6)
and (5.16), now mixed over a beta law; Lemma 19.1 is a random-cut variant
of Part I's Theorem 4.1 and Theorem 21.3 the rare-event analogue of
Theorem 9.1. The provenance note at the head of Part II lists them.

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

**Stale claims.** Part I: "Identifier searches for A181198 and A181199
returned no matching repository report" is true at its pin and still true
of the tree outside this report. Part II's repository claims were checked
at placement and are true (its predecessor proves the all-order expansion
and nonalgebraicity, asks D-finiteness as Question 7, does not claim its
boundary bound sharp, and proves no recurrence); its framing of Questions
4 and 7 is corrected as above. Dated notes in Part I record what Part II
changes: before the table of contents, at the end of Section 4.1, after
Remark 8.1, and at Research questions 4 and 7.

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

## Files

```text
README.md                                           this guide (replaces both delivery READMEs)
article.tex                                         the report, Parts I and II
article.pdf                                         compiled report, 55 pages
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
requirements file shipped elsewhere in the collection.

Not shipped: Part I's delivered 22-page `article.pdf` (307,362 bytes) and
`SHA256SUMS.txt` (covering its 20 other files); Part II's `article.tex`,
`README.md`, 24-page `article.pdf` (345,561 bytes) and `SHA256SUMS.txt`
(covering its 21 other files). They survive in the archives:
`git show 9d6968c8a:docs/incoming/Shifted_Rectangle_Asymptotics.zip > <scratch>/Shifted_Rectangle_Asymptotics.zip`
and
`git show 2172df76a:docs/incoming/Shifted_Rectangle_Boundary_Research.zip > <scratch>/Shifted_Rectangle_Boundary_Research.zip`.
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
total, 1,954, agrees.

**Byte-level notes.** `data/numerics.csv`,
`data/02-boundary-phases-exact_rare_counts.csv` and
`data/02-boundary-phases-numerics.csv` are CRLF throughout (Python's `csv`
module); three `-text` lines in `SetTheory/Cardinals/.gitattributes` keep
their bytes. Every other shipped file is LF. The programs write JSON in
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

## Build the PDF

pdfLaTeX (fontenc, xcolor, amsmath, amsthm, newtx, geometry, microtype,
mathtools, booktabs, array, longtable, graphicx, enumitem, fancyhdr,
tcolorbox, hyperref). The article is self-contained. Build in a scratch copy
(neither `build.sh` works from its shipped place):

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 55 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. Before the
batch-98 write the report had 24 pages. Part I's delivered source, built
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
