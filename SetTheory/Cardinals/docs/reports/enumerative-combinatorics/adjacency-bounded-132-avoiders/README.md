# Strict growth and the Catalan limit for adjacency-bounded 132-avoiding permutations

**Strict monotonicity of the growth constants, the exact constant 2 log π in their approach to 4, the largest-jump law near the boundary m = n − d, the macroscopic jump law for m proportional to n, the critical moments of the largest jump, the staircase of polynomial rarity below half size, the exact half-size crossover, and every fixed phase amplitude and reciprocal crossover**

This is a research report in eight parts. Part I is the original report of
19 September 2026. Part II was added on 28 September 2026 in batch 38 of
ProveIt's incoming-report intake, from a later manuscript that answers the
question Part I left open: whether the centered remainder `E_m` converges.
Part III was added on 29 September 2026 in batch 43, from a third manuscript
that treats the joint regime next to the trivial bound, `m = n − d`, through
the largest adjacent jump of a random 132-avoider. Part IV was added on the
same day in batch 52, merged from two further manuscripts, written
independently of each other, that answer Part III's questions on the bulk
profile and the exact moment constants (its Sections 32.1 and 32.2). Part V
was added on 30 September 2026 in batch 64, from a sixth manuscript that
answers Part IV's question on the centered half-moment and the subcritical
moment corrections (its Section 47.6). Part VI was added on the same day in
batch 68, from a seventh manuscript that proves the exact polynomial order of
`P(M_n ≤ ⌊θn⌋)` for every fixed `0 < θ < 1` and the order and order-crossover
scale at `m = n/2`, answering at the level of orders Part IV's questions on
the hierarchy below half size and the window at `m = n/2` (its Sections 47.1
and 47.2) and Part V's half-size question (its Section 63.3). Part VII was
added on 1 October 2026 in batch 71, from an eighth manuscript that proves
the limits Part VI left open at half size:
`n P(M_n ≤ ⌊n/2 + t sqrt(n)⌋) → 6 + 12 t_+/sqrt(π)` locally uniformly in `t`,
and `P(M_n ≤ ⌊θn⌋) ~ I_3(θ)/(2πn)` for `1/3 < θ ≤ 1/2`; this answers Part VI's
questions 74.1–74.3 in their first case (`r = 2`, `q = 2`) and the
transition questions of Parts IV and V (47.2, 63.3). Part VIII was added on
the same day in batch 72, from a ninth manuscript that proves them for every
fixed index: `P(M_n ≤ ⌊θn⌋) ~ ϰ_p I_p(θ) n^(-(p−1)/2)` in every phase
`1/p < θ < 1/(p − 1)`, with a capped-simplex integral `I_p` and
`ϰ_p = (p + 1)/(2^p π^((p−1)/2))`, and
`n^(r/2) P(M_n ≤ ⌊n/r + t 𝔴_r(n)⌋) → 𝔎_r + 𝔏_r t_+^(r−1)` at every
reciprocal threshold `1/r`; Part VII's two theorems are its cases `p = 3` and
`r = 2`, and Part IV's profile its case `p = 2`. This answers Part VII's
questions 89.1, 89.2 and 89.4, Part VI's 74.1–74.3 and, for the parser's
macroscopic pieces, 74.4. All nine are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Strict growth and the Catalan limit for adjacency-bounded 132-avoiding permutations*) | `strict_growth_132.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–9 (pp. 14–28) and Appendices A–C (pp. 198–199) |
| 02 | batch 38, manuscript 04 (*Closing the Catalan growth-constant gap: Endpoint renewal comparison for adjacency-bounded 132-avoiding permutations*, 28 Sep 2026, 23-page PDF as delivered) | `Closing_Catalan_Growth_Gap` (inner `Adjacency_Growth_Constant/`, main file `article.tex`) | `6c9175a54` | `938b2f74e` (prefix `02-centered-remainder-`) | Part II: Sections 10–20 (pp. 29–49) |
| 03 | batch 43, manuscript 02 (*The Largest Jump Is Almost Maximal: An algebraic boundary law for random 132-avoiding permutations*, 29 Sep 2026, 26-page US Letter PDF as delivered) | `ProveIt_Largest_Jump_Research.zip` (inner `ProveIt_Largest_Jump/`, main file `article.tex`), arrived in `06bcc37a8` | `8d936ee23` | `faef2ed2a` (prefix `03-largest-jump-`) | Part III: Sections 21–36 (pp. 50–74) |
| 04 | batch 52, manuscript 10 (*The Macroscopic Jump Law: Exact rare-event profiles and moment constants for random 132-avoiding permutations*, 29 Sep 2026, 23-page US Letter PDF as delivered); the base of Part IV. It also read the standalone Part III source `article(20260929-161704).tex` from Vladimir's library | `ProveIt_Macroscopic_Jump.zip` (inner `ProveIt_Macroscopic_Jump/`, main file `article.tex`), arrived in `458ccfb80` | `1ee53d57d` | `a701d9098` (prefix `04-macroscopic-jump-`) | Part IV: Sections 37–50 (pp. 75–115), merged with 05 |
| 05 | batch 52, manuscript 11 (*Macroscopic Deficits of the Largest Jump: A rare-event law and exact moment constants for 132-avoiding permutations*, 29 Sep 2026, 24-page US Letter PDF as delivered) | `ProveIt_Macroscopic_Jump_Research.zip` (inner directory also `ProveIt_Macroscopic_Jump/`, main file `article.tex`), arrived in `11e1e9001` | `1ee53d57d` | `a701d9098` (prefix `05-macroscopic-deficits-`) | Part IV (as 04), in particular Sections 40.4–40.5, 42, 43.3 and 46.2–46.5 |
| 06 | batch 64, manuscript 06 (*Every Logarithmic Scale Contributes: Critical moment crossover and endpoint corrections for the largest jump of a 132-avoiding permutation*, 30 Sep 2026, 27-page US Letter PDF as delivered) | `ProveIt_Critical_Jump_Moments.zip` (inner `Critical_Jump_Moments/`, main file `article.tex`), arrived in `7747fcfdd` | `cb1646dc4` | `3025c15df` (prefix `06-critical-moments-`) | Part V: Sections 51–66 (pp. 116–143) |
| 07 | batch 68, manuscript 05 (*A Staircase of Polynomial Rarity: Bulk exponents and reciprocal-threshold crossover scales for adjacency-bounded 132-avoiding permutations*, 30 Sep 2026, 25-page US Letter PDF as delivered) | `ProveIt_Polynomial_Rarity.zip` (inner `ProveIt_Polynomial_Rarity/`, main file `article.tex`), arrived in `a866ff9a2` | `ffddaa8b9` | `29e52fcdf` (prefix `07-polynomial-rarity-`) | Part VI: Sections 67–78 (pp. 144–170) |
| 08 | batch 71, manuscript 03 (*Exact half size crossover for adjacency bounded 132 avoiders*, 1 Oct 2026, 8-page US Letter PDF as delivered; byline "AI-assisted mathematical research") | `132_Avoider_Crossover_Package.zip` (inner `Half_Size_Crossover/`, main file `half_size_crossover.tex`), arrived in `aee32ad45` | `29e52fcdf` | `427bca743` (prefix `08-half-size-crossover-`) | Part VII: Sections 79–89 (pp. 171–183) |
| 09 | batch 72, manuscript 41 (*Exact Phase Amplitudes and Reciprocal Crossovers for 132-Avoiders*, 1 Oct 2026, 8-page A4 PDF as delivered; byline "Research note prepared for Vladimir Reshetnikov with OpenAI") | `General_132_Avoider_Crossovers_Package.zip` (inner `General_132_Avoider_Crossovers/`, main file `general_avoider_crossovers.tex`), arrived in `1512ef835` | `7421a4ca6` | `9e6b04645` (prefix `09-general-crossovers-`) | Part VIII: Sections 90–100 (pp. 184–197) |

The pin `6c9175a54` is ProveIt commit
`6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0`; the manuscript quotes the blob
`5ec75ee4…` of the `article.tex` it read, and that blob was unchanged at the
placement commit, so Part II's statements about Part I refer to the text
printed here. The archive arrived in `fbba58593`. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. Part II
prints every result, proof, example, remark, limitation and question of the
manuscript. What it re-derives from Part I (endpoint recurrence, component
structure and spectral interface, first-entry lemma, injective skew blocks) is
printed once, in Part I, and credited; the manuscript's different proof of
`lambda_U(m) > 1` is kept as a second proof (Section 11). Section 20.5 of the
article lists where the merge had to choose.

The pin `8d936ee23` is ProveIt commit
`8d936ee2357f9decf78c2ecc7d9baf3100a6787d`; manuscript 02 of batch 43 quotes
the blobs `7f56b878…` of this `README.md` and `f24ea59a…` of `article.tex`,
and both were unchanged at its placement commit, so Part III's statements
about Parts I–II refer to the text printed here. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. Part III
prints every result, proof, example, remark, limitation and question of the
manuscript (its three appendices become Sections 34–36). It uses none of the
theorems of Parts I–II; the one count it shares with Part I (the first-entry
formula, Part I's `h(k,j)` reindexed) is kept with the manuscript's different
derivation and credited (Remark 23.2). Section 36.2 lists where the merge had
to choose.

The pin `1ee53d57d` is ProveIt commit
`1ee53d57de253d16cdaad79d1f54bbd95d76d682` (root tree `c772efcde0`, which
manuscript 10 records). At that commit this `README.md` and `article.tex` had
the blobs `815242ed6…` and `aeadaf364b…` (manuscript 11 quotes the latter),
and both were unchanged at the placement commit `a701d9098`, so Part IV's
statements about Parts I–III refer to the text printed here. Neither
manuscript saw the other. Manuscript 10 additionally read the standalone
source of Part III's manuscript, `article(20260929-161704).tex`, from
Vladimir's file library (its `SOURCES.md`, shipped as
`04-macroscopic-jump-SOURCES.md`); that file is not in the repository, and its
own pin is Part III's `8d936ee23`. The two manuscripts, their PDFs and
delivery READMEs are not shipped; they survive in the arrival commits. Their
`SHA256SUMS` ledgers were verified at placement (16/16 and 20/20) and retired.
Manuscript 10 is the base (first arrival, broader regime coverage); Part IV
prints every result, proof, example, remark, limitation and question of both,
prints each shared result once with both sources credited, and keeps the
genuinely different proofs as second routes. Section 50.3 lists where the
merge had to choose.

The pin `cb1646dc4` is ProveIt commit
`cb1646dc442724f8e298cf259195b6c308367d80`, which manuscript 06 resolved
through GitHub's main branch on 30 September 2026. It records the blobs
`9b6865915b…` of this `README.md`, `c673f447a2…` of `article.tex` and
`f0248e0d61…` of `code/05-macroscopic-deficits-model.py`; all three were
unchanged at the placement commit `3025c15df`, so Part V's statements about
Parts I–IV refer to the text printed here. The manuscript, its PDF and its
delivery README are not shipped; they survive in the arrival commit
`7747fcfdd`. Its `SHA256SUMS` ledger was verified at placement (21/21) and
retired. Part V prints every result, proof, example, remark, limitation and
question of the manuscript. Its three inputs (Part III's limiting law and
total-variation bound, Part IV's profile) and the recurrence of its checks
(Parts I, III and IV) are printed again as its interface, each credited;
Section 66.2 lists where the merge had to choose.

The pin `ffddaa8b9` is ProveIt commit
`ffddaa8b9c89e7bf027e1442cc6216bb010906d0` (root tree `cb9c68b025`, which
manuscript 05 of batch 68 records). The manuscript read this `README.md`,
`code/model.py` and `code/05-macroscopic-deficits-model.py` there and records
their blobs `a40d20342f…`, `aee5528c72…` and `f0248e0d61…`; it did not read
`article.tex` (blob `0b7cb2f2e6…` at the pin). All four were unchanged at the
placement commit `29e52fcdf`, so Part VI's statements about Parts I–V refer to
the text printed here. The manuscript, its PDF and its delivery README are not
shipped; they survive in the arrival commit `a866ff9a2`. Its `SHA256SUMS`
ledger was verified at placement (15/15) and retired. Part VI prints every
result, proof, example, remark, limitation and question of the manuscript. It
uses no asymptotic theorem of Parts I–V: its two counting envelopes are
Part I's Propositions 5.1 and 5.2 (the latter at `d = 1`), reproved, and its
lower bounds are Part IV's Theorem 45.1, re-derived and credited; the upper
bounds, the endpoint orders, the crossover comparison and the renewal theorem
are new. Section 78.2 lists where the merge had to choose.

The pin `29e52fcdf` is ProveIt commit
`29e52fcdf8bfa99d52a76d3de380f58c24584b1e`, the placement commit of batch 68.
Manuscript 03 of batch 71 records the blob `0b7cb2f2e6…` of this
`article.tex` there, which ends at Part V (it is also the blob of the parent
of `cfdefe6e3`, the commit that wrote Part VI), and it read the incoming
batch-68 archive `ProveIt_Polynomial_Rarity.zip` (blob `cf18b47515…`,
arrival commit `a866ff9a2`), whose manuscript is printed here as Part VI. So
the manuscript's statements about Parts III–V refer to the text printed here
(less the dated batch-68 notes), and its citations of the "incoming
Polynomial Rarity manuscript" are printed as references to Part VI. The
manuscript, its PDF and its delivery README are not shipped; they survive in
the arrival commit `aee32ad45`. Its `SHA256SUMS` ledger was verified at
placement (11/11) and retired. Part VII prints every result, proof, remark,
limitation and question of the manuscript. What it re-derives from Parts IV
and VI (the first-deficiency and last-entry estimates, the threshold parser
above half size, the word masses and the two-piece acceptance weight, the
local small-word bound and the exponential tilt) is printed with merge notes
naming the earlier statement; the new content is the two limit theorems, the
three-piece endpoint table and its mass 8, the exclusion of every other
parser family at the scale `1/n`, and `I_3(1/2) = 12π`. Section 88.4 lists
where the merge had to choose.

The pin `7421a4ca6` is ProveIt commit
`7421a4ca60fdf125411edf412f825aac54278b37` ("Record write and catalogue
commits of batch 71 in the incoming README"). Manuscript 41 of batch 72
records the blob `b9697af6c8…` of this `article.tex` there (and its SHA-256),
which contains Parts I–VII as printed; the report did not change between the
pin and the placement commit `9e6b04645`, so the manuscript's statements about
Parts III–VII refer to the text printed here. The manuscript, its PDF and its
delivery README are not shipped; they survive in the arrival commit
`1512ef835`. Its two `SHA256SUMS` ledgers were verified at placement (15/15
and 8/8) and retired. Part VIII prints every result, proof, remark, limitation
and question of the manuscript. Its first cases are Part IV's profile
(`p = 2`) and Part VII's two theorems (`p = 3`, `r = 2`), which stay in their
Parts and are cited as such (Remark 91.3); the Catalan, endpoint, parser and
word-mass interfaces it recalls from Part VII are printed there and cited by
label (Section 92); its word bounds are Parts VI–VII's with a new moment bound
(Lemma 93.1). The new content is the endpoint-prefix count and its mass
`2^(p−2)(p + 1)`, the amplitudes for `p ≥ 4`, the windows for `r ≥ 3`,
`I_4(1/3) = 8 sqrt(2) π`, and the conditioned piece, channel and mixture laws.
Section 99.5 lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The exact
certificates and finite checks verify finite algebraic statements; they are
not a proof of the all-`m`, all-`n` or asymptotic theorems. Part IV's Monte
Carlo table and figure are illustrations only. Part V's theorems apply the
abstract transfer theorems it proves to three results of Parts III and IV, so
they have exactly the status of those parts; its printed decimals are
high-precision numerics, not interval certificates. Part VI's theorems are
two-sided orders (`Θ`, `≍`), not equivalents, and are proved without any
asymptotic theorem of Parts I–V; its exact counts through `n = 128` are
regression checks, not evidence for the orders. Part VII's theorems are
limits and equivalents with no finite-size error rate; they re-derive every
finite interface they use and assume no asymptotic theorem of Parts I–VI,
and its finite checks are regression checks. Part VIII's theorems are fixed-index
equivalents and limits, with no error rate and no uniformity as the index
grows; its finite table (`n ≤ 192`) is still far from the one-third limit and
is a regression check.

## Results

Let `a_n^(m)` count the 132-avoiding permutations of `{1,…,n}` with every
adjacent absolute difference at most `m`, and let `alpha_m` be their exponential
growth constant (`n → ∞` with `m` fixed). Logarithms are natural.

**Part I** (unchanged apart from dated pointers) proves:

1. `alpha_(m+1) > alpha_m` for every integer `m ≥ 1`. More strongly, both
   irreducible component growth rates increase strictly for `m ≥ 2`
   (Theorem 1.1). This completes the remaining strict-inequality part of
   Nadler's Conjecture 2, using the endpoint system introduced by Mayama and
   Akita; the report includes proofs of its finite-state prerequisites.
2. `4 - alpha_m = (2 log m + 4 log log m + O(1))/m` (Theorem 1.2), by a separate
   counting and analytic proof.
3. For `E_m = m(4 - alpha_m) - 2 log m - 4 log log m`,
   `2 log π - 4 log 2 ≤ liminf E_m ≤ limsup E_m ≤ 2 log π` (Theorem 1.3).

**Part II** (manuscript 04). Let `r_m` be the positive root of
`sum_{k=1}^m C_(k-1) r^k = 1` and `beta_m = 1/r_m`. It proves:

1. `alpha_m < beta_m < 4` for every `m ≥ 2` (Theorem 10.1), by a
   Catalan-weighted positive vector on the last endpoint threshold
   (Lemma 12.2) that absorbs the append transition through the Catalan
   renewal identity. This is strictly sharper than Part I's scalar majorant.
2. `0 ≤ beta_m - alpha_m ≤ beta_m - lambda_U(m) = O((log m)^2/m^2)`
   (Theorem 10.2), from a uniform first-deficiency tail bound (Lemma 13.2)
   and a cutoff `d = ⌈log_2 m⌉` growing with `m` (Theorem 15.2).
3. **`E_m → 2 log π`** (Corollary 15.3): the window of Part I's Theorem 1.3
   closes at its upper endpoint. Part II sharpens Part I; it refutes nothing.
4. An expansion of `m(4 - alpha_m)` to every inverse-logarithmic order, with
   an explicit triangular recursion for the correction polynomials and the
   first four printed and symbolically checked (Theorem 10.3,
   Proposition 16.1, equations (77) and (79)).
5. `(lambda_V(m) - lambda_U(m))_+ = O((log m)^2/m^2)` (Corollary 15.4): a
   one-sided constraint on the component competition.

**Part III** (manuscript 02 of batch 43). Let `M_n` be the largest absolute
difference between adjacent entries of a uniform 132-avoider of size `n`, and
`D_n = n - M_n`, so that `a_n^(m)/C_n = P(D_n ≥ n - m)`. With
`s = sqrt(1 - z)` and `r = sqrt((1 + s)/2)` it proves:

1. `D_n` converges in total variation to a positive integer law `D` with
   probability generating function
   `G(z) = (1 - s)(4 + 8s + 3s^2 - s^2 r) / (4(1 + 2s)(1 + s)^2)`, at the sharp
   rate `Θ(n^(-1/2))`, with an explicit bound for `n ≥ 8` and
   `3/sqrt(π) ≤ liminf, limsup of sqrt(n)·d_TV ≤ 4 sqrt(2)/sqrt(π)`
   (Theorem 22.1, Corollary 28.2).
2. `P(D = 1) = 7/48`, median 9, `P(D > k) = 3/sqrt(π k) + O(k^(-3/2))`, with
   second-order terms (Proposition 28.1); finite moments exactly of order
   `p < 1/2`; quantiles `~ 9/(π ε^2)` (Corollary 28.3).
3. **The boundary joint limit.** For fixed `d`,
   `a_n^(n-d)/C_n → P(D ≥ d)`, an explicit rational (41/48 at `d = 2`).
   Uniformly for `n ≥ 8` and `2 ≤ d ≤ n - 1`,
   `a_n^(n-d)/C_n = 3/sqrt(π d) + O(d^(-3/2) + n^(-1/2))` with an absolute
   constant; hence `a_n^(n-d)/C_n ~ 3/sqrt(π d)` and
   `a_n^(n-d) ~ (3/π) 4^n/(n^(3/2) sqrt(d))` whenever `d → ∞`, `d = o(n)`
   (Theorem 22.2, Section 29).
4. A moment transition: `E D_n^p → E D^p` for `p < 1/2`,
   `E sqrt(D_n) = (3/(2 sqrt(π))) log n + O(1)`, `E D_n^p = Θ(n^(p - 1/2))` for
   `p > 1/2`; so `E M_n = n - Θ(sqrt(n))` and `Var D_n = Θ(n^(3/2))`
   (Theorem 22.3, Corollary 30.1).
5. An exact count `#{M = n - 1} = C_(n-2) + sum_(j ≤ n-2) C_j` for `n ≥ 3`
   (Proposition 31.1), an algebraic certificate of degree at most four
   (Section 35), and ten research questions (Section 32).

This answers Part II's research direction "Joint growth of length and
adjacency bound" (Section 19.5) and this README's former "no joint limit in
`n` and `m`" **only in the boundary regime** `m = n − d`, `d = o(n)`; see
below. The proof is a finite absorbing "skeleton" decomposition with one large
unexpanded block, compared with the uniform measure by exact counting
domination; it uses standard singularity analysis and no random-tree limit
theorem as a black box.

**Part IV** (manuscripts 10 and 11 of batch 52, merged). With `D_n = n − M_n`
as in Part III and `Ψ(u) = (3/sqrt(π)) (1 − 2u)/sqrt(u(1 − u))` for
`0 < u < 1/2`, `Ψ(u) = 0` for `1/2 ≤ u ≤ 1`, it proves:

1. **The bulk profile** (both manuscripts, two different proofs):
   `sqrt(n) P(D_n > un) → Ψ(u)` for every `0 < u ≤ 1`, uniformly on
   `[δ, 1]`, and `sqrt(n) P(D_n ≥ d_n) → Ψ(u)` whenever `d_n/n → u ∈ (0, 1)`
   (Theorem 38.1). Hence, for fixed `1/2 < θ < 1`,
   `a_n^(⌊θn⌋)/C_n ~ 3(2θ − 1)/sqrt(π θ(1 − θ)) · n^(-1/2)` and
   `a_n^(⌊θn⌋) ~ 3(2θ − 1)/(π sqrt(θ(1 − θ))) · 4^n/n^2`; for `0 < θ ≤ 1/2`
   the ratio is `o(n^(-1/2))`. As `u → 0`, `Ψ(u) sqrt(u) → 3/sqrt(π)`, matching
   Part III's boundary tail `3/sqrt(π d)`; `Ψ(1/2 − ε) ~ 12ε/sqrt(π)`
   (Section 43.1).
2. **Rare-event measures.** `sqrt(n)·Law(D_n/n, L_n/n)` (with `L_n` the last
   entry) converges vaguely to an explicit measure with three equally
   weighted last-entry channels, and `sqrt(n)·Law(D_n/n)` to the density
   `(3/(2 sqrt(π))) [x(1 − x)]^(-3/2)` on `(0, 1/2)` (Theorem 38.2; the
   marked form is manuscript 10's, the deficit marginal both).
3. **Every supercritical moment** (both): for fixed `p > 1/2`,
   `E D_n^p ~ 𝔪_p n^(p − 1/2)` with
   `𝔪_p = (3/sqrt(π)) ∫_0^1 (z^2/(1 + z^2))^(p − 1) dz` (the manuscripts'
   `κ_p`); so `E D_n ~ 3 sqrt(n/π)` and
   `Var D_n ~ 3(4 − π)/(4 sqrt(π)) n^(3/2)` (Theorem 38.3), with closed forms
   at `p = 3/2, 2, 3, 4`, a recurrence, and `𝔪_p ~ 3/(sqrt(π)(2p − 1))` as
   `p ↓ 1/2`, `𝔪_p ~ 6·2^(-p)/(sqrt(π) p)` as `p → ∞` (Section 44).
4. Under deficit-size bias, `sqrt(D_n/(n − D_n))` converges to
   Uniform[0, 1]; half of the leading mean comes from deficits above `n/5`
   (Theorem 38.4, manuscript 10).
5. Conditionally on `M_n ≤ n − d_n` with `d_n/n → u < 1/2`, the canonical
   outer word and the terminal split converge jointly to an independent pair
   with a universal word law (mean length 7/3, infinite mean cost) and split
   density `∝ [y(1 − y)]^(-3/2)` on `[u, 1 − u]`, and `D_n/n` is the smaller
   macroscopic block (Theorem 43.2, Corollary 43.3, Proposition 43.4,
   manuscript 11); manuscript 10's Corollary 43.1 gives the conditional
   three-channel law of `(D_n/n, L_n/n)`.
6. Polynomial lower bounds below half size:
   `P(M_n ≤ ⌊θn⌋) ≥ c n^(-r/2)` whenever `(r + 1)θ > 1` (Theorem 45.1,
   manuscript 10). [30 September 2026, batch 68: Part VI proves the matching
   upper bounds; see below.]
7. Exact counts of `a_n^(n-d)` up to `n = 320` and exact moments for
   `n = 20, 40, 80` (manuscript 11), a uniform Catalan sampler with 675,000
   labelled Monte Carlo samples (manuscript 10), and thirteen research
   questions (Section 47).

This answers Part III's Section 32.1 completely and Section 32.2 for
`p > 1/2` (the critical centered half-moment stays open), and Part II's
research direction "Joint growth of length and adjacency bound" for
`1/2 < m/n < 1`. It shows that the equivalent `3/sqrt(π(1 − θ)n)` which
Part III declined to assert (Remark 29.3) is false for every `0 < θ < 1`.
[30 September 2026, batch 64: the critical centered half-moment is answered
by Part V.]

**Part V** (manuscript 06 of batch 64). From three results of Parts III and
IV — the limiting law with `P(D > x) = (3/sqrt(π)) x^(-1/2) + O(x^(-3/2))`,
the uniform bound `sup_x |P(D_n > x) − P(D > x)| = O(n^(-1/2))` implied by
Part III's total-variation theorem, and Part IV's pointwise profile `Ψ` — it
proves:

1. **The centered half-moment converges** (Theorem 53.1):
   `E sqrt(D_n) = (3/(2 sqrt(π))) log n + c_⋆ + o(1)`, where
   `c_⋆ = c_mic + c_mac`, `c_mic = 1 + (1/2) ∫_1^∞ x^(-1/2) (P(D > x) − (3/sqrt(π)) x^(-1/2)) dx`
   (microscopic) and `c_mac = (3/sqrt(π)) (log 2 − log(1 + sqrt(2)) + sqrt(2) − 2)`
   (macroscopic); numerically `c_⋆ ≈ −0.942121413999402`,
   `c_mic ≈ 0.367948538497933`, `c_mac ≈ −1.310069952497335`. A Laplace
   integral of `1 − G(e^(-t))` gives `c_mic` without truncation
   (Proposition 60.1).
2. **Every subcritical moment has an explicit first correction** (Theorem 53.2):
   for fixed `0 < p < 1/2`, `E D_n^p = E D^p + 𝔪(p) n^(p − 1/2) + o(n^(p − 1/2))`,
   where `𝔪(p) = (3/(2 sqrt(π))) B_{1/2}(p − 1/2, −1/2)` is a regularized
   incomplete beta function and `𝔪(p) < 0`; e.g. `𝔪(1/4) ≈ −2.5755`. For
   `p > 1/2` the same function is Part IV's constant, `𝔪(p) = 𝔪_p`
   (Remark 55.3), and its finite part at the pole `p = 1/2` is
   `B_1 = 3/sqrt(π) + c_mac ≈ 0.382498798`.
3. **A two-term crossover** (Theorem 53.3): for `p = 1/2 + λ/log n`,
   `E D_n^p = (3/(2 sqrt(π))) log n · (e^λ − 1)/λ + B_0 + B_1 e^λ + o(1)`
   locally uniformly in complex `λ`, with `B_0 = c_mic − 3/sqrt(π) ≈ −1.3246`.
4. **Every logarithmic scale contributes** (Theorem 53.4): under the
   `sqrt(D_n)`-weighted measure, `log D_n/log n` tends to Uniform[0, 1], and
   the weighted measure minus `(3/(2 sqrt(π))) log n` times Lebesgue measure
   converges to `B_0 δ_0 + B_1 δ_1` in the dual bounded-Lipschitz norm; tilted
   laws and all logarithm-weighted critical moments follow (Section 58).
5. **An abstract transfer theory** (Sections 54–59) for any `X_n` in `[1, n]`
   with a power tail, a uniform `O(n^(-α))` survival error and a pointwise
   profile; a counterexample (Proposition 59.1) shows the uniform error cannot
   be dropped, and a stability theorem (Proposition 59.2) allows
   `o(n^(-α))` perturbations.
6. Exact distributions of `D_n` for `n ≤ 64`, finite checks, and ten research
   questions (Section 63).

This answers Part IV's Section 47.6 (both questions) and the critical half of
Part III's Section 32.2, and sharpens Part III's `E sqrt(D_n) = … + O(1)` and
`E D_n^p = E D^p + O(n^(p − 1/2))` (Theorem 22.3).

**Part VI** (manuscript 05 of batch 68). With `p_n(m) = P(M_n ≤ m) =
a_n^(m)/C_n`, `f ≍ g` meaning bounded ratios in both directions (not ratio
convergence) and `(x)_+ = max(x, 0)`, it proves:

1. **The staircase** (Theorem 68.1): for every fixed `0 < θ < 1`,
   `p_n(⌊θn⌋) = Θ(n^(-⌊1/θ⌋/2))` and `a_n^(⌊θn⌋) = Θ(4^n n^(-(⌊1/θ⌋+3)/2))`,
   uniformly on compact subintervals of each phase
   `1/(r + 1) < θ ≤ 1/r`; at `θ = 1/q` the exponent is `q/2`, not `(q − 1)/2`.
   So the logarithmic rarity exponent is `⌊1/θ⌋/2`: `1/2` above half size,
   `1` on `(1/3, 1/2]`, `3/2` on `(1/4, 1/3]`, and so on (Table 25, Figure 14).
2. **The reciprocal thresholds** (Theorem 68.2, Corollary 68.3): for fixed
   `q ≥ 2`, uniformly for `m/n` in a fixed interval inside
   `(1/(q + 1), 1/(q − 1))` around `1/q`,
   `p_n(m) ≍ n^(-q/2) + n^(-3(q−1)/2) (qm − n)_+^(q−1)`, so the order changes
   on the scale `n^(1 − 1/(2(q−1)))`: `sqrt(n)` at `n/2`, `n^(3/4)` at `n/3`,
   `n^(5/6)` at `n/4`.
3. **Half size** (Corollary 68.4): `p_n(⌊n/2⌋) = Θ(1/n)` and
   `p_n(⌊n/2 + t sqrt(n)⌋) ≍ (1 + t_+)/n` for bounded `t`; no limit of
   `n p_n` is asserted.
4. A continuum of logarithmic exponents in shrinking neighbourhoods:
   `p_n(⌊n/q + c n^β⌋) = Θ(n^(-min(q/2, (q−1)(3/2 − β))))` (Corollary 71.2).
5. **A local theorem for truncated subcritical renewals** (Theorem 70.1):
   for weights `w_k` with total mass `< 1` and `w_k` between two multiples of
   `k^(-1-α)`, `0 < α < 1`, the coefficients of `1/(1 − sum_(k ≤ m) w_k z^k)`
   satisfy `u_m(n) ≍ n^(-1-(q+1)α) + n^(-q(1+α)) (qm − n)_+^(q−1)` uniformly
   for `m/n` in a fixed interval inside `(1/(q + 1), 1/(q − 1))`; and a
   transfer principle for any class sandwiched between two such renewals
   (Proposition 72.1). Part I's two scalar envelopes (Propositions 5.1 and
   5.2 at `d = 1`), normalized at `x = 1/4`, are such renewals with `α = 1/2`
   and masses `3/4` and `3/8`.
6. Exact counts for 20 fixed-fraction and 18 crossover samples through
   `n = 128` (Table 26, Figure 15), finite checks, and ten research questions
   (Section 74).

This answers the exponent part of Part IV's Section 47.1 (the amplitudes
`Ω_r(θ)` stay open) and, at the level of orders, Part IV's Section 47.2 and
Part V's Section 63.3 (the limiting transition functions stay open). It
re-derives Part IV's lower bounds (Theorem 45.1) and adds the matching upper
bounds; for `θ > 1/2` it gives only the order `n^(-1/2)`, weaker than Part IV's
equivalent. Part VI writes `r = ⌊1/θ⌋`; Part IV's question writes
`r = ⌈1/θ⌉ − 1`; the two agree unless `1/θ` is an integer, where the first is
`q` and the second `q − 1`. [1 October 2026, batch 71: Part VII proves, at
`q = 2` and `r = 2`, the limiting transition function, the endpoint constant
and the amplitude that this paragraph and item 3 leave open; see below.] [1 October 2026, batch 72: Part VIII proves them for every fixed
index; see below.]

**Part VII** (manuscript 03 of batch 71). With `p_n(m)` as for Part VI and
`I_3(θ) = ∬ (xyz)^(-3/2) dx dy` over `x + y + z = 1`, `0 < x, y, z ≤ θ`
(coordinate measure `dx dy`, `z = 1 − x − y`), it proves:

1. **The half-size crossover** (Theorem 80.1): for every `B < ∞`,
   `sup_(|t| ≤ B) |n p_n(⌊n/2 + t sqrt(n)⌋) − 6 − (12/sqrt(π)) t_+| → 0`; in
   particular `p_n(⌊n/2⌋) ~ 6/n`, along all `n`, odd and even.
2. **The first sub-half-size equivalent** (Theorem 80.2): for
   `1/3 < θ ≤ 1/2`, `p_n(⌊θn⌋) ~ I_3(θ)/(2πn)`, uniformly on compact
   subintervals of `(1/3, 1/2)`; `I_3` is finite and positive and
   `I_3(1/2) = 12π` (Section 87).
3. The ingredients: uniform endpoint estimates for a uniform avoiding block
   (Lemma 81.1); the canonical threshold parser for **every** bound `m < n`
   (Lemma 82.1; Part IV's parser needed `m ≥ n/2`); small-word estimates
   (Lemma 83.1); the two-piece ramp, of mass `3` (Section 84); the exact
   three-piece endpoint table (equation (371)) and its mass (372)
   `𝒲_R(1/4)² + 𝒲(1/4)𝒲_A(1/4)/2 = 4 + 4 = 8`; and the exclusion of every
   other parser family at the scale `1/n` (Section 86).
4. Finite regression checks (Table 28): `n p_n(⌊n/2⌋)` = 4.6298, 4.8690,
   5.0163, 5.1947, 5.3026 at `n` = 64, 96, 128, 192, 256, rising slowly
   towards 6; and four further questions (Section 89).

So Part VI's crossover question 74.3 is answered at `q = 2`: its candidate
`𝔎_q + 𝔏_q t_+^(q−1)` holds with `𝔎_2 = 6` and `𝔏_2 = 12/sqrt(π)`, the slope
Part VI said matching "would suggest", here proved directly. Its question
74.2 is answered at `q = 2` (`𝔎_2 = 6`, no residue-class oscillation in the
limit), and 74.1 at `r = 2` (`Ω_2(θ) = I_3(θ)/(2π)` for `1/3 < θ < 1/2`).
Part IV's 47.2 and Part V's 63.3 now have their transition function on the
scale `sqrt(n)`; Part IV's 47.1 is answered for `1/3 < θ < 1/2` only. [1 October 2026, batch 72: and for every fixed `θ ≤ 1/2` by Part VIII.]
Theorem 80.1 sharpens Part VI's Corollary 68.4 from an order to a limit, and
Theorem 80.2 its Theorem 68.1 from an order to an equivalent for
`1/3 < θ ≤ 1/2`. The ramp slope is the slope `12/sqrt(π)` of Part IV's
profile at its upper end (equation (222)), and `I_3(θ) → 0` as `θ ↓ 1/3`, in
agreement with the jump of the staircase exponent there. Nothing earlier is
refuted.

**Part VIII** (manuscript 41 of batch 72). With `p_n(m)` as for Part VI,
`I_p(θ) = ∫ ∏ x_i^(-3/2) dx_1 … dx_(p−1)` over `x_1 + … + x_p = 1`,
`0 < x_i ≤ θ` (coordinate measure; `I_3` is Part VII's), and
`ϰ_p = (p + 1)/(2^p π^((p−1)/2))`, it proves:

1. **Every fixed phase amplitude** (Theorem 91.1): for fixed `p ≥ 2` and
   `1/p < θ < 1/(p − 1)`, `p_n(⌊θn⌋) ~ ϰ_p I_p(θ) n^(-(p−1)/2)`, uniformly on
   compact subintervals, and for `p ≥ 3` also at `θ = 1/(p − 1)`. So Part VI's
   amplitude is `Ω_r(θ) = ϰ_(r+1) I_(r+1)(θ)` (the index shifts by one), and
   every fixed `0 < θ < 1` now has an equivalent.
2. **Every fixed reciprocal crossover** (Theorem 91.2): for fixed `r ≥ 2`,
   locally uniformly in `t`,
   `n^(r/2) p_n(⌊n/r + t n^(1 − 1/(2(r−1)))⌋) → 𝔎_r + 𝔏_r t_+^(r−1)`, with
   `𝔎_r = ϰ_(r+1) I_(r+1)(1/r)` and
   `𝔏_r = (r + 1) r^(5r/2 − 1)/(2^r π^((r−1)/2) (r − 1)!)`.
3. **The one-third window** (Corollary 97.1): `I_4(1/3) = 8 sqrt(2) π`, so
   `n^(3/2) p_n(⌊n/3 + t n^(3/4)⌋) → 5/sqrt(2π) + (729 sqrt(3)/(4π)) t_+^2`.
4. **Conditioned geometry** (Corollaries 98.1 and 98.2): in a fixed phase the
   ordered macroscopic piece vector of the canonical parser has the limit
   density `I_p(θ)^(-1) ∏ x_i^(-3/2)` on the capped simplex, independent of an
   endpoint/gap channel uniform over `p + 1` values, with independent gap words
   of probability `4^(-|w|)/2`; in the window at `1/r` the `r`-piece family has
   weight `𝔏_r t^(r−1)/(𝔎_r + 𝔏_r t^(r−1))` and Dirichlet(1, …, 1) deficits.
5. The ingredients: the endpoint-prefix count (equation (389)) with accepted
   mass `2^(p−2)(p + 1)` (3 at `p = 2`, Part IV's; 8 at `p = 3`, Part VII's);
   word bounds with a fixed gap count and all moment orders (Lemma 93.1);
   family bounds for many pieces and microscopic terminal children; the
   shrinking near-cap simplex; and a finite table (Table 30):
   `n^(3/2) p_n(n/3)` = 3.4611, 3.4549, 3.4191, 3.3353, 3.2588 at `n` = 48,
   72, 96, 144, 192, far above the limit 1.9947.

So Part VII's questions 89.1, 89.2 and 89.4 and Part VI's 74.1–74.3 are
answered for every fixed index, Part VI's 74.4 at the level of the parser's
pieces (not the positions of the blocks or of the largest jump), and Part IV's
47.1 completely (an equivalent for every fixed `0 < θ ≤ 1/2`, and above one
half Part IV's own); every `θ = 1/q` carries a window in the strong sense.
Part VII's two theorems are the cases `p = 3`, `r = 2`, and Part IV's profile
the case `p = 2`; they are printed once, in their Parts (Remark 91.3). The
slope `𝔏_r` is the lower-edge expansion of the `r`-piece amplitude
(Remark 91.4), a consistency check. `𝔎_4 = ϰ_5 I_5(1/4) ≈ 0.6770` is a
numerical value computed for this write-up (Section 97). Nothing earlier is
refuted.

## Not claimed

- The all-`m` component ordering (`V` dominates `U` for every `m ≥ 5`,
  Problem P3 of Mayama–Akita) is not proved, in either part. Part I certifies
  it only for `m = 2..20`; Part II bounds only a dominant `V`'s lead, and does
  not bound `|lambda_V - lambda_U|` when `V` is below `U`.
- No asymptotic equivalent, or optimal order, of the scalar defect
  `beta_m - alpha_m`; no joint limit in `n` and `m`; no minimal recurrence order,
  uniform denominator factorization, simple-pole statement or state
  minimization of `A_m(x)`.
  [29 September 2026, batch 43: the joint limit is now proved in the boundary
  regime only, by Part III: `m = n − d` with `d` fixed (an explicit rational
  limit) or `d → ∞`, `d = o(n)` (the equivalent `3/sqrt(π d)`). Every other
  item of this bullet stands.]
  [29 September 2026, batch 52: Part IV adds the bulk regime
  `m = ⌊θn⌋`, `1/2 < θ < 1`, to first order; see the next bullet.]
- **Part III alone does not give a bulk joint limit; Part IV gives it for
  `n − m` linear in `n` with `m/n > 1/2`:**
  `sqrt(n) P(D_n > un) → (3/sqrt(π)) (1 − 2u)/sqrt(u(1 − u))`, `u < 1/2`
  (Theorem 38.1). When `n − m` is a fixed fraction of `n`, Part III's additive
  error `O(n^(-1/2))` is as large as its main term, and Part III explicitly
  does **not** assert `a_n^(⌊θn⌋)/C_n ~ 3/sqrt(π(1−θ)n)` (Remark 29.3). Part IV
  shows that formula is false: the true equivalent is
  `3(2θ − 1)/sqrt(π θ(1 − θ)) · n^(-1/2)` for `1/2 < θ < 1`, and the ratio is
  `o(n^(-1/2))` for `θ ≤ 1/2`. [Corrected 29 September 2026, batch 52; the
  bullet read "**Part III does not give a bulk joint limit.**", and the bulk
  profile `Ψ(u)` of Section 32.1 was a proposed problem.] [30 September 2026,
  batch 68: for `θ ≤ 1/2` Part VI proves the exact order
  `Θ(n^(-⌊1/θ⌋/2))` (Theorem 68.1), but no equivalent.] [1 October 2026,
  batch 71: for `1/3 < θ ≤ 1/2` Part VII proves the equivalent
  `I_3(θ)/(2πn)` (Theorem 80.2); for `θ ≤ 1/3` there is still none.]
  [1 October 2026, batch 72: Part VIII proves it for every fixed `θ ≤ 1/3`
  (Theorem 91.1).] Nothing interpolates
  between the fixed-`m` spectral regime of Parts I–II and the boundary or
  bulk regimes (Sections 32.10 and 47.10).
- Part III does not claim exact leading constants for `E D_n` or the
  supercritical moments (only two-sided orders), convergence of
  `E sqrt(D_n) − (3/(2 sqrt(π))) log n`, the exact total-variation constant,
  a minimal `n` from which `D_n` has median 9, minimal algebraic degree four or
  irreducibility of the eliminated polynomial, or anything about the
  fixed-`m` component ordering. [29 September 2026, batch 52: Part IV proves
  the exact supercritical constants (Theorem 38.3); every other item stands.]
  [30 September 2026, batch 64: Part V proves the convergence of
  `E sqrt(D_n) − (3/(2 sqrt(π))) log n`, to `c_⋆ ≈ −0.9421` (Theorem 53.1).]
- **Part IV does not claim** an asymptotic equivalent for
  `a_n^(⌊θn⌋)/C_n` when `0 < θ ≤ 1/2` (only `o(n^(-1/2))` and polynomial
  lower bounds; the conjectured hierarchy `P(M_n ≤ θn) ~ Ω_r(θ) n^(-r/2)` is a
  question), the order or window at `m = n/2`, a local limit for individual
  lattice masses `P(D_n = ⌊xn⌋)`, the exact total-variation constant (the
  value `3 sqrt(2)/sqrt(π)` is only a suggested contribution), convergence of
  the centered half-moment or corrections to `E D_n^p` for `p < 1/2`,
  second-order terms of any moment, a relative error uniform from the
  boundary to the bulk, a full conditioned-permutation limit (position of the
  largest jump, joint largest ascent and descent), finite-`n` convergence of
  word-cost expectations, anything about the fixed-`m` component ordering, or
  any new Lean or Rocq declaration. The identification of manuscript 10's three
  channels with manuscript 11's three modes (Section 43.4) is the merge's
  reading, not a proved joint limit. [30 September 2026, batch 64: Part V
  proves the convergence of the centered half-moment and the first correction
  to `E D_n^p` for `0 < p < 1/2` (Theorems 53.1 and 53.2); every other item
  stands.] [30 September 2026, batch 68: Part VI proves the exponents of the
  hierarchy, `P(M_n ≤ ⌊θn⌋) = Θ(n^(-⌊1/θ⌋/2))` for every `0 < θ < 1`, and the
  order `n^(-1)` and order-crossover scale `sqrt(n)` at `m = n/2`
  (Theorem 68.1, Corollary 68.4); the equivalents, the amplitudes `Ω_r(θ)`
  and a limiting transition function at `m = n/2` stay unproved, and every
  other item stands.] [1 October 2026, batch 71: Part VII proves the
  equivalent for `1/3 < θ ≤ 1/2` (so `Ω_2(θ) = I_3(θ)/(2π)`) and the
  transition function `6 + 12 t_+/sqrt(π)` at `m = n/2` on the scale
  `sqrt(n)` (Theorems 80.1 and 80.2); equivalents for `θ ≤ 1/3` stay
  unproved.] [1 October 2026, batch 72: Part VIII proves them, the
  amplitudes `Ω_r(θ)` and the transition function at every `m = n/q`
  (Theorems 91.1 and 91.2).]
- **Part V does not claim** a local limit for individual lattice masses, the
  exact total-variation constant, the transition at `m = n/2`, a rate for the
  centered half-moment, any correction theorem for `p ≤ 0` (the coefficient
  `𝔪(p)` is continued analytically below `1/2`, but a continued coefficient
  does not continue an asymptotic theorem), an `o(1)`-accurate second-order
  constant for fixed supercritical `p`, uniformity in the exponent window as
  `|λ| → ∞`, total-variation convergence of the discrete biased laws to their
  continuous limit, a positive-measure meaning of the negative endpoint
  coefficient `B_0`, an elementary closed form, rationality or transcendence
  of `c_mic`, or a certified decimal enclosure of any constant. Its
  permutation theorems are exactly as reliable as the three inputs from
  Parts III and IV; its abstract theorems do not depend on them.
  [30 September 2026, batch 68: the transition at `m = n/2` is described at
  the level of orders by Part VI (Corollary 68.4).] [1 October 2026,
  batch 71: and its limiting function by Part VII (Theorem 80.1).]
- **Part VI does not claim** an asymptotic equivalent, an amplitude or any
  constant: its results are two-sided orders, and the normalized sequences are
  only shown to be bounded above and away from zero. In particular it does not
  claim the existence or value of `Ω_r(θ)`, of the endpoint constants
  `𝔎_q = lim n^(q/2) p_n(⌊n/q⌋)` (lattice oscillations are not excluded), or
  of limiting crossover functions `ℌ_q(t)` (the candidate `𝔎_q + 𝔏_q t_+^(q−1)`
  is a hypothesis), and its "order-crossover scale" is not a window in the
  sense of a rescaled limit; `(log p_n)/log n → −⌊1/θ⌋/2` is a pointwise
  law, not a large-deviation principle. It claims no description of the
  conditioned permutation (its large parts are marked in two auxiliary
  renewal encodings, not in the permutation), no uniformity as `q → ∞` (so no
  bridge to `m = o(n)` or to fixed `m`), nothing for tail index `α = 1` or
  critical mass `1` (where its tail lemma fails), nothing about the fixed-`m`
  component ordering, effective constants, or any Lean or Rocq declaration.
  For `θ > 1/2` it is weaker than Part IV's equivalent, which it does not use.
  Its lower bounds and its two envelopes are Part IV's and Part I's, credited,
  and its transfer principle (Proposition 72.1) requires cutoff-respecting
  encodings that a generic Catalan class need not have. [1 October 2026,
  batch 71: Part VII proves `Ω_2(θ)` for `1/3 < θ < 1/2`, `𝔎_2 = 6` and
  `ℌ_2(t) = 6 + 12 t_+/sqrt(π)`, the candidate with `𝔏_2 = 12/sqrt(π)`;
  every other item of this bullet stands.] [1 October 2026, batch 72: Part VIII proves
  `Ω_r(θ)`, `𝔎_q` and `ℌ_q` for every fixed index (the candidate form, with
  `𝔏_q` of equation (380)) and the conditioned law of the parser's pieces;
  the positions of the blocks and of the largest jump, uniformity in `q`,
  rates and the other items stand.]
- **Part VII does not claim** any finite-size error rate or explicit error
  term (Section 88.1; its delivery README's "explicit error bounds" is not
  borne out by the text, see "Discrepancies"), uniformity of Theorem 80.2 up
  to `θ = 1/3` or as `θ ↑ 1/2` beyond the stated compact subintervals and
  the endpoint, anything for `θ ≤ 1/3` (the amplitudes `Ω_r(θ)` for `r ≥ 3`
  and the endpoint constants `𝔎_q` for `q ≥ 3`), crossover functions at
  `1/q` for `q ≥ 3`, or a limit law for the conditioned permutation (its
  three-piece endpoint table identifies the leading parser families, not a
  conditioned limit); nothing about the fixed-`m` regime or the component
  ordering, and no Lean or Rocq declaration. Its finite table is a
  regression check, not evidence of convergence. Its endpoint estimates, the
  parser above half size, the word masses and the small-word lemmas are
  those of Parts IV and VI, re-derived and credited; no exhaustive priority
  is claimed. One step of its proof, the bound `4(1/2)^j` after Lemma 83.1,
  is terse as delivered and is justified in the editorial Remark 83.3. [1 October 2026, batch 72: Part VIII proves the
  amplitudes for `θ ≤ 1/3`, the constants `𝔎_q` and crossover functions for
  `q ≥ 3` and the conditioned three-piece law (Theorems 91.1 and 91.2,
  Corollary 98.1); the rest of this bullet stands.]
- **Part VIII does not claim** any effective convergence rate or error term,
  uniformity as the index `p` or `r` grows, a bridge to `m = o(n)` or to the
  fixed-`m` spectral regime, a description of the whole conditioned
  permutation (the positions and values of the macroscopic blocks and the
  location of the largest jump: Part VI's 74.4 is answered only for the
  parser's pieces), closed forms of `I_p` for `p ≥ 5` or of `𝔎_r` for
  `r ≥ 4`, anything about the fixed-`m` component ordering, or any Lean or
  Rocq declaration. Its first cases are Part IV's and Part VII's theorems,
  which it re-proves without importing them; its interfaces are Part VII's and
  its word bounds Parts VI–VII's, credited. No worldwide priority is claimed
  (its ledger records limited targeted searches on 1 October 2026). Its
  finite table is a regression check (see the numerics item below). Its
  package's "exact finite endpoint-prefix checks" are a finite automaton check
  over gap masks for `p = 2..14`, not a check against permutations
  (Section 99.1). The step "a fixed constant times `(1/2)^j`" is unproved in
  the manuscript, as in Part VII; Part VII's Remark 83.3 supplies it.
- Part II's scalar polynomial is not a denominator of `A_m`,
  `det(I - W_V) ≠ 1 - K_m` in general, and the coefficientwise majorant
  `A_m ⪯ 1/(1 - K_m)` is **false** (at `m = 2`, `n = 3`: 5 against 3). The
  upper bound is spectral only (Remark 12.4, Section 18).
- The Perron test vector is a supersolution, not an approximation of the true
  eigenvector. A fixed truncation of the asymptotic expansion does not promise
  better numerical accuracy at any particular `m`.
- **The numerics are not evidence for the value `2 log π`.** At `m = 10^6`
  the computed corridor for `E_m` is about `[3.1495, 3.1503]`, 0.86 above the
  limit `2 log π ≈ 2.2895`, and its lower endpoint is not monotone (it peaks
  near 3.168 at `m = 73,920`). This agrees with the slow inverse-logarithmic
  corrections (the first, `(8z - 12)/log m`, is about 0.98 at `m = 10^6`), but no
  computation in the range distinguishes `2 log π` from nearby constants; the
  value rests on the proofs alone (Remark 17.1).
- Floating-point tables and all fifteen figures are illustrations, not interval
  certificates; only Part I's Perron certificates and Part II's Table 7 are
  rigorous (outward-rounded from exact fractions). Part III's probabilities
  are exact fractions (Table 12 shows rounded decimals of them); its finite
  checks (Section 31.3) support implementation correctness, not the
  asymptotic claims, and cross-cost injectivity rests on the proof of
  Lemma 25.2, not on testing. Part IV's Table 15 and the moment table of
  Section 46.5 are rounded displays of exact integer counts, which converge
  slowly (the first column of Table 15 is not even monotone); Table 16 and
  Figure 7 are pseudorandom Monte Carlo illustrations whose error bars
  measure sampling error, not finite-size bias; no constant of Part IV was
  fitted to data. Part V's constants (Table 20) are 40- and 70-digit
  quadratures that agree to more than 29 decimals, not enclosures; its
  Table 21 and Figures 12–13 are exact finite-`n` values for `n ≤ 64`, far
  from the limits (the biased mean scale even moves away from `1/2`), and
  Figure 11 plots the exact limiting densities; no constant of Part V was
  fitted to data. Part VI's Table 26 and Figure 15 are rounded displays of
  exact counts for `n ≤ 128`, whose scaled columns are not all monotone (the
  `θ = 1/3` column rises and falls) and are not claimed to converge; Figure 14 graphs the proved exponent, not data.
  [1 October 2026, batch 71: two of Table 26's columns now have proved
  limits, `6` at `θ = 1/2` and `I_3(2/5)/(2π) ≈ 0.4693` at `θ = 2/5`; the
  tabulated `θ = 2/5` values, 1.14–1.21, are about 2.5 times that limit.] [1 October 2026, batch 72: two more, `𝔎_3 = 5/sqrt(2π) ≈ 1.9947` at
  `θ = 1/3` and `𝔎_4 = ϰ_5 I_5(1/4) ≈ 0.677` at `θ = 1/4` (Part VIII); the
  tabulated values are 1.2–1.7 and 3.5–4.2 times these.]
  Part VII's Table 28 is a rounded display of exact counts for
  `n ≤ 256`, far from the limit `6` (5.30 at `n = 256`); no constant of
  Part VII was fitted to data. Part VIII's Table 30 is a rounded display of exact
  counts for `n ≤ 192`, 1.6–1.7 times its limit `5/sqrt(2π)`; three-term fits
  to these five values alone extrapolate to about 0.5 or to 2.3–2.6 depending
  on the correction ladder. A floating-point evaluation made for this write-up
  (an independent endpoint recurrence, to `n = 1050`, not shipped) gives
  1.995 ± 0.005 under the ladder `n^(-1/2), n^(-1), n^(-3/2)` and excludes a
  wrong channel mass (Section 99.1); that is numerical support, not proof. No
  constant of Part VIII was fitted to data.
- No priority. All literature checks were targeted (Part I on
  19 September 2026, Part II on 28 September 2026, Parts III and IV on
  29 September 2026, Parts V and VI on 30 September 2026, Parts VII and VIII
  on 1 October 2026: the arXiv v1 records
  of Nadler and of Mayama–Akita, for Parts VI–VIII also the record of
  Kerriou–Mörters (for Part VI also an author-hosted PDF) and, for Part VI,
  searches for truncated heavy-tail
  and fewest-big-jumps asymptotics, for Part VII searches for half-size
  thresholds and crossover functions, for Part VIII limited searches for
  the general cap-window formulas, for
  Part III also the records of two Janson papers, and for Parts III–VI
  targeted searches for largest adjacent differences in 132-avoiders; the
  Flajolet–Odlyzko PDF was not retrieved); none is an exhaustive novelty
  certification or external peer review.

## Labels

Part I's 65 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `tab:`,
`fig:`, `app:`) and are unchanged, with unchanged numbers (compared in the
`.aux` files of the committed and the new build). Part II added **93** labels,
all with the prefix `crem:` ("centered remainder"). Part III added **112**
labels, all with the prefix `lj:` ("largest jump"): the report has no single
prefix and `crem:` names Part II's subject, so Part III takes its own, as
Part II did; the manuscript's 102 labels were prefixed (its `thm:main`,
`app:algebra`, … would otherwise collide with Part I's bare labels) and the
merge added 10. Total after batch 43: 270. Part IV added **163** labels, all
with the prefix `mj:` ("macroscopic jump"), again its own prefix; five of them
were added to headings of Part III's research questions (Sections 32.1–32.4
and 32.6: `mj:sec:lj-bulk`, `mj:sec:lj-moments`, `mj:sec:lj-tv`,
`mj:sec:lj-ascent`, `mj:sec:lj-weighted`), which had no labels, so that
Part IV can cite them. Total: 433 (counted with the pattern
`\\label(\[[^]]*\])?\{`). No label was renamed or removed, and in the
batch-52 build every one of the 270 earlier labels keeps its number (compared
in the `.aux` files of the committed and the new build); the page numbers of
Parts I–III moved by two, because the contents grew to six pages, and Part I's
appendices now follow Part IV. Part II starts at
Section 10, Part III at Section 21 and Part IV at Section 37; tables and
figures continue Part I's numbering (Part II: Tables 4–10, Figures 3–4;
Part III: Tables 11–13, Figures 5–6; Part IV: Tables 14–17, Figures 7–10),
and equations are numbered consecutively through all parts. Part I's
appendices come after Part IV and contain no numbered equations, tables or
figures.

Part V added **116** labels, all with the prefix `cjm:` ("critical jump
moments"), its own prefix as for Parts II–IV. The manuscript's 102 labels were
prefixed (its `eq:h` and `sec:computation` would otherwise collide with
Part I's bare labels); the merge added eight to new headings, tables and a
remark of Part V, and six to the unlabelled headings of Part IV's research
questions 47.2, 47.4, 47.5, 47.7, 47.8 and 47.13 (`cjm:sec:mj-half`,
`cjm:sec:mj-local`, `cjm:sec:mj-tv`, `cjm:sec:mj-second`,
`cjm:sec:mj-geometric`, `cjm:sec:mj-formal`) so that Part V can cite them.
Total: **549**. No label was renamed or removed, and in the batch-64 build
every one of the 433 earlier labels keeps its number (compared in the `.aux`
files of the committed and the new build); their page numbers moved by two,
because the contents grew to eight pages. Part V is Sections 51–66,
Tables 18–21 and Figures 11–13, and comes before Part I's appendices.

Part VI added **102** labels, all with the prefix `pr:` ("polynomial
rarity"), its own prefix as for Parts II–V. The manuscript's 79 labels were
prefixed (its `eq:upper` and `lem:shift` would otherwise collide with Part I's
bare labels), except `eq:prior`, whose display is Part IV's equation (153)
and is cited instead of reprinted; that leaves 78. The merge added ten to new
headings and tables of Part VI, ten to the manuscript's unlabelled research
questions, and four to unlabelled question headings of Parts IV and V so that
Part VI can cite them: Part IV's 47.10 (`pr:sec:mj-bridge`) and Part V's
63.3, 63.7 and 63.10 (`pr:sec:cjm-half`, `pr:sec:cjm-other`,
`pr:sec:cjm-formal`). Total: **651**. No label was renamed or removed, and in
the batch-68 build every one of the 549 earlier labels keeps its number
(compared in the `.aux` files of the committed and the new build); their page
numbers moved by two, because the contents grew to ten pages, except eight
labels of Parts II, IV and V that moved by three and one of Part IV that
moved by one, where dated notes reflowed pages, and the three of Part I's
appendices, which moved by 28. Part VI is Sections 67–78,
Tables 23–26 (Part V's uncaptioned audit longtable in Section 65 consumes the
number 22) and Figures 14–15, and comes before Part I's appendices.

Part VII added **49** labels, all with the prefix `hc:` ("half-size
crossover"), its own prefix as for Parts II–VI (no `hc:` label existed
before). The manuscript's 25 labels were all bare generic names
(`thm:window`, `eq:8`, `eq:J`, `eq:L`, `sec:remainders`, …) and all 25 were
prefixed; the merge added 24, to new sections, subsections, the two tables
and the editorial Remark 83.3. No label was added to Parts I–VI. Total:
**700**. No label was renamed or removed, and in the batch-71 build every one
of the 651 earlier labels keeps its number (compared in the `.aux` files of
the committed and the new build); their page numbers moved by one, because
the contents grew by one page (the title page, which would otherwise have
spilled onto a second page, still has one; see "Build the article"), except
three labels of Part VI that moved by two, where dated notes reflowed pages,
and the three of Part I's appendices, which moved by 14. Part VII is Sections 79–89, Tables 27–28 and
equations (359)–(376); it has no figures, and comes before Part I's
appendices.

Part VIII added **53** labels, all with the prefix `gc:` ("general
crossovers"), its own prefix as for Parts II–VII (no `gc:` label existed
before). The manuscript's 29 labels were all bare generic names (`thm:phase`,
`eq:A`, `eq:many`, …): the 22 that name printed material were prefixed, and the
seven that name interfaces printed in Part VII (`eq:catalan`, `eq:first`,
`eq:last`, `eq:lastlimit`, `lem:parser`, `eq:wordmass`, `eq:partner`) are
replaced by Part VII's labels. The merge added 31, to new sections and
subsections, the two tables, the manuscript's unlabelled one-third corollary
and four merge remarks. No label was added to Parts I–VII. Total: **753**. No
label was renamed or removed, and in the batch-72 build every one of the 700
earlier labels keeps its number (compared in the `.aux` files of the committed
and the new build). Their page numbers moved by one, because the title page's
scope box now opens a second front page (see "Build the article"); where dated
notes reflowed pages, 33 labels of Part IV, 115 of Part V and 42 of Part VI
moved by two and 55 of Part VI and all 49 of Part VII by three; the three of
Part I's appendices moved by 17. Part VIII is Sections 90–100, Tables 29–30
and equations (377)–(393); it has no figures, and comes before Part I's
appendices.

## Notation

Part I's symbols keep their meanings, and the manuscript uses them the same
way (`alpha_m`, `E_m`, `C_k`, `c_(k,p)`, `U_m`, `V_m`, `lambda_U`, `K_(m,d)`,
`s_(m,d)`). Table 4 (Section 10.2) lists Part II's symbols. Watch in
particular for:

- `K_m` (one index) `= sum_{k≤m} C_(k-1) x^k` is **not** the block polynomial
  `K_(m,d)` (two indices); `K_(m-d)` is the Catalan polynomial truncated at
  `m - d`, and `K_(m,d) ⪯ K_(m-d)`. Part I's majorant is `R_m = x + K_m`.
- `r_m`, `beta_m`, `t_m = m log(4 r_m)` belong to `K_m`; they are not the
  component roots `r_U(m)`, `r_V(m)`, nor Part I's `t_m* = m log(4/alpha_m)`.
- `b_1 = 1/4` in Part II, `b_1 = 1/2` in Part I's Section 7 (the extra `x`).
- Renamed from the manuscript: `L → Λ = (1/2) log m` (Part I's `L_m` includes
  `log log m`), `P_j → 𝒫_j` (Part I's `P_3`, `P_4` are numerators),
  `B_N → ℬ_N`, `T_m → Δ_m`, the absolute constants `C, c → C_*, c_*`,
  `W_U, W_V → W_(U_m), W_(V_m)`, and the manuscript's `H = log m` is written out.
  No normalization changed.

Part III is self-contained; it shares only `a_n^(m)`, `C_n`, `Cat`,
`Av_n(132)`, `m` and `n` with Parts I–II. Table 11 (Section 21.2) lists its
symbols against their meanings in Parts I–II. Watch in particular for:

- `D_n`, `D` (the largest-jump deficit and its limit law) are not Part I's
  common denominator `D(x)`, its denominators `D_U`, `D_V`, or its constant
  `D`; `d` is a deficit threshold `m = n − d` (and an endpoint-state
  coordinate), not Part I's fixed cutoff or Part II's `d_m = ⌈log_2 m⌉`.
- `z` is a generating-function variable, not Part II's
  `z = log log m + (1/2) log π`; `q = (1 − sqrt(1 − z))/2`, `r`, `s`, `h`
  (a cutoff `⌊n/4⌋`), `b_t`, `B(x)`, `c_j = C_j/4^j`, `H`, `J`, `T`, `t`, `L`,
  `R_β`, `A`, `T_τ` and the calligraphic `𝒦`, `𝒬` all mean something else in
  Parts I–II. Part III's first-entry count `N_(N,f)` is Part I's `h(k,j)`
  reindexed (`k = N + 1`, `j = N + 1 − f`).
- Renamed from the manuscript: `ε_n → ω_n` (Part II's `ε_d` bounds a related
  fraction differently), `𝒜 → Υ` (the clipping correction; `𝒜` is Part I's
  class), the quantile `q_(1−ε) → κ_(1−ε)`, the constants `C, C_0 → C_TV`
  (`C_0` would read as a Catalan number) and `c_p → c̲_p`. No normalization
  changed.

Part IV keeps Part III's `D_n`, `M_n`, `F`, `c_j`, `R_β`, `A`, `T_τ`, `t`,
`h` and `D` (Part III's limit law), and fixes one name for each notion of its
two manuscripts. Table 14 (Section 37.2) lists every symbol with the
manuscripts' names and the tempting false reading. Watch in particular for:

- The threshold fraction is always `u`, the split fraction `y`, the profile
  `Ψ` (Part III's name in Section 32.1). Manuscript 11 writes `x`, `u` and
  `Φ` (and `Φ` is also Part I's shift map).
- The moment constants are `𝔪_p`, not the manuscripts' `κ_p`, because
  Part III's quantile `κ_(1−ε)` has an index in the same range `(0, 1)`.
  Manuscript 11's moment integral `I(p)` is `𝓘(p)`; its split integral `I_x`
  is `I(u)`, as in manuscript 10.
- `T_W` (the limiting outer-word cost, tail `~ 5/(3 sqrt(π h))`) is not
  Part III's skeleton cost `T` (tail `~ 4/sqrt(π h)`), which manuscript 10
  also calls `T`. The outer-word series are `𝒲`, `𝒲_R` (manuscript 11's `W`,
  `W_R`), not Part I's matrix `W_m`; manuscript 11's acceptance weight
  `α(w)` is `χ(w)` (Part I's `α_m` is a growth constant), its word length `K`
  is `len(W)`, its events `E_(n,m)` are `ℰ_(n,m)` (Part I's `E_m` is the
  centered remainder), its count `H_s(u)` is `𝒩_s(u)`.
- Manuscript 10's projection `P f` is `S* f` (not Part III's `P(x, z)`), its
  space `E` is `𝒳`, its pair `Y_n` is `Ξ_n`, its size-biased distribution
  function `H` is `H*`, its conjectured constant `A_r(θ)` is `Ω_r(θ)` (not
  Part I's `A_m(x)`).
- No normalization changed. Manuscript 10 tests `D_n > un`, manuscript 11
  `D_n ≥ ⌈xn⌉`; the limits agree.

Part V keeps `D_n`, `M_n`, `D`, `G`, `s`, `r`, `N_(N,f)`, `Ψ`, `ρ`, `u` and
`𝒩_s(u)` from Parts III–IV, and renames every manuscript symbol that clashes
with the earlier parts. Table 19 (Section 51.5) lists them with the
tempting false reading. Watch in particular for:

- The coefficient function is `𝔪(p)` (the manuscript's `𝒦(p)`), because for
  `p > 1/2` it **is** Part IV's `𝔪_p` (Remark 55.3). For `0 < p < 1/2` it is
  **not** a leading constant: it is the negative coefficient of the correction
  `n^(p − 1/2)`, and the leading term is `E D^p`. A calligraphic `𝒦` would
  clash with Part III's clipping series and a Greek `κ` with its quantiles
  `κ_(1−ε)`.
- The microscopic and macroscopic constants are `c_mic`, `c_mac` (the
  manuscript's `h`, `j`; Part III's `h` is the cutoff `⌊n/4⌋`), the tail
  coefficient `3/sqrt(π)` is `𝔞` (the manuscript's `a`; `a_n^(m)` is a count),
  and Lebesgue measure on `[0, 1]` is `Leb` (the manuscript's `m`, the
  adjacency bound here).
- `Φ(λ) → 𝓜(λ) = (e^λ − 1)/λ`, `T_n → ϑ_n = log D_n/log n` (not a cost `T`),
  `Q_n^λ → P_n^λ, E_n^λ`, `μ_λ → ϖ_λ`, `S, S_n → 𝒮, 𝒮_n` (survival
  functions; Part IV's `S` is an endpoint map), `r(x) → ϱ(x)`, `b → 𝔟`,
  `H, J, J_n → 𝓗, 𝓙, 𝓙_n` (Part IV's `J_n` is the first deficiency),
  `𝒜 → 𝓡`, `c(p) → 𝔠(p)`, the constants `C → K`, and in the recurrence
  `h(n,u), c_k(u), T_m(n,u,v), A_j → 𝒩_n(u), c_(k,u), T^(m)_(u,v)(n), 𝒢_j`,
  Part IV's names for the same counts. The abstract exponents `α`, `β` are
  not Part I's `α_m` or Part II's `β_m`. No normalization changed.

Part VI keeps `a_n^(m)`, `C_n`, `Cat`, `M_n`, Part I's `A_m(x)`, `R_m`,
`K_(m,1)`, Part II's `K_m`, Part IV's `θ` and `Ω_r(θ)`, and the endpoint
counts of Parts III–V, and renames every manuscript symbol that clashes with
the earlier parts. Table 24 (Section 67.5) lists them with the tempting false
reading. Watch in particular for:

- `p_n(m) = P(M_n ≤ m)` is a probability, not a moment exponent.
- **`r = ⌊1/θ⌋`** (kept from the manuscript) is **not** Part IV's
  `r = ⌈1/θ⌉ − 1` at reciprocal points: at `θ = 1/q` it is `q`, Part IV's is
  `q − 1`, and the exponent there is `q/2`. Elsewhere the two agree. `q` is the
  reciprocal index, not Part III's `q = (1 − sqrt(1 − z))/2` or Part I's
  `q_m`.
- The envelopes are `A̲_m ⪯ A_m ⪯ A̅_m` (the manuscript's `L_m`, `B_m`):
  `A̅_m = 1 + x/(1 − R_m)` is Part I's majorant (Proposition 5.1) and
  `A̲_m = 1/(1 − K_(m,1))` Part I's block bound at `d = 1` (Proposition 5.2);
  the manuscript's block polynomial `H_(m−1)` is Part I's `K_(m,1)` and its
  block sets `ℬ_k` are `𝔅_k` (Part II's `ℬ_N` is a formal series).
- Renamed from the manuscript: `F_q(n, m) → 𝒪_q(n, m)` (Part I's
  `F^(m)_(p,q)`), the ratio interval `a ≤ m/n ≤ b → θ_− ≤ m/n ≤ θ_+`, the
  window `w_q(n) → 𝔴_q(n)` (the weights are `w_k`), the kernel masses
  `ρ, ρ_± → w̄, w̄_±` (Part IV's `ρ = −Ψ'`), the resolvents `R → Z` (Part I's
  `R_m`), `Λ → λ_⋆` (Part II's `Λ`), `b_n^(m) → ã_n^(m)`, the conjectural
  constants `K_q, L_q, H_q → 𝔎_q, 𝔏_q, ℌ_q`, and in the recurrence
  `f(n,d), h(n,u), T_free, T(n,u,v), c(k,u) → N_(n,n−d), 𝒩_n(u),
  T^free_(u,v)(n), T^(m)_(u,v)(n), c_(k,u)`. No normalization changed.
- `≍` and `Θ` mean bounded ratios for large `n`, never ratio convergence.

Part VII keeps Part VI's `p_n(m)`, `𝔴_q`, `𝔎_q`, `𝔏_q`, `ℌ_q`, Part IV's
`θ`, `Ω_r(θ)`, `c_j = C_j/4^j`, `c_±`, the endpoint letters `F`, `J`, `L`,
the operations `R_β`, `A`, the word series `𝒲`, `𝒲_R` and the acceptance
weight `χ(w)`, and renames the manuscript symbols that clash. Table 27
(Section 79.3) lists them with the tempting false reading. Watch in
particular for:

- The manuscript's word masses `W, W_R, W_A` are printed
  `𝒲(1/4), 𝒲_R(1/4), 𝒲_A(1/4)` (`= 4, 2, 2`), with `𝒲_A = 𝒲 − 𝒲_R`; a bare
  `W` is Part IV's random outer word or Part VI's renewal kernel.
- Its small-word series `S(z), T(z)` are printed `S_n(z), T_n(z)`: they are
  Part VI's equation (340) for the upper kernel (327), of mass `3/4`.
- `x, y, z` are the three macroscopic size fractions in `I_3` and in the
  three-piece section, and `z` is also the formal variable of Sections 82–83;
  the two never meet in one formula (in `I_3`, `z = 1 − x − y`).
- `K, K_h, K_B` are constants, as in Part IV, not Part II's polynomial `K_m`
  or Part VI's `𝔎_q`; `L` is the last entry, except in the proof of
  Lemma 83.1, where it is the tilt constant, as in Part VI.
- Its `I_3(θ)` is a three-piece integral, not Part IV's split integral
  `I(u)`. No normalization changed.

Part VIII keeps Part VI's `p_n(m)`, `𝔴_q`, `𝔎_q`, `𝔏_q`, `ℌ_q`, `Ω_r`, and
Part VII's `c_j`, endpoint letters, operations, word series, small-word series
`S_n`, `T_n` and constants, and renames the manuscript symbols that clash.
Table 29 (Section 90.3) lists them with the tempting false reading. Watch in
particular for:

- The manuscript's endpoint factor `C_p^⋆` is printed `ϰ_p`; a bare `C` with
  an index is a Catalan number. Its window constants `B_r`, `A_r` are Part VI's
  `𝔎_r`, `𝔏_r` (not Part I's `B_d`, the bound `B`, the operation `A` or
  `A_m(x)`), and its domain `D_p(θ)` is printed `𝒟_p(θ)`.
- **Index shift:** the phase index `p` counts macroscopic pieces, so Part VI's
  amplitude is `Ω_r(θ) = ϰ_(r+1) I_(r+1)(θ)` (`r = p − 1`), not `ϰ_r I_r`;
  Part VI's threshold index `q` is the window index `r`.
- The manuscript's `t_s = [z^s] T(z)^g` is printed `T^(g)_s`, because `t` is
  the window variable; its pair convolution `F_a(s)` and integral `J(A)` are
  printed `𝒫_a(s)` and `𝒥(γ)`. No normalization changed.

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 200 pages (title and abstract pp. 1–2,
                                                     contents pp. 3–13, Part I pp. 14–28, Part II pp. 29–49,
                                                     Part III pp. 50–74, Part IV pp. 75–115, Part V pp. 116–143,
                                                     Part VI pp. 144–170, Part VII pp. 171–183,
                                                     Part VIII pp. 184–197, Part I's appendices pp. 198–199,
                                                     bibliography p. 200)
README.md                                            this guide
build.sh, build.ps1                                  Part I's three-pass pdfLaTeX scripts (build in place; see below)
requirements.txt                                     Part I's pins: numpy 2.3.5, scipy 1.17.0, sympy 1.14.0, matplotlib 3.10.8
code/model.py                                        Part I: exact endpoint model and combinatorics
code/compute.py                                      Part I: numerical proposals and exact symbolic solver
code/verify.py                                       Part I: standard-library independent exact verifier
code/plot_results.py                                 Part I: Figures 1–2
data/sequences.csv                                   Part I: exact a_n^(m), n = 0..200, m = 1..12
data/growth_constants.csv                            Part I: component roots, m = 2..20
data/perron_certificates.json                        Part I: 38 rational Perron-radius certificates
data/symbolic_certificate_m1..m4.json                Part I: polynomial state certificates (four files)
data/generating_functions.json                       Part I: reduced rational functions, m = 1..4
data/large_m_scalar_bounds.csv                       Part I: scalar root evaluations through m = 1,000,000
data/computation_log.txt, data/verification_log.txt  Part I: recorded runs
data/environment.json                                Part I: the numerical/symbolic environment
figures/component_growth.{pdf,png}                   Part I: Figure 1
figures/scalar_remainder_bounds.{pdf,png}            Part I: Figure 2
code/02-centered-remainder-model.py                  Part II: exact Catalan, endpoint and block objects
code/02-centered-remainder-verify.py                 Part II: exact finite checks (standard library)
code/02-centered-remainder-verify_expansion.py       Part II: exact symbolic check of the expansion (SymPy)
code/02-centered-remainder-compute.py                Part II: floating-point illustrations (NumPy, SciPy)
code/02-centered-remainder-plot_results.py           Part II: its two figures from the CSVs (Matplotlib)
data/02-centered-remainder-verification_report.json  Part II: recorded exact-check run (PASS)
data/02-centered-remainder-verification_console.txt  Part II: its console output (identical to the report)
data/02-centered-remainder-rational_certificates.json  Part II: five exact scalar corridors (Table 7)
data/02-centered-remainder-expansion_verification.json  Part II: recorded symbolic run (P_1..P_4, residual 0)
data/02-centered-remainder-expansion_console.txt     Part II: its console output (identical to the JSON)
data/02-centered-remainder-scalar_numerics.csv       Part II: scalar corridor, 63 values of m from 10 to 10^6 (CRLF)
data/02-centered-remainder-component_numerics.csv    Part II: component rates and beta_m, m = 2, 3, 4, 5, 10, 20, 30, 50 (CRLF)
data/02-centered-remainder-environment.json          Part II: environment (byte-identical to data/environment.json)
data/02-centered-remainder-requirements.txt          Part II: lower-bound pins, as delivered at the package root
data/02-centered-remainder-pdf_fonts.txt             Part II: font list of the delivered (unshipped) PDF
data/02-centered-remainder-pdf_validation.json       Part II: inspection record of the delivered 23-page PDF
figures/02-centered-remainder-remainder_corridor.pdf Part II: Figure 3
figures/02-centered-remainder-corridor_width.pdf     Part II: Figure 4
code/03-largest-jump-model.py                        Part III: exact Catalan, endpoint, skeleton and rational-series code
code/03-largest-jump-verify.py                       Part III: standard-library exact finite verifier
code/03-largest-jump-verify_symbolic.py              Part III: exact symbolic identity and expansion checks (SymPy)
code/03-largest-jump-make_data.py                    Part III: regenerates the three CSV files
code/03-largest-jump-plot_results.py                 Part III: its two figures from the CSVs (Matplotlib)
code/03-largest-jump-build.sh                        Part III: the manuscript's three-pass build (for the delivered layout)
data/03-largest-jump-verification.json               Part III: recorded core run (PASS)
data/03-largest-jump-verification.txt                Part III: the same record (byte-identical to the JSON)
data/03-largest-jump-symbolic_verification.json      Part III: recorded symbolic run (PASS, SymPy 1.14.0)
data/03-largest-jump-limit_probabilities.csv         Part III: P(D = k) for k = 1..256 as exact fractions, with decimals (CRLF)
data/03-largest-jump-finite_histograms.csv           Part III: exact laws of D_n for n = 2..12 (CRLF)
data/03-largest-jump-extreme_jump_exact.csv          Part III: exact P(D_n = 1) for ten n from 3 to 1000 (CRLF)
data/03-largest-jump-requirements-optional.txt       Part III: optional pins, sympy 1.14.0 and matplotlib 3.10.8
03-largest-jump-PROOF_STATUS.md                      Part III: the manuscript's proof-status and non-claims note
03-largest-jump-SOURCES.md                           Part III: its source and provenance ledger
03-largest-jump-VALIDATION.md                        Part III: its delivery validation record
figures/03-largest-jump-tail_scaling.pdf             Part III: Figure 5
figures/03-largest-jump-finite_probabilities.pdf     Part III: Figure 6
code/04-macroscopic-jump-verify.py                   Part IV (ms. 10): standard-library exact finite checks
code/04-macroscopic-jump-simulate.cpp                Part IV (ms. 10): C++17 uniform Catalan-tree sampler
code/04-macroscopic-jump-plot_results.py             Part IV (ms. 10): Figures 7–8 (NumPy, Matplotlib)
code/04-macroscopic-jump-build.sh                    Part IV (ms. 10): the manuscript's three-pass build (delivered layout)
data/04-macroscopic-jump-verification.json           Part IV (ms. 10): recorded exact-check run (PASS)
data/04-macroscopic-jump-exact_small_distributions.csv  Part IV (ms. 10): exact laws of D_n, n = 1..11 (CRLF)
data/04-macroscopic-jump-simulation.csv              Part IV (ms. 10): 675,000 samples at five sizes (Table 16)
data/04-macroscopic-jump-build_audit.json            Part IV (ms. 10): audit of the delivered (unshipped) 23-page PDF
04-macroscopic-jump-SOURCES.md                       Part IV (ms. 10): its source and provenance ledger
figures/04-macroscopic-jump-bulk_profile.{pdf,png}   Part IV (ms. 10): Figure 7 (PDF regenerated, PNG as delivered)
figures/04-macroscopic-jump-mean_weighted_law.{pdf,png}  Part IV (ms. 10): Figure 8 (PDF regenerated, PNG as delivered)
code/05-macroscopic-deficits-model.py                Part IV (ms. 11): exact endpoint counts and Catalan generator
code/05-macroscopic-deficits-verify.py               Part IV (ms. 11): exhaustive combinatorial checks (standard library)
code/05-macroscopic-deficits-verify_symbolic.py      Part IV (ms. 11): eleven symbolic identity groups (SymPy)
code/05-macroscopic-deficits-numerics.py             Part IV (ms. 11): exact bulk and moment counts
code/05-macroscopic-deficits-plot_results.py         Part IV (ms. 11): Figures 9–10 (NumPy, Matplotlib)
code/05-macroscopic-deficits-build.sh                Part IV (ms. 11): the manuscript's latexmk build (delivered layout)
data/05-macroscopic-deficits-verification.json       Part IV (ms. 11): recorded exact-check run (PASS)
data/05-macroscopic-deficits-symbolic_verification.json  Part IV (ms. 11): recorded symbolic run (PASS, SymPy 1.14.0)
data/05-macroscopic-deficits-bulk_counts.csv         Part IV (ms. 11): ten exact bulk cases up to n = 320 (Table 15; CRLF)
data/05-macroscopic-deficits-moment_counts.csv       Part IV (ms. 11): exact moments for n = 20, 40, 80 (CRLF)
data/05-macroscopic-deficits-environment.json        Part IV (ms. 11): delivery environment (Python 3.13.5, Linux)
data/05-macroscopic-deficits-package_audit.json      Part IV (ms. 11): audit of the delivered (unshipped) 24-page PDF
05-macroscopic-deficits-SOURCES.md                   Part IV (ms. 11): its source and novelty ledger
figures/05-macroscopic-deficits-bulk_profile.{pdf,png}   Part IV (ms. 11): Figure 9 (PDF regenerated, PNG as delivered)
figures/05-macroscopic-deficits-mean_constant.{pdf,png}  Part IV (ms. 11): Figure 10 (PDF regenerated, PNG as delivered)
code/06-critical-moments-exact_counts.py             Part V: exact laws of D_n, exhaustive comparisons, PGF coefficients (standard library)
code/06-critical-moments-verify_symbolic.py          Part V: five exact algebraic identity checks (SymPy)
code/06-critical-moments-numerics.py                 Part V: constants by stable quadrature, regressions, finite moments (mpmath)
code/06-critical-moments-figures.py                  Part V: Figures 11–13 (NumPy, Matplotlib)
code/06-critical-moments-build.sh                    Part V: the manuscript's three-pass pdfLaTeX build (delivered layout)
data/06-critical-moments-exact_checks.json           Part V: recorded finite-check run (PASS; 625, 23,713, 784, 129)
data/06-critical-moments-exact_distributions.json    Part V: exact integer laws of D_n, n = 1..64 (index d = 0 holds 0)
data/06-critical-moments-pgf_coefficients.json       Part V: P(D = k), k = 0..128, as exact fractions
data/06-critical-moments-symbolic_checks.json        Part V: recorded symbolic run (PASS, five identities)
data/06-critical-moments-constants.json              Part V: 40/70-digit constants, 𝔪(p) values, regressions (not certified)
data/06-critical-moments-finite_moments.csv          Part V: finite-size moments for n = 8, 16, 32, 64 (Table 21; CRLF)
data/06-critical-moments-pdf_quality.json            Part V: audit of the delivered (unshipped) 27-page PDF
data/06-critical-moments-requirements.txt            Part V: pins mpmath 1.3.0, sympy 1.14.0, numpy 2.3.5, matplotlib 3.10.8
06-critical-moments-SOURCES.md                       Part V: the manuscript's pin, inspected files and literature ledger
06-critical-moments-PROOF_STATUS.md                  Part V: its proof-status and non-claims ledger
figures/06-critical-moments-tilted_densities.pdf     Part V: Figure 11 (regenerated)
figures/06-critical-moments-centered_moment.pdf      Part V: Figure 12 (regenerated)
figures/06-critical-moments-biased_distribution.pdf  Part V: Figure 13 (regenerated)
code/07-polynomial-rarity-model.py                   Part VI: exact endpoint counter, envelopes, lower-block generator, order proxy
code/07-polynomial-rarity-verify.py                  Part VI: finite tests and exact-count data (standard library)
code/07-polynomial-rarity-figures.py                 Part VI: Figures 14–15 (NumPy, Matplotlib)
code/07-polynomial-rarity-Makefile                   Part VI: the manuscript's pdf/check/figures/clean targets (delivered layout)
data/07-polynomial-rarity-phase_counts.csv           Part VI: 20 exact fixed-fraction samples, n = 32..128 (Table 26; CRLF)
data/07-polynomial-rarity-crossover_counts.csv       Part VI: 18 exact crossover samples, n = 64, 96 (CRLF)
data/07-polynomial-rarity-verification_log.txt       Part VI: recorded run (seven PASS lines)
07-polynomial-rarity-SOURCES.md                      Part VI: the manuscript's pin, inspected files and literature ledger
figures/07-polynomial-rarity-phase_exponents.{pdf,png}  Part VI: Figure 14 (PDF regenerated, PNG as delivered)
figures/07-polynomial-rarity-finite_counts.{pdf,png}    Part VI: Figure 15 (PDF regenerated, PNG as delivered)
code/08-half-size-crossover-model.py                 Part VII: the credited endpoint model (byte-identical to code/07-polynomial-rarity-model.py)
code/08-half-size-crossover-verify.py                Part VII: generator, parser and word checks, exact-count table (standard library)
code/08-half-size-crossover-build.sh                 Part VII: the manuscript's three-pass build (delivered layout)
data/08-half-size-crossover-finite_checks.csv        Part VII: 12 exact window samples, n = 64, 96, 128, t = −1/2, 0, 1/2, 1 (CRLF)
data/08-half-size-crossover-verification.json        Part VII: recorded finite-check run (PASS; 36, 5,599, 200; masses 3 and 8)
data/08-half-size-crossover-verification.log         Part VII: its stdout capture (byte-identical to the JSON)
data/08-half-size-crossover-validation.json          Part VII: audit of the delivered (unshipped) 8-page PDF
08-half-size-crossover-SOURCES.md                    Part VII: the manuscript's pin, inspected sources and novelty boundary
code/09-general-crossovers-verify.py                 Part VIII: channel masks, literal enumeration, endpoint states, exact counts (standard library)
code/09-general-crossovers-verify_integral.py        Part VIII: symbolic check of the I_4(1/3) algebra (SymPy)
code/09-general-crossovers-build.sh                  Part VIII: the manuscript's three-pass build (delivered layout)
data/09-general-crossovers-results.json              Part VIII: recorded full run (PASS; channels p = 2..14, 44 + 1,500 state checks)
data/09-general-crossovers-third_boundary_counts.csv Part VIII: exact counts at m = n/3, n = 48, 72, 96, 144, 192 (Table 30; CRLF)
data/09-general-crossovers-third_window_counts.csv   Part VIII: exact counts at n = 48, 96, t = ±1/8 (CRLF)
data/09-general-crossovers-integral_symbolic.json    Part VIII: recorded symbolic run (I_4(1/3) = 8 sqrt(2) π)
data/09-general-crossovers-validation.json           Part VIII: audit of the delivered (unshipped) 8-page PDF
09-general-crossovers-CHECKS.md                      Part VIII: the delivered checks README (scope, run, model lineage)
09-general-crossovers-SOURCES.md                     Part VIII: the manuscript's pin, credited results and literature ledger
```

The sixteen `02-centered-remainder-` code and data files were staged in the
placement commit `938b2f74e`, byte-identical to the delivery; the two CSVs
are all-CRLF as delivered and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The two Part II figure PDFs were added
in the write phase, copied byte-identically from the delivered `figures/`; the
delivered PNG versions of those figures are not shipped (the plot script
regenerates both formats).

The sixteen `03-largest-jump-` code, data and audit files were staged in the
placement commit `faef2ed2a`, byte-identical to the delivery (the delivered
root `build.sh` is `code/03-largest-jump-build.sh`, and the root
`requirements-optional.txt` is under `data/`); the three CSVs are all-CRLF as
delivered and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The two Part III figure PDFs were added
in the write phase, copied byte-identically from the delivered `figures/`; the
delivered PNG versions are not shipped.

The thirty `04-macroscopic-jump-` and `05-macroscopic-deficits-` files were
staged in the placement commit `a701d9098`, byte-identical to the deliveries
(each delivered root `build.sh` is `code/…-build.sh`); three CSVs are all-CRLF
as delivered and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The delivered `SHA256SUMS` ledgers are
not shipped. In the write phase the four figure **PDFs** were regenerated
(see "Discrepancies" below), so they are no longer the delivered bytes; the
four PNG previews, the code and the data are unchanged.

The eighteen `06-critical-moments-` files were staged in the placement commit
`3025c15df`, byte-identical to the delivery (the delivered root `build.sh` is
`code/06-critical-moments-build.sh`, and the root `requirements.txt` is under
`data/`). One of them, `data/06-critical-moments-finite_moments.csv`, is
all-CRLF as delivered (5 lines) and is protected by a `-text` line in
`SetTheory/Cardinals/.gitattributes`; no other Part V text file contains a CR
byte.
The delivered `SHA256SUMS`, manuscript, README and PDF are not shipped. In the
write phase the three figure PDFs were regenerated (see "Discrepancies"
below); the code and data are unchanged.

The twelve `07-polynomial-rarity-` files were staged in the placement commit
`29e52fcdf`, byte-identical to the delivery (the delivered root `Makefile` is
`code/07-polynomial-rarity-Makefile`, and the root `SOURCES.md` is
`07-polynomial-rarity-SOURCES.md`). The two CSVs are all-CRLF as delivered
(21 and 19 lines) and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`; no other Part VI text file contains a CR
byte. The delivered `SHA256SUMS` (15/15 verified at placement), manuscript,
README and PDF are not shipped. In the write phase the two figure PDFs were
regenerated (see "Discrepancies" below); the PNG previews, the code and the
data are unchanged.

The eight `08-half-size-crossover-` files were staged in the placement
commit `427bca743`, byte-identical to the delivery (the delivered root
`model.py`, `verify.py` and `build.sh` are under `code/`, the root
`finite_checks.csv`, `verification.json`, `verification.log` and
`validation.json` under `data/`, and the root `SOURCES.md` is
`08-half-size-crossover-SOURCES.md`). Two of them duplicate other files:
`code/08-half-size-crossover-model.py` is the same blob (`a4fdee3761`) as
`code/07-polynomial-rarity-model.py`, because the manuscript copied Part VI's
model, and `data/08-half-size-crossover-verification.log` is identical to the
JSON it captures; both are shipped so that the delivered layout can be
restored by renaming alone. `data/08-half-size-crossover-finite_checks.csv`
is all-CRLF as delivered (13 lines) and is protected by a `-text` line in
`SetTheory/Cardinals/.gitattributes`; no other Part VII file contains a CR
byte. The delivered `SHA256SUMS` (11/11 verified at placement), manuscript,
README and PDF are not shipped. Part VII has no figures.

The ten `09-general-crossovers-` files were staged in the placement commit
`9e6b04645`, byte-identical to the delivery (the delivered `checks/verify.py`,
`checks/verify_integral.py` and root `build.sh` are under `code/`; the
`checks/` records and root `validation.json` under `data/`; the root
`SOURCES.md` and `checks/README.md` are `09-general-crossovers-SOURCES.md` and
`09-general-crossovers-CHECKS.md`). The two CSVs are all-CRLF as delivered (6
and 5 lines) and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`; no other Part VIII file contains a CR
byte. Not shipped: the manuscript, its PDF and delivery README, the two
`SHA256SUMS` ledgers (15/15 and 8/8 verified at placement), and the delivered
`checks/model.py`, which is byte-identical to `code/07-polynomial-rarity-model.py`
and `code/08-half-size-crossover-model.py` (blob `a4fdee3761`; the rerun recipe
below restores it). Part VIII has no figures.

The forty-six files with the prefixes `10-logarithmic-bridge-` to
`15-growing-macro-counts-` (twelve ledgers and checks READMEs here, eighteen
programs in `code/`, sixteen records in `data/`) were staged in the same
placement commit `9e6b04645` for Part IX, which is written in a separate commit;
they are listed and described with it.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex` three times. Build in a scratch copy of `article.tex` and
`figures/`, so that no auxiliary files land here; `build.sh` and `build.ps1`
run three pdfLaTeX passes in this directory and leave `.aux`, `.log`, `.toc`
and `.out` files beside the source. The figures are retained, so Python is not
needed to rebuild. The Part I PDF was built with MiKTeX (pdfTeX 1.40.26) with
no errors, no undefined or multiply defined references, no duplicate
destinations and no overfull or underfull boxes; the two font-substitution
warnings (`T1/cmss` at 5.5 pt) are present in a build of the committed Part I
text as well. No font files are included. The batch-43 build (69 pages,
29 September 2026) is equally clean: the same two font warnings and nothing
else. `code/03-largest-jump-build.sh` is the manuscript's own script; it
builds an `article.tex` in its own directory and fails in `code/`. The
batch-52 build (111 pages,
29 September 2026, `latexmk` with pdfTeX 1.40.29 under MiKTeX 26.2), is
equally clean: 0 errors, 0 undefined references or
citations, 0 multiply defined labels, no duplicate destinations, no overfull
or underfull boxes, and the same two font warnings. To keep the abstract on
the title page, the batch-52 edit shortened four vertical spaces on it
(8 mm → 4 mm, 5 mm → 3 mm twice, 3 mm → 1 mm). Part IV's four figures embed
TrueType fonts; the Type 3 fonts still present in `article.pdf` come from the
unchanged Part II and Part III figure PDFs. `code/04-macroscopic-jump-build.sh`
and `code/05-macroscopic-deficits-build.sh` are the manuscripts' own scripts;
like Part III's, they change to their own directory, look for an
`article.tex` there and fail in `code/`.

The batch-64 build (141 pages,
30 September 2026, `latexmk` with pdfTeX 1.40.29 under MiKTeX 26.2) was
equally clean:
0 errors, 0 undefined references or citations, 0 multiply defined labels, no
duplicate destinations, no overfull or underfull boxes, and the same two font
warnings as a build of the committed batch-52 text. To keep the title page on
one page after the abstract's batch-64 paragraph, the batch-64 edit added
`\enlargethispage{3\baselineskip}` to it, which lowers the companion-archive
line into the bottom margin; nothing else on the title page changed. The
heading of Section 56 is typeset as text ("1/log n"), not math: in math it
loaded a sans-serif font at a size MiKTeX lacks and added a third font
warning. Part V's three figures embed TrueType fonts.
`code/06-critical-moments-build.sh` is the manuscript's own script; it changes
to its own directory, looks for an `article.tex` there and fails in `code/`.

The batch-68 build (169 pages,
30 September 2026, `latexmk` with pdfTeX 1.40.29 under MiKTeX 26.2) was
equally clean: 0 errors, 0 undefined references or citations, 0 multiply
defined labels, no duplicate destinations, no overfull or underfull boxes,
and the same two font warnings as a build of the committed batch-64 text. The
title page still fits on one page with the abstract's batch-68 paragraph,
under the existing `\enlargethispage`; nothing else on it changed. Part VI's
two figures embed TrueType fonts. `code/07-polynomial-rarity-Makefile` is the
manuscript's own file: its targets run `latexmk` on an `article.tex` and
`python code/…` from the package root, so they do nothing useful in `code/`.

The batch-71 build (183 pages,
30 September 2026 Pacific time, `latexmk` with pdfTeX 1.40.29 under
MiKTeX 26.2), is equally clean: 0 errors, 0 undefined references or
citations, 0 multiply defined labels, no duplicate destinations, no overfull
or underfull boxes, and the same two font warnings as a build of the
committed batch-68 text. With the abstract's batch-71 paragraph the title
page spilled its last lines onto a second page; the batch-71 edit shortened
its four vertical spaces (4 mm → 1 mm, 3 mm → 1 mm twice, 1 mm → 0 mm), and
the title page fits on one page again under the existing `\enlargethispage`;
nothing else on it changed. Part VII has no figures.
`code/08-half-size-crossover-build.sh` is the manuscript's own script; it
changes to its own directory and runs pdfLaTeX three times on a
`half_size_crossover.tex` there, which is not shipped, so it fails in
`code/`.

The batch-72 build of Part VIII, which is the shipped `article.pdf` (200 pages,
1 October 2026, `latexmk` with
pdfTeX 1.40.29 under MiKTeX 26.2) is equally clean: 0 errors, 0 undefined
references or citations, 0 multiply defined labels, no duplicate
destinations, no overfull or underfull boxes, and the same two font warnings
as a build of the committed batch-71 text (183 pages). With the abstract's
batch-72 paragraph the title page could no longer hold the abstract, the
scope box and the companion-archive line: the batch-72 edit added a
`\newpage` after the abstract, so the scope box and the companion-archive
line now form page 2 and the contents start on page 3; nothing else on the
front pages changed. Part VIII has no figures.
`code/09-general-crossovers-build.sh` is the manuscript's own script; it
changes to its own directory and runs pdfLaTeX three times on a
`general_avoider_crossovers.tex` there, which is not shipped, so it fails in
`code/`.

## Rerun the checks

**Part I.** Its exact verifier only reads its data and runs in place:

```sh
py code/verify.py        # or: python code/verify.py; do not use -O
```

It needs no third-party packages and checks, among others, 2,840 cumulative
endpoint counts, 53,534 weighted-edge comparisons for the shift, the 38
rational Perron certificates (3,458 strict integer row inequalities) and the
four polynomial-matrix certificates; `data/verification_log.txt` is its
recorded run (Python 3.13.5). Part I's generator and plot script
**overwrite** the shipped tables, certificates and figures, so run them only
on a copy:

```sh
W=/path/to/scratch
mkdir -p "$W/01" && cp -r code data figures requirements.txt "$W/01/"
(cd "$W/01" && python -m pip install -r requirements.txt \
   && python code/compute.py --max-m 20 --symbolic-max 4 --large-scalars \
   && python code/verify.py && python code/plot_results.py)
```

A positive numerical eigenvector is only a proposal: the generator refuses to
issue a certificate unless the integer inequalities pass, and the verifier
checks them again without the numerical solver. Part I's large-`m` scalar
bounds are floating-point evaluations of roots for which the article proves
exact comparison theorems, not outward-rounded interval endpoints.
`OPENBLAS_NUM_THREADS=1` is optional.

**Part II.** Its scripts still use the delivered names. Run in place,
`02-centered-remainder-verify.py` and `02-centered-remainder-compute.py` fail
with `ImportError`, because their `from model import …` loads Part I's
different `code/model.py`; `02-centered-remainder-verify_expansion.py` would
write a new `data/expansion_verification.json` here; and
`02-centered-remainder-plot_results.py` reads `data/scalar_numerics.csv`,
which does not exist here. Restore the delivered layout in a scratch copy
(Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code" "$W/02/data" "$W/02/figures"
for f in code/02-centered-remainder-*.py; do cp "$f" "$W/02/code/${f#code/02-centered-remainder-}"; done
for f in data/02-centered-remainder-*; do cp "$f" "$W/02/data/${f#data/02-centered-remainder-}"; done
mv "$W/02/data/requirements.txt" "$W/02/requirements.txt"
cd "$W/02"
py code/verify.py                 # standard library; writes data/verification_report.json
                                  #   and data/rational_certificates.json
py code/verify_expansion.py       # SymPy; writes data/expansion_verification.json
uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 python code/compute.py
                                  # writes data/scalar_numerics.csv, data/component_numerics.csv
uv run --no-project --with matplotlib==3.10.8 python code/plot_results.py
                                  # writes figures/remainder_corridor.* and corridor_width.*
```

The first three were run this way on 28 September 2026 (Python 3.14.4,
SymPy 1.14.0, NumPy 2.3.5, SciPy 1.17.0): `verify.py` passed with the recorded
counts (55 first-entry counts, 4,930 `V`-row comparisons, 9,000 tail
inequalities, 67,425 restricted-`U` comparisons, five corridors), and its two
outputs and the symbolic output equal the shipped files apart from Windows
line endings; the regenerated CSVs differ from the shipped ones by at most
6 × 10⁻¹⁶ relative (last-ulp floating-point differences). The plot script was
not rerun. On Windows, Python writes the JSON files with CRLF line endings.

**Part III.** Its scripts also use the delivered names. Run in place,
`03-largest-jump-verify.py` and `03-largest-jump-make_data.py` fail with
`ImportError` (their `from model import …` loads Part I's `code/model.py`,
which has no `avoiders`); `03-largest-jump-verify_symbolic.py` would write a
new `data/symbolic_verification.json` here; `03-largest-jump-plot_results.py`
reads `data/limit_probabilities.csv`, which does not exist here; and
`code/03-largest-jump-build.sh` finds no `article.tex` in `code/`. Restore the
delivered layout in a scratch copy:

```sh
W=/path/to/scratch
mkdir -p "$W/03/code" "$W/03/data" "$W/03/figures"
for f in code/03-largest-jump-*; do cp "$f" "$W/03/code/${f#code/03-largest-jump-}"; done
for f in data/03-largest-jump-*; do cp "$f" "$W/03/data/${f#data/03-largest-jump-}"; done
mv "$W/03/data/requirements-optional.txt" "$W/03/"
mv "$W/03/code/build.sh" "$W/03/"
cd "$W/03"
py code/verify.py                 # standard library, no -O; writes data/verification.json
py code/make_data.py              # rewrites the three CSV files
uv run --no-project --with sympy==1.14.0 python code/verify_symbolic.py
                                  # writes data/symbolic_verification.json
uv run --no-project --with matplotlib==3.10.8 python code/plot_results.py
                                  # writes figures/tail_scaling.* and finite_probabilities.*
```

The first three were run this way on 29 September 2026 (Python 3.14.4, SymPy
1.14.0): the verifier passed with the recorded counts (31 clipping
coefficients, 40 probability coefficients, median 9, 2,055 avoiders through
`n = 8`, 804 skeletons of costs 2–7, 269,402 reconstruction tests) and its
JSON differs from the shipped one only in `elapsed_seconds` and line endings;
the three regenerated CSVs are byte-identical to the shipped ones; the
symbolic output equals the shipped file apart from line endings. The plot
script was not rerun. The verifier prints the same JSON text it writes;
`data/03-largest-jump-verification.txt` is the delivered capture of that
console output (the delivered README refreshes it with
`python code/verify.py > data/verification.txt`). Independently, for this
write-up, the 256 shipped probabilities were recomputed from the formula for `G` (0 mismatches), and
the extreme-jump formula, the first-entry count and both first-entry bounds of
Remark 23.2 were checked by exhaustive enumeration for `n ≤ 8`.

**Part IV.** Both packages' scripts use their delivered names and write into
the delivered `data/` and `figures/`, **overwriting their own recorded
outputs** there. Run in place here they misbehave: `04-macroscopic-jump-verify.py`
would write new unprefixed `data/verification.json` and
`data/exact_small_distributions.csv` into this directory (Part III's verifier
writes a `data/verification.json` too); `04-macroscopic-jump-plot_results.py`
and `05-macroscopic-deficits-plot_results.py` read `data/simulation.csv` and
`data/bulk_counts.csv`, which do not exist here;
`05-macroscopic-deficits-verify.py` and `05-macroscopic-deficits-numerics.py`
fail with `ImportError` (their `from model import …` loads Part I's
`code/model.py`, which has no `Counter`); `05-macroscopic-deficits-verify_symbolic.py`
would write a new `data/symbolic_verification.json`; and both build scripts
find no `article.tex` in `code/`. Restore each delivered layout in a scratch
copy (Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
for k in 04-macroscopic-jump 05-macroscopic-deficits; do
  mkdir -p "$W/$k/code" "$W/$k/data" "$W/$k/figures"
  for d in code data figures; do
    for f in $d/$k-*; do cp "$f" "$W/$k/$d/${f#$d/$k-}"; done
  done
  mv "$W/$k/code/build.sh" "$W/$k/"
done
cd "$W/04-macroscopic-jump"        # manuscript 10
py code/verify.py                  # standard library, no -O; rewrites data/verification.json
                                   #   and data/exact_small_distributions.csv
g++ -O3 -std=c++17 code/simulate.cpp -o simulate && ./simulate > data/simulation.csv
                                   # rewrites the recorded samples (not rerun here)
uv run --no-project --with numpy==2.3.5 --with matplotlib==3.10.8 python code/plot_results.py
                                   # writes figures/bulk_profile.* and mean_weighted_law.*
cd "$W/05-macroscopic-deficits"    # manuscript 11
py code/verify.py                  # standard library, no -O; rewrites data/verification.json
uv run --no-project --with sympy==1.14.0 python code/verify_symbolic.py
                                   # rewrites data/symbolic_verification.json
py code/numerics.py                # exact counts, about 2 minutes; rewrites both CSVs
                                   #   (--section bulk or --section moments for one)
uv run --no-project --with numpy==2.3.5 --with matplotlib==3.10.8 python code/plot_results.py
                                   # writes figures/bulk_profile.* and mean_constant.*
```

These were run this way on 29 September 2026 (Python 3.14.4, SymPy 1.14.0,
NumPy 2.3.5, Matplotlib 3.10.8), except the C++ sampler, which was not
rerun. Manuscript 10's verifier passed (82,499 avoiders of sizes 1–11,
filter check through size 8, 101 cost tails, 2,352 cycle-lemma words); its
JSON equals the shipped one apart from line endings and its CSV is
byte-identical to the shipped one. Manuscript 11's verifier passed (6,916
avoiders, 36 total counts, 644 endpoint states, 18,738 parser checks, 60 word
coefficients) and its symbolic script passed all eleven groups; both JSONs
equal the shipped ones apart from line endings. `numerics.py` regenerated both
CSVs byte-identically (bulk section 91 s, moment section 13 s). On Windows,
Python writes the JSON files with CRLF line endings; the CSV writers use
`newline=''` with the `csv` module's `\r\n` terminator, so they write CRLF on
every platform, which is why the three delivered CSVs are CRLF. To reproduce
the shipped figure PDFs without Type 3 fonts, put a file `matplotlibrc`
containing `pdf.fonttype: 42` in the working directory before running a plot
script, as the write phase did; without it Matplotlib embeds Type 3 fonts, as
in the deliveries. Independently, for this write-up, the constants of Part IV
were checked symbolically (SymPy 1.14.0): the derivative of `Ψ`, the split
integral `I(u)` at `u = 1/5`, the three limits of Table 15,
`𝓘(p)` at `p = 1, 3/2, 2, 3, 4`, the equality of the two
variance forms and of manuscript 10's `𝔪_3`, the expansions at `u → 0` and
`u → 1/2`, `H*(1/5) = 1/2`, the word-length law (mass 1, mean 7/3), and the
exact cost tail of Lemma 40.2 for `h ≤ 29`; the recurrence (Section 44.2), the
large-`p` asymptotic and the equality of both integral forms at `p = 3/2, 3`
were checked numerically.

**Part V.** Its scripts use the delivered names and write into the delivered
`data/` and `figures/`, **overwriting their own recorded outputs** there.
Run in place here they misbehave: `06-critical-moments-exact_counts.py` would
write new unprefixed `data/exact_distributions.json`,
`data/pgf_coefficients.json` and `data/exact_checks.json` into this
directory; `06-critical-moments-verify_symbolic.py` would write a new
`data/symbolic_checks.json`; `06-critical-moments-numerics.py` reads
`data/pgf_coefficients.json` and `data/exact_distributions.json`, which do
not exist here, and would otherwise write `data/constants.json` and
`data/finite_moments.csv`; `06-critical-moments-figures.py` reads
`data/constants.json`; and the build script finds no `article.tex` in
`code/`. Restore the delivered layout in a scratch copy (Git Bash or another
POSIX shell, from this directory):

```sh
W=/path/to/scratch
k=06-critical-moments
mkdir -p "$W/$k/code" "$W/$k/data" "$W/$k/figures"
for d in code data figures; do
  for f in $d/$k-*; do cp "$f" "$W/$k/$d/${f#$d/$k-}"; done
done
mv "$W/$k/code/build.sh" "$W/$k/"
mv "$W/$k/data/requirements.txt" "$W/$k/"
cd "$W/$k"
py code/exact_counts.py --max-n 64 --pgf-terms 128
                                   # standard library, no -O; rewrites exact_distributions.json,
                                   #   pgf_coefficients.json, exact_checks.json
uv run --no-project --with sympy==1.14.0 python code/verify_symbolic.py
                                   # rewrites data/symbolic_checks.json
uv run --no-project --with mpmath==1.3.0 python code/numerics.py
                                   # rewrites data/constants.json and data/finite_moments.csv
printf 'pdf.fonttype: 42\n' > matplotlibrc   # TrueType instead of Type 3 fonts
uv run --no-project --with numpy==2.3.5 --with matplotlib==3.10.8 python code/figures.py
                                   # writes figures/{tilted_densities,centered_moment,biased_distribution}.pdf
```

These were run this way on 30 September 2026 (`py` was Python 3.14.4 and the
`uv` runs used Python 3.13.5, with SymPy 1.14.0, mpmath 1.3.0, NumPy 2.3.5 and
Matplotlib 3.10.8; about 18 seconds in all). The
finite checks passed with the recorded counts (625 definition-checked
avoiders of sizes 1–7, 23,713 generated avoiders of sizes 1–10, 784
endpoint-state equalities, 129 PGF coefficients), the symbolic script passed
its five identities, and `numerics.py` reported "PASS: numerical regression
only, not certified intervals". Every regenerated JSON file equals the
shipped one apart from line endings (and `exact_checks.json` also in its
`elapsed_seconds`); `finite_moments.csv` is byte-identical to the shipped
file. **CRLF hazard:** on Windows, Python writes the JSON files with CRLF line
endings, whereas the shipped JSON files are LF; the CSV writer uses
`newline=''` with the `csv` module's `\r\n` terminator, so it writes CRLF on
every platform, which is why the delivered CSV is CRLF and why it carries a
`-text` line in `SetTheory/Cardinals/.gitattributes`. Do not copy regenerated
outputs back over the shipped files; compare them with `diff
--strip-trailing-cr` or after removing CRs. The shipped Part V figure PDFs
are the figures of this run (see "Discrepancies"); a new run differs from
them in its PDF metadata. Independently, for this
write-up, the regularized formula for `𝔪(p)` was evaluated with mpmath at
`p = 3/4, 1, 3/2, 2, 3` and agreed with Part IV's integral for `𝔪_p` to
twenty digits; its value `−2.575500874573932` at `p = 1/4`, the finite part
`B_1 = 0.382498798145934` at the pole, and `c_mac` were recomputed from the
closed forms.

**Part VI.** Its programs use the delivered names and write into the
delivered `data/` and `figures/`, **overwriting their own recorded outputs**
there. Run in place here they misbehave: `07-polynomial-rarity-verify.py`
fails with `ImportError`, because its `from model import …` loads Part I's
`code/model.py`, which has no `EndpointCounter`; were the import to succeed,
it would write new unprefixed `data/phase_counts.csv`,
`data/crossover_counts.csv` and `data/verification_log.txt` into this
directory. `07-polynomial-rarity-figures.py` reads `data/phase_counts.csv`,
which does not exist here, and would write unprefixed PDFs and PNGs into
`figures/`; and the Makefile expects the package root. Restore the delivered
layout in a scratch copy (Git Bash or another POSIX shell, from this
directory):

```sh
W=/path/to/scratch
k=07-polynomial-rarity
mkdir -p "$W/$k/code" "$W/$k/data" "$W/$k/figures"
for d in code data figures; do
  for f in $d/$k-*; do cp "$f" "$W/$k/$d/${f#$d/$k-}"; done
done
mv "$W/$k/code/Makefile" "$W/$k/"
cd "$W/$k"
py code/verify.py                  # standard library, no -O; rewrites data/phase_counts.csv,
                                   #   data/crossover_counts.csv, data/verification_log.txt
printf 'pdf.fonttype: 42\n' > matplotlibrc   # TrueType instead of Type 3 fonts
uv run --no-project --with numpy==2.3.5 --with matplotlib==3.10.8 python code/figures.py
                                   # rewrites figures/{phase_exponents,finite_counts}.{pdf,png}
```

These were run this way on 30 September 2026 (`py` was Python 3.14.4; the
`uv` run used Python 3.13.5 with NumPy 2.3.5 and Matplotlib 3.10.8). The
verifier passed all seven checks with the recorded counts (permutations
through `n = 7`, 54 endpoint counts, 60 lower-construction cases with 13,431
objects, 276 sandwiches through `n = 24`, the `3 < 5` regression, 20 phase and
18 crossover samples) in about 14 seconds; both regenerated CSVs are
byte-identical to the shipped ones, and the log differs only in its
"Elapsed seconds" line and in its line endings. **CRLF hazard:** the CSV
writer uses `newline=''` with the `csv` module's `\r\n` terminator, so it
writes CRLF on every platform, which is why the two delivered CSVs are CRLF
and carry `-text` lines in `SetTheory/Cardinals/.gitattributes`; on Windows,
`write_text` also writes the log with CRLF, whereas the shipped log is LF. Do
not copy regenerated outputs back over the shipped files; compare them with
`diff --strip-trailing-cr`. The shipped Part VI figure PDFs are the figures of
this run (see "Discrepancies"); a new run differs from them in its PDF
metadata. Independently, for this write-up, every count and both envelope
columns of the 20 phase samples, and every count of the 18 crossover samples,
were recomputed with Part I's own counter `code/model.py` (`counts`,
`majorant_counts`, `block_counts` with `d = 1`; 0 mismatches, read-only
import), and Table 26 was checked against the CSV to six decimals.

**Part VII.** Its verifier uses the delivered names and writes beside
itself, **overwriting its own recorded outputs** there. Run in place here it
fails: `08-half-size-crossover-verify.py` does `from model import
EndpointCounter, avoiders, catalans, max_jump`, which in `code/` loads
Part I's `code/model.py`, which has no `EndpointCounter`, so it stops with an
`ImportError`; were the import to succeed, it would write new unprefixed
`code/finite_checks.csv` and `code/verification.json` (it writes to its own
directory, `Path(__file__).resolve().parent`). `08-half-size-crossover-build.sh`
needs the unshipped manuscript. Restore the delivered layout in a scratch
copy (Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
k=08-half-size-crossover
mkdir -p "$W/$k"
cp code/$k-model.py  "$W/$k/model.py"     # the credited model; same blob as code/07-polynomial-rarity-model.py
cp code/$k-verify.py "$W/$k/verify.py"
cd "$W/$k"
py verify.py                 # standard library, no -O; rewrites finite_checks.csv and verification.json here
py verify.py --max-n 256     # adds n = 192 and 256 to the table; several minutes
```

The default run was done this way on 30 September 2026 (Python 3.14.4): it
passed (`"status": "PASS"`, 36 endpoint counts, 5,599 parser
reconstructions, 200 word-coefficient equalities, masses 3 and 8) in about
21 seconds (the delivered record says 8.3). The regenerated
`finite_checks.csv` is byte-identical to the shipped one, and
`verification.json` differs only in `elapsed_seconds` and in its line
endings. **CRLF hazard:** the CSV writer uses `newline=''` with the `csv`
module's `\r\n` terminator, so it writes CRLF on every platform, which is why
the delivered CSV is CRLF and carries a `-text` line in
`SetTheory/Cardinals/.gitattributes`; on Windows `write_text` also writes the
JSON with CRLF, whereas the shipped JSON is LF. The shipped
`verification.log` is the delivery's capture of the script's standard
output, not a file the script writes. Do not copy regenerated outputs back
over the shipped files; compare them with `diff --strip-trailing-cr`. The
`--max-n 256` run was not repeated in full here (it exceeded a three-minute
limit); its two extra rows, the values 5.194724686827719 and
5.302598836522250 of Table 28, were reproduced independently, for this
write-up, to eight decimals by a floating-point evaluation of the endpoint
recurrence (validated against 38 exact counts to a relative error of
6·10⁻¹⁶). Also independently, for this
write-up: the eight counts at `n = 64` and `96` in the CSV were recomputed
with Part I's own counter `code/model.py` (a different implementation;
0 mismatches, read-only import), and the four rows shared with Part VI's
CSVs agree; `I_3(1/2) = 12π` was confirmed by quadrature to 3·10⁻¹⁶, and
`I_3(2/5)/(2π) = 0.469269`, `I_3(9/20)/(2π) = 1.636248`; the masses `1/2`
(one large `R` letter) and `1` (terminal core) of Remark 83.3 were
recomputed exactly with SymPy 1.14.0; and the same floating-point
evaluation up to `n = 800` is consistent with the two theorems without
testing them (a three-term fit
`A + B n^(-1/2) + C/n` gives `A ≈ 0.4615` at `θ = 2/5` against
`I_3(2/5)/(2π) = 0.4693`, `A ≈ 1.639` at `θ = 9/20` against `1.636`, and
`A ≈ 6.02` at `θ = 1/2` against `6`). At `n` = 255, 256, 257 the values
`n p_n(⌊n/2⌋)` = 5.109, 5.303, 5.113 show a finite-size parity effect of
about `3/sqrt(n)`, which vanishes in the limit.

**Part VIII.** Its verifiers use the delivered names and write beside
themselves, **overwriting their own recorded outputs** there. Run in place
here they fail: `09-general-crossovers-verify.py` does `from model import
EndpointCounter, avoiders, max_jump` (line 21), which in `code/` loads Part I's
`code/model.py` (no `EndpointCounter`), and it also checks the SHA-256 of a
`model.py` beside itself (lines 196–197); were it to run, it would write
unprefixed `results.json` (or `quick_results.json`),
`third_boundary_counts.csv` and `third_window_counts.csv` into `code/`
(lines 217–220); `09-general-crossovers-verify_integral.py` writes
`integral_symbolic.json` beside itself (line 26). Restore the delivered
`checks/` layout in a scratch copy (Git Bash or another POSIX shell, from this
directory):

```sh
W=/path/to/scratch
k=09-general-crossovers
mkdir -p "$W/$k"
cp code/07-polynomial-rarity-model.py "$W/$k/model.py"   # the credited model, byte-identical to the delivered checks/model.py
cp code/$k-verify.py          "$W/$k/verify.py"
cp code/$k-verify_integral.py "$W/$k/verify_integral.py"
cd "$W/$k"
py verify.py --quick         # small exhaustive checks only; writes quick_results.json here
py verify.py                 # standard library, no -O; rewrites results.json and both CSVs here
uv run --no-project --with sympy==1.14.0 python verify_integral.py   # rewrites integral_symbolic.json here
```

This was done on 1 October 2026 (Python 3.14.4): `--quick` passed in about
2 seconds and the full run in about 16 seconds (`PASS: channel masks
p=2,...,14; literal enumeration and all endpoint states n=1,...,8`, then the
five one-third rows). Both regenerated CSVs are byte-identical to the shipped
ones; `results.json` differs only in `"python_version"` (3.14.4 against the
delivered 3.12.14) and in its line endings; `integral_symbolic.json` (SymPy
1.14.0, about 9 seconds) is identical apart from line endings. **CRLF
hazard:** the CSV writer uses `newline=''` with the `csv` module's `\r\n`
terminator, so it writes CRLF on every platform, which is why the delivered
CSVs are CRLF and carry `-text` lines in `SetTheory/Cardinals/.gitattributes`;
on Windows `write_text` also writes the JSON files with CRLF, whereas the
shipped JSON files are LF. Do not copy regenerated outputs back over the
shipped files; compare them with `diff --strip-trailing-cr`. The delivered
README says `python3`, which on this machine may resolve to the Windows app
alias; use `py`.

Independently, for this write-up (none of it shipped): an endpoint recurrence
written from the maximum decomposition, sharing no code with the credited
model, agrees with literal enumeration for `1 ≤ m ≤ n ≤ 8` and reproduces the
five exact one-third counts digit for digit; its floating-point version, to
`n = 1050`, gives the convergence evidence of Section 99.1; mpmath quadratures
confirm `I_3(1/2) = 12π`, `I_4(1/3) = 8 sqrt(2) π` (also through `𝒥(9)` and
both integral reductions, which the SymPy check takes as inputs),
`𝔎_3 = 5/sqrt(2π)`, `𝔏_2`, `𝔏_3` and the derivation
`ϰ_r r^(3r/2) r^(r−1)/(r−1)! = 𝔏_r` for `r = 2..8`, the reduction
`ϰ_2 I_2(θ)` = Part IV's profile at `θ = 0.6, 0.75, 0.8, 0.9`, and the
lower-edge expansion of Remark 91.4 for `r = 2, 3, 4`; and two nested
pair-convolution quadratures agree on `I_5(1/4) ≈ 35.6357`, so
`𝔎_4 ≈ 0.6770`.

## Discrepancies and delivery names

- **Delivery names.** The Part II scripts and records use the delivered paths
  `code/verify.py`, `code/model.py`, `data/*.json`, `data/*.csv` and
  `figures/remainder_corridor.*`, `figures/corridor_width.*`; the recipe above
  recreates them in a copy. The article quotes the shipped names.
- **Unshipped PDF.** `data/02-centered-remainder-pdf_validation.json` and
  `data/02-centered-remainder-pdf_fonts.txt` describe the manuscript's
  delivered 23-page PDF, which is not shipped; `article.pdf` here is a new
  build of the merged text (200 pages since batch 72).
- **Duplicates.** Each Part II console capture is byte-identical to the JSON
  it prints, and `data/02-centered-remainder-environment.json` is
  byte-identical to Part I's `data/environment.json` (the same environment).
- **Requirements.** Part II's delivered `requirements.txt` (shipped as
  `data/02-centered-remainder-requirements.txt`) gives lower bounds
  (`numpy>=1.24`, `scipy>=1.10`, `sympy>=1.12`, `matplotlib>=3.7`); the
  versions actually used are those in its environment file, the same as
  Part I's exact pins in `requirements.txt`.
- **Table rows.** Table 8 of the article omits the `m = 30` row of
  `data/02-centered-remainder-component_numerics.csv`, as the manuscript did.
- **Part I's delivered files.** Part I's text and its data files predate the
  addition; the sentences of Part I that called the convergence of `E_m`
  open (Theorem 1.3, Section 9) now carry dated pointers to Part II, and its
  other files are unchanged.
- **Part III delivery names.** The Part III scripts use the delivered paths
  `code/model.py`, `data/verification.json`, `data/symbolic_verification.json`,
  `data/limit_probabilities.csv`, `data/finite_histograms.csv`,
  `data/extreme_jump_exact.csv` and `figures/tail_scaling.*`,
  `figures/finite_probabilities.*`; `code/03-largest-jump-build.sh` expects
  the manuscript's `article.tex` beside it. The three audit notes
  (`03-largest-jump-PROOF_STATUS.md`, `-SOURCES.md`, `-VALIDATION.md`) also
  speak of `article.tex`, `SOURCES.md`, `PROOF_STATUS.md`, `data/…` and
  `build.sh` under their delivered names, and of `figures/` holding PNG files.
  The recipe above recreates the delivered layout; the article quotes the
  shipped names. Manuscript 02 ships no Makefile.
- **Part III's unshipped PDF.** `03-largest-jump-VALIDATION.md` describes the
  manuscript's delivered 26-page US Letter PDF (built with TeX Live 2025, and
  by the delivered `build.sh`), and its core-test record names Python 3.13.5;
  that PDF is not shipped, and the reruns above used Python 3.14.4.
- **Part III duplicate record.** `data/03-largest-jump-verification.txt` is
  byte-identical to `data/03-largest-jump-verification.json`.
- **Part III scope wording.** The manuscript and its notes describe its target
  as the joint limit in `n` and `m` that this README excluded. The report
  records it as answering that question only in the boundary regime
  (Section 21.3), and the README bullet and Part II's research direction keep
  their wording with dated pointers.
- **Parts I–II text since batch 43.** The abstract, Part I's remark on the
  order of limits (Section 1), Part I's Appendix B, Part II's Remark 11.2, its
  research direction 19.5 and its ledger (Table 10) carry dated pointers to
  Part III; nothing else in Parts I–II changed.
- **Parts I–III text since batch 52.** The abstract gained a batch-52
  paragraph and the title page four shorter vertical spaces (see "Build the
  article"); Part II's research direction 19.5 and its ledger (Table 10),
  Part III's scope paragraph (Section 21.3), Remark 29.3, Remark 30.2, its
  audit table (Table 13), its research questions 32.1 and 32.2, and Part I's
  Appendix B carry dated pointers to Part IV, with their original wording
  kept; five Part III question headings gained `mj:` labels (see "Labels").
  Nothing else in Parts I–III changed.
- **Part IV delivery names.** The Part IV scripts use the delivered paths
  `code/model.py`, `data/verification.json`,
  `data/exact_small_distributions.csv`, `data/simulation.csv`,
  `data/symbolic_verification.json`, `data/bulk_counts.csv`,
  `data/moment_counts.csv` and unprefixed `figures/` names;
  `code/04-macroscopic-jump-simulate.cpp`'s header comment gives the delivered
  build and run commands. `04-macroscopic-jump-SOURCES.md` names
  `data/verification.json`; `05-macroscopic-deficits-SOURCES.md` names
  `code/model.py` and the manuscript's Appendix A (printed as Section 46.3).
  The recipe above recreates the delivered layouts; the article quotes the
  shipped names.
- **Part IV's unshipped PDFs and environments.**
  `data/04-macroscopic-jump-build_audit.json` and
  `data/05-macroscopic-deficits-package_audit.json` describe the manuscripts'
  delivered 23- and 24-page US Letter PDFs (their page counts, box
  diagnostics and visual reviews), which are not shipped; `article.pdf` here
  is a new A4 build of the merged text. Both audits and
  `data/05-macroscopic-deficits-environment.json` record Python 3.13.5 (the
  latter on Linux); the reruns above used Python 3.14.4 on Windows.
- **Part IV figures.** The delivered figure PDFs embedded Type 3 fonts
  (DejaVu Sans, and STIX in manuscript 11's). In the write phase the four
  PDFs were regenerated by the shipped plot scripts, unchanged, on copies of
  the delivered layouts, with Matplotlib 3.10.8, NumPy 2.3.5 and
  `pdf.fonttype: 42` in a local `matplotlibrc`; they now embed TrueType (CID)
  fonts and plot the shipped data. They are therefore not byte-identical to
  the deliveries. The PNG previews were not replaced: they are the delivered
  files (a PNG regenerated here differs from them in its bytes), and the
  article uses only the PDFs. Figure 9's legend still names the profile
  `Φ(x)`, manuscript 11's symbol for Part IV's `Ψ(u)`; its caption says so.
- **Part IV provenance.** Manuscript 10 read a file outside the repository:
  the standalone Part III source `article(20260929-161704).tex` from
  Vladimir's file library (`04-macroscopic-jump-SOURCES.md`). Its statements
  about Part III therefore rest on that file and on the repository at
  `1ee53d57d`, whose Part III text is the one printed here.
- **Part IV figure and table choices.** Figure 7 plots only the samples at
  `n = 1,024` and `16,384` of the five in `data/04-macroscopic-jump-simulation.csv`,
  as delivered; Figure 9 plots the ten exact cases of
  `data/05-macroscopic-deficits-bulk_counts.csv`, of which Table 15 prints
  all ten.
- **Parts I–IV text since batch 64.** The abstract gained a batch-64
  paragraph and the title page an `\enlargethispage` (see "Build the
  article"); Part III's research question 32.2, Part IV's scope list
  (Section 37.3), its paragraph on what neither manuscript claims
  (Section 38.6), its remark after Proposition 44.1, its research question
  47.6, its scope table (Table 17) and Part I's Appendix B carry dated
  pointers to Part V, with their original wording kept; six Part IV question
  headings gained `cjm:` labels (see "Labels"). Nothing else in Parts I–IV
  changed.
- **Part V delivery names.** The Part V scripts use the delivered paths
  `data/exact_distributions.json`, `data/pgf_coefficients.json`,
  `data/exact_checks.json`, `data/symbolic_checks.json`,
  `data/constants.json`, `data/finite_moments.csv` and unprefixed
  `figures/` names; `code/06-critical-moments-build.sh` expects the
  manuscript's `article.tex` beside it. `06-critical-moments-SOURCES.md`
  speaks of `SOURCES.md`, of the manuscript's "Appendix A" (printed as
  Section 64) and of "Part IV: Theorem 38.1" (still Theorem 38.1 here), and
  cites "source lines 231–249" of the README at the pin, whose passage is now
  the "Not claimed" bullets on Parts III and IV above (with batch-64 notes).
  `06-critical-moments-PROOF_STATUS.md` names `SOURCES.md` and writes the
  constants as `h`, `j`, `a`, `B0`, `B1`, `c_star` (Part V's `c_mic`,
  `c_mac`, `𝔞`, `B_0`, `B_1`, `c_⋆`); the data files use the same names
  (`h`, `j`, `A` for Part V's `𝓡`, `K_values` for `𝔪(p)`). The recipe above
  recreates the delivered layout; the article quotes the shipped names.
- **Part V's unshipped PDF and wording.** `data/06-critical-moments-pdf_quality.json`
  audits the delivered 27-page US Letter PDF, which is not shipped;
  `article.pdf` here is a new A4 build of the merged text. The delivered
  title page, PDF metadata and README describe the manuscript as prepared for
  Vladimir Reshetnikov; the article records it only as an AI-assisted
  manuscript, in its provenance section. The delivered README asks for
  Python 3.11 or later and writes `python`; the recipe above uses `py` and
  `uv`.
- **Part V figures.** The delivered figure PDFs embedded Type 3 fonts
  (DejaVu Sans, and STIX in `centered_moment.pdf`). In the write phase they
  were regenerated by the shipped `figures.py`, unchanged, on a copy of the
  delivered layout with Matplotlib 3.10.8, NumPy 2.3.5 and
  `pdf.fonttype: 42` (the recipe above); they now embed TrueType (CID) fonts
  and plot the shipped data, and are therefore not byte-identical to the
  delivery. Their axis labels still write `t = log D_n/log n` and the
  critical moment as `E sqrt(D_n) − (3/(2 sqrt(π))) log n`; the article's
  symbol for `t` is `ϑ_n`, and the captions say so.
- **Parts I–V text since batch 68.** The abstract gained a batch-68
  paragraph (the title page still fits; see "Build the article"); Part II's
  research direction 19.5, Part IV's scope list (Section 37.3), its paragraph
  on what neither manuscript claims (Section 38.6), its edge at one half
  (Section 43.1), its remark after Theorem 45.1, its research questions 47.1
  and 47.2, its scope table (Table 17) and "What is resolved" (Section 48.2),
  Part V's scope (Section 62) and its research question 63.3, and Part I's
  Appendix B carry dated pointers to Part VI, with their original wording
  kept; four question headings of Parts IV and V gained `pr:` labels (see
  "Labels"). Nothing else in Parts I–V changed.
- **Part VI's source ledger misdescribes one identifier.** Line 13 of
  `07-polynomial-rarity-SOURCES.md` says that its initial
  `/git/trees/main?recursive=1` request returned
  `f4457a1d19701d32e8f324240c497653d235b53e`, "the root-tree identifier",
  and that this "is NOT a commit identifier". In this repository
  `f4457a1d1` **is a commit**: the arrival commit of batch 67 (30 September
  2026, 16:35:42 −07:00), whose root tree is `32b9d20237`. The pinned commit
  `ffddaa8b9` and its root tree `cb9c68b025` (lines 9–11) are correct, and the
  three blobs the ledger lists are the same at `f4457a1d1`, at the pin and at
  the placement commit, so the error affects neither the mathematics nor the
  provenance of Part VI. The ledger is shipped byte-identical; Section 78.1
  prints the correction. Its line 53 also calls the endpoint derivation
  "Appendix A" (printed as Section 76), and line 27 calls the report
  "approximately 140-page" (it then had 141 pages).
- **Part VI delivery names.** The Part VI programs use the delivered paths
  `code/model.py`, `data/phase_counts.csv`, `data/crossover_counts.csv`,
  `data/verification_log.txt` and unprefixed `figures/` names, and the
  Makefile calls `python code/verify.py`, `python code/figures.py` and
  `latexmk … article.tex` from the package root. `07-polynomial-rarity-SOURCES.md`
  names only the repository files it inspected (`README.md`, `code/model.py`,
  `code/05-macroscopic-deficits-model.py`), under their shipped names; the
  docstring of `code/07-polynomial-rarity-model.py` names
  `05-macroscopic-deficits-model.py`, also a shipped name. The recipe above
  recreates the delivered layout; the article quotes the shipped names. The
  delivered README (not shipped) asks for
  Python 3.10 or later and writes `python`; the recipe above uses `py` and
  `uv`. A comment in `code/07-polynomial-rarity-verify.py` calls the
  `1/(1 − K_m)` bound "the invalid stronger majorant from the repository";
  the report never asserts it, and Part II warns against it
  (Remark 12.4).
- **Crossover samples outside the theorem's range.** In
  `data/07-polynomial-rarity-crossover_counts.csv`, `m` is
  `round(n/q + t·n^(1 − 1/(2(q−1))))` with `t = −1/4, 0, 1/4`. At `n = 64` and
  `96` the scale is so large that six of the 18 samples lie outside the open
  ratio interval `(1/(q + 1), 1/(q − 1))` of Theorem 68.2: for `q = 3`,
  `t = −1/4` gives `m/n = 1/4` exactly (both sizes), and for `q = 4`,
  `t = ±1/4` gives `m/n` of about 0.13 and 0.37. Their `ratio_to_proxy`
  values (0.26–0.34, 0.0004–0.0006 and 30–34) are therefore not covered by the
  theorem; the other twelve are. The manuscript prints none of these rows, and
  its verifier labels the proxy "not a limiting function".
- **Part VI's unshipped PDF and wording.** The delivered 25-page US Letter
  PDF is not shipped; `article.pdf` here is a new A4 build of the merged text.
  The delivered title page, running head, PDF metadata and README describe
  the manuscript as prepared for Vladimir Reshetnikov; the article records it
  only as an AI-assisted manuscript, in its provenance section.
- **Part VI figures.** The delivered figure PDFs embedded Type 3 fonts
  (DejaVu Sans). In the write phase they were regenerated by the shipped
  `figures.py`, unchanged, on a copy of the delivered layout with Matplotlib
  3.10.8, NumPy 2.3.5 and `pdf.fonttype: 42` (the recipe above); they now
  embed TrueType (CID) fonts and plot the shipped data, and are therefore not
  byte-identical to the delivery. The PNG previews are the delivered files.
  The axis label of Figure 15 writes `Pr` for the article's `P`; its caption
  says so.
- **Part VII delivery names.** `code/08-half-size-crossover-verify.py`
  imports `model` and writes `finite_checks.csv` and `verification.json`
  beside itself (lines 11, 42, 77 and 83), and its docstring says "Run python
  verify.py" and "The credited endpoint model is shipped as model.py";
  `code/08-half-size-crossover-build.sh` builds `half_size_crossover.tex`
  beside itself, which is not shipped (its text is Part VII);
  `data/08-half-size-crossover-validation.json` names `verification.json`
  and describes the delivered 8-page PDF, which is not shipped; and
  `08-half-size-crossover-SOURCES.md` names `model.py` and `verify.py`. All
  these are delivery names. The recipe above recreates the delivered layout;
  the article quotes the shipped names. The delivered README (not shipped)
  asks for Python 3.11 or later and writes `python`; the recipe uses `py`.
- **Part VII duplicates.** `code/08-half-size-crossover-model.py` is
  byte-identical to `code/07-polynomial-rarity-model.py` (Git blob
  `a4fdee3761`): the manuscript copied Part VI's model and credits it
  (`08-half-size-crossover-SOURCES.md`, line 13). Its docstring credits "the
  Mayama--Akita recurrence and ProveIt's 05-macroscopic-deficits-model.py",
  a shipped name. `data/08-half-size-crossover-verification.log` is
  byte-identical to `data/08-half-size-crossover-verification.json`; it is
  the delivery's capture of the script's standard output.
- **"Independent" generation.** The delivered README (line 10) calls the
  verifier's generator "independent finite Catalan generation", the
  manuscript (Section 88.1) speaks of "independent generation of every
  132-avoider through size eight", and `08-half-size-crossover-SOURCES.md`
  (line 13) says that the verifier "independently generates all avoiders
  through size eight". The generator is `avoiders` of the credited model module, which
  builds avoiders by the maximum decomposition; generator and endpoint
  counter are different algorithms in one module, and the Part VII verifier
  does not test the generator against the 132 predicate. Part VI's verifier
  did, for the same module, through `n = 7` (Section 88.1 prints a merge note).
- **"Explicit error bounds".** The delivered README (line 23) says the
  manuscript gives "ordinary mathematical proofs with explicit error bounds".
  It does not: its proofs give limits without explicit error terms, and its
  Section 9 says "No finite-size error rate is asserted here" (printed in
  Section 88.1); quantitative errors are its third further question
  (Section 89.3).
- **Part VII's pin predates Part VI.** The pin `29e52fcdf` is batch 68's
  placement commit; Part VI was written later, in `cfdefe6e3`. So
  `08-half-size-crossover-SOURCES.md` (lines 7 and 11) and the manuscript
  (its Section 9) describe this article as ending at Part V and the Polynomial
  Rarity manuscript as an incoming archive whose article was "not staged";
  both were true at the pin and are stale now. The article prints the
  manuscript's sentence with a merge note (Section 88.3) and cites Part VI by
  label wherever the manuscript cites the incoming manuscript.
- **One terse step.** The manuscript's bound "Their total is bounded by
  `4(1/2)^j`" (after Lemma 83.1) does not say where `(1/2)^j` comes from, and
  under one reading (summing the gap letters too) it is false (the bound would
  be `4·2^j`). The step is printed as delivered and followed by the
  editorial Remark 83.3, which justifies it: each large `R` letter carries
  total normalized mass `1/2`, the core `1`, and the gaps are controlled by
  the suppression bound; the conclusion `o(n^(-1))` stands.
- **Part VII's unshipped PDF, wording and date.** The delivered 8-page US
  Letter PDF is not shipped; `article.pdf` here is a new A4 build of the
  merged text. The delivery's byline and PDF metadata read "AI-assisted
  mathematical research" (metadata "AI assisted mathematical research"); no
  addressee is named. The manuscript and its ledger are dated
  1 October 2026, the UTC date of the arrival commit `aee32ad45`
  (30 September 2026, 19:45 −07:00); the dated notes of batch 71 use the
  same date.
- **Parts I–VI text since batch 71.** The abstract gained a batch-71
  paragraph (the title page still fits; see "Build the article"). Dated
  pointers to Part VII were added, with the original wording kept, to
  Part II's research direction 19.5, Part IV's scope list (Section 37.3), its
  paragraph on what neither manuscript claims (Section 38.6), its edge at one
  half (Section 43.1), its remark after Theorem 45.1, its research questions
  47.1 and 47.2, two rows of its scope table (Table 17) and "What is
  resolved" (Section 48.2), Part V's scope (Section 62) and its research
  question 63.3, Part VI's status box (Section 67.1), its answer list
  (Section 67.2), Corollary 68.4, the caption of Table 26 and its research
  questions 74.1–74.5, and Part I's Appendix B. No label of Parts I–VI was
  added, renamed or removed, and nothing else in them changed.
- **Part VIII delivery names.** `code/09-general-crossovers-verify.py`
  imports `model`, checks the SHA-256 of a `model.py` beside itself and writes
  `results.json`, `quick_results.json` and the two CSVs beside itself (lines
  21, 196–197, 217–220); `code/09-general-crossovers-verify_integral.py`
  writes `integral_symbolic.json` beside itself (line 26);
  `code/09-general-crossovers-build.sh` builds
  `general_avoider_crossovers.tex` beside itself, which is not shipped (its
  text is Part VIII); `09-general-crossovers-CHECKS.md` (the delivered
  `checks/README.md`) says "From this directory … `python verify.py`" and
  names `model.py`, `results.json` and the CSVs by their delivered names;
  `data/09-general-crossovers-validation.json` describes the delivered
  8-page PDF, which is not shipped; and `09-general-crossovers-SOURCES.md`
  says the model's lineage is "recorded in `checks/README.md`", which is
  `09-general-crossovers-CHECKS.md` here. All these are delivery names. The
  recipe above recreates the delivered layout; the article quotes the shipped
  names. The delivered README (not shipped) writes `python3`; the recipe uses
  `py`.
- **Part VIII's model is not shipped a third time.** The delivered
  `checks/model.py` is byte-identical to `code/07-polynomial-rarity-model.py`
  and `code/08-half-size-crossover-model.py` (Git blob `a4fdee3761`, SHA-256
  `c693d805…`, which `09-general-crossovers-CHECKS.md` records and the
  verifier checks); the recipe copies Part VI's file under the delivered name.
- **Part VIII's channel check.** The manuscript (Section 99.1) speaks of
  "exact finite endpoint-prefix checks of" the accepted mass. The verifier
  passes every binary gap mask through an endpoint-channel automaton under the
  pair-sum geometry, for `p = 2..14`, and counts the `p + 1` accepted
  channels; it is a check of that count, not a check against permutations,
  as `09-general-crossovers-CHECKS.md` itself says. The article prints a merge
  note. Its literal enumeration of all `n!` permutations under the 132
  predicate (`n ≤ 8`) is genuinely independent of the generator, unlike
  Part VII's check.
- **Part VIII's self-citation and pin sentence.** The manuscript cites this
  report as an external bibliography item ("combined article at commit
  `7421a4ca60fd`"); the article prints those citations as references by label.
  Its sentence "The source pin is the current combined article containing
  Parts VI and VII, not its earlier incomplete merge" refers to Part VII's
  older pin `29e52fcdf`, at which this article ended at Part V; it is printed
  with a merge note (Section 99.3).
- **One unproved bound, again.** The manuscript's "that mass is at most a
  fixed constant times `(1/2)^j`" (Section 93) is asserted without proof, as
  in Part VII; the article cites Part VII's editorial Remark 83.3, which
  supplies it, in a merge note.
- **Part VIII's unshipped PDF, byline and date.** The delivered 8-page A4 PDF
  is not shipped; `article.pdf` here is a new build of the merged text. The
  delivery's byline and PDF metadata read "Research note prepared for Vladimir
  Reshetnikov with OpenAI". The manuscript is dated 1 October 2026, the date
  of the arrival commit `1512ef835`.
- **Parts I–VII text since batch 72 (Part VIII).** The abstract gained a
  batch-72 paragraph, and the title page's scope box and companion-archive
  line moved to page 2 (see "Build the article"). Dated pointers to Part VIII
  were added, with the original wording kept, to Part II's research direction
  19.5, Part IV's scope list (Section 37.3), its paragraph on what neither
  manuscript claims (Section 38.6), its remark after Theorem 45.1, its
  research questions 47.1 and 47.2, two rows of its scope table (Table 17) and
  "What is resolved" (Section 48.2), Part VI's status box (Section 67.1), its
  answer list (Section 67.2), its Section 71.5 on the sense of "window", the
  caption of Table 26 and its research questions 74.1–74.5, Part VII's answer
  list (Section 79.2) and its research questions 89.1–89.4, and Part I's
  Appendix B. No label of Parts I–VII was added, renamed or removed, and
  nothing else in them changed.

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats these permutations,
and none of Parts II–VIII names a neighbouring report, so no reciprocal note
was written; the dated pointers of Parts IV, V, VI, VII and VIII are all inside
this report (a search of the collection for 132-avoidance, re-run on
30 September 2026 for batch 71, finds only this report, the catalogue and
copies of its manifest inside other reports, and notes of other reports that
name this one, e.g. to exclude it; none treats these permutations). Part V is a
probabilistic moment-transfer argument, Part VI a renewal-sandwich order
argument and Parts VII and VIII parser-and-Riemann-sum limit arguments, none
of them transseries work; the transseries volume's README already sent Part IV's two
manuscripts here on the same ground.
The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration anywhere in ProveIt formalizes any statement of Parts I–VIII (a
search of the repository's tracked `.lean` and `.v` files for 132-avoidance,
adjacency bounds or largest jumps finds none, re-run on 30 September 2026,
batch 71, and on 1 October 2026 for batch 72; Parts VII and VIII name no
Lean or Rocq file or declaration).
Section 19.9 records the formalization targets manuscript 04 of batch 38
proposes (the renewal polynomial identity, the supersolution argument, the
skew-cut injection, the uniform tail inequality), Section 32.9 those of
manuscript 02 of batch 43 (the deterministic reconstruction lemma and
injectivity, then the first-entry formula and the common-submeasure
inequality), and Section 47.13 those of batch 52's manuscripts 10 and 11
(the finite decomposition, the root recursion, endpoint counts and
stopping-word injection, then the tail envelope, the Riemann-sum source
theorem and the contraction argument; the threshold parser, the word
identities, the convolution tail estimate and the fixed-word acceptance
lemma), and Section 63.10 those of batch 64's manuscript 06 (the abstract
transfer theorem for real exponents on a compact interval, then the critical
half-moment and the bounded-Lipschitz estimate, with the three inputs from
Parts III and IV as separate interfaces), and Section 74.10 the staged plan of
batch 68's manuscript 05 (a finite combinatorial layer: maximum
decomposition, skew sums, unique skew-indecomposable factorization and the
injection behind the lower envelope; a formal-series layer: coefficientwise
inequalities and the marked expansion; an analytic layer: the local tail
bound, the exponential tilt and the composition bounds of the renewal
theorem); none has been started.

## Sources and attribution

Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*,
arXiv:2604.22135v1, Conjecture 2 in Section 5.2.
https://arxiv.org/abs/2604.22135

Teruki Mayama and Dai Akita, *Finite-state enumeration of adjacency-constrained
132-avoiding permutations*, arXiv:2605.23519v1, especially Theorem 2.4,
Proposition 2.7, Theorems 4.12 and 4.14, and Problems P1–P4.
https://arxiv.org/abs/2605.23519

The finite-state system, rationality, existence of the growth constants,
non-strict monotonicity, and the earlier O(log(m)/m) bound are established
work and are credited in the article. Part I's new arguments are the shift
embedding, its strict-growth consequence and the refined asymptotic
comparison; Part II's are the Catalan-weighted spectral upper bound, the
uniform tail and growing-cutoff corridor, the exact constant and the
all-orders expansion; Part III's are the absorbing skeleton decomposition and
its reconstruction lemma, the counting-domination rate, the exact clipping
calculation and algebraic law, and the boundary joint limits and moment
transition derived from them. Part IV's are, from manuscript 10, the exact
deficit recursion at the maximum, the stopping-word envelope, the marked
renewal equation and its contraction proof, the size-biased law and the
many-block lower bounds; from manuscript 11, the canonical threshold parser,
its rare-scale cost tail and the fixed-word endpoint acceptance calculation
with the universal outer-word law; and, from both, the bulk profile and the
supercritical moment constants. Manuscript 11's exact counts use the
Mayama–Akita endpoint recurrence (Part I's Proposition 2.1), credited as
prior work. Part V's are the locally uniform complex-moment transfer theorem
under a power tail, a uniform survival error and a pointwise profile; its
critical, subcritical, exponent-window and signed two-endpoint consequences;
the evaluation of the critical constants and the Laplace-integral formula for
the microscopic one; the intermediate-scale counterexample and the stability
theorem. Its exact checks also use the Mayama–Akita recurrence, credited as
prior work. Part VI's are the uniform local truncated-renewal estimate for
every tail index `0 < α < 1`, with its local convolution bound and
small-part suppression lemma; the matching upper bounds that complete the
polynomial-order staircase, the reciprocal endpoints, the uniform two-term
comparison and its order-crossover scales; and the renewal-sandwich transfer
principle. Its two envelopes are Part I's and its lower bounds Part IV's,
credited; its exact checks also use the Mayama–Akita recurrence. Part VII's
are the extension of the canonical threshold parser to every adjacency
bound, the exact three-piece endpoint table and its mass eight, the
exclusion of small terminal children and mesoscopic outer words at the scale
`1/n`, the three-piece integral `I_3` with `I_3(1/2) = 12π`, and the two
limit theorems (the half-size ramp `6 + 12 t_+/sqrt(π)` and the equivalent
`I_3(θ)/(2πn)`); its endpoint estimates, parser above half size, word masses
and two-piece weight are Part IV's, and its small-word estimates Part VI's,
re-derived and credited; its exact checks use Part VI's model, credited.
Part VIII's are the endpoint-prefix count and its accepted mass
`2^(p−2)(p + 1)`, the word bounds of every moment order, the family bounds
for many pieces and microscopic terminal children at the rare-event scale, the
shrinking near-cap simplex at `1/r`, the amplitude in every fixed phase and
the crossover limit at every fixed reciprocal threshold, `I_4(1/3) = 8 sqrt(2) π`,
and the conditioned piece, channel and window-mixture laws; its first cases
are Part IV's and Part VII's theorems, its interfaces Part VII's and its word
bounds Parts VI–VII's, credited; its exact checks use Part VI's model,
credited.

Part VI also cites, as related context only, Céline Kerriou and Peter
Mörters, *The fewest-big-jumps principle and an application to random
graphs*, Bernoulli 31(3) (2025) 2525–2543, arXiv:2206.14627; no theorem of
it is used, and the fewest-big-jumps mechanism is not claimed as new. Parts VII
and VIII cite it on the same terms.

Part III also cites, as background only, Svante Janson, *Simply generated
trees, conditioned Galton–Watson trees, random allocations and condensation*,
arXiv:1112.0510, and *Patterns in random permutations avoiding the pattern
132*, arXiv:1401.5679; and it uses the transfer principle of Philippe Flajolet
and Andrew Odlyzko, *Singularity analysis of generating functions*, SIAM J.
Discrete Math. 3(2) (1990) 216–240, whose PDF manuscript 02 records it did
not inspect. No third-party paper PDFs or font files are included.
