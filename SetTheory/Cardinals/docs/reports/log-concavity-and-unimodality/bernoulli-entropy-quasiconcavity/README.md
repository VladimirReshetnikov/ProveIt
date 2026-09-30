# Two-coin counterexamples to the proposed generalized Shepp–Olkin thresholds

**All finite orders above one, exact rational certificates, and the fixed-mean entropy phase diagram; with sharp dimension boundaries for product-Bernoulli entropy (nine bits, ten bits) and exact alphabet-size criteria for product entropy (beyond nine bits)**

This is a research report in three parts. Part I is the original report of
20 September 2026 on the Rényi and Tsallis entropy of the **ordinary sum**
`X_1 + … + X_n` of independent Bernoulli variables. Part II was added on
29 September 2026 in batch 43 of ProveIt's incoming-report intake, from a
manuscript written as this report's extension. It takes up Part I's "most
immediate remaining mathematical question" (Part I, Section 10), whether
universal joint concavity holds for all `0 < q < 1`, for a different
observable: the **joint bit vector** `(X_1, …, X_n)`, equivalently a weighted
sum whose `2^n` subset sums are distinct. For that observable it settles the
question. **For the ordinary sum the question stays open in this report.**
Part III was added on 29 September 2026 in batch 57, from a manuscript written
as Part II's extension. It answers Part II's question Q7 for **full categorical
simplices**: it replaces the independent bits by independent categorical
variables with arbitrary, possibly unequal, finite alphabets, evaluates the
block supremum that Part II's block-product criterion (Theorem 22.1) leaves
open, and recovers Part II's binary results as its two-symbol case. It too
concerns the joint vector, not the ordinary sum. All three parts are
AI-assisted research drafts prepared for Vladimir Reshetnikov.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*Two-coin counterexamples to the proposed generalized Shepp–Olkin thresholds*, 17-page PDF as delivered) | `bernoulli_entropy_research.zip` | (none) | `854a8b4f9` (Cardinals history), in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 5–18) and Appendices A–B (pp. 70–71) |
| 02 | batch 43, manuscript 01 (*Nine Bits, Ten Bits: Sharp dimension boundaries for product-Bernoulli entropy*, 29 Sep 2026, 21-page A4 PDF as delivered) | `proveit_product_entropy.zip` (inner `proveit_product_entropy/`, main file `article.tex`) | `ac9107d74` | `faef2ed2a` (prefix `02-product-entropy-`) | Part II: Sections 11–25 (pp. 19–41) |
| 03 | batch 57, manuscript 04 (*Beyond Nine Bits: Exact Alphabet-Size Criteria and the Shannon Boundary for Product Entropy*, 29 Sep 2026, 24-page A4 PDF as delivered) | `ProveIt_Alphabet_Entropy.zip` (inner `ProveIt_Alphabet_Entropy/`, main file `article.tex`) | `1085b506d` | `70b39943a` (prefix `03-alphabet-entropy-`) | Part III: Sections 26–40 (pp. 42–69) |

The pin `ac9107d74` is ProveIt commit
`ac9107d74083fcfe8064b4aaeda7989612e6a5b6`; the manuscript read Part I's
`article.tex` and `README.md` there. Part I's files are unchanged between the
pin and the placement commit (the placement only added the eleven
`02-product-entropy-` files), so Part II's statements about "the repository
report" refer to the Part I printed here. The archive arrived in `06bcc37a8`.
Its manuscript, PDF, delivery README, two figure PDFs and `SHA256SUMS`
(16/16 verified at placement) are not shipped; they survive in the arrival
commit. Its source notes are shipped verbatim as
`02-product-entropy-SOURCES_AND_STATUS.md`. Part II prints every result,
proof, remark, limitation and question of the manuscript; its Section 11
records the provenance, what is and is not settled, the notation, and where
the write had to choose.

The pin `1085b506d` of Part III is ProveIt commit
`1085b506d65e207a05b7e9c861bb1fe88432fe38`; the manuscript read this report's
`article.tex` (source lines 1470–1770 and 2350–2530, that is Sections 13–16
and 21–24) and `README.md` there. The report's files are unchanged between the
pin and the placement commit `70b39943a` (the placement only added the
eighteen `03-alphabet-entropy-` files; the last earlier change is the Part II
write `b8e46077b`), so the manuscript's "repository report", "Section 22" and
"Section 23" are Parts I–II and Sections 22–23 as printed here. The archive
arrived in `6ad01e9c8`. Its manuscript, delivery README and PDF are not
shipped, and its `SHA256SUMS` (23/23 verified at placement) was retired; they
survive in the arrival commit. Its two figure PDFs, not staged at placement,
are shipped by the write, byte-identical to the delivery. Part III prints
every result, proof, remark, limitation and question of the manuscript; its
Section 26 records the provenance, what is and is not settled, the notation
(Table 4) and where the write had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. All three
parts give written proofs; their exact-arithmetic, symbolic and numerical
suites are finite checks, not substitutes for those proofs. Bibliographic
priority is not certified for any part.

## Results

**Part I** (ordinary sum; unchanged apart from six dated pointers, two-line
Part II and Part III notices on the title page, contents entries for the
three parts, labels on seven headings, a page-anchor fix around the title
page and four bibliography entries used only by Parts II–III):

- For every finite real `q > 1`, Rényi-`q` and Tsallis-`q` entropy of a sum of
  independent Bernoulli variables fail even **quasiconcavity** in the
  Bernoulli parameters, already with two coins at strictly interior rational
  parameters, on a mean-preserving segment with opposite parameter slopes
  (Theorem 1.1, dyadic family Theorem 3.2). This refutes the numerical
  thresholds 2 and 3.65986… proposed beside Conjecture 4.2 of Hillion–Johnson,
  arXiv:1503.01570v1.
- A compact exact witness at `q = 2`: endpoints `(3/20, 1/20)`,
  `(1/20, 3/20)`, midpoint `(1/10, 1/10)`; collision probabilities
  54907/80000 at the endpoints and 55088/80000 at the midpoint; Tsallis
  midpoint deficit 181/80000; Rényi deficit `log(55088/54907)`.
- The sharp balanced-point curvature boundary `p_c(q)` (Theorem 4.2), the
  complete fixed-mean two-coin maximizer classification with boundaries
  `p_b(q) < p_c(q)` (Theorem 5.2) and closed forms at `q = 2`, asymptotics of
  both boundaries (Proposition 6.1), fixed-mean two-coin concavity for
  `0 < q ≤ 1` (Theorem 6.2), minimum dimensions (Tsallis `q > 1`: two coins;
  Rényi `1 < q ≤ 2`: two coins; Rényi `q > 2`: one coin; Propositions 7.1,
  7.2) and interior failures near `(p, …, p)` for every `n ≥ 2`
  (Theorem 8.1).

**Part II** (joint bit vector, equivalently collision-free weighted sums;
manuscript Section `n` is Section `n + 11`, Theorem `n.m` is Theorem
`(n + 11).m`):

- **Sharp universal dimension (Theorem 12.2).** `T_{q,n}` is jointly concave
  on `[0,1]^n` for **every** `0 < q < 1` if and only if `n ≤ 9`; for `n ≤ 9`
  it is strongly concave at each fixed order (Theorem 19.1). For every
  `n ≥ 10` it fails at `q = 20/41`.
- **Fixed-order criterion (Theorem 12.3).** `T_{q,n}` is concave iff
  `n Ψ(q) ≤ 1`, with `Ψ` the maximum of a scalar ratio evaluated at the unique
  root of `tanh((1−q)t) tanh t = 1−q`; the largest concave dimension is
  `N(q) = ⌊1/Ψ(q)⌋`. Via a rank-one Hessian (Lemma 13.1) with exactly one
  possible unstable direction.
- **Nine versus ten.** `Ψ(q) < q(1−q)/(2+q(1−q)) ≤ 1/9` (Theorem 15.2, from an
  elementary hyperbolic inequality, Lemma 15.1); `Ψ(1/2) = 1/10`,
  `N(1/2) = 10` (Theorem 16.1); `Ψ(1/3) = 1/11`, `N(1/3) = 11` (Theorem 16.2);
  `Ψ'(1/2) = (9 − 4√3 log(2+√3))/25 < 0` (Theorem 16.4); a quartic bending law
  at the `2^10` degenerate points of `T_{1/2,10}` (Theorem 16.3).
- **Exact counterexamples at `q = 20/41`.** Local failure reduces to a
  positive 96-digit integer `D_cert` (Theorem 17.1); a certified finite
  midpoint gap `8379718/10^14 < Δ < 8379719/10^14` (Proposition 17.3); with
  weights `w_i = 1 + δ 2^(i−1)`, failure persists at constant weighted mean
  (Theorem 18.2), certified at `δ = 10^−6` with
  `8378699/10^14 < Δ_w < 8378700/10^14` (Proposition 18.3).
- **Other orders.** Product Rényi entropy is concave in every dimension
  exactly for `0 < q ≤ 2` (Theorem 19.2); product Tsallis with `n ≥ 2` is
  concave for `1 ≤ q ≤ 2` and fails quasiconcavity for `q > 2`
  (Theorem 19.3); subunit Tsallis counterexamples remain quasiconcave
  (Proposition 19.4).
- **Endpoints, decisions, blocks.** Asymptotics as `q → 0`
  (`N(q) = 2/q + log(4/q) + O(1)`, Theorem 20.1) and `q → 1`
  (`N(q) = 1/(C(1−q)) + O(1)`, `C = t_*² − 1 ≈ 0.4392288`, Theorem 20.2);
  concavity recovers near both endpoints (Corollary 20.3); an exact algebraic
  decision procedure at rational orders (Theorem 21.1) with the threshold
  table (Table 3: `N` = 206, 24, 12, 11, 10, 9, 10, 10, 13, 26, 230 at
  `q` = 1/100, 1/10, 1/4, 1/3, 2/5, 20/41, 1/2, 3/5, 3/4, 9/10, 99/100); a
  block-product curvature criterion (Theorem 22.1); ten research questions
  Q1–Q10 (Section 23; Q7 is answered for categorical simplices by Part III,
  and a dated note there and after Theorem 22.1 says so).

**Part III** (independent categorical variables; manuscript Section `n` is
Section `n + 26`, Theorem `n.m` is Theorem `(n + 26).m`; its Appendix A is
Section 40):

- **Exact optimizer (Theorem 29.1).** On a simplex `Δ_k` the product
  `S_{1−α} S_{1+α}` of two power sums is maximized exactly at the `k`
  permutations of one large and `k − 1` equal probabilities, with a unique
  scalar optimizer given by a hyperbolic-tangent equation; the maximum
  `Π*_k(α)` is strictly increasing in `k`.
- **Subunit criterion (Theorem 30.3), answering Part II's Q7 for full
  simplices.** The block curvature has the closed form
  `τ_q = q(Π − 1)/(Π − q)` (Lemma 30.1), its maximum is the alphabet profile
  `Θ_k(q)` (Definition 30.2), and for `0 < q < 1` product Tsallis entropy is
  concave on `Δ_{k_1} × … × Δ_{k_n}` iff `Σ_i Θ_{k_i}(q) ≤ 1`, with at most
  one unstable direction; strong concavity under a strict budget and the
  equality geometry (Corollary 30.4); quasiconcavity of Tsallis and strict
  concavity of Rényi entropy always survive (Corollary 30.5).
- **Seventeen versus eighteen symbols (Theorem 31.1).** At `q = 1/2`, three
  factors are (strongly) concave whenever all alphabets have at most 17
  symbols, and for a common alphabet iff `k ≤ 17`; 18 symbols fail for every
  `n ≥ 3`. A sum-of-squares identity (31.4) certifies 17; the rational
  witness `(81/98, 1/98, …, 1/98)` has `Π(p_0) = 4849/2401`,
  `3τ − 1 = 47/7297`, and a rational line gives a certified finite gap
  `88119833628/10^18 < Δ < 88119833629/10^18` (Proposition 31.2). Table 5:
  largest concave factor count at `q = 1/2` for fourteen alphabet sizes
  (`k = 2` gives Part II's ten bits).
- **Rational orders (Theorem 32.1).** An exact real-algebraic decision
  procedure; only the half-order certificate branch is implemented.
- **Large alphabets (Theorems 33.1–33.2).** A convergent expansion
  `Θ_k(q) = q − q(1−q) K^{−(1−q)}/C_q + …`; concavity for **every** finite
  choice of `n` alphabets holds iff `nq ≤ 1`; the first failing alphabet near
  `q = 1/n` (Corollary 33.3); the endpoint limits and the varentropy constant
  `V_k` (Proposition 33.4; `V_2 = 0.4392288…` is Part II's `C`).
- **Shannon window (Theorem 34.1).** At `q = 1 − λ/log²(k − 1)` the maximal
  block curvature tends to `λ/(4 + λ)`, with a uniform first correction;
  local lower concavity boundaries (Corollary 34.2) and unequal large
  alphabets (Corollary 34.4).
- **Above order one (Theorem 35.2).** For `1 < q < 2` concavity is
  equivalent to positive semidefiniteness of an `n × n` compression matrix,
  with a scalar Schur-complement form; for equal alphabets `Π*_k(q − 1) ≤ q`
  independently of `n`. Order two, orders above two and Rényi entropy
  (Proposition 35.3); the upper Shannon boundary (Corollary 35.4).
- **Quantum product states (Theorem 36.1).** The same classifications hold
  for affine interpolation of the marginal density matrices.
- A Lean decomposition (Section 37.3) and nine research questions AQ1–AQ9
  (Section 38; the manuscript's Q1–Q9, renamed to keep them apart from
  Part II's Q1–Q10).

## What Part II settles, and what it does not

- **Settled, for the joint vector only.** Part I's subunit question, asked
  for the ordinary sum, is answered for the joint vector: Rényi yes in every
  dimension; Tsallis yes exactly when `n ≤ 9` (Section 11.2 of the article).
- **Not settled: the ordinary sum.** Neither Part II nor this report answers
  Part I's question for `X_1 + … + X_n`. Tempting false readings, printed in
  Section 11.2: "ten bits fail, so the ordinary sum fails for `n ≥ 10`" and
  "nine bits are concave, so the ordinary sum is concave for `n ≤ 9`" — neither
  is implied; entropy does not pass continuously from the vector to the sum
  as weights coalesce (Section 18.3).
- **An unverified external claim.** The manuscript records H. Wang,
  arXiv:2609.27433v1 (submitted 23 September 2026), which by the manuscript's
  account states that the ordinary-sum threshold is exactly one. The
  manuscript did not rely on it; **this report has not read or verified it**
  and does not mark Part I's question answered on its strength.
- Part I's other two questions (same-sign slopes; maximizers for three or
  more coins) and partially colliding weights (Q4) are not addressed.
- Part I's delivered `STATUS.md` (20 September 2026) is unchanged; its items
  "General joint concavity for every 0<q<1" and "An all-order interval
  theorem for arbitrary n" remain accurate for the ordinary sum.

## What Part III settles, and what it does not

- **Settled: Part II's Q7 for full categorical simplices.** The block
  supremum `M_j` of Theorem 22.1 is `Θ_{k_j}(q)`; sharp integer transitions
  persist and depend on the alphabet (17 versus 18 symbols for three factors
  at `q = 1/2`; `nq ≤ 1` for all alphabets at once). Part II's sentence after
  Theorem 22.1 ("No blanket assertion about all categorical distributions
  follows without calculating their block quantities") stays true; Part III
  does that calculation for full simplices (Section 26.2 of the article).
- **The binary case is Part II.** For `k = 2` Part III's block quantity is
  Part II's `ρ_q`, so `Θ_2 = Ψ` exactly; the placement audit also checked
  this numerically (`Θ_2 = 1/11, 1/10, 0.0657638785…` at `q = 1/3, 1/2, 0.8`),
  and `V_2` equals Part II's `C`.
- **Not settled.** Structured finite families other than full simplices
  (the other half of Q7; AQ8); global unimodality of `Θ_k` or of `Ψ`
  (Part II's Q1, AQ1); coarsenings and partially colliding weights (Part II's
  Q4–Q5, AQ5); Part I's question for the ordinary sum. The Wang preprint is
  again recorded from its abstract only.

## Not claimed

Part I (from its delivery): no proof of universal joint concavity for
`0 < q < 1` for the ordinary sum (only the largest finite universally
admissible order, one, is determined, using the known Shannon theorem); no
same-sign-slope result; no maximizer classification for `n ≥ 3`; no
uniform-in-`n` neighbourhoods; nothing at order zero or for the trivial
Tsallis limit at order infinity; the existential initial-interval statements
of Conjecture 4.2 are not disproved (they could hold with threshold one); the
Shannon theorem is not challenged; no referee review, author approval,
proof-assistant verification or exhaustive priority search. The exploratory
floating-point Hessian search certifies nothing.

Part II (from the manuscript, Sections 12, 15, 18, 19, 20, 21, 22 and 24):

- It concerns the joint vector and collision-free weighted sums, **not** the
  ordinary unweighted sum; partially colliding weight systems are not
  settled, and no conclusion is drawn about the minimum failing dimension
  among weight systems with collisions.
- The subunit counterexamples disprove concavity, not quasiconcavity.
- `1/9` is not claimed to be the sharp continuous bound on `Ψ`; the
  strong-concavity constant is not claimed optimal; the nonconcave orders are
  not proved to form one interval, and global unimodality of `Ψ` is not
  proved (the figures are numerical only).
- The general gcd/root-counting branch of the rational-order decision theorem
  is an algorithmic theorem, not implemented software; the exact script
  implements only the strict-interval branch for its tabulated orders, and
  the symbolic script checks the gcd branch only at `q = 1/2` and `1/3`.
- The block criterion yields no blanket statement about categorical
  distributions; Part III evaluates it for full categorical simplices.
- The known one-bit Rényi threshold, the ordinary-sum counterexample above
  one and its fixed-mean construction are **not** claimed as new.
- Not refereed, not formalized in Lean; priority not confirmed (targeted
  searches only); the symbolic checks are not a proof-assistant verification;
  running Python is not a proved bridge from the certificates to the real
  inequalities. The proof-assistant decomposition (Section 22.2) and Q10 are
  proposals.

Added at the write: the write read the manuscript's proofs and spot-checked
`Ψ(1/2)`, `Ψ(1/3)`, `Ψ(20/41)`, `Ψ'(1/2)`, `t_*`, `C` and the quartic
coefficients numerically (at placement the rank-one criterion had been
re-derived and the profile values reproduced independently); that is not an
independent proof review.

Part III (from the manuscript, its title page, Sections 27, 30, 31, 32, 33,
34, 35, 36, 37 and 39, and its claim ledger):

- Concavity is under affine interpolation of the **marginals**, not
  arbitrary mixtures of joint laws, and not for the entropy of the ordinary
  sum; no result settles arbitrary coarsenings, partially colliding weighted
  sums or all structured block families. The Wang preprint was checked from
  its abstract only and is neither a premise nor a consequence.
- The rank-one product-Hessian method and the block criterion are Part II's
  (and older); the two-order power-sum extremal problem (Sakai–Iwata) and the
  variance-of-surprisal problem (Reeb–Wolf) are credited, not claimed; the
  binary specializations are recovered, not new.
- The strong-concavity constant is not claimed optimal. The 17/18 statement is
  for three factors at `q = 1/2`; a mixed tuple with one 18-symbol block need
  not fail. No global unimodality of `Θ_k`, and no global interval theorem at
  all orders: Shannon-window uniqueness is local only. The large-alphabet
  expansion is for fixed `q`, locally uniform away from 0 and 1; no
  unrestricted infinite-alphabet limit is claimed.
- The general rational-order algebraic decision branch is not implemented;
  only the half-order certificate branch is.
- The quantum statement is for affine density-matrix parameters of product
  states, not an entanglement threshold or mixtures in the joint state space.
- The figures and the numerical layer are illustrations and diagnostics; the
  symbolic series checks do not prove the uniform remainder theorems; running
  Python is not a proof-assistant bridge. Not refereed, no Lean verification,
  priority from a targeted (not exhaustive) search; the Lean decomposition
  (Section 37.3) and AQ9 are proposals.

Added at the Part III write: the placement audit checked the closed-form block
curvature against a direct tangent Hessian, `Θ_2 = Ψ`,
`3Θ_17(1/2) = 0.99403… < 1 < 1.00680… = 3Θ_18(1/2)`, the witness values, the
identity (31.4), `U''(0)`, the finite gap, `Θ_k → q` and the Shannon-window
limit in exact or high-precision arithmetic, independently of the manuscript's
code; the quantum section was read, not checked. That is not an independent
proof review.

## Labels

Part I's 56 labels are bare (`thm:main`, `eq:D`, …) and unchanged. The write
added 98 labels (154 in total), all with the report prefix `bep:`: seven on
Part I headings (`bep:sec:problem`, `bep:sec:allorders`, `bep:sec:mindim`,
`bep:sec:verification`, `bep:sec:conclusions`, `bep:app:selection`,
`bep:app:certificate`) and 91 in Part II with the sub-prefix `bep:pe:` — the
manuscript's 70 labels, unchanged after the prefix, plus 21 on Part II's
section headings and the notation table. No label was renamed or removed. The
`.aux` numbers of all 56 Part I labels equal those of a build of the committed
text, and every manuscript label carries its delivered number shifted by
eleven sections (its Figures 1–2 and Table 1 are Figures 3–4 and Table 3
here; Table 2 is the new notation table). The manuscript's bibliography keys
`Wang` and `Tsallis` are `bep:pe:Wang` and `bep:pe:Tsallis`; its `HJ` is
Part I's `HJ2017`, and its `RepoEntropy` (Part I itself) became references to
Part I.

The Part III write added 113 labels (267 in total), all with the sub-prefix
`bep:ae:`: the manuscript's 107 labels, unchanged after the prefix (twelve in
the cleveref form `\label[type]{…}`, which keeps its optional argument; the
report now loads `cleveref`), plus five on Section 26 and its subsections and
one on the new notation table. No label was renamed or removed. The `.aux`
numbers of all 154 earlier labels equal those of a build of the committed
text; their page numbers are one higher, because the contents grew from three
to four pages. Every manuscript label carries its delivered number shifted by
26 sections (its Figures 1–2 and Table 1 are Figures 5–6 and Table 5 here;
Table 4 is the new notation table). Its bibliography keys `sakai` and `reeb`
are `bep:ae:sakai` and `bep:ae:reeb`; its `wang` is Part II's `bep:pe:Wang`
(whose entry gained a dated remark), and its `repo` (Parts I–II) became
references to Part II.

## Notation

Part II keeps the manuscript's symbols; the full table is Table 2 in
Section 11.3. Its entropies use Part I's unnormalized conventions, applied to
the vector: `T_{q,n} = (Z_{q,n} − 1)/(1 − q)`, `R_{q,n} = log Z_{q,n}/(1 − q)`
with `Z_{q,n} = Π h_q(p_i)`, `h_q(p) = p^q + (1−p)^q`. Watch for:

- **`a` flips sign.** Part I: `a = q − 1` throughout. Part II: `a = 1 − q`,
  except in the above-one part of the proof of Theorem 19.2, where `a = q − 1`.
- **`D`.** Part I's `D_q(p)` is the balanced-point quantity (4.1); Part II's
  `D` is the diagonal matrix `diag(d_q(p_i))`. The manuscript's 96-digit
  integer, also called `D` there (and in `data/02-product-entropy-checks.txt`
  and the certificate JSON), is **renamed `D_cert`** — the only renamed
  symbol; no normalization changed.
- **`F`.** Part I's `F_q` is the power sum of the sum; Part II's `F_a(t)`,
  `F(s)` and block product `F` are local, and its power sum is `Z_{q,n}`.
- **`N(q)`** is Part II's *largest concave* dimension; the product model's
  minimum failing dimension is `N(q) + 1`. It is not Part I's minimum number
  of coins for the ordinary sum.
- **`t`** is Part II's half log-odds, Part I's imbalance on `(p + t, p − t)`.
  **`L`**, **`C`**, **`w`**, **`m`**, **`K`**, **`y`**, **`g`** are local
  letters in both parts (Table 2 lists every use).

Part III keeps the manuscript's symbols apart from two renamings; the table
is Table 4 in Section 26.3. For binary alphabets its `F_q`, `T_q`, `H_q` are
Part II's `Z_{q,n}`, `T_{q,n}`, `R_{q,n}`. Watch for:

- **Renamed.** The manuscript's power-sum product `R_α(p) = S_{1−α}S_{1+α}`,
  its maximum `𝓡_k(α)` and the abbreviation `R` are `Π_α(p)`, `Π*_k(α)` and
  `Π` (they collided with Part II's Rényi entropy `R_{q,n}`); its
  `K = g(A⁻¹g)` of Lemma 30.1 is `ω` (the manuscript also uses `K = k − 1`).
  Labels, scripts and records keep the manuscript's names (for example
  `R_witness` in `data/03-alphabet-entropy-exact_certificates.json`, and the
  label `bep:ae:eq:K`). No normalization changed.
- **`H_q` is Rényi**, `T_q` Tsallis; **`S_q(p)`** is a one-marginal power
  sum, not Part I's ordinary sum `S_p`; **`F_q`** is the power sum of the
  joint law, not Part I's `F_q`.
- **`α`** is `1 − q` below order one and `q − 1` in Section 35. **`t`** is
  the log of the large-to-small probability ratio (at `k = 2` twice Part II's
  half log-odds), and also an interpolation parameter in Section 28.
- **`K = k − 1`** in Sections 31–33 and 40; **`k`** is the alphabet size, not
  Part II's `k` in `q = m/k`; Theorem 32.1 writes `q = a/b`.
- **`C_q`**, **`V_k`**, **`λ`**, **`h`**, **`ρ_i`**, **`L`**, **`U`**, **`D`**
  have Part III meanings (Table 4); `V_2` is Part II's `C`, and `τ_q`,
  `Θ_2` are Part II's `ρ_q`, `Ψ`. Part III's questions are **AQ1–AQ9**.

## Files

```
article.tex                                   the report (Parts I–III), standalone LaTeX, internal bibliography
article.pdf                                   the compiled report, 73 A4 pages (unnumbered title page,
                                              contents pp. 1–4, Part I pp. 5–18, Part II pp. 19–41,
                                              Part III pp. 42–69, Appendices A–B and references pp. 70–72)
README.md                                     this guide
STATUS.md                                     Part I's delivered status and claim boundaries (20 Sep 2026)
LICENSE.txt                                   Part I's delivered CC0 1.0 dedication
Makefile                                      Part I's delivered make targets (pdf, check, symbolic, figures, clean)
requirements-optional.txt                     Part I's optional Python pins (numpy, scipy, sympy, matplotlib, mpmath)
code/verify_exact.py                          Part I: exact standard-library checks (12,512)
code/verify_symbolic.py                       Part I: SymPy differentiation and identity checks
code/make_figures.py                          Part I: phase-boundary table, CSV and two figures
code/exploratory_hessian_probe.py             Part I: exploratory floating-point search (provenance only)
code/select_area.py                           Part I: the one-draw random-area selection script
results/exact_checks.json                     Part I: recorded exact-check result
results/symbolic_checks.txt                   Part I: recorded symbolic output
results/phase_boundaries.csv                  Part I: numerical phase boundaries
results/phase_table.tex                       Part I: Table 1 (input by the article)
results/exploratory_hessian_probe.log         Part I: exploratory log (not a certificate)
results/environment.txt                       Part I: tool versions
results/pdf_quality_control.txt               Part I: its delivered PDF's layout check
figures/phase_boundaries.pdf                  Part I: Figure 1
figures/collision_profiles.pdf                Part I: Figure 2
notes/selection.json                          Part I: original random draw
notes/area_list.tex                           Part I: the 96-area list (input by Appendix A)
notes/manifest_exclusion.md                   Part I: audit of the 71 excluded manifest entries
notes/sources.md                              Part I: source and novelty audit
02-product-entropy-SOURCES_AND_STATUS.md      Part II: source notes, priority audit, evidence boundaries
code/02-product-entropy-verify_exact.py       Part II: exact standard-library certificates (17,927 checks)
code/02-product-entropy-verify_symbolic.py    Part II: SymPy identity and root-count checks (14)
code/02-product-entropy-make_figures.py       Part II: profile CSV and two Matplotlib figures
code/02-product-entropy-Makefile              Part II: delivered make targets (see below)
data/02-product-entropy-checks.txt            Part II: recorded output of the exact script
data/02-product-entropy-certificates.json     Part II: exact root-enclosure certificates and thresholds
data/02-product-entropy-profile_table.tex     Part II: Table 3 (input by the article)
data/02-product-entropy-symbolic_checks.txt   Part II: recorded output of the symbolic script
data/02-product-entropy-profile_plot.csv      Part II: Ψ(q) at q = 0.001, …, 0.999 (CRLF, as delivered)
data/02-product-entropy-pdf_quality_control.txt  Part II: layout record of the delivered 21-page PDF
03-alphabet-entropy-CLAIM_LEDGER.md           Part III: claim ledger (manuscript theorem numbers)
03-alphabet-entropy-SOURCES.md                Part III: pinned repository source and bibliographic audit
03-alphabet-entropy-LAYOUT_QA.md              Part III: layout check of the delivered 24-page PDF
code/03-alphabet-entropy-verify_exact.py      Part III: exact standard-library certificates (70 assertions)
code/03-alphabet-entropy-verify_symbolic.py   Part III: SymPy identities (7)
code/03-alphabet-entropy-verify_numerical.py  Part III: NumPy/mpmath diagnostics (4,595 assertions)
code/03-alphabet-entropy-make_figures.py      Part III: profile CSV and the two figures
code/03-alphabet-entropy-Makefile             Part III: delivered make targets (do not use here; see below)
data/03-alphabet-entropy-exact_certificates.json  Part III: witness values, Jensen enclosure, 14 half-order entries
data/03-alphabet-entropy-exact_run.txt        Part III: console output of the exact script
data/03-alphabet-entropy-symbolic_checks.txt  Part III: recorded output of the symbolic script
data/03-alphabet-entropy-symbolic_run.txt     Part III: console output of the symbolic script
data/03-alphabet-entropy-numerical_checks.json   Part III: numerical diagnostics and Shannon-window table
data/03-alphabet-entropy-numerical_run.txt    Part III: console output of the numerical script
data/03-alphabet-entropy-alphabet_profiles.csv   Part III: Θ_k(q) for k = 2, 3, 17, 18, 64 (1,245 rows; CRLF, as delivered)
data/03-alphabet-entropy-environment.json     Part III: the delivery's Python and package versions
data/03-alphabet-entropy-requirements.txt     Part III: pinned numpy, mpmath, sympy, matplotlib
data/03-alphabet-entropy-latex_build.txt      Part III: log of the delivered 24-page build
figures/03-alphabet-entropy-alphabet_profiles.pdf  Part III: Figure 5 (as delivered)
figures/03-alphabet-entropy-shannon_window.pdf     Part III: Figure 6 (as delivered)
```

## Build the article

From this directory, with pdfLaTeX and the `pgfplots` and `cleveref`
packages (Part II's Figures 3–4 are drawn at build time from
`data/02-product-entropy-profile_plot.csv`; Part III's Figures 5–6 are the
shipped PDFs `figures/03-alphabet-entropy-*.pdf`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or two `pdflatex -interaction=nonstopmode -halt-on-error article.tex` runs
(Part I's `make pdf` does the same). No Python is needed. The build used for
the shipped PDF (MiKTeX pdfTeX, 29 September 2026, after the Part III write)
had no errors, undefined references or citations, multiply defined labels,
duplicate PDF destinations, or overfull boxes; three mildly underfull lines
remain, the two of the Part II build in paragraphs with long file names and
one in a narrow column of Part III's verification table (Section 37.1). The
committed Part I text produced one duplicate-destination warning (`page.1`,
from the title page); the Part II write fixed it with
`\hypersetup{pageanchor=false}` around the title page.

Fonts: Part I's two Matplotlib figures and Part III's two each embed two
Type 3 DejaVu fonts, so the PDF has eight Type 3 font rows (`pdffonts`); the
Part III figures were kept as delivered for that reason (regenerating them
with `pdf.fonttype: 42` would change nothing else and was not done).

## Rerun the checks

Run every suite on a **copy** of this directory: the scripts write into it.

```sh
cp -r . /path/to/copy && cd /path/to/copy
# Part I
python code/verify_exact.py                      # rewrites results/exact_checks.json
python code/verify_symbolic.py                   # rewrites results/symbolic_checks.txt
python code/make_figures.py                      # rewrites results/phase_*, figures/*.pdf
# Part II (standard library only; then SymPy 1.14.0)
python code/02-product-entropy-verify_exact.py > p2-checks.txt
python code/02-product-entropy-verify_symbolic.py > p2-symbolic.txt
python code/02-product-entropy-make_figures.py   # needs Matplotlib
```

Compare `p2-checks.txt` with `data/02-product-entropy-checks.txt` and
`p2-symbolic.txt` with `data/02-product-entropy-symbolic_checks.txt`. The Part
II exact script also writes `results/certificates.json` and
`results/profile_table.tex` (compare with the `data/02-product-entropy-`
copies); the figure script writes `results/profile_plot.csv` and
`figures/profile.pdf`, `figures/ten_bit_detail.pdf`. None of these names
collides with a Part I file, but they are strays in the shipped layout.
**Do not** redirect the Part II symbolic output to `results/symbolic_checks.txt`
(that is Part I's record), and **do not** use `code/02-product-entropy-Makefile`
here: its `check`, `symbolic` and `figures` targets run the delivered names
`code/verify_exact.py`, `code/verify_symbolic.py`, `code/make_figures.py`,
which in this directory are Part I's scripts, and its `pdf`/`clean` targets act
on the combined article.

Rerun on 29 September 2026, on a copy (Python 3.14.4; SymPy 1.14.0 via
`uv run --no-project --with sympy==1.14.0`): the Part II exact script passed
17,927 checks and the symbolic script 14; both outputs, `certificates.json` and
`profile_table.tex` equal the recorded files apart from line endings (the
scripts write CRLF on Windows). The placement run gave the same result.

### Part III

**Do not run Part III's scripts under their shipped names in this directory,
and do not use `code/03-alphabet-entropy-Makefile`.** Every Part III script
writes below its parent's parent directory (`Path(__file__).parents[1]`):
`verification/exact_certificates.json`, `verification/numerical_checks.json`,
`verification/symbolic_checks.txt`, `data/alphabet_profiles.csv`,
`figures/alphabet_profiles.pdf` and `figures/shannon_window.pdf`. Run in
place, that is this report's root, where they would create strays (a
`verification/` directory, `data/alphabet_profiles.csv`, two PDFs in
`figures/`) without overwriting a shipped file; only `verify_exact` creates
`verification/`, so the numerical and symbolic scripts fail without it. The
Makefile's targets
`exact`, `symbolic`, `figures` and `check` call `code/verify_exact.py`,
`code/verify_symbolic.py` and `code/make_figures.py`, which in this directory
are **Part I's** scripts; `numerical` calls `code/verify_numerical.py`, which
does not exist here; `pdf` and `clean` act on the whole report. Safe recipe
(restores the delivered layout in a scratch directory, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/03/code" "$W/03/verification" "$W/03/data" "$W/03/figures"
for f in code/03-alphabet-entropy-*.py; do cp "$f" "$W/03/code/${f#code/03-alphabet-entropy-}"; done
cd "$W/03" && for s in verify_exact verify_numerical make_figures verify_symbolic; do
  uv run --no-project --with numpy==2.3.5 --with mpmath==1.3.0 --with sympy==1.14.0 \
    --with matplotlib==3.10.8 python code/$s.py; done
```

Then compare `$W/03/verification/*` with `data/03-alphabet-entropy-*` of the
same names and `$W/03/data/alphabet_profiles.csv` with
`data/03-alphabet-entropy-alphabet_profiles.csv`. The records are compared
after converting CRLF to LF: on Windows `write_text` writes CRLF, and
`csv.writer` writes CRLF on every platform (why the shipped CSV is CRLF; it
keeps its bytes through a `-text` line in `SetTheory/Cardinals/.gitattributes`).
`verify_exact.py` needs only the standard library.

Rerun on 29 September 2026 with this recipe (Python 3.13.5 via `uv`,
Windows): all four exited 0 (about 1, 2, 2 and 46 s); 70 exact assertions,
4,595 numerical assertions, 7 symbolic identities; `exact_certificates.json`,
`numerical_checks.json` and `symbolic_checks.txt` equal the shipped files after
CRLF → LF; the CSV differs in the last digit of 386 of its 1,245 rows
(relative difference at most 7.6·10⁻¹⁶, platform floating point). The placement
audit's run on a copy gave the same result.

## Discrepancies and delivery names

- The shipped Part II files keep their delivered text, which uses delivery
  names: `02-product-entropy-SOURCES_AND_STATUS.md` names `article.tex` and
  the report path; `code/02-product-entropy-Makefile` names
  `code/verify_exact.py`, `code/verify_symbolic.py`, `code/make_figures.py`
  and `article.tex`; the scripts write `results/certificates.json`,
  `results/profile_table.tex`, `results/profile_plot.csv` and
  `figures/{profile,ten_bit_detail}.pdf`, not the prefixed `data/` names.
  Delivery-to-shipped map: `results/X` → `data/02-product-entropy-X` (six
  files), `code/X` → `code/02-product-entropy-X`, `Makefile` →
  `code/02-product-entropy-Makefile`, `SOURCES_AND_STATUS.md` →
  `02-product-entropy-SOURCES_AND_STATUS.md`.
- The delivery README (not shipped) lists `article.pdf`, `figures/` and
  `SHA256SUMS` of the package; none is shipped. The two figure PDFs are
  replaced by `pgfplots` redraws from the shipped CSV, whose step in `q` is
  0.001 (the delivered detail figure sampled `[0.48, 0.51]` at step `10^−5`).
- `data/02-product-entropy-pdf_quality_control.txt` describes the delivered
  21-page PDF, not this build.
- The Part II exact script and its certificate JSON call the 96-digit integer
  `D`; the article calls it `D_cert`.
- Part I's own delivered files (`STATUS.md`, `Makefile`, `notes/sources.md`,
  `results/pdf_quality_control.txt`, Section 9 of the article) describe
  Part I's 17-page package; they are unchanged. Part I's Section 9 carries a
  dated pointer to Part II's reproduction section.
- Part I's delivered README said the PDF has 17 pages and gave its contents
  and selection record; this README replaces it, and keeps its content above
  and below.
- The shipped Part III files keep their delivered text, which uses delivery
  names. Delivery-to-shipped map: `code/X` → `code/03-alphabet-entropy-X`
  (four scripts), `Makefile` → `code/03-alphabet-entropy-Makefile`,
  `verification/X` → `data/03-alphabet-entropy-X` (eight files),
  `verification/LAYOUT_QA.md` → `03-alphabet-entropy-LAYOUT_QA.md`,
  `data/alphabet_profiles.csv` → `data/03-alphabet-entropy-alphabet_profiles.csv`,
  `requirements.txt` → `data/03-alphabet-entropy-requirements.txt`,
  `CLAIM_LEDGER.md` and `SOURCES.md` → `03-alphabet-entropy-*.md`,
  `figures/X.pdf` → `figures/03-alphabet-entropy-X.pdf`.
  `03-alphabet-entropy-CLAIM_LEDGER.md` cites `article.pdf`/`article.tex` and
  the manuscript's numbers (add 26 to the section: its Theorem 3.1 is
  Theorem 29.1 here). `data/03-alphabet-entropy-exact_run.txt` ends
  "Written: verification/exact_certificates.json" and prints the lower gap
  bound in lowest terms, `22029958407/250000000000000000` (=
  `88119833628/10^18`). `03-alphabet-entropy-LAYOUT_QA.md` and
  `data/03-alphabet-entropy-latex_build.txt` describe the delivered 24-page
  PDF, not this build; `data/03-alphabet-entropy-environment.json` is the
  delivery's Linux environment (Python 3.13.5). The certificate file names
  the power-sum product `R` (`R_witness`), which the article calls `Π`.
- Part III's delivery README (not shipped) lists `article.pdf`, `SHA256SUMS`
  and the `verification/` and `data/` directories of the package; the PDF is
  replaced by this report's and `SHA256SUMS` was retired. Its manuscript's
  reproduction commands name the delivered paths; the article prints them
  with a warning and the safe recipe above (Section 37.2).

## Relation to neighbouring reports and to formal work

- No other report of the collection treats Shepp–Olkin concavity or Rényi or
  Tsallis entropy of Bernoulli families; the neighbours in
  `log-concavity-and-unimodality/` concern real roots, log-concavity of
  sequences and unimodality of polynomials.
- ProveIt has **no** Lean or Rocq development of Rényi or Tsallis entropy,
  Bernoulli sums or the Shepp–Olkin problem (no `.lean` or `.v` file mentions
  them), so no statement of any part is formalized, and none is claimed
  formalized. Part III's Lean decomposition (Section 37.3) and its AQ9 (a
  kernel-checked 17-symbol inequality, the 18-symbol rational witness and the
  half-order table) are proposals.

## Random selection (Part I)

Part I's area was fixed before a single OS-backed call to
`secrets.randbelow(96)`, which returned index 57 (one-based 58), **Discrete
probability**; there was no redraw. `notes/selection.json` is the preserved
record. Re-running `code/select_area.py` makes a fresh draw and writes
`code/selection.json`; it cannot reproduce the original randomness and is not
part of the verification or the build.

## License

`LICENSE.txt`, delivered with Part I, dedicates Part I's newly generated
article, code and data to the public domain under CC0 1.0. The Part II and
Part III manuscripts state no license of their own. No third-party paper,
font file or software package is redistributed by any part (the Part III
figure PDFs embed subsets of the DejaVu fonts, as Part I's do).
