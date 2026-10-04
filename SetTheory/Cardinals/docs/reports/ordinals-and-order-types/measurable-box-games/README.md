# Countable Information, Uncountably Many Boxes

**Sharp measurable prediction bounds, exact decision-tree enumeration, and an
all-orders asymptotic expansion (Part I); no universal sublinear bound for
measurable hat guessing (Part II); adaptive box games beyond cylinder
measurability (Part III); two queries in expectation: sharp information
thresholds and the exact inspection cost of infinite hat guessing (Part IV)**

A research report in four Parts, built from five manuscripts. Part I (3 October
2026) is a manuscript on Elliot Glazer's *A choiceless box game paradox*
(arXiv:2211.10474). Part II (added 4 October 2026) is a manuscript on the
surplus of correct guesses in Nathaniel Eldredge's infinite binary hat game
(arXiv:2508.02828); it names Part I as its most direct source and settles
Part I's Research question Q9 for one family of parameters. Part III (added
4 October 2026, batch 92) classifies every extension of the product measure to
the success events of adaptive box players and answers Part I's questions Q2
(for Borel and universally measurable outputs; the Baire-property case stays
open) and Q5. Part IV (added the same day) merges two independent manuscripts
that determine the cost of inspecting hats needed for a divergent surplus —
exactly two expected queries per player — answering Part II's Research question
29.2; one of them also settles Q9 for a larger family. The author lines of
Parts I–III and of Part IV's source 04 read "Prepared for Vladimir Reshetnikov"
or "Research report prepared for …" and carry no AI wording; **Part IV's base,
source 06, has no author line, and its PDF metadata name the author as
"ChatGPT research report"**. Like the other deliveries of the intake, all five
are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 87, manuscript 02 | `glazer_box_games_research.zip` (364,051 bytes; inner directory `glazer_box_games/`, main file `article.tex`, 999 lines, 24-page US Letter PDF), arrival commit `fa0a0576e` | `6fef5383b` (`6fef5383b126be343cccc9baf47081ef37ab5afe`, the article's `\commit` macro, quoted in Section 1 and in every repository URL of its bibliography) | `d151b39ca` | Part I: abstract, Sections 1–16, Appendices A–B |
| 02 | batch 90, manuscript 02 | `hat_guessing_research.zip` (550,545 bytes; inner directory `hat_guessing_research/`, main file `hat_guessing_growth.tex`, 1,587 lines, 22-page A4 PDF), arrival commit `a162e4386` | `7c0f2d9f9` (`7c0f2d9f92c3d51ec85703bed1022924a4b7359b`, quoted in Section 17.2 and bibliography entry 12) | `12076b2e8` | Part II: Sections 17–29, Appendices C–E |
| 03 | batch 92, manuscript 03 | `adaptive_box_games_research.zip` (485,758 bytes; inner directory `adaptive_box_games/`, main file `adaptive_box_games.tex`, 1,207 lines, 29-page US Letter PDF), arrival commit `9dc8db274` | `1afa38bf9` (`1afa38bf984377eb85a5569cf6376054994a17a5`, its `\snap` macro, Section 30 and bibliography entries 15–16) | `e38f368c2` | Part III: Sections 30–44, Appendices F–G |
| 04 | batch 92, manuscript 04 | `hat_inspection_frontier.zip` (491,169 bytes; inner directory `hat_inspection_frontier/`, main file `hat_inspection_frontier.tex`, 2,319 lines, 31-page A4 PDF), arrival commit `9dc8db274` | `9fe62865d` (`9fe62865dc30d71256183466b744b98ebf7e64d6`, Section 59.2, bibliography entry 29) | `e38f368c2` | Part IV, second source: Sections 59–69 |
| 05 | batch 92, manuscript 06 | `hat_query_thresholds_package.zip` (478,565 bytes; inner directory `hat_query_thresholds/`, main file `hat_query_thresholds.tex`, 1,919 lines, 26-page US Letter PDF), arrival commit `afd7ffabb` | `9fe62865d` (its `\pin` macro, Section 45.4 and bibliography entries 26–28) | `e38f368c2` | Part IV, base: Sections 45–58 |

The source numbers are this report's local sequence (they are the file
prefixes `01`–`05`); the batch-92 manuscripts 04 and 06 keep their batch
numbers in the article ("source 04", "source 06"), so source 06 has the file
prefix `05-hat-queries-`.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. The finite computations of all Parts
were executed (by the packages and again at intake or write); the infinite
theorems rest on the written proofs only. **Historical priority is not
established** for any Part; Part II explicitly disclaims priority for its
coding mechanism (Ebert–Merkle–Vollmer 2003) and for the slow-density
phenomenon, and Part IV's block construction is Eldredge's (his
Proposition 6.6), credited by both of its sources.

## Part I

### The question

Glazer's paper (one arXiv version, v1 of 15 November 2022, 6 pages, math.LO
and math.CO) ends Section 5, "More box games", with the question "Does ZF
prove that G([3], ℝ, {0,1}) is winnable?": can three players facing
continuum many boxes of bits, each opening any boxes it likes and then
guessing an unopened one, guarantee that at most one of them is wrong? The
report separates three properties an infinite strategy can have (a
measurable choice of box and guess, a measurable success event, actual
executability without reading the target) and answers the question for the
first class only.

### What it proves

- **Theorem 3.1 (exact minimax value).** For a standard Borel set of boxes,
  alphabet size `q` and `m` blind output maps measurable for the cylinder
  σ-algebra, some configuration gives at most `⌊m/q⌋` correct guesses, and
  constant guesses guarantee `⌊m/q⌋`. Success events are not assumed
  measurable. **Corollary 3.2:** three binary players with continuum many
  boxes and such outputs cannot guarantee two correct guesses (they can
  guarantee one). **Corollary 3.3:** with lists of `r` guesses the optimum is
  `⌊mr/q⌋`.
- **Theorem 4.1:** for a countable team, a countably additive extension `ν` of
  the product measure to the success events with `ν(E_τ) = 1/q` for every
  player (existence only).
- **Theorem 5.1:** a blind map whose success event is measurable (or
  measurable for the completion) has its targets in a countable set
  (pointwise, or off a null set); Remark 5.2 records two nonconverses.
- **Theorems 6.1–6.2:** on the boxes `ℕ ⊔ 2^ℕ`, a continuous diagonal
  selector whose success event has inner measure 0 and outer measure 1, and
  the classification of every extension to `σ(Σ_I, E)` by a measurable
  density `h`.
- **Proposition 7.1, Theorem 7.3, Lemma 7.4:** blind binary output maps on `n`
  boxes are labelled perfect matchings of the cube `Q_n`
  (`B_n = 2^(2^(n−1)) M_n`, with `M_n` = OEIS A005271); maps realizable by a
  decision tree that never queries its target are exactly those with a
  recursively sliceable matching; the first blind non-executable map has four
  boxes (explicit, Section 7.1).
- **Theorem 8.1:** `F_n = Σ_{k=1}^{n−1} (−1)^(k+1) C(n,k) F_{n−k}^(2^k)` for the
  number `F_n` of sliceable matchings, `L_n = 2^(2^(n−1)) F_n` legal maps:
  `F_n` = 1, 2, 9, 232, 206065, 212181312096, …; 40 of the 272 matchings of
  `Q_4` (10,240 maps) are not executable. The `q`-ary analogue, equation (10), gives,
  for `q = 3`, 1, 2, 21, 33976, 188162675402345.
- **Theorem 9.1:** `log F_n = γ 2^n − log n + Σ_{j≤N} c_j n^(−j) + O(n^(−N−1))`
  with rational, recursively computable `c_j`, and
  `F_n = e^(γ 2^n)/n · (1 − 3/(2n) + 17/(4n²) − 12/n³ + O(n^(−4)))`; `γ` is a
  growth constant ≈ 0.438158 (not Euler's constant), with a proved symbolic
  enclosure, equation (24).
- **Theorem 10.1:** `F_n/M_n < 2/(n+1) · (49F_6/(6D_6))^(2^(n−6))` for `n ≥ 6`,
  `49F_6 = 10,396,884,292,704 < 6D_6 = 12,009,535,517,376` (exact integers).
- **Theorem 11.1:** sharp information-budget inequalities (accuracy, entropy,
  mutual information, symmetric difference) for countable `I`, attained by
  Example 11.2.
- **Theorem 12.1:** a uniform partial algorithm that, for oracle strategies
  promised total and legal, extracts a finite losing prefix; **Theorem 12.2:**
  no computable function of program length bounds the horizon, and, for an
  encoding with an additive-overhead compiler, `H(n+c) ≥ BB_time(n) + 2`.
- Section 13: the executed checks; Section 14: foundations and a ProveIt
  formalization plan (four modules); Section 15: research questions Q1–Q12;
  Appendices A (assumption and claim ledger) and B (source and priority
  audit).

### What is not claimed

- **Glazer's question itself (Q1) is not answered:** Corollary 3.2 is a
  negative answer only for blind cylinder-measurable outputs, "not a statement
  that ZF disproves the existence of unrestricted winning strategies". The
  report does not claim that the question is still open in all literature; the
  intake did not search for its later status.
- ZFC is the ambient theory; no equivalence with ZF, ZF + DC or a subsystem is
  proved, and the countable-support selection needs a separate audit before
  any choiceless use.
- Standard ingredients are credited, not claimed: countable support,
  finite-coordinate averaging, Radon–Nikodym, compactness, halting-time
  diagonalization; Theorems 4.1 and 6.2 are special cases of Łoś–Marczewski
  extension theory.
- Theorem 4.1 gives existence, not uniqueness, and no independence of the
  players' successes; Theorem 5.1 does not say "measurable success implies
  probability 1/q".
- The enumeration counts extensional maps, not programs; the rarity theorem
  is about uniform counting on blind maps, not about any programming
  language. `F_n` is not A005271, and the sliceable sequence is not asserted
  absent from the literature.
- The asymptotic theorem is a Poincaré expansion; nothing is claimed beyond
  all orders. The decimal values of `γ` are rounded evaluations, not interval
  certificates; `formal_series.py` checks coefficients, not the remainder
  estimates.
- Theorem 12.1 needs its promise and gives no complexity bound;
  `BB_time` is a program-length running-time function, **not** Rado's
  n-state score function, and the inequality is conditional on the compiler.
- Questions Q2–Q12 are directions, not all recognized open problems. Since
  batch 92, Q2 is answered for Borel and universally measurable outputs and
  Q5 completely (Part III), and Q9 is settled for the families of Parts II and
  IV and for the trivial ranges of Remark 15.1 (below); the rest is open. No
  endorsement or authorship by Glazer is implied.

### Checks made at intake (batch 87)

On 3 October 2026:

- **arXiv.** The record of arXiv:2211.10474 lists one version, v1 of
  15 November 2022 (DOI 10.48550/arXiv.2211.10474); the date line "January 9,
  2023" of the manuscript's "inspected PDF" is printed in arXiv's PDF of
  that v1. The question quoted above is the last of its Section 5. The record
  of Glazer's arXiv:2312.11902 (also cited) has three versions, the last of
  7 January 2024.
- **OEIS.** Searches for `1,2,9,232,206065`, `9,232,206065` and
  `2,21,33976` returned no entry. A005271 ("Number of perfect matchings in
  n-cube") begins 1, 2, 9, 272, 589185, 16332454526976, agreeing with
  `M_1, …, M_5`. **Nothing was submitted to the OEIS**, by the author or by
  the intake; a submission is a human editor's decision after review.
- **Independent recomputation** (a separate script, not shipped): `F_1..F_6`,
  the ternary values to `n = 5`, the 232/40 split of the 272 matchings of
  `Q_4` by brute force, `D_6 = 2,001,589,252,896`, the integer comparison of
  Theorem 10.1, `e^(1/7) < 7/6`, and the two decimal enclosures of `γ` at
  `N = 20`. The displayed 16-digit decimals of Section 9.4 are outward
  roundings of the 65-digit values in `data/verification_report.json`.
- **Delivered suite** on a scratch copy: all three commands passed; the three
  regenerated JSON files equal the shipped ones after CRLF stripping (see
  "Rerun the checks").
- **Profile citation.** The post cited for Glazer's author profile (bibliography
  entry 3, at `samaritan-research.org`) was reachable with the cited title,
  authors and dates; the same post is on Epoch AI's blog. Which copy is the
  original was not established. The article's sentence that "The LinkedIn page
  was not fully accessible" names no address; no LinkedIn URL is in any shipped
  file.

## Part II

### The questions

Eldredge's *A probabilistic look at the infinite hat-guessing game*
(arXiv:2508.02828; v1 of 4 August 2025, v2 of 24 October 2025, 20 pages,
math.PR with math.LO) studies countably many players with independent fair
hats, each guessing its own hat after seeing all the others. His Theorem 4.1
says that for every measurable strategy, almost surely, the correctly
guessing players have lower density at most 1/2 and upper density at least
1/2. Following a suggestion that he credits to Elliot Glazer and Charles Wang,
he studies the surplus `D_n = S_n − n/2` of correct guesses among the first
`n` players: his Proposition 6.6 makes `D_n → +∞` almost surely, his
Remark 6.8 reaches orders `log log n` and `log n/(log log n)²`, and asks
(1) whether order `log n`, or faster, is possible, and (2) whether some `g`
slower than `n` has `liminf D_n/g(n) = 0` almost surely for every measurable
strategy. (Text of v2 read at the write, 4 October 2026.)

### What it proves

Numbers are the printed ones; the manuscript's Section `k` is Section `k+16`,
its statement or equation `k.m` is `(k+16).m`, and its Appendices A–C are
C–E.

- **Lemma 18.2, Proposition 18.3:** each legal guess is correct with
  probability 1/2; `P(S_N ≥ s) ≤ N/(2s)`.
- **Theorem 19.2, Corollary 19.3 (pairing transformation):** any legal partial
  predictor lifts to a compulsory strategy with `D_{2m} = C_m − W_m` (correct
  minus wrong predictions); the mechanism is credited to Ebert–Merkle–Vollmer,
  *SIAM J. Comput.* 32 (2003), Theorem 6.6.
- **Lemma 20.1, Theorem 20.2 (syndrome block):** for `r, a ≥ 1`, `t = 2^r − 1`,
  `N = 2at` players, a Hamming-syndrome rule on pair parities gives, for every
  hat assignment, `D_N = −at` if the syndrome is 0 (probability `2^(−r)`) and
  `D_N = +a` otherwise.
- **Corollary 20.3 (sharp finite teamwork):** for `N = 2a(2^r − 1)` the
  largest probability that a legal compulsory strategy has at least `a·2^r`
  correct guesses is exactly `1 − 2^(−r)`, attained by a legal finite decision
  procedure; blind maps cannot do better. This **settles Part I's Research
  question Q9** for `(m,q,n) = (N,2,N)` and threshold `a·2^r` (see below).
- **Lemma 21.1, Proposition C.1:** every prefix of a good block stays within
  `3/2` (sharply `3(t−1)/(2t)`) of `u/(2t)`.
- **Theorem 22.1, Corollary 22.2, Proposition 22.3:** concatenated blocks
  give `|D_n − F(n) + C| ≤ 3/2` for an explicit piecewise-linear `F` and an
  almost surely finite random debt `C` of infinite mean; `D_n → +∞`,
  `D_n/n → 0`, `S_n/n → 1/2` almost surely; a stabilization bound.
- **Theorem 23.1:** a computable finite-information strategy with
  `D_n = log₂ n + O_ω(1)` almost surely — Eldredge's question (1).
  **Propositions 23.2–23.3:** `D_n ≍ n^β` for every `0 < β < 1`, and
  `D_n ≍ n/log n`.
- **Theorem 24.1, Corollary 24.2:** for every positive `g = o(n)` a continuous
  finite-information strategy with `D_n/g(n) → +∞` and `S_n/n → 1/2` almost
  surely; so no positive `g = o(n)` is a universal envelope — the negative
  answer to Eldredge's question (2). Remark 24.3: the strategy depends on `g`.
  Remark 24.4: on the wording of question (2) (see below).
- **Theorem 25.1:** Eldredge's Theorem 4.1 in surplus form,
  `liminf D_n/n ≤ 0 ≤ limsup D_n/n` almost surely, re-proved by a different
  route and credited.
- **Theorems 26.1–26.2:** for dominant-block schedules the success set
  `{D_n/g(n) → ∞}` equals `{S_n/n → 1/2}` and is dense, conull, meager and
  `Σ⁰₂`-complete; on a comeager set `liminf S_n/n = 0`.
- **Proposition 27.1:** every Martin-Löf random hat sequence has only finitely
  many bad blocks (computable schedules with `r_k = k`); Section 27 also gives
  computable schedules from a sublinearity modulus and the costs of the finite
  rules.
- Section 28: the executed finite checks and a four-layer formalization
  proposal; Section 29: Research questions 29.1–29.12; Appendices C (sharp
  prefix constant), D (`Σ⁰₂`-completeness of FIN), E (reproducibility and
  source notes).

### What Part II does not claim

- No historical priority for the Hamming-code/XOR coding mechanism or the
  slow-density phenomenon: Ebert–Merkle–Vollmer's Theorem 6.6 is substantial
  prior art; priority of the exact compulsory-guess formulation is
  unverified. `D_n → +∞` itself is Eldredge's Proposition 6.6 (credited in a
  write note; the manuscript cites that proposition only in its
  bibliography), and Theorem 25.1 is his Theorem 4.1.
- The infinite theorems are not machine-checked; the finite verifier is
  exhaustive only for nine listed cases, not for all `r, a`, nor for any
  almost-sure or asymptotic claim; an observed finite maximum is not a
  theorem.
- Corollary 20.3 does not classify all player counts or thresholds; the
  answers to Eldredge refer to the v2 text; Theorem 24.1 is `∀g ∃` strategy,
  not one strategy for all `g`; Corollary 24.2 covers positive `g` with
  `g(n)/n → 0` only. The arbitrary-`g` schedule need not be computable, so no
  lightface complexity claim is made; the explicit strategies are
  constructions, not low-resource algorithms.
- No authorship, endorsement or review by Glazer, Eldredge or Ebert, Merkle
  and Vollmer is implied; Glazer's box-game paper is not a source of the
  growth formulas. The formalization layers are proposals; no such files
  exist. The research questions are proposed, not recognized open problems.
- The source audit calls the package "a fully worked research report with
  unestablished historical priority, not an endorsed or peer-reviewed
  breakthrough"; no message was sent to anyone.

### Checks made at the write (batch 90)

On 4 October 2026:

- **Eldredge.** arXiv record: v1 4 August 2025, v2 24 October 2025. The v2
  text was read: Theorem 4.1, Proposition 6.6, Remarks 6.7–6.8 and the credit
  to Glazer and Wang are as the manuscript reports.
- **The Theorem 4.1 wording issue raised by the audit** (`02-hat-surplus-source_audit.txt`,
  item 1). The audit says Theorem 4.1 gives `liminf D_n/n ≤ 0 ≤ limsup D_n/n`,
  not equality for every measurable strategy. Confirmed, and Theorem 4.1 is
  not itself wrong: it is `L ≤ 1/2 ≤ U`, the same statement. The issue is in
  Remark 6.8's question (2), which asks for `liminf D_n/g(n) = 0` and says
  Theorem 4.1 shows this for `g(n) = n`. Equality fails for some measurable
  strategies: the write checked that this Part's blocks with every `r_k = 1`
  (each block all right or all wrong, probability 1/2 each) and the
  dominant-block condition `L_k ≥ k N_{k−1}` give `liminf D_n/n = −1/2` almost
  surely (second Borel–Cantelli lemma and the endpoint estimate in the proof
  of Theorem 26.1). This check is the write's, not the manuscript's; the
  manuscript's Remark 24.4 says the same about the wording and answers the
  meaningful "≤ 0" reading.
- **Ebert–Merkle–Vollmer.** The ECCC record TR02-056 (19 September 2002) with
  the three authors and the title exists, and its abstract concerns the
  density of guessed bits in autoreductions of random sequences. The SIAM text
  and its Theorem 6.6 were **not** checked.
- **Pin and repository claims.** The pin `7c0f2d9f9` is the batch-89 arrival
  commit; it holds this report as placed (`d151b39ca`) but before its batch-87
  write (`5f02820a7`), so the manuscript read Part I's delivered text, where Q9
  is the ninth further-research item (line 914 there). Its claims hold: Q9
  asks for optimal average-case teamwork over legal decision trees; Part I
  has no surplus-rate theorem; at placement no tracked file mentioned
  Eldredge, arXiv:2508.02828, autoreducibility, Ebert–Merkle–Vollmer or hat
  guessing; the list-coding files it read
  (`Logic/PeanoArithmetic/ListCoding/README.md`,
  `Lean/PAListCoding/Basic.lean`, `Lean/PAListCoding/Predicates.lean` below
  that project) are byte-identical at the pin and now (blobs `74164ac6`,
  `b7e037f4`, `c9f8f650`) and are described as interfaces, not proofs.
  Nothing refuted; no retraction.
- **Delivered suite** on a scratch copy (Python 3.14.4, Windows): PASS, nine
  cases, 284,052 inputs, 5,010,248 crosschecks, 10,020,496 own-hat toggles,
  3,997,918 good prefixes; `examples.json` and `example_prefix.csv` equal the
  shipped files, `verification.json` too apart from its time, version and
  elapsed fields. About 112 s on a loaded machine (37 s at placement; the
  recorded run says 17.2 s under Python 3.12.14). At placement the figure
  script reproduced the PDF figure up to its creation date (Matplotlib
  3.10.8); the PNG regenerates at the same size with different bytes.

### Part I's Q9, re-scoped

Q9 asks, for fixed `(m,q,n)`, for the largest probability of at least `t`
successes over legal decision trees, compared with blind maps, and for the
first parameters where the two optima differ. Corollary 20.3 gives the answer
`1 − 2^(−r)` for `(m,q,n) = (2a(2^r−1), 2, 2a(2^r−1))` and `t = a·2^r`. The
first-moment bound behind it holds for every team of blind binary maps, with
free targets, because each blind map succeeds on exactly half of the
configurations (Proposition 7.1); so in this family the legal and blind optima
coincide. The write adds that the same holds for every `n ≥ m` (extra boxes
unread). The family contains `(6,2,6)`, `t = 4`, optimum 3/4; Part I's
three-box benchmark `(3,2,3)`, `t = 2` (also 3/4) is not in it. A dated
note after Part I's questions (Section 15) records this; Part II's Research
question 29.4 continues Q9 for fixed targets.

*Corrected 4 October 2026, batch 92.* This paragraph and the batch-90 note
went on to say that all other parameters stay open. That was false when
written, and both stay on record with the refutation in **Remark 15.1**
(after the batch-92 note in Section 15): for every `(m,q,n)` the optimum is 1
when `t ≤ ⌊m/q⌋` (Theorem 3.1's constant team reads no box) and 0 when
`t > m`; and `(3,2,3)`, `t = 2`, was already settled by Part I itself, since
every blind binary map succeeds on half of the configurations (Proposition
7.1), so Markov's inequality gives at most `(3/2)/2 = 3/4`, which the three-box
team attains. Since batch 92, Part IV's source 04 settles the larger family
`(m(2^r−1), 2, m(2^r−1))`, `t = m·2^(r−1)`, for every `m ≥ 1` (optimum
`1 − 2^(−r)`, legal = blind; Theorems 65.4–65.5 and the note after them),
which contains both Part II's family (even `m`) and the three-box benchmark.
An additional elementary family is settled for every `q ≥ 2` and `n ≥ 1`:
if `t` divides `m` and `⌊m/q⌋ < t ≤ m`, both optima equal `m/(qt)`.
Assign `t` players to each of `m/t` distinct colours at one shared target,
with no queries; this attains the first-moment bound. In particular, `t = m`
has optimum `1/q`. The batch-92 sentence calling every `q ≥ 3` case in this
range open was false; Remark 15.2 retains it with this proof. The general
optimization problem outside the cases established here, and the first
parameters separating the legal and blind optima, remain unclassified by
this report.

## Part III

### The questions

Part I's Research questions Q2 (does Theorem 3.1 survive when cylinder
measurability is replaced by full product-topology Borel measurability, the
Baire property or universal measurability?) and Q5 (characterize all
extensions of the product measure to a finite team's success events,
including their joint laws). They are the report's questions, not Glazer's.

### What it proves

Numbers are the printed ones: the manuscript's Section `k` is Section `k+29`,
its statement `k.m` is `(k+29).m`, its equation `(k)` is `(III.k)`, its
Appendices A–B are F–G and its Figure 1 is Figure 2. Setting: finite alphabet
`Q`, `q ≥ 2`, standard Borel box labels `I`, `X = Q^I`, cylinder σ-algebra `Σ`
with its product probability `μ` and completion `𝒜`; outputs `τ = (b,a)` blind
and `𝒜`-measurable ("regular"); success events not assumed measurable.

- **Lemma 32.1, Lemma 32.2, Corollary 32.3, Lemma 32.4, Corollary 32.6:**
  countable factorization; the open-set sandwich and completion regularity
  `Σ ⊆ ℬ(X) ⊆ 𝒜` with null (and meagre) errors (Kakutani; Gryllakis–Koumoullis,
  credited); an invariant good set for countably many outputs; universally
  measurable outputs are `𝒜`-measurable.
- **Lemmas 33.1–33.2:** diffuse targets escape every countable set; the
  internal success mass of a player is `α_p/q`, `α_p` the atomic mass of its
  target law.
- **Definition 34.1, Lemma 35.1, Theorem 35.2:** the measurable random set
  `Γ(x)` of feasible success patterns (players sharing a diffuse target must
  agree on one colour); every pattern event `E_H` has inner measure
  `μ{Γ ⊆ H}` and outer measure `μ{Γ ∩ H ≠ ∅}`.
- **Theorem 36.1 (answers Q5):** every extension to `σ(𝒜, E_1, …, E_m)`
  corresponds to `𝒜`-measurable densities `h_s ≥ 0`, `Σ h_s = 1`, `h_s = 0` off
  `{s ∈ Γ}`, unique a.e., and every such family defines one; Corollaries
  36.3–36.4: exact ranges of every payoff expectation; uniqueness iff every
  target law is purely atomic.
- **Theorem 37.1:** one player with atomic target mass `α`: inner measure
  `α/q`, outer `1 − (q−1)α/q`, every value in between attained; success is
  measurable iff `α = 1`, and then has probability `1/q`. A version for
  independent strictly positive non-uniform colour laws (Section 37.1).
- **Theorem 38.1:** the joint pattern laws form `Σ_T w_T Δ(T)` with Hall
  (marriage-type) inequalities (Artstein's selection polytope, credited).
- **Theorems 39.1–39.2, Corollary 39.3 (answer Q2's Borel and universal
  clauses):** a fair extension for finite teams; the guaranteed score is
  exactly `⌊m/q⌋` for regular, full Borel and universally measurable blind
  outputs; losing witnesses avoid any prescribed null set; `⌊mr/q⌋` for lists.
- Section 40: examples (every `α`; shared targets force correlations;
  distinct diffuse targets allow every joint law).
- **Theorem 41.1:** countable teams: extensions ⇔ base-measurable kernels
  `K` with `K(x, Γ(x)) = 1` (blindness not needed); **Theorem 41.2:** the
  guaranteed lower asymptotic success density is exactly `1/q`.
- **Proposition 42.1:** a category normal form for Baire-property outputs,
  and an invariant comeagre **null** set, showing why the averaging proof
  does not transfer; Q2's Baire-property clause is **left open**.
- Section 43: logical scope, the executed finite checks, a six-stage
  formalization plan; Section 44: directions R1–R12; Appendices F (assumption
  and result ledger) and G (sources and reproducibility).

### What Part III does not claim

- Glazer's unrestricted ZF question (Q1) is not resolved; the questions are
  the report's, not Glazer's; no endorsement by Glazer.
- The Baire-property clause of Q2 is unresolved; neither a strategy nor an
  impossibility is inferred for it.
- Completion regularity, the measure-extension machinery (Łoś–Marczewski),
  the selection polytope (Artstein) and factorization (Fremlin) are classical
  and credited; Part I's cylinder minimax, target collapse and diagonal example
  are not claimed again.
- Historical priority is not established, nor a breakthrough; no
  proof-assistant certificate; the finite checks do not verify the infinite
  proofs (on a finite space every target law is atomic; the diffuse weights in
  the polytope tests are formal).
- ZFC is the ambient theory; weak-choice strength is not determined; infinite
  alphabets and nonproduct laws are separate problems; the formalization
  stages are proposals.

### Relation to Parts I and II

Re-proofs of Part I: Lemma 32.1 is Lemma 2.4 (`mbg:lem:support`), the
fairness identity of Lemma 33.2 is the fibre identity in the proof of
Theorem 3.1, Theorem 39.1 is Theorem 4.1 for finite teams with completed
measurability. Extensions: Theorem 39.2 and the lists of Section 39.1 extend
Theorem 3.1 and Corollary 3.3. Generalizations: Theorems 35.2, 36.1 and 37.1
generalize Theorems 6.1 (the case `α = 0`), 6.2 (one event) and 5.1. Contacts
with Part II only: the comeagre null set of Section 42 and Part II's conull
meagre success sets (Theorems 26.1–26.2) show the same divergence of measure
and category on different objects, and Theorem 41.2 (worst case, adaptive
targets) and Theorem 25.1 (almost surely, own-hat targets) do not imply each
other.

### Checks made at the write (batch 92)

- **Pin and repository claims.** `1afa38bf9` ("Jointly recode U21 control
  words …", 4 October 2026) is an ancestor of the placement; it holds this
  report after its batch-87 write and before Part II's placement, so the
  manuscript read Part I only. Its claims hold: Q2 and Q5 are as quoted; the
  intake note listed all twelve questions as open at the pin; the cylinder
  minimax, collapse and diagonal example are Part I's; Part I gives blind maps
  no legal tree executes. Nothing refuted; no retraction.
- **Delivered checker** on a scratch copy (Python 3.14.4, Windows): passed in
  about a second; its standard output equals
  `data/03-adaptive-extensions-finite_results.json` after stripping CR bytes.
  The 236/276 split of worst scores over the 512 ordered triples agrees with
  Part I's own table (Section 13).
- The cited literature was not re-read at the write.

## Part IV

### The question

Part II's Research question 29.2, "Information cost versus guaranteed
growth": if player `i` may inspect at most `q(i)` other hats, which excess
profiles remain attainable; in particular, does a uniform bound on `q(i)`
permit `D_n → +∞` almost surely; and how does a bound on the number of
queries differ from a bound on their distance? Two manuscripts written against
the same commit answer it independently, by the same construction, and
neither cites the other; they are not editions of one text.

### How the two sources are merged

**Source 06 is the base** (README section 2 of the intake procedure): on the
shared spine it has the weaker hypotheses and stronger conclusions (any
visibility graph with finitely many colours, Baire-measurable rules, null
*and* meagre divergence sets) and it answers all three clauses of 29.2.
Source 04's proofs assume deterministic decision trees, the hypothesis of
source 06's threshold theorem too, so nothing taken from it rests on a
stronger hypothesis. To keep both numberings, source 06 is printed first and
whole (its Section `k` is Section `k+44`, Sections 45–58), then source 04 (its
Section `k` is Section `k+58`, Sections 59–69); statements and equations
follow the same offsets. Every statement of both is printed in its own place.
Where source 04 states a result source 06 has proved, a dated note says so; a
proof repeating source 06's argument is replaced by a pointer (source 04's
proofs of Lemma 62.1, the path lemma, and Lemma 63.1, the block law; each
note restates what the omitted proof contained), and genuinely different
proofs are printed as second routes (Theorem 61.3, the bounded-depth
obstruction by a sign bound and martingale convergence; Lemmas 61.1–61.2;
Theorem 63.3 and Lemma 63.4, the rates by Kronecker's lemma). Section 45.6
tabulates the shared results.

### What it proves

From source 06 (Sections 45–58):

- **Lemmas 47.1–47.2:** cylinder density; a conditional sign criterion.
- **Theorem 48.2, Lemma 48.3, Corollary 48.4:** a visibility graph with a
  finite colouring forces `P(Σ Y_i ≤ 0), P(Σ Y_i ≥ 0) ≥ 2^(−r)` and null
  (measurable rules) and meagre (Baire rules) divergence events; a common
  bound on adaptive queries gives a finite colouring — **answering the
  uniform-bound clause of 29.2 negatively**, with probability zero.
- **Lemmas 49.1–49.2, Corollary 49.3, Proposition 49.4:** degree bound for
  decision trees, the sign bound `1/(4·9^k)` (sharper `e^(−2k)/4` cited to
  O'Donnell), a Fourier-tail obstruction.
- **Theorem 50.1, Theorem 50.2:** sparse-support cancellation; with one
  query per player the best probability of strictly positive surplus over all
  finite teams is exactly `3/4` (zero queries: `1/2`).
- **Lemma 51.1, Corollary 51.2, Proposition 51.3:** a reachable path of `L`
  queries costs `2 − 2^(1−L)` in expectation, so a uniform expected cap below
  2 forces bounded depth; `E Q < 2` iff the tree is a path.
- **Propositions 52.2–52.3:** Eldredge's block, evaluated partner first with
  early stopping: surplus `−m`/`+1`/`0` with probabilities `4^(−m)`,
  `m·4^(−m)`; the S player's query count is `min(G, 2m−1)`, `G` geometric.
- **Theorem 53.1, Lemma 53.2, Theorem 53.3, Proposition 53.4:** schedules
  with `⌈4^m/m^(1+ε)⌉` blocks give `D_n ~ (log_4 n)^(1−ε)/(1−ε)` and
  `D_n ~ log log n`; **the exact deterministic expected-query threshold is
  2** (`inf sup_i E Q_i = 2`, for positive-probability and for almost-sure
  divergence), attained by a computable strategy with `E Q_i < 2` for each
  player; the construction's success set is conull and meagre.
- **Theorems 54.2–54.4, Proposition 54.5 (answer 29.2's other clauses
  qualitatively):** for count budgets eventually ≥ 1, almost-sure divergence
  ⇔ positive-probability divergence ⇔ `q` unbounded; `h(i) → ∞` permits count
  and distance budgets together; an explicit budget allowed as a count but not
  as a distance; acyclic directed visibility gives independent fair
  correctness.
- **Proposition 55.1, Theorem 55.2:** random seeds with bounded depth still
  fail; with free private coins every expected cap `C > 1` suffices.
- Section 56: checks and a formalization route; Section 57: Research
  questions 57.1–57.12; Section 58: contribution ledger.

From source 04 (Sections 59–69), besides its own versions of the shared core:

- **Theorem 62.2, Corollaries 62.3 and 62.5:** if `P(D_n → +∞) > 0` then
  `sup_i E φ(Q_i) ≥ E φ(G)` for **every** nonnegative nondecreasing cost `φ`:
  no common gap below 2, moments `2, 6, 26`, `E z^Q ≥ z/(2−z)` for
  `1 ≤ z < 2`, none for `z ≥ 2`; Proposition 63.2 attains all of them at once
  (Theorem 60.1).
- **Proposition 63.5, Theorem 63.6, Proposition 63.7:** endpoint central
  limit theorem with exact variance `Σ k(k+1)R_k 4^(−k)`; realized average
  inspection cost → `3/2` almost surely; maximal cost `~ log_2 n`.
- **Lemma 64.1, Theorem 64.2, Corollary 64.4, Theorem 64.5, Proposition
  64.7:** covariance through influences; `Var T_n ≤ n + Σ E Q_i`, sharp;
  concentration; bounded mean inspection forces `S_n/n → 1/2` almost surely;
  spectral escape.
- **Theorems 65.2–65.5 (finite teams):** first-moment saturation
  `P(S ≥ s) = n/(2s)` forces at least `s − 1` inspections of every hat at
  every all-wrong input, so depth ≥ `s − 1`; at depth `s − 1` it is possible
  **iff** `n = m(2^r − 1)`, `s = m·2^(r−1)`, and then the failure set is affine
  with every nonzero parity-check column repeated `m` times (affine Hamming
  codes for odd `n` at strict majority; Bonisoli's classification, credited
  and re-proved in the binary case); a replicated trace strategy over
  `GF(2^r)` attains every such pair. **This settles Part I's Q9 for
  `(m(2^r−1), 2, m(2^r−1))`, `t = m·2^(r−1)`, every `m ≥ 1`**, extending
  Part II's Corollary 20.3 (even `m`), and answers Research questions 29.4 and
  29.5 at minimum depth.
- Section 66: a formalization route; Section 67: the finite checks;
  Section 68: Research questions 68.1–68.12; Section 69: summary.

### What Part IV does not claim

- Eldredge's block rule and the almost-sure divergence it gives are his
  (Proposition 6.6), credited by both sources; the growth results of Part II
  are not re-claimed; hypercontractivity (Bonami, Austrin–Håstad, O'Donnell)
  and the constant-weight classification (Bonisoli) are classical.
- The threshold is `sup_i E Q_i = 2` for **deterministic** trees; individual
  means are below 2; with free randomness the problem changes (a public coin
  breaks the positive-probability lower bound, private coins make every
  `C > 1` sufficient), and the randomized optimum is open.
- Divergence is not eventual positivity (Remark 61.4); the average cost `3/2`
  is attained, not claimed optimal; finite bounds beyond one query are not
  claimed optimal.
- The count-budget classification assumes finitely many zero budgets; count
  and distance differ; general distance profiles are unclassified.
- The finite classification is at minimum depth only: it does not classify
  all optimal strategies or higher-depth extremizers; the affine Hamming
  conclusion is for odd team sizes.
- Finite checks do not prove the general or infinite statements; no
  proof-assistant formalization; unrefereed; priority not established; no
  endorsement by Glazer; Glazer's unrestricted problem is not addressed.

### Checks made at the write (batch 92)

- **Pin.** `9fe62865d` ("Merge branch 'main'", 4 October 2026, 09:56 UTC−7) is
  an ancestor of the placement and contains Part II's archive
  `docs/incoming/hat_guessing_research.zip` (arrival `a162e4386`) but not its
  placement, so both sources read Part II as the delivered
  `hat_guessing_growth.tex`, where 29.2 is Research question 13.2 (lines
  1278–1284). That archive path no longer exists; the archive survives in
  `a162e4386`.
- **Repository claims.** Source 06's (the question, Part II's stronger growth
  constructions, the box-game and list-coding context) and source 04's (the
  predecessor's blob, sizes, line ranges and Theorem 3.2; Part I's blob, its
  Q9–Q12 and the functions of `code/verify_certificates.py`; the list-coding
  blobs `74164ac6`, `b7e037f4`, `c9f8f650` and declarations) all hold. Source
  04's claim that its finite results address the box-game report's
  finite-teamwork program holds for Q9; neither source refines Q11. Nothing
  refuted; no retraction.
- **Programs** on scratch copies (Python 3.14.4, Windows): source 04's
  verifier passed ("Passed 19 exhaustive cases, 59546 hat assignments", about
  6 s) and reproduced its JSON; source 06's block verifier (about 18 s)
  reproduced its JSON, and its orbit verifier (about 1 s) reproduced its JSON
  except `elapsed_seconds` (0.393909 delivered); all comparisons after CR
  stripping. At placement both of source 06's programs also passed under
  `python -O`, its `SHA256SUMS.txt` matched 8/8, and an independent program
  confirmed the trace teams, the block law and the three-player value 3/4.
  The totals printed in Sections 56 and 67 (87,380 assignments; 104,330
  profiles; 59,546 assignments and 838,498 own-hat comparisons) equal the
  shipped JSON.
- **Eldredge.** Source 06 puts his credit to Glazer and Wang on "p. 14",
  source 04 in the paragraph before his Proposition 6.6; the placement found
  it in that paragraph of the v2 HTML text. Austrin–Håstad, Bonami, Bonisoli,
  O'Donnell, Lietz–Winkel and the Samaritan Research page were not checked.
- **Editorial corrections** (disclosed in Section 45.5 and at the places):
  source 04's correctness sign `ε_i g_i`, called `Y_i` in its Section 2 but
  `X_i` in its Sections 3 and 6, is `Y_i` throughout, as in source 06, where
  `X_i` is the hat; source 04's "D player" (clashing with the surplus `D_n`)
  is source 06's "T player"; source 04's equation (5.18), now (63.18), printed
  `3/2 − 1/2 , 4^(1−k_b)` with a comma for a product, corrected with a dated
  note. Source 04's bibliography lists Butler, Hajiaghayi, Kleinberg and
  Leighton, *Hat guessing games* (2008), which its text never cites; the
  entry is kept and cited from Section 45.5, unchecked.

## Relation to the repository

**Formal status.** No statement of any Part is formalized in Lean or Rocq.
Part I's manuscript read three files at its pin, all byte-identical at its
write: `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` (blob `4961655e`),
`Logic/PeanoArithmetic/ListCoding/README.md` (`74164ac6`) and
`SetTheory/ClosureAxiomatization/README.md` (`fb0ab511`). Its descriptions of
them (Sections 12 and 14.2) are accurate. They are used as architectural
interfaces only: no repository theorem enters a proof. The Busy Beaver
development formalizes blank-tape machines, halting scores and the domination
theorem with the compiler as a stated hypothesis; it says nothing about the
horizon `H` or `BB_time` of Section 12. Part II proposes encoding its finite
tables with the list-coding interfaces (Section 28.2); no such development
exists. Parts III and IV propose formalization stages (Sections 43.3, 56.3
and 66) and Part IV's sources read the list-coding files (unchanged since);
no Lean or Rocq file states any of their results.

**Review in the Hilbert's-tenth research tree.** Before Part I's placement,
another session reviewed all six batch-87 archives at their arrival revision
(commit `f15962acd`):
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_baire_polish_arithmetic_intake.md`,
with `review_baire_polish_arithmetic_intake_independent.md` and the receipt
`review_baire_polish_arithmetic_intake.json` beside it. For Part I's
manuscript it read the delivered lines 64–73, 82–110, 386–428, 776–820 and
927–955 (abstract, Sections 1–1.3, Section 7 through Lemma 7.4, Section 12,
conclusion and Appendix A). It confirms the sliceable-matching
characterization and the non-executability of blind tables, that the totality
promise of Theorem 12.1 is essential, and that the Busy Beaver inequality is
conditional on the encoding and compiler; it finds no fixed-size Diophantine
history certificate or paid arithmetic schedule, so the 84-operation
universal polynomial of the Hilbert's-tenth programme is unaffected; and it
did **not** review the probability, enumeration or asymptotic claims. No
scope correction was needed. The article's Section 1.4 note records this.
For Part II, the same tree's review
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_polish_partx_c9bc70d8f.md`
(commit `bcc1a4438`, after the batch-90 placement) inventoried the six
batch-90 archives at `a162e4386` and, for this one, read only the delivery
`README.txt` and `code/README.txt`: it routes the package as finite-dependence
hat strategies with asymptotic surplus, whose finite XOR/parity diagnostics
have size-dependent exhaustive scope, with no paid Diophantine source; it ran
no program and did not read the manuscript. A second review beside it,
`review_batch90_placement_12076b2e8.md` (commit `3c25fbb55`), authenticated
the placement by byte comparison (every placed Part II file equals its archive
member; the CSV keeps its CRLF bytes; host article and README unchanged at
the placement) without reading the files as mathematics. No bound of that
programme changes; no scope correction follows. Section 17.3 records both.
For batch 92, the same tree's
`review_latest_five_9dc8db274.md` (commit `3c25fbb55`, before the placement)
inventoried Part III's and Part IV's source 04 archives with three others: it
read only the delivery `README.txt` of each (lines 1–97 and 1–96),
authenticated members by hash, ran nothing, and routed them as measurable
extension laws (no algorithmic compiler follows from extending a measure) and
as query costs (the charged resource is observed hats, not arithmetic gates;
public randomness changes the model). `review_hat_threshold_afd7ffabb.md`
(commit `b560cee86`) reviewed source 06 mathematically: its README and
`SOURCE_NOTES.txt` in full and its lines 216–578, 795–1380 and 1466–1663
(Sections 46–49.3, 51–54.3 and 55–56 here), with "no finding in the inspected
proof"; it verified the checksum file 8/8, ran no program, did not check the
sharper constant cited to O'Donnell, the bibliography or novelty, and does not
supersede the README-only intake of source 04. Not reviewed there: Section 45,
Proposition 49.4, Section 50, Theorem 54.4, Proposition 54.5, Sections 57–58
and all of source 04. Both leave that programme's arithmetic bounds
unchanged; no scope correction follows. Sections 30.3 and 45.5 record them.

**Neighbouring reports.** None shares a theorem or a question with any
Part. Before batch 90 nothing in ProveIt treated box, hat, guessing or
prediction games (search of the tracked tree at the batch-87 placement,
including `2211.10474` and A005271); Parts II–IV are now the repository's
hat- and box-game material, and the batch-90 and batch-92 placements found no
other.

- `../games-on-ordinals/` holds different games: in
  `open-query-membership-games` a Seeker asks open-set queries about a hidden
  point (adaptive query strategies and finite-budget certificates, but no
  guess at an unread coordinate); `point-separating-game-values` and
  `ordinal-chomp-transition-at-two` are point-separating games and ordinal
  Chomp.
- `../non-baire-translation-invariant-ideal/` is the nearest in spirit to
  Part I: a ZFC construction, from a free ultrafilter, of an ideal without the
  Baire property, the kind of irregular object Research question Q2 asks
  about for the Baire-property version of Theorem 3.1. Since batch 92 that
  is the only clause of Q2 still open (Part III, Section 42), and Part III's
  invariant comeagre null set is another ZFC measure-versus-category contrast;
  no theorem is shared.
- `../games-on-ordinals/open-query-membership-games` also counts adaptive
  queries and certifies finite budgets; Part IV's query costs concern
  observed hats in a guessing game, not open-set queries about a hidden point;
  no theorem is shared.
- The five sister manuscripts of batch 87 concern Glazer's *other* question
  paper, *A Topological Tennenbaum Theorem* (arXiv:2311.13699), and became
  Parts VI–IX of
  `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic`.
  Different subject, no shared notation. In particular **"Glazer's
  Question 1" there (answered as claimed, unrefereed, in its Part VIII) is not
  Q1 here.** Part II's batch-90 siblings went to that report (Parts XI–XII),
  to `discrete-initial-subgroups-and-omnific-normalization`,
  `birthday-cutoffs-and-hereditary-sets` and the new
  `cantor-families-of-surreal-subfields`; none shares a theorem with Part II.

**Stale claims.** Part I's statement (Section 1.4 note) that the report is a
single manuscript and that nothing in ProveIt treats hat games was true at its
write; a dated batch-90 note there now says both are superseded by Part II,
and the batch-87 note "All twelve questions stay open as printed" is
qualified by a dated note on Q9. Batch 92 added dated notes in Section 1.4
(four Parts), after Section 15 (Q2 and Q5 answered, Q9's larger family) and
after Part II's questions (29.2 answered; 29.4 and 29.5 at minimum depth;
29.10 still open), and Remark 15.1, which refutes the batch-90 sentence
"Every other (m,q,n,t) remains open" (it was false when written; it stays on
record). The line above the contents now announces four Parts. No other
sentence of Parts I–II became false.

## Notation

Part I reuses letters with local meanings: `γ` (growth constant, not
Euler's), `F_n`/`M_n`/`B_n`/`L_n`, `BB_time` and `H` (horizon in Section 12,
entropy in Section 11), `I` (boxes; mutual information), `E` (expectation,
success sets), `C` (a group of players; Cantor space; the series `C(z)`), `D`,
`r`, `R`, `T`, `L`, `Q`/`𝒬_n`/`q`, and `Σ_I` (cylinder, not Borel,
σ-algebra). The table of Section 1.5 fixes each one with its tempting false
reading. No symbol was renamed.

Part II's letters collide with Part I's: `t` (columns per round, not Q9's
threshold), `D_n` (surplus, not `D(u)` or `D_6`), `r`, `a`, `M`, `F`, `C`,
`B_k`, `L_k`, `R_k`, `T_i`, `H`, `U`, `Z_i`, `q`, `K`, `σ`, and the words
*legal* (Part II: a guess unchanged when one's own hat changes, i.e. Part I's
*blind* with a fixed target) and *measurable* (countable product, not Part I's
cylinder σ-algebra on uncountable products). The table of Section 17.4 gives
each with its Part I meaning. No symbol was renamed; the manuscript's `\PP`,
`\EE` print with Part I's macros for the same symbols ℙ, 𝔼.

Part III (table in Section 30.4) keeps its letters: `𝒜` (completion), `ℬ(X)`,
`𝓕` (the enlarged σ-algebra, **not** Part II's blackboard `𝔽` of `𝔽_2`; its
macro `\F` was renamed `\Fext` because Part II's `\F` is the blackboard
letter), `Γ`, `D_s`, `D_H`, `L_H` (not the surplus `D_n`), `G` (good set), `α`
(atomic mass), `T`, `K`, `Ω_m`, and the directions R1–R12. Its `\Prob` prints
with Part I's `ℙ` macro; its colours and result box are Part I's.

Part IV (table in Section 45.7) keeps both sources' letters with two
renamings in source 04, disclosed in Section 45.5: its correctness sign
`ε_i g_i` is `Y_i` throughout (source 04 also called it `X_i`, which is the
hat in source 06), and its "D player" is source 06's "T player". `F_n` (06)
and `T_n` (04) are the same quantity `2D_n`, **not** Part I's `F_n`; `G` is a
geometric variable (and in source 06 a visibility graph), `Q_i` a query count
(not Part I's alphabet), `q(i)` and `h(i)` count and distance budgets; source
04's indicator macro with an argument prints as before through a new macro
`\indic`, its "almost surely" macro as those words.

## Labels

Every label carries the prefix `mbg:`; Part II's carry `mbg:hat:`, Part
III's `mbg:ext:`, Part IV's `mbg:qry:` (source 06) and `mbg:insp:` (source
04). **335 labels** after the batch-92 review (126 before; none removed or renamed): the
199 delivered labels of the three batch-92 manuscripts (62, 66 and 71),
prefixed with every reference updated, and ten added by the write and review —
`mbg:ext:part`, `mbg:ext:sec:provenance`, `mbg:ext:sec:notation`,
`mbg:qry:part`, `mbg:qry:sec:provenance`, `mbg:qry:sec:merge`,
`mbg:qry:sec:notation`, `mbg:qry:sec:conclusions` (source 06's unlabelled
Section 14), `mbg:insp:rem:q9-open-claim` (Remark 15.1), and
`mbg:insp:rem:q9-divisor-cases` (Remark 15.2). All 126 earlier
labels and all 13 earlier bibliography numbers print as before (compared with
a build of the committed text), and every one of the 199 delivered labels
prints its source's number shifted by the stated offset (compared with
standalone builds of the three manuscripts). The history of the first 126:

Part I:
the manuscript's 61 labels were prefixed before anything cited them and every
reference updated (19 `\ref`, 44 `\eqref`); the batch-87 write added four
(`mbg:sec:provenance`, `mbg:sec:notation`, `mbg:app:ledger`,
`mbg:app:audit`): 65 labels. Part II: the 55 delivered labels prefixed
`mbg:hat:` with every reference updated; the batch-90 write added
`mbg:part:one`, `mbg:hat:part`, `mbg:hat:sec:provenance`,
`mbg:hat:sec:notation`, `mbg:hat:rem:wording` and `mbg:hat:q:finiteteam`:
**126 labels**, none removed or renamed. No section, theorem, equation or
bibliography number of Part I moved (all 65 labels and 9 citation numbers
compared with a build of the batch-87 text; only page numbers moved, by one
or two pages). Part II continues Part I's numbering (Sections 17–29,
Appendices C–E, equations `(k+16).m` as explicit tags, bibliography entries
10–13; its Glazer entry is Part I's entry 1).

The batch-87 write also:

- added dated `[write]` notes: Section 1.4 (provenance, pin and repository
  claims, Glazer's paper, the Hilbert's-tenth review, OEIS, neighbouring
  reports), Section 1.5 (notation table), after the table of Section 8
  (`M_6` in A005271), after the enclosure of `γ` in Section 9.4, at the end of
  Section 12 (Busy Beaver formal status), after the verification box of
  Section 13 (shipped layout and replay), after the questions of Section 15
  (status of Q1 and Q8) and in Appendix B (sources checked, checksum
  manifest);
- added a one-line `[write]` pointer on the title page and a dated addition to
  bibliography entry 1 (the arXiv record);
- wrapped the title page in `\hypersetup{pageanchor=false}` … `=true`: the
  delivered source, rebuilt with MiKTeX, gave a duplicate `page.1`
  destination.

The batch-90 write:

- wrapped the existing text as Part I (`\part` before Section 1) and appended
  Part II after Part I's appendices, before the shared bibliography; a
  `[write]` line above the contents announces the two Parts;
- added dated `[write]` notes in Part I: Section 1.4 (two Parts; stale
  statements) and after Section 15 (status of Q9); in Part II: at its head
  (numbering offset), Section 17.3 (provenance, pin, repository claims,
  Eldredge's text, prior art, editorial changes), Section 17.4 (notation
  table), after Corollary 20.3 (Q9), after Section 22.1 (Eldredge's
  Proposition 6.6 and Remark 6.7), after Theorem 23.1 (question (1)), after
  Remark 24.4 (the wording check), after Theorem 25.1 (inherited, second
  route), in Section 28.1 (shipped layout and replay), after Section 29
  (status of the questions), in Appendix E (delivery names); and dated
  additions to bibliography entries 10–12;
- printed the manuscript's title page as the Part heading with its abstract,
  status box and keywords; renumbered by the offset 16; set Part I's macros
  for `\PP`, `\EE`, `\repo` and Part I's remark style; included the figure
  unconditionally from its shipped name (the manuscript included it only if
  present); added `graphicx`, `listings`, the macros `\F`, `\xor`, `\as`,
  `\FIN`, the `question` environment, the colour `muted` and the manuscript's
  `\lstset` to the preamble, which change nothing in Part I.

The batch-92 write:

- appended Part III (manuscript 03) after Part II's appendices and Part IV
  (sources 06, then 04) after Part III's appendices, before the shared
  bibliography; the line above the contents now announces four Parts;
- numbered Part III's sections by the offset 29 (appendices F–G), its
  consecutively numbered equations as `(III.k)`; Part IV's by the offsets 44
  (source 06) and 58 (source 04), with equations numbered within sections
  from Part IV on (`\counterwithin`), as both manuscripts did; Part III's
  figure is Figure 2;
- added dated `[write]` notes: in Part I, Section 1.4 (four Parts) and after
  Section 15 (status of Q2, Q5 and Q9), plus **Remark 15.1**; in Part II,
  after Section 29 (status of 29.2, 29.4, 29.5, 29.10) and a dated addition to
  bibliography entry 10 (Eldredge); in Part III, at its head (offsets),
  Sections 30.3–30.4 (provenance, notation), after Section 43.2 (shipped
  names, rerun), after Section 44 (status of R1–R12), in Appendix G (delivery
  names); in Part IV, at its head (offsets, merge rule), Sections 45.5–45.7
  (provenance, merge, notation), after Corollary 48.4, Lemma 49.2,
  Theorem 50.2, Proposition 51.3, Proposition 52.3, Theorem 53.3,
  Proposition 53.4, Section 54, Section 55, Section 56.2, Section 57, at the
  end of Section 59 and of Section 60.3, before Lemma 61.1, after Theorem 61.3,
  in place of source 04's proofs of Lemmas 62.1 and 63.1, after Theorem 63.3,
  after equation (63.18) (the correction), at the end of Section 65, Section
  67 and Section 68, and at the head of Section 69; and dated notes in the new
  bibliography entries that merge or identify sources;
- printed the title pages as Part headings with abstracts and status boxes
  (and source 04's keywords); set Part I's macros for `\Prob`/`\PP`, `\EE`,
  `\repo`, Part I's remark style, colours and result box; added `tikz` and
  `pgfplots` (Part III's figure is drawn by the manuscript's own code), the
  macros `\Fext`, `\A`, `\B`, `\cyl`, `\conv`, `\extsnap`, `\qrypin`,
  `\indic`, `\norm` and the operators `\Var`, `\Inf` to the preamble, which
  change nothing in Parts I–II;
- merged duplicate bibliography entries (Glazer's paper, Łoś–Marczewski,
  Eldredge and Ebert–Merkle–Vollmer are Parts I–II's entries 1, 4, 10, 11;
  Glazer's dissertation, the predecessor, the box-game report and list
  coding are one entry each, entries 14, 26–28); new entries 14–35 follow
  Part II's.

No statement, proof or non-claim of any manuscript was changed, apart from
the disclosed renamings, the pointer proofs and the one corrected typo of
Part IV.

## Files

```text
README.md                                         this guide (replaces Part I's delivered README.md, staged under this name)
article.tex                                       the report: Parts I-IV (delivered article.tex, hat_guessing_growth.tex, adaptive_box_games.tex, hat_query_thresholds.tex with hat_inspection_frontier.tex), labels prefixed, [write] notes
article.pdf                                       compiled report, 144 pages (unnumbered title page, then pages 1-143)
02-hat-surplus-source_audit.txt                   Part II: delivered source and claim audit (source_audit.txt)
04-hat-inspection-PROOF_STATUS.txt                Part IV, source 04: delivered proof-status record (PROOF_STATUS.txt)
04-hat-inspection-SOURCE_AUDIT.txt                Part IV, source 04: delivered source and claim audit (SOURCE_AUDIT.txt)
05-hat-queries-SOURCE_NOTES.txt                   Part IV, source 06: delivered source snapshot and contribution audit (SOURCE_NOTES.txt)
code/verify_certificates.py                       Part I: exact finite enumerations and certificate checks (standard library)
code/formal_series.py                             Part I: exact rational formal-series coefficients through a chosen degree
code/Makefile                                     Part I: delivered targets pdf, verify, clean (delivery layout; see below)
code/02-hat-surplus-verify_hat_strategy.py        Part II: exhaustive finite verifier (standard library)
code/02-hat-surplus-make_figures.py               Part II: regenerates Figure 1 (Matplotlib, NumPy)
code/02-hat-surplus-README.txt                    Part II: delivered verifier README (code/README.txt)
code/02-hat-surplus-Makefile                      Part II: delivered targets pdf, verify, figures (delivery layout)
code/02-hat-surplus-LICENSE.txt                   Part II: the code's own permissive licence (code/LICENSE.txt)
code/03-adaptive-extensions-verify_finite.py      Part III: exact finite checks, JSON on standard output (verify_finite.py)
code/03-adaptive-extensions-finite_checks_README.txt  Part III: methods and scope of the finite checks (finite_checks_README.txt)
code/04-hat-inspection-verify_finite.py           Part IV, source 04: exhaustive checks of blocks and trace teams (code/verify_finite.py)
code/04-hat-inspection-build.sh                   Part IV, source 04: three pdflatex passes of the unshipped manuscript (build.sh)
code/05-hat-queries-verify_hat_queries.py         Part IV, source 06: block and query-algorithm verifier (verify_hat_queries.py)
code/05-hat-queries-verify_orbit_bounds.py        Part IV, source 06: one-query enumeration and orbit verifier (verify_orbit_bounds.py)
data/certificates.json                            Part I: the four-box non-executable blind rule and the three-box team with P(score >= 2) = 3/4
data/verification_report.json                     Part I: recorded run of verify_certificates.py
data/formal_series_report.json                    Part I: recorded run of formal_series.py --degree 10
data/02-hat-surplus-verification.json             Part II: recorded verifier run (nine cases)
data/02-hat-surplus-examples.json                 Part II: one good and one bad block assignment
data/02-hat-surplus-example_prefix.csv            Part II: prefix path of the good example (CRLF, as delivered)
data/03-adaptive-extensions-finite_results.json   Part III: recorded output of the checker (finite_results.json)
data/04-hat-inspection-verification.json          Part IV, source 04: recorded run, 19 cases (data/verification.json)
data/05-hat-queries-hat_query_verification.json   Part IV, source 06: recorded block-verifier run (hat_query_verification.json)
data/05-hat-queries-orbit_verification.json       Part IV, source 06: recorded orbit-verifier run (orbit_verification.json)
figures/02-hat-surplus-block_prefix.pdf           Part II: Figure 1, included by article.tex
figures/02-hat-surplus-block_prefix.png           Part II: raster copy of Figure 1 (not used by the article)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Part I: placement moved the programs and
`Makefile` to `code/` and the three JSON files to `data/`. Part II: placement
(`12076b2e8`) added the prefix `02-hat-surplus-` and kept the delivered
`code/`, `data/` and `figures/` layout; the audit moved to the report root.
`data/02-hat-surplus-example_prefix.csv` is delivered with CRLF line ends and
kept so by a `-text` line in `SetTheory/Cardinals/.gitattributes`. Parts III
and IV: placement (`e38f368c2`) added the prefixes `03-adaptive-extensions-`,
`04-hat-inspection-` and `05-hat-queries-`, put programs and build script in
`code/`, outputs in `data/`, audits and notes at the report root, and moved
Part III's methods text to `code/` (as Part II's `code/README.txt`); no staged
file has CR bytes. The batch-92 packages ship no licence file; their code is
the packages' own and falls under the repository's MIT-0.

**Licence.** `code/02-hat-surplus-LICENSE.txt` is the Part II package's own
licence for its original code: permission to use, copy, modify, publish,
distribute, sublicense and sell, "with or without attribution", without
warranty. It asks nothing that MIT-0 (the repository's licence) does not
already grant and imposes no attribution condition, so it is compatible with
MIT-0; it is kept beside the code it governs.

**Not shipped**, surviving in the arrival archives:
Part I — the delivered 24-page `article.pdf` (332,597 bytes), the delivered
README (this file replaces it) and the checksum manifest `SHA256SUMS` (nine
entries, verified 9/9 at placement, dropped by repository policy):
`git show fa0a0576e:docs/incoming/glazer_box_games_research.zip > <scratch>/glazer_box_games_research.zip`.
Part II — `hat_guessing_growth.tex` (its text is Part II of `article.tex`),
the delivered 22-page A4 `hat_guessing_growth.pdf` and the top-level
`README.txt`; the package has no checksum manifest:
`git show a162e4386:docs/incoming/hat_guessing_research.zip > <scratch>/hat_guessing_research.zip`.
Part III — `adaptive_box_games.tex` (its text is Part III), the delivered
29-page `adaptive_box_games.pdf` (455,311 bytes) and `README.txt`; no
checksum manifest:
`git show 9dc8db274:docs/incoming/adaptive_box_games_research.zip > <scratch>/adaptive_box_games_research.zip`.
Part IV, source 04 — `hat_inspection_frontier.tex` (Sections 59–69), the
delivered 31-page A4 `hat_inspection_frontier.pdf` (451,026 bytes) and
`README.txt`; no checksum manifest:
`git show 9dc8db274:docs/incoming/hat_inspection_frontier.zip > <scratch>/hat_inspection_frontier.zip`.
Part IV, source 06 — `hat_query_thresholds.tex` (Sections 45–58), the
delivered 26-page `hat_query_thresholds.pdf` (439,236 bytes, metadata author
"ChatGPT research report"), `README.txt` and the checksum manifest
`SHA256SUMS.txt` (eight entries, verified 8/8 at placement, dropped by
repository policy):
`git show afd7ffabb:docs/incoming/hat_query_thresholds_package.zip > <scratch>/hat_query_thresholds_package.zip`.
Nothing was excluded as heavy.

Delivered text that names the delivery layout or a file not shipped:
Part I — `code/Makefile` (runs `verify_certificates.py`, `formal_series.py`
and `latexmk … article.tex` in one flat directory); both programs (default
outputs `verification_report.json`, `certificates.json` and
`formal_series_report.json` in the current directory);
`data/verification_report.json` and `data/formal_series_report.json` (no
paths). The article's Section 13 names the programs by their delivered names;
a note there gives the shipped paths. The delivered README named
`article.pdf` (its own build), `SHA256SUMS` and the flat layout.
Part II — `code/02-hat-surplus-Makefile` (`pdflatex hat_guessing_growth.tex`,
`python3 code/verify_hat_strategy.py`, `python3 code/make_figures.py`, from
the package root); `code/02-hat-surplus-README.txt` (`verify_hat_strategy.py`,
default outputs `../data/verification.json`, `examples.json`,
`example_prefix.csv`); `02-hat-surplus-source_audit.txt`
(`data/verification.json`); `data/02-hat-surplus-verification.json` (its
`examples_json` and `good_prefix_csv` fields name `examples.json` and
`example_prefix.csv`); the article's Sections 28.1 and
Appendix E (delivery names and the PDF build of `hat_guessing_growth.tex`;
notes there give the shipped names). The verifier's default output is
`../data/verification.json` relative to its own directory, so run in place it
would write unprefixed `verification.json`, `examples.json` and
`example_prefix.csv` into this report's `data/`; the figure script always
writes `figures/block_prefix.pdf` and `.png` beside `code/`'s parent.
Part III — `code/03-adaptive-extensions-finite_checks_README.txt` and the
article's Appendix G (`python3 verify_finite.py > finite_results.json`, the
build of `adaptive_box_games.tex`; notes in Sections 43.2 and G give the
shipped names); the program prints its JSON to standard output and writes no
file.
Part IV, source 04 — `code/04-hat-inspection-build.sh`
(`pdflatex hat_inspection_frontier.tex`, three passes);
`code/04-hat-inspection-verify_finite.py` (always writes
`../data/verification.json` relative to itself, so run in place it would add
an unprefixed `data/verification.json` here); `04-hat-inspection-SOURCE_AUDIT.txt`
(`PROOF_STATUS.txt`, `docs/incoming/hat_guessing_research.zip`, which no
longer exists in the tree); `04-hat-inspection-PROOF_STATUS.txt` (the same
archive); `data/04-hat-inspection-verification.json` (its block records say
`D_query_counts_per_player` for the role printed as T); the article's
Section 67 (delivery names; a note there gives the shipped ones).
Part IV, source 06 — both programs (default outputs
`hat_query_verification.json` and `orbit_verification.json` beside the
program, so run in place they would add unprefixed files to `code/`; both
accept `--output`); `05-hat-queries-SOURCE_NOTES.txt` (the retired archive
path); the article's Section 56 (delivery names; a note there gives the
shipped ones). Source 06's verifier and its delivered README call the T role
D.

## Rerun the checks (on a scratch copy)

**Part I.** Never run the programs in place without explicit output paths:
run without arguments, `verify_certificates.py` rewrites
`verification_report.json` **and `certificates.json`** in the current
directory, and `formal_series.py` rewrites `formal_series_report.json`.
Python 3.10 or newer, standard library only; do not use `python -O`
(`formal_series.py` checks with `assert`). From this directory, in Git Bash
(on a POSIX host use `python3` for `py`):

```sh
D=$(pwd); T=$(mktemp -d)
cp code/verify_certificates.py code/formal_series.py code/Makefile data/certificates.json data/verification_report.json data/formal_series_report.json "$T/"
cd "$T"
py verify_certificates.py                        # prints "status": "all exact checks passed"
py verify_certificates.py --check certificates.json
py formal_series.py --degree 10                  # prints the series and "Report: ..."
for f in certificates.json verification_report.json formal_series_report.json; do
  tr -d '\r' < "$f" | cmp -s - "$D/data/$f" && echo "same  $f" || echo "DIFF  $f"; done
```

The certificate check alone is read-only and can run on the shipped file:
`py code/verify_certificates.py --check data/certificates.json`. At intake
(3 October 2026, Python 3.14.4, Windows) the three commands passed in about
five seconds in all, and all three files compared `same`: on Windows the
programs write CRLF line ends (text mode), so compare after stripping `\r`
as above. The recorded run covers exhaustive matchings of `Q_1`–`Q_4`
(272 at `n = 4`, 232 sliceable), `M_5 = 589185` by a permanent dynamic
program, the 256 two-box tables (8 blind) and all 4,680 ordered teams of one
to four of them, 1,320 balanced-list constructions, `F_n` to `n = 12` (and
the recurrence to `n = 20` for the `γ` enclosure), the ternary values to
`n = 5`, and the rarity comparison.

**Part II.** Copy the two programs under their delivered names into a
scratch tree with a `code/` directory; the verifier then writes `data/` and
the figure script `figures/` inside that tree. Python 3.10 or newer; the
verifier needs only the standard library, the figure script Matplotlib and
NumPy. From this directory:

```sh
D=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"
cp code/02-hat-surplus-verify_hat_strategy.py "$T/code/verify_hat_strategy.py"
cp code/02-hat-surplus-make_figures.py "$T/code/make_figures.py"
cd "$T"
py code/verify_hat_strategy.py                  # nine "PASS" lines, then "Verified 9 cases, 284,052 inputs, ..."
for f in examples.json example_prefix.csv; do
  tr -d '\r' < "data/$f" | cmp -s - <(tr -d '\r' < "$D/data/02-hat-surplus-$f") && echo "same  $f" || echo "DIFF  $f"; done
strip() { grep -vE '"(completed_at_utc|python_version|elapsed_seconds)"' "$1" | tr -d '\r'; }
cmp <(strip data/verification.json) <(strip "$D/data/02-hat-surplus-verification.json") && echo "same  verification.json (but time, version, elapsed)"
uv run --no-project --with matplotlib==3.10.8 --with numpy python code/make_figures.py   # writes figures/block_prefix.pdf and .png
```

`--case R A` selects cases and `--output PATH` redirects the report (the two
example files go beside it); `--max-n` raises the default limit `N ≤ 18`. At
the write (4 October 2026, Python 3.14.4, Windows) all three comparisons
printed `same`, the verifier taking about 112 s on a loaded machine (37 s at
placement).
With Matplotlib 3.10.8 the regenerated PDF figure differs from the shipped
one only in its creation date (6 bytes), and the PNG has the same size
(1735 × 646) but different bytes; a newer Matplotlib (tried at the write)
gives a visibly equivalent but differently encoded PDF. The shipped figure
files are the delivered ones.

**Part III.** The checker prints its JSON to standard output; redirect it
into a scratch file. Python 3.9 or newer, standard library only. From this
directory:

```sh
D=$(pwd); T=$(mktemp -d)
cp code/03-adaptive-extensions-verify_finite.py "$T/verify_finite.py"
cd "$T"
py verify_finite.py > finite_results.json        # exit status 0; "status": "all_exact_checks_passed"
tr -d '\r' < finite_results.json | cmp -s - "$D/data/03-adaptive-extensions-finite_results.json" && echo "same  finite_results.json"
```

At the write (4 October 2026, Python 3.14.4, Windows) it ran in about a
second and printed `same` (on Windows the redirected output has CRLF line
ends, hence the `tr`).

**Part IV.** Source 04's verifier writes `../data/verification.json`
relative to itself, so copy it into a `code/` directory of a scratch tree;
source 06's programs write beside themselves (or to `--output PATH`). Python
3.8 (source 04) or 3.10 (source 06) or newer, standard library only. From
this directory:

```sh
D=$(pwd); T=$(mktemp -d); mkdir -p "$T/code"
cp code/04-hat-inspection-verify_finite.py "$T/code/verify_finite.py"
cp code/05-hat-queries-verify_hat_queries.py "$T/verify_hat_queries.py"
cp code/05-hat-queries-verify_orbit_bounds.py "$T/verify_orbit_bounds.py"
cd "$T"
py code/verify_finite.py                          # "Passed 19 exhaustive cases, 59546 hat assignments."
py verify_hat_queries.py                          # writes hat_query_verification.json here
py verify_orbit_bounds.py                         # writes orbit_verification.json here
s() { tr -d '\r' < "$1"; }
cmp <(s data/verification.json) "$D/data/04-hat-inspection-verification.json" && echo "same  verification.json"
cmp <(s hat_query_verification.json) "$D/data/05-hat-queries-hat_query_verification.json" && echo "same  hat_query_verification.json"
cmp <(s orbit_verification.json | grep -v elapsed_seconds) <(grep -v elapsed_seconds "$D/data/05-hat-queries-orbit_verification.json") && echo "same  orbit_verification.json (but elapsed time)"
```

At the write (Python 3.14.4, Windows) the three runs took about 6, 18 and
1 seconds and all three comparisons printed `same`. Source 06's checks are
explicit runtime tests and also pass under `python -O` (checked at
placement); source 04's verifier is not documented for `-O`, so run it
without. The build script `code/04-hat-inspection-build.sh` compiles the
unshipped `hat_inspection_frontier.tex`; to rebuild the delivered PDF,
extract the archive (see "Not shipped") and run it there.

## Build the PDF

pdfLaTeX with newtxtext/newtxmath, amsthm, geometry, microtype, mathtools,
booktabs, longtable, array, enumitem, xcolor, fancyhdr, titlesec, tcolorbox,
xurl, graphicx, listings, tikz, pgfplots and hyperref; the bibliography is
inline. The
article includes `figures/02-hat-surplus-block_prefix.pdf`, so copy it too.
Build in a scratch copy:

```sh
B=$(mktemp -d); mkdir -p "$B/figures"
cp article.tex "$B/"; cp figures/02-hat-surplus-block_prefix.pdf "$B/figures/"
cd "$B"; latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX (4 October 2026, batch 92):
143 pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The log has four informational lines "Infinite glue
shrinkage found in box being split" (ignored by TeX when a page breaks inside
a framed box or note); the committed batch-90 text, built the same way (53
pages), has one. The batch-87 text gives 26 pages with a clean log; its
delivered source gave 24 pages and one duplicate-destination warning
(`page.1`), removed as described under Labels.

The arithmetic-research review corrected the later Q9 open-range claim with
Remark 15.2 and repaired `\ind C` to `\indic{C}` in Theorem 65.3. A direct
three-pass `pdflatex -no-shell-escape` rebuild of this edited source produced
144 pages, with no undefined references/citations or bad boxes; the only
warning reports the intentionally disabled shell escape. PDF pages 29 and
131 were visually inspected for the new remark and repaired indicator. The
immutable [publication review](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_box_publication_721cf8196.md)
retains both original findings and its exact proof-read limits.

## Provenance

- Part I, sources cited by the manuscript: Glazer, arXiv:2211.10474 (the
  anchor) and arXiv:2312.11902; the FrontierMath competition post with
  Glazer's author profile; Łoś–Marczewski, *Extensions of measure*, Fund.
  Math. 36 (1949) 267–276; OEIS A005271; the three ProveIt files above at the
  pin. Repository input: the pin `6fef5383b` (3 October 2026, the batch-85C
  write of `a181199-shifted-rectangles`), an ancestor of the placement.
  Batch 87 of `docs/incoming`, manuscript 02 of six; arrival `fa0a0576e`,
  placement `d151b39ca`, written in the batch-87 write phase (3 October 2026).
- Part II, sources cited by the manuscript: Eldredge, arXiv:2508.02828v2 (the
  questions answered); Ebert, Merkle and Vollmer, *On the Autoreducibility of
  Random Sequences*, SIAM J. Comput. 32(6) (2003) 1542–1569, with its ECCC
  preprint (the credited prior art); Glazer, arXiv:2211.10474 (the broader
  connection); Part I of this report and the list-coding files at the pin
  `7c0f2d9f9` (the batch-89 arrival commit, 3 October 2026), an ancestor of
  the placement. Batch 90 of `docs/incoming`, manuscript 02 of six; arrival
  `a162e4386`, placement `12076b2e8`, written in the batch-90 write phase
  (4 October 2026).
- Part III, sources cited by the manuscript: Glazer, arXiv:2211.10474 and
  his Harvard dissertation (2023); Part I of this report at the pin
  `1afa38bf9` (4 October 2026), an ancestor of the placement; Kakutani
  (1943), Gryllakis–Koumoullis (1990), Fremlin's *Measure Theory* (254P, 4A2E,
  4A3N, 4A3S), Łoś–Marczewski (1949), Artstein (1983), Janson (2013), Vidmar
  (2021). Batch 92 of `docs/incoming`, manuscript 03 of six; arrival
  `9dc8db274`, placement `e38f368c2`, written in the batch-92 write phase
  (4 October 2026).
- Part IV, sources cited by the manuscripts: Eldredge, arXiv:2508.02828v2
  (the block rule, credited); Glazer, arXiv:2211.10474 and his dissertation;
  Part II (as the delivered `hat_guessing_growth.tex`), Part I and the
  list-coding project at the common pin `9fe62865d` (4 October 2026), an
  ancestor of the placement; source 06 also Ebert–Merkle–Vollmer (2003),
  Bonami (1970) and O'Donnell (2014/2021); source 04 also Austrin–Håstad
  (2009, 2011), Bonisoli (1984), Lietz–Winkel (2024), a Samaritan Research
  article (2025) and, uncited in its text, Butler–Hajiaghayi–Kleinberg–Leighton
  (2008). Batch 92, manuscripts 06 (arrival `afd7ffabb`) and 04 (arrival
  `9dc8db274`); placement `e38f368c2`; written in the batch-92 write phase.
- Merge choices. Parts I–III are single sources. Manuscripts 03, 04 and 06
  were placed here, not as reports of their own, because they answer named
  questions of this report (Q2, Q5; 29.2; Q9, 29.4, 29.5). Part IV merges 06
  (base) and 04, which prove the same core by the same construction; the
  choices — base 06, both printed in their own numbering, shared statements
  kept in both places with dated cross-notes, two of source 04's proofs
  replaced by pointers to source 06's identical arguments, its other shared
  proofs kept as second routes — are described in Section 45.6 and under
  "How the two sources are merged" above. Placing manuscript 02 of batch 90 as
  Part II was the only earlier choice.
