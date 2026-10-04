# Countable Information, Uncountably Many Boxes

**Sharp measurable prediction bounds, exact decision-tree enumeration, and an
all-orders asymptotic expansion (Part I); no universal sublinear bound for
measurable hat guessing (Part II)**

A research report in two Parts, built from two manuscripts. Part I (3 October
2026) is a manuscript on Elliot Glazer's *A choiceless box game paradox*
(arXiv:2211.10474). Part II (added 4 October 2026) is a manuscript on the
surplus of correct guesses in Nathaniel Eldredge's infinite binary hat game
(arXiv:2508.02828); it names Part I as its most direct source and settles
Part I's Research question Q9 for one family of parameters. Both author lines
read "Prepared for Vladimir Reshetnikov" (Part II: "Research report prepared
for …") and carry no AI wording; like the other deliveries of the intake,
both are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 87, manuscript 02 | `glazer_box_games_research.zip` (364,051 bytes; inner directory `glazer_box_games/`, main file `article.tex`, 999 lines, 24-page US Letter PDF), arrival commit `fa0a0576e` | `6fef5383b` (`6fef5383b126be343cccc9baf47081ef37ab5afe`, the article's `\commit` macro, quoted in Section 1 and in every repository URL of its bibliography) | `d151b39ca` | Part I: abstract, Sections 1–16, Appendices A–B |
| 02 | batch 90, manuscript 02 | `hat_guessing_research.zip` (550,545 bytes; inner directory `hat_guessing_research/`, main file `hat_guessing_growth.tex`, 1,587 lines, 22-page A4 PDF), arrival commit `a162e4386` | `7c0f2d9f9` (`7c0f2d9f92c3d51ec85703bed1022924a4b7359b`, quoted in Section 17.2 and bibliography entry 12) | `12076b2e8` | Part II: Sections 17–29, Appendices C–E |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. The finite computations of both Parts
were executed (by the packages and again at intake); the infinite theorems
rest on the written proofs only. **Historical priority is not established**
for either Part; Part II explicitly disclaims priority for its coding
mechanism (Ebert–Merkle–Vollmer 2003) and for the slow-density phenomenon.

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
- Questions Q2–Q12 are directions, not all recognized open problems. Q9 is
  now settled for one family by Part II (below) and otherwise open. No
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
three-box benchmark `(3,2,3)`, `t = 2` (also 3/4) is not in it. All other
parameters, and the location of the first legal/blind gap, stay open. A dated
note after Part I's questions (Section 15) records this; Part II's Research
question 29.4 continues Q9 for fixed targets.

## Relation to the repository

**Formal status.** No statement of either Part is formalized in Lean or Rocq.
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
exists.

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

**Neighbouring reports.** None shares a theorem or a question with either
Part. Before batch 90 nothing in ProveIt treated box, hat, guessing or
prediction games (search of the tracked tree at the batch-87 placement,
including `2211.10474` and A005271); Part II is now the repository's hat-game
material, and the batch-90 placement found no other.

- `../games-on-ordinals/` holds different games: in
  `open-query-membership-games` a Seeker asks open-set queries about a hidden
  point (adaptive query strategies and finite-budget certificates, but no
  guess at an unread coordinate); `point-separating-game-values` and
  `ordinal-chomp-transition-at-two` are point-separating games and ordinal
  Chomp.
- `../non-baire-translation-invariant-ideal/` is the nearest in spirit to
  Part I: a ZFC construction, from a free ultrafilter, of an ideal without the
  Baire property, the kind of irregular object Research question Q2 asks
  about for the Baire-property version of Theorem 3.1.
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
qualified by a dated note on Q9. No other sentence of Part I became false.

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

## Labels

Every label carries the prefix `mbg:`; Part II's carry `mbg:hat:`. Part I:
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

No statement, proof or non-claim of either manuscript was changed.

## Files

```text
README.md                                    this guide (replaces Part I's delivered README.md, staged under this name)
article.tex                                  the report: Part I (delivered article.tex) and Part II (hat_guessing_growth.tex), labels prefixed, [write] notes
article.pdf                                  compiled report, 53 pages (unnumbered title page, then pages 1-52)
02-hat-surplus-source_audit.txt              Part II: delivered source and claim audit (source_audit.txt)
code/verify_certificates.py                  Part I: exact finite enumerations and certificate checks (standard library)
code/formal_series.py                        Part I: exact rational formal-series coefficients through a chosen degree
code/Makefile                                Part I: delivered targets pdf, verify, clean (delivery layout; see below)
code/02-hat-surplus-verify_hat_strategy.py   Part II: exhaustive finite verifier (standard library)
code/02-hat-surplus-make_figures.py          Part II: regenerates Figure 1 (Matplotlib, NumPy)
code/02-hat-surplus-README.txt               Part II: delivered verifier README (code/README.txt)
code/02-hat-surplus-Makefile                 Part II: delivered targets pdf, verify, figures (delivery layout)
code/02-hat-surplus-LICENSE.txt              Part II: the code's own permissive licence (code/LICENSE.txt)
data/certificates.json                       Part I: the four-box non-executable blind rule and the three-box team with P(score >= 2) = 3/4
data/verification_report.json                Part I: recorded run of verify_certificates.py
data/formal_series_report.json               Part I: recorded run of formal_series.py --degree 10
data/02-hat-surplus-verification.json        Part II: recorded verifier run (nine cases)
data/02-hat-surplus-examples.json            Part II: one good and one bad block assignment
data/02-hat-surplus-example_prefix.csv       Part II: prefix path of the good example (CRLF, as delivered)
figures/02-hat-surplus-block_prefix.pdf      Part II: Figure 1, included by article.tex
figures/02-hat-surplus-block_prefix.png      Part II: raster copy of Figure 1 (not used by the article)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Part I: placement moved the programs and
`Makefile` to `code/` and the three JSON files to `data/`. Part II: placement
(`12076b2e8`) added the prefix `02-hat-surplus-` and kept the delivered
`code/`, `data/` and `figures/` layout; the audit moved to the report root.
`data/02-hat-surplus-example_prefix.csv` is delivered with CRLF line ends and
kept so by a `-text` line in `SetTheory/Cardinals/.gitattributes`.

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

## Build the PDF

pdfLaTeX with newtxtext/newtxmath, amsthm, geometry, microtype, mathtools,
booktabs, longtable, array, enumitem, xcolor, fancyhdr, titlesec, tcolorbox,
xurl, graphicx, listings and hyperref; the bibliography is inline. The
article includes `figures/02-hat-surplus-block_prefix.pdf`, so copy it too.
Build in a scratch copy:

```sh
B=$(mktemp -d); mkdir -p "$B/figures"
cp article.tex "$B/"; cp figures/02-hat-surplus-block_prefix.pdf "$B/figures/"
cd "$B"; latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 53 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The batch-87
text, built the same way, gives 26 pages with the same clean log; its
delivered source gave 24 pages and one duplicate-destination warning
(`page.1`), removed as described under Labels.

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
- Each Part is a single source: the report made no merge choices beyond
  placing manuscript 02 of batch 90 as a Part of this report (it names
  Part I as its most direct source and answers its Q9 for a family) rather
  than as a separate report.
