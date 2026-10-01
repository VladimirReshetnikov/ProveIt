# Term counts in the derivatives of power towers

**One framework and three sequences: OEIS A293239 (`x^x`), A290268 (`x^(x^2)`), A281434 (`x^(x^x)`), with depth certificates for A290268 at logarithmic deficits 3 and 4, a second route to deficit 3, Lehmer–Comtet nonvanishing on prime-multiple offsets for A293239, and deficits 5 and 6 with explicit count bounds for A290268**

**What this report is.** One article covering three OEIS sequences that ask the
same question about three different functions:

| Sequence | Function | The question |
|---|---|---|
| [A293239](https://oeis.org/A293239) | `x^x` | how many distinct monomials are in the fully collected `n`-th derivative? |
| [A290268](https://oeis.org/A290268) | `x^(x^2)` | the same |
| [A281434](https://oeis.org/A281434) | `x^(x^x)` | the same |

The three were written as separate reports and are merged here because they
share a setup, not because they share a result. **They reach three different
answers by three different recurrences**, and the article keeps all three
intact. What is proved once instead of three times is the common machinery:
the canonical differential-polynomial form, the uniqueness of that form, the
transition recurrence it obeys, and the reduction of "count the terms" to
"count the nonvanishing coefficients". That is Part 1 (Section 1). Parts 2, 3
and 4 are the three investigations; Section 5 compares them. A fourth
manuscript, on A290268 only, was written into the end of Part 3 on
29 September 2026 as Sections 3.14–3.26, and a fifth, also on A290268 only,
after it on 30 September 2026 as Sections 3.27–3.34. Three more, on the
Lehmer–Comtet triangle behind A293239, were written into the end of Part 2 on
1 October 2026 as Sections 2.11–2.15, and two more on A290268 into the end of
Part 3 on the same day as Sections 3.35–3.41.

**Status.** AI-assisted research notes. Unrefereed. Nothing in this report is
formalized; see "Relation to the Lean development" below for what the nearby
Lean development does and does not prove.

## Sources

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Cardinals-era delivery | `A293239_research_report.zip` (16-page article) | not recorded | merged in `630e041e5` (Cardinals history, brought in by `dc54c3cb3`) | Part 2 (Section 2) |
| 01 | Cardinals-era delivery | `A290268_partial_results.zip` (15-page article) | not recorded | as above | Part 3, Sections 3.1–3.13 |
| 01 | Cardinals-era delivery | `A281434_exact_algorithm_and_cubic_growth.zip` (17-page article) | not recorded | as above | Part 4 (Section 4) |
| 02 | batch 42, manuscript 06 | `ProveIt_A290268_Finite_Certificates.zip` (*From Infinite Nonvanishing to Finite Certificates: Bulk positivity, fixed-depth finiteness, and a four-depth solution for OEIS A290268*, 22-page PDF, dated 29 September 2026) | `afb2d1227` | `3609d0473` | Part 3, Sections 3.14–3.26 |
| 03 | batch 70, manuscript 03 | `ProveIt_A290268_Depth3_Article.zip` (*Depth Three Is Complete for OEIS A290268: A beta–sine transform, centered moment polynomials, and exact nonvanishing*, 17-page PDF, dated 30 September 2026) | `a02ab3567` | `51c6943bf` | Part 3, Sections 3.27–3.34 |
| 04 | batch 72A, manuscript 09 | `ProveIt_Lehmer_Comtet_Stirling_Residues_and_Candidate_Lists.zip` (*Stirling Residues and Finite Candidate Lists: Arithmetic restrictions on Lehmer–Comtet zeros*, 6-page PDF, dated 1 October 2026) | `ca81647a9` | `d292c6765` | Part 2, Section 2.13 |
| 05 | batch 72A, manuscript 12 | `ProveIt_Lehmer_Comtet_Prime_Multiple_Nonvanishing.zip` (*Complete Nonvanishing on Prime-Multiple Offsets: Lehmer–Comtet coefficients and derivatives of x^x*, 6-page PDF, dated 1 October 2026) | `ca81647a9` | `d292c6765` | Part 2, Section 2.12 |
| 06 | batch 72A, manuscript 17 | `ProveIt_Lehmer_Comtet_Uniform_Padic_Nonvanishing.zip` (*Uniform p-adic Nonvanishing: Two valuation families for Lehmer–Comtet coefficients*, 4-page PDF, dated 1 October 2026) | `ca81647a9` | `d292c6765` | Part 2, Section 2.14 |
| 07 | batch 72A, manuscript 68 | `ProveIt_A290268_Count_Bounds.zip` (*Pointwise and Summatory Bounds for OEIS A290268*, 6-page PDF, dated 1 October 2026) | `ca81647a9` | `d292c6765` | Part 3, Section 3.40 |
| 08 | batch 72A, manuscript 70 | `ProveIt_A290268_Depths_Five_Six.zip` (*Depths Five and Six Nonvanishing for OEIS A290268*, 9-page PDF, dated 1 October 2026) | `ca81647a9` | `d292c6765` | Part 3, Sections 3.35–3.39 |

The first three rows are the original merge; `MERGE_EDITS.md` records every
edit made to them, and all fifty of their theorems, lemmas, propositions,
corollaries, definitions, conjectures and remarks are present with their
statements unchanged. Part 1 and Section 5 were written for the merge.

Source 02 (manuscript 06) is printed in full: every theorem, proposition,
lemma, corollary, definition, remark and research question, with its proofs
and its non-claims. It was written against the repository note
`Oeis/A290268/README.md` and the conditional Lean reduction, and **never read
this report**. Its bulk positivity, symmetry holes, depths one and two, upper
bound, depth bridge and linear independence therefore re-derive Part 3's
Theorem 3.7, Theorem 3.11, Theorems 3.16–3.17, Theorem 3.14, Proposition 3.4
and Lemma 3.2; they are printed as marked second routes, with Part 3
credited. Its manuscript, README, PDF and `SHA256SUMS.txt` (10/10 verified at
placement) are not shipped; the archive survives in the history of
`8315d24e3`. Where the write had to choose: the addition is placed as
subsections at the end of Part 3, not as a new part, so that no existing
section, theorem or equation number moved (checked against the `.aux` of a
build of the previous text: 0 of 217 labels changed number); the manuscript's
letters are kept, with a dictionary; three editorial remarks (3.31, 3.42,
3.46) are marked as additions of the intake.

Source 03 (batch 70, manuscript 03) is also printed in full: every theorem,
proposition, lemma, corollary, definition, remark, table and research
question, with its proofs, its proof-boundary and warning boxes and its audit
table. **Its main theorem — at depth `d = 3` the only zeros of
`gamma(k,3,M)` are `M = k+13`, `k` odd — is the `d = 3` case of Theorem 3.23,
which Source 02 had already put in this report; it is printed as a second
proof (Theorem 3.59).** The manuscript says depth three was "the stated open
core" at its pin `a02ab3567` and that its theorem is new there. That is
mistaken: the pin descends from `0e6632abf`, the commit that wrote Source 02
into this report, and the note it cites (`Oeis/A290268/README.md`) already
says so in its dated correction; the manuscript read only that note's older
line "Open core: D >= 3". The sentences are kept verbatim (abstract, summary
box, novelty paragraph, conclusion, audit table) with editorial corrections,
and its question "Depth four" is marked as answered by Theorem 3.23. Its
reduction, parameter derivative, beta–sine transform, centred recurrence,
vertical-root corollary and bulk lemma re-derive Proposition 3.24,
equation (3.58), Proposition 3.30, equation (3.61), Corollary 3.27 and
Theorem 3.21 (all Source 02's), and are marked as second routes. New relative to this report:
the harmonic factorization at the root `x = 7`, the sign law of the harmonic
quantity `E_q` (Lemma 3.54: negative exactly for `1 <= q <= 37`), which
*proves* the `q = 37/38` sign change that Section 3.20 recorded only as an
observation of the certificate data; the propagation recurrence in `k` and
its finite certificate (Proposition 3.55); the eventual signs of Corollary
3.57; the sign phase diagram of the log-free diagonal; and the interlacing
clause of Corollary 3.53. Editorial Remark 3.61 compares the two proofs:
their finite anchors partly coincide (`H_{3,14,6} = 720^2 F_14(6)`,
`H_{3,0,38} = 720*38!*E_38`), and the manuscript's sign table reproduces
every `d = 3` row of `data/02-depth-certificates-sign_thresholds.csv`. Its
manuscript, README, PDF and `SHA256SUMS.txt` (5/5 verified at placement) are
not shipped; the archive survives in the history of `1b3960d8a`. Where the
write had to choose: the addition follows Source 02 at the end of Part 3, so
that no existing number moved (checked against the `.aux` of a build of the
previous text: 0 of 302 numbered labels changed); the manuscript's letters
are renamed where they collide (Table 5, below); the dictionary (3.89),
Remark 3.61 and the editorial notes are additions of the intake.

Sources 04–06 (batch 72A, manuscripts 09, 12 and 17) are printed in full at
the end of Part 2, in the order 12, 09, 17 (09 builds on 12): every theorem,
lemma, corollary and proof, and every non-claim. All three pin `ca81647a9`,
this report's text at the time, and cite it as "Part I" (they mean Part 2).
They attack Conjecture 2.9 (the complete zero list of the Lehmer–Comtet
triangle) one offset at a time and **leave it open**. New relative to this
report: Theorem 2.19 (every offset `mu(p-1)`, `p > mu` prime, is zero-free
under two explicit conditions, which hold for `p >= max(4 mu, 1 + 3^(4 mu - 7))`)
and its Corollaries 2.20–2.22 (offsets `2(p-1)` and `4(p-1)` for every prime,
`3(p-1)` for odd primes); the universal positivity cone `T_d(Y) > 0` for
`Y >= 4d` (Corollary 2.25); the Stirling residue, root displacements and
candidate list of 09 (Theorems 2.30, 2.32, 2.33), offset `5(p-1)` for odd
primes (Corollary 2.35), offset `(p-1)^2` reduced to one candidate (Corollary
2.36), offset `p^2-1` reduced to `1 <= Y <= p-1` (Theorem 2.38) together with
12's explanation why a fixed `p`-power sieve cannot do that alone (Theorem
2.28); and 17's exact valuations on divisibility progressions and on the odd
offsets `(p-1)mu + 1` (Theorems 2.39, 2.40). Re-derivations of this report's
results are printed once and credited: 17's Theorem 2.39 at `mu = 1` is the
valuation of Theorem 2.12 (a second route, by Davis's multinomial count); 12
re-uses (2.28) and restates the offset-8 certificate of Theorem 2.14 (its
`F(Y)` is `R_8(Y+8)`, same scalar `1/1393459200`, checked at the intake); its
Lemma 2.27 at `j = 1, 2` is Proposition 2.15's columns 1–2; (2.50) is
Proposition 2.4 with (2.22). Three lemmas of 09 that re-prove 12's (the cone,
the ordinary congruence, the prime-square congruence) are recorded as Remarks
2.29, 2.31, 2.37, without reprinting the same proofs. Where the write had to
choose: the addition follows Part 2's last subsection, so that no existing
number moved (checked against the `.aux` of a build of the previous text: 0 of
359 numbered labels changed); the notation table is numbered 2.A and the
article-wide table counter is restored after it and after the file table, so
that no later table number moves; the manuscripts' offset `r` and multiplier
`m` are renamed `d` and `mu` (Table 2.A, below); Remarks 2.26, 2.34 and 2.42,
the notation subsection and the editorial notes are additions of the intake.
Remark 2.34 records an unstated second route: 09's candidate list re-proves
Corollary 2.21 for `p >= 5` and Corollary 2.22 for `p >= 7`, `p != 11`. Not
shipped: the three manuscripts, READMEs and PDFs, 09's embedded byte-identical
copy of archive 12 and its PDF, and three copies of a generic `build_local.sh`;
the archives survive in the history of `1512ef835`.

Sources 07 and 08 (batch 72A, manuscripts 68 and 70) are printed in full at
the end of Part 3, 70 first (68 uses its Theorem 7.2), including 68's input
file `sharpness.tex`. Both pin `ca81647a9`. **Source 08 answers Question 1 of
Section 3.24**: Theorem 3.71 classifies depths 5 and 6 (only the reflection
holes `M = k+4d+1`, `k+d` even), by exact moment seeds (Lemmas 3.75, 3.79)
for the convexity criteria (3.88) and finite rectangles of 343,151 and
4,785,360 cells, so **the open region is now deficit `m >= 7`**. It answers
Question 2 non-optimally (Theorem 3.81: cutoffs `ceil((2d+1)e^d)` and twice
that, against the tower-type constants (3.74)), and Question 3 in part
(Proposition 3.80, the sharp largest-root affine minorant). Source 07 gives
the first explicit bound with an `N log N` gain (Theorem 3.83:
`a(N) >= 3N^2/8 + (N/2)log N - (N/2)log log N - 5N/4` for `N >= e^10`), an
exact summatory bound with cubic constant `11/72` (Theorem 3.85), the average
`11/24` (Corollary 3.86), and the sharpness of `11/72` for integer-support
information alone (Proposition 3.87), which quantifies the last sentence of
Question 6. Re-derivations are printed once and credited: 70's Lemma 2.1 is
Theorems 3.21 and 3.29, its branch cut Proposition 3.30, its factorization
Proposition 3.26, its Lemma 4.1 Proposition 3.34 (with Lemmas 3.32–3.33),
its recurrences (3.80) and (3.81), its Lemma 3.1 the criterion (3.88); 68's
Proposition 3.82 at depth cap 4 is Corollary 3.45 and its row budget is
Theorem 3.44. **Neither manuscript cites Sections 3.27–3.34**, yet 70's
tail-moment formula (3.120) at `d = 3` is `pi^2/3 + 2 E_q`, the harmonic
quantity of Lemma 3.54, and reproduces the cutoff `q >= 38`; its parameter
integral is the beta–sine transform (3.94); Remark 3.76 records both. Where
the write had to choose: the addition follows the batch-70 addition, so that
no existing number moved (checked against the `.aux` of a build of the
previous text: 0 of 417 numbered labels changed, and 0 of the 359 of the
text before batch 72A); the notation table is numbered 3.A with the table
counter restored; 70's `C_d, K_d, Q_d` and 68's `K_d, Q_d` are printed
`hat C_d, hat K_d, hat Q_d`, because the same letters already name the
different constants (3.74) (Table 3.A); Lemma 2.1 and Lemma 4.1 of 70 are
printed with their proofs cited, not repeated; Remarks 3.76 and 3.84, the
notation table and the editorial notes are additions of the intake. Remark
3.84 records an intake check: the bound of Theorem 3.83 already follows from
Corollary 3.45 for `3 <= N <= 92653`, from Corollary 3.78 for
`N <= 814895`, and from Proposition 3.82 with the largest admissible depth
cap for every `3 <= N <= 3*10^6`, so the threshold `e^10` is conservative.
Not shipped: the two manuscripts, READMEs and PDFs, 68's `sharpness.tex`,
and two copies of `build_local.sh`.

## Status of each headline question — read this first

**None of the three headline questions is fully settled here, and this report
does not pretend otherwise.** Two of the three OEIS entries print a conjectured
closed form, and neither is proved. The third prints no closed form; there the
growth *order* is settled and the constant is not — and the obstruction is a
different kind of statement, because further zeros provably exist and the open
question is only how many.

- **A293239 (`x^x`): the principal all-order closed formula is NOT proved.**
  Its precise missing nonvanishing statement is isolated. What *is* proved
  unconditionally: the term count reduces exactly to zeros of the first-kind
  Lehmer–Comtet triangle [A008296](https://oeis.org/A008296), giving
  `a(n) = 1 + n(n+1)/2 - Z(n)`; and `n + 1 + floor(n^2/4) <= a(n) <= q(n)`, so
  `a(n) = Theta(n^2)`. Separately, **the recurrence printed in the OEIS entry
  with the range `n > 6` is disproved at `n = 8`** (the recurrence gives 36,
  the true value is 35). For the proposed sequence `q` the recurrence holds for
  every `n >= 14` and fails at `n = 13`; asserting the corrected range for the
  actual derivative count remains conditional on the principal conjecture.
  The missing statement — no zeros of the triangle beyond `b(8,5)` and the
  symmetry family — was proved in Part 2 on the offsets `d <= 16`, on every
  offset `d = p-1` (`p` prime) and on the columns 1–3. Sections 2.11–2.15
  (1 October 2026) add infinitely many settled offsets: every `mu(p-1)` with
  `p > mu` under explicit conditions, in full for `2(p-1)` and `4(p-1)` (every
  prime) and `3(p-1)`, `5(p-1)` (odd primes); one candidate left on `(p-1)^2`,
  only columns `1..p-1` on `p^2-1` (`p >= 5`); exact `p`-adic valuations on
  divisibility progressions; and the cone `T_d(Y) > 0` for `Y >= 4d`. The
  complete classification, and with it the closed formula, stays open.

- **A290268 (`x^(x^2)`): the OEIS conjecture is NOT proved.** What is proved:
  the conjectured expression `U(n)` is an *upper* bound; every predicted
  cancellation is explained; positivity holds on a large coefficient region;
  there are no further zeros on the first **four** logarithmic-deficit
  diagonals (deficits 1 and 2 in Part 3 as first written; deficits 3 and 4 in
  Sections 3.14–3.26, by an effective infinite-to-finite reduction plus exact
  finite certificates; deficit 3 again in Sections 3.27–3.34, by a second
  route — a harmonic sign law and positivity propagation — with its own exact
  finite certificate); and `Lambda(n) <= a(n) <= U(n)` with
  `Lambda(n) = (3n^2+10n+8)/8` for even `n` and `(3n^2+12n+1)/8` for odd `n`,
  so `a(n) = Theta(n^2)`. The addition improves the lower bound (Corollary
  3.45, Remark 3.46) to `(3n^2+26n-72)/8` for even `n >= 8` and
  `(3n^2+28n-111)/8` for odd `n >= 17` — a gain of `2n-10`, resp. `2n-14`, in
  the linear term only; the leading constant `3/8` is unchanged, and the
  proposed leading constant `1/2` is not established. The certified finite
  range `a(n) = U(n)` for `n <= 3000` (Proposition 3.18) is unchanged. The
  open region was then logarithmic deficit `m = k - j >= 5`, `n >= 2k + 2`.
  **Since 1 October 2026 (Sections 3.35–3.41) deficits 5 and 6 are also
  classified (Theorem 3.71), so the open region is now `m >= 7`,
  `n >= 2k + 2`**, away from the reflection zeros. At every fixed `m >= 3` it
  is reduced to a finite rectangle of `2*ceil((2m+1)e^m)^2` cells (Theorem
  3.81; the earlier bounds of Theorem 3.22 were tower-sized), still about
  `5.4*10^8` cells at `m = 7`. The explicit lower bound is now
  `a(n) >= 3n^2/8 + (n/2)log n - (n/2)log log n - 5n/4` for `n >= e^10`
  (Theorem 3.83), with the exact summatory bound
  `sum_{n<=X} a(n) >= 11X^3/72 + 5X^2/6 - O(X)` (Theorem 3.85); the leading
  constant of every explicit lower bound is still `3/8`.

- **A281434 (`x^(x^x)`): the growth order is settled; the constant is not.**
  For `n >= 1`, with `eps = 1` for odd `n` and `0` otherwise,

      (7n^3 + 39n^2 + 26n + 3*eps*(n-1))/24  <=  a(n)  <=  (2n^3 + 3n^2 + 4n)/3

  hence `a(n) = Theta(n^3)`. The sharper equivalent `a(n) ~ (2/3)n^3` is **not**
  proved; it would need the deficit from the upper polynomial to be `o(n^3)`.

Every finite computation in this report certifies a range or a finite list of
cells. None of them is by itself an all-`n` proof, and each verifier says so in
its own output. The depth-3 and depth-4 certificates of Sections 3.14–3.26
decide every `n` only because a proved reduction (Proposition 3.41) shows the
finite rectangles to be exhaustive; the rectangles themselves reach only
derivative order `n <= 359`, inside the range `n <= 3000` that Part 3's
modular certificate already covers. What that certificate does not supply is
the six seed *signs* the reduction needs. The same holds for the second route
of Sections 3.27–3.34: its exact rational check (Proposition 3.55; the
36 values `q` in `{1..5} ∪ {7..37}` with `0 <= k <= 14`, plus the centre
`q = 6`) decides every `n` only because the proved recurrence (3.107) and the
harmonic sign law (Lemma 3.54) make it exhaustive; its larger boxes are
diagnostics. The depth-5 and depth-6 rectangles of Sections 3.35–3.39 decide
every `n` only because the exact moment seeds (Lemmas 3.75 and 3.79) and the
proved comparisons make them exhaustive (Proposition 3.77); the depth-5
rectangle reaches `n <= 1665`, inside the certified range, while the depth-6
rectangle reaches `n = 6198` and is the first certificate of cells with
`3000 < n <= 6198`.

## What is not claimed

- No closed formula for any of the three sequences, and no leading constant
  for A290268 or A281434.
- For A290268: nothing at deficits `m >= 7` beyond the finite range
  `n <= 3000` and the per-depth finiteness theorems (until 1 October 2026
  this read `m >= 5`; deficits 5 and 6 are Theorem 3.71); the batch-42
  manuscript's general bounds `K_d`, `Q_d` are "deliberately crude" and not
  claimed practical, and manuscript 70's cutoffs `hat Q_d`, `hat K_d` are
  "not a bit-complexity estimate or a claim of optimality".
- For A290268, Sections 3.35–3.41: manuscript 70 does not claim "that the
  coefficient distributions attain the worst case" of its sharp threshold;
  "the full OEIS conjecture, the finite nonvanishing obligations at depths
  `d >= 7`, and formal verification remain separate tasks". Manuscript 68's
  average constant `11/24` "is an average statement, not a pointwise bound";
  neither result proves `a(N) ~ N^2/2`; its sharpness pattern "is not
  asserted to arise from any function". Its sentence "Depths one and two are
  already classified" understates this report (depths 1–4 are), and 70's
  "the leading lower-bound constant remains 3/8" is true only of explicit
  bounds; both are kept with editorial notes. No exhaustive priority, formal
  verification or refereeing is claimed; their READMEs' "independent"
  checks are not confirmed here.
- The manuscript's zero-count bound (at most `d` real zeros per row of the
  Mellin interpolant) is not an integer nonvanishing statement.
- No priority: manuscript 06's literature and repository checks are "not a
  comprehensive historical-priority search"; Meixner–Pollaczek theory and the
  reflection, covariance and Chebyshev-system arguments are classical.
- No novelty for the depth-3 theorem of Sections 3.27–3.34: it is Theorem
  3.23 at `d = 3`, and only its proof is new. Its manuscript's claims that
  depth 3 was open at its pin and that "depths `D >= 4` remain open" are
  stale and corrected in the text (the open depths are `d >= 5`). Its other
  non-claims are kept: "not a claim that the full A290268 conjecture has been
  proved"; the Python certificate "is not a kernel-checked theorem"; no
  "exhaustive priority over inaccessible or unpublished work"; no peer review.
- For A293239 (Sections 2.11–2.15): not the complete zero classification of
  the Lehmer–Comtet triangle, hence not the closed formula; the candidates
  left on the offsets `(p-1)^2` and `p^2-1` are "necessary possibilities, not
  a claimed zero list", and no assertion is made that the single `(p-1)^2`
  candidate vanishes; 12 asserts no real-rootedness of the polynomials `T_d`;
  17 does not assert its valuation equality when a competing term has more
  than `p^e` factors, and its restricted formula fails without its hypotheses
  (`T_9(9) = 2021/268800`), which is not a new zero. All three disclaim
  exhaustive literature priority, formal verification and refereeing; the
  READMEs of 12 and 17 mention an "independent review" that this report
  cannot confirm.
- No Lean or Rocq verification, no referee, no independent human review.

## A warning about notation

The parts keep the notation of their sources, which is *not* consistent
between them, because silently rewriting 2,600 lines of dense manipulation is a
worse risk than declaring the clash. Three collisions matter more than the rest:

- **`j` changes role.** In Parts 2 and 3 it is the exponent of `log x`. In
  Part 4 it is the exponent of `x^-1`, and `l` is the logarithm exponent. Every
  envelope and every bound in Part 4 is indexed the second way.
- **`z` has three meanings.** It is `x^2` in Part 3 and `log x` in Part 4 — a
  direct contradiction — and in Part 2 it is neither, but the formal variable
  in which the Lehmer–Comtet numbers are defined.
- **Sections 3.14–3.26 swap `j` and `k`.** They use the depth coordinates of
  manuscript 06 and of the Lean development: **`k` is the exponent of
  `log x`** (Part 3's `j`), `j` is the exponent of `x` in `x^(x^2+j)`, `d` is
  the logarithmic deficit (Part 3's `m`, *not* Part 3's `d = n-2k-1`, which is
  the addition's `q`). Table 3 of the article gives the full dictionary with
  the false readings, and lists the symbols renamed from the manuscript
  (`P_d -> Pi_d`, `Q_k^(r) -> calQ_k^(r)`, `A_{M,k} -> calA_{M,k}`,
  `B_d(r) -> calB_d(r)`, `B(N) -> beta(N)`, `L -> tau`, `h_d(N) -> chi_d(N)`,
  `m -> nu_d` and `rho`, `F_{d,k} -> calF_{d,k}`, series variable `z -> xi`;
  no normalization changed).
- **Sections 3.27–3.34 keep those depth coordinates** and rename manuscript
  03's colliding letters (Table 5 of the article, with false readings): its
  `n -> N` (derivative order) and its `N -> r` (`= M - k`; its `N` is *not*
  the derivative order); `R_{N,k} -> calQ_k^(r)` (the same polynomial as
  Source 02's) and `Q_{N,k}(x) -> calQ_k^(r)(x - (r+1)/2)`; its kernel
  `K_D -> R_d` (Source 02's kernel; *not* the constant `K_d`); `L -> tau`;
  `P_M -> calP_M`, `H_{M,k} -> calH_{M,k}` (*not* the integer `H_{d,k,q}`),
  `S_N -> Omega_r`, `S_{N,k} -> calT_{r,k}`, `I_k -> calI_k`; harmonic
  numbers `H_q -> upright H_q`; `E_q, F_k(q), U_{q,k}, V_k` in sans-serif;
  `z -> lambda_q`, `a -> alpha_q` or `2d+1` or `theta`, `B -> |E_q|`. The
  two tail values are related by `H_{3,k,q} = 720 (-1)^q q! F_k(q)` (3.89).
  No normalization changed.
- **Sections 2.11–2.15 rename the offset and the multiplier.** Their sources
  write the offset polynomial `T_r(Y)` with `r` the **offset** — Part 2's
  `r` is the *column* of `b(m,r)` — and call a multiplier `m` — Part 2's
  *row*. They are printed with Part 2's offset `d` (`T_d(Y)`, `d = m - r`) and
  the multiplier `mu`; Table 2.A of the article gives the full dictionary with
  the false readings (also `M -> m`, harmonic numbers in sans-serif, the
  falling factorial `P_M -> F_m`, the log-derivative `Phi_P(b) -> Psi_P(xi)`,
  and local letters such as `U -> omega`, `D -> calV`, `L -> Lambda`,
  `q -> nu`, `E_j -> bold e_j`). 09's unsigned Stirling numbers `c(mu,j)` are
  `(-1)^(mu-j) s(mu,j)` in terms of Part 2's signed `s(m,l)`. No normalization
  changed.
- **Sections 3.35–3.41 keep the depth coordinates** but print manuscript 70's
  `C_d`, `K_d`, `Q_d` and manuscript 68's `K_d`, `Q_d` as **`hat C_d`,
  `hat K_d`, `hat Q_d`**: they are *not* the constants `C_d`, `K_d`, `Q_d` of
  (3.74). Table 3.A of the article lists the other renamings (70's `r_d`,
  `beta_l` -> `varrho_d`, `omega_l`; `Q_k^(r)`, `A_{M,k}`, `B(r)`, `E_{k,q}` ->
  the batch-42 `calQ`, `calA`, `calB_d`, `calE_{d,k,q}`; harmonic numbers ->
  upright `H`; `L_4(N)` -> `Lambda_4(N)`; `U` -> `Xi`; 68's `D` -> `bar d`,
  `L` -> `frak L`, `F` -> `calN`, `B(X)` -> `bar beta(X)`, `S(X)` -> `calS(X)`,
  `A(X)` -> `Sigma_a(X)`, `h(d,k)` -> `iota(d,k)`). The practical cutoffs keep
  the letters `(R, Q)` of Proposition 3.41. No normalization changed.

§1.5 of the article gives the three canonical monomials side by side, and is
explicit that many other letters (`u`, `v`, `t`, `q`, `U`, `Z`, `E`, `Δ`) are
reused across parts with unrelated meanings. `a(n)` denotes a different
sequence in each part.

## Labels

Labels carry a per-part prefix: `fw:` (Part 1), `xx:` (Part 2), `xxb:`
(Part 3), `xxc:` (Part 4), `syn:` (Section 5). The batch-42 addition uses the
sub-prefix **`xxb:dc:`** (85 labels) and the batch-70 addition the sub-prefix
**`xxb:d3:`** (57 labels: the manuscript's 47, prefixed, and 10 of the
intake's). The batch-72A Part 2 addition (Sections 2.11–2.15) uses the
sub-prefixes **`xx:pm:`** (21 labels, manuscript 12), **`xx:st:`** (15,
manuscript 09), **`xx:pn:`** (14, manuscript 17) and **`xx:lc:`** (8, the
intake's): 58 in all. They are the manuscripts' own labels with the prefix
(all 19 of 12's, 14 of 09's, 13 of 17's), four subsection labels and the
intake's eight; the four manuscript labels not carried (`st:H`, `st:b`,
`pn:H`, `pn:b`) label 09's and 17's repetitions of 12's definitions, which
are printed once. The batch-72A Part 3 addition (Sections 3.35–3.41) uses
**`xxb:d56:`** (30 labels: manuscript 70's 20, prefixed, and 10 of the
intake's) and **`xxb:cb:`** (18: manuscript 68's 15, prefixed, and 3 of the
intake's, one of them on the unnumbered proposition of `sharpness.tex`). The
article has 467 `\label`s (219 before the batch-42 addition, 304 before the
batch-70 one, 361 before batch 72A, 419 after its Part 2 addition); none was
renamed or removed. No label here has a Lean mapping.

## Files

```
README.md                                         this guide
article.tex                                       the article (pdfLaTeX, internal bibliography)
article.pdf                                       the compiled article, 141 pages (A4)
MERGE_EDITS.md                                    every edit made to the three original texts in the merge
A293239_oeis_notes.txt                            statement of the x^x recurrence-range correction
A290268_result_status.json                        Part 3's machine-readable status, as delivered (stale; see below)
02-depth-certificates-SOURCE_AUDIT.md             manuscript 06's source and proof-boundary audit, as delivered
CODE_LICENSE.txt                                  license for the code (shipped with the A281434 group)
Makefile, build.sh, build.ps1                     article build and the original verification targets
requirements-optional.txt                         optional NumPy for the A281434 modular path
code/verify.py, code/verify_diagonals.py          A293239 (Part 2) verifiers
code/verify_gmp.cpp                               A293239 compiled exact verifier
code/verify_exact.py, code/verify_modular.cpp     A290268 (Part 3) exact and modular verifiers
code/combine_certificates.py                      A290268 certificate combiner
code/a281434.py, code/test_a281434.py,
code/run_experiments.py                           A281434 (Part 4) algorithm, tests, experiments
code/02-depth-certificates-verify.py              manuscript 06: full exact verifier (writes nothing unless --write-data)
code/02-depth-certificates-minimal_verify.py      manuscript 06: standalone verifier printed in Section 3.25.2
code/02-depth-certificates-Makefile               manuscript 06's delivered Makefile (do not use; see below)
code/03-depth-three-verify_depth3.py              batch-70 manuscript 03: exact depth-3 verifier (writes depth3_certificate.txt beside itself)
code/04-stirling-residues-verify_stirling.py      batch-72A manuscript 09: Stirling residues, triangle congruences, root displacements
code/04-stirling-residues-verify_prime_square_lifts.py
                                                  09: roots modulo p^3 at offset p^2-1, p = 3, 5, 7, 11
code/04-stirling-residues-verify_square_candidates.py
                                                  09: exact values at the one (p-1)^2 candidate, seven primes
code/04-stirling-residues-replay_falling_products.py
                                                  09: independent integer falling-product replay (run with -O)
code/05-prime-multiple-verify.py                  batch-72A manuscript 12: exact checks of Section 2.12
code/05-prime-multiple-replay_convolution.py      12: independent convolution and finite-difference replay
code/06-padic-valuations-verify_padic.py          batch-72A manuscript 17: integer-triangle check of both valuation families
code/06-padic-valuations-check_rational_powers.py 17: direct rational power recurrence (prints its JSON, writes nothing)
code/06-padic-valuations-replay_padic_powers.py   17: integer-scaled convolution replay
code/07-count-bounds-verify_counts.py             batch-72A manuscript 68: exact count checks of Section 3.40 (SymPy; prints, writes nothing)
code/08-depths-five-six-verify_depth5.py          batch-72A manuscript 70: depth-5 rectangle and seeds, exact integers
code/08-depths-five-six-independent_pascal_depth5.py
                                                  70: depth-5 rectangle by the Pascal recurrence modulo 1009/1013/1019, and seeds
code/08-depths-five-six-independent_pascal_depth6.py
                                                  70: depth-6 rectangle by the Pascal recurrence modulo 1000003/1000033, and seeds
code/08-depths-five-six-verify_depth6_columns.cpp 70: depth-6 rectangle by the centered recurrence, same moduli (C++17; prints its JSON)
data/02-depth-certificates-finite_certificate.csv all 16,034 rectangle cells: sign, reduced sign, residues mod 1009, 1013 (CRLF)
data/02-depth-certificates-sign_thresholds.csv    observed sign transitions per tested row (CRLF)
data/02-depth-certificates-verification.json      executed-check summary and exact seed integers
data/03-depth-three-depth3_certificate.txt        batch-70 manuscript 03: recorded verifier output (anchors, sign table, digest)
data/04-stirling-residues-{stirling_checks,prime_square_lifts,square_candidates,replay_falling_products}.json
                                                  09: recorded outputs of the four programs above
data/05-prime-multiple-{checks,replay_convolution}.json
                                                  12: recorded outputs of its two programs
data/06-padic-valuations-{padic_checks,rational_power_checks,replay_padic_powers}.json
                                                  17: recorded outputs of its three programs
data/07-count-bounds-{verification.txt,requirements.txt}
                                                  68: recorded output (three PASS lines); its SymPy pin (sympy==1.14.0)
data/08-depths-five-six-{depth5_certificate,depth6_column_certificate,independent_pascal_depth5,independent_pascal_depth6}.json
                                                  70: recorded outputs of its four programs (depth5_certificate.json has a wall-clock field)
data/b281434.txt, data/b352697.txt, data/benchmarks.csv, data/counts.csv,
data/python_report.json, data/selected_holes.json, data/test_results.txt,
data/zeros.csv, data/environment.json             A281434 and A293239 outputs
data/diagonal_certificates.json, data/diagonal_report.txt,
data/gmp_report.txt                               A293239 diagonal and GMP outputs
data/exact_counts.csv, data/exact_run.log, data/exact_summary.json,
data/certified_counts.csv, data/certificate_run.log, data/certificate_summary.json,
data/modular_witnesses.csv, data/sample_coefficients.json,
data/watch_coordinates.csv                        A290268 exact and certificate outputs
data/p1000000007_{counts.csv,run.log,summary.txt,watches.csv,zeros.csv}
data/p1000000009_{counts.csv,run.log,summary.txt,watches.csv,zeros.csv}
                                                  A290268 modular runs, one set per modulus
```

That is all 89 files in the directory.

## Building

    sh build.sh            # three pdflatex passes
    make pdf               # the same, into build/, then copies article.pdf
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built with `latexmk` (pdfTeX, MiKTeX): 0 errors, 0
undefined references or citations, 0 multiply-defined labels, 0 duplicate
destinations, 0 LaTeX warnings; one overfull box (8.4 pt, in the Section 5
comparison table) and five hyperref "Token not allowed in a PDF string"
notices (superscripts in section titles), all present before the later
additions as well.

## Verifying

Run from the report root. Each script is independent of the others.

    python code/verify.py --max-n 1500              # A293239, exact
    python code/verify_diagonals.py                 # A293239, offsets 1..16
    python code/verify_exact.py --max-n 200 --formula-n 16   # A290268, exact
    python code/test_a281434.py                     # A281434, 10 regression groups
    python code/run_experiments.py                  # A281434, data + benchmarks

Optional compiled verifiers, both exact rather than probabilistic:

    g++ -O3 -std=c++17 code/verify_gmp.cpp -lgmp -o verify_gmp      # A293239
    g++ -O3 -std=c++17 code/verify_modular.cpp -o verify_modular    # A290268

`make verify` runs the A290268 exact and modular passes and the certificate
combiner. **Note that several of these rewrite files in `data/`**: `make verify`
tees its run logs there, and `code/verify.py` rewrites `data/python_report.json`.
The shipped `data/` is the output of a full run, so re-running is reproduction,
not corruption — but the files will change.

**Depth certificates (Sections 3.14–3.26).** Python 3.9 or later, standard
library only:

    py code/02-depth-certificates-minimal_verify.py   # prints PASS, writes nothing
    py code/02-depth-certificates-verify.py           # prints a JSON report with "status": "PASS", writes nothing

To regenerate the data, **work on a copy** of this directory:
`verify.py --write-data` writes the *unprefixed* files
`data/finite_certificate.csv`, `data/sign_thresholds.csv` and
`data/verification.json` next to the shipped prefixed ones. On the intake
copy both CSVs came out byte-identical to the shipped ones and the JSON
identical up to line endings (the suite writes CRLF on Windows). The
recomputed `H_{d,k,q}` of all 494 depth-3 cells and of 925 depth-4 cells were
also checked independently from the series definition in exact rationals,
with no mismatch. Do **not** use `code/02-depth-certificates-Makefile`: from
the report root its `verify` target runs `code/minimal_verify.py` (absent
under that name) and `code/verify.py` — the A293239 verifier of Part 2, which
rewrites `data/python_report.json` — and its `data` target does the same with
`--write-data`; its `all`/`clean` targets run `latexmk` on the merged
`article.tex`.

**Second route to depth 3 (Sections 3.27–3.34).** Python 3, standard library
only (`fractions.Fraction`). **Work on a copy** of this directory and do not
pass `-O` (its checks are `assert` statements):

    py code/03-depth-three-verify_depth3.py

It prints the certificate and writes it, under the unprefixed name
`depth3_certificate.txt`, into the directory that contains the script — on a
copy of the shipped layout that is `code/depth3_certificate.txt`, beside the
program, not the shipped `data/03-depth-three-depth3_certificate.txt`. It
writes LF line endings on every platform. On the intake copy it exited with
status 0 in about 12 s, and its output was byte-identical to the shipped
certificate. The intake also checked the dictionary
`H_{3,k,q} = 720 (-1)^q q! F_k(q)` against Source 02's integers for
`0 <= k <= 14`, `0 <= q < 60`, and that the manuscript's sign table
reproduces every `d = 3` row of `data/02-depth-certificates-sign_thresholds.csv`
(Remark 3.61); those checks used scratch scripts that are not shipped.

**Lehmer–Comtet additions (Sections 2.11–2.15).** Python 3, standard library
only (`fractions.Fraction`). Every program except one writes its JSON
**beside itself**, under its delivery name (`checks.json`,
`stirling_checks.json`, `prime_square_lifts.json`, `square_candidates.json`,
`padic_checks.json`), or, for the three replays, under its own shipped name
with `.json` (for example `code/05-prime-multiple-replay_convolution.json`).
None of them touches `data/`, but **work on a copy** of this directory so that
`code/` stays clean:

    py code/05-prime-multiple-verify.py
    py code/05-prime-multiple-replay_convolution.py
    py code/04-stirling-residues-verify_stirling.py
    py code/04-stirling-residues-verify_prime_square_lifts.py
    py code/04-stirling-residues-verify_square_candidates.py
    py -O code/04-stirling-residues-replay_falling_products.py
    py code/06-padic-valuations-verify_padic.py
    py code/06-padic-valuations-check_rational_powers.py        # prints its JSON, writes nothing
    py code/06-padic-valuations-replay_padic_powers.py

Compare each output with the matching `data/04-…`, `data/05-…` or
`data/06-…` file, ignoring line endings (a Windows Python may write CRLF; the
shipped files are LF). At the intake all nine were run under their shipped
names on a copy: each exited with status 0 in under 10 s, and every output
equalled the shipped file; the standard output of `check_rational_powers.py`
equals `data/06-padic-valuations-rational_power_checks.json`. The replay of 09
is meant to be run with `-O`: its README runs it so, and the manuscript says
it "passes with Python assertions disabled".

**Depths five and six, and count bounds (Sections 3.35–3.41).** The three
Python programs of manuscript 70 use only the standard library and write
their JSON **beside themselves under their delivery names**
(`depth5_certificate.json`, `independent_pascal_depth5.json`,
`independent_pascal_depth6.json`), so **work on a copy** of this directory;
the C++ checker prints its JSON to standard output. Use `py`, not bare
`python` (the delivery README says `python`):

    py code/08-depths-five-six-verify_depth5.py
    py code/08-depths-five-six-independent_pascal_depth5.py
    py code/08-depths-five-six-independent_pascal_depth6.py
    g++ -O2 -std=c++17 code/08-depths-five-six-verify_depth6_columns.cpp -o verify_depth6_columns
    ./verify_depth6_columns > depth6_column_certificate.json

Manuscript 68's checker needs SymPy 1.14.0 and writes nothing:

    uv run --no-project --with sympy==1.14.0 python code/07-count-bounds-verify_counts.py

At the intake, on a copy and under the shipped names, all five exited with
status 0 (the slowest, the depth-6 Pascal audit, took 11 s here and 105 s at
placement; compiling the C++ checker took 5 s). Every output equalled the
shipped file, ignoring line endings, except the field `elapsed_seconds` of
`depth5_certificate.json`, which records wall-clock time and can never
reproduce byte for byte; its digest and exact seed ratio agree. The standard
output of `verify_counts.py` equals `data/07-count-bounds-verification.txt`.

## What the modular verifiers do and do not do

Both compiled verifiers are exact. A nonzero residue certifies a nonzero
coefficient outright. Every *zero* residue inside the proved support envelope is
checked again with an exact integer formula rather than being accepted. Neither
is a probabilistic zero test. Manuscript 06's witnesses modulo 1009 and 1013
follow the same rule: a nonzero residue proves nonvanishing, and exact zeros
are the 48 symmetry holes, computed as exact integers by two independent
recurrences.

## Relation to the Lean development

Placement beside a Lean development confers no formal status. The Lean library
`A290268` (`Combinatorics/DerivativeExpansions/A290268/Lean`, namespace
`LeanProofs.A290268`, imported by the root `ProveIt.lean`) defines the
coefficient lattice `coeff n j k` by the recurrence of Section 3.15 in the
same `(j, k)` coordinates, and proves:

- `Count.card_S`: the conjectured support `S n` has cardinality `closedForm n`;
- `Table.a_values_le_53`: `a n = closedForm n` for `n <= 53` (`native_decide`);
- `Main.a_eq_closedForm_of_support`, `Main.a_eq_closedForm_of_two_sided`,
  `Main.a_eq_closedForm_of_support_all`: `a n = closedForm n` **conditional**
  on the support characterization (or its two inclusions). Manuscript 06
  relies on these statements and reads them as conditional;
- `Structural.mem_S_of_coeff_ne_zero`: the structural inclusion, conditional
  on a hypothesis `hhole` of vanishing on the hole line. That line is exactly
  the reflection family of Theorem 3.11 / Theorem 3.29, so either proof would
  discharge `hhole` on paper; neither is formalized, and the module
  `A290268.Hole` named in the declaration's docstring does not exist.

Theorem 3.23 (deficits 1–4) would discharge the nonvanishing inclusion only on
cells of depth at most four, and with Theorem 3.71 (Sections 3.35–3.41, which
neither cite nor rely on the library) at most six; the `Main` theorems stay
conditional. Manuscript
03 (Sections 3.27–3.34) also cites only `A290268.Main` and reads its theorems
as conditional; its Theorem 3.59 covers depth 3 only, already covered by
Theorem 3.23. The six modules of its formalization blueprint (Section 3.33.2:
`A290268.SeriesReduction`, `.FallingFactorial`, `.CenteredMoments`,
`.DepthThreeHarmonic`, `.DepthThreeCertificate`, `.DepthThree`) are proposals
and do not exist; the library defines no `gamma`, and its `coeff` has type
`ℕ → ℤ → ℤ → ℤ`. None of this report's theorems is formalized.

For Part 2 and its Sections 2.11–2.15 there is no neighbouring formal
development at all: no Lean or Rocq file in the repository mentions the
Lehmer–Comtet numbers, A008296 or A293239.

## Relation to neighbouring material

- `Oeis/A290268/README.md` (research notes, outside the collection) is the
  note manuscript 06 continued. It still calls the general-`k` bulk open and
  lists three Lean modules (`A290268.Hole`, `.DepthOne`, `.Series`) that never
  existed; both are stale with respect to this report. It is not edited here.
  Its line "Open core: `D >= 3` negative region" is also stale (its own dated
  correction says deficits 3 and 4 are closed here); it is the line that led
  batch-70 manuscript 03 to call depth 3 open.
- `Combinatorics/ExpressionEnumeration/PowerTowers/` (power-tower *value*
  counts) is unrelated.

## Discrepancies and delivered-file disclosures

- `A290268_result_status.json` is Part 3's delivered status record and is kept
  byte-identical. Its `remaining_obligation` ("k-j >= 3 and n >= 2k+2") and
  `proved_results` predate the addition: the obligation is now `k-j >= 5`, and
  deficits 3 and 4 are classified (Theorem 3.23).
- `code/02-depth-certificates-minimal_verify.py` says in its docstring that it
  is the listing of "Appendix A of article.tex" (the manuscript's numbering;
  here Section 3.25.2). `code/02-depth-certificates-verify.py` gives
  `python3 code/verify.py` as its usage line and writes unprefixed file names
  under `--write-data`. `code/02-depth-certificates-Makefile` uses the
  delivery names throughout (see above).
- `02-depth-certificates-SOURCE_AUDIT.md` cites the pinned repository URLs of
  `afb2d1227`, calls the inspected note's general-`k` bulk open, and does not
  know this report; the article corrects this in Section 3.25.3.
- In Part 3's own reproduction listing (Section 3.12) the build commands still
  name the original `A290268_partial_results.tex`; the file is `article.tex`.
- `code/03-depth-three-verify_depth3.py` (byte-identical to the delivered
  `verify_depth3.py`) records the manuscript's pin `a02ab3567` as
  `REPO_COMMIT`, writes the unprefixed `depth3_certificate.txt` beside itself
  (see "Verifying"), and the manuscript gives its usage as
  `python3 verify_depth3.py`. A code comment in it says the last range of each
  sign row is replaced by an infinity marker; the output does not do so — the
  rows end at `q = 38` (for example `35-38:-`), and their behaviour beyond 38
  is the analytic part of the proof, not the computation.
- `data/03-depth-three-depth3_certificate.txt` heads its theorem line
  "Verified theorem: gamma(k,3,M)=0 ... iff M=k+13 and k is odd". The program
  checks the finite strip, the anchors and the diagnostic boxes; the
  all-`k`, all-`M` statement rests on the proof in Sections 3.30–3.31, not on
  the run. Its pin line is the manuscript's pin.
- The manuscript's own file table lists its `.tex`, `.pdf` and `README.md`,
  which are not shipped; the article replaces that table with the shipped
  file list (Section 3.34.2).
- Sources 04–06 (Sections 2.11–2.15): the shipped programs, byte-identical to
  the delivery, write under their delivery names beside themselves (see
  "Verifying"); the replays of 09, 12 and 17 use `with_suffix('.json')`, so on
  the shipped layout they write `code/<prefixed name>.json`, not the
  `data/` file. The JSON files keep the manuscripts' letters (`r` = offset `d`,
  `m` = multiplier `mu`); the field `primitive_r8` of
  `data/05-prime-multiple-replay_convolution.json` holds the coefficients of
  `F(Y) = R_8(Y+8)`, not of Part 2's `R_8(X)`. The delivery READMEs (not
  shipped) give `python <name>.py` commands and list files that are not
  shipped (`article.pdf`, `article.tex`, `build_local.sh`, 09's companion PDF
  and zip). The manuscripts' bibliography entries call this report "Part I";
  the article re-targets them to Part 2.
- Sources 07 and 08 (Sections 3.35–3.41): manuscript 70's three Python
  programs write their JSON beside themselves under the delivery names, and
  the delivery README tells the user to run `python …` in the extracted
  folder; `data/08-depths-five-six-depth5_certificate.json` contains a
  wall-clock `elapsed_seconds`. The docstring of
  `code/08-depths-five-six-independent_pascal_depth6.py` (and of its depth-5
  twin) says the centered recurrence is used "only for its separate moment
  seed": the central seed is recomputed by the same recurrence as in the
  main certificate; the rectangles are the independent part (the tail seed is
  a harmonic sum and needs no recurrence). The programs and JSON keep the manuscripts' letters (`R`,
  `Q` cutoffs, `D` the depth). Manuscript 68's bibliography names
  `ProveIt_A290268_Depths_Five_Six.zip` for "the companion"; the article
  re-targets it to Theorem 3.81. Its main source loads `sharpness.tex` with
  `\IfFileExists`; the file is printed in Section 3.40 and not shipped.
  `data/07-count-bounds-requirements.txt` is byte-identical to a requirements
  file already in the repository (`sympy==1.14.0`).

## Provenance

The three original reports were merged into one article on 20 September 2026
(`630e041e5`, Cardinals history) and brought into ProveIt with the Cardinals
repository (`dc54c3cb3`). Manuscript 06 of batch 42 arrived in `8315d24e3`,
was placed as an addition in `3609d0473` (staged files prefixed
`02-depth-certificates-`, byte-identical to the delivery), and was written
into Sections 3.14–3.26 on 29 September 2026, with dated notes pointing
forward from the abstract, the reading guide, §1.5, Part 3's status box,
Theorem 3.1, Section 3.7.4, the precise missing step (Section 3.10), Part 3's
conclusion and Section 5.

Manuscript 03 of batch 70 arrived in `1b3960d8a`, was placed as an addition
in `51c6943bf` (staged files prefixed `03-depth-three-`, byte-identical to
the delivery; manuscript, README, PDF and `SHA256SUMS.txt` not staged), and
was written into Sections 3.27–3.34 on 30 September 2026, with dated notes
pointing forward from the abstract, the reading guide, §1.5, Part 3's status
box, Section 3.7.4, the sign-change observation of Section 3.20 and
Questions 3 and 7 of Section 3.24.

Manuscripts 12, 09 and 17 of batch 72A arrived in `1512ef835` (with seventeen
others of their cluster), were placed as additions 05, 04 and 06 in
`d292c6765` (staged files prefixed `05-prime-multiple-`,
`04-stirling-residues-` and `06-padic-valuations-`, byte-identical to the
delivery; manuscripts, READMEs, PDFs, 09's embedded copy of 12 and the
`build_local.sh` wrappers not staged), and were written into Sections
2.11–2.15 on 1 October 2026, with dated notes pointing forward from the
abstract, the reading guide, §1.5, Part 2's "What remains" (Section 2.10)
and Section 5.1. All three are pinned to `ca81647a9`; all carry the line
"Research note prepared for Vladimir Reshetnikov with OpenAI".

Manuscripts 70 and 68 of batch 72A arrived and were placed in the same
commits, as additions 08 and 07 (staged files prefixed
`08-depths-five-six-` and `07-count-bounds-`, byte-identical to the
delivery; manuscripts, READMEs, PDFs, 68's `sharpness.tex` and the
`build_local.sh` wrappers not staged), and were written into Sections
3.35–3.41 on 1 October 2026, with dated notes pointing forward from the
abstract, the reading guide, §1.5, Part 3's status box and its update on
`Lambda(n)`, Sections 3.7.4 and 3.10 and Part 3's conclusion, the batch-42
introduction, example and conclusion, Questions 1–4 of Section 3.24, the
formal-status list, the batch-70 introduction, its note on what depth four
leaves open and two of its research questions ("Critical-strip bounds",
"Asymptotic harmonic phases"), and Sections 5.1 and 5.5. Question 6 of
Section 3.24 carries no note from this write; Section 3.40 says what
manuscript 68 contributes to it. Both manuscripts are pinned to `ca81647a9`
and carry the same "with OpenAI" line.

These are AI-assisted drafts. None is refereed or machine-checked.
