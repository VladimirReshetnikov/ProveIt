# A cyclic-coloring obstruction to maximal binary DFAO reversal

**Nonattainment of the full coloring space for every 3 ≤ k ≤ n, the exact three-output maximum for every n ≥ 7, the exact maximum for four and more outputs, and a second four-output route with stability and the missing orbits**

This is a research report in four parts. Part I is the original report of
20 September 2026, itself the merge of two independently prepared packages.
Part II was added on 28 September 2026 in batch 39 of ProveIt's
incoming-report intake, from a later manuscript that answers, for three
outputs, the question Part I left open: the exact value of `R_2(n,k)` beyond
its finite range `7 ≤ n ≤ 30`. Part III was added on 29 September 2026 in
batches 40–41, merged from three further manuscripts that answer the same
question for four and more outputs (Part II's Question 23.1). Part IV was added
on 29 September 2026 in batch 43, merged from two manuscripts that, written
before Part III was printed, re-derive its `k = 4` case with a much smaller
analytic threshold (26 against `N(4) = 212`) and add stability theorems, the
missing-orbit inventory, the count of extremal output maps and a recurrence of
proved minimal order 15. All sources were prepared for Vladimir Reshetnikov and
are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | two Cardinals-collection packages of 20 Sep 2026, `dfao-reversal-cyclic-coloring` (the spine) and `dfao-reversal-coloring-bound`, merged into one report | `dfao_reversal_research.zip` + `binary_dfao_reversal_research.zip` (as the collection manifest records them) | (none) | merged `8374aaa79` (Cardinals repository), in ProveIt since `dc54c3cb3` | Part I: Sections 1–12 (pp. 1–29), Appendices A–D (pp. 138–141); Section 1.3 records what each package contributed |
| 02 | batch 39, manuscript 06 (*Exact Binary Reversal with Three Outputs: An all-state solution and rigidity of extremizers*, 28 Sep 2026, 19-page PDF as delivered) | `ProveIt_Three_Output_Reversal.zip` (inner `three_output_reversal/`, main file `article.tex`) | `fbba58593` | `e2b1f016a` (prefix `02-three-output-`) | Part II: Sections 13–27 (pp. 30–51) |
| 03 | batch 40, manuscript 01 (*Eventual Optimality in Binary DFAO Reversal: Closest coprime cycles, a parity-sensitive defect law, and exact finite certificates*, 28 Sep 2026, 22-page PDF) | `ProveIt_DFAO_Eventual_Optimality.zip` (inner directory of the same name), arrived `017e6c0d8` | `2cdcd74f3` (with Part I's blobs `e6dbd47b` article, `13166e22` README) | `afb2d1227` (prefix `03-eventual-`) | Part III (pp. 52–106), label sub-prefix `evo:et:`: Sections 30, 35, 36, parts of 31–32, 38, 41, 44–47 |
| 04 | batch 40, manuscript 03 (*Binary DFAO Reversal: Exact Three-Output Complexity, Odd-Output Rigidity, and Sharp Deficit Asymptotics*, 28 Sep 2026, 21-page PDF) | `ProveIt_Binary_DFAO_Reversal.zip` (inner directory of the same name), arrived `017e6c0d8` | `2cdcd74f3` | `afb2d1227` (prefix `04-deficit-asymptotics-`) | Part III, label sub-prefix `evo:da:`: Sections 37, 38, 42, parts of 29, 32, 41, 43–47 |
| 05 (base of Part III) | batch 41, manuscript 06 (*Eventual Exactness in Binary DFAO Reversal: Balanced coprime cycles, a uniform quartic threshold, and rank-sensitive obstructions*, 28 Sep 2026, 22-page PDF) | `ProveIt_Binary_Reversal_Exactness.zip` (inner `binary_reversal_eventual_exactness/`), arrived `9754e8360` | `e2b1f016a` | `eaf787d50` (prefix `05-quartic-threshold-`) | Part III, labels `evo:`: Sections 28–29, 31–34, 39–41, 43–47 |
| 06 | batch 43, manuscript 03, called FO in Part IV (*Exact Four-Output Binary Reversal: Optimal state complexity, collision rigidity, and secondary asymptotics*, 29 Sep 2026, 21-page PDF) | `ProveIt_Four_Output_Reversal.zip` (inner directory of the same name), arrived `06bcc37a8` | `c130dba62` | `faef2ed2a` (prefix `06-four-output-`) | Part IV (pp. 107–138), label sub-prefix `fo:fo:` and shared `fo:` labels: the second routes of Sections 50–53, the penalty and stability of Section 53, parts of 49, 51, 54–59 |
| 07 (base of Part IV) | batch 43, manuscript 05, called AS in Part IV (*Exact Binary Reversal with Four Outputs: An all-state formula, quantitative rigidity, and the structure of the missing reversal states*, 29 Sep 2026, 21-page PDF) | `ProveIt_Four_Output_Reversal (1).zip` (inner `four_output_reversal/`; a download-name collision, not a re-ship of 06), arrived `06bcc37a8` | `8315d24e3` (with this report's blobs `84923bc5` article, `f93f98bb` `03-eventual-SOURCE_AUDIT.md`) | `faef2ed2a` (prefix `07-all-state-`) | Part IV, labels `fo:as:` and shared `fo:`: Sections 48–59 |

The pins in full: `fbba58593dc0622aa914972896150d4848f935b5` (Part II),
`2cdcd74f3abcbbff7bd47c6c4265522395def609` (batch-40 manuscripts 01 and 03)
and `e2b1f016a94102663f12b970e6dd434229f90d01` (batch-41 manuscript 06). At
all three pins Part I's `article.tex` had blob `e6dbd47b…` and its
`README.md` blob `13166e22…`, unchanged at the placement commits, so every
statement the manuscripts make about Part I refers to the text printed here.
None of the three Part III manuscripts knew Part II's text: 01 and 03 were
pinned before it was placed, and 06 was pinned at its placement commit, where
only its files (and its source audit, which 06 read) existed. The batch-43 pins in full are
`8315d24e33a0f4901ca85f0e330ed1d5e19b1ae2` (AS) and
`c130dba623c420551d90db41dae7b3d9cff72dfd` (FO); at both, `article.tex` had
blob `84923bc5…` (Parts I–II printed, Part III staged but written only in
`18634ca66`, after both pins), so neither Part IV manuscript knew Part III's
threshold `N(k)` or its all-`n` closure of `4 ≤ k ≤ 7`. The manuscripts,
PDFs and delivery READMEs of Parts II–IV are not shipped and survive in
the arrival commits. Each part prints every result, proof, example, remark,
limitation and question of its manuscripts; what a manuscript re-derives from
an earlier part is printed once and credited, and genuinely different proofs
are kept as marked second routes. Sections 27.6, 47.7 and 59.7 of the article
list where the merges had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The finite
computations check stated finite ranges and implementations; they are not a
proof of the all-`n` statements. Attainment in Parts II and III (and in
Part I's finite optimality result) rests on published external theorems:
Davies's Theorem 3 / Corollary 3, and, in Part III's second route, the
Holzer–König two-generation theorem for the monoid `U_{a,b}`; they are cited,
not reproved. Part III's closure of `4 ≤ k ≤ 7` below its analytic threshold
is computer-assisted, and so are Part IV's certificates below `n = 26`; Part
IV's attainment imports the Holzer–König theorem.

## Results

For maps `a, b : Q → Q` and `τ : Q → Δ` with `|Q| = n`, `|Δ| = k`, the
reachable reverse states are the coloring orbit `τ⟨a,b⟩`; for accessible
DFAOs its size is the state complexity of the reversal (Proposition 2.1).
Throughout, `(a_n, b_n)` is the closest coprime split of `n`: `(h, h+1)` for
`n = 2h+1`, `(h−1, h+1)` for `n = 2h` with `h` even, `(h−2, h+2)` for `n = 2h`
with `h` odd (Part II writes `(A_n, B_n)`).

**Part I** (unchanged apart from dated pointers) gives a self-contained
proposed proof of

    |τ⟨a,b⟩| ≤ k^n − k! + g(k) < k^n        (3 ≤ k ≤ n),

where `g(k)` is Landau's function, answering Davies's Problem 1
(arXiv:1705.07150v2, Section 5, printed page 17). The `k = n` case is
Holzer–König's classical bound and is not claimed as new. Nonattainment is
proved twice, by a short qualitative route (Lemma 4.1, Theorem 4.2) and by the
counting argument (Theorem 1.1). Part I also proves an abelian-permutation
extension, a polynomial-time missing-coloring algorithm with two certificate
formats, two instance-specific chromatic bounds and a universal structural
bound `U(n,k)` (Theorem 9.4); a complete C++ enumeration settles all 462,066
reduced instances with `n ≤ 4`; and `U(n,k)` equals the published lower
construction `L(n,k)` on all 372 pairs `7 ≤ n ≤ 30`, `3 ≤ k < n`
(Proposition 10.1), a finite computer-assisted optimality result.

**Part II** (batch 39) works at `k = 3`. It proves:

1. **`R_2(n,3) = 3^n − 3(2^A + 2^B − 2) + B` for every `n ≥ 7`**
   (Theorem 13.1), `(A,B) = (a_n,b_n)`, whether the original automaton is
   required to be accessible with `n` states or minimal with exactly `n`
   states; the upper bound `|τ⟨s,t⟩| ≤ 3^n − D_n` holds for arbitrary maps. The
   upper bound is new; the attainment is Davies's published construction. This
   settles the `k = 3` slice of Davies's Problem 2.
2. Every extremizer has one permutation letter with cycles of lengths `A, B`
   and one rank-`(n−1)` singular letter with exactly one cross-cycle double
   fiber; the output is constant on the `A`-cycle and primitive on the
   `B`-cycle; and the reachable set is every improper coloring of `K_{A,B}`
   plus one `B`-element proper orbit (Theorem 19.1). These conditions are
   necessary, not sufficient (Example 19.3).
3. A `6AB` penalty for a second cross collision (Proposition 19.2), the orbit
   inventory of the missing colorings (Theorem 20.1), residue-class
   asymptotics `(3^n − R_2(n,3))/2^{n/2} → 9/√2, 15/2, 51/4` and an order-12
   linear recurrence for the deficit (Corollaries 21.1, 21.2).

Added in that merge (not stated by the manuscript): Remark 18.3 shows
`D(n,3) = D_n` and `U(n,3) = L(n,3) = R_2(n,3)` for every `n ≥ 7`; the closed
form equals the `upper` and `lower` columns and the split of all 24 rows
`k = 3` of `data/finite_range_bounds.csv` (Section 18.2).

**Part III** (batches 40–41). With `𝓑_k(a,b)` the number of proper
`k`-colorings of `K_{a,b}` (Part I's `B_k(a,b)`):

1. **`R_2(n,k) = k^n − 𝓑_k(a_n,b_n) + a_n b_n` for every `k ≥ 4` once
   `n ≥ N(k)`**, with an explicit integer-defined threshold `N(k) ≤ 3k^4`
   (`N(4..7) = 212, 240, 954, 840`), **and for every `n ≥ max(7,k+1)` when
   `4 ≤ k ≤ 7`** (Theorems 28.1, 33.4, 34.1, Corollary 33.5; manuscript 06).
   The upper bound is proved conventionally for `n ≥ N(k)`; below `N(k)` for
   `k = 4..7` two exact-integer implementations check 9,247,046 structural
   comparisons in 2,217 rows (computer-assisted). Attainment is Davies's
   construction; original-state minimality is proved. Because the range
   `n ≥ 3k^4` lets `k` grow, the formula holds for every `4 ≤ k ≤ (n/3)^{1/4}`.
2. Manuscript 06 also proves strict bipartite balancing (Theorem 31.3, via
   total positivity of Stirling numbers), the necessary structure of every
   maximizer for `k ≥ 4` in its exactness range, including singular-letter
   rank `n − 1` (Theorem 39.1; necessary, not sufficient, Example 39.3), a
   matching hierarchy of rank-sensitive upper bounds (Theorem 40.1,
   Proposition 40.2), and exact exponential expansions of the optimal deficit:
   one leading constant for even `k`, three residue-dependent ones for odd `k`
   (Theorems 41.2, 41.4).
3. Manuscript 01 (a second, non-effective route): the exact formula
   `R_2(n,k) = k^n − 𝓑_k(a_n,b_n) + G_k(a_n,b_n)` (`G_3 = b`, `G_k = ab` for
   `k ≥ 4`) for every fixed `k ≥ 3` and all sufficiently large `n`, with no
   explicit threshold (Theorem 36.1); an eventual if-and-only-if extremizer
   criterion (Theorem 36.4); a proof of the witness's orbit from the
   Holzer–König two-generation theorem (Section 30); a quantitative balancing
   gap (Theorem 31.4); eventual recurrences and rational generating functions
   on residue classes (Theorem 41.6, Corollary 41.7); and **919 exact finite
   certificates** establishing the formula for all `7 ≤ n ≤ 100`,
   `3 ≤ k ≤ min(12, n−1)` (Proposition 35.1), which extends Part I's
   `n ≤ 30`.
4. Manuscript 03 (a third route): a second proof of Part II's Theorem 13.1
   (analytic for `n ≥ 32`, a 3,717-inequality certificate for `7 ≤ n ≤ 31`;
   Theorem 38.1) with a weaker rigidity theorem (Theorem 38.4); sharp
   first-order asymptotics for every fixed `k ≥ 3` (also proved by 01 and 06;
   Theorem 41.1: `lim D_k(n)^{1/n} = √⌊k²/4⌋`); eventual exactness for fixed
   odd `k` (Theorem 37.2) and near-optimal rigidity (Corollary 37.3); and, for
   even `k`, an interval of asymptotically optimal cycle proportions within
   the witness family (Theorem 42.1), which is a first-order statement.

Added in the merge (not stated by the manuscripts): Remark 33.6 shows
`U(n,k) = L(n,k) = R_2(n,k)` on Part III's exactness range, the `k ≥ 4` case
of Part I's Section 12.1 problem; for the one entry of Part I's collection
that manuscript 06 does not treat (nonsurjective outputs), `k^n − (k−1)^n >
D*_k(n)` was checked in the write phase on all 2,217 finite rows. Section 35.5
records the write-phase comparisons: all 919 rows of
`data/03-eventual-finite_certificates.csv` and all 372 rows of Part I's
`data/finite_range_bounds.csv` equal the closed formula and split; 375 rows
overlap between manuscripts 01 and 06 and 95 between Part I and 06, all equal;
manuscript 06's rows agree with the formula in all 1,025 rows with `n ≤ 300`
that were recomputed; the 13 threshold rows were recomputed from their
definition; manuscript 03's 25 rows equal Part II's.

**Part IV** (batch 43) works at `k = 4`. Both manuscripts (called AS and FO in
the article) were written before Part III was printed and re-derive its
`k = 4` case; the formula is printed as Part III's (and Part I's for `n ≤ 6`),
with their proofs as a second route.

1. **Second route to `R_2(n,4) = 4^n − 6·2^n − 4(3^a + 3^b) + 12(2^a + 2^b) − 12 + ab`**
   (`(a,b) = (a_n,b_n)`, every `n ≥ 7`) and `R_2(4,4) = 176`,
   `R_2(5,4) = 826`, `R_2(6,4) = 3526` (Theorem 48.1). Not new: the formula is
   Part III's Theorem 28.1 at `k = 4` (Theorem 34.1 for `7 ≤ n ≤ 211`,
   `N(4) = 212`), and the three small values are in Part I's small-case table
   (Section 10.2) with the same witness arrays (Appendix A). New: the upper
   bound is **analytic for every `n ≥ 26`** (AS, Proposition 50.2; FO,
   Proposition 50.5), against Part III's `N(4) = 212`, and below 26 a finite
   certificate of **2,082** integer comparisons for `4 ≤ n ≤ 25` (AS) or
   **2,059** for `7 ≤ n ≤ 25` (FO) suffices (Proposition 51.2, Table 13);
   every structural case other than the optimal biclique has deficit larger by
   more than `a_n b_n` (Corollary 51.3). Like `N(4)`, 26 is only sufficient
   (Remark 50.6).
2. Rigidity at `k = 4` (Theorem 53.1): the output uses exactly two colors on
   each cycle with primitive words, and the reachable set is every improper
   coloring of `K_{a,b}` plus one proper orbit of length `ab`, with the
   converse; this specializes Part III's Theorem 39.1. The second-collision
   penalty `4^{a+b} − 𝓑_4(a,b) − 12ab(2^{a−1}+2^{b−1}−2) + ab` (FO, for every
   output map; Proposition 53.4) is Part III's Theorem 40.1 with (40.7) at
   `k = 4, t = 2`, under a weaker hypothesis on the singular letter; AS's
   `R_2(n,4) − 24ab` (Proposition 53.5, proper outputs only) is weaker.
   Necessary is not sufficient: FO's 7-state example has 212 reverse states
   (Remark 53.2).
3. **Stability** (new): an orbit larger than `R_2(n,4) − a_n b_n/2` forces the
   optimal split, one cross double fiber and primitive `2+2` palettes (AS,
   Theorem 53.6); for `n ≥ 26`, a deficit below `7·2^n` forces two full coprime
   cycles `a' ≤ b'` with deficit at least `6·2^n + 3^{b'} − n²/4`, and a deficit
   at most `6·2^n + κ3^{n/2}` (with `κ3^{n/2} < 2^n`) bounds
   `b' − a' ≤ 2 log_3(κ + n²/(4·3^{n/2}))` (FO, Theorem 53.7).
4. **The missing orbits** (new at `k = 4`): an extremizer misses
   `o_{u,v} − [(u,v)=(a,b)]` orbits of length `uv` for `u | a`, `v | b`, with
   `o_{u,v}` given by primitive-word counts (Theorem 54.2; at `n = 7`, 175
   missing orbits, 912 colorings, Example 54.3); on the standard witness
   exactly `6P_2(a)P_2(b)` output maps are extremal (AS, Theorem 54.4; 432 at
   `n = 7`).
5. **A minimal recurrence** (new): from `n = 7`, `D_4(n) = 4^n − R_2(n,4)`
   satisfies the recurrence with characteristic polynomial
   `(x−2)(x⁴−9)(x⁴−4)(x−1)²(x⁴−1)`, of proved minimal order 15 (AS; FO proves
   that the same operator annihilates), and `R_2(n,4)` one of minimal order 16;
   the tail generating function has this reduced denominator (Theorem 55.2,
   Corollary 55.3). Exact residue formulas make Part III's Theorem 41.2 exact
   at `k = 4`: `(D_4(n) − 6·2^n)/3^{n/2} → 16/√3, 40/3, 328/9` for `n` odd,
   `≡ 0`, `≡ 2 (mod 4)` (Proposition 55.1).

Added in that merge (not stated by the manuscripts): Section 51.2 compares the
closed form with Part I's 24 rows `k = 4`, manuscript 01's 94 rows, the 205
rows of `data/05-quartic-threshold-finite_k4.csv` (split and target) and the
two new certificates (213 FO rows, 22 AS rows): no mismatch, and identical
margins on `7 ≤ n ≤ 25`; Remark 55.4 shows that Part III's `k = 4` annihilator
`(E−1)³(E−4)(E−9)(E−16)` is minimal on each residue class (answering Part
III's Question 44.15 at `k = 4`); Remark 50.6 compares the thresholds; and
Proposition 53.4 is shown to imply Proposition 53.5.

## Not claimed

- Davies's Problem 2 in full: the exact maximum for `k ≥ 8` with
  `max(7,k+1) ≤ n < N(k)` stays open outside the certified finite ranges
  (Part I: `n ≤ 30`; manuscript 01: `n ≤ 100` for `k ≤ 12`), for example
  `k = 8`, `101 ≤ n ≤ 2687`; so does the boundary `k = n` and the
  near-diagonal regime. Part II's Question 23.1 is re-scoped, not closed
  (Question 44.1). None of the parts settles Davies's other Section 5
  questions or the largest-two-generated-transformation-monoid problem.
- No least thresholds: `N(k)` is sufficient, not optimal; manuscripts 01 and
  03 prove only that some threshold exists. Part IV's `26` at `k = 4` is also
  only sufficient for its particular estimates. Every asymptotic statement of
  Part III is for fixed `k`; the only uniform statement is the threshold
  `n ≥ 3k^4`. Manuscript 03's plateau theorem is first order and concerns the
  witness family; it does not say that every split in the interval is exactly
  optimal (only the nearest split is, in the proved range).
- No new proof of Davies's lower construction or of the Holzer–König
  two-generation theorem; Part III's Section 30 proves only the saturation
  step given generation. Finite breadth-first searches do not replace that
  dependency.
- Part IV's four-output formula is not a new theorem: it is Part III's
  Theorem 28.1 at `k = 4` (and Part I's table for `n = 4, 5, 6`, values 176,
  826, 3526); Part IV prints the manuscripts' proofs as a second route. Its
  claims are confined to four outputs; its penalties and stability radius are
  not claimed sharp, no second-largest value or distance between transition
  tables is given, and its output-map count concerns one fixed transition pair.
- No classification of extremizers: the rigidity theorems (Parts II–IV)
  give necessary conditions only (Examples 19.3 and 39.3, Remark 53.2); the `6AB` penalty
  and the matching bounds are proved only under their stated hypotheses; no
  classification of extremal transformation monoids (orbit extremality is
  weaker than monoid-size extremality); no second-best value or near-maximum
  spectrum.
- No novelty for the orbit reduction, the lower witness, the graph
  classification method, primitive-word counting, standard Stirling and
  palette identities, the small values 24, 67, 218, 699 (exact in Davies's
  Table 3), the `n = 8`, `k = 5` value 369020, the ternary witness, the Landau
  function, the diagonal specialization `k = n`, or graph coloring as a
  method. The threshold `n ≥ 7` is essential: at five states the coprime
  two-cycle construction is not optimal.
- No priority. All literature checks were targeted (Part I on
  20 September 2026, Parts II and III on 28 September 2026, Part IV on
  29 September 2026); none is an
  exhaustive citation-index review, a survey of theses, or correspondence with
  the author. A missing search hit is not evidence that no earlier or later
  result exists.
- No claim that random tests, finite enumerations or finite tables establish a
  universal theorem, that a finite region plus an unspecified tail covers
  every intervening `n`, or that all improper colorings are reachable in
  arbitrary cases (Parts II–IV prove it only for extremizers).

## Labels

Part I's 90 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`rem:`, `tab:`, `fig:`, `app:`); Part II's 82 carry the prefix `tor:`
("three-output reversal"); Part III added **201** labels, all with the prefix
`evo:` ("eventual optimality"): manuscript 06's material uses plain `evo:`,
manuscript 01's `evo:et:` and manuscript 03's `evo:da:` ("deficit
asymptotics"). Part IV added **106** labels, all with the prefix `fo:` ("four
outputs"): material only in manuscript AS uses `fo:as:` (23), material only in
FO `fo:fo:` (20), and statements of both, or added in the merge, plain `fo:`
(63). Total: 479 (pattern `\\label(\[[^]]*\])?\{`; 373 before Part IV, 172
before Part III). No label was renamed or removed. Part III starts at Section 28; its
tables continue the numbering (Tables 6–11) and its figure is Figure 2. Part IV
starts at Section 48 and has Tables 12–13. In the
`.aux` files of the committed and the new build every label of Parts I and II
has the same number (page numbers after Part I's Section 1.4 moved, because of
the dated pointers). Comparing the `.aux` files of the committed three-part
build and the four-part build, every one of the 373 earlier labels keeps its
number; only pages in Part III (dated pointers) and in the appendices moved.
Part I's appendices come after Part IV and contain no
numbered equations, tables, figures or theorem-like items.

As recorded for Part II, the theorem-like environments are declared through
alias counters (`aliascnt`), so each cross-reference carries its own name.

## Notation

Part I's symbols keep their meanings. Table 5 (Section 13.2) lists Part II's
symbols and Table 6 (Section 28.2) Part III's, each with the tempting false
reading. The most important points:

- `𝓑_k(a,b)` (`\Bip_k`) is the proper `k`-coloring count of `K_{a,b}`, Part I's
  `B_k(a,b)`; manuscripts 06 and 03 call it `P_k(a,b)` and 01 calls it
  `B_k(a,b)`. Manuscript 03's `B_k(n)` is the **maximum** (here `R_2(n,k)`,
  01's `M_k(n)`), not a coloring count.
- `D_k(n) = k^n − R_2(n,k)` is the optimal deficit and
  `D*_k(n) = 𝓑_k(a_n,b_n) − G_k(a_n,b_n)` the witness deficit (01's
  notation); manuscript 06's `D_k(n)` is `D*_k(n)` here. Part I's `D(n,k)` is
  the minimum of its finite collection and Part II's `D_n` is `D*_3(n)`.
- `N(k)` is manuscript 06's explicit threshold; `N_∃(k)` is the unspecified
  threshold of manuscripts 01 and 03 (their `N(k)`).
- `G_k(a,b)` is Part I's period term (01's `T_k`, 03's `γ_k`), not Part I's
  residual-order bound `T_{r,k}`.
- Part IV (Table 12, Section 48.2): the manuscripts' `A, B` and `D_n` are
  written `a_n, b_n`, `D*_4(n)` (formula, `n ≥ 7`) and `D_4(n)` (optimum,
  `n ≥ 4`) — Part II's `D_n` is the **three**-output deficit; their `𝓑(a,b)` is
  `𝓑_4(a,b)`; FO's cycles `L, R` are `X, Y`; the two manuscripts' clashing
  `E` are renamed `Ω^e_4(a,b)` (FO: one-monochromatic-edge colorings) and
  `𝓒_{u,v}` (AS: proper colorings with exact periods `u, v`); FO's `N_{u,v}`
  is `o_{u,v}`; the order-15 polynomial is `χ_4`, with shift `𝖲` in `n`
  (Part III's `𝖤` shifts the residue step `t`); `ψ(t) = 3^t − 3·2^t` is AS's
  `h(t)` and a quarter of FO's `g(t)`. No normalization changed.
- Manuscript 06's threshold constants are hatted: `Ĥ, M̂, Ĉ, B̂, L̂, Ŝ, Û` are
  its `H, M, C, B, L, S, U` (the keys of
  `data/05-quartic-threshold-thresholds.json`), renamed because of Part I's
  `H_r`, `M(n,k)`, `C_L(k)`, `B_k`, `L(n,k)`, `U(n,k)`.
- `λ_k = √⌊k²/4⌋` (06's `λ`, 01's `s_k`, 03's `α_k`); `ω_h = log((h+1)/h)`
  with `h = ⌊k/2⌋` (01's `λ`, 03's `log t`); `δ_n = (b_n − a_n)/2 ∈ {1/2,1,2}`
  as in 06 and 03 — manuscript 01's `δ_n` is twice this, the only
  normalization change. `J(r)` is Part II's largest partition product (01's
  `A(r)`); `γ_r = ⌊3^{r/3}⌋` is 06's `g_r`, not Landau's `g(k)`. The two
  cycles of a two-cycle permutation are `X, Y` (06's and 01's `A, B`).

## Files

```
article.tex                            the report, standalone LaTeX with an internal bibliography; \inputs
                                       data/04-deficit-asymptotics-finite_table.tex
article.pdf                            the compiled report, 147 pages (title page, contents pp. i–iv,
                                       Part I pp. 1–29, Part II pp. 30–51, Part III pp. 52–106,
                                       Part IV pp. 107–138, Part I's appendices pp. 138–141,
                                       bibliography pp. 141–142)
README.md                              this guide
Makefile                               Part I: build, check and audit targets (build in place; see below)
source_audit.md                        Part I: locations inspected in Davies v2, attribution, dependency boundary
RESEARCH_STATUS.md                     Part I: status record of the merged-in source dfao-reversal-coloring-bound
LITERATURE_SEARCH.md                   Part I: that source's literature-search record
02-three-output-SOURCE_AUDIT.md        Part II: manuscript 06's source audit (delivered as SOURCE_AUDIT.md)
03-eventual-SOURCE_AUDIT.md            Part III, batch-40 01: source and proof audit (delivered as SOURCE_AUDIT.md)
04-deficit-asymptotics-SOURCES.md      Part III, batch-40 03: sources and novelty audit (delivered as SOURCES.md)
04-deficit-asymptotics-STATUS.md       Part III, batch-40 03: theorem-by-theorem status (delivered as STATUS.md)
05-quartic-threshold-SOURCE_AUDIT.md   Part III, batch-41 06: sources, scope, provenance (delivered as SOURCE_AUDIT.md)
05-quartic-threshold-RESEARCH_STATUS.md  Part III, batch-41 06: research status (delivered as RESEARCH_STATUS.md)
06-four-output-SOURCE_AUDIT.md         Part IV, FO: source and novelty audit (delivered as SOURCE_AUDIT.md)
06-four-output-PROOF_AUDIT.md          Part IV, FO: proof audit and verification boundaries (delivered as PROOF_AUDIT.md)
07-all-state-SOURCE_AUDIT.md           Part IV, AS: source and novelty audit (delivered as notes/SOURCE_AUDIT.md)
07-all-state-PROOF_AUDIT.md            Part IV, AS: proof and verification audit (delivered as notes/PROOF_AUDIT.md)
code/reversal.py                       Part I: primary implementation (composition, orbits, missing
                                       colorings, CRT membership, chromatic counts, structural bound, u_witness)
code/run_checks.py                     Part I: primary Python suite and the finite-range CSV
code/check_bound_certificate.py        Part I: independent re-evaluation of the 372 bounds
code/check_large_example.py            Part I: tuple-set BFS of the n=8, k=5 witness
code/orbit_count.cpp                   Part I: single-instance C++17 BFS over code/bfs_cases.txt
code/bfs_cases.txt                     Part I: the 20 BFS fixtures
code/exhaustive.cpp                    Part I: complete C++17 enumeration for n ≤ 4
code/dfao.py                           Part I: second implementation family
code/certificate_checker.py            Part I: standalone certificate verifier (imports nothing from dfao.py)
code/run_experiments.py                Part I: second audit suite
code/test_dfao.py                      Part I: ten unit tests
code/02-three-output-verify.py         Part II: structural comparisons, witness BFS, inventories (delivered as code/verify.py)
code/02-three-output-independent_check.py  Part II: independent arithmetic checks (delivered as code/independent_check.py)
code/02-three-output-Makefile          Part II: the delivered root Makefile (pdf/check/clean)
code/03-eventual-verify.py             Part III (01): producer of the 919 certificates and 42,960 checks (delivered as code/verify.py)
code/03-eventual-check_certificates.py Part III (01): independent certificate checker (delivered as code/check_certificates.py)
code/03-eventual-Makefile              Part III (01): the delivered root Makefile (all/pdf/verify/clean)
code/04-deficit-asymptotics-verify.py  Part III (03): producer of the 3,717-candidate certificate and 4 BFS checks (delivered as code/verify.py)
code/04-deficit-asymptotics-independent_check.py  Part III (03): independent reconstruction (delivered as code/independent_check.py)
code/04-deficit-asymptotics-Makefile   Part III (03): the delivered root Makefile (all/check/pdf/clean)
code/05-quartic-threshold-theorem_checks.py  Part III (06): primary finite closure k = 4..7 and threshold table (delivered as code/theorem_checks.py)
code/05-quartic-threshold-independent_check.py  Part III (06): independent closure (delivered as code/independent_check.py)
code/05-quartic-threshold-supplementary_checks.py  Part III (06): regression checks; imports theorem_checks (delivered as code/supplementary_checks.py)
code/05-quartic-threshold-Makefile     Part III (06): the delivered root Makefile (all/pdf/check/clean)
code/06-four-output-verify.py          Part IV (FO): certificate, n ≤ 200 sweep, inventories, recurrence (delivered as code/verify.py)
code/06-four-output-independent_check.py  Part IV (FO): independent re-derivation (delivered as code/independent_check.py)
code/06-four-output-witness_bfs.cpp    Part IV (FO): C++17 packed-color BFS of the witness, n = 7..12 (delivered as code/witness_bfs.cpp)
code/06-four-output-Makefile           Part IV (FO): the delivered root Makefile (all/check/independent/bfs/pdf/clean)
code/07-all-state-verify.py            Part IV (AS): the 2,082-entry certificate, BFS witnesses, inventories, recurrence (delivered as code/verify.py)
code/07-all-state-independent_check.py Part IV (AS): independent re-enumeration and integer BFS (delivered as code/independent_check.py)
code/07-all-state-Makefile             Part IV (AS): the delivered root Makefile (all/pdf/check/clean)
data/finite_range_bounds.csv           Part I: 372 rows of exact upper and lower values, split, minimizing graph
data/verification_summary.json         Part I: primary check counts and recorded seed
data/independent_bounds_check.json     Part I: independent arithmetic-verifier result
data/small_witnesses.json              Part I: explicit small automata and counts
data/bfs_witnesses.json                Part I: explicit automata and counts
data/cpp_orbit_counts.csv              Part I: C++ BFS results with checksums
data/independent_python_bfs.json       Part I: the separate large-example Python BFS
data/example_certificate.json          Part I: the 8-state, 5-output K(3,5) certificate
data/checks_console.txt                Part I: primary test run output
data/02-three-output-verification.json Part II: recorded run of the verifier (PASS)
data/02-three-output-console.txt       Part II: its console output (byte-identical to the JSON)
data/02-three-output-structural_checks.csv  Part II: n, a, b, defect, maximum, candidates for n = 7..200 (194 rows, CRLF)
data/02-three-output-independent_check.json Part II: recorded independent run (PASS)
data/02-three-output-independent_console.txt Part II: its console output (byte-identical to the JSON)
data/02-three-output-pdf_audit.json    Part II: rendering audit of the delivered (unshipped) 19-page PDF
data/03-eventual-finite_certificates.csv   Part III (01): the 919 certificate rows (CRLF)
data/03-eventual-verification_summary.json Part III (01): producer check counts, BFS states (PASS)
data/03-eventual-verification_console.txt  Part III (01): its console output (byte-identical to the JSON)
data/03-eventual-independent_check.json    Part III (01): checker result, 919 accepted, 0 rejected
data/03-eventual-independent_console.txt   Part III (01): its console output (byte-identical to the JSON)
data/03-eventual-bfs_witnesses.json    Part III (01): the eight explicitly enumerated witnesses
data/03-eventual-recurrences.json      Part III (01): annihilator coefficients for k = 3..10
data/03-eventual-asymptotic_ratios.csv Part III (01): illustrative floating-point ratios, not part of any proof (CRLF)
data/03-eventual-pdf_layout_audit.json Part III (01): rendering audit of the delivered (unshipped) 22-page PDF
data/04-deficit-asymptotics-finite_certificate.json  Part III (03): every candidate record for n = 7..31
data/04-deficit-asymptotics-finite_table.tex  Part III (03): the table input by the article (Table 10)
data/04-deficit-asymptotics-bfs_checks.json   Part III (03): the four BFS sanity checks
data/04-deficit-asymptotics-verification_summary.json  Part III (03): producer summary (PASS)
data/04-deficit-asymptotics-verify_console.txt  Part III (03): producer console
data/04-deficit-asymptotics-optimized_verify_console.txt  Part III (03): the same under python -O (byte-identical)
data/04-deficit-asymptotics-independent_summary.json  Part III (03): independent summary (PASS)
data/04-deficit-asymptotics-independent_console.txt   Part III (03): its console (byte-identical to the JSON)
data/04-deficit-asymptotics-optimized_independent_console.txt  Part III (03): the same under python -O (byte-identical)
data/04-deficit-asymptotics-environment_summary.json  Part III (03): Python/platform/pdfTeX versions
data/04-deficit-asymptotics-pdf_audit.json  Part III (03): rendering audit of the delivered (unshipped) 21-page PDF
data/05-quartic-threshold-finite_k4.csv   Part III (06): per-row target deficit, strict margin, closest excluded case, k = 4 (CRLF)
data/05-quartic-threshold-finite_k5.csv   Part III (06): per-row target deficit, strict margin, closest excluded case, k = 5 (CRLF)
data/05-quartic-threshold-finite_k6.csv   Part III (06): per-row target deficit, strict margin, closest excluded case, k = 6 (CRLF)
data/05-quartic-threshold-finite_k7.csv   Part III (06): per-row target deficit, strict margin, closest excluded case, k = 7 (CRLF)
data/05-quartic-threshold-primary_k4.json  Part III (06): primary summary, k = 4
data/05-quartic-threshold-primary_k5.json  Part III (06): primary summary, k = 5
data/05-quartic-threshold-primary_k6.json  Part III (06): primary summary, k = 6
data/05-quartic-threshold-primary_k7.json  Part III (06): primary summary, k = 7
data/05-quartic-threshold-primary_console.txt  Part III (06): primary console (one JSON line per k)
data/05-quartic-threshold-independent.json    Part III (06): independent summaries
data/05-quartic-threshold-independent_console.txt  Part III (06): its console (one JSON line per k)
data/05-quartic-threshold-supplementary.json  Part III (06): supplementary counts and the non-saturating example
data/05-quartic-threshold-supplementary_console.txt  Part III (06): its console (byte-identical to the JSON)
data/05-quartic-threshold-rank_matching_enumerations.json  Part III (06): the 27 matching-spectrum enumerations
data/05-quartic-threshold-thresholds.json     Part III (06): threshold constants H, M, C, B, L, S, U, N for k = 4..16
data/05-quartic-threshold-sample_values.csv   Part III (06): R_2(n,k) for n = 7..12, k = 4..7 (CRLF)
data/05-quartic-threshold-environment.txt     Part III (06): Python and pdfTeX versions
data/05-quartic-threshold-pdf_audit.json      Part III (06): rendering audit of the delivered (unshipped) 22-page PDF
data/06-four-output-base_certificate.csv  Part IV (FO): the 2,059-entry certificate summary, n = 7..25, with runner-up tags (CRLF)
data/06-four-output-structural_sweep.csv  Part IV (FO): the same fields for n = 7..200 (194 rows, CRLF)
data/06-four-output-verification.json     Part IV (FO): primary run record (PASS)
data/06-four-output-independent_check.json  Part IV (FO): independent run record (PASS)
data/06-four-output-inventory.json        Part IV (FO): orbit inventories and one-edge counts for (a,b) = (3,4), (3,5)
data/06-four-output-recurrence.json       Part IV (FO): recurrence, denominator and numerator coefficients
data/06-four-output-bfs.json              Part IV (FO): C++ BFS counts n = 7..12 and the 212-state example
data/06-four-output-pdf_audit.json        Part IV (FO): rendering audit of the delivered (unshipped) 21-page PDF
data/07-all-state-finite_certificate.json Part IV (AS): all 2,082 certificate entries, n = 4..25
data/07-all-state-finite_summary.csv      Part IV (AS): minima, runner-up values, gaps and maxima, 22 rows (CRLF)
data/07-all-state-bfs_witnesses.json      Part IV (AS): witness arrays n = 4..9, orbit sizes, inventories at n = 7, 8
data/07-all-state-orbit_inventories.json  Part IV (AS): period inventories for n = 7..100
data/07-all-state-recurrence.json         Part IV (AS): denominator, numerator and initial deficits
data/07-all-state-verification_summary.json  Part IV (AS): producer record (PASS)
data/07-all-state-independent_check.json  Part IV (AS): independent record (PASS)
data/07-all-state-PDF_AUDIT.json          Part IV (AS): rendering audit of the delivered (unshipped) 21-page PDF (delivered as notes/PDF_AUDIT.json)
results/certificates.json              Part I: four certificates in the second schema
results/exhaustive.json                Part I: per-row counts, maxima and one maximizer per row for n ≤ 4
results/examples.json                  Part I: the four worked examples
results/sharp_n3_orbit.json            Part I: the 24 (coloring, word) pairs of Appendix C
results/landau_gaps.json               Part I: g(k) and k! − g(k), k = 3..12
results/audit_summary.json, python_audit_log.txt, certificate_check.txt,
  unit_tests.txt, reproduce_log.txt, environment.txt   Part I: audit records and environment
results/pdf_checks.json                Part I: rendering audit of a 19-page predecessor article
```

The prefixed files were staged in the placement commits (`e2b1f016a` for
`02-`, `afb2d1227` for `03-` and `04-`, `eaf787d50` for `05-`, `faef2ed2a` for
`06-` and `07-`), byte-identical to the deliveries. Eleven of them are all-CRLF
CSVs as delivered (written by `csv.writer`): Part II's `structural_checks.csv`,
manuscript 01's `finite_certificates.csv` and `asymptotic_ratios.csv`,
manuscript 06's four `finite_k*.csv` and `sample_values.csv`, FO's
`base_certificate.csv` and `structural_sweep.csv`, and AS's
`finite_summary.csv`; each is protected by a `-text`
line in `SetTheory/Cardinals/.gitattributes`. The manuscripts' delivered
`README.md`, `article.tex` and `article.pdf` are not shipped.

## Build the article

```sh
W=/path/to/scratch
mkdir -p "$W/data" && cp article.tex "$W/" && cp data/04-deficit-asymptotics-finite_table.tex "$W/data/"
cd "$W" && latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex article.tex` three times there. Build in a scratch copy, so
that no auxiliary files land here: Part I's `make pdf` and the `pdf` targets
of the six prefixed Makefiles all run LaTeX on `article.tex` in place (and
`code/03-eventual-Makefile`'s and `code/05-quartic-threshold-Makefile`'s
`clean` targets run `latexmk -c` in place, and
`code/04-deficit-asymptotics-Makefile`'s deletes `article.aux`, `.log`,
`.out`, `.toc`, `.fls` and `.fdb_latexmk` here). The article `\input`s
`data/04-deficit-asymptotics-finite_table.tex`, so that file must sit at that
relative path. Needed packages: newtx, amsmath/amsthm/mathtools, microtype,
geometry, booktabs, array, longtable, enumitem, fancyhdr, tcolorbox, TikZ,
listings, aliascnt, hyperref, cleveref. No bibliography processor, font file
or downloaded paper is needed. The shipped PDF was built with MiKTeX (pdfTeX
1.40.26) with no errors, no warnings, no undefined or multiply defined
references, no duplicate destinations and no overfull or underfull boxes
(as was the build of the committed three-part text). The title page still fits
one page; the dated pointers of Parts III and IV are in the reading-routes box
after the contents instead, because one more line on the title page would push
it onto a second page.

## Rerun the checks

Python 3.10+ (standard library only) for all parts. Do not use `-O` or
`PYTHONOPTIMIZE` for Part I, whose audits use assertions deliberately (Parts
II and III use explicit exceptions).

**Part I.** Its scripts write into `data/` and `results/` and would
**overwrite** the shipped records (on Windows also with CRLF line endings), so
run them on a copy:

```sh
W=/path/to/scratch
mkdir -p "$W/01" && cp -r code data results "$W/01/"
cd "$W/01"
python code/run_checks.py --max-n 30        # rewrites data/finite_range_bounds.csv, small_witnesses.json,
                                            #   example_certificate.json, verification_summary.json
python code/check_bound_certificate.py      # reads the CSV; writes data/independent_bounds_check.json
python code/check_large_example.py          # writes data/independent_python_bfs.json (appreciable memory)
python code/run_experiments.py              # writes results/*.json
python code/certificate_checker.py results/certificates.json   # prints ACCEPTED 4 certificate(s)
python -m unittest discover -s code -p 'test_*.py' -v
c++ -std=c++17 -O2 -Wall -Wextra -pedantic code/orbit_count.cpp -o orbit_count
./orbit_count < code/bfs_cases.txt          # 20 fixtures; largest visits 1,539,561 states
c++ -std=c++17 -O3 -Wall -Wextra -pedantic code/exhaustive.cpp -o exhaustive
./exhaustive 4 > results/exhaustive.json    # 462,066 reduced instances; run before run_experiments.py
```

On Windows PowerShell, `Get-Content -Raw code/bfs_cases.txt | .\orbit_count.exe`.
`run_checks.py` covers 19,683 unreduced `n = k = 3` triples, 161,838 CRT
membership tests, 2,550 fixed-seed random automata (seed 20260920), 1,362
graph-count checks, 46,234 permutation-order checks, the 372 finite bounds and
ten explicit witnesses; `run_experiments.py` covers 4,374 ordered pairs with
all output bijections, 1,000 cyclic-membership cross-checks, 252 relabeling
checks, 2,724 chromatic-formula checks, 330 random reverse-orbit checks,
1,440 larger structural certificates and the six C++ maximizers.
`check_bound_certificate.py` does not import `reversal.py`, and
`certificate_checker.py` does not import `dfao.py`. The main API:

```python
import sys
sys.path.insert(0, "code")
from reversal import missing_coloring, structural_bound, u_witness
p, s, tau = u_witness(3, 5, 5)
print(missing_coloring(p, s, tau, 5)["target"])
print(structural_bound(8, 5)["upper_bound"])  # 369020
```

Transformations are tuples whose `q`-th entry is the image of `q`;
`compose(a,b)` means `a∘b`; a word `ab` in a reverse-orbit record means
`τ∘a∘b` (pull back by `a`, then by `b`).

**Parts II–IV.** Their scripts still use the delivered names. Each takes
its package root as `parents[1]` of its own path. Run in this directory:

- Part II's verifier leaves two stray unprefixed files in `data/`, its
  independent check fails unless the verifier has run there first, and
  `make -f code/02-three-output-Makefile check` runs `python3 code/verify.py`,
  which does not exist here (after its shell redirection has already created an
  empty stray `data/console.txt`).
- Manuscript 01's `03-eventual-verify.py` writes five files into
  `results/` (Part I's directory): `finite_certificates.csv`,
  `bfs_witnesses.json`, `recurrences.json`, `asymptotic_ratios.csv`,
  `verification_summary.json`; its checker reads
  `results/finite_certificates.csv` and writes `results/independent_check.json`.
- Manuscript 03's `04-deficit-asymptotics-verify.py` writes
  `results/finite_certificate.json`, `bfs_checks.json`, `finite_table.tex` and
  **`verification_summary.json`** — the same name as manuscript 01's, so the
  two would overwrite each other; its independent check reads
  `results/finite_certificate.json` and writes `results/independent_summary.json`.
- Manuscript 06's `theorem_checks.py` and `independent_check.py` write
  `finite_k*.csv`, `primary_k*.json`, `thresholds.json` and `independent.json`
  into `results/` by default (`--out` changes it); `supplementary_checks.py`
  does `from theorem_checks import …` and stops with `ModuleNotFoundError`
  under its shipped name.
- Part IV, AS: `07-all-state-verify.py` writes `data/finite_certificate.json`,
  `finite_summary.csv`, `orbit_inventories.json`, `recurrence.json` and
  **`data/bfs_witnesses.json` and `data/verification_summary.json`, which would
  overwrite Part I's shipped files of those names**; `07-all-state-independent_check.py`
  then reads `data/finite_certificate.json` and `data/bfs_witnesses.json` (in
  place, Part I's file) and writes `data/independent_check.json`.
- Part IV, FO: `06-four-output-verify.py` writes `data/base_certificate.csv`,
  `structural_sweep.csv`, `recurrence.json`, `inventory.json` and
  `verification.json` (strays); `06-four-output-independent_check.py` reads
  `data/base_certificate.csv` (a `FileNotFoundError` in place) and writes
  `data/independent_check.json`; the Makefile's `bfs` target writes
  `./witness_bfs` and `data/bfs.json`, and `clean` also removes `code/__pycache__`.
- The six prefixed Makefiles name the delivered scripts (`code/verify.py`,
  `code/independent_check.py`, `code/check_certificates.py`,
  `code/theorem_checks.py`, `code/supplementary_checks.py`,
  `code/witness_bfs.cpp`), which do not exist here; their `pdf` and `clean` targets act on the merged `article.tex` in
  place.

Apart from AS's two files above, no output name collides with a shipped
file, but every output would be a stray. Restore the delivered layouts in scratch copies instead (Git Bash or
another POSIX shell, from this directory):

```sh
W=/path/to/scratch
for P in 02-three-output 03-eventual 04-deficit-asymptotics 05-quartic-threshold 06-four-output 07-all-state; do
  mkdir -p "$W/$P/code" "$W/$P/data" "$W/$P/results"
  for f in code/$P-*.py code/$P-*.cpp; do [ -e "$f" ] && cp "$f" "$W/$P/code/${f#code/$P-}"; done
  cp code/$P-Makefile "$W/$P/Makefile"
done
cd "$W/02-three-output"
py code/verify.py --max-n 200 --bfs-max-n 11 > data/console.txt   # writes data/structural_checks.csv, data/verification.json
py code/independent_check.py > data/independent_console.txt       # writes data/independent_check.json
cd "$W/03-eventual"
py code/verify.py > results/verification_console.txt               # writes results/finite_certificates.csv etc.
py code/check_certificates.py > results/independent_console.txt   # writes results/independent_check.json
cd "$W/04-deficit-asymptotics"
py code/verify.py > results/verify_console.txt                     # writes results/finite_certificate.json etc.
py code/independent_check.py > results/independent_console.txt    # writes results/independent_summary.json
cd "$W/05-quartic-threshold"
py code/theorem_checks.py > results/primary_console.txt            # writes results/finite_k*.csv, primary_k*.json, thresholds.json
py code/independent_check.py > results/independent_console.txt    # writes results/independent.json
py code/supplementary_checks.py > results/supplementary_console.txt  # writes supplementary.json, rank_matching_enumerations.json, sample_values.csv
cd "$W/06-four-output"
py -O code/verify.py                    # writes data/base_certificate.csv, structural_sweep.csv, recurrence.json, inventory.json, verification.json
py -O code/independent_check.py         # writes data/independent_check.json
g++ -O3 -std=c++17 -Wall -Wextra -pedantic code/witness_bfs.cpp -o witness_bfs && ./witness_bfs 12 > data/bfs.json
cd "$W/07-all-state"
py code/verify.py                       # writes data/finite_certificate.json, finite_summary.csv, bfs_witnesses.json, orbit_inventories.json, recurrence.json, verification_summary.json
py code/independent_check.py            # writes data/independent_check.json
```

(In the delivered layouts the `results/` or `data/` names correspond to the
shipped `data/<prefix>-<name>` files; `make check`, `make verify` in a
scratch copy do the same with `python3`.) Part II's run was made on
28 September 2026 (Python 3.14.4, about 3 s): both passed; the CSV is
byte-identical to the shipped one, and the three JSON files and two console
captures equal the shipped ones apart from Windows line endings. It evaluates
752,291 structural candidates over the 194 values `7 ≤ n ≤ 200`, fully explores
the witness orbits for `7 ≤ n ≤ 11` (largest 176,871 states), checks three
orbit inventories and 72 unique-cross-pair colorings; the independent script
checks the closed form for `7 ≤ n ≤ 1000` (994 values) and 982 recurrence
instances.

The three Part III runs were made on 29 September 2026 (Python 3.14.4; about
5 s, 1 s and 30 s): all passed. Every CSV is byte-identical to the shipped
one; every JSON, `.tex` and console record equals the shipped one apart from
Windows line endings, except manuscript 01's `verification_summary.json` and
its console copy, which record the Python version (`3.14.4` instead of the
delivered `3.13.5`). Manuscript 03's delivered records also include runs with
`python -O` (the `optimized_*` consoles), which were not repeated.

The two Part IV runs were made on 29 September 2026 in this way (Python 3.14.4
and the WinLibs `g++`; about 2 s each): all passed. The three CSVs are
byte-identical to the shipped ones; every JSON equals the shipped one apart
from Windows line endings, except FO's `verification.json` and
`independent_check.json`, which record the Python version (`3.14.4` instead of
the delivered `3.13.5`); the C++ output equals `data/06-four-output-bfs.json`
apart from line endings (orbits 15,472 … 16,744,863 for `n = 7..12`, and 212).
AS certifies 2,082 entries for `n = 4..25` and FO 2,059 for `n = 7..25`, with
the 752,291-entry sweep for `n ≤ 200` and 101,568 independently checked
entries for `n ≤ 100`.

## Discrepancies and delivery names

- **Delivery names.** The Part II and Part III scripts, Makefiles and some
  audits use the delivered paths listed above. `data/02-three-output-independent_check.json`
  (and its console copy) says "No imports from verify.py";
  `04-deficit-asymptotics-STATUS.md` says "`independent_check.py` does not
  import `verify.py`"; `data/03-eventual-independent_check.json` records
  `"imports_producer": false`. Each refers to the delivered names of the
  corresponding prefixed files. The article quotes the shipped names.
- **Unshipped PDFs.** `data/02-three-output-pdf_audit.json`,
  `data/03-eventual-pdf_layout_audit.json`,
  `data/04-deficit-asymptotics-pdf_audit.json`,
  `data/05-quartic-threshold-pdf_audit.json`,
  `data/06-four-output-pdf_audit.json` and `data/07-all-state-PDF_AUDIT.json`
  describe the manuscripts' delivered PDFs (19, 22, 21, 22, 21 and 21 pages),
  which are not shipped; so do the sentences of `06-four-output-PROOF_AUDIT.md`
  on the compiled PDF and on limitations "stated in the manuscript and README"
  (FO's delivery README is not shipped). `results/pdf_checks.json` describes a
  19-page predecessor of Part I. `article.pdf` here is a new build of the
  merged text (147 pages).
- **Part IV delivery names.** The two Part IV Makefiles and scripts use the
  delivered names (`code/verify.py`, `code/independent_check.py`,
  `code/witness_bfs.cpp`, `data/…` without prefixes); the docstring of
  `code/06-four-output-independent_check.py` ("does not import verify.py"),
  `data/06-four-output-independent_check.json` (`"imports_primary_checker":
  false`) and `data/07-all-state-independent_check.json`
  (`"no_import_from_producer": true`) refer to the delivered names;
  `07-all-state-PROOF_AUDIT.md`'s "The JSON records in data/" means the shipped
  `data/07-all-state-*.json`. AS's audits were delivered in `notes/`.
- **Duplicates.** Part II's console captures, manuscript 01's two console
  captures, manuscript 03's independent console (and its `-O` copy) and
  manuscript 06's supplementary console are byte-identical to the JSON they
  print; manuscript 03's `optimized_verify_console.txt` equals its
  `verify_console.txt`.
- **Scope of the verifiers' bounds.** `02-three-output-verify.py` uses the
  product bound `J(r)` instead of Part I's exact residual order sets, so its
  "structural" deficits are relaxations of Part I's `D(n,3)` entries; the same
  holds for manuscript 01's certificates (`J(r)`, Part III's Proposition 35.1)
  and manuscript 06's closure (`⌊3^{r/3}⌋`, Section 34), whose two-permutation
  entry is `k^n − k^{n−1}` rather than Part I's multinomial entry. Manuscript
  03's certificate uses Part I's exact order sets. All give the same minima.
- **Stale delivered text.** Part I's `RESEARCH_STATUS.md` ("No proof of the
  exact optimal binary reversal complexity for arbitrary `n,k`") and
  `source_audit.md` describe Part I at its original date; for `k = 3` the
  exact value is proved in Part II and for `k ≥ 4` in Part III's range.
  `03-eventual-SOURCE_AUDIT.md` ("It explicitly leaves unrestricted exact
  optimality unresolved") and `04-deficit-asymptotics-SOURCES.md`/`STATUS.md`
  describe the report at `2cdcd74f3`, before Part II, and manuscript 03
  presents its `k = 3` theorem as new, although it is Part II's Theorem 13.1
  (printed in Part III as a second proof, Section 38). All are kept verbatim.
  The article's own sentences to that effect now carry dated pointers: Part I's
  reading-routes box and Sections 1.4, 10.1, 12.1, 12.2, 12.3, 12.5 (batch 39
  pointers kept), and Part II's Sections 13.3, Remark 18.3, Questions 23.1 and
  23.6 (re-scoped: answered for `k ≤ 7`, eventually for every `k ≥ 4`, open
  for `k ≥ 8` below `N(k)`; the growing-`k` question partly touched), and
  Section 27.5.
- **Stale text of Part IV's sources.** Both manuscripts were pinned before
  Part III was written: FO's `06-four-output-SOURCE_AUDIT.md` lists the exact
  result for `k ≥ 4` as "explicitly left open", and AS's
  `07-all-state-SOURCE_AUDIT.md` repeats the eventual audit's "no established
  explicit fixed-k threshold" and claims the exact four-output optimum as its
  contribution. Part III now proves the four-output formula with an explicit
  threshold, so Part IV prints it as Part III's with the manuscripts' proofs as
  a second route (Section 48.3); the audits are kept verbatim. The small values
  176, 826, 3526 that AS's package reports are Part I's (Section 10.2), with
  identical witness arrays (Appendix A). Part III's text now carries dated
  pointers to Part IV in Section 28.3, Questions 44.2, 44.10 and 44.15 and
  Section 47.6, and Part I's reading-routes box one more.
- **Base of Part III.** The batch-40 placement (`afb2d1227`) named manuscript
  01 as the base of a two-manuscript Part III; batch 41's manuscript 06
  proves more for `k ≥ 4` and is the base of the three-manuscript part, as the
  batch-41 placement (`eaf787d50`) records.
- **Source-table note.** Part I (Section 10.3) corrects Davies's printed
  Table 2 entry for `n = 8, k = 5` from 368020 to 369020; manuscript 01's
  worked example (Example 35.2) reproduces 369020.

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats DFAO reversal, and
the Part III and Part IV manuscripts name no report other than this one, so no
reciprocal note was written. The report sits in the research-report collection of the
`SetTheory/Cardinals` Lean project. That placement confers no formal status:
no Lean or Rocq declaration anywhere in ProveIt formalizes any statement of
Parts I–IV (a search of the tracked `.lean` and `.v` files for DFAOs,
automata with output or Davies finds none). Section 26 records the
formalization plan Part II's manuscript proposes, and Question 44.16 the
Part III manuscripts' proposals (a verified checker for the finite
obligations first), Section 56.6 the Part IV manuscripts' plans (a verified
partition and divisor enumerator for the 2,082 inequalities, with the
Holzer–König theorem as an explicit hypothesis); none has been started.

## Sources and attribution

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
Automata with Output*, arXiv:1705.07150v2 (17 October 2017): Proposition 4,
Theorem 3 and Corollary 3, Section 3 (the monoid `U_{a,b}` and its
generators), Tables 2–3, Section 5 Problems 1–2.
https://arxiv.org/abs/1705.07150

Markus Holzer and Barbara König, *On deterministic finite automata and
syntactic monoid size*, Theoretical Computer Science 327(3), 319–347 (2004),
https://doi.org/10.1016/j.tcs.2004.04.010 — background, Theorem 13 (the
`k = n` bound), the graph-coloring method, and Theorem 8 (two-generation of
`U_{a,b}`, imported in Part III's Section 30 in the form quoted by Davies).

B. Krawetz, *Monoids and the State Complexity of the Operation root(L)*,
Master's thesis, University of Waterloo, 2003 — cited for the attribution of
the `U_{a,b}` generator through Davies's account; not read in full.

Marc Deléglise and Jean-Louis Nicolas, *The Landau Function and the Riemann
Hypothesis*, arXiv:1907.07664 — cited only for the name of `g(k)`.

No third-party paper PDFs or font files are included.
