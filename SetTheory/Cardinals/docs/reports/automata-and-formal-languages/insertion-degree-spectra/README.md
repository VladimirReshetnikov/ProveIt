# Gaps in Bounded-Shuffle Hierarchies

**Counterexamples, arbitrary finite spectra, and a no-gap theorem for iteration depth; with arbitrary binary spectra from a single unary word, and sharp isolation thresholds for binary insertion**

This is a research report in three parts. Part I is the original report of
20 September 2026, which refutes the insertion-degree No-Gap Conjecture of
Hughes (arXiv:2608.27755v1, Section 11). Part II was added on
29 September 2026 in batch 41 of ProveIt's incoming-report intake, from a
later manuscript that answers the question Part I left open in its
Section 10: which finite spectra can be realized over one fixed binary
alphabet. Part III was added on 30 September 2026 in batch 66, from a
manuscript that answers Part II's Question 21.3 (the exact minimum lengths
of an isolated full-coverage witness for `m = 3, 4, 5`) and, for the centers
and the mandatory targets, its Question 21.4. All three sources are
AI-assisted research manuscripts prepared for Vladimir Reshetnikov; the
title-page wording of the two additions (which names the assistant, ChatGPT)
is recorded as provenance in Sections 11.1 and 25.1 of the article.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection package *Gaps in Bounded-Shuffle Hierarchies: Counterexamples, arbitrary finite spectra, and a no-gap theorem for iteration depth*, 20 Sep 2026 (delivered as `shuffle-spectra`) | not committed as an archive (Cardinals-era delivery) | (none) | sorted in `8374aaa79` (Cardinals repository), in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 6–17), Appendices A–B (pp. 61–63) |
| 02 | batch 41, manuscript 01 (*Binary Insertion Spectra from a Single Unary Word: Arbitrary finite profiles and a sharp quadratic witness bound*, 28 Sep 2026, 18-page PDF as delivered) | `ProveIt_Binary_Insertion_Spectra.zip` (inner directory of the same name, main file `article.tex`), arrived in `9754e8360` | `e2b1f016a` | `eaf787d50` (prefix `02-binary-profiles-`) | Part II: Sections 11–24 (pp. 18–37) |
| 03 | batch 66, manuscript 04 (*Sharp Isolation Thresholds for Binary Insertion: Exact parameter ranges, extremal centers, mandatory targets, and a complete degree-three classification*, 30 Sep 2026, 21-page US-letter PDF as delivered) | `ProveIt_Sharp_Insertion_Isolation.zip` (inner directory of the same name, main file `article.tex`), arrived in `9ad899cbe` | `176e31c5c` | `4fee1cd07` (prefix `03-sharp-isolation-`) | Part III: Sections 25–40 (pp. 38–61) |

The pin `e2b1f016a` is ProveIt commit
`e2b1f016a94102663f12b970e6dd434229f90d01`. At that pin, Part I's
`article.tex` had blob `946173d8…` and its `README.md` blob `59bfcb36…`;
both were unchanged at the batch-41 placement commit, so every statement
manuscript 01 makes about Part I, and about "the README", refers to the text
printed in Part I and to an earlier version of this file (it survives in
history). The manuscript's `article.tex`, `article.pdf`, delivery `README.md`
and `SHA256SUMS.txt` (11/11 entries verified at placement) are not shipped;
they survive in the arrival commit. Part II prints every result, proof,
example, remark, limitation and question of the manuscript. The definitions
it repeats from Part I (insertion, degree, spectrum, the run
characterization) are printed once, in Part I, and credited in Section 11.6;
Section 24.3 of the article lists where the merge had to choose.

The pin `176e31c5c` is ProveIt commit
`176e31c5c7ee369edf51edd815463dc029e3faed`. At that pin this report's
`article.tex` had blob `7f5a958e7ac6d6df902d4efa40cfefa813bb20db` and its
`README.md` blob `bca8c085…`; both were unchanged at the placement commit
`4fee1cd07`, so every statement manuscript 04 makes about "the repository
report" (its Theorem 12.3, Section 16, Questions 21.1, 21.3, 21.4, 21.6)
refers to Parts I and II as printed and to the previous version of this
file. Part II's numbering did not change, so those numbers are still the
article's. The manuscript's `article.tex`, `article.pdf` and delivery
`README.md` are not shipped and survive in the arrival commit; the archive
had no checksum file. Part III prints every result, proof, example, remark,
table, limitation and question of the manuscript. What it repeats from
Parts I and II is credited in Section 25.8: the insertion definitions are
recalled from Part I; Part II's gap-degree lemma keeps its statement and is
proved once, in Part II; Part II's volume bound is restated with a new
support bound and the manuscript's proof kept as a marked second route; the
`m²` length for `m ≥ 6` and the 46-target worked example are Part II's.
Section 40.3 lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing in any part is formalized in
Lean, Rocq or any other proof assistant, and no source claims otherwise; the
repository has no formal development of insertion degrees. The report sits in
a collection beside Lean and Rocq projects, which confers no formal status on
it. The finite computations are exact checks of stated finite ranges and
implementations, and samples where so labelled; the all-parameter statements
rest on the written proofs.

## Results

Notation: for languages `A` (inserted source) and `B` (target source),
`I_k(A,B)` splits one word of `A` into at most `k` pieces (empty pieces
allowed) and inserts them, in order, into one word of `B`; the degree
`d_{A,B}(w)` is the least such `k`, and the spectrum `D(A,B)` is the set of
degrees attained (Part I, Section 2; the orientation of Hughes, Sections 2
and 11).

**Part I** (unchanged apart from dated pointers):

1. A ternary pair with spectrum `{1,3}`: `I_1 = I_2 = {a,b,c}^5 \ {abcba}`,
   `I_3 = {a,b,c}^5` (Theorem 3.1). Five is the least length of any gap
   witness (Corollary 3.2).
2. A one-word delay `{1,r}` for every `r ≥ 2` (Theorem 4.2), hence no fixed
   plateau test is sound (Corollary 4.3).
3. Every nonempty finite list of degrees ≥ 2 is realized by distinct
   exceptional outputs over a finite alphabet that grows with the list
   (Theorem 5.1); so the spectra of pairs of nonempty finite languages are
   exactly the finite sets containing 1 (Corollary 5.2). Explicit regular
   expressions, grammars and automata (Section 6).
4. A binary pair with spectrum `{1,2,4}` whose 18 singleton source-pair
   spectra are all initial intervals: source-pair ambiguity can erase a whole
   degree (Theorem 7.1, Appendix A), answering Hughes's finite
   representation-erasure problem; two letters is the least alphabet admitting
   any gap (Corollary 7.2).
5. The iteration-depth spectrum is an initial interval for arbitrary
   languages (Theorem 8.2, via the shortest-prefix Lemma 8.1).

**Part II** (manuscript 01 of batch 41; unchanged apart from dated pointers),
over the alphabet `{a,b}` with `A = {a^m}`:

1. **Arbitrary binary profiles** (Theorem 12.1): for every `m ≥ 2` and every
   nonempty list `t_0,…,t_{q−1}` in `{2,…,m}` there is a finite target
   language `B` whose shuffle with `a^m` is a whole fixed-letter-count class,
   in which exactly the designated outputs `W_i` have degree `t_i` and every
   other output has degree 1. Each `W_i` has a unique target word; uniqueness
   of its position mask is not claimed.
2. **Fixed-binary classification** (Corollary 12.2): the spectra of pairs of
   nonempty finite binary languages are exactly the finite subsets of the
   positive integers containing 1, each attained with a single unary inserted
   word. This settles the Part I passage (Section 10) saying the report "does
   not establish which finite spectra can all be realized over one fixed
   binary alphabet", and answers its least-alphabet question for `{1,r}`: two
   letters, for every `r ≥ 2`.
3. **Sharp length in the full-coverage class** (Theorem 12.3): if
   `A = {a^m}`, `A ⧢ B` is an entire binary fixed-letter-count class, exactly
   one output has degree > 1 and its degree is `m ≥ 3`, then the output length
   is at least `m²`; equality is attained for every `m ≥ 6`. **This bound
   assumes full coverage (and the single unary inserted word); it is not a
   lower bound for binary spectra in general, where the elementary bound is
   `2m − 1`.**
4. Exact sizes (Proposition 15.2), arbitrary higher-degree multiplicities
   (Corollary 15.3), a succinct membership test and certified degree
   computation (Section 19), a 14-symbol worked example with `|B| = 46`
   (Theorem 17.1), and the contrast between identical real-rooted singleton
   histograms (Theorem 18.3) and aggregate degree polynomials with almost all
   zeros nonreal (Section 18.2).

Added in the batch-41 merge (not stated by manuscript 01): Remark 11.1
compares the two realizations (growing alphabet at length `2m − 1` against
the binary alphabet at length `m²` in the full-coverage class; the `{1,2,4}`
example against Part II's list `(2,4)`, which uses one inserted word and
2,570 target words of outputs of length 30), and the merge notes of
Sections 19.3 and 20.

**Part III** (manuscript 04 of batch 66), in Part II's full-coverage class:
`A = {a^m}`, a finite binary target language whose shuffle with `a^m` is the
whole class of words with `T` letters `a` and `g − 1` letters `b`, exactly
one output (the *center*, gap vector `v`) of degree `m` and every other output
of degree 1:

1. **Largest admissible language** (Lemma 27.2, Corollary 27.3): every
   realizing target set lies in one explicit maximal set and must contain a
   special target; this characterizes all realizing languages by finite
   covering constraints.
2. **Complete center criterion** (Theorem 29.1): for `m ≥ 3`, `v` is feasible
   exactly when its support has at least `m` coordinates, `T > g(m−1)`, and,
   with heights `h_i = (v_i − m + 1)_+`, `H = Σ h_i` and `ĥ = max h_i`, either
   `H − ĥ ≥ m + 1` (the strict case, Part II's escape condition) or
   `H − ĥ = m` with height multiset `{ĥ, 1^m}` (a boundary family outside
   Part II's criterion; Proposition 32.1 gives its sharp cost
   `N ≥ m² + 2m`). The test takes `O(g)` arithmetic operations.
3. **All feasible parameters** (Lemma 30.1, Theorem 30.2): for `m ≥ 3`, a
   realization with `g` gaps and `T` letters `a` exists exactly when `g ≥ m`
   and `T ≥ max(g(m−1)+1, τ_m)`, with `τ_3 = 12` and `τ_m = 5m − 2` for
   `m ≥ 4`.
4. **Exact minimum lengths** (Theorem 30.3): `3, 14, 21, 27` for
   `m = 2, 3, 4, 5`, and `m²` for `m ≥ 6` (Part II's value); every shortest
   realization has `g = m`. This answers Question 21.3 completely: the upper
   bounds 14, 21, 27 of Part II are optimal, and more gaps never help.
5. **Extremal centers** (Theorems 31.1, 31.2): the centers at the least
   length are exactly the positive `m`-tuples of total `m² − m + 1` (for
   `m ≥ 6`) with `H − ĥ ≥ m + 1`; up to permutation `(4,4,4)` for `m = 3`,
   `(8,8,1,1)`, `(6,6,5,1)` for `m = 4`, `(10,10,1,1,1)`, `(7,7,7,1,1)` for
   `m = 5`, and 19 orbits for `m = 6`. A finite binomial formula counts the
   ordered centers (1, 18, 20, 2,220, 677,985, … for `m = 3, …, 7`; Table 3).
6. **Mandatory targets** (Proposition 33.1, Theorem 33.2): an explicit test
   for every target that must occur in every realizing language
   (Table 4: 28, 263, 257, 3,080, 3,066 for the five small center types).
   Items 5 and 6 answer Question 21.4 for centers and mandatory targets.
7. **Complete degree-three classification** (Theorem 34.1): at the least
   length for `m = 3`, every realizing language is the 28 mandatory targets
   plus a nonempty choice from each of nine disjoint pairs; there are
   `3^9 = 19,683` languages, with size polynomial `z^37 (2+z)^9`, so the
   minimum size is 37, attained by `2^9 = 512` of them.
8. A residue-class decomposition of the remaining covering problem
   (Proposition 35.1) and a counting lower bound for target sets
   (Corollary 35.2), ten research questions (Section 38), the executed
   checks (Section 36, Table 6) and a proof audit (Section 37).

## Not claimed

- The unrestricted singleton (both-singleton) insertion-degree conjecture,
  Hughes's Conjecture 2, is not resolved by any part (Questions 21.1, 38.8).
  Part I's arbitrary-spectrum construction uses many source words; Parts II
  and III use one inserted word but many target words.
- No classification of infinite spectra over a fixed finite alphabet
  (Question 21.9).
- No minimality of language sizes in general: Part I claims none for its
  `19`/`9`, `6`/`3` or constructed languages; Part II's inserted language
  (one word) is optimal, but the minimum target-language size is open
  (Question 21.2), and the degree-one multiplicity is not independently
  prescribed. Part III determines the minimum target size (37) only for
  `m = 3` at the least length in the full-coverage class; not for `m ≥ 4`
  (Question 38.1), not at longer lengths (Question 38.2), and not without
  full coverage. Its maximal-language sizes (Table 4) are not minima.
- Part II's `m²` bound holds only in its full-coverage class. Part III
  settles the exact optimal lengths for `m = 3, 4, 5` (14, 21, 27) and
  classifies the centers and mandatory targets at equality, in that class
  only; no length bound without full coverage (Questions 21.6 and 38.6).
  Full coverage, the unary inserted word and a unique exception of maximum
  degree are essential to every Part III theorem.
- No minimal grammar, automaton or DFA-state claims in any part
  (Question 21.7), and no class of controlled representations restoring an
  interval theorem (Question 21.8).
- No novelty for Hughes's Theorem 9 (the unary-source singleton interval
  theorem), which Part II reproves and credits, nor priority for the
  real-rootedness of the singleton histogram polynomial. Part III's novelty
  claim is relative to Part II as pinned. All three literature checks were
  targeted (20, 28 and 30 September 2026), not exhaustive priority searches.
- No claim that the finite checks prove the all-parameter theorems. Part II's
  `m ≤ 80` output tests are seeded samples (seed 20260928), not exhaustive;
  Part III's larger-dimension deficit suite is a seeded sample (seed
  20260930), and its parameter-construction suite checks finitely many
  inputs of a proved theorem.
- The Z3 discovery searches of Part I support no claim; the solver is not
  needed for any verification.

## Labels

Part I's 29 labels are bare (`sec:`, `eq:`, `lem:`, `prop:`, `thm:`, `cor:`,
`app:`). Part II's 87 labels carry the prefix `ids:bp:` ("insertion-degree
spectra, binary profiles"). Part III added **104** labels, all with the prefix
`ids:si:` ("insertion-degree spectra, sharp isolation"): the manuscript's 80
labels (its `eq:insertion` collided with Part I's), ten for its questions, and
14 for the sections and the notation table added in the merge. Total: 220. No
label was renamed or removed, and no existing label changed its number
(compared in the `.aux` files of the committed and the new build; page numbers
moved because the contents grew by a page). Part III starts at Section 25,
after Part II's Section 24; its equations continue the single equation
sequence (from (46)), and its tables are Tables 2–6. Part I's appendices come
after Part III and contain no numbered equations, tables, figures or
theorem-like items. Part III added two macros to the preamble (`\Adm`,
`\bpSpecial`); no existing macro changed.

## Notation

Part I's symbols keep their meanings. Table 1 (Section 11.5) lists Part II's
symbols and Table 2 (Section 25.7) Part III's; watch in particular for:

- `A`, `B`, `m`, `q`, `t_i`, `W_i` have the same roles as in Part I's
  Theorem 5.1, but name different languages and words (Part II indexes the
  list from 0).
- `N` is an output length in all parts, of different constructions:
  `2m − 1` in Part I, `T + g − 1` in Parts II and III.
- `m²` in Theorems 12.3 and 30.3 is a minimum in the full-coverage class, not
  a lower bound for every word of degree `m`.
- Renamed in Part II from manuscript 01, because Part I already uses the
  letter: `d → g` (number of gaps; `d_{A,B}` is the degree), `w(c) → ω(c)`
  (gap-vector word), `E, E_safe → 𝓔, 𝓔_safe` (Part I's `E` is the set of bad
  pairs), `E_m → η_m`, `D → Λ` (Part I's `D(i,j,s)` and `𝒟(A,B)`),
  `R_j → ρ_j`, `Q_i → Box_i`, `K_m → κ_m`, `J_n → Φ_n` (Part I's `J_{m,t}`),
  `F_{A,B} → Deg_{A,B}` (Part I's `F` of forbidden triples), `M → μ`,
  `Q → p` (test polynomial).
- Renamed in Part III from manuscript 04: `E → 𝓔` (as in Part II), `M → ĥ`
  (maximum height; Part I's `M`, Part II's `μ`), `H_j → ρ_j` (**the same
  quantity** as Part II's escape sum `ρ_j(v)`), `Q(c) → P^adm_m(c)` (Part I's
  `Q`), `K(β) → Hi(β)` (Part I's `K`, Part II's `κ_m`), `K → ν` (quotient
  total of a residue class), `C(n,r,b) → Comp(n,r,b)` (Part II's `𝒞_{T,g}`).
  The manuscript's `𝒞(T,g)`, `𝒲(T,g)` and `I_k(A,B)` are printed as Part II's
  `𝒞_{T,g}`, `𝒲_{T,g}` and Part I's `𝓘_k(A,B)`; Part III's `h_i`, `H` are
  heights, not Part II's `h_{m,g,r}`, `H_m(z)`.
- No normalization changed in either addition. Both manuscripts numbered
  equations within sections; the report numbers them in one sequence, so
  every equation and theorem number differs from the delivered PDFs.

## Files

```
article.tex                                   the report, standalone LaTeX with an internal bibliography
article.pdf                                   the compiled report, 63 US-letter pages (title page p. 1, contents pp. 2–5,
                                              Part I pp. 6–17, Part II pp. 18–37, Part III pp. 38–61,
                                              Part I's appendices pp. 61–63, bibliography p. 63)
README.md                                     this guide
SOURCES.md                                    Part I: primary sources and literature-search boundary (20 Sep 2026)
02-binary-profiles-CLAIMS_AND_VALIDATION.md   Part II: claim and validation boundaries (delivered as CLAIMS_AND_VALIDATION.md)
02-binary-profiles-SOURCES.md                 Part II: repository snapshot, primary source, search boundary (delivered as SOURCES.md)
03-sharp-isolation-PROOF_AUDIT.md             Part III: logical chain, scope checks, finite-check boundary (delivered as PROOF_AUDIT.md)
03-sharp-isolation-SOURCE_AUDIT.md            Part III: pin, attribution, primary source, search boundary (delivered as SOURCE_AUDIT.md)
tex/binary_pairs.tex                          Part I: per-source-pair degree table included in Appendix A
tex/binary_erasure.tex                        Part I: the 23 competing low-cost certificates included in Appendix A
code/verify.py                                Part I: exact verifier (mask exhaustion vs. dynamic program), stdlib only
code/make_search.py                           Part I: generator of the optional SMT-LIB discovery instances
code/02-binary-profiles-verify.py             Part II: exact verifier and construction routines, stdlib only (delivered as code/verify.py)
code/02-binary-profiles-Makefile              Part II: the delivered root Makefile (all/verify/clean; see below)
code/03-sharp-isolation-isolation.py          Part III: classifier, maximal targets, counting formulas, literal masks (delivered as code/isolation.py)
code/03-sharp-isolation-verify.py             Part III: audit driver and data exporter, stdlib only (delivered as code/verify.py)
code/03-sharp-isolation-Makefile              Part III: the delivered root Makefile (pdf/verify/clean; see below)
data/verification.json                        Part I: recorded checks and sample sizes
data/verification_run.txt                     Part I: console copy of the same report (byte-identical to the JSON)
data/ternary_degrees.csv                      Part I: all 243 ternary output words, degrees and optimal masks
data/ternary_pairs.csv                        Part I: degree histograms of the 171 ternary source pairs
data/binary_degrees.csv                       Part I: the 111 binary shuffle words, degrees and optimal masks
data/binary_pairs.csv                         Part I: degree histograms of the 18 binary source pairs
data/binary_erasure.csv                       Part I: the 23 competing low-cost certificates
data/search_binary.smt2                       Part I: free SMT-LIB search for a binary counterexample
data/search_binary.solver.txt                 Part I: recorded solver output (sat and a model)
data/binary_fixed_model.smt2                  Part I: SMT-LIB instance pinning the six-word/three-word pair
data/binary_fixed_model.solver.txt            Part I: recorded solver output (sat and a model)
data/02-binary-profiles-verification.json     Part II: executed receipt, Python 3.13.5 (delivered as data/verification.json)
data/02-binary-profiles-profile_checks.csv    Part II: the 26 exhaustively checked profiles (26 rows, CRLF)
data/02-binary-profiles-worked_targets.csv    Part II: the 46 target words of the worked example (46 rows, CRLF)
data/02-binary-profiles-worked_outputs.csv    Part II: its 91 output words and their degrees (91 rows, CRLF)
data/03-sharp-isolation-verification.json     Part III: executed receipt, Python 3.13.5, status PASS (delivered as data/verification.json)
data/03-sharp-isolation-verification_run.txt  Part III: console output of that run
data/03-sharp-isolation-extremal_center_counts.csv     Part III: ordered-center counts for m = 2..12 (11 rows, CRLF)
data/03-sharp-isolation-extremal_orbits_m3_m6.json     Part III: all extremal center orbits for m = 3..6 (1, 2, 2, 19)
data/03-sharp-isolation-complete_examples.csv          Part III: the 8 completely checked centers (5 extremal, 3 boundary; 8 rows, CRLF)
data/03-sharp-isolation-degree3_pair_constraints.json  Part III: the nine degree-three pair constraints
data/03-sharp-isolation-minimal_degree3_targets.csv    Part III: a minimum 37-word target language (37 rows, CRLF)
data/03-sharp-isolation-provenance.json       Part III: delivery record (pin, report blob, questions answered)
data/03-sharp-isolation-build_status.json     Part III: build record of the delivered 21-page PDF, not of this report
```

The three Part II CSV files and the three Part III CSV files have CRLF line
endings as delivered; they keep their bytes through `-text` lines in
`SetTheory/Cardinals/.gitattributes`. Every Part II and Part III file is
byte-identical to the delivered file.

## Relation to other work in ProveIt

- Part III continues Part II directly: it answers Questions 21.3 and (for
  centers and mandatory targets) 21.4, gives a restricted answer to
  Question 21.2, and restates Questions 21.1 and 21.6 as its Questions 38.8
  and 38.6. Dated notes in Sections 11.4, 16 and 21 of Part II, and in the
  front matter and Appendix B, point to it.
- The sibling report
  `SetTheory/Cardinals/docs/reports/automata-and-formal-languages/constrained-crossover-closure`
  concerns constrained crossover (front-matter note of batch 44); it uses
  nothing proved here. A dated note of batch 66 after Corollary 4.3 (no fixed
  plateau test), which extends that front-matter note, summarizes its
  Parts II–III (commit `202aafd08`): PSPACE-complete finite stabilization for
  NFA seeds, PSPACE for DFA seeds, a quadratic rank bound, decidable
  regularity of the full closure of context-free seeds, and a classification
  of finitely stabilizing sparse one-marker seeds. None of it concerns
  insertion degrees.
- The neighbouring report
  `SetTheory/Cardinals/docs/reports/automata-and-formal-languages/shuffle-six-state-bound`
  concerns the state complexity of the shuffle operation (the six-state
  bound), not insertion degrees; it shares no theorem with this report.
- No Lean or Rocq development in ProveIt formalizes insertion degrees,
  shuffle spectra or anything proved here. Part II's Question 21.10 and
  Part III's Question 38.10 sketch where a formal development could start;
  nothing of it exists.

## Building

From this directory (pdfLaTeX; newtx, amsthm, shuffle, microtype, booktabs,
enumitem, listings, fancyhdr, hyperref; no BibTeX step):

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy (with `tex/`) to keep auxiliary files out of the
repository. The committed PDF was built this way with MiKTeX on
30 September 2026: 0 errors, 0 warnings, 0 undefined references, 0
multiply-defined labels, 0 duplicate destinations, no overfull or underfull
boxes. Do not use `code/02-binary-profiles-Makefile` or
`code/03-sharp-isolation-Makefile` for this (see below).

## Rerunning the checks

All three verifiers need only the Python standard library (Part I:
Python 3.9+; Parts II and III: Python 3.10+) and **all three write into this
report's `data/` by default**, where they would overwrite Part I's
`data/verification.json`. Never run them in place.

```text
py code/verify.py --out <scratch>/part1
py code/02-binary-profiles-verify.py --out <scratch>/part2
```

Part III's verifier also imports its companion module under the delivered
name `isolation`, so it fails under its prefixed name; run it on a copy with
the delivered names:

```text
mkdir -p <scratch>/part3/code
cp code/03-sharp-isolation-isolation.py <scratch>/part3/code/isolation.py
cp code/03-sharp-isolation-verify.py    <scratch>/part3/code/verify.py
cd <scratch>/part3
py code/verify.py --output-dir audit-output
```

- Part I writes `verification.json`, `ternary_degrees.csv`,
  `ternary_pairs.csv`, `binary_degrees.csv`, `binary_pairs.csv` and
  `binary_erasure.csv`; compare them with the shipped files of the same
  names. It does not regenerate `data/verification_run.txt` or `tex/`.
- Part II writes `verification.json`, `profile_checks.csv`,
  `worked_targets.csv` and `worked_outputs.csv` — its delivered names;
  compare them with the shipped `data/02-binary-profiles-*` files. **Run
  without `--out`, it would overwrite Part I's `data/verification.json`** and
  add three unprefixed CSV files. It prints each profile as it passes (about
  10 seconds). On Windows the JSON is written with CRLF line endings; compare
  it parsed, and expect `python_version` to differ.
- Part III writes `verification.json`, `extremal_orbits_m3_m6.json`,
  `degree3_pair_constraints.json`, `extremal_center_counts.csv`,
  `complete_examples.csv` and `minimal_degree3_targets.csv` — its delivered
  names; compare them with the shipped `data/03-sharp-isolation-*` files. It
  prints the console record (shipped as
  `data/03-sharp-isolation-verification_run.txt`) but does not write it, and
  it does not regenerate `provenance.json` or `build_status.json`. Its default
  output directory is the `data/` next to its `code/` directory, so even the
  copy above writes into `<scratch>/part3/data` unless `--output-dir` is
  given. On Windows the JSON files are written with CRLF line endings.
- In the batch-41 write phase (29 September 2026) Part II's suite was rerun
  this way on a copy with Python 3.14.4: it passed, its three CSV files were
  byte-identical to the shipped ones, and its JSON equal to the shipped one in
  every field except `python_version`.
- During the batch-66 placement checks (30 September 2026) Part III's suite
  was rerun this way on a copy with Python 3.14.4: it passed in about seven
  seconds; its three CSV files were byte-identical to the shipped ones, its
  two other JSON files equal apart from line endings, and its
  `verification.json` equal apart from line endings and `python` (3.14.4
  instead of 3.13.5). Part I's suite was not rerun for either addition.
- Part I's optional discovery search needs an SMT solver such as Z3:
  `z3 data/search_binary.smt2` and `z3 data/binary_fixed_model.smt2` should
  both report `sat` (the free search may find a different counterexample).
  `code/make_search.py` also writes into `data/` by default; pass `--out`.

## Delivered text that uses delivery names

Delivered files are shipped byte-identical, so their text still speaks of the
delivered package:

- `code/02-binary-profiles-Makefile`: `verify` runs `python code/verify.py`,
  which here is **Part I's** verifier, not Part II's; `all` and `clean` run
  `latexmk` on `article.tex`, which here is the merged report. It is shipped
  for provenance; do not run it from this directory.
- `code/03-sharp-isolation-Makefile`: likewise, `verify` runs
  `python3 code/verify.py --output-dir audit-output`, which here is **Part I's**
  verifier, which has no `--output-dir` option and stops with a usage error;
  `pdf` runs
  `pdflatex` on the merged `article.tex` into `build/`; `clean` removes
  `build` and `audit-output`. Shipped for provenance; do not run it here.
- `code/02-binary-profiles-verify.py`: its default `--out` is this report's
  `data/`, and it writes the unprefixed delivery names (above).
- `code/03-sharp-isolation-verify.py`: imports `isolation` (the delivered
  name of `code/03-sharp-isolation-isolation.py`), defaults to this report's
  `data/`, and writes the unprefixed delivery names; its docstring says "Run
  from any directory", which is true only of the delivered layout.
- `02-binary-profiles-CLAIMS_AND_VALIDATION.md` calls the receipt
  `data/verification.json`; in this report that name is Part I's receipt, and
  Part II's is `data/02-binary-profiles-verification.json`. Its closing "No
  repository files were modified and no pull request was submitted" describes
  the delivery, not the write phase. Its item 3 says "Exact optimal lengths
  for m = 3,4,5 are not claimed": true of Part II, and now settled by
  Part III (Theorem 30.3).
- `02-binary-profiles-SOURCES.md` describes Part I at the pin (its
  `article.tex`, "Its README", the report manifest) and "this archive"; the
  README it read is an earlier version of this file.
- `03-sharp-isolation-PROOF_AUDIT.md` calls `data/verification.json` "the
  authoritative executed receipt"; in this report that name is Part I's
  receipt, and Part III's is `data/03-sharp-isolation-verification.json`.
- `03-sharp-isolation-SOURCE_AUDIT.md` cites line ranges (990–1230,
  1400–1545, 1790–1950) of `article.tex` at the pin (blob `7f5a958e`); the
  preamble macros and dated notes added in the batch-66 write phase move
  those lines down by 13 to 42.
  It speaks of "the paper" and "this package", and its closing "this package
  does not create a commit, pull request, issue, or persistent Library
  upload" describes the delivery.
- `data/03-sharp-isolation-provenance.json` (`"pdf_pages": 21`) and
  `data/03-sharp-isolation-build_status.json` (21 pages, PyMuPDF rendering)
  describe the delivered PDF, which is not shipped; the report's PDF is
  described above. `data/03-sharp-isolation-verification_run.txt` ends with
  the delivery path `/mnt/data/ProveIt_Sharp_Insertion_Isolation/data`.
- Part I's own text (Appendix B, `SOURCES.md`) speaks of "the archive" and
  "this archive" for Part I's delivered package, whose files are the
  unprefixed files here. Appendix B carries dated pointers to Part II's and
  Part III's files.
- The delivered articles and READMEs of Parts II and III cite
  `code/verify.py`, `data/profile_checks.csv`, `code/isolation.py`,
  `data/minimal_degree3_targets.csv` and the like; in the report
  (Sections 24.1 and 40.1 map every delivered name to its shipped path)
  those names are replaced.

## Other discrepancies

- The delivered PDF of manuscript 01 was A4; the report is US letter, in
  Part I's layout, so page and equation numbers differ from the delivered
  PDF. Manuscript 04's PDF was US letter (21 pages) but numbered equations
  within sections; the report's numbers differ from it too.
- Manuscript 01's bibliography entry for Part I (the pinned GitHub URL of
  `article.tex`) is replaced by internal references to Part I, and its entry
  for Hughes's preprint by Part I's entry (the same arXiv version, v1); the
  page reference "Theorem 9 on page 9" is kept in the text (Section 11.3).
  Manuscript 04's entries are replaced the same way (its entry for the pinned
  report by internal references to Part II, its entry for Hughes by Part I's).
- Manuscript 04's preamble redefined `\supp`, which this report declares as
  an operator (a fatal "already defined" error in a merged build), and its
  `\word`, which here prints typewriter words; Part III uses the report's
  `\supp` and Part II's `\bpgap` (same printed output). It used `cleveref`,
  `tcolorbox`, `xurl` and per-section equation numbers, none of which the
  report loads: its references are plain `\ref`s, its two boxed statements
  are plain text, and its equations join the report's single sequence.
- The delivered PDF of manuscript 04 contains one Type 3 font (`F142`); it
  is not shipped. The report's PDF was built from source.
- Manuscript 04's line-broken "unique-predecessor" in its conclusion printed
  as "unique- predecessor"; Part III prints it unbroken.
