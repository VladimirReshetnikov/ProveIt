# Gaps in Bounded-Shuffle Hierarchies

**Counterexamples, arbitrary finite spectra, and a no-gap theorem for iteration depth; with arbitrary binary spectra from a single unary word**

This is a research report in two parts. Part I is the original report of
20 September 2026, which refutes the insertion-degree No-Gap Conjecture of
Hughes (arXiv:2608.27755v1, Section 11). Part II was added on
29 September 2026 in batch 41 of ProveIt's incoming-report intake, from a
later manuscript that answers the question Part I left open in its
Section 10: which finite spectra can be realized over one fixed binary
alphabet. Both sources were prepared for Vladimir Reshetnikov and are
AI-assisted (Part II's author line: "prepared with ChatGPT").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection package *Gaps in Bounded-Shuffle Hierarchies: Counterexamples, arbitrary finite spectra, and a no-gap theorem for iteration depth*, 20 Sep 2026 (delivered as `shuffle-spectra`) | not committed as an archive (Cardinals-era delivery) | (none) | sorted in `8374aaa79` (Cardinals repository), in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 5–16), Appendices A–B (pp. 36–38) |
| 02 | batch 41, manuscript 01 (*Binary Insertion Spectra from a Single Unary Word: Arbitrary finite profiles and a sharp quadratic witness bound*, 28 Sep 2026, 18-page PDF as delivered) | `ProveIt_Binary_Insertion_Spectra.zip` (inner directory of the same name, main file `article.tex`), arrived in `9754e8360` | `e2b1f016a` | `eaf787d50` (prefix `02-binary-profiles-`) | Part II: Sections 11–24 (pp. 17–36) |

The pin `e2b1f016a` is ProveIt commit
`e2b1f016a94102663f12b970e6dd434229f90d01`. At the pin, Part I's
`article.tex` had blob `946173d8…` and its `README.md` blob `59bfcb36…`;
both were unchanged at the placement commit, so every statement manuscript 01
makes about Part I, and about "the README", refers to the text printed in
Part I and to the previous version of this file (now replaced; it survives in
history). The manuscript's `article.tex`, `article.pdf`, delivery `README.md`
and `SHA256SUMS.txt` (11/11 entries verified at placement) are not shipped;
they survive in the arrival commit. Part II prints every result, proof,
example, remark, limitation and question of the manuscript. The definitions
it repeats from Part I (insertion, degree, spectrum, the run
characterization) are printed once, in Part I, and credited in Section 11.6;
Section 24.3 of the article lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing in either part is
formalized in Lean, Rocq or any other proof assistant, and no source claims
otherwise; the repository has no formal development of insertion degrees.
The report sits in a collection beside Lean and Rocq projects, which confers
no formal status on it. The finite computations are exact checks of stated
finite ranges and implementations, and samples where so labelled; the
all-parameter statements rest on the written proofs.

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

**Part II** (manuscript 01), over the alphabet `{a,b}` with `A = {a^m}`:

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

Added in the merge (not stated by the manuscript): Remark 11.1 compares the
two realizations (growing alphabet at length `2m − 1` against the binary
alphabet at length `m²` in the full-coverage class; the `{1,2,4}` example
against Part II's list `(2,4)`, which uses one inserted word and 2,570 target
words of outputs of length 30), and the merge notes of Sections 19.3 and 20.

## Not claimed

- The unrestricted singleton (both-singleton) insertion-degree conjecture,
  Hughes's Conjecture 2, is not resolved by either part (Question 21.1).
  Part I's arbitrary-spectrum construction uses many source words; Part II's
  uses one inserted word but many target words.
- No classification of infinite spectra over a fixed finite alphabet
  (Question 21.9).
- No minimality of language sizes: Part I claims none for its `19`/`9`,
  `6`/`3` or constructed languages; Part II's inserted language (one word) is
  optimal, but the minimum target-language size is open (Question 21.2), and
  the degree-one multiplicity is not independently prescribed.
- Part II's `m²` bound only in its full-coverage class; exact optimal lengths
  for `m = 3, 4, 5` are not claimed (proved lower bounds 9, 16, 25; upper
  bounds 14, 21, 27; Question 21.3); no classification of the equality cases
  (Question 21.4); no length bound without full coverage (Question 21.6).
- No minimal grammar, automaton or DFA-state claims in either part
  (Question 21.7), and no class of controlled representations restoring an
  interval theorem (Question 21.8).
- No novelty for Hughes's Theorem 9 (the unary-source singleton interval
  theorem), which Part II reproves and credits, nor priority for the
  real-rootedness of the singleton histogram polynomial. Both literature
  checks were targeted (20 and 28 September 2026), not exhaustive priority
  searches.
- No claim that the finite checks prove the all-parameter theorems. Part II's
  `m ≤ 80` output tests are seeded samples (seed 20260928), not exhaustive.
- The Z3 discovery searches of Part I support no claim; the solver is not
  needed for any verification.

## Labels

Part I's 29 labels are bare (`sec:`, `eq:`, `lem:`, `prop:`, `thm:`, `cor:`,
`app:`) and are unchanged, with unchanged numbers (compared in the `.aux`
files of the committed and the new build). Part II added **87** labels, all
with the prefix `ids:bp:` ("insertion-degree spectra, binary profiles").
Total: 116. No label was renamed or removed. Part II starts at Section 11,
after Part I's Section 10; its equations continue Part I's single equation
sequence (from (11)), and its one numbered table is Table 1. Part I's
appendices come after Part II and contain no numbered equations, tables,
figures or theorem-like items. The preamble gained a `question` environment
on the shared theorem counter and five `\bp…` macros; no existing macro
changed.

## Notation

Part I's symbols keep their meanings. Table 1 (Section 11.5) lists Part II's
symbols; watch in particular for:

- `A`, `B`, `m`, `q`, `t_i`, `W_i` have the same roles as in Part I's
  Theorem 5.1, but name different languages and words (Part II indexes the
  list from 0).
- `N` is an output length in both parts, of different constructions:
  `2m − 1` in Part I, `T + g − 1` in Part II.
- `m²` in Theorem 12.3 is a minimum in the full-coverage class, not a lower
  bound for every word of degree `m`.
- Renamed from the manuscript, because Part I already uses the letter: `d →
  g` (number of gaps; `d_{A,B}` is the degree), `w(c) → ω(c)` (gap-vector
  word), `E, E_safe → 𝓔, 𝓔_safe` (Part I's `E` is the set of bad pairs),
  `E_m → η_m`, `D → Λ` (Part I's `D(i,j,s)` and `𝒟(A,B)`), `R_j → ρ_j`,
  `Q_i → Box_i`, `K_m → κ_m`, `J_n → Φ_n` (Part I's `J_{m,t}`),
  `F_{A,B} → Deg_{A,B}` (Part I's `F` of forbidden triples), `M → μ`,
  `Q → p` (test polynomial). No normalization changed. The manuscript
  numbered equations within sections; the report numbers them in one
  sequence, so every equation and theorem number differs from the delivered
  PDF.

## Files

```
article.tex                                   the report, standalone LaTeX with an internal bibliography
article.pdf                                   the compiled report, 38 US-letter pages (title page p. 1, contents pp. 2–4,
                                              Part I pp. 5–16, Part II pp. 17–36, Part I's appendices pp. 36–38,
                                              bibliography p. 38)
README.md                                     this guide
SOURCES.md                                    Part I: primary sources and literature-search boundary (20 Sep 2026)
02-binary-profiles-CLAIMS_AND_VALIDATION.md   Part II: claim and validation boundaries (delivered as CLAIMS_AND_VALIDATION.md)
02-binary-profiles-SOURCES.md                 Part II: repository snapshot, primary source, search boundary (delivered as SOURCES.md)
tex/binary_pairs.tex                          Part I: per-source-pair degree table included in Appendix A
tex/binary_erasure.tex                        Part I: the 23 competing low-cost certificates included in Appendix A
code/verify.py                                Part I: exact verifier (mask exhaustion vs. dynamic program), stdlib only
code/make_search.py                           Part I: generator of the optional SMT-LIB discovery instances
code/02-binary-profiles-verify.py             Part II: exact verifier and construction routines, stdlib only (delivered as code/verify.py)
code/02-binary-profiles-Makefile              Part II: the delivered root Makefile (all/verify/clean; see below)
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
```

The three Part II CSV files have CRLF line endings as delivered; they keep
their bytes through `-text` lines in `SetTheory/Cardinals/.gitattributes`.
Every Part II file is byte-identical to the delivered file.

## Relation to other work in ProveIt

- The neighbouring report
  `SetTheory/Cardinals/docs/reports/automata-and-formal-languages/shuffle-six-state-bound`
  concerns the state complexity of the shuffle operation (the six-state
  bound), not insertion degrees; it shares no theorem with this report.
- No Lean or Rocq development in ProveIt formalizes insertion degrees,
  shuffle spectra or anything proved here. Part II's Question 21.10 sketches
  where a Lean development could start; nothing of it exists.

## Building

From this directory (pdfLaTeX; newtx, amsthm, shuffle, microtype, booktabs,
enumitem, listings, fancyhdr, hyperref; no BibTeX step):

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy (with `tex/`) to keep auxiliary files out of the
repository. The committed PDF was built this way with MiKTeX: 0 errors,
0 warnings, 0 undefined references, no overfull boxes. Do not use
`code/02-binary-profiles-Makefile` for this (see below).

## Rerunning the checks

Both verifiers need only the Python standard library (Part I: Python 3.9+;
Part II: Python 3.10+) and **both write into this report's `data/` by
default**. Run them with an explicit output directory outside the
repository, never in place:

```text
py code/verify.py --out <scratch>/part1
py code/02-binary-profiles-verify.py --out <scratch>/part2
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
- In the write phase (29 September 2026) Part II's suite was rerun this way
  on a copy with Python 3.14.4: it passed, its three CSV files were
  byte-identical to the shipped ones, and its JSON equal to the shipped one in
  every field except `python_version`. Part I's suite was not rerun for this
  addition.
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
- `code/02-binary-profiles-verify.py`: its default `--out` is this report's
  `data/`, and it writes the unprefixed delivery names (above).
- `02-binary-profiles-CLAIMS_AND_VALIDATION.md` calls the receipt
  `data/verification.json`; in this report that name is Part I's receipt, and
  Part II's is `data/02-binary-profiles-verification.json`. Its closing "No
  repository files were modified and no pull request was submitted" describes
  the delivery, not the write phase.
- `02-binary-profiles-SOURCES.md` describes Part I at the pin (its
  `article.tex`, "Its README", the report manifest) and "this archive"; the
  README it read is the previous version of this file.
- Part I's own text (Appendix B, `SOURCES.md`) speaks of "the archive" and
  "this archive" for Part I's delivered package, whose files are the
  unprefixed files here. Appendix B carries a dated pointer to Part II's files.
- Part II's delivered article and README cite `code/verify.py`,
  `data/profile_checks.csv` and the like; in the report (Section 24.1 maps
  every delivered name to its shipped path) those names are replaced.

## Other discrepancies

- The delivered PDF of manuscript 01 was A4; the report is US letter, in
  Part I's layout, so page and equation numbers differ from the delivered
  PDF.
- Manuscript 01's bibliography entry for Part I (the pinned GitHub URL of
  `article.tex`) is replaced by internal references to Part I, and its entry
  for Hughes's preprint by Part I's entry (the same arXiv version, v1); the
  page reference "Theorem 9 on page 9" is kept in the text (Section 11.3).
