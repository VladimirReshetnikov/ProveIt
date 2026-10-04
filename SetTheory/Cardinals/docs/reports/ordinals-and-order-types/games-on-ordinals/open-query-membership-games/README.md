# Open-query games on ordinal spaces

**An explicit negative answer to the topological-sum problem, with a finite Cantor–Bendixson classification; its extension to finite output alphabets: sharp synchronization and a complexity dichotomy; and filter profiles: an exact classification for finite derived sets, ultrafilter thresholds and a three-color separation; and closure-word duality: universal finite models, optimal topological compression, finite-budget certificates and an exact product law; and universal word profiles on scattered spaces: a finite-height attainment theorem, countable extremal witnesses and an inverse theory of query spectra**

This is a research report in five parts. Part I is the original report of
19 September 2026. Part II was added on 29 September 2026 in batch 52 of
ProveIt's incoming-report intake, from a later manuscript that replaces
Part I's membership bit by one of `q` output labels. Part III was added on
29 September 2026 in batch 56, from a manuscript that answers Part II's
Research question 1 for spaces with a finite nonempty derived set. Part IV
was added on 30 September 2026 in batch 65, from a manuscript that answers
the fixed-coloring half of that question on every topological space. Part V
was added on 30 September 2026 in batch 68, from a manuscript that answers
Part III's Research question 12 in the affirmative at every finite height,
and with it the attainment half of Part II's Research question 1 on locally
compact and sequential spaces. All five are AI-assisted; the manuscripts of
Parts II–V were "prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Open-query games on ordinal spaces: a negative solution to the topological-sum problem, with an exact Cantor–Bendixson classification*) | `ordinal_membership_games.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–13 (pp. 6–20) and Appendices A–B (pp. 124–125) |
| 02 | batch 52, manuscript 12 (*Finite-Output Open-Query Games: Sharp Synchronization and a Complexity Dichotomy*, 29 Sep 2026, 22-page US Letter PDF as delivered) | `ProveIt_Finite_Output_Open_Query_Games.zip` (inner `finite_output_open_query_games/`, main file `article.tex`), arrived in `11e1e9001` | `5c695cfdf` | `a701d9098` (prefix `02-finite-output-`) | Part II: Sections 14–28 (pp. 21–45) and Appendix C (p. 125) |
| 03 | batch 56, manuscript 05 (*Filter Profiles and Open-Query Complexity: Exact finite-derivative classification, ultrafilter thresholds, and a three-color separation*, 29 Sep 2026, 20-page US Letter PDF as delivered) | `ProveIt_Filter_Profiles_Open_Query_Complexity.zip` (inner `proveit_filter_games/`, main file `article.tex`), arrived in `e47ed8547` | `2d4919838` (blob `75f0c4d7` of this `article.tex`, Parts I–II) | `ae718a441` (prefix `03-filter-profiles-`) | Part III: Sections 29–42 (pp. 46–70) and Appendix D (pp. 125–126) |
| 04 | batch 65, manuscript 05 (*Closure-Word Duality for Open-Query Games: Universal finite models, optimal topological compression, finite-budget certificates, and an exact product law*, 30 Sep 2026, 25-page US Letter PDF as delivered) | `ProveIt_Closure_Word_Duality.zip` (inner `ProveIt_Closure_Word_Duality/`, main file `article.tex`), arrived in `529a082b9` | `a4268e78e` (blob `d1e50fd0` of this `article.tex`, Parts I–III) | `3fd85006b` (prefix `04-closure-words-`) | Part IV: Sections 43–58 (pp. 71–97) and Appendices E–F (pp. 126–128) |
| 05 | batch 68, manuscript 02 (*Universal Word Profiles on Scattered Spaces: A finite-height attainment theorem, countable extremal witnesses, and an inverse theory of query spectra*, 30 Sep 2026, 23-page US Letter PDF as delivered) | `ProveIt_Universal_Word_Profiles.zip` (inner `proveit_universal_word_profiles/`, main file `article.tex`), arrived in `a866ff9a2` | `781594d88` (blob `d1e50fd0` of this `article.tex`, Parts I–III) | `29e52fcdf` (prefix `05-word-profiles-`) | Part V: Sections 59–72 (pp. 98–123) and Appendices G–H (pp. 128–129) |

The pin `5c695cfdf` is ProveIt commit
`5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864`. At that commit Part I's
`article.tex` was the blob `5e5ed2a806…` and this README the blob
`a8e024d1e3…`; both were unchanged at the placement commit, so every
statement of Part II about "the ProveIt report" refers to Part I as printed
here. (Its source audit, `02-finite-output-SOURCES.md`, says it read that
README and lines 1–160 of the article.) The manuscript, its PDF and its
delivery README are not shipped; they survive in the arrival commit. Part II
prints every result, proof, example, remark, limitation and question of the
manuscript, and its title block, abstract and status paragraph (Section 14.2).
Section 14.1 lists where the merge had to choose; Section 14.3 is the
notation table; Section 14.4 checks Part II against Part I at `q = 2`.

The pin `2d4919838` is ProveIt commit
`2d49198382cc068f46747d1b3d9067d47cee4f24`, which is later than Part II's
write (`f11edd3c5`). At that commit this `article.tex` was the blob
`75f0c4d7ba…` (Parts I–II, including the batch-52 note under Research
question 1) and this README the blob `3357ea6820…` (the manuscript records
the article blob only); both were unchanged at the placement commit. The
manuscript read them through the GitHub connector
(`03-filter-profiles-SOURCES.md`), so its "Part II, Section 27, Research
question 1" is Section 27 and Research question 1 here. Its manuscript, PDF,
delivery README and checksum ledger (`SHA256SUMS`, 12 entries under the
delivery names, verified 12/12 at intake and retired) are not shipped; they
survive in the arrival commit. Part III prints every result, proof, example,
remark, limitation and question of the manuscript, and its title block,
abstract and status paragraph (Section 29.2). Section 29.1 lists where the
merge had to choose; Section 29.3 is the notation table; Section 29.4 checks
Part III against Parts I and II.

The pin `a4268e78e` is ProveIt commit
`a4268e78ebd0f6bf71ba609c07f4b3415748f532`, which is later than Part III's
write (`f8a20bcb1`). At that commit this `article.tex` was the blob
`d1e50fd006…` (Parts I–III with the notes of batches 52 and 56), which the
manuscript records, and this README the blob `465cb1e062…`; both were
unchanged at the placement commit. The manuscript read them through the
GitHub connector (`04-closure-words-SOURCES.md`), so its "Part II, Theorem
16.2 and Proposition 16.3" are Theorem 16.2 and Proposition 16.3 here and
its "Research question 1 in Part II" is Research question 1. Its manuscript,
PDF and delivery README are not shipped; they survive in the arrival commit
(the archive had no checksum ledger). Part IV prints every result, proof,
example, remark, limitation and question of the manuscript, and its title
block, abstract and status paragraph (Section 43.2). Section 43.1 lists where
the merge had to choose; Section 43.3 is the notation table; Section 43.4
checks Part IV against Parts I–III.

The pin `781594d88` is ProveIt commit
`781594d886f8dc56069221e2b56bd1e94d9c6e5f` ("Write batch 63 (2/3) …"),
which is later than Part III's write but earlier than Part IV's placement
(`3fd85006b`) and write (`674300897`). At that commit this `article.tex` was
the blob `d1e50fd006…` (Parts I–III with the notes of batches 52 and 56) and
this README the blob `465cb1e062…`, the same blobs Part IV's manuscript read;
the manuscript records both, and they were unchanged until Part IV's write.
So Part V's manuscript did not see Part IV, and its "Part II, Theorem 16.2",
"Theorem 19.1", "Theorem 20.1", "Section 24", "Part III, Theorem 35.1" and
"Research questions 11 and 12" are those numbers here. It read the article
and the README through the GitHub connector (`05-word-profiles-SOURCES.md`).
Its manuscript, PDF and delivery README are not shipped; they survive in the
arrival commit, and its checksum ledger (`SHA256SUMS`, 13 entries, verified
13/13 at intake) was retired. Part V prints every result, example, remark,
limitation and question of the manuscript, its title block, abstract and
research-status box (Section 59.2), and every proof except two: its proofs of
the tree–layer normal form and of the restricted-start word constant are
step for step Part II's proofs of Theorems 16.2 and 19.1, so the statements
are printed with their labels and the proofs point to Part II. Section 59.1
lists where the merge had to choose; Section 59.3 is the notation table;
Section 59.4 checks Part V against Parts I–IV, including the routes through
Part IV that the manuscript could not cite.

**Status.** AI-assisted and unrefereed. Nothing in any part is formalized in
Lean, Rocq or any other proof assistant, and no source claims otherwise.
Part II's NP-completeness theorem imports the modified-SCS hardness theorem
of Lagoutte and Tavenas (arXiv:1309.0422, Corollary 6) as an external input;
Part III's NP-completeness proposition imports the NP-completeness of
directed feedback vertex set (Göke–Marx–Mnich, arXiv:2003.02483). Part III
uses free ultrafilters, whose existence is a theorem of ZFC. Part IV imports
no theorem; it cites the Lagoutte–Tavenas hardness only to delimit its
algorithmic claims. Part V imports no theorem either; its arguments are in
ZFC with choices of points and sequences, no ultrafilter existence principle
and no continuum hypothesis. The finite computations check finite posets,
finite topologies, finite graphs, finite word families and integer
arithmetic only; every infinite-space statement rests on the written proofs.

## Files

```
article.tex                                    the report, standalone LaTeX with an internal bibliography
article.pdf                                    the compiled report, 131 pages, US Letter (unnumbered title
                                               page, contents pages 1–5, Part I pp. 6–20, Part II
                                               pp. 21–45, Part III pp. 46–70, Part IV pp. 71–97,
                                               Part V pp. 98–123, appendices pp. 124–129,
                                               references pp. 129–130)
README.md                                      this guide
RESEARCH_STATUS.md                             Part I's scope, source identification and limitations, as delivered
Makefile                                       Part I's build and verification targets, as delivered (see below)
code/verify.py                                 Part I's verifier: standard library, minimax, closure
                                               profiles, alternating chains, strategy synthesis
data/verification.json                         Part I's recorded run through six points
data/verification.log                          its console output
data/finite_poset_checks.csv                   posets and targets checked at each size
data/ordinal_values.csv                        exact formula values for last derivative ranks 0–128
data/sharp_family.csv                          sharp duplication examples for levels 1–16
data/strategy_certificate.json                 an optimal three-query tree for two oppositely colored
                                               four-element chains
02-finite-output-RESEARCH_STATUS.md            Part II's claim boundaries, as delivered
02-finite-output-SOURCES.md                    Part II's source audit, as delivered
code/02-finite-output-verify.py                Part II's verifier: standard library, exact minimax,
                                               ideal-state search, chain words, greedy feasibility,
                                               closure elimination, constructions
code/02-finite-output-Makefile                 Part II's delivered Makefile (do not use here; see below)
data/02-finite-output-verification.json        Part II's recorded run (--max-n 5 --brute-n 4)
data/02-finite-output-verification.log         its console output
data/02-finite-output-poset_counts.csv         enumeration counts (CRLF, as delivered)
data/02-finite-output-sharp_families.csv       universal-family examples (CRLF, as delivered)
data/02-finite-output-restricted_start_families.csv  restricted-start examples (CRLF, as delivered)
data/02-finite-output-strategy_certificate.json      an optimal three-question strategy on the
                                               twelve-point six-chain ternary example
data/02-finite-output-pdf_build.log            the pdfTeX log of the delivered 22-page PDF (not shipped)
03-filter-profiles-SOURCES.md                  Part III's source audit and novelty boundary, as delivered
code/03-filter-profiles-verify.py              Part III's verifier: standard library, digraphs against
                                               reduced-word search, positive-cell and capacity checks,
                                               extremal thresholds, strategy certificates
code/03-filter-profiles-Makefile               Part III's delivered Makefile (do not use here; see below)
data/03-filter-profiles-verification.json      Part III's recorded run (default --max-q 4)
data/03-filter-profiles-verification.log       its console output (the same JSON)
data/03-filter-profiles-capacity_checks.json   the 98 capacity-attainment cases
data/03-filter-profiles-strategy_certificates.json   optimal words and balanced suffix-query trees
                                               for the two three-color examples
data/03-filter-profiles-extremal_thresholds.csv      least arc counts T(q,r) and equality-graph
                                               counts for q ≤ 4 (CRLF, as delivered)
data/03-filter-profiles-query_jump_thresholds.csv    first component counts forcing an extra
                                               question, q = 2–64 (CRLF, as delivered)
04-closure-words-SOURCES.md                    Part IV's source audit, pin and novelty boundary, as delivered
code/04-closure-words-verify.py                Part IV's verifier: standard library, all labelled topologies
                                               on ≤ 4 points with their three-colorings, minimax against
                                               closure signatures, products, digraphs, universal words
code/04-closure-words-Makefile                 Part IV's delivered Makefile (do not use here; see below)
data/04-closure-words-verification.json        Part IV's recorded run (default --max-n 4 --q 3)
data/04-closure-words-validation.json          the delivered build and package record (digests of the
                                               delivered manuscript, PDF and verifier)
05-word-profiles-SOURCES.md                    Part V's source audit, pin and claim boundaries, as delivered
code/05-word-profiles-verify.py                Part V's verifier: standard library, universal-word search
                                               against the envelope test, finite-forest minimax,
                                               threshold and spectrum-equivalence arithmetic
code/05-word-profiles-Makefile                 Part V's delivered Makefile (do not use here; see below)
data/05-word-profiles-verification.json        Part V's recorded run (no options)
data/05-word-profiles-verification.log         its console output (the same bytes as the JSON)
data/05-word-profiles-certificate.json         the word 01201 for q = 3, h = 2, S = {0}: embeddings,
                                               envelope positions and a balanced suffix-query tree
data/05-word-profiles-depth_aliases.json       depth-spectrum alias classes through normalized height 16
data/05-word-profiles-universal_words.csv      the 36 tested (q, h, s) triples (CRLF, as delivered)
data/05-word-profiles-finite_forests.csv       the 23 finite-forest minimax cases (CRLF, as delivered)
data/05-word-profiles-sample_spectra.csv       layer and depth values for 196 sample (h, t, q)
                                               (CRLF, as delivered)
```

Every file other than `article.tex`, `article.pdf` and this README is
byte-identical to its delivery. Part II's delivery was laid out as
`code/verify.py`, `results/X`, `Makefile`, `RESEARCH_STATUS.md` and
`SOURCES.md`; the mapping is `code/verify.py` →
`code/02-finite-output-verify.py`, `results/X` → `data/02-finite-output-X`,
and the other three → the `02-finite-output-` names above. Part III's
delivery was laid out as `code/verify.py`, `results/X`, `Makefile` and
`SOURCES.md`; the mapping is `code/verify.py` →
`code/03-filter-profiles-verify.py`, `results/X` →
`data/03-filter-profiles-X`, `Makefile` → `code/03-filter-profiles-Makefile`
and `SOURCES.md` → `03-filter-profiles-SOURCES.md`. Part IV's delivery was
laid out as `code/verify.py`, `results/X`, `Makefile` and `SOURCES.md`; the
mapping is `code/verify.py` → `code/04-closure-words-verify.py`, `results/X`
→ `data/04-closure-words-X`, `Makefile` → `code/04-closure-words-Makefile`
and `SOURCES.md` → `04-closure-words-SOURCES.md`; none of its files has CR
bytes. Part V's delivery was laid out as `code/verify.py`, `results/X`,
`Makefile` and `SOURCES.md` (with `article.tex`, `article.pdf`, `README.md`
and `SHA256SUMS`, not shipped); the mapping is `code/verify.py` →
`code/05-word-profiles-verify.py`, `results/X` → `data/05-word-profiles-X`,
`Makefile` → `code/05-word-profiles-Makefile` and `SOURCES.md` →
`05-word-profiles-SOURCES.md`. The eight CSV files of Parts II, III and V
were delivered with CRLF line endings and are kept byte for byte by `-text`
lines in `SetTheory/Cardinals/.gitattributes`; no other file of Part V has
CR bytes. The `.log` files of Parts II, III and V (their three verification
logs and Part II's PDF build log) were added past the repository's `*.log`
ignore rule.

## Labels and numbering

Part I's 54 labels are bare (`thm:height`, `eq:question`, …) and unchanged;
none was renamed or removed, and a comparison of the `.aux` files of this
build and of a build of the committed Part I text shows every Part I number
unchanged. Every label of Part II carries the prefix `fo:` (finite output):
the manuscript's 57 labels keep their names after the prefix, and the write
added seven (`fo:sec:provenance`, `fo:sec:source`, `fo:sec:abstract`,
`fo:sec:notation`, `fo:sec:crosswalk`, `fo:sec:three-colors`,
`fo:app:certificates`), 118 labels in all. The manuscript's Section *n* is
Section *n* + 14 here and every numbered statement and equation keeps its
position (its Theorem 2.2 is Theorem 16.2); this was checked label by label
against a build of the delivered text. Its Research questions 1–10 keep their
numbers, and its Appendix A is Appendix C, after Part I's appendices.
(Corrected 29 September 2026, batch 56: this sentence and Section 14.1 said
"1–9" when Part II was written in; Part II prints ten research questions, as
did its delivered manuscript.)
Text added at the write is marked **[Added 29 September 2026, batch 52]**:
five notes in Part I (Section 1, after Remark 4.4, after Corollary 8.2, after
the example of Section 11, in Section 12), a paragraph of the abstract and one
of the title page, and in Part II Section 14 and seven notes (Sections 15, 20,
22, 25, 26, 27, Appendix C).

Every label of Part III carries the prefix `fp:` (filter profiles): the
manuscript's 46 labels keep their names after the prefix (the prefix also
removes two collisions, `sec:normal` and `thm:normal`, with Part I), and the
write added sixteen: `fp:sec:provenance`, `fp:sec:source`,
`fp:sec:abstract`, `fp:sec:notation`, `fp:sec:crosswalk`,
`fp:sec:conclusion`, `fp:app:certificates` and the nine research-question
labels `fp:q:next-level` … `fp:q:choice`. Part II's Research question 1
gained the label `fo:q:invariants`, which prints nothing. The report now has
181 labels (118 before). The manuscript's Section *n* is Section *n* + 29 here
and its Appendix A is Appendix D; every theorem keeps its position (its
Theorem 4.4 is Theorem 33.4), and its equations, numbered (1)–(14)
consecutively in the manuscript, are numbered within sections here (its
equation (2) is (30.2)). Its Research questions 1–9 are Research questions
11–19, because the counter continues after Part II's ten. All of this was
checked label by label against a build of the delivered text, and a
comparison of the `.aux` files of this build and of a build of the committed
Parts I–II text shows every number of the 118 earlier labels unchanged (only
page numbers moved). Text added at this write is marked **[Added 29 September
2026, batch 56]**: in Part II, notes after Research question 1, after the
remark following Theorem 20.3 and after the proof of Theorem 22.4, and a note
in Section 14.1 correcting its count of research questions (with the two
corrected sentences); a paragraph of the abstract and one of the title page;
and in Part III, Section 29 and five notes (Sections 30, 39 twice, 40,
Appendix D).

Every label of Part IV carries the prefix `cw:` (closure words): the
manuscript's 76 labels keep their names after the prefix (the prefix also
removes three collisions with Part I, `sec:height`, `sec:normal` and
`thm:normal`), and the write added fifteen: `cw:sec:provenance`,
`cw:sec:source`, `cw:sec:abstract`, `cw:sec:notation`, `cw:sec:crosswalk`,
`cw:sec:conclusion` and the nine research-question labels
`cw:q:fixed-space` … `cw:q:formal`. The report now has 272 labels (181
before: 54 bare, 65 `fo:`, 62 `fp:`, 91 `cw:`). The manuscript's Section *n*
is Section *n* + 43 here and its Appendices A–B are Appendices E–F; every
theorem and equation keeps its position (its Theorem 4.2 is Theorem 47.2, its
equation (10.3) is (53.3)), and its Research questions 1–9 are Research
questions 20–28. All of this was checked label by label against a build of
the delivered text, and a comparison of the `.aux` files of this build and
of a build of the committed Parts I–III text shows every number and every
cross-reference type of the 181 earlier labels unchanged (only page numbers
moved). Text added at this write is marked **[Added 30 September 2026,
batch 65]**: in Part II, notes after Research questions 1, 3 and 6; in
Part III, notes after Research questions 11 and 14; a paragraph of the
abstract and one of the title page; a dated sentence on the two titles in
the Chiozini–Csernák–Soukup bibliography entry; and in Part IV, Section 43
and four notes (Sections 44, 53, 56, 57). The sentences recording how
Part IV's manuscript cites that entry and the Lagoutte–Tavenas and Selivanov
entries are undated, as Part III's were.

Every label of Part V carries the prefix `uw:` (universal words): the
manuscript's 71 labels keep their names after the prefix (the prefix also
removes five collisions with Part I, `cor:product`, `eq:normal`,
`eq:product-derivative`, `sec:normal` and `thm:normal`), and the write added
fourteen: `uw:sec:provenance`, `uw:sec:source`, `uw:sec:abstract`,
`uw:sec:notation`, `uw:sec:crosswalk`, `uw:sec:conclusion` and the eight
research-question labels `uw:q:necessary` … `uw:q:beyond`. The report now
has 357 labels (272 before: 54 bare, 65 `fo:`, 62 `fp:`, 91 `cw:` and now
85 `uw:`); none was renamed or removed. The manuscript's Section *n* is
Section *n* + 59 here and its Appendices A–B are Appendices G–H; every
theorem, equation and figure keeps its position (its Theorem 6.1 is Theorem
65.1, its equation (6.2) is (65.2), its Figure 1 is Figure 1), and its eight
research questions are Research questions 29–36. All of this was checked
label by label against a build of the delivered text (71 of 71 numbers and
cross-reference types as expected), and a comparison of the `.aux` files of
this build and of a build of the committed Parts I–IV text shows every
number and every cross-reference type of the 272 earlier labels unchanged
(only page numbers moved). Text added at this write is marked **[Added 30
September 2026, batch 68]**: in Part II, a note after Research question 1;
in Part III, notes after Research questions 11, 12, 14 and 18; in Part IV,
notes after the scope note of Section 44 and after Research question 20; a
paragraph of the abstract and one of the title page (whose vertical spacing
was tightened so that it stays one page; no text changed); and in Part V,
Section 59 and eight notes (Sections 60, 62, 66, 68, 69, 70, 71 and
Appendix H). The sentences recording how Part V's manuscript cites the
Chiozini–Csernák–Soukup and Borlido–Gehrke–Krebs–Straubing entries are
undated, as before. The preamble gained the note environment of this write,
the macro `\nextpos`, and `\usepackage{tikz}` (already loaded by
`tcolorbox`) with `\usetikzlibrary{arrows.meta}` for Part V's one figure.

## Results

**Part I.** The selected question is Problem 1.3 of Chiozini, Csernák and
Soukup, arXiv:2510.05754v3: is the set-membership number of a topological sum
the supremum of the component values? No: two copies of `[0, ω]` each have
value 1, and their sum has value 2. More generally, for every nonempty
Hausdorff space of finite Cantor–Bendixson height, with `h` the index of the
last nonempty derivative, the value is `ceil(log2(h+1))` when that derivative
is a singleton and `ceil(log2(h+2))` otherwise. The report proves this through
a finite normal form (depth = `ceil(log2 L)` for the least number `L` of
alternating closed layers) and canonical oriented closure profiles; it
derives sharp one-extra-move examples `K_k = [0, ω^(2^k − 1)]` at every level,
product and bounded-height sum formulae, an `ω` upper bound for sums of finite
values, the value `ω` on countable scattered spaces of infinite height, and a
quadratic-time alternating-chain formula on finite posets.

**Part II.** A coloring `c : X → Σ` with `q` labels is to be determined by
open questions.

- *Normal form* (Theorem 16.2): the least number of ordered layers with open
  suffixes, `L(X, c)`, equals the least number of nonempty leaves of a correct
  tree, and the optimal depth is `ceil(log2 L(X, c))`; a fixed-word closure
  test (Proposition 16.3).
- *Posets* (Theorem 17.1): `L` is the shortest common supersequence length of
  the reduced color words of chains; a linear-time least-map feasibility test.
- *Compact realization* (Theorem 18.2): an iterated convergent-sequence tower
  `𝖪_m` (the manuscript's `K_m`) realizes every reduced word with exactly its
  supersequence profile; every finite colored poset has a compact countable
  metrizable model.
- *Universal words* (Theorem 19.1): reduced words of length `m` with first
  letter in an `s`-set need exactly `s + (q−1)(m−1)` letters.
- *Cantor–Bendixson* (Theorem 20.1): `L ≤ (q−1)h + s`, sharp, where `s` is the
  number of colors on the last derivative; *towers* (Theorem 20.3): the worst
  case over `q`-colorings of `t` towers of rank `m − 1` is
  `ceil(log2((q−1)(m−1) + min(q, t)))`.
- *Sums* (Theorems 21.2, 21.3): components with at most `m` layers need at most
  `(q−1)m + 1` jointly, sharply; the exact extra cost is `ceil(log2 q)`
  questions, attained by fixed colorings of compact countable metrizable
  spaces. Six two-point chains `01, 02, 10, 12, 20, 21` go from one question
  each to three jointly (Section 21.1).
- *Complexity* (Proposition 22.1, Theorem 22.4): polynomial for two labels;
  NP-complete for three, even on disjoint chains and on succinct tower lists,
  with an exact common-prefix padding to power-of-two budgets.
- *Algorithms* (Theorem 23.1, Proposition 23.2): a cyclic algorithm within
  `ceil(log2(q−1))` questions of optimal (one for three labels, optimal in the
  integer-additive sense unless P = NP); exact search on order ideals.
- *Obstructions* (Theorem 24.1): a failed `m`-layer budget has a witness of at
  most `(m+1)q^m` points; exact optimization is fixed-parameter tractable in
  the joint parameters `(q, d)`.
- Ten research questions (Section 27). (Corrected 29 September 2026, batch
  56: this line said "Nine" when Part II was written in.)

**At `q = 2` Part II reproduces Part I** (Section 14.4, checked at the write):
its normal form and closure test are Part I's Theorems 4.2 and 5.2; its binary
chain formula is Part I's Theorem 11.1 read from the other end of each chain;
by Part I's Theorem 6.2, `⊔_t 𝖪_m` has value `ceil(log2 m)` for `t = 1` and
`ceil(log2(m+1))` for `t ≥ 2`, which is Part II's tower formula at `q = 2`;
`m = 2, t = 2` is the counterexample `sm(S ⊔ S) = 2`, and since
`𝖪_m ≅ [0, ω^(m−1)]` (proved in item 4 there), `K_k ≅ 𝖪_(2^k)` and `m = 2^k`
gives Part I's sharp family. The formula was compared with all 129 rows of
`data/ordinal_values.csv` and all 16 of `data/sharp_family.csv`: all agree.
The `q = 2` rows of `data/02-finite-output-sharp_families.csv` with word
lengths 2 and 4 are finite analogues of `S ⊔ S` and Part I's eight-point
example. Part I also answers Part II's Research question 1 at `q = 2` (the
bound `h + s` is attained on every Hausdorff space of finite height); a note
after the question re-scopes it to `q ≥ 3`. Part III (batch 56) answers it
for every `q` on spaces with a finite nonempty derived set. Part IV
(batch 65) answers its second half for each fixed coloring on every space
(the closure signature), and for a fixed coloring the layer count is now
known on every Hausdorff space with `X'' = ∅`. Part V (batch 68) answers its
first half on every locally compact or sequential (more generally
rank-accessible) Hausdorff space of finite height, at every `h` and also
when the last derivative is infinite: there `(q−1)h + s` is attained for
every feasible `s`. For the uniform invariant `sm_q`, heights `h ≥ 2` and
infinite derived sets therefore remain open only outside that class, and
which spaces attain `(q−1)h + s` in general remains open (rank
accessibility is sufficient, not necessary). (Updated 30 September 2026,
batch 68: before Part V this paragraph said that heights `h ≥ 2` and
infinite derived sets remain open for `sm_q`.)

**Part III.** `X` is a Hausdorff space whose derived set
`X' = {p_1, …, p_t}` is finite and nonempty (so `h = 1`, but not every
`h = 1` space is of this kind), and `c` a coloring using `q_c` colors.

- *Filter model* (Lemma 32.1, Lemma 32.2): `X` splits into a clopen discrete
  part and clopen neighborhoods `N_i` of the `p_i`, each a one-point space on
  a free filter; a finite union of color cells is a neighborhood exactly when
  it contains every positive cell.
- *Exact profile* (Theorems 33.1, 33.4): a word is admissible iff it contains
  every used color and every arc `ab` of a digraph `G_c` on the colors (arcs
  from each center color to the colors accumulating at that point) as a
  subsequence; hence `L(X, c) = q_c + τ(G_c)` with `τ` the directed feedback
  vertex number, and depth `ceil(log2(q_c + τ(G_c)))` (Lemma 33.3:
  `ℓ(G) = |V| + τ(G)`); a weighted version (Corollary 33.5).
- *Capacities* (Proposition 34.2, Theorem 34.4): the partition capacity `b_i`
  of the neighborhood filter at `p_i` (1 exactly for an ultrafilter; finite
  `b` exactly for an intersection of `b` ultrafilters) determines
  `sm_q(X)` through `min(b_i, q−1)` alone.
- *Attainment* (Theorem 34.5): `L = q + s − 1`, the bound `(q−1)h + s` at
  `h = 1`, is attained with exactly `s` colors on `X'` iff the points split
  into `s` nonempty bins each of total capacity at least `s − 1`.
- *Three labels* (Theorem 35.1): `sm_3(X) = 3` iff `v + floor(u/2) ≥ 3`
  (`u` points of capacity 1, `v` of capacity ≥ 2), else 2. Three one-point
  free-ultrafilter spaces give 2, three convergent sequences 3, with equal
  derivative cardinalities (equation (35.1)); the ultrafilter space is not
  locally compact and has no convergent injective sequence (Proposition 35.2).
- *Regular points* (Proposition 36.1, Corollary 36.2): first countable or
  locally compact points have infinite capacity, so then
  `sm_q(X) = ceil(log2(q − 1 + min(q, t)))`, Part II's tower value at `m = 2`
  for all such spaces.
- *Extremal graphs* (Lemma 37.1, Theorem 37.2): the least number of arcs of a
  digraph on `q` vertices with acyclic number at most `r` is
  `T(q, r) = ra(a−1) + 2as` (`q = ar + s`, `0 ≤ s < r`), attained exactly by
  balanced unions of complete bidirected graphs.
- *Ultrafilter sums* (Theorem 38.1, Corollary 38.2, Corollary 38.3): for `t`
  one-point ultrafilter spaces the worst layer count is `2q − r_*(q, t)`; the
  extra question over `ceil(log2 q)` appears exactly from `t_q` components
  (2 when `q` is a power of two, `q(q−1)` when `q = 2^(k−1) + 1`; table
  through 64 labels in the data).
- *Algorithms* (Section 39): an exact `O(2^q(q + |E|))` algorithm on supplied
  profiles (not on arbitrary infinite presentations); NP-completeness of
  `L ≤ M` and `D ≤ d` for profile-graph input with unbounded alphabet
  (Proposition 39.1), by directed feedback vertex set.
- Nine research questions (Section 41, numbered 11–19).

**Part III against Parts I and II** (Section 29.4, checked at the write): at
`q = 2` it gives value 1 for `t = 1` and 2 for `t ≥ 2`, Part I's Theorem 6.2
at `h = 1`; its bound (34.3) is Part II's Theorem 20.1 at `h = 1`; for sums of
convergent sequences its Corollary 36.2 is Part II's Theorem 20.3 at
`m = 2`. Part II's remark after Theorem 20.3 never asserted that every space
of a given height has the same invariant, so the separation refutes nothing.
An independent script written at intake and rerun at this write (not
shipped) confirmed `ℓ(G) = |V| + τ(G)` on all 4,165 loopless digraphs on at
most four labelled vertices, `T(q, r)` and its equality graphs for `q ≤ 4`,
the ternary formula and the bin criterion on 172 capacity lists (and Part
II's tower formula for infinite capacities), the ultrafilter layer formula
for `q ≤ 4`, and all 63 rows of the jump table.

**Part IV.** `X` is any nonempty topological space, with no separation
axiom unless stated, and `c : X → Σ` a coloring with `q` letters. For a
closed set `F` put `T_a(F) = cl(c⁻¹(a) ∩ F)` and, for a word `v`,
`F_v = T_(v_1) ⋯ T_(v_k)(X)`. The *closure signature* `S(X, c)` is the set
of nonempty reduced words `v` with `F_v ≠ ∅`; its rank `ρ(X, c)` is the
supremum of their lengths.

- *Duality* (Theorem 47.2): a word `w` of length `m` is admissible iff every
  signature word is a subsequence of `w`, iff every signature word of length
  at most `m` is; a rejected word has a rejected signature word of length at
  most `m`. The signature is a downset (Lemma 46.2).
- *Finite rank* (Theorem 48.1, Proposition 48.2, Corollary 48.4): finite
  depth ⇔ finite `L` ⇔ finite `ρ`; then `L` is the shortest common
  supersequence length of the maximal signature words, of which there are at
  most `q(q−1)^(ρ−1)`, and `ρ ≤ L ≤ (q−1)ρ + 1`, sharp, on every space.
- *Recovery and classification* (Theorems 49.2, 50.3, 50.5): at finite depth
  the admissible words determine the signature, and finite-depth colored
  spaces, up to equality of admissible words, correspond exactly to nonempty
  finite downsets of reduced words; each class has a finite-poset
  representative (at most `ρq(q−1)^(ρ−1)` points) and a compact countable
  metrizable one (a finite sum of towers `𝖪_b`).
- *Optimal height* (Lemma 51.1, Theorem 51.2): on a Hausdorff space
  `F_v ⊆ X^(|v|−1)`; the least Cantor–Bendixson height of a Hausdorff
  representative of a finite-depth profile is exactly `ρ`.
- *Rank one* (Theorem 51.3): on every Hausdorff space with `X'' = ∅`,
  `L(X, c) = q_c + τ(G_c)`, with an arc `a → b` when
  `c⁻¹(a) ∩ cl(c⁻¹(b)) ≠ ∅`; `X'` may be infinite.
- *Finite budgets* (Theorem 52.1, Corollary 52.2): every space has a finite
  poset of at most `mq(q−1)^(m−1)` points with the same admissible words of
  length at most `m`; a finite poset failing an `m`-layer budget has an induced
  obstruction of at most `mq(q−1)^(m−1)` points (Part II: `(m+1)q^m`).
- *Products* (Theorem 53.1, Corollary 53.2): the signature of `c × e` consists
  of the reduced pair words whose reduced projections lie in the factor
  signatures; `ρ(X × Y) = ρ(X) + ρ(Y) − 1`; `L` and depth are bounded by
  max/product and max/sum.
- *Higher order* (Theorem 54.1, Proposition 54.2): two three-colorings of one
  compact countable metrizable space of height four agree on every signature
  word of length at most three and on every derivative's color cardinalities,
  yet need 9 and 7 layers, 4 and 3 questions; the construction repeats at
  every height.
- *Algorithms* (Section 55): bounded-signature extraction relative to closure
  and emptiness oracles, exact SCS by progress-state search, and conversion of
  a word into open questions.
- Nine research questions (Section 57, numbered 20–28).

**Part IV against Parts I–III** (Section 43.4, checked at the write): its
normal form and elimination are Part II's Theorem 16.2 and Proposition 16.3;
on finite posets the signature is Part II's set of reduced chain words, so
duality there is Part II's Theorem 17.1 and the rank bounds are Part II's
Corollary 19.2; its universal constant is Part II's equation (19.2); for a finite
nonempty derived set its digraph is Part III's and Theorem 51.3 is Part III's
Theorem 33.4; its rank bound `L ≤ (q−1)h + q` on spaces of last rank `h` is
weaker than Part II's sharp `(q−1)h + s`, as the manuscript says; and the
product rank law is the coloring analogue of Part I's Lemma 9.1 (product of
last ranks `h + k`), which the manuscript does not cite. An independent
script written at intake and rerun at this write (not shipped) reproduced the
counts of Section 56 (389 topologies, 29,577 colorings, 21,639 with a finite
tree, 109 signatures), compared duality and the short-certificate test with a
brute-force layering search that does not use elimination (every coloring on
at most three points and a random 2% on four: 73,452 comparisons in the
rerun, 69,612 at intake, all agreeing), and confirmed `U(q, r) = (q−1)r + 1`
for seven `(q, r)`, the 9/7 layers and the 24/12 bases of Theorem 54.1, the
product law on 300 random pairs of two-colored preorders, and
`L = q + τ(G)` on all 4,165 loopless digraphs on at most four vertices.

**Part V.** `X` is a nonempty Hausdorff space of last derivative rank
`h < ω`, `t = |X^(h)|` (possibly infinite; `min(q, t)` then means `q`), and
the colorings `c : X → Σ` are arbitrary. `Λ_q(X)` is the worst layer count
over all `q`-colorings, and `sm_q(X)` its ceiling binary logarithm.

- *Universal upper profile* (Lemma 62.2, Theorem 62.3, Corollary 62.4): on
  every finite-height Hausdorff space, any word containing every reduced
  word of length `h + 1` that starts in a set `S ⊇ c(X^(h))` is admissible;
  a next-occurrence envelope recognizes such words in time `O(qn + qh)`.
  This recovers Part II's bound `(q−1)h + s`.
- *Rank accessibility* (Definition 63.1, Propositions 63.3–63.4, Lemma
  63.5): call `X` rank-accessible when every point of rank `r > 0` is the
  limit of an injective sequence of points of rank `r − 1`. Locally compact
  Hausdorff spaces are rank-accessible without any countable local base (a
  compact rank-one slice has cofinite neighborhoods), and so are sequential,
  in particular first-countable, Hausdorff spaces.
- *Forcing and exact realization* (Lemmas 64.1–64.2, Theorem 64.4,
  Corollary 64.5): on a rank-accessible space, for every set `S` of
  `s ≤ t` colors, one coloring, equal to one color off a countable set
  `F`, has exactly the admissible words `Up(A_{q,h+1}(S))`, and `F` itself
  witnesses the whole profile; any prescribed coloring of `X^(h)` with image
  `S` extends to such an extremizer. `F` is not claimed closed or compact.
- *The invariant* (Theorem 60.1, Theorem 65.1): `Λ_q(X) = h(q−1) +
  min(q, t)` and `sm_q(X) = ceil(log2(h(q−1) + min(q, t)))` on every locally
  compact or sequential (more generally rank-accessible) Hausdorff space of
  finite height; for each `1 ≤ s ≤ min(q, t)` the worst count with exactly
  `s` terminal colors is `(q−1)h + s`. This answers Part III's Research
  question 12 in the affirmative. Examples: `Λ_3 = 5` at `h = 2`, `t = 1`
  (word `01201`); `Λ_q = (h+1)q − h` for infinite `t`; finite witnesses are
  impossible whenever `h(q−1) + s > q`.
- *Products and sums* (Lemma 66.1, Proposition 66.2, Corollaries 66.3,
  66.4): rank accessibility passes to finite products, so
  `Λ_q(∏ X_i) = (q−1)Σ h_i + min(q, ∏ t_i)` with factors of different kinds
  allowed, and `Λ_q(⊔ X_i) = H(q−1) + min(q, T)` for bounded heights, with
  `H` the largest last rank and `T` the number of terminal points at that
  rank. The lower bound needs accessibility only near one terminal point
  per color (Section 66.3).
- *Inverse spectra* (Theorems 67.1–67.3, Corollary 67.4): the layer
  spectrum `(Λ_q)_q` determines `(h, t)` except that `(h, ∞)` and
  `(h + 1, 1)` agree; the depth thresholds have the closed form (67.4); a
  finite test (an initial segment plus one period of the powers of 2 modulo
  the odd part of the normalized height) decides when two depth spectra
  agree for every `q`; and at
  `h = 2^r` all terminal sizes `1 ≤ t ≤ 2^r` share one depth spectrum.
- *Limits* (Example 68.1): a point with a cocountable neighborhood filter
  on an uncountable discrete set is not rank-accessible, yet carries the
  full single-root profile; no coloring equal to the root color off a
  countable set realizes it. Rank accessibility is sufficient, not
  necessary.
- Eight research questions (Section 71, numbered 29–36).

**Part V against Parts I–IV** (Section 59.4, checked at the write): the
normal form and word constant are Part II's Theorems 16.2 and 19.1 (printed
once; Part V's statements point there); Corollary 62.4 is the upper bound of
Theorem 20.1, whose proof is the case of the cyclic universal word; Part II's
tower invariant (Theorem 20.3) is Theorem 65.1 on `⊔_t 𝖪_m`, and Part III's
Corollary 36.2 is Theorem 65.1 at `h = 1` with finite `t` (Part III's local
hypotheses make the space rank-accessible, and rank-accessible points have
infinite capacity); at `q = 2` the formula is Part I's `h + 1` / `h + 2`,
which Part I proves with no local hypothesis, and the product and sum laws
are Part I's; Part III's three ultrafilter points (`sm_3 = 2` where the
formula would give 3) show that some local hypothesis is needed, and the
cocountable example is a finite-derived-set space covered by Part III's
Theorem 33.1 and Part IV's Theorem 51.3; the identity of Lemma 66.1 is Part
I's Lemma 9.1. Part IV appeared after the manuscript's pin: its duality
gives a second proof of Theorem 62.3 (printed after Corollary 62.4), its
recovery theorem shows that Part V's extremal coloring has the largest
signature allowed for its terminal colors, which bears on Part IV's
Research question 20, and its product law (one pair coloring) and Part V's
(the supremum over colorings) are complementary. The certificate word
`01201` is also the word of Part II's six-chain example. The intake check
script, rerun at this write (not shipped), confirmed the word constant by
exact search for `q ≤ 4`, the example `01201`, the threshold formula
(28,014 cases), dyadic aliasing (80,132 cases), the delivered
`spectra_equal` against brute force over `q ≤ 4096` (11,664 pairs) and the
`(h, ∞) ~ (h + 1, 1)` identity; no statement of Parts I–IV is refuted.

## Notation

Part II's notation table (Section 14.3) lists every letter used differently
in Parts I and II; Part III's (Section 29.3), Part IV's (Section 43.3) and
Part V's (Section 59.3) do the same for Parts III, IV and V. The readings
most likely to mislead:

- **`K_k` vs `𝖪_m`.** True: Part I's `K_k = [0, ω^(2^k−1)]` has
  `sm(K_k) = k`; Part II's tower `𝖪_m` (printed in sans-serif; the
  manuscript's `K_m`) has last derivative rank `m − 1` and
  `sm_2(𝖪_m) = ceil(log2 m)`, so `K_k ≅ 𝖪_(2^k)`. False: `𝖪_k = K_k`. This is
  the only renamed symbol of Part II.
- **Layer direction and outer color.** Part I indexes closed layers from the
  outer (open) one, with outer color `c ∈ {0, 1}`; Part II numbers positions
  from the bottom, and `c` is the coloring. Part I's outer color is the *last*
  letter of a Part II word.
- **`h`.** The last derivative rank in all parts, except Part II's `h_c`
  (Corollary 19.2, the supremum of reduced chain-word lengths) and the column
  `h` of `data/02-finite-output-sharp_families.csv`, which is the word length.
  Part III's class (finite nonempty derived set) is a proper subclass of
  `h = 1`: `[0, ω²)` has `h = 1` and an infinite derived set. False: "Part III
  settles `h = 1`".
- **`sm` vs `sm_q`.** Part I's `sm(X)` is an ordinal (a least winning length);
  Part II's and Part III's `sm_q(X)` is a supremum of finite depths, or `∞`.
  At `q = 2` they agree whenever either is finite. The manuscript of Part III
  defined its own macro `\smq` (plain `sm`), which clashes with Part II's
  (`sm_q`, subscript included); it is set with Part I's `\sm`, and the printed
  symbol is unchanged.
- **`L`, `D` in Part III.** The manuscript printed layer count and depth as
  sans-serif `𝖫`, `𝖽`; Part III prints them as Part II's `L`, `D` (same
  numbers). Its `D_i` is the isolated part of a neighborhood, not the depth.
- **`s`, `a`, `b` in Part III.** `s` is the number of colors on `X'` (as in
  Part II), but in `T(q, r)` with `q = ar + s` it is a remainder and `a` a
  quotient, not a color; `b_i` is a partition capacity, not Part II's
  coloring `b_(a,m)`.
- **Fixed coloring vs supremum over colorings.** Part II's sharp
  synchronization examples are fixed colorings; its tower formula is a
  supremum over colorings. For towers `𝖪_m` with `m ≥ 2` the supremum
  increases by at most one under sums, even though fixed colorings can lose `ceil(log2 q)` questions.
  Every result of Part IV concerns a fixed coloring (its product law, the
  specified pair coloring), not `sm_q`.
- **Macros renamed in Part IV.** The manuscript's one-argument `\cl` (an
  overline) clashed with Part I's `\cl` and is set as `\cwcl` (printed
  unchanged); its `\rk` (printed `ρ`) clashed with Part I's `\rk` and is
  written `\rho`; its `\depth` (printed `depth`) is Part II's `\depth`
  (printed `D`); its italic `L(X, c)` is Part II's `L(X, c)` (upright, same
  number); its `\Adm` and `\wordlen` are Part II's `\W` and `\len`; its
  tower `K_k` is printed `𝖪_k`, as in Part II (not Part I's `K_k`); its basis
  `𝓑(X, c)` is printed `𝓑^bas(X, c)`, because Part III's `𝓑` is a Boolean
  algebra.
- **`T_a`, `F_v` in Part IV.** `T_a(F)` is a color closure, not Part II's
  ideal-automaton transition `T_a(I)` (equation (23.3)); `F_v` is a nested
  closure, not Part I's layer `F_i` or Part III's filter `𝓕`.
- **Height in Part IV.** The Cantor–Bendixson *height* is the least `k` with
  `X^(k) = ∅`, that is `h + 1`; the space of Theorem 54.1 has height four and
  `h = 3`. `D` and `D_m` are downsets of words, not the depth.
- **Height in Part V.** Part V's manuscript says "height `h`", "height
  two", "height zero" and "normalized height `H`" for the last derivative
  rank `h`, whereas Part I's Appendix B and Part IV call `h + 1` the height.
  False: a "height-two space" of Part V has height two in Part IV's sense
  (it has height three there).
- **Macros and symbols renamed in Part V.** The manuscript's sans-serif
  `𝖫(X, c)` and `𝖣(X, c)` are printed as Part II's `L(X, c)` and `D(X, c)`
  (same numbers); its `\rank` (printed `rk`) is Part I's `\rk`, the
  Cantor–Bendixson rank of a point, not Part IV's signature rank `ρ`; its
  arithmetic spectra `F_{h,t}(q)` and `E_{h,t}(q)` are printed `Φ_{h,t}(q)`
  and `Ψ_{h,t}(q)`, because Part IV's `F_v` is a nested closure and Part I's
  `F_i` a layer. Its `F`, `F_a`, `F_n` are countable point sets (witness and
  skeletons), its `b_0, …, b_h` envelope positions (not Part III's
  capacities `b_i`), and its `(H, T)`, `(K, U)` normalized pairs (not
  Part III's arc count `T(q, r)` or Part IV's closure `T_a`).
- **`Λ_q` vs a fixed coloring.** `Λ_q(X)` is a maximum over colorings, like
  `sm_q`; Part V's product and sum laws are about these maxima and are
  complementary to Part IV's product law for one pair coloring.

## Not claimed

- Part I refutes Problem 1.3 as printed in v3 of the arXiv paper; it does not
  resolve the paper's other questions (large countable point-separation
  ordinals, finite membership values on crowded spaces) or classify games of
  arbitrary uncountable length. No transfinite version of the logarithm
  formula is asserted; `∞` in a finite profile is not an ordinal rank.
- No part claims to introduce difference hierarchies, canonical
  difference chains, multi-valued partition hierarchies (Selivanov) or the
  three-letter modified-SCS hardness (Lagoutte–Tavenas); Part II credits
  typed-DAG fusion (Darte) through Lagoutte–Tavenas without a direct audit.
- Part II does not claim Part I's binary counterexample, binary chain
  algorithm or binary Cantor–Bendixson results anew. It announces no named
  longstanding published problem as solved and does not assert the word
  "breakthrough". Its uniform bound `(q−1)h + s` is not claimed to be attained
  by every coloring or every space for `q ≥ 3`; its compact sharpness
  constructions concern specified colorings, not `sm_q`. It makes no claim
  about transfinite determinacy, countable stopping times or the full
  point-separating invariant.
- Part III does not classify spaces of height `h ≥ 2` or with infinite
  derived sets, transfinite play or expected-cost optimization, and does not
  address Part II's Research question 2 (minimum synchronization families):
  its ultrafilter thresholds count components while permitting every label
  at finitely many isolated exceptions, a specific input model. It makes no
  priority claim for the supersequence/feedback-set lemma, the random-order
  bound or the balanced-clique arc extremum, and its literature search was
  targeted, not exhaustive. It does not refute Part II's upper bound. Free
  ultrafilters are used in ZFC; the finite checks construct none. Its
  algorithm takes the positive-cell sets as input; computing them from an
  arbitrary presentation is not claimed (Research question 16). Its
  NP-completeness is for explicit profile encodings with an unbounded
  alphabet.
- Part IV does not determine which signatures the colorings of a prescribed
  space can have, so it does not settle the attainability half of Part II's
  Research question 1, the uniform invariant `sm_q` at heights `h ≥ 2` or on
  infinite derived sets, or transfinite games; it claims the normal form,
  greedy elimination, chain interpretation, compact word construction and
  universal constant of Parts II and III only as credited prior material. It
  does not identify word equivalence with homeomorphism, continuous
  reducibility, Wadge equivalence or any partition hierarchy (Selivanov), and
  does not claim the shortest-common-supersequence problem or its three-letter
  hardness. Its algorithms are relative to supplied closure and emptiness
  operations, not polynomial-time algorithms for arbitrary input; its product
  law concerns the pair coloring, not every coloring of a product; its
  obstruction bound is an upper bound, not claimed optimal, and a Hausdorff
  finite-subspace version is false (remark after Corollary 52.2). "New here"
  means new relative to the inspected report, not certified priority.
- Part V concerns maxima over colorings: it does not classify every fixed
  coloring at height two (Part III's Research question 11, restated as
  Research question 30, stays open), does not cover Hausdorff spaces without
  a local hypothesis (rank accessibility is sufficient but not necessary,
  Example 68.1), does not assert that its countable witness is closed or
  compact, and does not treat transfinite games or expected cost. It claims
  the tree–layer normal form and the restricted-start word constant only as
  Part II's results, reproved, and the derivative calculus of products as
  not new. Its advance is stated relative to the repository question at the
  pin; historical priority outside the inspected sources is not certified,
  and its targeted literature searches were not exhaustive. Its arguments
  are in ZFC.
- No priority is certified by any part. Targeted searches found no earlier
  resolution; that is a search statement only.
- The finite checks do not establish the infinite-space theorems, the general
  NP-hardness reductions, or novelty. Part II's six-point verifier option was
  not run; the three-color optimality of its approximation guarantee is
  conditional on P ≠ NP, and no such claim is made for `q ≥ 4`.
- Part I's computations were not rerun in the repository. The batch-52
  intake reran Part II's full suite on a copy (59 s): CSV files identical,
  JSON files equal after CRLF → LF except `python` and `elapsed_seconds`. The
  batch-56 write reran Part III's suite on a copy (about 4 s, Python 3.14.4):
  both CSV files byte-identical, JSON files and console log equal after
  CRLF → LF. The batch-65 write reran Part IV's suite on a copy (29.8 s on a
  loaded machine, Python 3.14.4; 4.282 s recorded under Python 3.13.5, a
  timing specific to the delivering environment): the JSON equal after
  CRLF → LF except `python` and `elapsed_seconds`. The batch-68 write reran
  Part V's suite on a copy (2.6 s, Python 3.14.4; 1.118 s recorded under
  Python 3.13.5): the three CSV files byte-identical, the JSON files equal
  after CRLF → LF except `python` and `elapsed_seconds` of
  `verification.json`, and the console output equal to the recorded `.log`
  in the same way.

## Build the article

Build in a scratch copy so that no auxiliary files land here:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three
times. The shipped PDF was built with MiKTeX (pdfTeX, MiKTeX 26.2): 131 pages,
no errors or warnings, no undefined or multiply defined references, no
duplicate destinations, no overfull or underfull boxes, no Type 3 fonts (the
build of the committed Parts I–IV text was equally clean at 101 pages). The
bibliography is internal; Latin Modern is used as an installed TeX font, and
no font files are included. Part V's one figure is drawn by TikZ in the
source. Part I's `Makefile`
runs three pdfLaTeX passes in this directory and leaves `.aux`, `.log`,
`.out` and `.toc` files here. Do not use `code/02-finite-output-Makefile`: it
is written for the delivery's layout, runs only two passes, and from this
directory its `verify` and `smoke` targets would call Part I's
`code/verify.py`, which rejects `--brute-n`. Do not use
`code/03-filter-profiles-Makefile` either: from this directory its `verify`
target would run Part I's `code/verify.py` without `--output`, replacing
Part I's recorded files in `data/`, and write its console output to a new
`results/verification.log`; its `pdf` target runs two passes in place and
its `clean` target deletes this report's auxiliary files. Do not use
`code/04-closure-words-Makefile` either: from this directory its `verify`
target would run Part I's `code/verify.py --output results/rerun.json`,
which treats the output as a directory and creates `results/rerun.json/`
with Part I's files; its `pdf` target runs three passes in place and its
`clean` target deletes this report's auxiliary files. Do not use
`code/05-word-profiles-Makefile` either: from this directory its `verify`
target would run Part I's `code/verify.py --output results`, writing Part
I's outputs into a new `results/` directory; its `pdf` target runs three
passes in place and its `clean` target deletes this report's auxiliary
files.

## Rerun the checks

All five verifiers use only the Python standard library (3.10 or later). Do
not use Python's `-O` option: the assertions are the checks (Part IV's
verifier refuses to run under it). Use `py` or `python3` as your system
provides; the Makefiles call bare `python3`.

**Part I.** Without `--output` it writes into `data/` and replaces the
recorded files. Pass a scratch directory:

```sh
py code/verify.py --max-n 6 --output ../scratch-part1   # about 13 s recorded; --max-n 4 is a smoke test
```

This repeats 320,866 poset-and-target tests on 5,231 naturally labelled
posets: for every target it compares exhaustive minimax over all legal open
questions, canonical alternating-closure profiles and an alternating-chain
dynamic program, and it checks a synthesized balanced query tree on every
point. Without options it checks through five points, not six; the allowed
maximum of seven is substantially more expensive. The tables
`ordinal_values.csv` and `sharp_family.csv` evaluate the proved formulae in
exact integer arithmetic; they are not experiments on infinite spaces. Its
JSON output has the platform's line endings and its CSV files
CRLF on every platform, whereas the recorded files are LF: compare after
CRLF → LF (a `--max-n 4` run on a copy gave the recorded
`ordinal_values.csv`, `sharp_family.csv` and `strategy_certificate.json` after
normalization).

**Part II.** Without `--output` it creates a `results/` directory in this
report directory, with unprefixed names. Pass a scratch directory:

```sh
py code/02-finite-output-verify.py --max-n 5 --brute-n 4 --output ../scratch-part2
py code/02-finite-output-verify.py --max-n 3 --brute-n 3 --output ../scratch-smoke
```

The first is the recorded run: 102,331 colored-poset checks on 407 naturally
labelled posets, 4,156 chain-language checks, 416,432 fixed-word checks, 36
restricted-start triples (15 cross-checked by brute force) and 1,176 padding
checks (`data/02-finite-output-verification.json`; 12.19 s recorded, 59 s on
this machine). Compare `verification.json` → `02-finite-output-verification.json`
and so on: its JSON files are written with the platform's line endings (CRLF
on Windows) and differ from the record in `python` and `elapsed_seconds`; its
CSV files are CRLF everywhere, like the recorded ones. The counts are not
counts of isomorphism classes: every finite poset has a natural labelling, so
every type through the stated size is covered, possibly repeatedly. The
finite posets carry the Alexandrov upper-set topology and are not finite
Hausdorff approximations of the ordinal spaces.

**Part III.** Without `--output` it too creates a `results/` directory here,
with unprefixed names. Pass a scratch directory and capture the console:

```sh
W=../scratch-part3
mkdir -p "$W"
py code/03-filter-profiles-verify.py --output "$W/results" > "$W/verification.log"
for f in verification.json capacity_checks.json strategy_certificates.json; do
  diff <(tr -d '\r' < "$W/results/$f") "data/03-filter-profiles-$f"; done
for f in extremal_thresholds.csv query_jump_thresholds.csv; do
  cmp "$W/results/$f" "data/03-filter-profiles-$f"; done    # CRLF on both sides
diff <(tr -d '\r' < "$W/verification.log") data/03-filter-profiles-verification.log
```

This is the recorded default run (`--max-q 4`): 4,165 loopless digraphs on
one to four labelled vertices against 4,472 reduced words, 11,515
positive-cell word checks, 98 capacity cases, 10 extremal arc thresholds
with every equality graph, and threshold tables and balanced constructions
through 64 labels (not an exhaustive digraph check at that size). Its JSON
files and console output have the platform's line endings (CRLF on Windows),
whereas the recorded ones are LF; its CSV files are CRLF on every platform,
like the recorded ones. The JSON records no Python version or time, so a
rerun agrees exactly after CRLF → LF (checked on 29 September 2026).

**Part IV.** Without `--output` it writes `results/verification.json` beside
`code/`, that is, a new `results/` directory in this report (in the delivery
that path was the recorded file; here the record is
`data/04-closure-words-verification.json`). Pass an explicit file outside
the report:

```sh
W=../scratch-part4
mkdir -p "$W"
py code/04-closure-words-verify.py --output "$W/rerun.json"
diff <(tr -d '\r' < "$W/rerun.json") data/04-closure-words-verification.json
```

This is the recorded default run (`--max-n 4 --q 3`): all 389 labelled
topologies on one to four points (including non-T₀ ones) and all 29,577
three-colorings, 21,639 of them with a finite tree; 3,481,578 candidate-word
comparisons of exhaustive minimax, closure elimination, the full signature
test and the short-certificate test (2,847,462 rejected candidates with short
certificates, 109 distinct finite signatures, 7,296 separating-word tests);
256 ordered products of the 16 finite-depth two-colorings on one or two
points, with 9,856 rectangular-closure identities; all 4,165 loopless
digraphs on one to four vertices; the universal-word constant for `q = 2`,
`r ≤ 8`, `q = 3`, `r ≤ 6`, `q = 4`, `r ≤ 3`; and the explicit hard and soft
words of Theorem 54.1. The output is written with the platform's line
endings (CRLF on Windows), whereas the record is LF, and it differs from the
record in `python` and `elapsed_seconds` (checked on 30 September 2026). The
counts are of labelled topologies, not homeomorphism classes. Its options
are `--max-n` (1–4) and `--q` (2–4).

**Part V.** Without `--output` it creates a `results/` directory beside
`code/`, that is, in this report, with unprefixed names (in the delivery
that was the record; here the record is `data/05-word-profiles-*`). Its only
option is `--output`, a directory. Pass a scratch directory outside the
report and capture the console:

```sh
W=../scratch-part5
mkdir -p "$W"
py code/05-word-profiles-verify.py --output "$W/results" > "$W/verification.log"
for f in certificate.json depth_aliases.json verification.json; do
  diff <(tr -d '\r' < "$W/results/$f") "data/05-word-profiles-$f"; done
for f in universal_words.csv finite_forests.csv sample_spectra.csv; do
  cmp "$W/results/$f" "data/05-word-profiles-$f"; done    # CRLF on both sides
diff <(tr -d '\r' < "$W/verification.log") data/05-word-profiles-verification.log
```

This is the recorded run: 36 universal-family triples (`q = 2`, `h ≤ 5`;
`q = 3`, `h ≤ 3`; `q = 4`, `h ≤ 2`; every `s`) with 185,322 reduced
candidate words scanned directly and by the envelope test, 10,599
candidates with repeated letters, 23 finite-forest minimax computations on
Alexandrov ancestor posets of at most ten points, 19,968 threshold boundary
cases, 8,448 spectrum-pair tests, 64,449 dyadic-alias cases and 4,352
infinite-terminal normalizations. Its JSON files are written with the
platform's line endings (CRLF on Windows), whereas the recorded ones are LF;
its CSV files are CRLF on every platform, like the recorded ones. The
program does not write a log: `data/05-word-profiles-verification.log` is a
captured copy of its console output, which prints the summary JSON, so the
shipped `.log` and `.json` are the same bytes. A rerun differs from the
record only in `python` and `elapsed_seconds` (checked on 30 September
2026). The finite forests are Alexandrov posets, not Hausdorff models of
convergent sequences. To use the all-alphabet spectrum test as the
delivered README suggests, import `spectra_equal` from a copy of the
verifier saved as `verify.py` (the module name the delivered example
imports), not from the shipped file name, which is not a valid module name.

**Strategy certificates.** In the certificate files of Parts I and II, bit
`i` of a mask is point `i` (zero-based). At an internal node ask membership
in `open_mask` and follow `yes` or `no`. Part I's leaves record `color` and a
closed-layer index; its eight-point example has two disjoint four-element
chains, profile `(5,5)`, depth 3, and "strict-upper" rows. Part II's leaves
record `color` and a one-based `layer`; its predecessor masks hold strict
predecessors, the chains are `01, 02, 10, 12, 20, 21` in that order, and the
word is `01201`. Part III's file holds two examples, `ultrafilter_three`
(arcs `0→1, 1→2, 2→0`, word `0120`, four layers, depth 2) and
`convergent_three` (all six arcs, word `01210`, five layers, depth 3); a node
`ask_suffix_from_position: j` asks for the union of the zero-based word
positions `j, j+1, …`, and leaves record `leaf_position` and `label`. That
these suffixes are open sets is proved in the article (Theorem 33.1); the
JSON does not encode an ultrafilter. Part V's file records `q = 3`, `h = 2`,
`starts = [0]`, the word `01201`, the zero-based envelope `[0, 2, 4]`
(the one-based `b_0, b_1, b_2 = 1, 3, 5` of Appendix G), zero-based
embeddings of the four patterns `010, 012, 020, 021`, and a query tree whose
nodes `ask_suffix_from_position: j` ask whether the layer index is at least
`j` (the `yes` branch keeps that suffix) and whose leaves record `position`
and `color`; the tree has depth three. That the suffixes are open on a
height-two space is Theorem 62.3, not something the JSON encodes.

## Discrepancies and delivery names

- `RESEARCH_STATUS.md` is Part I's delivered status record and is not edited:
  it describes Part I only. Part II's claim boundaries are in
  `02-finite-output-RESEARCH_STATUS.md` and in the article (Section 14.1);
  Part III's in `03-filter-profiles-SOURCES.md` and in the article
  (Section 29.1); Part IV's in `04-closure-words-SOURCES.md` and in the
  article (Section 43.1); Part V's in `05-word-profiles-SOURCES.md` and in
  the article (Section 59.1).
- `02-finite-output-RESEARCH_STATUS.md` and `02-finite-output-SOURCES.md`
  describe "this archive", its PDF and its compile, which are not shipped.
  The status record's sentence that a repository search for `supersequence`
  returned no matches was true at the pin; the repository now contains
  Part II.
- `03-filter-profiles-SOURCES.md` names `results/verification.json` (shipped
  as `data/03-filter-profiles-verification.json`), "Section 11 of the article"
  (Section 40 here) and "the README and article", meaning the delivery
  README (not shipped) and the manuscript (printed as Part III).
- `code/02-finite-output-Makefile` names `article.tex` and `code/verify.py`
  (in the delivery: its own article and verifier) and
  `/tmp/open-query-smoke`; `code/03-filter-profiles-Makefile` names
  `article.tex`, `code/verify.py` and `results/`; see "Build the article".
- `code/02-finite-output-verify.py` and `code/03-filter-profiles-verify.py`
  default to `results/` beside `code/` and write unprefixed names (see "Rerun
  the checks").
- `data/02-finite-output-pdf_build.log` is the log of the delivered PDF, which
  is not shipped; the shipped `article.pdf` is a build of the merged text.
- The verification sections and certificate appendices of Parts II and III
  are printed with the shipped names and an explicit `--output`; the
  delivered commands (`code/verify.py`, `/tmp/open-query-smoke`, Part III's
  `python3 code/verify.py` without an output option) and Part III's delivered
  file table are quoted in the notes there.
- Part I's own texts name `python3 code/verify.py --max-n 6` without
  `--output` (Section 12, `Makefile`): that command replaces the files in
  `data/`.
- When Part II was written in, Section 14.1 and this README said "nine"
  research questions and "1–9"; Part II prints ten. Corrected at the batch-56
  write, with a dated note in Section 14.1.
- `code/04-closure-words-verify.py` defaults its `--output` to
  `results/verification.json` beside `code/`, a path this report does not
  have (the record is `data/04-closure-words-verification.json`), and writes
  its JSON with the platform's line endings; `code/04-closure-words-Makefile`
  calls `python3 code/verify.py --output results/rerun.json` and builds
  `article.tex` in place. See "Rerun the checks" and "Build the article".
- `04-closure-words-SOURCES.md` names "the corresponding directory README",
  "the new manuscript" and "the package", meaning this README at the pin, the
  manuscript (printed as Part IV) and the delivery; its line ranges (500–640,
  …, 3780–3970) refer to the article blob `d1e50fd0` (Parts I–III), not to
  this `article.tex`, in which the notes of this write move later lines. Its
  sentence that the rendered HTML of Chiozini–Csernák–Soukup "has also
  circulated with an earlier title" is inaccurate: both titles belong to v3
  (see "Sources and attribution").
- `data/04-closure-words-validation.json` describes the delivered
  manuscript: its 25 pages, word count, pdfTeX log summary and the SHA-256
  digests of the delivered `article.pdf` and `article.tex` (not shipped) and
  of the verifier (`code/04-closure-words-verify.py`, which still matches).
  It does not describe the shipped `article.pdf`.
- The delivered manuscript defines lemmas, propositions and corollaries with
  `\newtheorem` on the theorem counter without `aliascnt`, so its PDF calls
  them all "Theorem" in cross-references; in this report they carry their own
  names. Numbers are unchanged.
- The verification section of Part IV is printed with the shipped names and
  an explicit `--output`; the delivered text (`code/verify.py`,
  `results/verification.json`, `python3 code/verify.py --output
  results/rerun.json`, run "from the package root") is quoted in the note in
  Section 56.
- `05-word-profiles-SOURCES.md` names "Report directory", "Article Git blob"
  and "README Git blob" at the pin: its line ranges (1100–1520, …,
  4570–4759) refer to the article blob `d1e50fd0` (Parts I–III), not to this
  `article.tex`, and its "README lines 210–400" to the README blob
  `465cb1e0`. Its sentence that a connected GitHub search for the exact term
  `rank-accessible` returned no matches was a statement about the pin; the
  repository now contains Part V. Its last paragraph ("The final PDF was
  compiled locally …", "No existing repository file was modified by this
  task") describes the delivered PDF, which is not shipped, and the
  delivery.
- `code/05-word-profiles-Makefile` names `article.tex`, `code/verify.py`
  and `results` and calls `python3`; it is written for the delivery's
  layout (see "Build the article"). `code/05-word-profiles-verify.py`
  defaults to `results/` beside `code/` and writes unprefixed names (see
  "Rerun the checks").
- `data/05-word-profiles-verification.log` is not written by the verifier:
  it is a captured copy of the console output and has the same bytes as
  `data/05-word-profiles-verification.json`. The manuscript's package table
  calls it the "recorded console output", which is accurate.
- The verification section and package appendix of Part V are printed with
  the shipped names and an explicit `--output`; the delivered text
  (`code/verify.py`, `results/certificate.json`, `python3 code/verify.py
  --output results`, and the delivered package table with `README.md`,
  `Makefile`, seven `results/` files and `SHA256SUMS`) is quoted in the notes
  in Section 69 and Appendix H. The checksum ledger `SHA256SUMS` that the
  manuscript and its delivery README mention is not shipped (retired at
  placement after a 13/13 check).
- The manuscript's proofs of the tree–layer normal form and of the
  restricted-start word constant are not printed in Part V: they are Part
  II's proofs of Theorems 16.2 and 19.1, which the manuscript reproved and
  credited (Section 59.1). Its claim table keeps the words "Existing;
  reproved".

## Research status

Part I's counterexample directly refutes the question as printed in the
retrieved v3; Part II extends Part I's finite normal form and Cantor–Bendixson
analysis from a membership bit to `q` output labels, with sharp constants and
a two-versus-three-label complexity dichotomy, and reproduces Part I's values
at `q = 2`. Part III answers Part II's Research question 1 on Hausdorff spaces
with a finite nonempty derived set, through local filter capacities, and
shows by a three-label separation that rank and derivative sizes do not
determine the finite-output invariant. Part IV characterizes the admissible
words of every fixed coloring of every space by its closure signature and
classifies finite-depth behaviors; for a fixed coloring the layer count is
now known on every Hausdorff space with `X'' = ∅`, which answers the
fixed-coloring part of Research question 14 there, and Part II's obstruction
bound is improved from `(m+1)q^m` to `mq(q−1)^(m−1)` for finite posets.
Part V answers Research question 12 in the affirmative: on every locally
compact or sequential (in particular compact or first-countable) Hausdorff
space of finite height, and more generally on every rank-accessible one, the
uniform invariant is `sm_q(X) = ceil(log2(h(q−1) + min(q, |X^(h)|)))` at
every height and also for infinite last derivatives, realized by one
coloring supported off a countable set with the full universal word profile;
this answers the attainability half of Research question 1 on that class and
the worst-case part of Research question 14 there. For `sm_q`, heights
`h ≥ 2` and infinite derived sets remain open only outside that class
(Research questions 29 and 36 ask for necessary conditions and for the
transfinite case); fixed colorings at height two remain open (Research
questions 11 and 30), and which signatures the colorings of a given space can
have remains open beyond Part V's maximal ones (Research question 20).
(Updated 30 September 2026, batch 68: before Part V this paragraph said that
for `sm_q`, heights `h ≥ 2` and infinite derived sets remain open, Research
questions 11, 12 and 14, and that the attainability half of Research
question 1 remains open.) No part claims a
resolution of all the paper's open questions, independent peer review, or
proof-assistant formalization. No priority conclusion follows merely from
not finding an earlier resolution. Classical difference-hierarchy machinery,
the multi-valued partition literature, the modified-SCS hardness theorem and
the directed-feedback-vertex-set literature are explicitly credited in the
article.

## Relation to neighbouring reports and to the formal project

Two other reports in `games-on-ordinals/` study games on ordinal spaces:
[`point-separating-game-values`](../point-separating-game-values) answers
Problem 1.2 of the same Chiozini–Csernák–Soukup paper (point-separating game
values), a different question from the one Part I answers, and
[`ordinal-chomp-transition-at-two`](../ordinal-chomp-transition-at-two)
studies ordinal Chomp. Parts II–V bear on neither, so no reciprocal
note was written. The report sits in the research-report collection of the
`SetTheory/Cardinals` Lean project, whose library is about large cardinals
(it uses ultrafilters for that purpose, not for these games). That placement
confers no formal status: no Lean or Rocq declaration anywhere in ProveIt
formalizes any statement of Parts I–V (a search of the repository's
`.lean` and `.v` files for open-query games, set-membership numbers,
cut-and-choose games, supersequences, feedback vertex sets, partition
capacities, closure signatures, closure words, rank accessibility,
universal words and word profiles finds none; re-run on 30 September 2026
at the batch-68 write). Section 70.3 records the four interfaces batch-68
manuscript 02 proposes (the tree–layer normal form with `m ≤ 2^d` as the
primary bound, the envelope recurrence and reduced-word universality,
derivative locality with rank accessibility, thinning and skeletons, then
rooted forcing and the profile equivalence, with the arithmetic spectrum
test verified separately). Section 26.3 records the Lean formalization plan
batch-52 manuscript 12 proposes (words and greedy embeddings, query trees and
suffix openness, the chain-language equivalence, a certified checker, then
the towers), Section 39.3 the route batch-56 manuscript 05 proposes (normal
form, digraphs and the feedback-set word, the filter partition lemma, then the
decomposition, capacities and the extremal theorem), and Section 55.4 the
three interfaces batch-65 manuscript 05 proposes (finite words and diagonal
avoidance, the closed-set operator lattice, Hausdorff derivatives and towers);
none of these plans has been started.

[Batch 87, 3 October 2026.] A different kind of query game, in which
players open boxes and must guess an unopened one, is the subject of
[`measurable-box-games`](../../measurable-box-games/); its legal decision
trees are characterized by recursively sliceable cube matchings (its
Theorem 7.3). Both reports work with adaptive query strategies and finite
certificates, but nobody there asks open-set queries about a hidden point,
and nobody here guesses an unread coordinate. No theorem is shared.

## Sources and attribution

Lucas Chiozini, Tamás Csernák, Lajos Soukup, *Gamification of the
T0-pseudoweight via cut-and-choose games on topological spaces*,
arXiv:2510.05754v3, Problem 1.3 and Theorem 3.4.
https://arxiv.org/abs/2510.05754 (Corrected 30 September 2026, batch 65:
this entry said "earlier title *Cut-and-choose games in topological
spaces*". Both titles belong to v3, revised 29 May 2026: the arXiv abstract
page carries *Cut-and-choose games in topological spaces*, the v3 HTML full
text the longer title; checked at this write. Parts III and IV cite the
shorter title; Part V cites the longer one and notes the shorter, for the
game context only.)

Aurélie Lagoutte, Sébastien Tavenas, *The complexity of Shortest Common
Supersequence for inputs with no identical consecutive letters*,
arXiv:1309.0422v2, Corollary 6 (Part IV cites it for context only).
https://arxiv.org/abs/1309.0422

Alexander Göke, Dániel Marx, Matthias Mnich, *Parameterized Algorithms for
Generalizations of Directed Feedback Vertex Set*, arXiv:2003.02483 — the
NP-completeness of directed feedback vertex set used by Part III.
https://arxiv.org/abs/2003.02483

Célia Borlido, Mai Gehrke, Andreas Krebs, Howard Straubing, *Difference
hierarchies and duality with an application to formal languages*, Topology
and its Applications 273 (2020), 106975; Borys Álvarez-Samaniego, Andrés
Merino, *Some properties related to the Cantor–Bendixson derivative on a
Polish space*, New Zealand J. Math. 50 (2020), 207–218; Victor Selivanov,
*Towards a Descriptive Theory of cb_0-Spaces*, arXiv:1406.3942; Saeed Akbari,
Amir Hossein Ghodrati, Afrouz Jabalameli, Morteza Saghafian, *Chromatic
Number and Dichromatic Polynomial of Digraphs*, arXiv:1711.06293; Shamil
Asgarli, Donald Falkenhagen, Kaya Hoshi, *Improved lower bounds for the
maximum order of an induced acyclic subgraph*, arXiv:2511.02819v3 — cited as
background, not as sources of the new game computations (Part V cites the
first, as its arXiv preprint arXiv:1812.01921, for the difference-chain
framework only). No third-party papers or font files are bundled.
