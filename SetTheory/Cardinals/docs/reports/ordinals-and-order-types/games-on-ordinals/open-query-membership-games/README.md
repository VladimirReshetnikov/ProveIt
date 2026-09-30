# Open-query games on ordinal spaces

**An explicit negative answer to the topological-sum problem, with a finite Cantor–Bendixson classification; and its extension to finite output alphabets: sharp synchronization and a complexity dichotomy**

This is a research report in two parts. Part I is the original report of
19 September 2026. Part II was added on 29 September 2026 in batch 52 of
ProveIt's incoming-report intake, from a later manuscript that replaces
Part I's membership bit by one of `q` output labels. Both are AI-assisted;
Part II's manuscript was "prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Open-query games on ordinal spaces: a negative solution to the topological-sum problem, with an exact Cantor–Bendixson classification*) | `ordinal_membership_games.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–13 (pp. 3–17) and Appendices A–B (pp. 41–42) |
| 02 | batch 52, manuscript 12 (*Finite-Output Open-Query Games: Sharp Synchronization and a Complexity Dichotomy*, 29 Sep 2026, 22-page US Letter PDF as delivered) | `ProveIt_Finite_Output_Open_Query_Games.zip` (inner `finite_output_open_query_games/`, main file `article.tex`), arrived in `11e1e9001` | `5c695cfdf` | `a701d9098` (prefix `02-finite-output-`) | Part II: Sections 14–28 (pp. 18–41) and Appendix C (pp. 42–43) |

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

**Status.** AI-assisted and unrefereed. Nothing in either part is formalized
in Lean, Rocq or any other proof assistant, and neither source claims
otherwise. Part II's NP-completeness theorem imports the modified-SCS
hardness theorem of Lagoutte and Tavenas (arXiv:1309.0422, Corollary 6) as an
external input. The finite computations check finite posets only; every
infinite-space statement rests on the written proofs.

## Files

```
article.tex                                    the report, standalone LaTeX with an internal bibliography
article.pdf                                    the compiled report, 45 pages, US Letter (unnumbered title
                                               page, contents pages 1–2, Part I pp. 3–17, Part II pp. 18–41,
                                               appendices pp. 41–43, references pp. 43–44)
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
```

Every file other than `article.tex`, `article.pdf` and this README is
byte-identical to its delivery. Part II's delivery was laid out as
`code/verify.py`, `results/X`, `Makefile`, `RESEARCH_STATUS.md` and
`SOURCES.md`; the mapping is `code/verify.py` →
`code/02-finite-output-verify.py`, `results/X` → `data/02-finite-output-X`,
and the other three → the `02-finite-output-` names above. The three CSV files
were delivered with CRLF line endings and are kept byte for byte by `-text`
lines in `SetTheory/Cardinals/.gitattributes`; the two `.log` files were added
past the repository's `*.log` ignore rule.

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
against a build of the delivered text. Its Research questions 1–9 keep their
numbers, and its Appendix A is Appendix C, after Part I's appendices.
Text added at the write is marked **[Added 29 September 2026, batch 52]**:
five notes in Part I (Section 1, after Remark 4.4, after Corollary 8.2, after
the example of Section 11, in Section 12), a paragraph of the abstract and one
of the title page, and in Part II Section 14 and seven notes (Sections 15, 20,
22, 25, 26, 27, Appendix C).

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
- Nine research questions (Section 27).

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
after the question re-scopes it to `q ≥ 3`.

## Notation

Part II's notation table (Section 14.3) lists every letter used differently
in the two parts. The readings most likely to mislead:

- **`K_k` vs `𝖪_m`.** True: Part I's `K_k = [0, ω^(2^k−1)]` has
  `sm(K_k) = k`; Part II's tower `𝖪_m` (printed in sans-serif; the
  manuscript's `K_m`) has last derivative rank `m − 1` and
  `sm_2(𝖪_m) = ceil(log2 m)`, so `K_k ≅ 𝖪_(2^k)`. False: `𝖪_k = K_k`. This is
  the only renamed symbol.
- **Layer direction and outer color.** Part I indexes closed layers from the
  outer (open) one, with outer color `c ∈ {0, 1}`; Part II numbers positions
  from the bottom, and `c` is the coloring. Part I's outer color is the *last*
  letter of a Part II word.
- **`h`.** The last derivative rank in both parts, except Part II's `h_c`
  (Corollary 19.2, the supremum of reduced chain-word lengths) and the column
  `h` of `data/02-finite-output-sharp_families.csv`, which is the word length.
- **`sm` vs `sm_q`.** Part I's `sm(X)` is an ordinal (a least winning length);
  Part II's `sm_q(X)` is a supremum of finite depths, or `∞`. At `q = 2` they
  agree whenever either is finite.
- **Fixed coloring vs supremum over colorings.** Part II's sharp
  synchronization examples are fixed colorings; its tower formula is a
  supremum over colorings. For towers `𝖪_m` with `m ≥ 2` the supremum
  increases by at most one under sums, even though fixed colorings can lose `ceil(log2 q)` questions.

## Not claimed

- Part I refutes Problem 1.3 as printed in v3 of the arXiv paper; it does not
  resolve the paper's other questions (large countable point-separation
  ordinals, finite membership values on crowded spaces) or classify games of
  arbitrary uncountable length. No transfinite version of the logarithm
  formula is asserted; `∞` in a finite profile is not an ordinal rank.
- Neither part claims to introduce difference hierarchies, canonical
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
- No priority is certified by either part. Targeted searches found no earlier
  resolution; that is a search statement only.
- The finite checks do not establish the infinite-space theorems, the general
  NP-hardness reduction, or novelty. Part II's six-point verifier option was
  not run; the three-color optimality of its approximation guarantee is
  conditional on P ≠ NP, and no such claim is made for `q ≥ 4`.
- Neither source's computations were rerun in the repository. The batch-52
  intake reran Part II's full suite on a copy (59 s): CSV files identical,
  JSON files equal after CRLF → LF except `python` and `elapsed_seconds`.

## Build the article

Build in a scratch copy so that no auxiliary files land here:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three
times. The shipped PDF was built with MiKTeX (pdfTeX, MiKTeX 26.2): 45 pages,
no errors or warnings, no undefined or multiply defined references, no
duplicate destinations, no overfull or underfull boxes, no Type 3 fonts (the
build of the committed Part I text was equally clean at 18 pages). The
bibliography is internal; Latin Modern is used as an installed TeX font, and
no font files are included. Part I's `Makefile`
runs three pdfLaTeX passes in this directory and leaves `.aux`, `.log`,
`.out` and `.toc` files here. Do not use `code/02-finite-output-Makefile`: it
is written for the delivery's layout, runs only two passes, and from this
directory its `verify` and `smoke` targets would call Part I's
`code/verify.py`, which rejects `--brute-n`.

## Rerun the checks

Both verifiers use only the Python standard library (3.10 or later). Do not
use Python's `-O` option: the assertions are the checks. Use `py` or
`python3` as your system provides; both Makefiles call bare `python3`.

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

**Strategy certificates.** In both certificate files, bit `i` of a mask is
point `i` (zero-based). At an internal node ask membership in `open_mask` and
follow `yes` or `no`. Part I's leaves record `color` and a closed-layer index;
its eight-point example has two disjoint four-element chains, profile
`(5,5)`, depth 3, and "strict-upper" rows. Part II's leaves record `color` and
a one-based `layer`; its predecessor masks hold strict predecessors, the
chains are `01, 02, 10, 12, 20, 21` in that order, and the word is `01201`.

## Discrepancies and delivery names

- `RESEARCH_STATUS.md` is Part I's delivered status record and is not edited:
  it describes Part I only. Part II's claim boundaries are in
  `02-finite-output-RESEARCH_STATUS.md` and in the article (Section 14.1).
- `02-finite-output-RESEARCH_STATUS.md` and `02-finite-output-SOURCES.md`
  describe "this archive", its PDF and its compile, which are not shipped.
  The status record's sentence that a repository search for `supersequence`
  returned no matches was true at the pin; the repository now contains
  Part II.
- `code/02-finite-output-Makefile` names `article.tex` and `code/verify.py`
  (in the delivery: its own article and verifier) and
  `/tmp/open-query-smoke`; see "Build the article".
- `code/02-finite-output-verify.py` defaults to `results/` beside `code/`
  and writes unprefixed names (see "Rerun the checks").
- `data/02-finite-output-pdf_build.log` is the log of the delivered PDF, which
  is not shipped; the shipped `article.pdf` is a build of the merged text.
- Part II's verification section and Appendix C are printed with the shipped
  names (`code/02-finite-output-verify.py`, `data/02-finite-output-…`) and an
  explicit `--output`; the delivered commands, which used `code/verify.py`
  and `/tmp/open-query-smoke`, are quoted in the notes there.
- Part I's own texts name `python3 code/verify.py --max-n 6` without
  `--output` (Section 12, `Makefile`): that command replaces the files in
  `data/`.

## Research status

Part I's counterexample directly refutes the question as printed in the
retrieved v3; Part II extends Part I's finite normal form and Cantor–Bendixson
analysis from a membership bit to `q` output labels, with sharp constants and
a two-versus-three-label complexity dichotomy, and reproduces Part I's values
at `q = 2`. Neither part claims a resolution of all the paper's open
questions, independent peer review, or proof-assistant formalization. No
priority conclusion follows merely from not finding an earlier resolution.
Classical difference-hierarchy machinery, the multi-valued partition
literature and the modified-SCS hardness theorem are explicitly credited in
the article.

## Relation to neighbouring reports and to the formal project

Two other reports in `games-on-ordinals/` study games on ordinal spaces:
[`point-separating-game-values`](../point-separating-game-values) answers
Problem 1.2 of the same Chiozini–Csernák–Soukup paper (point-separating game
values), a different question from the one Part I answers, and
[`ordinal-chomp-transition-at-two`](../ordinal-chomp-transition-at-two)
studies ordinal Chomp. Part II bears on neither, so no reciprocal note was
written. The report sits in the research-report collection of the
`SetTheory/Cardinals` Lean project, whose library is about large cardinals.
That placement confers no formal status: no Lean or Rocq declaration anywhere
in ProveIt formalizes any statement of Part I or Part II (a search of the
repository's `.lean` and `.v` files for open-query games, set-membership
numbers, cut-and-choose games and supersequences finds none). Section 26.3
records the Lean formalization plan manuscript 12 proposes (words and greedy
embeddings, query trees and suffix openness, the chain-language equivalence,
a certified checker, then the towers); none of it has been started.

## Sources and attribution

Lucas Chiozini, Tamás Csernák, Lajos Soukup, *Gamification of the
T0-pseudoweight via cut-and-choose games on topological spaces*,
arXiv:2510.05754v3 (earlier title *Cut-and-choose games in topological
spaces*), Problem 1.3 and Theorem 3.4. https://arxiv.org/abs/2510.05754

Aurélie Lagoutte, Sébastien Tavenas, *The complexity of Shortest Common
Supersequence for inputs with no identical consecutive letters*,
arXiv:1309.0422v2, Corollary 6. https://arxiv.org/abs/1309.0422

Célia Borlido, Mai Gehrke, Andreas Krebs, Howard Straubing, *Difference
hierarchies and duality with an application to formal languages*, Topology
and its Applications 273 (2020), 106975; Borys Álvarez-Samaniego, Andrés
Merino, *Some properties related to the Cantor–Bendixson derivative on a
Polish space*, New Zealand J. Math. 50 (2020), 207–218; Victor Selivanov,
*Towards a Descriptive Theory of cb_0-Spaces*, arXiv:1406.3942 — cited as
background, not as sources of the new game computations. No third-party
papers or font files are bundled.
