# Countable Information, Uncountably Many Boxes

**Sharp measurable prediction bounds, exact decision-tree enumeration, and an
all-orders asymptotic expansion**

A research report dated 3 October 2026, built from one manuscript on Elliot
Glazer's *A choiceless box game paradox* (arXiv:2211.10474). Its author line
reads "Prepared for Vladimir Reshetnikov" and carries no AI wording; like the
other deliveries of the intake, it is AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 87, manuscript 02 | `glazer_box_games_research.zip` (364,051 bytes; inner directory `glazer_box_games/`, main file `article.tex`, 999 lines, 24-page US Letter PDF), arrival commit `fa0a0576e` | `6fef5383b` (`6fef5383b126be343cccc9baf47081ef37ab5afe`, the article's `\commit` macro, quoted in Section 1 and in every repository URL of its bibliography) | `d151b39ca` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. Its finite computations were executed
(by the package and again at intake); its infinite theorems rest on the
written proofs only. **Historical priority is not established.**

## The question

Glazer's paper (one arXiv version, v1 of 15 November 2022, 6 pages, math.LO
and math.CO) ends Section 5, "More box games", with the question "Does ZF
prove that G([3], ℝ, {0,1}) is winnable?": can three players facing
continuum many boxes of bits, each opening any boxes it likes and then
guessing an unopened one, guarantee that at most one of them is wrong? The
report separates three properties an infinite strategy can have (a
measurable choice of box and guess, a measurable success event, actual
executability without reading the target) and answers the question for the
first class only.

## What it proves

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

## What is not claimed

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
- Questions Q2–Q12 are directions, not all recognized open problems. No
  endorsement or authorship by Glazer is implied.

## Checks made at intake

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

## Relation to the repository

**Formal status.** No statement is formalized in Lean or Rocq. The manuscript
read three files at its pin, all byte-identical at the write:
`Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` (blob `4961655e`),
`Logic/PeanoArithmetic/ListCoding/README.md` (`74164ac6`) and
`SetTheory/ClosureAxiomatization/README.md` (`fb0ab511`). Its descriptions of
them (Sections 12 and 14.2) are accurate. They are used as architectural
interfaces only: no repository theorem enters a proof. The Busy Beaver
development formalizes blank-tape machines, halting scores and the domination
theorem with the compiler as a stated hypothesis; it says nothing about the
horizon `H` or `BB_time` of Section 12.

**Review in the Hilbert's-tenth research tree.** Before placement, another
session reviewed all six batch-87 archives at their arrival revision (commit
`f15962acd`):
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_baire_polish_arithmetic_intake.md`,
with `review_baire_polish_arithmetic_intake_independent.md` and the receipt
`review_baire_polish_arithmetic_intake.json` beside it. For this manuscript it
read the delivered lines 64–73, 82–110, 386–428, 776–820 and 927–955 (abstract,
Sections 1–1.3, Section 7 through Lemma 7.4, Section 12, conclusion and
Appendix A). It confirms the sliceable-matching characterization and the
non-executability of blind tables, that the totality promise of Theorem 12.1
is essential, and that the Busy Beaver inequality is conditional on the
encoding and compiler; it finds no fixed-size Diophantine history certificate
or paid arithmetic schedule, so the 84-operation universal polynomial of the
Hilbert's-tenth programme is unaffected; and it did **not** review the
probability, enumeration or asymptotic claims. No scope correction was
needed. The article's Section 1.4 note records this.

**Neighbouring reports.** None shares a theorem or a question; nothing in
ProveIt treats box, hat, guessing or prediction games (search of the tracked
tree at placement, including `2211.10474` and A005271).

- `../games-on-ordinals/` holds different games: in
  `open-query-membership-games` a Seeker asks open-set queries about a hidden
  point (adaptive query strategies and finite-budget certificates, but no
  guess at an unread coordinate); `point-separating-game-values` and
  `ordinal-chomp-transition-at-two` are point-separating games and ordinal
  Chomp.
- `../non-baire-translation-invariant-ideal/` is the nearest in spirit: a ZFC
  construction, from a free ultrafilter, of an ideal without the Baire
  property, the kind of irregular object Research question Q2 asks about for
  the Baire-property version of Theorem 3.1.
- The five sister manuscripts of batch 87 concern Glazer's *other* question
  paper, *A Topological Tennenbaum Theorem* (arXiv:2311.13699), and became
  Parts VI–IX of
  `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic`.
  Different subject, no shared notation. In particular **"Glazer's
  Question 1" there (answered as claimed, unrefereed, in its Part VIII) is not
  Q1 here.**

**Stale claims.** None. The manuscript's repository statements ("No Lean
source claiming these new theorems as already established is included"; the
three interface descriptions) are true at the pin and at the write.

## Notation

The manuscript reuses letters with local meanings: `γ` (growth constant, not
Euler's), `F_n`/`M_n`/`B_n`/`L_n`, `BB_time` and `H` (horizon in Section 12,
entropy in Section 11), `I` (boxes; mutual information), `E` (expectation,
success sets), `C` (a group of players; Cantor space; the series `C(z)`), `D`,
`r`, `R`, `T`, `L`, `Q`/`𝒬_n`/`q`, and `Σ_I` (cylinder, not Borel,
σ-algebra). The table of Section 1.5 fixes each one with its tempting false
reading. No symbol was renamed.

## Labels

Every label carries the prefix `mbg:`. The manuscript's 61 labels were
prefixed before anything cited them and every reference updated (19 `\ref`,
44 `\eqref`); the write added four (`mbg:sec:provenance`, `mbg:sec:notation`,
`mbg:app:ledger`, `mbg:app:audit`): 65 labels. No section, theorem or
equation number of the manuscript moved (checked against a build of the
delivered source); the two new subsections are 1.4 and 1.5.

The writing step also:

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

No statement, proof, number or non-claim of the manuscript was changed.

## Files

```text
README.md                        this guide (replaces the delivered README.md, staged under this name)
article.tex                      the report (delivered article.tex; labels prefixed, [write] notes)
article.pdf                      compiled report, 26 pages (unnumbered title page, then pages 1-25)
code/verify_certificates.py      exact finite enumerations and certificate checks (standard library)
code/formal_series.py            exact rational formal-series coefficients through a chosen degree
code/Makefile                    delivered targets pdf, verify, clean (delivery layout; see below)
data/certificates.json           the four-box non-executable blind rule and the three-box team with P(score >= 2) = 3/4
data/verification_report.json    recorded run of verify_certificates.py
data/formal_series_report.json   recorded run of formal_series.py --degree 10
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery; placement moved the programs and `Makefile`
to `code/` and the three JSON files to `data/`. Not shipped: the delivered
24-page `article.pdf` (332,597 bytes), the delivered README (this file
replaces it) and the checksum manifest `SHA256SUMS` (nine entries, verified
9/9 at placement, dropped by repository policy). They survive in the archive:
`git show fa0a0576e:docs/incoming/glazer_box_games_research.zip > <scratch>/glazer_box_games_research.zip`.
Nothing was excluded as heavy.

Delivered text that names the delivery layout or a file not shipped:
`code/Makefile` (runs `verify_certificates.py`, `formal_series.py` and
`latexmk … article.tex` in one flat directory); both programs (default
outputs `verification_report.json`, `certificates.json` and
`formal_series_report.json` in the current directory);
`data/verification_report.json` and `data/formal_series_report.json` (no
paths). The article's Section 13 names the programs by their delivered
names; a note there gives the shipped paths. The delivered README named
`article.pdf` (its own build), `SHA256SUMS` and the flat layout.

## Rerun the checks (on a scratch copy)

Never run the programs in place without explicit output paths: run without
arguments, `verify_certificates.py` rewrites `verification_report.json` **and
`certificates.json`** in the current directory, and `formal_series.py`
rewrites `formal_series_report.json`. Python 3.10 or newer, standard library
only; do not use `python -O` (`formal_series.py` checks with `assert`). From
this directory, in Git Bash (on a POSIX host use `python3` for `py`):

```sh
D=$(pwd); T=$(mktemp -d)
cp code/verify_certificates.py code/formal_series.py code/Makefile data/*.json "$T/"
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

## Build the PDF

pdfLaTeX with newtxtext/newtxmath, amsthm, geometry, microtype, mathtools,
booktabs, longtable, array, enumitem, xcolor, fancyhdr, titlesec, tcolorbox,
xurl and hyperref; the bibliography is inline. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 26 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 24 pages and one duplicate-destination
warning (`page.1`), removed as described under Labels.

## Provenance

- Sources cited by the manuscript: Glazer, arXiv:2211.10474 (the anchor) and
  arXiv:2312.11902; the FrontierMath competition post with Glazer's author
  profile; Łoś–Marczewski, *Extensions of measure*, Fund. Math. 36 (1949)
  267–276; OEIS A005271; the three ProveIt files above at the pin.
- Repository input: the pin `6fef5383b` (3 October 2026, the batch-85C write
  of `a181199-shifted-rectangles`), an ancestor of the placement.
- Batch 87 of `docs/incoming`, manuscript 02 of six; arrival `fa0a0576e`,
  placement `d151b39ca`, written in the batch-87 write phase (3 October 2026).
  Single source, so the write made no merge choices.
