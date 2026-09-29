# Aligned Fragments and Constrained Crossover

**Undecidability, exact generation depth, and rational growth of context-free recombination closures**

This is a research report dated 29 September 2026, built from one
manuscript. Author line: "Research draft prepared with ChatGPT for Vladimir
Reshetnikov". It answers a question that Charles E. Hughes left open in
arXiv:2608.27755v1: the complexity of deciding `L ⊗_c L = L` for a
context-free language `L`, where `⊗_c` is constrained crossover (see
"Which question of Hughes" below).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (only) | batch 44, manuscript 02 | `ProveIt_Constrained_Crossover` (arrived in `ae28ea2db`; 23-page US-letter PDF) | `9b24a3a8d` | `203016015` | the whole article, apart from text marked `[write]` |

The pin is ProveIt commit `9b24a3a8d545af9624f6ac455f5b548be62818b6`
(recorded in the manuscript's Section 1.1 and in `provenance.md`).

**Status.** AI-assisted and unrefereed. **Not formalized**: no statement of
the report has a Lean or Rocq proof, and the manuscript claims none. The
finite computations are exact audits of finite specializations, not proofs
of the universal statements. The report sits in a repository with Lean and
Rocq developments; that placement gives it no formal status (see "Formal
status" below).

```
article.tex        the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf        the compiled report, 27 US-letter pages (unnumbered title page, contents p. 1,
                   Sections 1-12 pp. 2-23, Appendices A-D pp. 23-25, references pp. 25-26)
README.md          this guide
provenance.md      the manuscript's source record and bounded novelty audit, as delivered
proof-audit.md     the manuscript's author-side proof and edge-case audit, as delivered
code/verify.py     exact finite reference verifier (Python >= 3.10, standard library only)
code/Makefile      the delivered Makefile (pdf, check, clean; see below)
data/verification.json   the delivered receipt: PASS, 1,766,639 checks
data/verification.txt    console output of the delivered run
```

Delivery names and shipped paths: `notes/provenance.md` -> `provenance.md`,
`notes/proof-audit.md` -> `proof-audit.md`, `Makefile` -> `code/Makefile`;
`code/verify.py` and `data/verification.{json,txt}` keep their delivered
paths. All six are byte-identical to the delivery. Not shipped: the delivered
`article.pdf` (this directory's PDF is a build of the written `article.tex`)
and the delivered `README.md` (replaced by this file; it is in the placement
commit `203016015`). The package had no checksum ledger.

Delivered files whose text still uses delivery names or describes the
package rather than this report:

- `code/Makefile` runs `python3 code/verify.py` and `latexmk` on
  `article.tex` from the package root; see "Building" and "Rerunning".
- `code/verify.py` writes its receipt to `../data/verification.json`
  relative to its own directory, that is, **over this report's shipped
  receipt** when run in place.
- `data/verification.txt` ends with the receipt path of the delivered run
  (`/mnt/data/ProveIt_Constrained_Crossover/data/verification.json`).
- `provenance.md` speaks of "this package" and says no file of the
  repository was edited; that describes the delivery, not the write phase.
- The article's own Section 10.2 lists the delivered package layout
  (`notes/`, root `Makefile`, `article.pdf`); a `[write]` note there gives the
  shipped paths.

## Labels

Every label in `article.tex` carries the prefix `ccc:`. The manuscript's 71
labels were given the prefix when the report was written, and every `\ref`
and `\eqref` was updated with it. Five labels were added: `ccc:sec:sibling`,
`ccc:sec:notation`, `ccc:app:provenance` (new `[write]` sections),
`ccc:sec:lean` (the manuscript's Section 11.1) and `ccc:q:arithmetical` (its
Question 11.1): 76 in total. Compared with a build of the delivered text, no
theorem, section, equation or question number changed.

## Which question of Hughes

Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion,
Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1 (27 August
2026; 13 pages, printed page numbers equal to PDF page numbers). Checked
against that PDF when this report was written:

- Section 2 ("Definitions and Notations", p. 2) defines unconstrained
  crossover `⊗_u` and constrained crossover `A ⊗_c B = {wz, yx : wx ∈ A,
  yz ∈ B, |w| = |y|, |x| = |z|}`, the operation of this report (same
  symbol).
- **Section 4 ("Foundational Results"), under "Single step equality"**:
  Theorem 1 and its Corollary make single-step equality undecidable for
  operators that contain concatenation (simple insertion, shuffle,
  unconstrained crossover). The note after the Corollary (p. 3) says that
  constrained crossover fails this criterion, so the complexity of the
  question "does L ⊗_c L = L?" is open; the list of open questions that
  follows repeats it for a context-free `L` (its second item, top of p. 4).
  This is the question the report answers (its Theorem 4.2).
- Section 14 (p. 12) lists "Study constrained crossover" among its open
  directions without a specific question; the report's `[write]` note after
  Question 11.9 says how its results bear on Hughes's other Section 13-14
  questions (for crossover only).

The delivered abstract says "Section 4", and the delivered README and
bibliography say "printed page 3"; both are correct.

## What is claimed

Constrained one-point crossover: equal-length parents exchange suffixes at
the same cut (endpoint cuts allowed); `T(L) = L ⊗_c L`, parallel iterates
`L^[k]`, frozen-source iterates `Y_k` (one parent always from `L`).

- **Exact rank calculus** (Section 3): the aligned-fragment rank satisfies
  `rank_{T(L)}(w) = ⌈rank_L(w)/2⌉` (Theorem 3.2); `L^[k] = {w : rank ≤ 2^k}`,
  depth `⌈log₂ rank⌉`, and the union of all generations is the coordinate
  hull (Theorem 3.3); the ranks on a slice have no gaps (Theorem 3.4); sharp
  slice stabilization by `⌈log₂ n⌉` (Corollary 3.5, Example 3.6,
  Corollary 3.7); frozen-source depth `rank − 1` (Theorem 3.8).
- **One-step undecidability** (Theorem 4.2): deciding `L ⊗_c L = L` for a
  context-free grammar is co-r.e.-complete, already over `{0,1,@}`, even on
  a family whose first generation is universal; no computable bound on
  shortest counterexamples (Corollary 4.3). This answers Hughes's question.
- **Finite stabilization** (Section 5): exact rank `r + 1` for `r` repeated
  forbidden blocks (Theorem 5.1); eventual stabilization undecidable over
  `{0,1,@,#}`, each fixed adjacent equality co-r.e.-complete (Theorem 5.2;
  frozen-source version Corollary 5.3); the eventual-stabilization set is in
  `Σ⁰₂` and `Π⁰₁`-hard (Proposition 5.4).
- **Fixed target** (Proposition 6.1): rank and generation of one word are
  computable in `O(g n^5)` time from a CNF grammar.
- **Regular inputs** (Section 7): a polynomial DFA one-step test with
  counterexamples of length at most `2s³ − 1` (Theorem 7.1); PSPACE-complete
  one-step problem for NFAs over a fixed ternary alphabet (Theorem 7.2); a
  distance automaton with at most `s·4^s` states whose value is rank − 1
  (Theorem 7.3); finite stabilization decidable, with an EXPSPACE upper bound
  for DFA input that is not claimed optimal (Corollary 7.4).
- **Counting** (Section 8): the full closure of every context-free seed has
  an effectively rational commutative generating function, commuting letter
  weights retained (Theorem 8.3, Corollary 8.4).
- **Non-context-free closure** (Section 9): the binary linear seed `S_q`
  (`q ≥ 3`) has a non-context-free closure `K_q` (Theorem 9.2) with
  `|(K_q)_n| = 4^⌊n/q⌋` and exact generation counts (Theorem 9.3); the
  minimal recurrence order of generation `k` is `q·2^k + 1`, and `q(k+1) + 1`
  for the frozen source (Theorem 9.4).
- **Audit** (Section 10.1): 1,766,639 exact checks, all passing: all 65,814
  binary seed sets of lengths 0-4 (1,050,698 target-rank queries), all 64
  complete two-state binary DFAs (8,128 queries), 255 guard repairs, block
  amplification for 1-64 blocks, the linear-seed family for `q = 3..7` up to
  length 12, and 25 recurrence pairs.

## What is not claimed

Kept from the manuscript: an unrefereed draft, not a proof-assistant
development; the bounded literature search is not a priority claim, and
equivalents in recombination, splicing or genetic-algorithm literature have
not been excluded; the coordinate-hull (product) observation is not claimed
as a first discovery; CFG universality, effective Parikh semilinearity,
Presburger counting (Woods) and distance-automaton limitedness (Kirsten) are
imported, not reproved; the guard construction alone cannot prove
undecidability of eventual stabilization; `Σ⁰₂`-completeness is not claimed
(Question 11.1); the EXPSPACE bound is not claimed optimal and the
`O(g n^5)` bound not optimal; rationality of the commutative series implies
neither regularity nor context-freeness of the closure; the finite audits do
not implement a general CFG compiler, Presburger counting engine or
limitedness solver, and the executable verifier specializes to finite seeds
and DFAs; the research questions other than Hughes's are not asserted to be
new or globally open; the Lean section is a plan. The report does not solve
the both-singleton insertion conjecture and does not reprove the sibling
report's spectrum realizations. Its results for crossover answer none of
Hughes's questions about insertion or shuffle.

## Relation to neighbouring reports

- **`automata-and-formal-languages/insertion-degree-spectra`** (*Gaps in
  Bounded-Shuffle Hierarchies*, the "ProveIt report" of the manuscript's
  Section 1.1, read at the pin; unchanged from the pin to the placement).
  Both reports start from Hughes's preprint, from different parts of it.
  That report answers questions of Hughes's Sections 10-11 on insertion
  degrees and iteration depth; its scope sentence says it addresses "the
  indicated no-gap questions, not the surrounding undecidability results",
  and it never names the crossover question. This report answers one of
  those surrounding decision problems (Section 4), for crossover. No theorem
  is shared or used across the two. This report's no-gap theorem for aligned
  rank (Theorem 3.4) is an analogue, for another operation, of that
  report's iteration-depth no-gap theorem (its Theorem 8.2); that report
  iterates with the inserted language held fixed, so its closest crossover
  counterpart here is the frozen-source iteration (Theorem 3.8). Hughes's
  singleton conjecture (that report's Question 21.1) stays open. Article
  Section 1.4 sets this out; that report carries a dated reciprocal remark
  under its scope sentence.
- No other report of the research-report or surreal collections treats
  crossover of languages or cites Hughes's preprint (searched: crossover,
  Hughes, 2608.27755; the other reports using the word "crossover" use it in
  unrelated senses). `shuffle-six-state-bound` in this category concerns the
  state complexity of shuffle and shares no theorem with this report.

## Formal status

ProveIt has no formal development of crossover, aligned rank, context-free
grammars, Post correspondence, Parikh images, Presburger counting or
distance-automaton limitedness (the vendored
`lib/Coq-Library-Undecidability` snapshot contains no grammar or PCP
files). The nearest formal neighbour is `Logic/PresburgerArithmetic`, whose
Lean development proves Cooper quantifier elimination for Presburger
arithmetic over the integers:
`PresburgerArithmetic.Formula.holds_iff_quantifierEliminate` and the
decision procedure `PresburgerArithmetic.Formula.presburgerArithmetic_decidable`
(`Logic/PresburgerArithmetic/Lean/PresburgerArithmetic/Decision.lean`), with
an independent Rocq proof of the one-variable Cooper step
(`Logic/PresburgerArithmetic/Coq/Cooper.v`). The report's Lemma 8.2 and
Appendix B invoke quantifier elimination of this kind as an effectivity
step, but they are not connected to that development, and the counting
theorem they need is not formalized. **Not formalized:** every statement of
the report. No Lean build was run for it.

## Setting and notation

Article Section 1.5 has the table. No symbol of the manuscript was renamed.
To watch: `⊗_c` is Hughes's constrained crossover (his `⊗_u` contains
concatenation); `L^[k]` is the parallel iteration, whereas Hughes's iterated
operations, read as for his iterated insertion, give the frozen-source `Y_k`
when both inputs are `L`; `ρ_L(w)` (aligned-fragment rank) and `d_L(w)`
(generation depth) are not the sibling report's insertion degree
`d_{A,B}(w)`; "no gaps" here concerns ranks on a slice, not insertion
spectra, which can have gaps. Words are indexed with zero-based boundaries,
`w[i:j]` being positions `i+1..j`. The write added a note after Remark 2.3:
Hughes's remark that iterated constrained crossover can lose earlier words
applies to two different inputs, not to self-crossover under either clock.

## Building

In a scratch directory holding a copy of `article.tex`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built this way with MiKTeX pdfLaTeX (packages include
newtx, `shuffle`, fancyhdr, listings, tikz, hyperref; no BibTeX step): 27
pages, 0 errors, 0 warnings, 0 overfull or underfull boxes, no undefined or
multiply-defined references and no duplicate destinations. The title page
is excluded from page anchors. Do not run `make pdf` or `make clean`
(`code/Makefile`) in this directory: they would leave `latexmk` auxiliary
files here. GNU `make` is not installed on the reference machine anyway.

## Rerunning the checks

Never run the verifier in place: it overwrites `data/verification.json`
(and `make -f code/Makefile check` from the report root does the same). Run
it on a copy that keeps the `code/` + `data/` layout:

    mkdir run && cd run
    cp -r <report>/code <report>/data .
    py code/verify.py          # Python >= 3.10, standard library; python3 elsewhere

It prints the lines of `data/verification.txt` and rewrites
`run/data/verification.json`. When this report was written it was rerun this
way with Python 3.14.4: PASS with 1,766,639 checks in about 36 seconds; the
rewritten JSON equals the shipped one except for `elapsed_seconds` (and is
written with CRLF line endings on Windows), and the console output differs
from `data/verification.txt` only in the elapsed time and the receipt path.
Checks raise exceptions rather than use `assert`, so they stay active under
`python -O`.

## Other discrepancies

- The delivered PDF was 23 pages; this build is 27, because of the `[write]`
  text (Sections 1.4-1.5, notes in Sections 1.1, 2, 10 and 11, Appendix D).
  The page size stays US letter.
- The manuscript cites the sibling report by its article title, *Gaps in
  Bounded-Shuffle Hierarchies*; its directory is `insertion-degree-spectra`.
- `data/verification.json` records the delivered run's `elapsed_seconds`
  (11.498), a machine timing.
