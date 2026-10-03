# Lexicographic Orders of Well-Orderings of the Surreal Numbers

**Set approximations, the singular birthday transition, set-length words, class orders, and higher-order structure**

This is a research report merged on 2 October 2026 from four manuscripts
written independently on the same day and delivered together in batch 80
(arrival `4e270aa46`, placement `ccc046989`, cluster K3). Author lines: 08
and 09 "Research manuscript prepared for Vladimir Reshetnikov", 11 "Research
report", 12 "Research report prepared for Vladimir Reshetnikov"; sources 09
and 12 call themselves AI-assisted. The report is AI-assisted, unrefereed and
not formalized. Its review in the collection's
[review record](../../REVIEW.md) is **pending**, and it is not yet indexed in
the [formalization ledger](../../FORMALIZATION.md). The four delivered
archives have a written-proof review in the Hilbert's-tenth research tree,
and since 3 October 2026 this merged text has a scoped synthesis review and
a preservation audit there too, whose corrections are applied; see
"Reviews" below.

| Source | Batch-80 manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 11 (base) | 11 | `surreal_well_orders (1).zip` (*Lexicographic Orders of Well-Orderings of the Surreal Numbers: Set Approximations, Class Orders, and Higher-Order Structure*; 2,807 lines, 35-page PDF; dated "3 October 2026", the UTC date of its pin) | `ae7c1e6aa` (2 October 2026, 18:03:53 PDT = 3 October, 01:03:53 UTC) | `ccc046989` | abstract and Status paragraph; Sections 2–3; 5.1, 5.3, 5.7; 6 (before 6.1); 7 (before 7.1); 9–12; 13 (before 13.1); 14 (before 14.1); 15; 16 (before 16.1); 19 (its own subsections 19.1, 19.2, 19.4, 19.5, 19.8, 19.11); 20; 27.1; 29 (before 29.1); Appendix A (before A.1) |
| 12 | 12 | `surreal_well_orders.zip` (*Well-Orders of the Surreal Numbers and Their Lexicographic Geometry*; 1,689 lines, 24-page PDF) | `63bb8b1d9` (18:01:32 PDT) | `ccc046989` | Sections 4.1, 5.4, 6.2 (route), 8 (new), 13.1, 14.1, 16.1 (routes), 18, 19.9, 19.10, 21, 24, 27.2, 28.1, 29.1, A.1, C; Lemmas 5.3, 5.14–5.15 and 19.5; Notes 19.11, 19.21, 19.28 |
| 09 | 09 | `Surreal_Well_Orders_Research.zip` (*Well-orders of the Surreal Numbers: Lexicographic universality, a surreal dense core, and the boundary between sets and classes*; 1,677 lines, 24-page PDF) | `63bb8b1d9` | `ccc046989` | Sections 4.2, 5.5, 5.8, 6.3, 7.1, 11.1, 13.2, 19.3, 19.6, 19.12, 22, 25, 27.3, 28.2, 29.2, A.2, A.3, C; Proposition 19.24; notes in Sections 6, 11 and 19 |
| 08 | 08 | `Surreal_Well_Orders_Research (1).zip` (*Lexicographic Orders of Surreal Well-Orderings: Set-sized spectra, global enumeration orders, and a surreal-sized dense skeleton*; 2,022 lines, 26-page PDF) | `ae7c1e6aa` | `ccc046989` | Sections 4.3, 4.4, 5.2, 5.6, 7.2, 17, 19.7, 23, 26, 27.4, 28.3, 29.3, A.4, A.5, C; notes and printed paragraphs in Sections 5, 6, 7, 11 and 19 |

The two pairs of archives sharing a name (08/09 and 11/12) are **not
editions**: every pair of the four texts has word 8-gram overlap of
0.6–1.1 % (preamble boilerplate), no member file is shared, the pins differ
within each pair, and the result sets differ. None supersedes another; all
four are merged (union). Source 11 is the base: it proves the global-choice
equivalence over GB without set choice (sources 09 and 12 assume set choice,
and source 12 asks the choiceless case), it covers set alphabets, set-length
words, and set-like and unrestricted class well-orders, and it alone
attributes the set-sized general-alphabet theorems to the reals report.

Every result, proof, example, remark, question and limitation of the four
manuscripts is printed. A result proved again by the same argument is
recorded in a numbered **Note** that gives the source's statement, number and
differences; a different argument is printed in full as a marked route;
source-specific results are printed in full where they belong. Each source's
introduction, foundational section, model section, Lean plan, questions,
conclusion, ledger and reproducibility record are printed whole. Text written
for the merge is marked `[merge]`. Appendix D maps every numbered statement of
the four sources to its place here.

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 116 pages (title page unnumbered)
README.md                                this guide
09-core-RESEARCH_STATUS.md               source 09's research status and audit, as delivered
11-raw-orders-repository_audit.md        source 11's targeted repository audit, as delivered
12-singular-RESEARCH_STATUS.md           source 12's research status and audit, as delivered
code/08-skeleton-build.sh                source 08's build script (builds nothing here; see below)
code/08-skeleton-verify_finite.py        source 08's finite checks
code/09-core-build.sh                    source 09's build script (builds nothing here)
code/09-core-finite_checks.py            source 09's finite checks
code/11-raw-orders-finite_checks.py      source 11's finite checks (prints)
code/12-singular-build.sh                source 12's build script (fails here)
code/12-singular-finite_checks.py        source 12's finite checks
data/08-skeleton-verification_results.json   source 08's recorded run
data/09-core-finite_checks.json              source 09's recorded run
data/11-raw-orders-finite_checks_results.txt source 11's recorded run
data/12-singular-finite_checks.json          source 12's recorded run
```

All code, data and the three audit files are byte-identical to the delivery.

## Delivery names

| Source | Delivered | Shipped |
|---|---|---|
| 11 | `surreal_well_orders.tex` | `article.tex`, rewritten as this merged report |
| 11 | `README.txt` | staged at placement as `README.md` with unchanged bytes; replaced by this README |
| 11 | `repository_audit.md` | `11-raw-orders-repository_audit.md` |
| 11 | `finite_checks.py`, `finite_checks_results.txt` | `code/11-raw-orders-finite_checks.py`, `data/11-raw-orders-finite_checks_results.txt` |
| 12 | `RESEARCH_STATUS.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `12-singular-RESEARCH_STATUS.md`, `code/12-singular-build.sh`, `code/12-singular-finite_checks.py`, `data/12-singular-finite_checks.json` |
| 09 | `RESEARCH_STATUS.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `09-core-RESEARCH_STATUS.md`, `code/09-core-build.sh`, `code/09-core-finite_checks.py`, `data/09-core-finite_checks.json` |
| 08 | `build.sh`, `verify_finite.py`, `verification_results.json` | `code/08-skeleton-build.sh`, `code/08-skeleton-verify_finite.py`, `data/08-skeleton-verification_results.json` |

Not shipped (all recoverable with `git show 4e270aa46:"docs/incoming/<archive>.zip"`):
the four delivered PDFs (08 26 pages, 09 24, 11 35, 12 24); the manuscripts
and delivery READMEs of sources 08, 09 and 12; and three checksum manifests
(08 6/6, 09 7/7, 12 7/7 verified at placement; source 11 shipped none).
Nothing was excluded as regenerable (the largest delivered non-PDF file is
126,780 bytes), so there is no data to reconstruct.

Shipped files whose text still uses delivery names or names unshipped files:
`11-raw-orders-repository_audit.md` ("the accompanying article"; its audit
inputs are named by their delivery copies, which are not shipped);
`12-singular-RESEARCH_STATUS.md` (names `data/finite_checks.json`,
`SHA256SUMS.txt` and its own 24-page PDF); `09-core-RESEARCH_STATUS.md`
(describes its own article and build); the three build scripts, which build
`surreal_well_orders.tex` or `article.tex` beside themselves; and the
reproducibility records printed in the report's Appendix A and Section 29,
which name delivery files (annotated there and in Appendix B).

## Labels

Every label carries the prefix `swo:`. Source 11's 60 labels are kept with
that prefix, unchanged after it (`swo:sec:…`, `swo:sw:…`, `swo:cf:…`,
`swo:gl:…`, `swo:thm:…`, `swo:lem:delete`, `swo:prop:universal`,
`swo:app:sources`). Source 12's labels carry `swo:st:`, source 09's `swo:ec:`,
source 08's `swo:sk:`. Numbered statements without a label in their source
carry `swo:`*sub*`:n`*number* (for example `swo:st:n10.4`, source 12's
Corollary 10.4); source 08's equation tags (1)–(13) are printed as
(S08.1)–(S08.13), labelled `swo:sk:eq:t`*n*. Totals: 272 labels — `swo:`
only 92 (60 of source 11, 11 for its unlabelled statements, 21 for the
merge), `swo:st:` 61 (39 + 22), `swo:ec:` 52 (46 + 6), `swo:sk:` 67
(53 + 2 + 12 equation tags). Every one of the 198 labels of the four sources
is present exactly once. Cross-references are typed (lemma, note, …) through
alias counters. No `swo:` label has a Lean mapping.

## Notation (Section 1.3)

`GB` includes **no** choice principle (as in `found:sub:gbconvention` and
the [notation guide](../../NOTATION.md)); sources 09 and 12 work over GB with
set choice when they analyse choice, written `GB + AC`. Renamed, with the
false reading printed in the table: birthday `bd(x)` (11's `ℓ(x)`, 12's
`b(s)`; in 08 and 09 `b` is the baseline enumeration); cutoff `No_{<κ}`
(08's `X_λ`, `X_κ`; 09's `X_θ`; 11's `X_κ`; 12's `S_κ`, which is the reals
report's `S_{<κ}`, not `S_{<κ⁺}`); `𝒲_λ(X)` for 11's `𝒫_λ(X)`; calligraphic
`𝒲` for 12's script `𝒲`; `𝔚_sl(No)`, `𝔚_all(No)` for 12's `SL(No)` (printed
`ℰ`) and `WO_cl(No)`, 09's and 08's `ℰ`; `𝓘` for 09's `𝒯` (injective words;
11's `𝒯` is all words); `𝔹_Ord` for 12's `𝔅`; `≃_e` for 11's `≈_emb`; the
core `𝒫_s(b)` for 09's `𝒞_b` and 08's `𝒫_b`, beside 11's `𝒫_bd(e₀)` (two
codings with the same evaluations). Source 12's "binary coding rank" `ℓ₂` is
the reals report's binary coding length; `rank(x)` is the von Neumann rank.
The notation guide gained one paragraph on these conventions in the same
change.

## What the report claims

Numbers refer to the built `article.pdf`. None is claimed to be historically
first.

1. **Sets of surreals.** For every infinite linear alphabet the cardinality,
   universality, ordinal spectrum, cube spectrum, coding length, extrema and
   adjacency of the enumeration order (Theorem 6.1 and Section 6) — these are
   the reals report's theorems, printed with pointers (Section 6.1), with
   source 12's route (Section 6.2, Theorem 6.8) and source 09's (Section 6.3).
   At birthday cutoffs, `|No_{<κ}| = 2^{<κ}` and its spectra (Corollary 7.1,
   Proposition 7.3), regular-stage saturation (Lemma 7.2, Proposition 12.1),
   and **source 12's dichotomy** (Theorem 8.3): with `μ = 2^{<κ}`, the
   minimal slice `𝒲_μ(No_{<κ})` is equimorphic with `𝔹_{κ·κ}` (ordinal
   product) exactly when `κ` is a singular strong limit and with `𝔹_μ`
   otherwise; `κ = ℶ_ω` is an unconditional example (Example 8.5).
2. **Set-length words.** An explicit order embedding of all set-length surreal
   words into `No` with birthday bounds (Theorem 9.1, Proposition 9.2), exact
   local characters, non-isomorphism with `No` (Theorem 10.1, Corollary
   10.2), the complete obstruction to filling a set cut and successor-length
   words `≅ No` in GBC (Theorem 11.1, Corollary 11.2).
3. **Global choice.** Over GB without set choice, a class well-order of `No`
   exists iff global choice holds (Theorem 13.1, source 11); sources 12 and 09
   prove it over `GB + AC` (Theorem 13.2, Proposition 13.7).
4. **All class well-orders.** A direct lexicographic order of all class
   well-orders of a labelled class, with elementary comprehension, without
   ETR (Theorem 14.2; source 12's route, Theorem 14.7); the canonical initial
   set-like part and convex fibres (Theorem 15.1, Proposition 15.3); exact
   adjacency, by finite residual permutations (Theorem 16.2; source 12's
   Theorem 16.6, Corollary 16.7); relation-code lexicography (Proposition
   17.1, source 08).
5. **Set-like global well-orders** (GBC). Bounded-support codes interpolate
   every uniformly set-indexed cut (Theorem 19.10) and form a class
   isomorphic to `No` (Corollary 19.15); cylinders, approximants, no suprema;
   bounded reflection (Theorem 19.30, source 09); finite support does not
   suffice (Proposition 19.31, source 08); binary-class equimorphism (Theorem
   19.32; source 12's route, Theorem 19.34); no exhaustive uniform coding
   (Theorem 19.37; source 12's stronger Theorem 19.38); omitted ranges and raw
   cuts (Theorems 19.42, 19.43, Corollary 19.46).
6. **Models.** In `(V_κ, 𝒫(V_κ))` for inaccessible `κ`, the unrestricted order
   does not embed into the set-like one (Theorem 20.1), with source 12's exact
   identification of both orders (Theorem 21.1) and source 09's model
   (Theorem 22.1); no definable uniform embedding in `KM + GC` (Theorem 20.2).

## What the report does not claim

Section 1.4 keeps every limitation of every source; none was dropped.

- No novelty for the set-sized general-alphabet layer: it re-proves the
  reals report. Universality and homogeneity of `No` are classical (Ehrlich;
  Hamkins, MathOverflow 57597); the coding behind the choice equivalence is
  a standard well-founded coding.
- No machine verification, no Lean or Rocq build, no new Lean file. The Lean
  module names in the four formalization plans (Sections 20.7, 24, 25, 26) are
  proposals; no such module exists.
- The finite checks verify finite instances only, never a transfinite,
  class-theoretic or cardinal statement.
- Source 11's README says that "the mathematical proofs underwent a separate
  proof review". That is the delivery's statement; no such review is recorded
  in the repository, and the report does not rely on it.
- No class of classes is formed: `𝔚_sl` and `𝔚_all` are predicates on class
  variables. The core realizes uniform set-sized cuts only; source 12's
  bounded theorem is not a full class model at a singular cardinal; the
  research questions are proposals.

## Formal status

Nothing in this report is formalized. Four inputs that the sources use are
proved in Lean on the sign carrier, in the universe-relative form of the
formalization ledger: properness and bounded birthdays (`found:prop:proper`;
`SignSequence`, `birthdays_bounded`, `small_bounded`, `not_small` in
`Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean`); small-cut
filling (`small_cut_fillers` in `SignSequenceCut.lean`,
`exists_separator_of_small_sets` in `SignSequenceCutOperation.lean`); a
separator of exactly a prescribed birthday above all option birthdays, which
is source 08's Theorem 5.6 here (`exists_cut_separator_of_birthday_lt` in
`SignSequenceCut.lean`, proved by the same complete-lattice route); and the
inconsistency of unrestricted cuts (`noUnrestrictedCuts` in
`SizeObstructions.lean`). Every other declaration the sources cite exists at
the current revision; none states a result of this report. Placement in the
surreal collection beside the Lean foundations confers no formal status.

## Where one source answers another (Section 1.7)

- Source 12's question on the weak-choice strength (its Remark 4.2 and
  Question 14.5): **answered** by source 11's Theorem 13.1; printed as
  Remark 27.15, with Remark 13.4.
- Source 08's question 11 (comparing non-set-like class well-orders):
  **answered** by Theorems 14.2 and 14.7.
- Source 08's question 3 (coding lengths at singular cutoffs): answered in
  part by Theorem 8.3; question 2: answered in part by Proposition 12.1.
- The reals report's question "Other ground orders"
  (`lwo:sec:research`, which names set-sized suborders of surreal numbers):
  answered in part by Theorem 8.3, for `X = No_{<κ}` and the minimal stratum;
  open for longer strata and other alphabets.

## Relation to the neighbouring reports

**[lexicographic-well-orderings-of-reals](../../../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/)**
(research-report collection, batch 76) proves the set-sized theorems of
Section 6 for every infinite linear alphabet; they are printed here as
pointers and marked routes, never as new. Source 08 re-derived them from
batch-76 manuscript 02, now that report's base source. Source 12's dichotomy
answers that report's question "Other ground orders" in part.

**[foundations](../foundations/)** supplies the conventions used throughout
(`found:sub:gbconvention`, `found:prop:recursion`, `found:sub:km`,
`found:rem:secondsort`, `found:prop:proper`, `found:prop:allcuts`).

**[birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)**:
the saturation of `No_{<κ}` at regular `κ` (`hset:rem:saturation`, through
`hset:eq:cut-bound`) is classical and is source 11's Lemma 7.2 and source 08's
Note 7.4; its ordinal-graph coding (`hset:thm:choice`) is the set-level form of
the mechanism in Theorem 13.1 (Remark 13.4) and is unchanged.

**[real-vector-space-structure](../../surreal/real-vector-space-structure/)**
uses a set-like global well-order; by Theorem 13.1 that hypothesis is
equivalent to global choice over GB. Its question on the weaker class-choice
principles (`rvs:w:q:foundations`) is unaffected.

**[surreal-fields-across-universes](../surreal-fields-across-universes/)**
studies the saturation of `No_{<κ}` across universes; nothing here depends on
it.

## Build

TeX Live or MiKTeX with lmodern, amsmath/amssymb/amsthm, mathtools, mathrsfs,
geometry, microtype, booktabs, longtable, array, tabularx, enumitem, xcolor,
fancyhdr, listings, tcolorbox, aliascnt, hyperref, xurl and cleveref. No
external figures or bibliography file.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Built with MiKTeX (pdfLaTeX): 116 pages; no errors, undefined references or
citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull boxes.

The corrections of 3 October 2026 (see "Reviews": two words, two dated
notes and one paragraph; no label, macro or bibliography entry) add one
page to the 115 of the first build. The `.aux` of a build of the previous
text has the same 272 labels with the same numbers (544 `\newlabel`
lines, page fields aside); the title page and the three changed pages
(9, 47, 96) were rendered and inspected.

## Rerunning the checks

Run the programs on copies or with explicit outputs, never so that they write
into this directory: source 08's program writes `verification_results.json`
beside itself, and source 09's default `--output` is an unprefixed
`data/finite_checks.json` here. From this directory, with an empty scratch
directory `$S`:

```
cp code/08-skeleton-verify_finite.py "$S/"
python "$S/08-skeleton-verify_finite.py"                  # writes $S/verification_results.json
python code/09-core-finite_checks.py --output "$S/09.json"
python code/11-raw-orders-finite_checks.py > "$S/11.txt"
python code/12-singular-finite_checks.py --output "$S/12.json"
```

Compare with the four records in `data/` using `diff --strip-trailing-cr`.
Rerun on 2 October 2026 with Python 3.14.4 on Windows (`py`), each program
reproduced its record exactly apart from line endings (all four write CRLF on
Windows): 08 5,906 + 7,432 permutation pairs, 21,845 pair-code and 16,129
sign-code comparisons; 09 164,560 assertions, 1,101 separator families, seed
20261002; 11 465 sign-code pairs, 79,800 word-code pairs, 266,272 permutation
pairs (867 adjacent); 12 180,905 cases. All use the standard library only.
The three build scripts are kept as delivered and build nothing in this
layout: `code/08-skeleton-build.sh` runs `verify_finite.py` and compiles
`surreal_well_orders.tex` beside itself, `code/09-core-build.sh` compiles an
`article.tex` in `code/`, and `code/12-singular-build.sh` changes into `code/`
and then calls `code/finite_checks.py`.

## Other discrepancies

- Source 11 is dated 3 October 2026, the UTC date of its pin; the other three
  are dated 2 October 2026.
- Source 08 cites its predecessor as a manuscript "in the user's library";
  it is batch-76 manuscript 02, now the reals report's base source (Section
  4.3 and its note).
- The sources' hypotheses differ for the choice equivalence (GB or `GB + AC`;
  all or only set-like well-orders) and for the diagonal theorem (rows indexed
  by `Ord`, by a class of set codes, or arbitrary uniform families); the
  strongest statement is printed and the weaker ones are recorded as notes or
  routes.
- One reference in source 11's text cited a proposition as "Theorem"
  (Section 12); it is corrected.
- One sentence of source 08 (its lines 765–766, here in Section 5.6) said
  that for non-set-like relations "the model's class collection can matter to
  the well-order assertion". It is replaced by the scoped statement of the
  Hilbert's-tenth review's patch (see "Reviews"): under GBC, internal
  well-foundedness of a fixed class relation is equivalent to the absence of a
  set-coded descending ω-sequence, so enlarging the class collection does not
  change it; what can change is which relations are available. The note
  before Section 5.6 records the original sentence.
- No retraction was made; no claim of another report or README is refuted.

## Reviews

- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_surreal.md`
  (commit `c338541e3`, by the session that maintains that tree): a
  written-proof review of the four delivered archives, with a replay script
  and receipt beside it. It found the principal proof arguments sound under
  the stated foundations, reran the four finite checks and added independent
  finite checks, and proposed one scoped correction to source 08
  (`surreal_research1_wellfounded_scope.patch` there), which this report
  applies in its text (the delivered code is untouched).
- `review_surreal_placement_ccc046989.md` in the same directory (commit
  `3aa123856`): authenticates the placement, 16 byte-exact transfers and 13
  disclosed unstaged members.

Both are pinned to the delivered archives and the placement; neither covers
the text written for this merge, and neither is an entry of the collection's
review record.

Added 3 October 2026: the same tree has since reviewed the merged text
(write commits `d51fafea8` and `0be9b9134`).

- `review_surreal_synthesis_0be9b9134.md` (commit `280583d2f`): reads all
  98 blocks written for the merge, this README and the NOTATION addition;
  no mathematical defect under the stated hypotheses, two minor
  overstatements, and a three-location patch
  `review_surreal_synthesis_0be9b9134.patch`, which **was applied verbatim**
  on 3 October 2026. (1) Remark `swo:rem:answered-choice` and the answered
  question `swo:st:n14.5` called the choice recursion of `swo:cf:choice` a
  "coherent" sequence (well-ordering) of the sets V_α; it is uniformly
  defined, but later orders need not restrict to earlier ones (if W puts
  `-` before `+` and `+-` before `--`, then w_2 puts ∅ before {∅} and w_3
  reverses them), so both now say "uniform(ly defined)". The global-choice
  theorem is unaffected: it uses only the w_rank(A)-least element of each
  set A. Both places carry a dated note crediting the review; the first
  gives the example, and adds that ordering all sets by rank and then by
  w_(γ+1) within rank γ does give a coherent class well-order (not used by
  the proof). (2) "the largest delivered file is 126,780 bytes" now says
  "non-PDF": source 11's TeX is 126,780 bytes, its PDF 543,575 (checked
  against the four archives at this change).
- `review_surreal_transfer_0be9b9134.md` (commit `afb706742`): a
  preservation audit; all 166 formal statements of the four sources are
  accounted for (124 normalized-exact bodies, 41 duplicate-result notes, one
  question kept verbatim inside an answered remark), all 198 original labels
  occur once, and the 14 code/data companions are byte-identical. No
  further defect.
- `review_surreal_reciprocal_a13efdd51.md` (commit `a3cf6e939`) audits the
  reciprocal notes in four other surreal reports, finds no new defect, and
  confirms that they do not repeat the "coherent" wording.

The "Review status" item of the report's Section 1 records the first two in
a dated note. None of these is an entry of the collection's review record,
where this report's review stays pending.
