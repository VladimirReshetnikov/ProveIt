# Lexicographic Orders of the Well-Orderings of the Reals

**Ordinal spectra, coding length and representation rank, finite-tail geometry, characters, gaps, and self-absorption**

This is a research report dated 2 October 2026, merged from three
manuscripts that were written independently on the same question and
delivered together in batch 76. Author line of all three: research
manuscript or report "prepared for Vladimir Reshetnikov". The report is
AI-assisted, unrefereed and not formalized.

| Source | Batch-76 manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 02 (base) | 02 | `lexicographic_well_orderings_of_reals.zip` (*Lexicographic Orders of Well-Orderings of the Continuum: ordinal spectra, lexicographic complexity, finite-tail geometry, and self-absorption*; 1,826 lines, 24-page PDF) | `6ea60e367` | `2a04b60f2` | Sections 2–16, Appendices A–B |
| 06 | 06 | `Lexicographic_Well_Orderings_of_Reals (1).zip` (*The Lexicographic Order of All Well-Orderings of the Real Line: universality, exact ordinal spectra, finite tails, local characters, and Dedekind gaps*; 1,522 lines, 23-page PDF) | `6ea60e367` | `2a04b60f2` | routes and notes in Sections 2–16 (this stage) |
| 07 | 07 | `lexicographic_well_orderings_research.zip` (*Lexicographic Orders of Real Well-Orderings: ordinal universality, representation rank, products, and cut geometry*; 1,521 lines, 21-page PDF) | `6ea60e367` | `2a04b60f2` | routes and notes in Sections 2–16, Corollaries 5.6 and 8.4 (this stage) |

All three archives arrived in `6914ccca6`. The pin of every source is
`6ea60e3677bd847a00baf023c3c532c83884530e` (the batch-75 placement): source
02 records it in its Appendix B and in `02-strata-RESEARCH_STATUS.md`, source
06 in its Section 1.1 and in `06-spectra-research_audit.md`, source 07 in its
Section 13.2 and in `07-rank-source_audit.md`.

**This is the first stage of the merge.** `article.tex` prints source 02 in
full, with the routes of sources 06 and 07 marked at every shared theorem,
the two in-batch answers that attach to source 02's text (Corollary 8.4 and
Remark 8.5), source 07's real-power strictness (Corollary 5.6), the notation
table and the theorem crosswalk. The results proved only by sources 06 and 07
are listed in the crosswalk (Appendix C) as "not yet printed".

```
article.tex                               the report, standalone LaTeX with an internal bibliography
article.pdf                               the compiled report, 33 pages
README.md                                 this guide
02-strata-RESEARCH_STATUS.md              source 02's status and source provenance, as delivered
06-spectra-research_audit.md              source 06's research and proof audit, as delivered
07-rank-source_audit.md                   source 07's source and proof audit, as delivered
code/02-strata-finite_checks.py           source 02's finite checks (standard library)
code/06-spectra-finite_checks.py          source 06's finite checks (standard library)
code/06-spectra-build.sh                  source 06's three-pass pdflatex script for its own manuscript (see below)
code/07-rank-finite_checks.py             source 07's finite checks (standard library)
data/02-strata-finite_checks.json         source 02's recorded run: 552,450 checks, status "passed"
data/06-spectra-finite_checks_results.json  source 06's recorded run, status "PASS"
data/07-rank-finite_checks_results.json   source 07's recorded run, status "all finite assertions passed"
```

### Delivery names and shipped paths

| Source | Delivered | Shipped as |
|---|---|---|
| 02 | `article.tex` | `article.tex`, rewritten as this merged report |
| 02 | `README.md` | replaced by this README |
| 02 | `RESEARCH_STATUS.md` | `02-strata-RESEARCH_STATUS.md` |
| 02 | `finite_checks.py` | `code/02-strata-finite_checks.py` |
| 02 | `finite_checks.json` | `data/02-strata-finite_checks.json` |
| 06 | `research_audit.md` | `06-spectra-research_audit.md` |
| 06 | `finite_checks.py` | `code/06-spectra-finite_checks.py` |
| 06 | `finite_checks_results.json` | `data/06-spectra-finite_checks_results.json` |
| 06 | `build.sh` | `code/06-spectra-build.sh` |
| 07 | `source_audit.md` | `07-rank-source_audit.md` |
| 07 | `finite_checks.py` | `code/07-rank-finite_checks.py` |
| 07 | `finite_checks_results.json` | `data/07-rank-finite_checks_results.json` |

Not shipped (they survive in the archives of `6914ccca6`): the three
delivered PDFs; source 02's `SHA256SUMS.txt` (6/6 verified at placement);
the manuscripts and READMEs of sources 06 and 07. Recover any of them with
`git show 6914ccca6:"docs/incoming/<archive>.zip" > <scratch>/<archive>.zip`.
Every shipped file except `article.tex`, `article.pdf` and this README is
byte-identical to the delivery.

The delivered files still use delivery names: the docstrings of the three
`finite_checks.py` programs name `finite_checks.py`,
`finite_checks.json` and `finite_checks_results.json`; source 02's status
file speaks of "the PDF" and "the supplied TeX" (its own, not shipped);
source 06's and 07's audits name `article`, `finite_checks.py` and
`finite_checks_results.json`; source 07's audit names its companion
`README.md`. `code/06-spectra-build.sh` changes to its own directory and runs
pdflatex on an `article.tex` there; in `code/` there is none, and the
manuscript it was written for is not shipped, so it does not build anything
here. Use the build command below instead.

## Labels

Every label carries the prefix `lwo:`. Source 02's 74 labels are kept,
unchanged after the prefix. Material from source 06 carries `lwo:sp:` and
material from source 07 `lwo:rk:`; front matter added at the merge carries
plain `lwo:`. At this stage the article has 88 labels: 74 of source 02,
10 `lwo:` labels of the merge front matter and crosswalk, two `lwo:sp:`
(the next-value decomposition and the cellularity remark) and two `lwo:rk:`
(real-power strictness and the no-fixed-power corollary).

Text added at the merge is tagged **[merge]** in the article; everything
untagged in Sections 2–16 and Appendices A–B is source 02 as delivered.

## Notation

Section 1.4 of the article fixes one notation for the three sources and
lists every renamed symbol. The main points: the minimal-type slice is
`W_κ` (source 06's and source 07's 𝒫, which is not the power set); the
Kanovei–Shelah index is 𝒜; the binary cube is 𝔹_θ and the real power
ℝ^γ_lex; both complexity invariants are kept, source 02's binary coding
length ℓ₂ and source 07's real representation rank repr_ℝ, which satisfy
repr ≤ ℓ₂ ≤ ω·repr and agree on 𝒲 and 𝒲_κ but not in general; cf κ is
written out (source 07's θ); cellularity is `cell`, never `c`.

## What is claimed

In ZFC, with κ the continuum as an initial ordinal and 𝒲 the order of all
well-orderings of ℝ compared at the first unequal real entry (proved by all
three sources unless noted):

- |𝒲| = |𝒲_κ| = |𝒜| = 2^κ; every linear order of size at most κ embeds;
  an ordinal β embeds exactly when β < κ⁺, also reversed.
- 𝒲_κ, 𝒜 and every fibre 𝒜_U are equimorphic with 𝔹_κ (02, 07; 06 for
  𝒲_κ).
- Binary coding length ℓ₂(𝒲) = κ⁺; 𝔹_θ ↪ 𝒲 exactly for θ < κ⁺ (02);
  real powers ℝ^γ_lex ↪ 𝒲 exactly for γ < κ⁺ (02, 07).
- 𝒲 embeds into no bounded union of strata, hence not into 𝒲_κ, 𝒜, or any
  ℝ^γ_lex or 𝔹_γ with γ < κ⁺ (02, 07). This answers source 06's Research
  question 14.1, which 06 had settled only under 2^{<κ} < 2^κ.
- Every stratum: 𝒲_{λ+n} ≃ 𝔹_λ ×_lex n!, with exact lengths and
  comparison between strata (02 only).
- Power absorption 𝒲^γ_lex ≃ 𝒲 exactly for 0 < γ < κ⁺; (𝒲_κ)^γ and 𝒜^γ
  are equimorphic with 𝔹_{κ·γ} (02, 07).
- Adjacency criterion, finite blocks of size n!, isolated points; global
  topology of 𝒲 and of 𝒲_κ; topology of 𝒜; unfilled (ω, ω) cuts;
  completion invariants (02, with routes of 06 and 07).
- Strictness of real powers ℝ^α ↪ ℝ^β ⇔ α ≤ β (Kuhlmann 1995, Corollary
  2.4; source 07's proof is printed as a second route).

## What is not claimed

- No historical priority: none of the three sources claims it. Source 07's
  real-power strictness is Kuhlmann's classical theorem; source 02's cube
  hierarchy is Corollary `cor:strict` of the point-separating report
  (below); source 06 attributes characteristic-function coding to the
  standard literature.
- No peer review and no machine verification. The finite checks test
  finite instances only; they verify no transfinite statement.
- No intrinsic criterion for an arbitrary order to embed into 𝒲.
- Repository and literature searches of all three sources were targeted.
- The research questions are proposed continuations, not catalogued open
  problems.

## Relation to the neighbouring reports and the formal project

- [`games-on-ordinals/point-separating-game-values`](../games-on-ordinals/point-separating-game-values/):
  source 02's strict cube hierarchy (Theorem 5.3) re-proves its Corollary
  `cor:strict` (`ordinal_separation.tex`, lines 633–641); the article cites
  it first and prints source 02's cylinder proof as a second route. Source
  02's coding length ℓ₂(L) is that report's game value ps(L^dd) by its
  Theorem `thm:embedding` (equation `eq:embedding-rank`), so ps(𝒲^dd) = κ⁺.
- `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`
  is cited by source 06 as context for bounded sign orders. None of its
  declarations states a result of this report.
- `transfinite-words` concerns wqo-type embeddings of finite-alphabet words,
  not lexicographic orders of enumerations; there is no overlap.
- Placement beside the Lean development of the Cardinals project confers no
  formal status: no declaration of the repository formalizes any statement
  of this report.

## Build

TeX Live or MiKTeX with amsmath, amsthm, mathtools, newtx, geometry,
microtype, xcolor, booktabs, array, tabularx, longtable, enumitem,
fancyhdr, tcolorbox, hyperref, xurl and cleveref. No external figures or
bibliography database.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 33 pages and no errors, undefined
references or citations, multiply defined labels, duplicate destinations,
LaTeX or package warnings, or overfull or underfull boxes. Source 02's
delivered text builds equally cleanly to 24 pages.

## Rerunning the finite checks

Each program uses only the Python standard library (Python 3.10 or later)
and runs in a few seconds. Each writes its JSON to the path given by
`--output`, defaulting to a file in the **current directory**, so pass an
explicit scratch path and never a shipped `data/` file. Do not use
`python -O` (source 06's program refuses it). From the report directory:

```sh
py code/02-strata-finite_checks.py --output <scratch>/02.json
py code/06-spectra-finite_checks.py --output <scratch>/06.json
py code/07-rank-finite_checks.py --output <scratch>/07.json
```

On Windows the programs write CRLF line endings; the reruns made at
placement (Python 3.14.4) matched the recorded files after removing the
carriage returns, except that source 06's JSON records the Python version
(3.13.5 in the delivered run). Compare with, for example,
`diff <(tr -d '\r' < <scratch>/02.json) data/02-strata-finite_checks.json`.

## Discrepancies

- Source 02 cites the Kanovei–Shelah index as Section 1 of their paper and
  page 2 of the arXiv PDF; source 07 cites §2, printed page 160 of the
  published version. Both quote the same definition. The section numbering
  was not rechecked at the merge.
- Source 07 states the fixed-length power result as
  (𝒲_κ)^β ≃ ℝ^{κ·β}_lex; source 02 as (𝒲_κ)^β ≃ 𝔹_{κ·β}. These are the
  same statement, since ω·κ·β = κ·β; the article says so instead of calling
  either stronger.
