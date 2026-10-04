# Lexicographic Orders of the Well-Orderings of the Reals

**Ordinal spectra, coding length and representation rank, finite-tail geometry, characters, gaps, and self-absorption**

This is a research report dated 2 October 2026, merged from three
manuscripts that were written independently on the same question and
delivered together in batch 76. Author line of all three: research
manuscript or report "prepared for Vladimir Reshetnikov"; none carries AI
wording in its author line. The report is AI-assisted, unrefereed and not
formalized.

| Source | Batch-76 manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 02 (base) | 02 | `lexicographic_well_orderings_of_reals.zip` (*Lexicographic Orders of Well-Orderings of the Continuum: ordinal spectra, lexicographic complexity, finite-tail geometry, and self-absorption*; 1,826 lines, 24-page PDF) | `6ea60e367` | `2a04b60f2` | Sections 2–14 and 25–26, Appendices A–B |
| 06 | 06 | `Lexicographic_Well_Orderings_of_Reals (1).zip` (*The Lexicographic Order of All Well-Orderings of the Real Line: universality, exact ordinal spectra, finite tails, local characters, and Dedekind gaps*; 1,522 lines, 23-page PDF) | `6ea60e367` | `2a04b60f2` | Sections 15–18, 20 (with 07), 21 (with 07) and 22; Remark 8.5; routes and notes in Sections 2–14; questions in Section 26; Section 27 |
| 07 | 07 | `lexicographic_well_orderings_research.zip` (*Lexicographic Orders of Real Well-Orderings: ordinal universality, representation rank, products, and cut geometry*; 1,521 lines, 21-page PDF) | `6ea60e367` | `2a04b60f2` | Sections 19, 23 and 24, parts of 17, 18, 20 and 21; Corollaries 5.6 and 8.4; routes and notes in Sections 2–14; questions in Section 26; Section 27 |

All three archives arrived in `6914ccca6`. The pin of every source is
`6ea60e3677bd847a00baf023c3c532c83884530e` (the batch-75 placement): source
02 records it in its Appendix B and in `02-strata-RESEARCH_STATUS.md`, source
06 in its Section 1.1 and in `06-spectra-research_audit.md`, source 07 in its
Section 13.2 and in `07-rank-source_audit.md`. The three texts share no
member file; their word 8-gram overlap is 0.65–0.75 % pairwise. None is a
version of another, and none supersedes another.

Every result, proof, example, remark, question and limitation of the three
manuscripts is printed. They prove the same core three times
(prefix-freeness, cardinality, universality, the ordinal spectrum below κ⁺,
𝒲_κ ≃ 𝔹_κ, adjacency, the n! blocks, the topology of 𝒲 and 𝒲_κ); sources
02 and 07 also share coding rank, real powers, absorption, the fixed-length
powers and the Kanovei–Shelah index; sources 06 and 07 share the
point-character spectrum, the gap spectrum of 𝒲 and the dense quotient. Each
shared theorem is printed once, with the other sources' arguments as notes
("also source 06, Theorem 5.2, 06:465, same argument") or, where the argument
differs, as marked second or third routes. Appendix C is the crosswalk of
every numbered statement of the three sources.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 55 pages
README.md                                   this guide
02-strata-RESEARCH_STATUS.md                source 02's status and source provenance, as delivered
06-spectra-research_audit.md                source 06's research and proof audit, as delivered
07-rank-source_audit.md                     source 07's source and proof audit, as delivered
code/02-strata-finite_checks.py             source 02's finite checks (standard library)
code/06-spectra-finite_checks.py            source 06's finite checks (standard library)
code/06-spectra-build.sh                    source 06's three-pass pdflatex script for its own manuscript (see below)
code/07-rank-finite_checks.py               source 07's finite checks (standard library)
data/02-strata-finite_checks.json           source 02's recorded run: 552,450 checks, status "passed"
data/06-spectra-finite_checks_results.json  source 06's recorded run, status "PASS"
data/07-rank-finite_checks_results.json     source 07's recorded run, status "all finite assertions passed"
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
the manuscripts and READMEs of sources 06 and 07, whose text is merged into
`article.tex`. Recover any of them with
`git show 6914ccca6:"docs/incoming/<archive>.zip" > <scratch>/<archive>.zip`.
Every shipped file except `article.tex`, `article.pdf` and this README is
byte-identical to the delivery.

The delivered files still use delivery names: the docstrings of the three
`finite_checks.py` programs name `finite_checks.py`,
`finite_checks.json` and `finite_checks_results.json`; source 02's status
file speaks of "the PDF" and "the supplied TeX" (its own, not shipped);
source 06's and 07's audits name the article, `finite_checks.py` and
`finite_checks_results.json`; source 07's audit names its companion
`README.md`. `code/06-spectra-build.sh` changes to its own directory and runs
pdflatex on an `article.tex` there; in `code/` there is none, and the
manuscript it was written for is not shipped, so it builds nothing here. Use
the build command below instead.

## Labels

Every label carries the prefix `lwo:`; there are 150. Source 02's 74 labels
are kept, unchanged after the prefix. Material from source 06 carries
`lwo:sp:` (43 labels) and material from source 07 `lwo:rk:` (21 labels);
the merge's own sections and tables carry plain `lwo:` (12 labels). A
statement proved by both 06 and 07 carries the prefix of the source whose
statement and proof are printed (06 for the characters, the gap spectrum of
𝒲 and the quotient). No `lwo:` label has a Lean or Rocq mapping.

The first write commit printed source 02 with routes, front matter and
crosswalk (88 labels); the second added Sections 15–24, the merged research
questions and conclusions, and the appendix material of sources 06 and 07
(62 labels). Text added at the merge is tagged **[merge]**; everything
untagged in Sections 2–14, 25–26 and Appendices A–B is source 02 as
delivered, and Sections 15–24 and 27 open with a tagged note naming their
source.

## Notation

Section 1.4 of the article fixes one notation for the three sources and
lists every renamed symbol. The renamings are changes of letter only:

- the minimal-type slice is 𝒲_κ (source 06's and source 07's 𝒫; source 07's
  𝒫 is **not** the power set 𝒫(ℕ), which it also uses);
- the Kanovei–Shelah index is 𝒜 (source 07's macro `\KS`), its ultrafilter
  U (source 07's D);
- the binary cube is 𝔹_θ (06: (^θ2, <lex); 07: 2^θ_lex) and the real power
  ℝ^γ_lex;
- both complexity invariants are kept: source 02's binary coding length ℓ₂
  and source 07's real representation rank repr_ℝ. They satisfy
  repr ≤ ℓ₂ ≤ ω·repr and agree on 𝒲 (κ⁺) and on 𝒲_κ and 𝒜 (κ), but not in
  general (repr(ℝ) = 1, ℓ₂(ℝ) = ω);
- cf κ is written out (source 07's θ, because θ is an ordinal variable
  here), and 2^{<κ} too (source 07's τ);
- cellularity is `cell`, never `c` (sources 06 and 07 write c);
- gap sides are (L, U) (source 07's (A, B));
- the quotient by finite condensation is 𝒲/∼_fin (source 06's D, source
  07's 𝒲_fc);
- source 06's J (injections κ → ℝ) is 𝓘, and source 07's J (bijections
  κ → 𝒫(ℕ)) is 𝒥: the two sources use the same letter for different orders.

## What is claimed

In ZFC, with κ the continuum as an initial ordinal and 𝒲 the order of all
well-orderings of ℝ compared at the first unequal real entry:

- |𝒲| = |𝒲_κ| = |𝒜| = 2^κ; every linear order of size at most κ embeds,
  even into every single slice 𝒲_β (06); an ordinal β embeds exactly when
  β < κ⁺, also reversed (02, 06, 07).
- 𝒲_κ, 𝒜 and every fibre 𝒜_U are equimorphic with 𝔹_κ and ℝ^κ_lex (02, 07;
  06 for 𝒲_κ).
- ℓ₂(𝒲) = κ⁺ (02) and repr(𝒲) = κ⁺ (07), against κ for 𝒲_κ and 𝒜; 𝔹_θ and
  ℝ^γ_lex embed in 𝒲 exactly below κ⁺ (02, 07).
- 𝒲 embeds into no bounded union of strata, hence not into 𝒲_κ, 𝒜, or any
  ℝ^γ_lex or 𝔹_γ with γ < κ⁺ (02, 07). This answers source 06's Research
  question 14.1, which 06 had settled only under 2^{<κ} < 2^κ.
- Every stratum 𝒲_{λ+n} ≃ 𝔹_λ ×_lex n!, with exact lengths and comparison
  between strata (02).
- Power absorption 𝒲^γ_lex ≃ 𝒲 exactly for 0 < γ < κ⁺, not as an
  isomorphism (02, 07); fixed-length powers are equimorphic with 𝔹_{κ·γ}
  (02, 07).
- Adjacency, the finite blocks of size n!, isolated points (02, 06, 07); the
  isolated points are dense and the remainder is perfect, nowhere dense and
  zero-dimensional (06).
- The point-character spectrum {(u, v) ∈ K² : u = v or min(u, v) ≤ ω},
  K = {1} ∪ Reg(≤ κ) (06, 07); the gap spectrum of 𝒲,
  {(ω, ρ), (ρ, ω) : ρ ∈ Reg(≤ κ)}, so every gap has a countable side, with
  exactly 2^κ gaps (06, 07).
- The gap spectrum of 𝒲_κ, which contains (cf κ, cf κ); hence 𝒲_κ has no
  convex copy in 𝒲 (07). The canonical lexicographic-sum decomposition of 𝒲
  over injections κ → ℝ and the missing exhaustive branches (06).
- The quotient 𝒲/∼_fin is dense and equimorphic with 𝒲, with a connected
  completion of size 2^κ (06, 07). This answers source 02's question.
- Topology of 𝒲_κ and 𝒜: density, cellularity and weight 2^{<κ}, clopen
  bases (02, 06, 07), P-spaces (07); 𝒜 has gaps (ω, ω) and (cf κ, cf κ)
  (02, 07).
- Bounded surreal sign orders S_{<θ} embed for θ < κ⁺, S_{<κ⁺} does not (06).
- A well-ordering-based ultrafilter index 𝒥 covering every free ultrafilter,
  equimorphic with ℝ^κ_lex (07).
- Strictness of real powers ℝ^α ↪ ℝ^β ⇔ α ≤ β is Kuhlmann's classical
  theorem (1995, Corollary 2.4); source 07's proof is printed as a second
  route.

## What is not claimed

- No historical priority: none of the three sources claims it. Source 07's
  real-power strictness is Kuhlmann's theorem; source 02's cube hierarchy is
  Corollary `cor:strict` of the point-separating report (below); source 06
  attributes characteristic-function coding to the standard literature.
- No peer review and no machine verification. The finite checks test finite
  instances only; they verify no transfinite statement.
- No intrinsic criterion for an arbitrary order to embed into 𝒲; absence of
  κ⁺ and its reverse is necessary and is not claimed sufficient.
- No classification of the gaps of 𝒜 or of the longer strata 𝒲_β (κ < β),
  no isomorphism type of the quotient or of the completions, no automorphism
  group, and no claim that full AC is necessary.
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
- [`Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders`](../../../../../../Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/)
  (batch 80, labels `swo:`) answers the question "Other ground orders"
  (Section 26.6) in part for X = S_{<θ}, θ an infinite cardinal, at the
  minimal stratum: its Theorem 8.3 (`swo:st:thm:transition`) gives
  𝒲_λ(S_{<θ}) ≃ 𝔹_λ with λ = 2^{<θ}, except at singular strong-limit θ, where
  𝒲_θ(S_{<θ}) ≃ 𝔹_{θ·θ} (ordinal product), so ℓ₂ = θ·θ > θ (θ = ℶ_ω is an
  example in ZFC). It stays open for n > 0, longer strata, non-cardinal
  cutoffs and other alphabets. That report reprints its sources' re-proofs of
  this report's general-alphabet results (Lemmas 4.1, 5.1, 6.1, 8.1, 11.1,
  Proposition 4.4, Theorems 5.3, 6.2, 6.4, 8.2, 11.2, 11.5, 15.1) as pointers,
  with no novelty claim. Two dated notes, bracketed "[Added 2 October 2026,
  batch 80: …]", record this after the question in Section 26.6 and at the
  end of Section 22; no label or number changed, and nothing in this report
  uses that one. Since batch 81 (its sources 13–18) that report also proves,
  for X = S_{<θ} and μ = 2^{<θ}, 𝒲_{μ·γ+n}(S_{<θ}) ≃ 𝔹_{ρ·γ} × n! for every
  0 < γ < μ⁺ and n < ω, with ρ = μ except ρ = θ·θ at a singular strong limit
  (its Theorem 31.2, `swo:cb:new:thm:block-types`), so the display of Section
  26.6 holds for these strata except at a singular strong limit with γ not a
  left multiple of θ^ω; the density and cellularity of every stratum of every
  infinite linear alphabet and the incompleteness of every stratum (its
  Theorems 27.2, 28.1); and, for minimal slices, a gap-spectrum transfer
  theorem with exact multiplicities (its Theorems 30.10, 30.16). Three more
  dated notes, "[Added 3 October 2026, batch 81: …]", after the question of
  Section 26.6, after the commentary of Research question 26.8 and after
  Research question 26.9, record this (one page more; no label or number
  changed). Since batch 83 (its sources 19–30) that report also gives, for
  every ordinal α of cardinality μ, a coding sandwich
  𝔹_{ϱ_lo} × n! ↪ 𝒲_α(S_{<θ}) ↪ 𝔹_{ϱ_up} × n! with the exact cube spectrum,
  the two bounds agreeing unless some residual cardinal is a singular
  non-strong limit at most θ (its Theorems 64.7, 64.11, source 19); the
  display of Section 26.6 in ZFC at every cardinal cutoff θ < ℵ_ω, θ = ω₁
  included (its Corollary 64.20, source 30), and at every noncardinal cutoff
  ω < θ < ω₁ (its Corollary 78.10, source 29); and the weight μ^{<μ} or 2^μ
  of the strata of type μ + n over every infinite linear alphabet (its
  Corollary 63.12, source 30). A fourth note in Section 26.6, "[Added 3
  October 2026, batch 83: …]", records this (no page, label or number
  changed).
- `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`
  is cited by source 06 as context for bounded sign orders (Section 22). None
  of its declarations states a result of this report.
- `wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets` records a
  lexicographic-sum result (`data/lexicographic_tails_result.json`) that
  source 07's audit read and set aside: it concerns a different order.
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

The recorded build (MiKTeX, pdfTeX) has 55 pages and no errors, undefined
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

## Discrepancies and choices

- Source 02 cites the Kanovei–Shelah index as Section 1 of their paper and
  page 2 of the arXiv PDF; source 07 cites §2, printed page 160 of the
  published version. Both quote the same definition. The section numbering
  was not rechecked at the merge.
- Source 07 states the fixed-length power result as
  (𝒲_κ)^β ≃ ℝ^{κ·β}_lex; source 02 as (𝒲_κ)^β ≃ 𝔹_{κ·β}. These are the
  same statement, since ω·κ·β = κ·β; the article says so instead of calling
  either stronger, and prints source 07's rank repr = κ·β.
- Source 06's conditional separation (its Corollary 9.5) is kept as Remark
  8.5, the cellularity route, after the unconditional Corollary 8.4; its
  Research question 14.1 is answered and not repeated.
- Source 02's research topic on spectra of cuts and point characters is
  printed with a re-scoping note: it stays open only for the strata 𝒲_β with
  κ < β < κ⁺, for the gap spectrum of 𝒜, and for convex-suborder criteria.
- Where 06 and 07 prove the same statement, the article prints 06's
  statement and proof and records 07's differing realizations (triples
  instead of four-element blocks; a cut above a reserved interval) as second
  routes; identical arguments are notes, not reprints.
