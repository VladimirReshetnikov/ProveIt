# Lexicographic Orders of Well-Orderings of the Surreal Numbers

**Set approximations, the singular birthday transition, set-length words, class orders, and higher-order structure**

This is a research report merged from **ten** manuscripts. The first four
were written independently on 2 October 2026 and delivered together in
batch 80 (arrival `4e270aa46`, placement `ccc046989`, cluster K3) and form
Parts I–V. Six more, written independently on 3 October 2026 as
continuations of this report, were delivered in batch 81 (arrivals
`9a4ce14e9` for sources 13–17 and `bd599ac06` for source 18; placements
`f0cd7032d` (81L) and `c4720e1b2` (81L2)) and were merged by theme as Parts
VI–IX in four writes (`a3cfa73ca`, `691454089`, `2a9292305` and the commit
that adds this README text). Author lines: 08 and 09 "Research manuscript
prepared for Vladimir Reshetnikov", 11 "Research report", 12 "Research report
prepared for Vladimir Reshetnikov"; 13, 14 and 17 "Research manuscript
prepared for Vladimir Reshetnikov", 15, 16 and 18 "Research article prepared
for Vladimir Reshetnikov". Sources 09, 12, 13, 15, 17 and 18 call themselves
AI-assisted (source 18 also cites "independent AI-assisted proof review");
source 14 calls itself unrefereed, and source 16 says that its "independent
mathematical checks during preparation" are not external peer review. The report is
AI-assisted, unrefereed and not formalized. Its review in the collection's
[review record](../../REVIEW.md) is **pending**, and it is not yet indexed in
the [formalization ledger](../../FORMALIZATION.md). The four batch-80
archives have a written-proof review in the Hilbert's-tenth research tree,
and the batch-80 merged text a scoped synthesis review and a preservation
audit there, whose corrections are applied; no review of the batch-81
sources exists yet (see "Reviews" below).

| Source | Batch, manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 11 (base) | 80, 11 | `surreal_well_orders (1).zip` (*Lexicographic Orders of Well-Orderings of the Surreal Numbers: Set Approximations, Class Orders, and Higher-Order Structure*; 2,807 lines, 35-page PDF; dated "3 October 2026", the UTC date of its pin) | `ae7c1e6aa` (2 October 2026, 18:03:53 PDT = 3 October, 01:03:53 UTC) | `ccc046989` | abstract and Status paragraph; Sections 2–3; 5.1, 5.3, 5.7; 6 (before 6.1); 7 (before 7.1); 9–12; 13 (before 13.1); 14 (before 14.1); 15; 16 (before 16.1); 19 (its own subsections 19.1, 19.2, 19.4, 19.5, 19.8, 19.11); 20; 61.1; 63 (before 63.1); Appendix A (before A.1) |
| 12 | 80, 12 | `surreal_well_orders.zip` (*Well-Orders of the Surreal Numbers and Their Lexicographic Geometry*; 1,689 lines, 24-page PDF) | `63bb8b1d9` (18:01:32 PDT) | `ccc046989` | Sections 4.1, 5.4, 6.2 (route), 8 (new), 13.1, 14.1, 16.1 (routes), 18, 19.9, 19.10, 21, 24, 61.2, 62.1, 63.1, A.1, C; Lemmas 5.3, 5.14–5.15 and 19.5; Notes 19.11, 19.21, 19.28 |
| 09 | 80, 09 | `Surreal_Well_Orders_Research.zip` (*Well-orders of the Surreal Numbers: Lexicographic universality, a surreal dense core, and the boundary between sets and classes*; 1,677 lines, 24-page PDF) | `63bb8b1d9` | `ccc046989` | Sections 4.2, 5.5, 5.8, 6.3, 7.1, 11.1, 13.2, 19.3, 19.6, 19.12, 22, 25, 61.3, 62.2, 63.2, A.2, A.3, C; Proposition 19.24; notes in Sections 6, 11 and 19 |
| 08 | 80, 08 | `Surreal_Well_Orders_Research (1).zip` (*Lexicographic Orders of Surreal Well-Orderings: Set-sized spectra, global enumeration orders, and a surreal-sized dense skeleton*; 2,022 lines, 26-page PDF) | `ae7c1e6aa` | `ccc046989` | Sections 4.3, 4.4, 5.2, 5.6, 7.2, 17, 19.7, 23, 26, 61.4, 62.3, 63.3, A.4, A.5, C; notes and printed paragraphs in Sections 5, 6, 7, 11 and 19 |
| 13 | 81, 01 | `Surreal_Well_Orders_Further_Study.zip` (*Lexicographic Orders of Surreal Well-Orderings: Further Structure*, title page "Cut reconstruction, asymmetric products, prefix non-rigidity, and size-safe foundations"; 2,215 lines, 33-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.6; 32 (Part VI); 34–36 (Part VII); 42, 46, 47 (Part VIII); 51, 55, 57, 59 (Part IX); 61.6, 62.4, A.6, A.7, C, D |
| 14 | 81, 02 | `lexicographic_surreal_well_orders_II.zip` (*Lexicographic Well-Orders of the Surreals II: cut classification, support thresholds, and class-model absoluteness*; 2,114 lines, 33-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.7, 4.12; 32; 34, 35; 40, 41, 43–45, 47–49 (base of Part VIII); 54, 56, 57, 59; 61.7, 62.5, 63.4, A.8, A.9, C, D |
| 15 | 81, 03 | `surreal_lexicographic_orders.zip` (*Lexicographic Orders of Surreal Well-Orders: interpretations, canonical blocks, represented cuts, and fixed-type spectra*; 2,596 lines, 37-page PDF) | `0ecd158fd` (also cites `491ed8411`) | `f0cd7032d` | Sections 4.8; 29–32 (block types: Section 31); 34, 38; 42, 46, 47; 51–53, 57, 59; 61.8, 63.5, A.10, C, D |
| 16 | 81, 04 | `surreal_well_orders_further.zip` (*Lexicographic Orders of Surreal Well-Orders: Cuts, Canonical Blocks, and the Limits of Set-Sized Coding*; 2,279 lines, 33-page PDF) | `491ed8411` | `f0cd7032d` | Sections 4.9; 27, 28, 30, 32; 34–36; 42, 46; 51, 52, 56, 57, 59; 61.9, 63.6, C, D |
| 17 | 81, 05 | `surreal_well_orders_further_study (1).zip` (*Lexicographic Well-Orders of the Surreal Numbers, II: exact cut spectra, branch recognition, optimal support reserves, and automorphism-extension obstructions*; 2,056 lines, 29-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.10, 4.13; 29, 30, 32; 34; 42, 46–49; 51, 54, 59; 61.10, 62.6, 63.7, A.11, C, D |
| 18 | 81, 06 (81L2) | `surreal_lexicographic_orders_further_study.zip` (*Lexicographic Well-Orders of the Surreal Numbers: Cuts, canonical class blocks, and changes of interpretation*; 3,928 lines, 53-page PDF) | `83befe707` | `c4720e1b2` | Sections 4.11; 27, 29, 30, 32; 34–37; 42, 46; 51, 52, 57–59; 61.11, 63.8, C, D |

The two pairs of batch-80 archives sharing a name (08/09 and 11/12) are
**not editions**: every pair of the four texts has word 8-gram overlap of
0.6–1.1 % (preamble boilerplate), no member file is shared, the pins differ
within each pair, and the result sets differ. None supersedes another; all
four are merged (union). Source 11 is the base of Parts I–V: it proves the
global-choice equivalence over GB without set choice (sources 09 and 12 assume
set choice, and source 12 asks the choiceless case), it covers set alphabets,
set-length words, and set-like and unrestricted class well-orders, and it
alone attributes the set-sized general-alphabet theorems to the reals report.

The six batch-81 sources are likewise independent texts, not editions: every
pair shares 0.6–1.4 % of word 8-grams (preamble, this report's title and
address, bibliography), no member file is shared, and the theorem sets differ.
Sources 14 and 17 share only the inner directory name `surreal_well_orders_II`
and a "II" in the title; source 18's archive name extends source 15's. All
six continue this report; sources 13–17 read it at `0be9b9134`, source 18 at
`83befe707` (after the corrections of `0f52c0dca`, before sources 13–17
arrived). They overlap heavily with each other and with Parts I–V, so they are
printed by theme, one Part per theme: VI set-sized strata (base 16 and 17),
VII words and termination conventions (base 16; 18 for centered increasing
words; 15 for other comparison orders), VIII cuts of the set-coded core (base
14; 17 for the reserve and extension criterion), IX unrestricted class
well-orders (base 15 for blocks and histories, 17 for finite components, 13
for products, 16 for the Σ¹₁ bound, 18 for countable models). Their
introductions are in Section 4.5–4.13, their foundations, universe sections
and Lean plans at the end of Part IX (Sections 51, 57, 59; not in Part V, so
that no existing section is renumbered), their questions in Section 61.5–61.11.

Every result, proof, example, remark, question and limitation of the ten
manuscripts is printed. A result proved again by the same argument is
recorded in a numbered **Note** that gives the source's statement, number and
differences, or, where each source builds on its own proof, printed whole as
a marked route under a credit note (the represented-cut theorem is proved six
times, Note 46.1; the block decomposition three times, Note 52.1);
source-specific results are printed in full where they belong. Each source's
introduction, foundational section, model section, Lean plan, questions,
conclusion, ledger and reproducibility record are printed whole. Text written
for the merge is marked `[merge]`. Appendix D maps every numbered statement of
the ten sources (311 of sources 13–18) to its place here.

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 349 pages (title page unnumbered)
README.md                                this guide
09-core-RESEARCH_STATUS.md               source 09's research status and audit, as delivered
11-raw-orders-repository_audit.md        source 11's targeted repository audit, as delivered
12-singular-RESEARCH_STATUS.md           source 12's research status and audit, as delivered
13-products-RESEARCH_STATUS.md           source 13's research status and audit, as delivered
14-trichotomy-RESEARCH_STATUS.md         source 14's research status and audit, as delivered
16-strata-SOURCE_STATUS.txt              source 16's source and proof status, as delivered
17-gaps-research_status.md               source 17's research status, as delivered
code/08-skeleton-build.sh                source 08's build script (builds nothing here; see below)
code/08-skeleton-verify_finite.py        source 08's finite checks
code/09-core-build.sh                    source 09's build script (builds nothing here)
code/09-core-finite_checks.py            source 09's finite checks
code/11-raw-orders-finite_checks.py      source 11's finite checks (prints)
code/12-singular-build.sh                source 12's build script (fails here)
code/12-singular-finite_checks.py        source 12's finite checks
code/13-products-build.sh                source 13's build script (builds nothing here)
code/13-products-finite_checks.py        source 13's finite checks
code/14-trichotomy-build.sh              source 14's build script (builds nothing here)
code/14-trichotomy-verification.py       source 14's finite checks (writes beside itself)
code/15-blocks-build.sh                  source 15's build script (builds nothing here)
code/15-blocks-examples.py               source 15's finite examples (prints)
code/16-strata-finite_checks.py          source 16's finite checks
code/17-gaps-build.sh                    source 17's build script (fails here)
code/17-gaps-finite_checks.py            source 17's finite checks
code/18-shuffle-build.sh                 source 18's build script (builds nothing here)
data/08-skeleton-verification_results.json   source 08's recorded run
data/09-core-finite_checks.json              source 09's recorded run
data/11-raw-orders-finite_checks_results.txt source 11's recorded run
data/12-singular-finite_checks.json          source 12's recorded run
data/13-products-finite_results.json         source 13's recorded run
data/13-products-pdf_inspection.json         source 13's record of the layout check of its (unshipped) PDF
data/14-trichotomy-verification_results.json source 14's recorded run
data/15-blocks-finite_examples.txt           source 15's recorded output
data/16-strata-finite_check_results.json     source 16's recorded run
data/17-gaps-finite_checks.json              source 17's recorded run
```

All code, data and the seven audit and status files are byte-identical to the
delivery. Source 18 shipped no code or data; source 15 no status file.

Batch 83 files placed here (sources 19–30, placement `2e06337d5`, for the
forthcoming Parts X–XIV). They are not yet merged into the report, and this
README does not describe them; they are listed so that the listing matches
the directory:

```
19-residual-source_status.txt
21-obstructions-LEAN_INTERFACE_AUDIT.txt
21-obstructions-SOURCE_AUDIT.txt
22-unranked-RESEARCH_STATUS.md
22-unranked-SOURCE_AUDIT.md
23-termination-RESEARCH_STATUS.md
23-termination-SOURCE_AUDIT.md
24-completions-SOURCE_AUDIT.md
25-symmetries-RESEARCH_STATUS.md
25-symmetries-SOURCE_AUDIT.md
26-nonborel-RESEARCH_STATUS.md
27-scans-SOURCE_AUDIT.txt
28-envelope-SOURCE_AUDIT.md
29-birthdays-PROOF_STATUS.txt
29-birthdays-SOURCE_AUDIT.txt
30-tables-proof_review.txt
30-tables-source_audit.txt
code/19-residual-build.sh
code/19-residual-check_restrictions.py
code/20-limits-finite_diagnostics.py
code/22-unranked-build.sh
code/22-unranked-finite_checks.py
code/23-termination-build.sh
code/23-termination-finite_checks.py
code/24-completions-build.sh
code/24-completions-finite_checks.py
code/25-symmetries-build.sh
code/25-symmetries-finite_checks.py
code/26-nonborel-build.sh
code/26-nonborel-finite_checks.py
code/27-scans-finite_checks.py
code/28-envelope-build.sh
code/28-envelope-finite_checks.py
code/30-tables-build.sh
code/30-tables-verify_finite.py
data/19-residual-restriction_checks.json
data/20-limits-finite_diagnostics_results.json
data/22-unranked-finite_checks.json
data/22-unranked-pdf_validation.json
data/23-termination-finite_checks.json
data/24-completions-build_validation.json
data/24-completions-finite_checks.json
data/25-symmetries-finite_checks.json
data/26-nonborel-finite_checks.json
data/27-scans-finite_checks.json
data/28-envelope-finite_checks.json
data/29-birthdays-source_manifest.json
data/29-birthdays-verification.json
data/30-tables-verification_results.json
```

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
| 13 | `RESEARCH_STATUS.md`, `build.sh`, `code/finite_checks.py`, `data/finite_results.json`, `data/pdf_inspection.json` | `13-products-RESEARCH_STATUS.md`, `code/13-products-build.sh`, `code/13-products-finite_checks.py`, `data/13-products-finite_results.json`, `data/13-products-pdf_inspection.json` |
| 14 | `RESEARCH_STATUS.md`, `build.sh`, `verification.py`, `verification_results.json` | `14-trichotomy-RESEARCH_STATUS.md`, `code/14-trichotomy-build.sh`, `code/14-trichotomy-verification.py`, `data/14-trichotomy-verification_results.json` |
| 15 | `build.sh`, `examples.py`, `finite_examples.txt` | `code/15-blocks-build.sh`, `code/15-blocks-examples.py`, `data/15-blocks-finite_examples.txt` |
| 16 | `SOURCE_STATUS.txt`, `finite_checks.py`, `finite_check_results.json` | `16-strata-SOURCE_STATUS.txt`, `code/16-strata-finite_checks.py`, `data/16-strata-finite_check_results.json` |
| 17 | `research_status.md`, `build.sh`, `finite_checks.py`, `finite_checks.json` | `17-gaps-research_status.md`, `code/17-gaps-build.sh`, `code/17-gaps-finite_checks.py`, `data/17-gaps-finite_checks.json` |
| 18 | `build.sh` | `code/18-shuffle-build.sh` |

Not shipped (recoverable with `git show 4e270aa46:"docs/incoming/<archive>.zip"`
for batch 80, `git show 9a4ce14e9:"docs/incoming/<archive>.zip"` for sources
13–17 and `git show bd599ac06:"docs/incoming/<archive>.zip"` for source 18; mind
the space in `"surreal_well_orders_further_study (1).zip"`): the ten delivered
PDFs (08 26 pages, 09 24, 11 35, 12 24, 13 33, 14 33, 15 37, 16 33, 17 29,
18 53); the manuscripts and delivery READMEs of sources 08, 09, 12 and 13–18;
and seven checksum manifests (08 6/6, 09 7/7, 12 7/7, 13 8/8, 14 7/7, 16 6/6,
17 7/7 verified at placement; sources 11, 15 and 18 shipped none). Nothing was
excluded as regenerable (the largest delivered non-PDF file of batch 80 is
126,780 bytes, of batch 81 185,939 bytes, both manuscripts; the largest shipped
batch-81 file is 17,413 bytes), so there is no data to reconstruct.

Shipped files whose text still uses delivery names or names unshipped files:
`11-raw-orders-repository_audit.md` ("the accompanying article"; its audit
inputs are named by their delivery copies, which are not shipped);
`12-singular-RESEARCH_STATUS.md` (names `data/finite_checks.json`,
`SHA256SUMS.txt` and its own 24-page PDF); `09-core-RESEARCH_STATUS.md`
(describes its own article and build); `13-products-RESEARCH_STATUS.md` (its
33-page PDF, three-pass build and checksums); `14-trichotomy-RESEARCH_STATUS.md`
(its delivered tests, by count); `16-strata-SOURCE_STATUS.txt` (its "standalone
source", PDF and Python script); `17-gaps-research_status.md` (`finite_checks.py`
and its JSON); `data/13-products-pdf_inspection.json` (describes the unshipped
33-page PDF); the nine build scripts, which build `surreal_well_orders.tex`,
`article.tex`, `surreal_lexicographic_orders.tex` or
`surreal_lexicographic_orders_further_study.tex` beside themselves or in
`code/`; and the reproducibility records printed in the report's Appendix A and
Section 63, which name delivery files (annotated there and in Appendix B).

## Labels

Every label carries the prefix `swo:`. Source 11's 60 labels are kept with
that prefix, unchanged after it (`swo:sec:…`, `swo:sw:…`, `swo:cf:…`,
`swo:gl:…`, `swo:thm:…`, `swo:lem:delete`, `swo:prop:universal`,
`swo:app:sources`). Source 12's labels carry `swo:st:`, source 09's `swo:ec:`,
source 08's `swo:sk:`; the batch-81 sources' carry `swo:fs:` (13, replacing
its own `swf:`), `swo:tc:` (14), `swo:cb:` (15, keeping its internal `cce:`
and `new:`), `swo:ds:` (16), `swo:gs:` (17) and `swo:sh:` (18, keeping its
internal `wv:`). Two labels of source 13 printed in Part VI keep its old
prefix after the new one (`swo:fs:swf:sec:fixed`, `swo:fs:swf:thm:fixed`);
labels are never renamed, so they stay. Numbered statements without a label
in their source carry `swo:`*sub*`:n`*number* (for example `swo:st:n10.4`,
source 12's Corollary 10.4; `swo:sh:n16.7`, source 18's Remark 16.7, which is
not source 11's question `swo:n16.7`); source 08's equation tags (1)–(13) are
printed as (S08.1)–(S08.13), labelled `swo:sk:eq:t`*n*, and the batch-81
equations as (S13.*n*), (S16.*n*), (S17.*n*), (S18.*n*) with their sources'
numbers. Labels written for the merge begin `swo:vi:`, `swo:vii:`, `swo:viii:`
and `swo:ix:` in Parts VI–IX.

Totals: **794 labels.** `swo:` only 98 (60 of source 11, 11 for its
unlabelled statements, 21 merge labels of batch 80, 6 of batch 81: four Part
labels and two subsections), `swo:st:` 61, `swo:ec:` 52, `swo:sk:` 67 (as
before), `swo:fs:` 62 (48 source labels + 14 for unlabelled statements),
`swo:tc:` 62 (40 + 22), `swo:cb:` 69 (51 + 18), `swo:ds:` 74 (62 + 12),
`swo:gs:` 85 (56 + 29), `swo:sh:` 98 (76 + 22), and merge labels `swo:vi:` 20,
`swo:vii:` 12, `swo:viii:` 15, `swo:ix:` 19. Every one of the 531 labels of
the ten sources is present exactly once. Cross-references are typed (lemma,
note, …) through alias counters. No `swo:` label has a Lean mapping.

## Notation (Sections 1.3 and 1.3.1)

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

For sources 13–18 (dated addendum, Section 1.3.1): `κ` is a cutoff, `μ = 2^{<κ}`,
`r = cf κ`, `q = cf μ` (source 18's `ν, τ`, source 14's `τ = cf κ`, source 15's
`δ` renamed; source 16's alphabet size `κ` and cutoff `θ` printed `μ` and `κ`);
source 15's coding length `r_κ` is printed `ρ_κ` and its cube product `D_{σ,m}`
as `𝔹_σ ×_lex m`; density, cellularity, weight are `d`, `cell`, `w` (cellularity
never `c`); gap characters `GapChar` (17's `Σ`, 18's `GapSpec`); `𝔚_sl`, `𝔚_all`
for 13/14/16/17's `𝔈`, 14's and 17's `𝔚`, 16's `𝔥`, 18's script `𝓗`; class
injections `𝔍` (never the injective-words class `𝓘`, which 16's macro `\I`
collides with); all words `𝒯`, injective `𝓘`, increasing `𝒯^inc` (16's `\Words`
is *all* words); the core `𝒫_bd(b)` (15, 16) or `𝒫_s(b)` (13, 14, 17, 18; 18's
macro `\Pbd` is the support coding); 14's support layer `𝒫_{<κ}(b)` is not
`𝒫_bd`; cylinders `C_p`, and "straddles" for the cylinder test (13 and 14 say
"crosses", 15 "persistent"). Part IX keeps the sources' block notations (15's
`B_W`, `C_b`; 16's `J_R`, `α_R`; 18's `B_R`, `θ_R`), with the false readings
printed (15's `b` there is not the baseline; 14's `J_R` is an initial branch,
not 16's `J_R`); in its universe sections `κ` is an inaccessible. The
notation guide's paragraph for these symbols belongs to the reciprocal-notes
commit of batch 81L.

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
7. **Set-sized strata (Part VI, sources 16, 17, 18, 15).** Density and
   cellularity of every stratum `𝒲_α(X)` of every infinite linear alphabet:
   `μ^{<μ}` for `α = μ, μ+1, μ+2`, `2^μ` from `μ+3` on (Theorem 27.2; source 18's
   route); every stratum is incomplete (Theorem 28.1); the gap spectrum of
   `No_{<κ}` for every `κ`, including singular `κ` and `κ = ω` (Theorem 29.4);
   the minimal slice's characters `(q,q)`, global character `r`, density,
   weight and cellularity `μ^{<μ}` (Theorem 30.2), the general permutation
   gap-spectrum principle (Theorem 30.10, source 18), its exact gap spectrum
   (Theorem 30.11) and multiplicities (Theorem 30.16, source 18), saturation
   exactly `η_r` (Corollary 30.18); the regular saturated spectrum (Theorem
   30.14, source 16); and the strata `μ·γ + n`: `𝒲_{μ·γ+n}(No_{<κ}) ≡ 𝔹_{ρ·γ} ×_lex n!`
   with `ρ = κ·κ` at a singular strong limit, `μ` otherwise (Theorem 31.2,
   source 15).
8. **Words and conventions (Part VII, sources 16, 18, 13, 15).** Unrestricted,
   injective and increasing shorter-first words are isomorphic in GBC (Theorem
   35.1); the exact criterion for a terminator placement to give an order
   `≅ No` and the complete list of termination types (Theorems 36.1, 36.2;
   source 13's central case, Theorem 36.4); the cut classification of centered
   increasing words (Theorems 37.1, 37.2, source 18); inverse-rank and
   relation-table lexicographies (Theorems 38.1, 38.2, source 15).
9. **Cuts of the core (Part VIII, base source 14).** Every proper class cut of
   the core is uniquely a cylinder edge, a numerical gap or a branch (Theorem
   43.3), with characters (Theorem 44.1); the cuts of global enumerations are
   recognized by straddling prefixes at every set length and coverage (Theorem
   45.1, proved by all six sources), which answers source 11's question on
   represented cuts; automorphism orbits are the character classes (Theorem
   47.2), a core automorphism extends to `𝔚_sl` exactly when it preserves
   represented cuts (Theorem 47.5), and some do not (Theorem 47.7); cylinders
   are not invariant (Theorem 47.12, source 13); class extensions with the same
   sets add no old represented cut and always a new one (Theorems 48.1, 48.4);
   `𝒫_{<κ}(b)` is `η_{cf κ}` and not `η_{(cf κ)^+}` (Theorem 49.3), and the
   exact reserve of a supported completion (Theorem 49.7, source 17).
10. **Unrestricted class well-orders (Part IX).** The canonical decomposition of
    every class well-order into `Ord`-blocks and one final set block, elementary
    in GB, with every class well-order as a block index (Theorems 52.3, 52.5;
    source 16's Theorem 52.6 and source 18's Theorem 52.11 as routes);
    explicit condensation histories of every class length (Theorem 53.4); the
    maximal finite components are the `n!` permutation blocks (Theorem 54.4)
    and the core traces of raw orders are the cuts of their initial branches
    (Theorem 54.6); `𝔚_sl ≅ No ×_lex 𝔚_sl`, while `𝔚_sl ×_lex 2 ↛ 𝔚_sl` in the
    full inaccessible universe and definably in `KM + GC`, and `𝔚_sl² ≅ 𝔚_sl`
    externally in countable models (Theorems 55.1, 55.3, 55.4, Proposition 55.5,
    source 13, whose proofs are source 11's); `GBC + Σ¹₁-CA` suffices for the
    uniform nonembedding of elementary transformations (Theorem 56.2, source
    16); `𝒲_{κ+2} ↛ 𝒲_κ` in the full model (Theorem 57.3); and in every countable
    ω-standard model the full order is the factorial shuffle `σ({n!})` and
    set-likeness is not definable in it (Theorem 58.6, Corollary 58.10,
    source 18).

## What the report does not claim

Section 1.4 keeps every limitation of every source; none was dropped.

- No novelty for the set-sized general-alphabet layer: it re-proves the
  reals report. Universality and homogeneity of `No` are classical (Ehrlich;
  Hamkins, MathOverflow 57597); the coding behind the choice equivalence is
  a standard well-founded coding.
- No novelty for re-proofs. Sources 13–18 re-prove the core layer of Part IV,
  the direct comparison, choice equivalence, adjacency and diagonal theorems of
  Parts III–IV, the alphabet gap pairs of `univ:gs:lem:boundary` at regular
  uncountable `κ`, and much of each other; these are notes or credited routes.
  Results proved independently by several batch-81 sources are credited to all
  of them, with no priority.
- No machine verification, no Lean or Rocq build, no new Lean file. The Lean
  module names in the ten formalization plans (Sections 20.7, 24, 25, 26 and
  59) are proposals; no such module exists.
- The finite checks verify finite instances only, never a transfinite,
  class-theoretic or cardinal statement.
- Source 11's README says that "the mathematical proofs underwent a separate
  proof review", source 15's that its extensions "received independent
  mathematical review within the task", source 16's status file that its
  proofs "underwent independent mathematical checks during preparation", and
  source 18's that its validation includes "independent AI-assisted proof
  review". These are the deliveries' statements; no such review is recorded in
  the repository, and the report does not rely on them.
- No class of classes is formed: `𝔚_sl` and `𝔚_all` are predicates on class
  variables. The core realizes uniform set-sized cuts only; source 12's
  bounded theorem is not a full class model at a singular cardinal; the
  research questions are proposals. The cut classification of Part VIII is
  relative to the labelled prefix structure: the bare order recovers neither
  cylinders nor represented cuts. Source 13's product nonembedding is not a
  theorem of bare GBC about a third sort of maps. Source 15's fixed-type
  classification covers `μ·γ + n` with finite `n` only. Source 16's Σ¹₁ bound
  is sufficient, not necessary.

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
the current revision, including `le_iff_options_lt` and
`lt_iff_exists_option` in `SignSequenceComparison.lean` (cited by source 18);
none states a result of this report. No batch-81 statement is formalized.
Placement in the surreal collection beside the Lean foundations confers no
formal status.

## Where one source answers another (Sections 1.7, 33, 39, 50, 60)

- Source 12's question on the weak-choice strength (its Remark 4.2 and
  Question 14.5): **answered** by source 11's Theorem 13.1; printed as
  Remark 61.15, with Remark 13.4.
- Source 08's question 11 (comparing non-set-like class well-orders):
  **answered** by Theorems 14.2 and 14.7.
- Source 08's question 3 (coding lengths at singular cutoffs): answered in
  part by Theorem 8.3, its cut half by Theorems 29.4 and 30.11; question 2:
  **answered** by Part VI (Section 33).
- The reals report's question "Other ground orders"
  (`lwo:sec:research`, which names set-sized suborders of surreal numbers):
  answered in part by Theorem 8.3, for `X = No_{<κ}` and the minimal stratum,
  and further by Theorem 31.2 for every stratum `μ·γ` and every finite tail;
  open for strata that are not of this form, noncardinal cutoffs and other
  alphabets.
- Batch 81 (dated notes of 3 October 2026, Sections 33, 39, 50 and 60, and the
  status cells of the question index, Section 61): source 11's questions on
  represented cuts and on the minimal slice's cut spectrum (`swo:n16.1`,
  `swo:n16.7`), source 09's directions 3 and 8 and source 08's questions 2 and
  7 are **answered**; source 11's `swo:n16.2`–`swo:n16.5` and `swo:n16.8`,
  source 12's `swo:st:n14.1`, `14.3`, `14.4`, `14.7`, `14.8`, source 09's
  directions 4–7 and source 08's questions 4, 6, 8, 9, 12, 13, 14 are answered
  in part. Among the batch-81 sources' own 74 questions (index in Section
  61.5), source 13's on termination cuts is answered by source 16, source 14's
  and source 16's on the minimal slice's local geometry by source 17, and
  source 16's on centered increasing words by source 18 (at the zero
  threshold).

## Relation to the neighbouring reports

**[lexicographic-well-orderings-of-reals](../../../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/)**
(research-report collection, batch 76) proves the set-sized theorems of
Section 6 for every infinite linear alphabet; they are printed here as
pointers and marked routes, never as new. Source 08 re-derived them from
batch-76 manuscript 02, now that report's base source. Source 12's dichotomy
and source 15's block types answer that report's question "Other ground
orders" in part; source 16's density and incompleteness theorems answer its
questions on other alphabets in part, and source 18's general permutation
principle bears on its request for a cut-spine transfer theorem (Section 33).
Part VI's minimal-slice results are the `No_{<κ}` analogues of that report's
`lwo:prop:fixed-topology`, `lwo:rk:thm:Pgaps` and `lwo:sp:thm:gapcount`.

**[foundations](../foundations/)** supplies the conventions used throughout
(`found:sub:gbconvention`, `found:prop:recursion`, `found:sub:km`,
`found:rem:secondsort`, `found:prop:proper`, `found:prop:allcuts`).

**[birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)**:
the saturation of `No_{<κ}` at regular `κ` (`hset:rem:saturation`, through
`hset:eq:cut-bound`) is classical and is source 11's Lemma 7.2 and source 08's
Note 7.4; its ordinal-graph coding (`hset:thm:choice`) is the set-level form of
the mechanism in Theorem 13.1 (Remark 13.4) and is unchanged. Its remark on
the gap pairs of `No_{<κ}` (`hset:rem:cutoffgaps`) is re-proved, and extended
to singular `κ` and `κ = ω`, by source 17's Theorem 29.4.

**[real-vector-space-structure](../../surreal/real-vector-space-structure/)**
uses a set-like global well-order; by Theorem 13.1 that hypothesis is
equivalent to global choice over GB. Its question on the weaker class-choice
principles (`rvs:w:q:foundations`) is unaffected.

**[surreal-fields-across-universes](../surreal-fields-across-universes/)**
studies the saturation of `No_{<κ}` across universes; nothing here depends on
it. Its `univ:gs:lem:boundary` (with `M = N`) is the regular uncountable case
of Theorem 29.4, which Part VI records with a pointer.

The Lean development in `Algebra/SurrealNumbers/Surreal/Foundations/` is
cited, not extended: see "Formal status".

## Build

TeX Live or MiKTeX with lmodern, amsmath/amssymb/amsthm, mathtools, mathrsfs,
geometry, microtype, booktabs, longtable, array, tabularx, enumitem, xcolor,
fancyhdr, listings, tcolorbox, aliascnt, hyperref, xurl and cleveref. No
external figures or bibliography file.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Built with MiKTeX (pdfLaTeX): 349 pages; no errors, undefined references or
citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull boxes; 15 underfull-box warnings (10 in the build before
Part IX). The four batch-81 writes added Parts VI–IX (116 → 151 → 188 → 236 →
349 pages); the fourth added Part IX, the introductions, questions,
conclusions, ledgers, reproducibility records, title pages and crosswalk of
sources 13–18. Its `.aux`, compared with a build of the previous text, keeps
every label; the only numbers that changed are those of the three sections of
the questions part (51–53 became 61–63), as in the third write.

## Rerunning the checks

Run the programs on copies or with explicit outputs, never so that they write
into this directory: source 08's and source 14's programs write beside
themselves; source 09's default `--output` is an unprefixed
`data/finite_checks.json` here, source 13's an unprefixed
`data/finite_results.json` relative to the working directory, source 16's
`code/finite_check_results.json` beside the script, and source 17's
`finite_checks.json` in the working directory. From this directory, with an
empty scratch directory `$S`:

```
cp code/08-skeleton-verify_finite.py "$S/"
python "$S/08-skeleton-verify_finite.py"                  # writes $S/verification_results.json
python code/09-core-finite_checks.py --output "$S/09.json"
python code/11-raw-orders-finite_checks.py > "$S/11.txt"
python code/12-singular-finite_checks.py --output "$S/12.json"
python code/13-products-finite_checks.py --output "$S/13.json"
cp code/14-trichotomy-verification.py "$S/"
python "$S/14-trichotomy-verification.py"                 # writes $S/verification_results.json
python code/15-blocks-examples.py > "$S/15.txt"
python code/16-strata-finite_checks.py --output "$S/16.json"
python code/17-gaps-finite_checks.py --output "$S/17.json"
```

(Sources 08 and 14 both write `verification_results.json`; run them in
different scratch directories or compare between the two.) Compare with the
records in `data/` using `diff --strip-trailing-cr`. Rerun on 2 October 2026
(batch 80) and 3 October 2026 (batch 81) with Python 3.14.4 on Windows (`py`),
each program reproduced its record apart from line endings (they write CRLF on
Windows) and, for sources 13 and 14, the recorded `python_version` (3.13.5):
08 5,906 + 7,432 permutation pairs, 21,845 pair-code and 16,129 sign-code
comparisons; 09 164,560 assertions, 1,101 separator families, seed 20261002;
11 465 sign-code pairs, 79,800 word-code pairs, 266,272 permutation pairs (867
adjacent); 12 180,905 cases; 13 533,417 relation-versus-lexicographic pairs,
2,371 cylinders, 67,081 central-word pairs; 14 15,018 common-prefix pairs,
15,126 partial injections, 320,000 word-code pairs (seven kernels); 15 the
three-label table and the predecessor formula for all permutations of up to 5
points; 16 232,324 word comparisons under four sign codes and 15,018 relation
pairs; 17 533,418 predecessor comparisons, 266,272 adjacency checks, 160,000
word-code comparisons. All use the standard library only. The nine build
scripts are kept as delivered and build nothing in this layout:
`code/08-skeleton-build.sh` runs `verify_finite.py` and compiles
`surreal_well_orders.tex` beside itself, `code/09-core-build.sh`,
`code/13-products-build.sh` and `code/14-trichotomy-build.sh` compile an
`article.tex` in `code/` (13's writes `build-pass-1.log` there first),
`code/12-singular-build.sh` changes into `code/` and then calls
`code/finite_checks.py`, `code/15-blocks-build.sh` and
`code/18-shuffle-build.sh` run `latexmk` on their unshipped manuscripts, and
`code/17-gaps-build.sh` first runs `python3 finite_checks.py`, absent under that
name.

## Other discrepancies

- Source 11 is dated 3 October 2026, the UTC date of its pin; the other three
  batch-80 sources are dated 2 October 2026, the six batch-81 sources 3 October
  2026.
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
  before Section 5.6 records the original sentence. Source 15 makes the same
  claim again ("Adding classes … can destroy the internal well-foundedness of
  an old relation"); its sentence is kept and withdrawn for GBC realizations
  in Note 57.5, citing source 16's opposite statement.
- Corrections to batch-81 source text, each marked `[merge]` where made:
  "In GBC" added to source 15's Proposition 51.10 and Theorem 47.10 (the
  latter in write 3); source 14's "coherently" (its line 401) printed as "uniformly";
  source 13's "new point" about split products annotated as contained in
  source 11's proofs (Section 55); source 14's "Four main results" (five are
  listed), source 17's question table (it maps its reserve theorem to
  `swo:n16.6`, which asks for birthday bounds) and source 18's "advance"
  column annotated (Section 4.5); source 17's singular example states
  `κ^{<κ} = 2^κ` (write 1); citations of this report replaced by
  cross-references, with the sources' numbers "at the pin".
- `14-trichotomy-RESEARCH_STATUS.md` says that the inspected Lean simplicity
  theorem "is NOT an independent arbitrary-small-cut existence theorem"; that
  is true of `SignSequenceSimplicity.lean`, but the existence theorem is
  `small_cut_fillers` in `SignSequenceCut.lean` (Sections 1.4 and 59).
- The status files of sources 13, 14 and 15's README describe this report as
  115 pages and four manuscripts, as it was at their pins.
- No retraction was made; no claim of another report or README is refuted.

## Reviews

- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_surreal.md`
  (commit `c338541e3`, by the session that maintains that tree): a
  written-proof review of the four delivered batch-80 archives, with a replay
  script and receipt beside it. It found the principal proof arguments sound
  under the stated foundations, reran the four finite checks and added
  independent finite checks, and proposed one scoped correction to source 08
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
where this report's review stays pending. There is no review of the batch-81
archives (sources 13–18) or of Parts VI–IX yet.
