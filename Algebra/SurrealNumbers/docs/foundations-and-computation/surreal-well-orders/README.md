# Lexicographic Orders of Well-Orderings of the Surreal Numbers

**Set approximations, the singular birthday transition, set-length words, class orders, and higher-order structure**

This is a research report merged from **twenty-eight** manuscripts. The first four
were written independently on 2 October 2026 and delivered together in
batch 80 (arrival `4e270aa46`, placement `ccc046989`, cluster K3) and form
Parts I–V. Six more, written independently on 3 October 2026 as
continuations of this report, were delivered in batch 81 (arrivals
`9a4ce14e9` for sources 13–17 and `bd599ac06` for source 18; placements
`f0cd7032d` (81L) and `c4720e1b2` (81L2)) and were merged by theme as Parts
VI–IX in four writes (`a3cfa73ca`, `691454089`, `2a9292305`, `57d66a24b`).
Twelve more, written independently on 3 October 2026 as continuations of this
report, were delivered in batch 83 (arrivals `b63f0c852` for sources 19–24,
`5ad44b1ed` for source 25, `0d7b2441d` for source 26, `79049d58c` for sources
27–28 and `51b0a69d7` for sources 29–30; one placement `2e06337d5`, batch 83L)
and were merged by theme as Parts X–XIV in one write (`07ee2b30c`). One more,
source 31, a continuation of this report dated 4 October 2026 (the UTC date of
its arrival on 3 October 2026, PDT), was delivered in batch 89 (arrival
`7c0f2d9f9`, placement `23adb85f9`, which staged nothing for it) and is printed
whole as Part XV (write `193e2e942`). Four more, sources 32–35, written
independently on 4 and 5 October 2026 in answer to one request (how far
definable class well-orders reach beyond `Ord`), were delivered in batch 96
(manuscripts 08–11; arrival `e3839ad2c`, placement `111c38012`, batch 96D) and
are merged as Part XVI, with source 34 as base (write `62b16914e`). One more,
source 36, a fifth independent answer to the same request, was delivered in
batch 97 (manuscript 01; arrival `d7cf7d554`, fifteen minutes after the batch-96
placement; placement `6571ee1af`, batch 97A) and is printed whole as Part XVII
(the commit that adds this README text). Author lines: 08 and 09 "Research manuscript
prepared for Vladimir Reshetnikov", 11 "Research report", 12 "Research report
prepared for Vladimir Reshetnikov"; 13, 14 and 17 "Research manuscript
prepared for Vladimir Reshetnikov", 15, 16 and 18 "Research article prepared
for Vladimir Reshetnikov". Sources 09, 12, 13, 15, 17 and 18 call themselves
AI-assisted (source 18 also cites "independent AI-assisted proof review");
source 14 calls itself unrefereed, and source 16 says that its "independent
mathematical checks during preparation" are not external peer review. Of
batch 83, sources 19, 20, 21, 23, 24, 26, 27, 28 and 29 say "Research manuscript
prepared for Vladimir Reshetnikov", 22 and 25 "Prepared for Vladimir
Reshetnikov", 30 "Research article prepared for Vladimir Reshetnikov"; sources
19–26, 28 and 29 call themselves AI-assisted (23–26 and 28 add "unrefereed",
19 and 29 "not a refereed publication"/"paper"), source 27 makes "no claim of
historical priority or external peer review", and source 30 reports
"independent AI-assisted proof review". Source 31 says "Research article
prepared for Vladimir Reshetnikov", does not use the word AI-assisted, claims
no machine-checked proof or established priority, and names expert review of
its localized theorem as "the next scholarly step". Of batch 96, sources 32
and 33 say "Research manuscript prepared for Vladimir Reshetnikov" and call
themselves AI-assisted and unrefereed; sources 34 and 35 say "Research report
prepared for Vladimir Reshetnikov", "not a refereed publication" and
"unrefereed", with "independent mathematical checks during preparation". Source
36 has no author line ("An investigation prompted by the ProveIt repository"),
does not use the word AI-assisted, and reports "conventional written proofs
with independent review during preparation". The report is
AI-assisted, unrefereed and not formalized. Its review in the collection's
[review record](../../REVIEW.md) is **pending**, and it is not yet indexed in
the [formalization ledger](../../FORMALIZATION.md). The four batch-80
archives have a written-proof review in the Hilbert's-tenth research tree,
and the batch-80 merged text a scoped synthesis review and a preservation
audit there, whose corrections are applied; no review of the batch-81,
batch-83 or batch-89 sources exists yet, and the four batch-96 archives have a
bounded intake review there that checks source 34's choice-free power theorem
only, and a later bounded publication review there checks the selected GB
history and completion chain and corrects three metadata claims without
certifying all of Part XVI; source 36's archive has a bounded intake review
there that checks its arithmetic and notation proofs but not its spectrum
proofs (see "Reviews" below).

| Source | Batch, manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 11 (base) | 80, 11 | `surreal_well_orders (1).zip` (*Lexicographic Orders of Well-Orderings of the Surreal Numbers: Set Approximations, Class Orders, and Higher-Order Structure*; 2,807 lines, 35-page PDF; dated "3 October 2026", the UTC date of its pin) | `ae7c1e6aa` (2 October 2026, 18:03:53 PDT = 3 October, 01:03:53 UTC) | `ccc046989` | abstract and Status paragraph; Sections 2–3; 5.1, 5.3, 5.7; 6 (before 6.1); 7 (before 7.1); 9–12; 13 (before 13.1); 14 (before 14.1); 15; 16 (before 16.1); 19 (its own subsections 19.1, 19.2, 19.4, 19.5, 19.8, 19.11); 20; 113.1; 115 (before 115.1); Appendix A (before A.1) |
| 12 | 80, 12 | `surreal_well_orders.zip` (*Well-Orders of the Surreal Numbers and Their Lexicographic Geometry*; 1,689 lines, 24-page PDF) | `115bb8b1d9` (18:01:32 PDT) | `ccc046989` | Sections 4.1, 5.4, 6.2 (route), 8 (new), 13.1, 14.1, 16.1 (routes), 18, 19.9, 19.10, 21, 24, 113.2, 114.1, 115.1, A.1, C; Lemmas 5.3, 5.14–5.15 and 19.5; Notes 19.11, 19.21, 19.28 |
| 09 | 80, 09 | `Surreal_Well_Orders_Research.zip` (*Well-orders of the Surreal Numbers: Lexicographic universality, a surreal dense core, and the boundary between sets and classes*; 1,677 lines, 24-page PDF) | `115bb8b1d9` | `ccc046989` | Sections 4.2, 5.5, 5.8, 6.3, 7.1, 11.1, 13.2, 19.3, 19.6, 19.12, 22, 25, 113.3, 114.2, 115.2, A.2, A.3, C; Proposition 19.24; notes in Sections 6, 11 and 19 |
| 08 | 80, 08 | `Surreal_Well_Orders_Research (1).zip` (*Lexicographic Orders of Surreal Well-Orderings: Set-sized spectra, global enumeration orders, and a surreal-sized dense skeleton*; 2,022 lines, 26-page PDF) | `ae7c1e6aa` | `ccc046989` | Sections 4.3, 4.4, 5.2, 5.6, 7.2, 17, 19.7, 23, 26, 113.4, 114.3, 115.3, A.4, A.5, C; notes and printed paragraphs in Sections 5, 6, 7, 11 and 19 |
| 13 | 81, 01 | `Surreal_Well_Orders_Further_Study.zip` (*Lexicographic Orders of Surreal Well-Orderings: Further Structure*, title page "Cut reconstruction, asymmetric products, prefix non-rigidity, and size-safe foundations"; 2,215 lines, 33-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.6; 32 (Part VI); 34–36 (Part VII); 42, 46, 47 (Part VIII); 51, 55, 57, 59 (Part IX); 113.6, 114.4, A.6, A.7, C, D |
| 14 | 81, 02 | `lexicographic_surreal_well_orders_II.zip` (*Lexicographic Well-Orders of the Surreals II: cut classification, support thresholds, and class-model absoluteness*; 2,114 lines, 33-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.7, 4.12; 32; 34, 35; 40, 41, 43–45, 47–49 (base of Part VIII); 54, 56, 57, 59; 113.7, 114.5, 115.4, A.8, A.9, C, D |
| 15 | 81, 03 | `surreal_lexicographic_orders.zip` (*Lexicographic Orders of Surreal Well-Orders: interpretations, canonical blocks, represented cuts, and fixed-type spectra*; 2,596 lines, 37-page PDF) | `0ecd158fd` (also cites `491ed8411`) | `f0cd7032d` | Sections 4.8; 29–32 (block types: Section 31); 34, 38; 42, 46, 47; 51–53, 57, 59; 113.8, 115.5, A.10, C, D |
| 16 | 81, 04 | `surreal_well_orders_further.zip` (*Lexicographic Orders of Surreal Well-Orders: Cuts, Canonical Blocks, and the Limits of Set-Sized Coding*; 2,279 lines, 33-page PDF) | `491ed8411` | `f0cd7032d` | Sections 4.9; 27, 28, 30, 32; 34–36; 42, 46; 51, 52, 56, 57, 59; 113.9, 115.6, C, D |
| 17 | 81, 05 | `surreal_well_orders_further_study (1).zip` (*Lexicographic Well-Orders of the Surreal Numbers, II: exact cut spectra, branch recognition, optimal support reserves, and automorphism-extension obstructions*; 2,056 lines, 29-page PDF) | `0ecd158fd` | `f0cd7032d` | Sections 4.10, 4.13; 29, 30, 32; 34; 42, 46–49; 51, 54, 59; 113.10, 114.6, 115.7, A.11, C, D |
| 18 | 81, 06 (81L2) | `surreal_lexicographic_orders_further_study.zip` (*Lexicographic Well-Orders of the Surreal Numbers: Cuts, canonical class blocks, and changes of interpretation*; 3,928 lines, 53-page PDF) | `83befe707` | `c4720e1b2` | Sections 4.11; 27, 29, 30, 32; 34–37; 42, 46; 51, 52, 57–59; 113.11, 115.8, C, D |
| 19 | 83, 01 | `surreal_lexicographic_orders_continuation.zip` (*Lexicographic Orders of Surreal Well-Orders: Residual spectra, decorated completions, and model invariants*; 3,352 lines, 45-page PDF) | `d5bd4a67b` | `2e06337d5` | Sections 61.1–61.2 (scope); 62 (note), 64, 65, 67 (Part X); 73 (XI); 98–100 (XIII); 109 (XIV); 111.1–111.4; 113.13; C, D |
| 20 | 83, 02 | `surreal_orders_limits_symmetries_models.zip` (*Lexicographic Orders of Surreal Well-Orders: Coherent Limits, Nonextendible Symmetries, and Countable Models*; 3,686 lines, 50-page PDF) | `d5bd4a67b` | `2e06337d5` | Sections 61.3–61.4; 67 (X); 74 (XI); 97 (XIII); 107–109 (XIV); 111.5–111.7; 113.14; C, D |
| 21 | 83, 03 | `surreal_well_orders_further_structure.zip` (*Lexicographic Orders of Surreal Well-Orders: Further Structure, Automorphism Obstructions, and Model Dependence*; 3,329 lines, 44-page PDF) | `109aaca15` | `2e06337d5` | Sections 61.5–61.6; 62, 65, 67 (X); 75, 77 (XI); 86, 97, 102 (XIII); 109 (XIV); 111.8–111.9; 113.15; C, D |
| 22 | 83, 04 | `Surreal_Lexicographic_Orders_Residual_Geometry.zip`, inner `Surreal_Lexicographic_Orders/` (*Lexicographic Orders of Surreal Well-Orderings: Residual geometry, the finite-tail transition, unranked cylinders, and reconstruction of class realizations*; 1,067 lines, 33-page PDF) | `d5bd4a67b` | `2e06337d5` | Sections 61.7–61.8; 62 (note), 63 (X); 86, 87, 102 (XIII); 111.10–111.15; 113.16; C, D |
| 23 | 83, 05 | `Surreal_Lexicographic_Termination_Condensation.zip`, inner `surreal_lexicographic_further/` (*Lexicographic Surreal Well-Orders: Termination markers, increasing-word obstructions, and transfinite condensation*; 1,816 lines, 30-page PDF) | `109aaca15` | `2e06337d5` | Sections 61.9; 80–82 (XII); 106, 108 (XIV); 111.16–111.22; 113.17; C, D |
| 24 | 83, 06 | `Surreal_Lexicographic_Orders_Prefix_Completions.zip`, inner `surreal_lex_prefix_completions/` (*Lexicographic Well-Orders of the Surreals: Prefix completions, generalized Baire models, and the set–class boundary*; 1,197 lines, 32-page PDF) | `109aaca15` | `2e06337d5` | Sections 61.10–61.11; 62, 65–67, 69, 71 (X, base); 111.23–111.27; 113.18; C, D |
| 25 | 83, 11 | `Surreal_Well_Orders_Prefix_Symmetries.zip`, inner `surreal_prefix_symmetries/` (*Lexicographic Surreal Well-Orders: Prefix homogeneity, invisible exhaustiveness, and label rigidity*; 1,155 lines, 33-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.12–61.13; 86, 88–95, 103, 104 (XIII); 111.28–111.31; 113.19; C, D |
| 26 | 83, 12 | `Surreal_Lexicographic_Boundaries.zip` (*Lexicographic Well-Orders of the Surreals: Non-Borel boundaries, closed universality, and safe foundations*; 1,214 lines, 34-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.14–61.15; 62, 69, 71 (X); 111.32–111.35; 113.20; C, D |
| 27 | 83, 13 | `surreal_lexicographic_orders.zip` (*Lexicographic Orders of Surreal Well-Orders: Further Structure from Encodings, Prefix Trees, and Support Bounds*; 2,336 lines, 34-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.16; 80, 82, 84 (XII); 96, 101, 102 (XIII); 107, 110 (XIV); 111.36–111.38; 113.21; C, D |
| 28 | 83, 14 | `Surreal_Lexicographic_Group_Envelope.zip` (*Lexicographic Well-Orders of the Surreals: Singular permutation geometry and the canonical group envelope*; 1,204 lines, 32-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.17–61.18; 62 (note), 70, 71 (X); 111.39–111.43; 113.22; C, D |
| 29 | 83, 15 | `surreal_orders_new_structures.zip` (*Lexicographic Orders of Surreal Well-Orders: Exact Birthday Spectra, Word Products, Topological Transitions, and Class Comparability*; 4,470 lines, 57-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.19–61.20; 68 (X); 76, 78 (XI); 80, 82, 83 (XII); 86, 96 (XIII); 108 (XIV); 111.44–111.45; 113.23; C, D |
| 30 | 83, 16 | `surreal_well_orders.zip`, inner `surreal_well_orders/` (*Lexicographic Well-Orders of the Surreals: Residual Codes, Topological Transitions, and Class Reconstruction*; 3,583 lines, 47-page PDF) | `7ff7736ec` | `2e06337d5` | Sections 61.21; 63, 64, 68 (X); 80, 84 (XII); 102 (XIII); 109 (XIV); 111.46–111.48; 113.24; C, D |
| 31 | 89, 01 | `global_choice_surreal_coding.zip`, same inner directory (*Countable Global Choice and Surreal Coding over Zermelo Set Theory: A localized nonconservativity theorem and exact rank-model spectra*; 1,547 lines, 21-page PDF) | `2b7b388ba` | `23adb85f9` (nothing staged) | Part XV whole (Sections XV.1–XV.12 its Sections 1–12, XV.13–XV.14 its Appendices A–B, XV.15 status); 1.3.3, 1.10; 113.26–113.27; A.12; C, D |
| 34 (base of XVI) | 96, 10 | `beyond_ord.zip`, same inner directory (*Beyond Ord: Definable Class Well-Orders, Canonical Arithmetic, and the Limits of Notation*; 2,314 lines, 32-page PDF) | `e1d2f3048` | `111c38012` | Sections XVI.1–XVI.10 (its Sections 1–10, whole, with its numbering: its statement *k.m* is XVI.*k.m*), XVI.11.1 (its Appendix A); its agenda R1–R12 in 113.28; 1.3.4, 1.11; A.13; C; D.24 |
| 35 | 96, 11 | `class_orders_beyond_ord.zip`, same inner directory (*Definable Class Well-Orders Beyond Ord: Arithmetic, canonical notation, fixed-point completion, and the limits of uniform definability*; 3,132 lines, 40-page PDF) | `f158f27b4` | `111c38012` | "Source 35" subsections of XVI.1–XVI.10 (its Sections 1–7 in XVI.1–XVI.7, its Section 3 split between XVI.3 and XVI.4, Sections 5–6 in XVI.6, Section 8 in XVI.9, Sections 9.1–9.3 in XVI.8 and 9.4–9.5 in XVI.10), XVI.11.2; 113.28; C; D.25 |
| 32 | 96, 08 | `Beyond_Ord_Research.zip`, same inner directory (*Beyond Ord: Definable Class Well-Orders. Explicit arithmetic, condensation, definability ceilings, and truth jumps*; 982 lines, 27-page PDF) | commit `8f7d4a5c8` (its "root tree") | `111c38012` | "Source 32" subsections of XVI.1–XVI.10, XVI.11.3–XVI.11.5; 113.28; C; D.26 |
| 33 | 96, 09 | `Beyond_Ord_Class_Well_Orders.zip`, same inner directory (*Beyond Ord: Definable Class Well-Orders, Arithmetic, Condensation, and Definability Heights*; 1,981 lines, 30-page PDF) | none (two blobs; between `c14a866bc` and `e3839ad2c`) | `111c38012` | "Source 33" subsections of XVI.1–XVI.10, XVI.11.6–XVI.11.8; 113.28; C; D.27 |
| 36 | 97, 01 | `Beyond_Ord_Research_Package.zip`, inner directory `Beyond_Ord` (*Beyond Ord: Definable Class Well-Orders, Finite-Support Arithmetic, and Definability Horizons*; 2,950 lines, 40-page PDF; no author line, "October 2026") | `e1d2f3048` (the pin of source 34) | `6571ee1af` | Sections XVII.1–XVII.10 (its Sections 1–9 and Appendix A, whole, with its numbering: its statement *k.m* is XVII.*k.m*), XVII.11 status; its questions in 113.30, dated notes 113.31; 1.3.5, 1.12; A.14; C; D.28 |

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
that no existing section is renumbered), their questions in Section 113.5–113.11.

The twelve batch-83 sources are independent texts, not editions: every pair
shares at most 3.3 % of word 8-grams (source 28 with 24; 22 with 25 2.4 %;
every other pair, and each source against this report and sources 13–18, at
most 2.2 %), no member file is shared, and the theorem sets differ. Three name
coincidences are not editions: source 27's archive, inner directory and main
file have the names of source 15's (`surreal_lexicographic_orders.zip`;
different title, pin and theorems, 0.6 % overlap); source 30's archive has the
name of source 12's and its inner directory and main file those of sources 11
and 08 (`surreal_well_orders.zip`; at most 0.5 %); source 23's inner directory
is source 13's (`surreal_lexicographic_further/`). They read this report at
`d5bd4a67b` (19, 20, 22) and `109aaca15` (21, 23, 24), both with Parts I–V
only, and at `7ff7736ec` (25–30), with Parts I–VIII. Several read unplaced
manuscripts that are now sources here (19: 15, 16, 18; 20: 18; 22 and 23: 13,
17; 24: 13, 14, 17; 25: 13, 17, 22, 23; 26: 24; 28: 13, 24; 29: 19, 20, 21);
21, 27 and 30 cite none. They overlap heavily (the countable-cutoff theorem is
proved by seven of them, the represented-cut theorem three more times, the
faithful reconstruction of a class realization three times), so they are
printed by theme after Part IX: X set-sized strata, topology and permutation
groups (base 24; 19, 21, 22, 26, 28, 30); XI across birthday cutoffs (19, 20,
21, 29); XII words, termination markers and comparison codes (23, 27, 29, 30);
XIII the core and its cylinders (25, 22, 20, 21, 19, 27, 29, 30); XIV
unrestricted class well-orders II (20, 19, 21, 23, 27, 29, 30). Their scope
sections head Part X (Section 61; the maps of 23, 27, 29 and 30 are in Section
80 of Part XII), their foundations, Lean plans, ledgers and verification
records close Part XIV (Section 111, before Part XIV's status section, as Part
IX's Lean plans precede its own; the foundations of 24, 26 and 28 are in
Section 71, source 25's size audit in Section 104, source 27's foundations in
Section 110), their questions are in Section 113.12–113.25 with an index and
dated status notes, and their abstracts in Appendix C. Source 28's headline
question (complete metrizability of the full singular permutation space) is
answered negatively in ZFC by source 26, which 28 did not see; it is printed
with that status (Note 70.13).

The batch-89 source 31 is an independent text, not an edition: it shares no
file with any earlier source, 0.6 % of its word 8-grams occur in this report
(bibliography and standard phrasing), and it shares at most 0.33 % with the
other four batch-89 manuscripts, which are placed in other reports. It read
this report at `2b7b388ba`, whose `article.tex` (blob `05807d292`) is the text
of the batch-83 write with Parts I–XIV, and it starts from three of its labels:
the global-choice equivalence `swo:cf:choice` (Theorem 13.1), source 12's
inaccessible full-class model `swo:st:thm:model` (Theorem 21.1) and source 28's
question `swo:ge:n10` (Research question 113.209). Being a single source with
material of its own, it is printed whole and in its own order as Part XV:
Sections XV.1–XV.12 are its Sections 1–12 (its statement *k.m* is XV.*k.m*),
XV.13 and XV.14 its Appendices A (axiom ledger) and B (source audit), and XV.15
the status section; its twelve questions are Section 113.26, with dated status
notes in 113.27, its abstract closes Appendix C, and its 43 numbered statements
are mapped in Appendix D. The Part numbers its sections XV.1–XV.15 so that the
questions part keeps Sections 113–115 and no number printed before this write
changes (the batch-81 and batch-83 writes had moved the closing sections).

The four batch-96 sources 32–35 are independent texts, not editions: no file
is shared, every pair shares at most 1.64 % of word 8-grams (34 with 35), and
each at most 1.62 % with this report (preambles, bibliography, quoted
phrasing). They answer one request independently, and their main theorems
overlap heavily. All four read this report with Parts I–XV, exactly as before
this write: sources 34 and 35 at `e1d2f3048` and `f158f27b4`, source 32 at the
commit `8f7d4a5c8` (which it calls a "root tree"), and source 33 at an unrecorded
revision between `c14a866bc` and the arrival (it records only two README
blobs); at all of these `article.tex` is blob `72eee5cc8` and the README blob
`d2e24b58`. Sources 34 and 35 prove independently that `CWO`, `CTH` and the two
polynomial forms are equivalent over GB with ZF sets and no choice, which this
report listed as open after source 29's GBC theorem. They are merged as Part
XVI with source 34 as base, because on the shared theorems it has the weakest
hypotheses (GB for the equivalence, as 35; GB for the hereditary order, where
32, 33 and 35 use GBC; any transitive β-model for the definable ceiling, where
32 and 33 use `V_κ`). Sections XVI.1–XVI.10 are source 34's Sections 1–10
whole, in order and with its own numbering (its statement *k.m* is XVI.*k.m*),
each followed by subsections printing the corresponding sections of sources 35,
32 and 33; XVI.11 collects the four sources' ledgers and audits and XVI.12 is the
status section. Like Part XV, the Part numbers its sections XVI.1–XVI.12, so no
earlier number changes. The four sources' 50 research questions (34's agenda
R1–R12, 35's 13, 32's 11, 33's 14) are merged by theme in Section 113.28, with
dated notes on earlier questions in 113.29; their abstracts close Appendix C,
their delivery record is A.13, and their 188 numbered statements and agenda
items are mapped in Appendix D.24–D.27.

Source 36 (batch 97) is an independent fifth answer to the same request: it
shares no file with sources 32–35 and 0.36–0.78 % of word 8-grams with each,
and 0.90 % with this report including Part XVI. It read this report at
`e1d2f3048`, with Parts I–XV, and did not see Part XVI, which was written
and committed before it could join that merge. It is printed whole as Part
XVII, as source 31 is in Part XV: Sections XVII.1–XVII.8 are its Sections
1–8 with its numbering, XVII.9 its Section 9 (its ten questions are printed
in Section 113.30), XVII.10 its Appendix A and XVII.11 the status section.
Where it proves a result of Part XVI again (set localization, the power
calculus, the hereditary order, the uniform diagonal, the `V_κ` horizon
theorem, the bounded-complexity diagonal, truth promotion and others), a
numbered credit Note follows its statement; the fifteen credit Notes are
numbered XVII.*k*.A, XVII.*k*.B, … so that no source number moves. Its
novelty sentences carry dated credit notes to sources 32–34, and the stronger
leastness that its proof of Theorem XVII.4.5 gives is stated in Note XVII.4.B
with credit to source 34. Its 42 numbered statements and 10 questions are
mapped in Appendix D.28.

Every result, proof, example, remark, question and limitation of the
twenty-eight manuscripts is printed. A result proved again by the same argument is
recorded in a numbered **Note** that gives the source's statement, number and
differences, or, where each source builds on its own proof, printed whole as
a marked route under a credit note (the represented-cut theorem is proved six
times in batches 80–81, Note 46.1, and nine times with batch 83, Note 87.6; the
block decomposition three times, Note 52.1; the countable-cutoff theorem by
seven batch-83 sources, Note 67.1);
source-specific results are printed in full where they belong. Each source's
introduction, foundational section, model section, Lean plan, questions,
conclusion, ledger and reproducibility record are printed whole. Text written
for the merge is marked `[merge]`. Appendix D maps every numbered statement of
the twenty-eight sources (311 of sources 13–18, 644 of sources 19–30, 43 of
source 31, 176 of sources 32–35 and source 34's 12 agenda items, 52 of source
36) to its place here. For source 36 a line-by-line check (`coverage97.py` of
the write, not shipped) confirms that of the 2,357 non-blank, non-comment
lines of its body (its lines 136–2830, Sections 1–9 and Appendix A), 2,187
are printed verbatim up to label prefixes, citation keys and macro names, and
the other 170 differ only by the renamings of Section 1.3.5 (finite-support
powers `A^{[B]}`, horizons `𝔥`, height stages `𝖤^{≤n+1}`), by tagged displays
printed as starred displays, by question headings, or by one citation of its
starred equation by its tag; its title page and abstract are printed in
Appendix C. For sources 32–35 a line-by-line check (`coverage.py` of the write, not
shipped) confirms that every non-blank, non-comment line of each delivered
body (from `\begin{document}` to the bibliography) is printed verbatim, up to
the renamings and label prefixes of Section 1.3.4, except: title-page and
abstract wrappers (the titles are printed in Appendix C); section headings
replaced by merge headings that carry the source's label; source 34's twelve
`\item` lines of its agenda, replaced by question headings; and the statements
and proofs recorded in numbered Notes (source 35 22, source 32 13, source 33
18 statements), each of which restates the statement and names the printed
statement it repeats. Of 1,922 such lines of source 34, 1,893 are printed
verbatim; of source 35's 2,613, 2,050; of source 32's 670, 492; of source
33's 1,613, 1,264. A line-by-line check confirms that every
non-blank line of source 31's abstract, scope statement and body (its lines
75–106 and 116–1475) is printed, verbatim up to the renamings and label
prefixes of Section 1.3.3, except its `\vfill`, `\clearpage` and `\appendix`
lines; its Section 13 heading, replaced by the heading of Section 113.26; the
first line of its scope statement, printed in a quotation without
`\noindent\small`; and seven lines that gained a cross-reference, a label, a
`[merge]` annotation or ragged-right table columns. Its title, byline and date
are printed in Appendix C, and its bibliography as entries with the key prefix
`gcz` or as the existing `HamkinsGC` and `HamkinsRecursionPrinciple`. For
sources 19–30 the write also checked, line by line, that every non-blank line of each delivered `.tex` body is printed, or is a section heading
replaced by a merge heading carrying the source's label, a bibliography line, a
source part divider, or a duplicate recorded in a numbered note that quotes the
statement (Part X's notes on sources 19, 21, 22, 24, 26, 28 and 30 and Part
XI's on source 29 keep the statement and cite the printed proof).

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 1,050 pages (title page unnumbered)
README.md                                this guide
09-core-RESEARCH_STATUS.md               source 09's research status and audit, as delivered
11-raw-orders-repository_audit.md        source 11's targeted repository audit, as delivered
12-singular-RESEARCH_STATUS.md           source 12's research status and audit, as delivered
13-products-RESEARCH_STATUS.md           source 13's research status and audit, as delivered
14-trichotomy-RESEARCH_STATUS.md         source 14's research status and audit, as delivered
16-strata-SOURCE_STATUS.txt              source 16's source and proof status, as delivered
17-gaps-research_status.md               source 17's research status, as delivered
19-residual-source_status.txt            source 19's source and proof-status record, as delivered
21-obstructions-LEAN_INTERFACE_AUDIT.txt source 21's audit of the Lean declarations it cites, as delivered
21-obstructions-SOURCE_AUDIT.txt         source 21's repository and literature audit, as delivered
22-unranked-RESEARCH_STATUS.md           source 22's research status, as delivered
22-unranked-SOURCE_AUDIT.md              source 22's source audit, as delivered
23-termination-RESEARCH_STATUS.md        source 23's research status, as delivered
23-termination-SOURCE_AUDIT.md           source 23's source audit, as delivered
24-completions-SOURCE_AUDIT.md           source 24's source audit, as delivered
25-symmetries-RESEARCH_STATUS.md         source 25's research status, as delivered
25-symmetries-SOURCE_AUDIT.md            source 25's source audit, as delivered
26-nonborel-RESEARCH_STATUS.md           source 26's research status and audit, as delivered
27-scans-SOURCE_AUDIT.txt                source 27's source audit, as delivered
28-envelope-SOURCE_AUDIT.md              source 28's source audit, as delivered
29-birthdays-PROOF_STATUS.txt            source 29's proof-status guide, as delivered
29-birthdays-SOURCE_AUDIT.txt            source 29's source audit, as delivered
30-tables-proof_review.txt               source 30's proof-review record, as delivered
30-tables-source_audit.txt               source 30's source audit, as delivered
32-ceilings-PROOF_STATUS.md              source 32's proof, source and computational status, as delivered
33-heights-PROOF_STATUS.md               source 33's proof status and assumptions, as delivered
33-heights-SOURCE_AUDIT.md               source 33's source and repository audit, as delivered
34-choicefree-PROOF_STATUS.txt           source 34's proof status and assumption ledger, as delivered
36-horizons-SOURCE_AUDIT.txt             source 36's repository snapshot and literature audit, as delivered
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
code/19-residual-build.sh                source 19's build script (compiles an unshipped .tex; builds nothing here)
code/19-residual-check_restrictions.py   source 19's finite check (writes restriction_checks.json beside itself)
code/20-limits-finite_diagnostics.py     source 20's finite diagnostics (--output, else standard output)
code/22-unranked-build.sh                source 22's build script (builds nothing here)
code/22-unranked-finite_checks.py        source 22's finite checks
code/23-termination-build.sh             source 23's build script (builds nothing here)
code/23-termination-finite_checks.py     source 23's finite checks
code/24-completions-build.sh             source 24's build script (builds nothing here)
code/24-completions-finite_checks.py     source 24's finite checks (default output beside code/)
code/25-symmetries-build.sh              source 25's build script (builds nothing here)
code/25-symmetries-finite_checks.py      source 25's finite checks
code/26-nonborel-build.sh                source 26's build script (builds nothing here)
code/26-nonborel-finite_checks.py        source 26's finite checks
code/27-scans-finite_checks.py           source 27's finite checks (--output, else standard output)
code/28-envelope-build.sh                source 28's build script (builds nothing here)
code/28-envelope-finite_checks.py        source 28's finite checks (--output, else standard output)
code/30-tables-build.sh                  source 30's build script (compiles an unshipped .tex; builds nothing here)
code/30-tables-verify_finite.py          source 30's finite checks (default output beside itself)
code/32-ceilings-Makefile                source 32's Makefile (compiles an unshipped .tex; builds nothing here)
code/32-ceilings-finite_checks.py        source 32's finite checks (--output)
code/33-heights-build.sh                 source 33's build script (compiles an unshipped .tex; builds nothing here)
code/33-heights-finite_checks.py         source 33's finite checks (--output)
code/35-completion-finite_notation_checks.py  source 35's finite illustrations (writes beside itself)
code/36-horizons-build.sh                source 36's build script (compiles an unshipped .tex; builds nothing here)
code/36-horizons-notation_demo.py        source 36's notation demonstrator (PYTHONUTF8=1 on Windows; --report overwrites its argument)
data/08-skeleton-verification_results.json     source 08's recorded run
data/09-core-finite_checks.json                source 09's recorded run
data/11-raw-orders-finite_checks_results.txt   source 11's recorded run
data/12-singular-finite_checks.json            source 12's recorded run
data/13-products-finite_results.json           source 13's recorded run
data/13-products-pdf_inspection.json           source 13's record of the layout check of its (unshipped) PDF
data/14-trichotomy-verification_results.json   source 14's recorded run
data/15-blocks-finite_examples.txt             source 15's recorded output
data/16-strata-finite_check_results.json       source 16's recorded run
data/17-gaps-finite_checks.json                source 17's recorded run
data/19-residual-restriction_checks.json       source 19's recorded run
data/20-limits-finite_diagnostics_results.json source 20's recorded run
data/22-unranked-finite_checks.json            source 22's recorded run
data/22-unranked-pdf_validation.json           source 22's record of the layout check of its (unshipped) PDF
data/23-termination-finite_checks.json         source 23's recorded run
data/24-completions-build_validation.json      source 24's build record (hashes of its unshipped .tex and PDF)
data/24-completions-finite_checks.json         source 24's recorded run
data/25-symmetries-finite_checks.json          source 25's recorded run
data/26-nonborel-finite_checks.json            source 26's recorded run
data/27-scans-finite_checks.json               source 27's recorded run
data/28-envelope-finite_checks.json            source 28's recorded run
data/29-birthdays-source_manifest.json         source 29's provenance manifest (see below)
data/29-birthdays-verification.json            source 29's build and document metadata
data/30-tables-verification_results.json       source 30's recorded run
data/32-ceilings-finite_checks.json            source 32's recorded run
data/33-heights-BUILD_REPORT.json              source 33's record of its (unshipped) PDF build
data/33-heights-verification_results.json      source 33's recorded run
data/35-completion-finite_notation_results.json source 35's recorded run
data/36-horizons-DOCUMENT_CHECKS.json          source 36's record of its (unshipped) PDF build and four package hashes
data/36-horizons-verification.json             source 36's recorded run
```

All code, data and the 29 audit and status files are byte-identical to the
delivery. Source 18 shipped no code or data; source 15 no status file. Of batch
83 (49 files, 211,105 bytes; no CR bytes, longest path 133 characters, none
over 1 MB), sources 21 and 29 shipped no code, source 21 no data, and source 20
no status file. Source 31 (batch 89) shipped no code, data, audit or status
file: its archive holds only its manuscript, its PDF and a delivery
`README.txt`, so nothing of it is in this directory except the text of Part XV
and its related sections. Of batch 96 (13 files, 39,802 bytes; LF only, longest
path 123 characters, none over 1 MB), source 34 shipped only its status file
and source 35 no status file; source 34 shipped no code or data. Of batch 97,
source 36 ships 5 files (24,944 bytes; LF only; longest path 113 characters
below the repository root; none over 1 MB): its source audit, build script,
demonstrator, recorded run and document-check record. Its demonstrator's
guide (`code/README.md`) is not shipped; its scope text is reproduced under
"Rerunning the checks".

**Disclosure for `data/29-birthdays-source_manifest.json`.** Source 29's
provenance manifest mixes SHA-256 hashes (sixteen repository files at its pin,
the delivered `.tex` of sources 19, 21 and 20, which the hashes match, and its
six deliverables; all verified at placement) with provenance fields. Three of
those fields, `persistent_file_identity`, hold opaque library-file identifiers
(`libfile_…`) of the authoring tool for the three earlier manuscripts. They are
identifiers, not credentials, are shipped as delivered because delivered bytes
are not edited, and identify nothing in this repository.

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
| 19 | `source_status.txt`, `build.sh`, `check_restrictions.py`, `restriction_checks.json` | `19-residual-source_status.txt`, `code/19-residual-build.sh`, `code/19-residual-check_restrictions.py`, `data/19-residual-restriction_checks.json` |
| 20 | `finite_diagnostics.py`, `finite_diagnostics_results.json` | `code/20-limits-finite_diagnostics.py`, `data/20-limits-finite_diagnostics_results.json` |
| 21 | `SOURCE_AUDIT.txt`, `LEAN_INTERFACE_AUDIT.txt` | `21-obstructions-SOURCE_AUDIT.txt`, `21-obstructions-LEAN_INTERFACE_AUDIT.txt` |
| 22 | `RESEARCH_STATUS.md`, `SOURCE_AUDIT.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json`, `data/pdf_validation.json` | `22-unranked-RESEARCH_STATUS.md`, `22-unranked-SOURCE_AUDIT.md`, `code/22-unranked-build.sh`, `code/22-unranked-finite_checks.py`, `data/22-unranked-finite_checks.json`, `data/22-unranked-pdf_validation.json` |
| 23 | `RESEARCH_STATUS.md`, `SOURCE_AUDIT.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `23-termination-RESEARCH_STATUS.md`, `23-termination-SOURCE_AUDIT.md`, `code/23-termination-build.sh`, `code/23-termination-finite_checks.py`, `data/23-termination-finite_checks.json` |
| 24 | `SOURCE_AUDIT.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json`, `data/build_validation.json` | `24-completions-SOURCE_AUDIT.md`, `code/24-completions-build.sh`, `code/24-completions-finite_checks.py`, `data/24-completions-finite_checks.json`, `data/24-completions-build_validation.json` |
| 25 | `RESEARCH_STATUS.md`, `SOURCE_AUDIT.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `25-symmetries-RESEARCH_STATUS.md`, `25-symmetries-SOURCE_AUDIT.md`, `code/25-symmetries-build.sh`, `code/25-symmetries-finite_checks.py`, `data/25-symmetries-finite_checks.json` |
| 26 | `RESEARCH_STATUS.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `26-nonborel-RESEARCH_STATUS.md`, `code/26-nonborel-build.sh`, `code/26-nonborel-finite_checks.py`, `data/26-nonborel-finite_checks.json` |
| 27 | `SOURCE_AUDIT.txt`, `finite_checks.py`, `finite_checks.json` | `27-scans-SOURCE_AUDIT.txt`, `code/27-scans-finite_checks.py`, `data/27-scans-finite_checks.json` |
| 28 | `SOURCE_AUDIT.md`, `build.sh`, `code/finite_checks.py`, `data/finite_checks.json` | `28-envelope-SOURCE_AUDIT.md`, `code/28-envelope-build.sh`, `code/28-envelope-finite_checks.py`, `data/28-envelope-finite_checks.json` |
| 29 | `SOURCE_AUDIT.txt`, `PROOF_STATUS.txt`, `source_manifest.json`, `verification.json` | `29-birthdays-SOURCE_AUDIT.txt`, `29-birthdays-PROOF_STATUS.txt`, `data/29-birthdays-source_manifest.json`, `data/29-birthdays-verification.json` |
| 30 | `source_audit.txt`, `proof_review.txt`, `build.sh`, `verify_finite.py`, `verification_results.json` | `30-tables-source_audit.txt`, `30-tables-proof_review.txt`, `code/30-tables-build.sh`, `code/30-tables-verify_finite.py`, `data/30-tables-verification_results.json` |
| 32 | `PROOF_STATUS.md`, `Makefile`, `finite_checks.py`, `finite_checks.json` | `32-ceilings-PROOF_STATUS.md`, `code/32-ceilings-Makefile`, `code/32-ceilings-finite_checks.py`, `data/32-ceilings-finite_checks.json` |
| 33 | `PROOF_STATUS.md`, `SOURCE_AUDIT.md`, `build.sh`, `finite_checks.py`, `verification_results.json`, `BUILD_REPORT.json` | `33-heights-PROOF_STATUS.md`, `33-heights-SOURCE_AUDIT.md`, `code/33-heights-build.sh`, `code/33-heights-finite_checks.py`, `data/33-heights-verification_results.json`, `data/33-heights-BUILD_REPORT.json` |
| 34 | `PROOF_STATUS.txt` | `34-choicefree-PROOF_STATUS.txt` |
| 35 | `artifacts/finite_notation_checks.py`, `artifacts/finite_notation_results.json` | `code/35-completion-finite_notation_checks.py`, `data/35-completion-finite_notation_results.json` |
| 36 | `Beyond_Ord/SOURCE_AUDIT.txt`, `Beyond_Ord/build.sh`, `Beyond_Ord/code/notation_demo.py`, `Beyond_Ord/code/verification.json`, `Beyond_Ord/DOCUMENT_CHECKS.json` | `36-horizons-SOURCE_AUDIT.txt`, `code/36-horizons-build.sh`, `code/36-horizons-notation_demo.py`, `data/36-horizons-verification.json`, `data/36-horizons-DOCUMENT_CHECKS.json` |

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

Not shipped from batch 83 (recoverable with
`git show <arrival>:"docs/incoming/<archive>.zip"`, the arrival being
`b63f0c852` for sources 19–24, `5ad44b1ed` for 25, `0d7b2441d` for 26,
`79049d58c` for 27–28 and `51b0a69d7` for 29–30): the twelve manuscripts and
their PDFs (19 45 pages, 20 50, 21 44, 22 33, 23 30, 24 32, 25 33, 26 34, 27
34, 28 32, 29 57, 30 47); the delivery READMEs (`README.txt` of 19, 20, 21, 27,
29 and 30, `README.md` of 22–26 and 28); and the checksum manifests
`SHA256SUMS.txt` of 22 (9/9), 23 (8/8), 24 (8/8), 25 (8/8), 26 (7/7) and 28
(7/7), all verified at placement. Nothing was excluded as regenerable.

Not shipped from batch 89 (recoverable with
`git show 7c0f2d9f9:docs/incoming/global_choice_surreal_coding.zip`): source
31's manuscript `global_choice_surreal_coding.tex` (1,547 lines, 70,676 bytes),
its 21-page PDF (400,246 bytes) and its `README.txt` (2,590 bytes), all inside
the inner directory `global_choice_surreal_coding/`. It shipped no checksum
manifest, and nothing was excluded as regenerable. Its README's build command
compiles the unshipped `.tex`; rebuilt from a fresh extraction with MiKTeX on 3
October 2026, it gives 21 pages without warnings.

Not shipped from batch 96 (recoverable with
`git show e3839ad2c:docs/incoming/<archive>.zip`, the archives being
`Beyond_Ord_Research.zip` (source 32), `Beyond_Ord_Class_Well_Orders.zip` (33),
`beyond_ord.zip` (34) and `class_orders_beyond_ord.zip` (35), each with an inner
directory of the same name): the four manuscripts (`beyond_ord.tex` of 32 and of
34, `article.tex` of 33, `class_orders_beyond_ord.tex` of 35) and their PDFs (32
27 pages, 33 30, 34 32, 35 40); the delivery READMEs (`README.md` of 32 and 33,
`README.txt` of 34 and 35); and the checksum manifests `SHA256SUMS` of 32 (7/7)
and `MANIFEST.sha256` of 33 (9/9), verified at placement. Nothing was excluded
as regenerable.

Not shipped from batch 97 (recoverable with
`git show d7cf7d554:docs/incoming/Beyond_Ord_Research_Package.zip`, inner
directory `Beyond_Ord/`): source 36's manuscript `beyond_ord.tex` (2,950
lines, 130,010 bytes), its 40-page PDF (674,664 bytes), its delivery
`README.txt` (3,348 bytes) and the demonstrator's guide `code/README.md`
(5,590 bytes). It shipped no checksum manifest; the `sha256` block of
`DOCUMENT_CHECKS.json` (manuscript, PDF, demonstrator, report) matches the
delivered files. Nothing was excluded as regenerable.

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
Section 115, which name delivery files (annotated there and in Appendix B).
Of batch 83, the shipped audit and status files and the build scripts name
delivery files (`article.tex`, `article.pdf`, `SHA256SUMS.txt`,
`code/finite_checks.py`, `data/finite_checks.json`, the manuscripts' own `.tex`
and PDF names) and other manuscripts by library names: `surreal_well_orders_II.pdf`
is source 17, `Surreal_Well_Orders_Further_Study.tex` source 13,
`article(20261003-193743).tex` source 23 and
`Surreal_Lexicographic_Orders_Prefix_Completions.tex` source 24. The table above
maps the names; the unshipped files are in the arrival commits. The records
printed in Section 111 (its subsections on checks, audits and the shipped checks,
111.49) name delivery files and are annotated there. Of batch 96:
`code/32-ceilings-Makefile` compiles `beyond_ord.tex` and writes
`finite_checks.json`, and `code/33-heights-build.sh` compiles `article.tex` into
`.build/` and copies `article.pdf` (both build nothing here);
`32-ceilings-PROOF_STATUS.md` names `finite_checks.json` (shipped as
`data/32-ceilings-finite_checks.json`) and describes its unshipped 27-page PDF;
`33-heights-PROOF_STATUS.md` names `article.tex` and the "generated package
manifest" (the unshipped `MANIFEST.sha256`); `data/33-heights-BUILD_REPORT.json`
describes the unshipped 30-page PDF; `34-choicefree-PROOF_STATUS.txt` describes
its own 32-page PDF and sections; source 35's program writes
`finite_notation_results.json` beside itself (here in `code/`), using
`Path(__file__).with_name`, independently of the working directory. The
appendices printed in Section XVI.11 name delivery files and carry
`[merge]` notes with the shipped names.
Of batch 97: `code/36-horizons-build.sh` compiles the unshipped
`beyond_ord.tex` (it builds nothing here); `36-horizons-SOURCE_AUDIT.txt`
names `beyond_ord.tex`; `data/36-horizons-DOCUMENT_CHECKS.json` names
`beyond_ord.tex`, `beyond_ord.pdf`, `code/notation_demo.py` and
`code/verification.json` (the delivery paths of the last two); the
demonstrator's documented command `--report code/verification.json` and its
printed rerun in Section XVII.10.2 use delivery paths, annotated there.

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
and `swo:ix:` in Parts VI–IX. The batch-83 sources' labels carry `swo:rs:` (19),
`swo:lm:` (20), `swo:fu:` (21), `swo:rg:` (22), `swo:tm:` (23), `swo:pc:` (24),
`swo:ph:` (25), `swo:nb:` (26), `swo:sc:` (27), `swo:ge:` (28), `swo:bw:` (29)
and `swo:rt:` (30), each before the delivered label unchanged, internal prefixes
included (21's and 29's `gl:` become `swo:fu:gl:` and `swo:bw:gl:`, unrelated to
source 11's `swo:gl:`); their displayed equations keep their numbers as
(S*NN*.*n*); merge labels begin `swo:x:`, `swo:xi:`, `swo:xii:`, `swo:xiii:`,
`swo:xiv:` in Parts X–XIV and `swo:b83:` in the front and back matter.
The batch-89 source 31's labels carry `swo:gcz:` before the delivered label;
its unlabelled numbered statements are `swo:gcz:n`*number* (`swo:gcz:n3.4`)
and its research questions, numbered 1–12 in its PDF, `swo:gcz:n1`–`swo:gcz:n12`
(as source 28's consecutive `swo:ge:n`*k*); its equations (1)–(10) are tagged
(S31.1)–(S31.10); the labels written for the merge also begin `swo:gcz:`.
The batch-96 sources' labels carry `swo:bo:` (34), `swo:fc:` (35), `swo:dc:`
(32) and `swo:dh:` (33) before the delivered label; unlabelled numbered
statements are *prefix*`n`*number* (`swo:fc:n2.1`), source 34's agenda items
`swo:bo:R1`–`swo:bo:R12`; displayed equations keep their numbers as (S34.*k*),
(S35.*k*), (S32.*k*) and (S33.*s*.*k*); the Part label is `swo:part:beyondord`
and the other labels written for the merge begin `swo:xvi:`.
The batch-97 source 36's labels carry `swo:hn:` before the delivered label
(its prefixes `intro:`, `ar:`, `ns:`, `hz:`, `form:`, `agenda:`, `audit:`);
its unlabelled Definition 6.1 is `swo:hn:n6.1` and its research questions,
numbered 1–10 in its PDF, `swo:hn:q1`–`swo:hn:q10`; its displayed equations
keep their numbers as (S36.*k*.*m*) and its starred equation as (S36.∗); the
Part label is `swo:part:horizons`, the merge labels begin `swo:xvii:`, and the
fifteen credit notes use a note counter of their own, printed XVII.*k*.A, ….

Totals: **2,293 labels** (2,188 before batch 97, 1,876 before batch 96, 1,799
before batch 89, 794 before batch 83; none renamed or lost). Batch 97 added
105: `swo:hn:` 81 (70 delivered labels of source 36, 1 for its unlabelled
Definition 6.1, 10 for its questions), `swo:xvii:` 23 (15 credit notes, the
notation addendum, the batch subsection, the status section, the two question
subsections, the delivery record, the abstract and the crosswalk) and
`swo:part:horizons`; every one of the 70 delivered labels is present exactly
once. Batch 96 added 312: `swo:bo:` 68 (53
delivered labels of source 34, 3 for its unlabelled statements, 12 for its
agenda items), `swo:fc:` 73 (57 + 16), `swo:dc:` 71 (55 + 15, and the merge
label `swo:dc:sec:conclusion` for its unlabelled conclusion), `swo:dh:` 84 (62
+ 22), `swo:xvi:` 15 and `swo:part:beyondord`; every one of the 227 delivered
labels of sources 32–35 is present exactly once. `swo:gcz:` 77: 47 delivered labels of source 31, 9 for its
unlabelled numbered statements, 12 for its questions, and 9 written for the
merge (`swo:gcz:part`, `swo:gcz:sub:notation89`, `swo:gcz:sub:batch89`,
`swo:gcz:sub:glazerinput`, `swo:gcz:sub:noexperiment`, `swo:gcz:sec:status`,
`swo:gcz:sec:qstatus`, `swo:gcz:app:delivery`, `swo:gcz:app:abstract`). Before
batch 89: `swo:`
only 103 (60 of source 11, 11 for its unlabelled statements, 21 merge labels
of batch 80, 6 of batch 81: four Part labels and two subsections; 5 Part labels
of batch 83), `swo:st:` 61, `swo:ec:` 52, `swo:sk:` 67 (as before), `swo:fs:`
62 (48 source labels + 14 for unlabelled statements), `swo:tc:` 62 (40 + 22),
`swo:cb:` 69 (51 + 18), `swo:ds:` 74 (62 + 12), `swo:gs:` 85 (56 + 29),
`swo:sh:` 98 (76 + 22); `swo:rs:` 91 (74 + 17), `swo:lm:` 79 (68 + 11),
`swo:fu:` 94 (91 + 3), `swo:rg:` 60 (39 + 21), `swo:tm:` 65 (48 + 16 + 1),
`swo:pc:` 72 (53 + 19), `swo:ph:` 65 (51 + 14), `swo:nb:` 72 (54 + 18),
`swo:sc:` 71 (56 + 15), `swo:ge:` 71 (52 + 19), `swo:bw:` 122 (109 + 11 + 2),
`swo:rt:` 76 (65 + 11); and merge labels `swo:vi:` 20, `swo:vii:` 12,
`swo:viii:` 15, `swo:ix:` 19, `swo:x:` 19, `swo:xi:` 2, `swo:xii:` 8,
`swo:xiii:` 9, `swo:xiv:` 13, `swo:b83:` 11. Three batch-83 labels with a source
sub-prefix were written for the merge (`swo:tm:sub:failures`,
`swo:bw:sec:increasing`, `swo:bw:sub:scans`). Every one of the 531 labels of
sources 08–18, of the 760 delivered labels of sources 19–30 and of the 47 of
source 31 is present exactly once. Cross-references are typed (lemma, note, …)
through alias counters. No `swo:` label has a Lean mapping.

## Notation (Sections 1.3, 1.3.1, 1.3.2, 1.3.3, 1.3.4 and 1.3.5)

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

For sources 19–30 (dated addendum, Section 1.3.2): source 26's alphabet size `κ`
and cutoff `θ` are printed `μ` and `κ`, as are source 27's (in its scan and
convex-copy sections) and source 23's `κ`, `λ` in its spectra section; at a
noncardinal cutoff `θ` the sources' `κ = |θ|`, `μ = 2^κ` are kept, with the
false reading printed. The core keeps its two codings by source: normalized
permutations `𝒫_bd(b)` for 19, 20, 21, 24, 26, 28 and 29 (29's `𝒫_bd(e)`),
support codes `𝒫_s(b)` for 22, 25, 27 and 30; source 25's two-sorted reduct
(its script `𝒞_b`) is `𝐂_b`. Source 19's and 29's residual weights and
weighted lengths `r(λ)`, `u_κ(λ)`, `R`, `U` are `wt(λ)`, `wt⁺_κ(λ)`, `ϱ_lo`,
`ϱ_up` (30's `r(ν)` is `wt(ν)`); their `r_κ` is `ρ_κ`; source 21's `br` and
29's `ℓ₂` are `ℓ₂`. The minimal slice and its injections are `𝒲_μ(X)`,
`𝓘_μ(X)`, `𝓘_{<μ}(X)`, `𝓘^b_μ` (24, 26, 28's `𝒫_μ(X)`, `𝓘_μ(X)`; 24's
`𝒯_μ(X)`; 26's `ℬ⁺`); source 28's bounded ideal `ℬ_μ` is `𝒥_b` and its loci
`B^±_μ` are `H^±_μ`; `cf μ` is `q` (28's `δ`). Countable strata: the dense
alphabet is `D`, `P_{ω+n}` (30's `P_n`), 30's nonisolated set `S_n` and
relation tables `Tab_n`, 29's completion `Î`. Termination markers at a cut
are `ε` (23's `𝖾`, 27's and 29's `†` at a cut), with `𝒯_ε`, `𝓘_ε`, `𝒯^inc_ε`;
`†` stays the centered terminator; the shorter-first type of all words is
`𝐓_min` (27's `ℬ`, 29's `𝐓`) and the centered increasing classes are
`𝒯^inc_c`, `𝒯^inc_{†±}`, `𝒯^inc_pad` (27's `J`, `J_±`, `Q_0`; 29's `𝒞`, `𝒞_±`,
`𝒞_pad`). Relation-table scans are `𝗌: ϑ → X×X` (27's `q`, `θ`); 30's
inversion class is `Inv(W)`; the external order of an internally finite
nonstandard interval is `I_∞` (19's `K`, 21's `H`); `ℱ = {n!}`; class
well-order polynomials `P(Γ)` (23's `𝖯(Γ)`, 29's `𝒫(Γ)`); `CTH`, `CWO` as in
source 29. Source 20's local ranks and minimum-type cutoffs are `lr_α(x)`,
`Min_R`, and its restriction maps `π_{βα}` (19's `r_Y` is `π_Y`). Every
renaming is listed in the table of Section 1.3.2 with its false reading.

For source 31 (dated addendum, Section 1.3.3): `𝖹` is Zermelo set theory
(Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, Separation; no
Replacement, Foundation or Choice), `𝖹𝖢` adds Choice and `𝖹𝖢_F` Foundation;
`GC_{≤ω}` is a selector on nonempty countable sets with Separation `Sep(c)` for
formulas mentioning it, never this report's global choice `GC`;
`𝓜_λ = (V_λ, 𝒫(V_λ))` is the full-class rank model at a limit `λ > ω`, with
`κ = |λ|` (the cutoff only when `λ` is a cardinal); the sign carrier
`S_λ = ⋃_{α<λ} 2^α` is kept, being `No_{<λ}` as a set of sign sequences
without its field structure (false reading: not source 28's `S_μ = Sym(μ)` or
Part X's `S_n`); `CR(a)`, `CR(Ord)`, `CR`, `OA` are Class Replacement on a
domain, on ordinals, in full, and ordinal abstraction. Renamed: source 31's
injections `X ↪ D` are printed `X ↣ D`, since `↪` is an order embedding in this
report, and its threads `𝒯_X` are `Thr_X`, since `𝒯` is the class of all
words. The trace `H_a` is not a fibre, history slice or group, and the theory
`𝖳` is not the type `𝐓_min`.

For sources 32–35 (dated addendum, Section 1.3.4): `Ω` is the presentation
`(Ord, <)`, never a set ordinal or a surreal (32's and 35's `\Om`, 33's `\On`);
the finite-support power is `A^{[B]}` (34's `\Pow{A}{B}`, printed with `\fsp`
because `\Pow` is this report's power set; 32's and 33's `A^B` wherever the
operands are class orders) and the polynomial order `P(Γ) = Ω^{[Γ]}` (34's
`\PWO`, 35's `𝖯(Γ)`, 32's and 33's `P_Γ`); the hereditary term order is `𝖤`
(sans-serif; 34's and 35's `ℰ`, renamed because `ℰ_κ` and `𝓔` mean other
things here), its version over a base `𝖤(A)` (34's `H(A)`, 32's `ℋ(A)`), its
height cuts `𝖤^{≤n}` (34's `E_n`); 33's direct limit `E` is `𝕋`; 32's domain
`D_W` is `dom W` (since `D_W` is the condensation operator); an embedding
exists `↪`, none exists `↪̸`, initial and proper initial ones `≼_init`,
`≺_init` (the sources' `≼_emb`, `≼_e`, `≼_i`). Kept with false readings: the ceilings `Θ_L` (34),
`δ_A` (32), `δ_G` (33), `δ_0`, `δ_ord`, `δ_set` (35), one invariant over
`V_κ`; truth predicates `T`, `T_A`; the global order `G` (not source 23's
exponent class); 32's and 33's diagonals `D`, `D_n` (not `D_W`); 35's `T` for a
class of terms and for the reflection tree; source 33's digit map `Φ` and
source 35's completion isomorphism `Φ`.

For source 36 (dated addendum, Section 1.3.5): its bold `Ω` is `Ω`; its
finite-support powers `A^B` of class orders are printed `A^{[B]}` (in term and
point displays `Ω^t α` the superscript is a term or an exponent point, and set
ordinal powers keep `^`); its term class, sans-serif `𝖳_Ω`, is `𝖤`, and its
height stages `T_n` (height at most `n+1`) are `𝖤^{≤n+1}`; its sans-serif `𝖤`
for the epsilon-term functor is printed `𝖤𝗉`, since `𝖤` is the hereditary order
here; its horizons `H(M)`, `H_0(M)`, `H_p(M)`, `H_G`, `H_{G,T}` are `𝔥(M)`, …,
`𝔥_{G,T}` (Fraktur H), since `H`, `H_i` are histories; its truth predicate keeps
`T`, as source 33's does. Kept with false readings: the tower codes `w_n`
(source 34's terms `τ_{n+1}`), `⊞`, `⊠` (not natural sums), `𝓗_κ` (a set of
horizons, not source 32's `ℋ(A)`), `H_{κ⁺}` (hereditarily small sets), the
diagonals `D_n`, heights `h_n` (not source 20's `h_κ`), the order `E_G` (not a
stage equivalence), the zeta order `W`, the ordinals `τ_n` in one proof (not
source 34's terms) and `Ω_u` (an ordinal of the next universe level, not the
presentation `Ω`). Over `V_κ`, `𝔥_G` is source 34's `Θ_L` for `L = {∈, G}`,
source 33's `δ_G` and source 32's `δ_A` for trivial `A`.

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
11. **Set-sized strata, topology and permutation groups (Part X, sources 24,
    19, 22, 26, 28, 21, 29, 30).** For every fixed type `α` of `No_{<κ}` with
    finite tail `n`, `𝔹_{ϱ_lo} ×_lex n! ↪ 𝒲_α ↪ 𝔹_{ϱ_up} ×_lex n!` and the exact
    embedded cube spectrum (Theorems 64.7, 64.11, source 19); every type at the
    cutoff `ω₁` in ZFC (Corollary 64.20, source 30); weight and point characters
    of every fixed-length stratum (Theorems 63.4, 63.9, source 22); the forward
    prefix completion (Theorem 65.1), a homeomorphism `λ^μ ≅ 𝒲_μ(X)` with
    `λ = μ^{<μ}` at regular `μ` (Theorem 66.2), and at the countable cutoff Baire
    space with Dedekind completion `ℝ` (Theorem 67.2, source 24; homogeneity,
    Theorem 67.8, source 21; seven proofs, Note 67.1); the strata `ω + n`
    (Section 68, sources 29 and 30); at uncountable `μ` of countable cofinality
    the minimal slice is not Borel in its injection completion (Theorem 69.17)
    and it is completely metrizable exactly when `μ = ω` (Theorem 69.18,
    source 26); the bounded subgroup is maximal and self-normalizing, and the
    coarsest group topology above the bounded-prefix topology is `τ_{<μ}`
    (Theorems 70.4, 70.6, 70.18, source 28); the global prefix completion
    (Theorem 71.5, source 24).
12. **Across birthday cutoffs (Part XI, sources 19, 20, 21, 29).** Exactly when
    restriction preserves the native order (Theorem 73.1); coherent gluing of
    cutoff profiles to class well-orders, set-likeness detected on a club, and
    the append-tail direct system (Theorems 74.1, 74.7, 74.8, source 20);
    fixed-slot coherence within a cardinality band (Theorem 75.1, source 21);
    `𝔹_β ↪ No_{<θ}` iff `β < θ` for all ordinals (Theorem 76.5, source 29);
    noncardinal cutoffs (Theorem 77.4, source 21; Section 78, source 29).
13. **Words, markers and codes (Part XII, sources 23, 27, 29, 30).** No fixed
    marker makes increasing words set-cut saturated (Theorem 82.1, source 23);
    increasing words split at the terminator and the centered increasing order
    is `𝐓_min^op ×_lex 𝐓_min` (Theorem 82.4, Corollary 82.5, source 27; source
    29's route, Note 82.11); two scans of one countable carrier give orders with
    the same spectrum and different topology (Theorems 84.2, 84.3, source 27);
    the core is dense in relation-table orders of set-like scans (Theorems 84.5,
    84.11, sources 27 and 30).
14. **The core and its cylinders (Part XIII, sources 25, 22, 20, 21, 19, 27,
    29, 30).** Branch configurations are classified up to core-and-cylinder
    automorphisms (Theorem 90.1), exhaustiveness is invisible to the core with
    all its unlabelled cylinders and set-many parameters (Theorems 91.1, 91.2),
    and one cross-node label relation makes the structure rigid (Theorems
    93.1, 93.3, source 25); the decorated completion and automorphism
    extension of the raw order in an external set-sized model (Theorems 98.2,
    98.5, source 19); the exact least ordinal support `max(δ_S, δ_T)`
    (Theorems 101.1, 101.2, source 27); the admitted labelled enumerations
    recover an available class realization (Theorem 102.3, source 22; sources
    27 and 30 in notes).
15. **Unrestricted class well-orders II (Part XIV, sources 20, 19, 21, 23, 27,
    29, 30).** A local coding dichotomy for intervals of the unrestricted order
    (Theorem 107.4, source 20); termination and normal forms of condensation
    histories (Theorems 108.1, 108.16), and over GBC canonical terminating
    histories exist iff class well-orders are strongly comparable,
    `CTH ⇔ CWO` (Theorem 108.19, source 29); the external order of an externally
    countable GBC model is `σ(ℱ)` or `σ(ℱ ∪ {I_∞})` as the model is ω-standard
    or not (Theorem 109.1, source 19; sources 20 and 21 in notes), and every
    set-sized GBC model's external order has the complete theory of `σ(ℱ)`
    (Theorem 109.9, source 19; **the strongest unreviewed claim of batch 83**),
    which is decidable (Corollary 109.22, source 20).
16. **Countable global choice and surreal coding over Zermelo set theory
    (Part XV, source 31).** Over Zermelo set theory, with fixed well-orders
    on `D` and its code set `C_D` and Separation in the relevant expanded
    language, a selector on `D`-small sets and a uniform assignment of
    injections into `D` are interconvertible by uniform definitions, without
    Replacement or ordinal collapse (Theorem XV.3.3). Ordinary Choice supplies
    the code well-order in `ZC`. Bounded trace compression needs no Collection
    (Theorem XV.4.1);
    `ZC + GC_{≤ω} + Sep(c)`, and the same with Foundation, is not conservative
    over `ZC` (`ZC_F`), even with selection only from countably infinite sets
    (Theorem XV.5.1, Corollaries XV.5.3–XV.5.4), **conditional on source 31's
    interface to Glazer's published countermodels (arXiv:2312.11902,
    Propositions 3.8 and 4.11), whose exact match with them is unreviewed**;
    without expanded Separation the selector is conservative (Proposition
    XV.5.5). In the full-class rank models `(V_λ, 𝒫(V_λ))` at every limit
    `λ > ω`, global choice and birthday-monotone set-like well-orders of the
    sign carrier exist (Propositions XV.6.1–XV.6.2); a class bijection
    `Ord ↔ S_λ` exists iff `λ = κ` is a cardinal with `2^{<κ} = κ` (Theorem
    XV.7.2), a birthday-monotone one iff `λ` is a strong-limit cardinal
    (Theorem XV.7.4), universal set coding and ordinal abstraction iff
    `λ = κ = ℶ_κ` (Theorems XV.8.2, XV.8.4); Class Replacement on a set `a`
    holds iff `|a| < cf λ`, on all ordinals iff `λ` is an uncountable regular
    cardinal, and in full iff `λ` is strongly inaccessible (Lemma XV.9.2,
    Theorem XV.9.3, Corollary XV.9.4); the external cardinalities of internal
    proper classes are exactly the cardinals from `cf λ` to `|V_λ|` (Theorem
    XV.10.1); separating heights `ω+ω`, `ω₁` under CH, `ℶ_ω`, the first beth
    fixed point above `ω` and an inaccessible (Section XV.11). This extends
    source 12's inaccessible model (Theorem 21.1) to every limit height and
    answers source 28's Research question 113.209 (`swo:ge:n10`) in part.
17. **Definable class well-orders beyond `Ord` (Part XVI, sources 34, 35, 32,
    33).** Over GB with ZF sets and no form of choice: a class linear order is
    a class well-order iff every nonempty set subset has a least element
    (Lemma XVI.2.2, source 34); finite-support powers `A^{[B]}` of class
    well-orders are class well-orders (Theorem XVI.4.2, source 34; source 35's
    route, Note XVI.4.4); and strong comparability `CWO`, canonical histories
    `CTH`, terminating histories on some schedule and initial embeddings
    `W ≼_init P(W)` are equivalent (Theorem XVI.5.8, source 34; Note XVI.5.19,
    source 35), which source 29 proved over GBC (Theorem 108.19). The
    hereditary term order `𝖤` is a class well-order in GB with `Ord^{[𝖤]} ≅ 𝖤`,
    the least initial pre-fixed point (Theorems XVI.6.3, XVI.6.6, XVI.6.7),
    height cuts of cofinality ω (Theorem XVI.6.5), external type
    `ε_{κ+1}` in the full model over inaccessible `κ` (Theorem XVI.6.9), and
    general bases (Corollary XVI.6.10). Source 35's fixed-point completion: a
    class well-order `W` initially embeds in a polynomial fixed point iff it
    initially embeds in `P(W)` iff (for nonempty `W`) it has its history on
    `W+1`, and `FPE ⇔ CWO ⇔ CTH` (Theorems XVI.6.17, XVI.6.18, Corollaries
    XVI.6.19, XVI.6.20; stated over GBC, proved over GB by this write's
    Theorem XVI.6.21). No uniformly coded family of class well-orders is
    cofinal under embedding (Theorem XVI.7.2, all four sources); a full
    satisfaction class gives an order dominating every definable one (Theorem
    XVI.7.4); for each standard `n` one order escapes all `Σ_n` presentations
    (Corollary XVI.7.6; source 33's Theorem XVI.7.20 with a named global order;
    source 35's Theorem XVI.7.11 on `Ord` in the pure language, with no uniform
    ordinal-parameter evaluator, Corollary XVI.7.12). Over a transitive
    β-model, the set-parameter-definable order types form `[0, Θ_L)` with
    `Θ_L < |M|^+`, and with a named global well-order parameter-free definitions
    are cofinal and `cf Θ_L = ω` (Proposition XVI.8.2, Theorem XVI.8.3); at
    `V_κ`, `κ < Θ_L < κ^+` (Corollary XVI.8.4), `κ^{δ_A} = δ_A` (Theorem XVI.8.9,
    source 32), the ceilings exhaust `κ^+` as the predicate varies (Corollary
    XVI.8.11), the ceiling is an epsilon number closed under ordinal arithmetic
    (Corollary XVI.8.17, source 33), a truth predicate represents the old
    ceiling exactly (Theorem XVI.8.12, source 32) and raises it (Theorem
    XVI.8.19, source 33); in the pure language `κ < δ_0 ≤ δ_ord ≤ δ_set < κ^+`
    with `cf δ_0 = ω` (Theorem XVI.8.6, source 35). Source 33's digit map from a
    supplied tower (Theorem XVI.5.27) has initial image (this write's Remark
    XVI.5.29), and source 33's conditional converse (Proposition XVI.5.30). This
    answers over GB the question of `swo:xiv:note:strength` and source 20's
    Research question 113.111 (`swo:lm:n11.5`), and source 31's Research
    question 113.239 (`swo:gcz:n7`) in part.
18. **Finite-support arithmetic and definability horizons (Part XVII, source
    36).** Over GB with ZF sets and no choice: normal-form addition and
    multiplication on the hereditary order `𝖤` represent sums and products
    of its initial segments (Theorems XVII.5.1, XVII.5.2). The addition rule
    also applies to points of every `Ω^{[B]}`, and
    `D + Ω^{[B]} ≅ Ω^{[B]}` for every point-cut D. Finite-support powers
    have the exact predecessor decomposition of Theorem XVII.3.5. If A
    has at least two elements and B is nonempty, `A^{[B]}` is set-like iff
    A is a set and B is set-like, or B is a singleton and A is set-like
    (Theorem XVII.3.6). For every set ordinal a≥2,
    `a^{[Ω·B]} ≅ Ω^{[B]}` (Corollary XVII.3.7); every proper class well-order
    has a presentation on
    the carrier `Ord` (Proposition XVII.2.4); a finite-support term operator
    with the restriction property that preserves set well-orders preserves
    class well-orders (Theorem XVII.6.2); the epsilon-term functor `𝖤𝗉` sends
    class well-orders to class well-orders, with set-case type `ε_β` (Theorem
    XVII.6.4). Over every transitive `M ⊨ ZFC` of height `κ`: `ε_κ = ζ_κ = κ`,
    `otp 𝖤^M = ε_{κ+1}`, `otp 𝖤𝗉(𝖤)^M = ε_{ε_{κ+1}}`, a parameter-free order of
    type `ζ_{κ+1}` (Lemma XVII.6.5, Theorems XVII.6.6, XVII.6.7); the definable
    order types form `[0, 𝔥(M))`, those of internally proper carriers
    `[κ, 𝔥(M))`, with `𝔥(M) < |κ|⁺` and a parameter-preserving transfer to
    `Ord^M` (Theorem XVII.6.9, Proposition XVII.6.10); `ε_{𝔥(M)} = 𝔥(M)` and
    `ζ_{κ+1} < 𝔥_0(M) ≤ 𝔥_p(M) ≤ 𝔥(M)`, both parameter-restricted horizons of
    cofinality ω (Proposition XVII.6.11); `𝔥(M)` is bounded by every admissible
    height above `M` (equation (S36.6.2), after Blass). At `V_κ`, `κ`
    inaccessible, with a named enumeration `G`: the ceiling theorem of Part
    XVI again, with `ε_{𝔥_G} = 𝔥_G` (Theorem XVII.7.5), the bounded-complexity
    diagonal (Proposition XVII.7.6), an effective strict complexity hierarchy
    (Corollary XVII.7.7), truth promotion (Theorem XVII.7.9, source 32's
    Theorem XVI.8.12 again), and `sup_G 𝔥_G = κ⁺` with every
    `α ∈ [κ, κ⁺)` the type of a parameter-free `G`-definable order for some `G`,
    by coding any subset of `κ` into `G` (Lemma XVII.7.10, Theorem XVII.7.11);
    the full model unrolls to `H_{κ⁺}` (Proposition XVII.8.1). This answers
    source 33's research question 12.4 (`swo:dh:n12.4`) and the addition and
    multiplication part of source 34's R3, and advances `swo:dc:n12.4`,
    `swo:dh:n12.3`, R4 and R9 (Sections XVII.11, 113.31). Note XVII.4.B states
    the leastness of `𝖤` against initial pre-fixed points that the proof of
    Theorem XVII.4.5 gives; it is source 34's Theorem XVI.6.7.

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
  module names in the ten formalization plans of sources 08–18 (Sections 20.7, 24, 25, 26 and
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
- Batch 83 (Section 1.4, addendum for sources 19–30; every source's limitation
  is printed in its sections): no batch-83 source claims historical priority,
  peer review or machine verification; none built the repository or compiled a
  new Lean file; every Lean module name in their plans (Section 111) is a
  proposal; their finite checks verify finite mechanisms only; their 139
  research questions are proposals, not a census of open problems. Re-proofs
  of Parts I–IX and of each other are notes or credited routes (the
  countable-cutoff theorem by seven of them, the represented-cut theorem by
  three more). Specific limits kept: source 19's coding length is exact only
  when its two weighted bounds agree (open at singular non-strong-limit
  residual cardinals at most `κ`); source 22's density and cellularity column
  re-proves source 16 (only weights and characters are new); source 23's
  termination criterion is a second route to source 16's theorem; source 24's
  homeomorphisms are not order isomorphisms; source 26 treats minimal lengths
  and ordinary Borel sets only; source 28's character bound concerns the
  coarsest group refinement; source 29 does not establish `CWO ⇒ ETR`; source
  30's classification under GCH is conditional; source 27's least support bound
  optimizes ordinal height only, not birthdays; the countable-model theorems
  describe external order types, not internal enumerations, and uncountable
  class models are not classified. Sources 19, 20, 21 and 29 report internal
  mathematical review and source 30 "independent AI-assisted proof review";
  no such review is recorded in the repository.
- Batch 89 (Section 1.4, addendum for source 31): conventional proofs, no Lean
  or Rocq verification, no machine-checked formalization; its formalization
  architecture is a proposal. Its nonconservativity theorem uses Glazer's
  countermodel theorem (Propositions 3.8 and 4.11) as an explicitly cited
  input, stated as an abstract interface that has **not** been checked against
  Glazer's paper here; source 31 itself says that expert review of the
  localized statement "would be the next scholarly step", and Part XV prints
  the theorem as claimed, conditional on that interface (Section XV.5.1). The
  rank-model classification is proved in an external ZFC metatheory for full
  classes; the equivalence of universal set coding with ordinal abstraction
  holds within this family of models, not over every weak class theory; no
  field operations on `S_λ` are asserted at arbitrary cutoffs; nothing is
  asserted about first-order Replacement at singular heights. It does not
  claim that the three schemes of `swo:ge:n10` are equivalent to rows of its
  table, a solution of the surreal transfer problem, a classification for
  definable-class realizations or the finite-input conservativity boundary.
  Its searches were targeted and are "not a proof of priority"; restricted
  global choice (Enayat), ordinal abstraction and `V_{ω₁}` (Hamkins, Rin),
  set-like orders without Replacement (Carneiro), well-ordered Replacement
  (Freire and Hamkins), the global-choice equivalences (Hamkins) and beth fixed
  points (MathOverflow) are credited.

- Batch 96 (Section 1.4, addendum for sources 32–35): no priority, peer review
  or machine-checked formalization; neither source 34 nor source 35 proves
  `CWO` or `CTH` in GB, and `CWO ⇒ ETR` (Hamkins and Woodin's Question 7) is
  open; source 34's set-subset criterion is for linear orders and does not
  identify the absence of descending sequences with well-foundedness without
  choice; the surreal-carrier reduction keeps global choice; source 32's
  termination theorem is conditional on the hierarchy (and repeats source 20,
  Remark XVI.1.1), `ETR` "sufficient, not proved necessary"; the spectra are
  external and need an inaccessible `κ` or a transitive β-model, and do not
  transfer to countable, non-β or nonstandard models; countable cofinality of
  a ceiling does not make it countable; source 35 does not claim its three
  suprema distinct or a separation of consecutive levels; the truth jumps
  assume a full satisfaction class, and source 34's `J_γ` are "not canonical
  absolute class ordinals"; hereditary ordinal notation (Weiermann, Freund)
  and class epsilon notation (Rathjen, through Jeon) are credited; the finite
  checks are "NOT machine proofs"; the Lean module plans are proposals; the
  repository and literature searches were targeted. This write's Theorem
  XVI.6.21 and Remarks XVI.5.24, XVI.5.29, XVI.5.31 are the write's, unreviewed.
  (Dated note, 4 October 2026: an independent check has since found all four
  valid after editorial corrections, which are made; see "Reviews".)

- Batch 97 (Section 1.4, addendum for source 36): "publication priority and a
  breakthrough resolution of a recognized open problem are not asserted";
  long class orders, their arithmetic and the epsilon notation functor "have
  established antecedents" (Barton–Williams; Marcone–Montalbán); its `V_κ`
  horizon theorem, bounded-complexity diagonal and truth promotion are
  theorems of sources 32–34 (credit notes in Part XVII); the converse from
  comparability to `ETR` is not established; the arithmetic is relative to
  ordinal coefficients, and no normalization of general powers inside `𝖤` is
  proved; the transfer theorem does not apply to an arbitrary normal ordinal
  function; the spectra count externally well-founded orders, an arbitrary
  transitive model need not recognize external ill-foundedness, the `V_κ`
  theorems use inaccessibility and a named `G`, "parameter-free" excludes only
  set parameters, and `cf 𝔥(M) = ω` is not claimed for unrestricted
  parameters over an arbitrary `M`; the diagonal formulas are an external
  schema, not one evaluator; the size of the truth jump is not computed; the
  admissible bound's equality cases (Taranovsky) are not claimed as new; the
  proofs are conventional, with no referee and no Lean or Rocq; the five
  proposed modules are design targets; the demonstrator checks natural
  coefficients only and "does not prove any class-theoretic theorem"; its
  repository audit was targeted and did not read this report's article.

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
none states a result of this report. No batch-81 or batch-83 statement is
formalized; the batch-83 sources ship no Lean code, and the declarations their
plans name as existing were checked against
`Algebra/SurrealNumbers/Surreal/Foundations/` (Section 1.5). Source 31 ships
no Lean or Rocq code and cites no Lean declaration; none of its statements is
formalized, and the milestones its formalization architecture proposes (the
domain-size criterion, a verified bounded uniformization theorem) do not
exist. Sources 32–35 ship no Lean or Rocq code; no statement of Part XVI is
formalized. Source 32 cites `SetTheory/ZF/Lean/ZF/Zf.lean` (whose
`Sep_form`, `Repl_form`, `ZFax`, `ZFprov` exist as it says) and Mathlib's
`Ordinal.univ` and `Ordinal.type_lt_ordinal`, and reports that
`Ordinal.univ_id` is deprecated since 2026-03-20. These API/deprecation claims
remain attributed to source 32; this review does not recheck their external
history. Both repository manifests pin Mathlib **v4.32.0**, revision
`81a5d257c8e410db227a6665ed08f64fea08e997`;
source 33's proposed directory `SetTheory/ClassWellOrders/` does not exist.
Source 36 ships no Lean or Rocq code; no statement of Part XVII is formalized.
Its five proposed modules (`ClassOrderPresentation`, `FiniteSupportPower`,
`OmegaNormalForm`, `EpsilonTerms`, `DefinabilityHorizon`) do not exist; it
cites `Logic/PeanoArithmetic/ListCoding/README.md` (natural-number hereditary
codes below `ε_0`, with Lean denotation theorems and separately scoped Rocq
results) and Mathlib's `Mathlib/SetTheory/Ordinal/CantorNormalForm.lean`
(present in the pinned Mathlib) as engineering patterns, not as theorems
about class orders.
Placement in the surreal collection beside the Lean foundations confers
no formal status.

## Where one source answers another (Sections 1.7, 33, 39, 50, 60, 72, 79, 85, 105, 112, 113.25, XV.15, 113.27, XVI.12, 113.29, XVII.11, 113.31)

- Source 12's question on the weak-choice strength (its Remark 4.2 and
  Question 14.5): **answered** by source 11's Theorem 13.1; printed as
  Remark 113.15, with Remark 13.4.
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
  status cells of the question index, Section 113): source 11's questions on
  represented cuts and on the minimal slice's cut spectrum (`swo:n16.1`,
  `swo:n16.7`), source 09's directions 3 and 8 and source 08's questions 2 and
  7 are **answered**; source 11's `swo:n16.2`–`swo:n16.5` and `swo:n16.8`,
  source 12's `swo:st:n14.1`, `14.3`, `14.4`, `14.7`, `14.8`, source 09's
  directions 4–7 and source 08's questions 4, 6, 8, 9, 12, 13, 14 are answered
  in part. Among the batch-81 sources' own 74 questions (index in Section
  113.5), source 13's on termination cuts is answered by source 16, source 14's
  and source 16's on the minimal slice's local geometry by source 17, and
  source 16's on centered increasing words by source 18 (at the zero
  threshold).
- Batch 83 (dated notes of 3 October 2026 in Section 113.25, items (a)–(q),
  each Part's "What this Part answers", Sections 72, 79, 85, 105 and 112, dated
  pointers at the end of Sections 33, 39, 50 and 60, and dated cells in both
  question indexes): source 12's `swo:st:n14.1`, `14.2`, `14.3`, `14.7`, `14.8`
  and `14.9` and source 11's `swo:n16.3`, `16.4`, `16.5` and `16.8` are answered
  further, most in part; Part VIII's open items on extra predicates
  (equality of labels across extension edges suffices, unlabelled cylinders do
  not) and on ordinal support bounds (the ordinal half is **answered**);
  source 09's fifth direction (a dense set-coded core exists for every
  set-like scan) and source 08's question 9 (scan dependence, negatively at set
  level); source 18's ω-nonstandard question `swo:sh:n19.8` (**answered**, three
  times); source 17's `swo:gs:n15.4` (complete metrizability, **answered**) and
  `swo:gs:n15.7` (recovering a class realization, **answered**); source 15's
  `swo:cb:n13.5` and `swo:cb:n13.6` and source 14's `swo:tc:n14.7` (**answered**
  in an external formulation by source 19). Within batch 83: source 24's
  question 13.1 and source 28's question 1 are answered negatively by source
  26; source 24's subgroup question by source 28; source 20's question 11.2 by
  source 19 and 11.5 by source 29; source 22's label question by source 25;
  source 23's question 16.1 had been answered by source 16. The 139 questions
  of sources 19–30 are indexed in Section 113.12.
- Batch 89 (dated notes of 3 October 2026 in Section XV.15 and Section 113.27,
  after `swo:ge:n10`, in source 28's status note and in the batch-83 question
  index): source 28's `swo:ge:n10` (Research question 113.209) is **answered
  in part** by source 31, for the mechanisms (selection, collapse and coding,
  image bounding) rather than for the three named schemes, whose weakest
  assumptions stay open (source 31's Research question 113.242); the sibling
  questions `swo:pc:n13.9` and `swo:nb:n14.10` stay open. Source 31's Research
  question 113.241 (external types of set-like well-orders of `S_λ`) is
  answered at inaccessible heights by source 12's Theorem 21.1(ii). Dated
  notes after Theorem 13.1 (`swo:cf:choice`) and in Section 21
  (`swo:st:thm:model`) record that its equivalence uses GB's class
  Replacement and that the inaccessible model extends to every limit height.
- Batch 96 (dated notes of 4 October 2026 in Sections XVI.12 and 113.29, after
  `swo:xiv:note:strength`, in item (b) of Section 112, after Research question
  113.111, after `swo:gcz:n7` and `swo:bw:n13.8`, in the status notes of
  Sections 113.13 and 113.25 and in the three question indexes): the strength
  of complete condensation histories over GB without global choice
  (`swo:xiv:note:strength`; source 20's `swo:lm:n11.5`, Research question
  113.111) is **answered** by sources 34 and 35; source 11's `swo:n16.3` and its
  relatives are answered over GB in the canonical-history form, while source
  15's uniform finite condensation (`swo:cb:n13.3`) stays open; source 31's
  `swo:gcz:n7` is answered in part (order types at inaccessible heights);
  source 29's `swo:bw:n13.8` (Hamkins–Woodin's Question 7) is not settled.
  Within batch 96: source 33's Remark 5.5 and research question 12.7 (initial
  image of its digit map) are answered by Part XIV's normal-form theorem
  (Remark XVI.5.29); source 32's question 12.1 and source 33's 12.6 (strength
  of tower existence) are answered by source 29 over GBC and sources 34 and 35
  over GB; source 35's question 10.6 (a choice-free completion theorem) is
  answered positively by this write (Theorem XVI.6.21); source 32's claim to
  answer this report's termination question repeats source 20 (Remark XVI.1.1).
  All stay on record with these statuses (Section 113.28).
- Batch 97 (dated notes of 4 October 2026 in Sections XVII.11 and 113.31,
  after six questions of Section 113.28, and in Section 1.7): source 33's
  research question 12.4 (`swo:dh:n12.4`, how far `δ_G` varies with `G`) is
  **answered** by source 36 (unbounded in `κ⁺`; any subset of `κ` can be coded
  into `G`); source 34's R3 is **answered for addition and multiplication**
  (exponentiation open, source 36's question 6); source 32's question 12.4,
  source 33's 12.3 (new necessary conditions `ε_δ = δ`, `δ > ζ_{κ+1}`) and
  source 34's R4 and R9 are advanced; source 31's `swo:gcz:n7` is advanced for
  external order types at every transitive height. Source 36's own question 2
  is answered in part by source 34's Theorem XVI.8.3 (β-models with a
  parameter-free definable global well-order). Its other questions coincide
  with questions of Section 113.28, as the notes in Section 113.30 say.

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
Batch 83 answers its "Other ground orders" question further: source 19's cube
spectrum and coding sandwich for every fixed type of `No_{<κ}` (Theorems 64.7,
64.11), source 29's classification on the countable birthday band and its
native birthday spectrum (Corollary 78.10, Theorem 76.5), and source 30's
weight formula for the finite-tail strata of every alphabet (Corollary 63.12); the
display remains open at singular non-strong-limit residual cardinals. A
reciprocal note in that report belongs to a commit of its own.

**[foundations](../foundations/)** supplies the conventions used throughout
(`found:sub:gbconvention`, `found:prop:recursion`, `found:sub:km`,
`found:rem:secondsort`, `found:prop:proper`, `found:prop:allcuts`). A dated
"Related (batch 89)" note there, after `found:rem:conservativity`, records
source 31's nonconservativity theorem and rank-model Replacement thresholds.

**[birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)**:
the saturation of `No_{<κ}` at regular `κ` (`hset:rem:saturation`, through
`hset:eq:cut-bound`) is classical and is source 11's Lemma 7.2 and source 08's
Note 7.4; its ordinal-graph coding (`hset:thm:choice`) is the set-level form of
the mechanism in Theorem 13.1 (Remark 13.4) and is unchanged. Its remark on
the gap pairs of `No_{<κ}` (`hset:rem:cutoffgaps`) is re-proved, and extended
to singular `κ` and `κ = ω`, by source 17's Theorem 29.4. Its batch-89 Part VI
(manuscript 03 of batch 89, written separately) shows that `V_{ω+ω}` fails
Replacement for definable families; that is the definable special case, at a
height of cofinality `ω`, of source 31's domain-size criterion for full-class
Replacement (Lemma XV.9.2). Neither is claimed as the other's. The witness is
its Proposition 30.1 (`hset:zr:prop:rankmodel`), and its Remark 24.7
(`hset:zr:rem:swo`) records the inclusion; the provenance paragraph of Part XV
cites both (added 4 October 2026). Its batch-89 Part VII calibrates set-level
surreal universality over ZF by the first Kinna–Wagner principle
(`hset:kw:thm:coding`, `hset:kw:thm:equivalences`); a dated note after Remark
13.4 records that Hamkins's question whether universality implies global
choice is not affected.

**[naming-elementary-embeddings](../../../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/)**
(research-report collection, batch-89 manuscript 05) studies Replacement,
Collection and reflection schemes in urelement models expanded by named
elementary embeddings; with source 31's Proposition XV.5.5 (a selector is
conservative unless Separation mentions it) it shares the theme of schemes in
an expanded language, with different theorems and models.

**[polish-models-of-omnific-arithmetic](../polish-models-of-omnific-arithmetic/)**
(batch 90): Glazer's class-manifold question (does `ZFC − Fnd + GC` prove that
every topological manifold is a set? from his Oberwolfach abstract *A
hypertalk*, Oberwolfach Reports 22 (2025), Report No. 2/2025, pp. 106–107,
which reports that Global Choice proves, over `ZFC` without Foundation, a
classification of one-dimensional manifolds that `ZFC − Fnd` does not) is
printed, with partial results proved without Global Choice, in its Part XII
(`pma:gcm:q:glazer`); the question stays open. A dated `[merge]` note after
Remark XV.5.2 (`swo:gcz:n5.2`, following Theorem XV.5.1) records this; no
theorem is shared with source 31.

**[real-vector-space-structure](../../surreal/real-vector-space-structure/)**
uses a set-like global well-order; by Theorem 13.1 that hypothesis is
equivalent to global choice over GB. Its question on the weaker class-choice
principles (`rvs:w:q:foundations`) is unaffected; source 31 shows that the
equivalence uses GB's class Replacement (in the rank models `(V_λ, 𝒫(V_λ))`
set-like well-orders of the sign carrier exist at every limit height, an
`Ord`-enumeration only when `2^{<κ} = κ` at a cardinal height); a second
dated note there (batch 89) records this.

**[surreal-fields-across-universes](../surreal-fields-across-universes/)**
studies the saturation of `No_{<κ}` across universes; nothing here depends on
it. Its `univ:gs:lem:boundary` (with `M = N`) is the regular uncountable case
of Theorem 29.4, which Part VI records with a pointer.

**[foundations](../foundations/)**, again: its `found:sub:etr` (ETR and two
invalid moves) bears on Part XVI, whose sources keep set-valued and
finite-trace recursion apart from class-valued `ETR` and show the canonical
histories equivalent to `CWO` over GB. A reciprocal note there belongs to a
commit of its own (drafted by this write, not applied).

Part XVI has no counterpart in the research-report collection's
`ordinals-and-order-types` reports, which concern set ordinals; the
`omnific-notations` and definable-surreal reports concern notations for
individual surreal numbers, not presentations of class well-orders (source 34,
its Section 1.1).

**ListCoding** (`Logic/PeanoArithmetic/ListCoding/README.md`) is cited by
source 36 as an engineering pattern for its proposed modules: hereditary
Cantor-normal-form codes below `ε_0` for natural numbers, with Lean and Rocq
results of its own scope. Nothing of Part XVII is proved there, and Part XVII
confers nothing on it.

The Lean development in `Algebra/SurrealNumbers/Surreal/Foundations/` is
cited, not extended: see "Formal status".

## Build

TeX Live or MiKTeX with lmodern, amsmath/amssymb/amsthm, mathtools, mathrsfs,
geometry, microtype, booktabs, longtable, array, tabularx, enumitem, xcolor,
fancyhdr, listings, tcolorbox, aliascnt, etoolbox, hyperref, xurl and
cleveref. No external figures or bibliography file.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The current H1–H5 and empty-domain corrections were rebuilt directly with
TeX Live pdfLaTeX, shell escape disabled, in three passes: **1,051 pages**.
The committed 1,050-page before-image was separately rebuilt under the same
settings. Both final logs have 37 underfull boxes and the expected
shell-escape-disabled warning, with no errors, undefined references or
citations, duplicate labels/destinations or overfull boxes. All 2,293 literal
labels remain in the same order; all 4,586 ordinary/cleveref auxiliary label
entries keep their displayed numbers. PDF pages 25, 31, 780–782, 794, 848,
888 and 889 were rendered and visually checked. This verifies those affected
pages and the build diagnostics, not the whole PDF or all proofs.

The previous merged release was built with MiKTeX (pdfLaTeX): 1,050 pages;
no errors, undefined references
or citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull boxes; 38 underfull-box warnings, the same 38 as the
994-page build before batch 97, the 860-page build before batch 96 and the 831-page build before batch 89 (15 in the build before batch 83, 10 before
Part IX). The batch-89 write added Part XV and source 31's front matter,
questions, delivery record, abstract and crosswalk (831 → 860 pages). The
batch-96 write added Part XVI and the front matter (1.3.4, 1.11), questions
(113.28–113.29), delivery record (A.13), abstracts and crosswalk (D.24–D.27) of
sources 32–35, and dated notes in Sections 108, 112 and 113 (860 → 994 pages).
The later R1–R3 metadata corrections were rebuilt directly with TeX Live
pdfLaTeX, with shell escape disabled, in three passes: 994 pages, no errors,
undefined references, duplicate labels/destinations or overfull boxes. The
final log has 37 underfull-box warnings and the expected shell-escape-disabled
package warning. All 2,188 literal labels remain in their original order.
Corrected text was extracted and PDF pages 824 and 840 visually inspected;
this checks those pages, not the entire PDF.

The batch-97 write added Part XVII and source 36's front matter (1.3.5, 1.12),
questions (113.30–113.31), delivery record (A.14), abstract and crosswalk
(D.28), dated notes in Sections 1.4, 1.7, 1.11, XVI.12 and 113.28, and the
four corrections to Part XVI (994 → 1,049 pages; 1,050 after merging the
concurrent R1–R3 review remarks of `ec4b972db`, rebuilt with the same 38
underfull boxes and nothing else). Its `.aux`, compared with a
build of the committed text, keeps every one of the 2,188 earlier `\newlabel`
entries with an unchanged number: Part XVII numbers its sections
XVII.1–XVII.11 as Parts XV and XVI do (contents' number box 5.0em for Part
XVII only), its credit notes have a counter of their own, and its new
questions 113.295–113.304 follow all earlier ones; every one of source 36's
70 labels carries its source number (XVII.*k.m*, S36.*k.m*). Its tagged
displays are printed as starred displays, as elsewhere in the report.
Its `.aux`, compared with a build of the committed text, keeps every one of
the 1,876 earlier `\newlabel` entries with an unchanged number: Part XVI
numbers its sections XVI.1–XVI.12 as Part XV does, the contents' number box is
4.6em for Part XVI only, and the questions part keeps Sections 113–115 (its
new subsections 113.28–113.29 and the new questions 113.245–113.294 follow all
earlier ones). Two source lines and the crosswalk columns were set ragged-right
or with breakable paths so that the Part adds no underfull box. Its
`.aux`, compared with a build of the previous text, keeps every one of the
1,799 earlier `\newlabel` entries with an unchanged number: Part XV numbers its
sections XV.1–XV.15 (`\thesection` and hyperref's `\theHsection` are switched
for the Part and restored after it, and the section counter is reset to 112),
so the questions part stays Sections 113–115. The contents' number box is
widened to 4.1em for Part XV only, through `\swosecnumwidth`, which the
`\l@section` patch now uses (2.3em elsewhere). Source 31's ledger table was
given ragged-right columns, which removed two underfull boxes of its justified
columns at this page width. The four batch-81 writes added Parts
VI–IX (116 → 151 → 188 → 236 → 349 pages); the fourth added Part IX, the
introductions, questions, conclusions, ledgers, reproducibility records, title
pages and crosswalk of sources 13–18. The batch-83 write added Parts X–XIV and
the front matter, questions, abstracts and crosswalk of sources 19–30 (349 →
831 pages). Its `.aux`, compared with a build of the previous text, keeps
every one of the 1,588 earlier `\newlabel` entries; the only numbers that changed
are those of the three sections of the questions part (61–63 became 113–115),
as in the batch-81 writes. With more than 99 sections, the contents' number box
was widened (`\patchcmd` on `\l@section`, 1.5em → 2.3em), which removed 16
overfull boxes in the table of contents. Tagged displays in the batch-83 Parts
are printed as starred displays with `\tag`, as elsewhere in the report, since
a tagged numbered `equation` repeats a hyperref destination.

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

**Batch 83.** Ten programs (sources 19, 20, 22–28 and 30) use only the Python
standard library and check finite mechanisms only. Run them on copies, never in
this directory: source 19's checker always writes `restriction_checks.json`
beside itself, source 24's defaults to `data/finite_checks.json` beside `code/`,
source 30's to `verification_results.json` beside itself, and sources 22, 23,
25 and 26 to a relative `data/finite_checks.json`. With this directory as `$R`
and an empty scratch directory `$S`:

```
cp "$R"/code/19-residual-check_restrictions.py "$R"/code/2[0-8]-*.py "$R"/code/30-tables-verify_finite.py "$S/"
cd "$S"
python 19-residual-check_restrictions.py               # writes restriction_checks.json here
python 20-limits-finite_diagnostics.py  --output 20.json
python 22-unranked-finite_checks.py     --output 22.json
python 23-termination-finite_checks.py  --output 23.json
python 24-completions-finite_checks.py  --output 24.json
python 25-symmetries-finite_checks.py   --output 25.json
python 26-nonborel-finite_checks.py     --output 26.json
python 27-scans-finite_checks.py        --output 27.json
python 28-envelope-finite_checks.py     --output 28.json
python 30-tables-verify_finite.py       --output 30.json
```

and compare each output with its record in `"$R"/data/` using
`diff --strip-trailing-cr`. Rerun on copies on 3 October 2026 with Python
3.14.4 on Windows, each reproduced its record apart from line endings (CRLF on
Windows). Recorded scope: 19 — 695,228 adjacent comparisons, carriers up to 7;
20 — 58,255 + 609,862 restriction and witness checks, 28,920 dyadic word
comparisons; 22 — 1,388,197 assertions; 23 — 547,480 checks (seed 20261003);
24 — 5,913 permutations, 16,071 cylinders; 25 — 269,329 assertions (seed
20261003); 26 — 5,645,785 assertions; 27 — 48 scans, 28,672 increasing-word
pairs, 103,772 support-bound checks; 28 — 470,323 conjugation and 940,646
group-uniformity identities; 30 — 59,810 partial orientation tables. The build
scripts `code/{19,22,23,24,25,26,28,30}-*-build.sh` compile `.tex` files that
are not shipped (some run their checker with a relative output first); they
build nothing in this layout and are kept as delivered. Source 29 has no
executable checks; its manifest hashes can be rechecked against the archive in
its arrival commit. The records are summarized in Section 111.49.

**Batch 89.** Source 31 ships no program and no data; its Section XV.12.3
explains why "no experimental computation is offered as proof". There is
nothing to rerun. Its manuscript can be rebuilt on a copy, never here, with
`git show 7c0f2d9f9:docs/incoming/global_choice_surreal_coding.zip`, unzipping
into an empty scratch directory and running `latexmk -pdf
-interaction=nonstopmode -halt-on-error global_choice_surreal_coding.tex` in
its inner directory (21 pages, as delivered).

**Batch 96.** Three programs, standard library only, check finite coding
conventions only, as each says. Source 32's and source 33's take `--output`
(32's defaults to `finite_checks.json` in the working directory; 33's prints
only); source 35's always writes `finite_notation_results.json` beside itself,
so run it on a copy. With this directory as `$R` and an empty scratch
directory `$S`:

```
python "$R"/code/32-ceilings-finite_checks.py --output "$S/32.json"   # seed 20261004
python "$R"/code/33-heights-finite_checks.py  --output "$S/33.json"
cp "$R"/code/35-completion-finite_notation_checks.py "$S/"
python "$S"/35-completion-finite_notation_checks.py                  # writes $S/finite_notation_results.json
```

and compare with `data/32-ceilings-finite_checks.json`,
`data/33-heights-verification_results.json` and
`data/35-completion-finite_notation_results.json` using
`diff --strip-trailing-cr`. Rerun on copies on 4 October 2026 with Python
3.14 on Windows, each reproduced its record as JSON and byte for byte up to
line endings (CRLF on Windows): 32 — 689,808 assertions; 33 — 155,530; 35 —
1,825 splitting, 21,993 flattening and 2,700 comparison cases (30 terms, bases
5, 7 and 11). `code/32-ceilings-Makefile` (targets `pdf`, `check`, `clean`)
compiles the unshipped `beyond_ord.tex` and runs `finite_checks.py` under its
delivery name; `code/33-heights-build.sh` compiles the unshipped `article.tex`
into `.build/`; both build nothing in this layout and are kept as delivered.
The manuscripts can be rebuilt on a copy from
`git show e3839ad2c:docs/incoming/<archive>.zip` (their READMEs give
`latexmk -pdf` or three `pdflatex` passes).

**Batch 97.** Source 36's demonstrator (Python 3.10 or later, standard
library only) prints the letter `Ω`. On Windows it must run with
`PYTHONUTF8=1` (or `py -X utf8`): under the default code page it stops with
`UnicodeEncodeError`, and the report run then leaves a **0-byte** report
file. Its documented command `--report code/verification.json` overwrites
its argument, so run it on a copy. With this directory as `$R` and an empty
scratch directory `$S`:

```
cp "$R"/code/36-horizons-notation_demo.py "$S/notation_demo.py"
cd "$S"
PYTHONUTF8=1 python notation_demo.py --examples-only
PYTHONUTF8=1 python notation_demo.py --report verification.json
```

(PowerShell: `$env:PYTHONUTF8 = '1'` before the two commands.) Compare
`verification.json` with `data/36-horizons-verification.json`. Rerun on a copy
on 4 October 2026 with Python 3.14.4 on Windows: status `passed`, 994 distinct
terms, 493,521 unordered and 2,000 ordered pair checks against the independent
base-7 evaluator, 994 reflexive checks, 16 malformed inputs rejected, 8 tower
boundaries, largest evaluated integer 92 bits (seed 20261004); the report
equals the record except for `python_version` (3.14.4; recorded 3.12.14) and
CRLF line endings. `code/36-horizons-build.sh` compiles the unshipped
`beyond_ord.tex`; the manuscript can be rebuilt on a copy from
`git show d7cf7d554:docs/incoming/Beyond_Ord_Research_Package.zip` with
`latexmk -pdf -interaction=nonstopmode -halt-on-error beyond_ord.tex` in
`Beyond_Ord/` (40 pages, as recorded in `data/36-horizons-DOCUMENT_CHECKS.json`).

Scope and limitations of the demonstrator, from its unshipped guide
`code/README.md` (quoted as delivered):

> The article permits arbitrary positive **set-ordinal** coefficients. Python
> integers implement only the positive natural coefficients. In particular,
> the program has no code for an infinite set-ordinal constant such as ω. The
> printed symbol Ω denotes the paper's formal `Ord` symbol and is not that
> missing ω constant.
>
> Consequently this restricted language is not closed under the whole ordinal
> arithmetic of the article: arbitrary ordinal coefficients and arbitrary
> ordinal-indexed sums can leave it. For example, the supremum of the natural
> constants is the missing set-ordinal constant ω; similarly, the full grammar
> allows the term `Ω·ω`, which this program cannot express. No claim about a
> complete arithmetic implementation is made.
>
> This is **not a Lean formalization** or a formalization in another proof
> assistant. It does not implement proper classes, class quantifiers, a truth
> predicate, general elementary transfinite recursion, or an enumeration of
> all set ordinals. Python's ordinary recursion and memory limits apply.
>
> The report's successful outcome means that the listed bounded computations
> completed without disagreement. The proofs, foundational assumptions, and
> research-status qualifications belong to the accompanying article.

The same guide says that `monomial` "does not implement exponentiation of
arbitrary class-order presentations", that "there is no addition or
multiplication API", and that the checks compare the structural comparator
with an "independently implemented exact ordinary-natural evaluator" at the
radix 7; "these finite computations are evidence about the Python
implementation; **they do not prove any class-theoretic theorem**". Its tower
convention `w_0 = Ω`, `w_{n+1} = Ω^{w_n}` is the article's: `w_0 = [(1̄, 1)]`
is the term displayed `Ω`.

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
- The batch-83 placement message (`2e06337d5`) says that source 25's archive
  `Surreal_Well_Orders_Prefix_Symmetries.zip` arrived in `0d7b2441d`; it
  arrived in `5ad44b1ed` (`git log --diff-filter=A`), so batch 83's twelve
  archives arrived in five commits, not four. The staged bytes are unaffected;
  the report and this README give the correct commit.
- Sources 19–30 read this report at pins with Parts I–V (`d5bd4a67b`,
  `109aaca15`) or Parts I–VIII (`7ff7736ec`), and several describe it as it
  was then (Parts I–V, a four-source or 116-page merge) or say that it lacks
  what Parts VI–IX now hold. These sentences are kept as pinned provenance with
  dated `[merge]` corrections: for example source 30's opening of its Section 4
  (Note 64.14), source 23's "additions" and its
  "settle the additional case asked there" (Part XII), the "answers negatively
  the extension question" of sources 20 and 21 (second routes to Part VIII,
  Section 97), and source 22's "We have not shown that this label information
  can be discarded", answered by source 25 (Note 87.6).
- Corrections to batch-83 source text, each marked where made: two typos of
  source 29 (its lines 2123 and 2244, "sigma-compatp" and "distintp") and a
  stray double comma in its Proposition 4.3 (`D_{λ,,2^n−1}`); citations of this
  report and of sibling manuscripts replaced by cross-references; tagged
  numbered displays printed as starred displays. A draft of Part XI printed
  source 20's core as `𝒫_s(b)`; its codes are normalized permutations, so it
  is printed `𝒫_bd(b)` (Section 1.9, "Where the batch-83 merge had to
  choose").
- Source 28's headline question (complete metrizability of the full singular
  permutation space) was asked without knowledge of source 26, which answers it
  negatively in ZFC; it is printed with that status (Note 70.13).
- Source 31 is dated 4 October 2026, the UTC date of its arrival
  (`7c0f2d9f9`, 3 October 2026, 21:36 PDT). It cites this report by its pin
  `2b7b388ba` and blob `05807d292`, which is the text of the batch-83 write
  `07ee2b30c`, so the numbers it cites (Theorem 13.1, Theorem 21.1, Research
  question 113.209) are the current ones; its bibliography's key for this
  report is printed as `gczAtPin`, its key `HamkinsRecursion` (Hamkins's 2014
  post) as this report's `HamkinsRecursionPrinciple`, since this report's
  `HamkinsRecursion` is a different, 2017 post. Source 31's README says "No
  repository files were modified", which is true of its delivery.
- Source 31's main theorem depends on an abstract interface to Glazer's
  published countermodels whose exact match with Glazer's Propositions 3.8 and
  4.11 has not been reviewed; it is printed as claimed, with that dependency
  flagged in the Part's introduction, in Section XV.5.1, in Section 1.4 and in
  the abstract.
- Batch 96. Source 35 is dated 5 October 2026, after its pin and its arrival
  (4 October 2026, 17:22 PDT); source 33's files carry 5 October timestamps.
  Source 32 calls the commit `8f7d4a5c8` a "root tree" (its tree is
  `08039c482`); source 33 records no commit. Sources 32 and 33 did not read Part
  XIV: source 32's claim to answer this report's termination question repeats
  source 20's `swo:lm:con:termination` (Remark XVI.1.1), and the "open"
  strength questions of both are answered (Section 113.28); source 33's
  Remark 5.5 leaves open an initiality that always holds (Remark XVI.5.29).
  These sentences are printed as delivered, with the dated corrections. Source
  33's description of this README as "twenty-three merged manuscripts and an
  860-page report" was accurate at its reading. Source 35's 2026 citations were
  checked online at this write (Section 1.11): Frittaion–Genovesi
  (arXiv:2603.13913v3, 14 July 2026), Jeon–Walsh (JSL, online 28 April 2026),
  Jeon's note (its Proposition 1.5 cites Rathjen), and the correction to
  Gitman–Hamkins's countdown argument recorded in the class-forcing paper's
  version 2 are as source 35 states; Glazer's MathOverflow question 270535 and
  the cited results of Williams's dissertation were not checked.
- The batch-96 placement message and dossier described Mathlib's
  `Ordinal.univ` and `Ordinal.type_lt_ordinal` as deprecated; only
  `Ordinal.univ_id` is (since 2026-03-20), as source 32 says. Source 32's
  `Zf.lean` declarations exist as it says.
- Renamings and label conventions of Part XVI are listed in Section 1.3.4; no
  source text was corrected and no statement strengthened. This write adds
  four statements of its own, marked `[merge]`: the identification of towers
  with histories (Remark XVI.5.24), the initiality of source 33's digit map
  (Remark XVI.5.29), its consequence under `ETR_{Γ+1}` (Remark XVI.5.31), and the
  choice-free completion theorem (Theorem XVI.6.21).
- No retraction was made; no claim of another report or README is refuted.
- Batch 97. Source 36 has no author line; its title page is dated "October
  2026" and its source audit "4–5 October 2026"; its PDF was created on 4
  October 2026, before its arrival (18:06 PDT). Its pin `e1d2f3048` is source
  34's; its audit adds that a code-search index first offered the older
  commit `555ee36fb`. It did not see Part XVI: its sentences presenting the
  horizon theorem, parameter-free cofinality and truth promotion as "proved
  results of this investigation" (Section XVII.1.5, its title page, its status
  table in Section XVII.10.5) are printed as delivered with dated credit notes
  to sources 32–34. Its Theorem XVII.4.5 states leastness only against
  isomorphisms `Ω^{[X]} ≅ X`; its proof gives source 34's form against initial
  pre-fixed points, stated in Note XVII.4.B, not in the theorem. Its PDF title
  metadata drops "Finite-Support" (cosmetic). Its web citations (MSE 4072813,
  MathOverflow 116590 and 379630, Freire–Williams, Marcone–Montalbán, Traytel,
  Mathlib documentation) were not checked by this write. Two sentences of its
  question commentary are conjectures without proof ("Further finitary
  notation operators may force additional closure conditions"; "An audited
  coding might yield a small constant shift"); they are marked so in Section
  113.30. No statement of source 36 was found false, and none was moved or
  refuted.
- Corrections to Part XVI, made by the batch-97 write after an independent
  check of the four statements the batch-96 write had added (each marked
  "[corrected after independent check, 4 October 2026]" where made):
  Theorem XVI.6.21, the class of terms in item (1) misprinted `Tm` (it is the
  lemma's `T`), and the proof's first sentence reworded to mention that
  source 35's proof of Corollary XVI.6.19 also cites the GBC equivalence,
  which item (4) replaces; Remark XVI.5.24, "Γ nonempty" added; Remark
  XVI.5.29, the sentence calling the last part of source 33's question 12.7
  answered replaced by two readings (the base theory for `Φ`: GB; existence
  for every `W` of a map with initial image: exactly `CWO` over GB, while plain
  embeddings `x ↦ e_x` into `P(W)` are free in GB); Remark XVI.5.31, "for
  nonempty `W` and `Γ`" added to its last clause. No mathematical gap was found.

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
archives (sources 13–18) or of Parts VI–IX yet, nor of the batch-83 archives
(sources 19–30) or of Parts X–XIV. The claim most in need of one is source
19's Theorem 109.9: every externally set-sized two-sorted model of GBC gives
its pure external order `𝔚_all^𝓜` the complete theory of `σ(ℱ)`.

Batch 89: the Hilbert's-tenth research tree routed source 31's archive with
four other arrivals of the day
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_topology_surreal_arrivals_20261003.md`,
commit `6aadaa4f2`). It hashed the archive's three members, read bounded line
ranges of the manuscript (its lines 146–225, 359–376, 526–567, 678–703,
860–889, 1199–1263 and 1457–1473), ran nothing, and found that it yields no
Diophantine construction; that note records scope, not a proof review, and
has no correctness finding. There is no review of source 31 or of Part XV;
its Theorem XV.5.1, through its interface to Glazer's countermodels, is the
claim most in need of one, as source 31 itself says.

Batch 96: the same tree reviewed the four archives in a bounded intake
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_beyond_ord_e3839ad2c.md`,
commit `fcc4098ec`). It read 2,468 archive-member lines, including 1,665
manuscript lines, and a separate 446 lines of context, checked source 34's
choice-free power theorem and
set-subset criterion (Theorem XVI.4.2, Lemma XVI.2.2) in full and "found no
defect", confirmed that this report states the equivalence over GBC and left
the GB base open at the sources' pins, and found no demonstrably wrong
computational-interface claim; it did not audit the floor, finite-change,
reconstruction and restriction dependencies of the GB equivalence or the
fixed-point, condensation and spectrum proofs, ran nothing supplied, and
certifies none of the manuscripts. `review_beyond_ord_placement_111c38012.md`
(commit `b16786caf`) authenticates the placement byte for byte, with no new
mathematical read. `ordinal_two_type_effectivity_boundary.md` (commit
`c6082d075`) proves that no uniform effective procedure decides, for computable
well-orders of ℕ promised to have type ω or ω+1, which type occurs, and that
the upper type has no effective existential certificate; it is consistent
with sources 34 and 35's restrictions of their notations to supplied
coefficient orders and selected effective systems and refutes no claim. None
covers Part XVI as written (Section XVI.12). The claims most in need of review
are the full GB dependency analysis (Theorem XVI.5.8; Note XVI.5.10), source
32's exact truth presentation (Theorem XVI.8.12), source 35's separation on
`Ord` (Theorem XVI.7.11) and this write's Theorem XVI.6.21. This is the
historical intake assessment; the later bounded reviews below cover selected
publication proofs, with the empty-domain qualifications of Review remark H5.

A later bounded review of the actual Part XVI publication at `62b16914e` is
recorded in `review_beyond_ord_write_62b16914e.md` in the same research tree,
with the separate `review_beyond_ord_gb_62b16914e.md`. The selected GB
history, floors, finite changes, normal forms, anchored restriction and
completion arguments pass, including the internal finite-code induction in
Theorem XVI.6.21. This is neither a full proof audit of Part XVI nor a
formalization. Truth presentation, separation and spectrum proofs remain
outside that scope. The finite notation interfaces provide no paid
fixed-arity ordinary-integer computation history.

The following numbered review remarks retain three incorrect publication
claims and their concrete counterevidence.

1. **Review remark R1 (coverage).** The earlier phrase “2,468 selected lines
   of the four manuscripts” counted non-manuscript material as manuscript
   reading. The pinned intake receipt counts 392+318+584+371=1,665 TeX
   lines and 803 other archive-member lines, totaling 2,468. Its 446 context
   lines are separate. The corrected wording above preserves that scope.
2. **Review remark R2 (dependency pin).** The phrase “pinned Mathlib
   v4.31.0” is false at `62b16914e`: both root and surreal `lake-manifest.json`
   give `inputRev: v4.32.0` and revision
   `81a5d257c8e410db227a6665ed08f64fea08e997`. This corrects the repository
   pin, not any separately consulted documentation. The source's named API
   and deprecation statements remain attributed claims, not newly audited
   Mathlib history.
3. **Review remark R3 (output path).** The early guide said the program
   writes `artifacts/finite_notation_results.json` relative to its working
   directory. Its line 161 instead constructs
   `Path(__file__).with_name("finite_notation_results.json")`, so it writes
   beside the script. This inert source observation agrees with the later
   delivery instructions; no supplied program was run.

Independent check of the Part XVI write (dated 4 October 2026): an
adversarial verification of the four statements the batch-96 write added
(Theorem XVI.6.21; Remarks XVI.5.24, XVI.5.29, XVI.5.31), made by the intake
session for the batch-97 write (a working note, not shipped), rechecked source
34's set-subset criterion, every use of global choice in source 35's proofs
of its 3.5, 5.3, 5.7, 5.8, 5.9 and 5.10, the internal induction of Theorem
XVI.6.21 (3), the identification of towers with histories, the digit map and
source 33's converse, and found no mathematical gap: Theorem XVI.6.21 is
valid after two editorial fixes, the remarks after the fixes listed under
"Other discrepancies". The fixes are made, each with a dated note; Theorem
XVI.6.21 is now marked as independently checked. This is a careful reading,
not a formal verification, an external review or an entry of the
collection's review record.

**Review remark H5 (qualification of earlier passes).** The preceding
working-note report and the frozen `62b16914e` GB/publication reviews missed
empty-domain qualifications in the tower/history and digit/converse chain.
The later [four-correction review](../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_horizons_xvi_corrections_a21a42d8c.md)
retains the counterexamples: `W=1, Γ=0` has an exhausting tower but no
canonical history under the printed definition; `W=0, Γ=1` embeds initially
but is outside the exact-tower definition. The digit proof now treats the
empty schedule, the source converse states nonempty W, and the broader
embedding equivalence treats both empty cases separately. The adjacent
Note XVI.5.32 likewise says “all nonempty class well-orders” and retains
its former unrestricted wording with the same empty-carrier counterexample.
Those fixes
preserve the endpoint results. The GB completion proof remains valid;
the earlier unqualified passes remain on record with this scope correction.
Its retained dependency correction now has the explicit locator Review
remark H4 in the article; the notation correction was typographical.

Batch 97: the same tree reviewed source 36's archive in a bounded intake
before placement
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_beyond_ord_package_d7cf7d554.md`,
commit `39bb02ece`). It authenticated the nine members and the four hashes of
`DOCUMENT_CHECKS.json`, read 1,879 lines of the manuscript, checked the
set-localization lemma, the ordinal initial segment and carrier reduction, the
power calculus with its transport, continuity, predecessor and set-likeness
results, the hereditary comparison, root decomposition, towers and least
fixed point, the normal-form addition and multiplication and the transfer
theorem, read the uniform diagonal and the horizon theorem's setting, filter
and complexity hierarchy, and found no defect and requested no correction. It
records that the arithmetic procedures keep ordinal-label primitives and that
the demonstrator has no addition or multiplication API. It did not read the
proofs of the epsilon interpretation, the epsilon and zeta calibrations, the
general spectrum theorem, truth promotion, the variation of `G`, the
admissible bound or the unrolling proposition, and ran no delivered program.
The placement (`6571ee1af`) read the main proofs and recomputed the three
worked products. A later [bounded publication review](../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_horizons_write_a21a42d8c.md)
at `a21a42d8c` reads the full 557-line guide diff and 1,698 selected article
lines, authenticates all nine archive members, five placements and 70 source
label routes, and passes the selected arithmetic proofs, the stronger
initial-embedding leastness of Note XVII.4.B and the fixed-standard-complexity
syntax hierarchy. It corrects three editorial claims, retained below and
as Review remarks H1–H3 in the article. It does not certify the epsilon
interpretation/calibrations, general spectrum, truth promotion, varying-G,
admissible-bound or unrolling proofs. No supplied program was run, and the
ordinal-relative arithmetic supplies no paid fixed-arity integer compiler.

1. **Review remark H1 (multiplication scope).** The guide, notation table
   and Part XVII introduction extended multiplication to points of every
   `Ω^{[B]}`. At `B=2`, multiplying the point-cut Ω by itself gives the
   whole order Ω², which cannot be a proper point-cut of itself. Both
   operations are proved on `𝖤`; only addition extends to every such power.
2. **Review remark H2 (set-likeness).** The guide omitted `A≥2` and
   nonempty B. At `A=1, B=Ord+1`, the power is the set-like singleton
   although neither criterion alternative holds. At `A=Ord, B=0` the
   same failure shows why the second hypothesis is needed.
3. **Review remark H3 (set-base collapse).** The guide omitted “set ordinal
   a≥2” from `a^{[Ord·B]}≅Ord^{[B]}`. Taking `a=1, B=1` would assert
   `1≅Ord`. The corrected guide repeats the printed corollary's premise.
