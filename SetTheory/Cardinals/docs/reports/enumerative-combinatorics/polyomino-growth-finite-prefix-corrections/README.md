# Finite-Prefix Corrections and Dual Certificates for Polyomino Growth

**A computer-assisted exact-rational bound λ ≤ 2249/500 = 4.498 for Klarner's constant, and a certificate theorem for convolution recurrences**

This is a report of ProveIt's research-report collection
(`polyomino-growth-finite-prefix-corrections`), dated September 2026 and
built from one manuscript. It continues the formal Lean project
`Combinatorics/Polyominoes/KlarnerConstant`, whose kernel-checked endpoint is
λ ≤ 9047/2000 = 4.5235. Author line of the source: "Research report prepared
for Vladimir Reshetnikov · AI-assisted research draft".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (only source) | batch 36, manuscript 06 | `ProveIt_Polyomino_Research` (delivered in `e13affd32`; delivered main file `article.tex`, 27-page PDF) | `e21766d04` | `1a1396d4d` | the whole article, Sections 1–10 and Appendices A–C; Sections 1.4, 1.5 and Appendix D added in the write |

**Status: AI-assisted and unrefereed. Nothing in this report is formalized.**
The new bound 4.498 is a computer-assisted theorem (exact enumeration plus an
exact rational certificate, replayed in Python), not a Lean theorem; the
project's Lean-verified bound remains 4.5235.

```
README.md                          this guide (replaces the delivery README)
VALIDATION.md                      the source's validation record, as delivered
article.tex                        the report, standalone LaTeX; \inputs tex/*.tex
article.pdf                        the compiled report, 32 pages (unnumbered title page,
                                   contents pages i–ii, then pages 1–29)
code/Makefile                      the delivered Makefile (moved from the package root; see below)
code/check_profile.py              compares a regenerated CSV table with data/profiles.json
code/discover_certificates.py      numerical candidate search and rounding (exploratory; overwrites data/)
code/enumerate.cpp                 incremental marked enumerator, sizes 1..18 (C++17)
code/enumerate_direct.cpp          direct-scanning marked enumerator (C++17)
code/make_tables.py                regenerates tex/*.tex from data/ (not part of the proof)
code/model.py                      the 53-monomial map, patterns, exact polynomial arithmetic
code/research.py                   set-based Python enumerator and float critical-point search (exploratory)
code/verify.py                     exact rational replay of every certificate (standard library only)
data/critical_estimates.json       floating-point critical estimates (not certified)
data/dual_original.json            the 53 balanced integer weights at ζ_dual = 100000/452349
data/profiles.json                 exact unmarked and marked counts, sizes 1..18
data/profiles_18.csv               the same table as CSV (19 columns × 18 rows)
data/profiles_python_11.json       the source's independent Python enumeration through size 11
data/requirements-discovery.txt    NumPy/SciPy/SymPy for the exploratory scripts (moved from the root)
data/upper_N7.json … upper_N18.json   twelve rational upper certificates, prefix sizes 7..18
data/verification.json             the verifier's exact record (rewritten by every --report run)
data/verification.txt              the verifier's recorded stdout
tex/dual_table.tex                 generated table of dual weights (cites \ref{eq:map})
tex/profiles_1_9.tex               generated profile table, sizes 1..9
tex/profiles_10_18.tex             generated profile table, sizes 10..18
tex/progress_table.tex             generated table of the prefix hierarchy
tex/upper_table.tex                generated N = 18 certificate table
```

That is 38 files: 4 at the root, 9 in `code/`, 20 in `data/` and 5 in
`tex/`. The delivered package had 39 files: the 35 shipped byte-identical
(code, data, `tex/`, `VALIDATION.md`), `article.tex` (the source of the
written text), and its README (replaced by this file), its 27-page PDF (replaced by a
build of the written text) and a checksum manifest `SHA256SUMS` (not shipped:
checksum manifests are abolished in ProveIt; all 38 of its entries matched the
delivered files at intake). Code, data, `tex/` and `VALIDATION.md` are
byte-identical to the delivery.

## Labels

Every label in `article.tex` carries the prefix `kfp:` with **one
exception, `eq:map`** (the 53-monomial map, equation (6)): the delivered,
generated and byte-identical `tex/dual_table.tex` cites it as
`\ref{eq:map}`, and `code/make_tables.py` regenerates that text, so the key is
kept unprefixed. The source had 53 bare labels (no duplicates, no
`\label[type]`); after the write there are 56: 52 prefixed source labels,
`eq:map`, and three new ones (`kfp:sec:notation`, `kfp:sec:formal-status`,
`kfp:app:provenance`). The write added cleveref type hints
(`\label[lemma]`, `\label[proposition]`) to the three lemma and proposition
labels, which share the theorem counter; before, cleveref printed them as
"theorem 3.2" and so on. No number changed through that.

Text added in the write is marked `[write]` in the PDF.

## Notation

Section 1.4 fixes the conventions; no delivered symbol was renamed and no
normalization changed.

- The seventeen upper-case letters `C, D, E, F, G, H, P, Q, R, S, T, U, V, W,
  X, Y, Z` name the neighborhood types and their counts; lower-case `c … z` are
  the coordinates of the vector `X`. Many of these letters are reused
  (`P_N` the exact prefix, `D_N` the defect, `T_N`, `Y_N`, `B_N`, the
  enumerator's sets `S`, `U`, `E`, the offset sets `R`, `E`, `B`, the nonlinear
  part `H`, the dual product `𝒞`, the map `F(X) = Φ(ζ,X)` and the unknowns
  `X_1, …, X_d` of a general system, …); Section 1.4 tabulates every reuse
  across sections (constants local to one proof are left to context).
- **Collision with the project.** The project's research note
  (`Combinatorics/Polyominoes/KlarnerConstant/Research/klarner-bound-4.5235.md`,
  §3) writes `b_N` for the ζ-weighted prefix profile. That profile is
  `p_N = P_N(ζ)` here; this report's `b_N` (Section 8) is the high-degree
  forcing vector, and `b_{ik}` are ξ-exponents. The project's supersolution
  `a` is `v` here. `λ`, `A(n) = A_n`, `ζ` and the map (`Φζ` there, `Φ(ζ,·)`
  here) agree.
- `A_0 = 0` here, unlike OEIS A001168's `a(0) = 1`.
- `μ_original` (growth of Bui's *uncorrected equality recurrence*) occurs only
  here. Tempting false reading printed in the article: its lower bound 4.52349
  is a lower bound on λ. **It is not.**

## What the report claims

Numbers are those of the built `article.pdf`.

- **Lemma 3.2** (formal fixed points and comparison) for proper positive
  polynomial systems (nilpotent linear part).
- **Theorem 3.3 (prefix-corrected majorant).** With the exact prefix `P_N`
  of the true counts, `Ψ_N(ξ,Y) = Φ(ξ,P_N+Y) − T_N` has nonnegative
  coefficients, and its fixed point gives `B_N = P_N + Y_N` with `A ⪯ B_N`
  and `[ξ^{≤N}]B_N = P_N`. No convergence is assumed.
- **Theorem 3.4 (rational upper certificate).** `v ≥ P_N(ζ)` (the tail
  condition, essential by Remark 3.5) and `v ≥ Φ(ζ,v) − D_N(ζ)` give
  `a_{i,n} ≤ v_i ζ^{-n}`, hence `A_n ≤ v_G ζ^{-n}` and `λ ≤ 1/ζ`.
- **Theorem 3.6.** `A ⪯ B_{N+1} ⪯ B_N`; a certificate for `N` is one for `N+1`.
- **Theorem 4.1 (computer-assisted).**
  `A_n ≤ (927884613/10^9)(2249/500)^n` for `n ≥ 1`, so
  **λ ≤ 2249/500 = 4.498 < 4.5**. It uses the size-≤18 marked table
  (Appendix A) and the `N = 18` rational vector (Table 2); every residual is
  at least 99/10^9 and every tail budget at least 14724/10^6. The certificates
  for `N = 7, …, 17` give 4.5233, 4.5225, 4.5212, 4.5194, 4.5173, 4.5149,
  4.5123, 4.5096, 4.5068, 4.5039 and 4.5009 (Table 3).
- **Proposition 4.2** (correctness of the include/exclude enumerator) and an
  a-priori `uint64` overflow bound through size 18.
- **Theorem 5.1 (balanced-monomial obstruction)**, by weighted AM–GM, and the
  lower-growth consequence (18).
- **Theorem 6.3 (certificate alternative)**, with Lemma 6.2: for productive,
  strongly connected, nonlinear positive polynomial systems with rational data,
  exactly one of "positive supersolution" and "balanced integer weights with
  product > 1" holds. This answers the certificate-existence part of Bui's
  Question 2 for that class.
- **Theorem 7.1.** `452349/100000 ≤ μ_original ≤ 9047/2000` for the
  uncorrected equality recurrence (53 integer weights of total 1,000,000, an
  exact rational log enclosure (20), and the project's 4.5235 vector
  replayed). So no supersolution of the uncorrected system proves a bound below
  4.52349; the improvement comes from the prefix correction.
- **Theorem 8.1 (stability and obstruction)** of the prefix hierarchy
  (`spr(J) < 1` gives certificates for large `N`; a supercritical, irreducible,
  nonzero-forcing case obstructs every `N`).
- **Theorem 8.2.** For `Φ = ξ + x²` and `A = ξ/(1−ξ)` (growth 1) the
  prefix-majorant growths tend to 3.
- A conditional sensitivity formula (24), a Lean extension plan (Section 9.3)
  and ten research questions (Section 10).

## What the report does not claim

Appendix D.3 lists the source's thirteen limitations (N1–N13) and three added
in the write (W1–W3):

- (N1) `μ_original ≥ 4.52349` is **not** a lower bound on λ.
- (N2) No new Lean formalization; the Lean proof of 4.5235 is not a proof of
  4.498, of the finite-prefix theorem, or of the size-18 data.
- (N3) The arithmetic checker does not prove that the table enumerates the
  stated objects; its consistency checks are necessary conditions only.
- (N4) The enumeration cross-checks are not a formal certificate that every
  size-18 object was generated exactly once; the two C++ implementations share
  one generation strategy. (The source's caveat that no fresh size-18 run was
  made after the final command-line changes is re-scoped below.)
- (N5) AI-assisted draft, not independently refereed.
- (N6) Novelty only relative to the inspected snapshot and sources; no
  exhaustive priority search.
- (N7) Geometric programming, weighted AM–GM and Redelmeier-style enumeration
  are prior tools.
- (N8) The alternative covers only productive, strongly connected, nonlinear
  systems; no uniform bit-length bound; no maximum or signed recurrences.
- (N9) The case `spr(J) = 1` is not classified.
- (N10) Theorem 8.2 does not disprove Bui's Question 1.
- (N11) The sensitivity formula is conditional and unused in Theorem 4.1.
- (N12) The numerical critical estimates (Table 3, middle column;
  `data/critical_estimates.json`) are not certified.
- (N13) The OEIS comparison is a consistency check, not an input.
- (W1) The geometric lemma is kernel-checked in ProveIt only relative to the
  transcription of Bui's diagrams into `Patterns.lean`.
- (W2) 4.498 remains unverified by Lean; 9047/2000 remains the project's
  Lean-verified bound.
- (W3) The earlier bounds (Eden, Klarner–Rivest, Barequet–Shalah) were not
  re-examined; their bibliographic data were checked, their contents not read.

## Relation to the formal project

The report does not live in, and is not part of, the Lean development; filing
it in the collection or citing the development confers no formal status on
it. What the project **has** formalized (namespace
`LeanProofs.KlarnerConstant`, files in
`Combinatorics/Polyominoes/KlarnerConstant/Lean/KlarnerConstant/`, no
`sorry`, project axiom or `native_decide`; audit in `Audit.lean`; the files
are unchanged between the pin and the placement commit):

| Statement in the report | Lean declaration | File:line |
|---|---|---|
| Bui's Lemma 4 for the actual marked counts, i.e. (7) coefficientwise (the manuscript calls it "imported") | `geometricPublishedBuiRecurrences : PublishedBuiRecurrences geometricCoefficientProfile` | `GeometricComplete.lean:63` |
| the five partitions (8), as equalities | `buiF_occurrenceCount_eq_g_add_p`, `buiG_…_eq_e_add_q`, `buiH_…_eq_d_add_s`, `buiR_…_eq_y_add_w`, `buiT_…_eq_x_add_v` | `GeometricLinear.lean:279–312` |
| `A_n ≤ G_n` (half of (5); `G_n ≤ nA_n` is not formalized) | `fixedPolyominoCount_le_geometricCoefficientProfile_g` | `GeometricProfile.lean:371` |
| supermultiplicativity and Fekete (3) | `fixedPolyominoCount_supermultiplicative`, `tendsto_realNthRoot_fixedPolyominoCount_growthSup` | `GeometricComplete.lean:97` (the latter) |
| λ ≤ 9047/2000 (the "old" bound, upper half of Theorem 7.1) | `certificate_isSupersolution`; `fixedPolyominoCount_le_9047_div_2000_pow`, `fixedPolyominoCount_real_le_9047_div_2000_pow`, `growthSup_fixedPolyominoCount_le_9047_div_2000` | `Certificate.lean:232`; `GeometricComplete.lean:69, 76, 88` |

Nothing else is formalized: not Lemma 3.2, Theorems 3.3–4.1, the size-18
table, or anything in Sections 5–8. The Lean endpoint chain is hard-wired to
`certificateZeta = 2000/9047`: `PrefixRecurrence.g_le_certificate`,
`PrefixRecurrence.g_lt_one`, `CoefficientProfile.g_lt_9047_div_2000_pow` and
`dominatedCoefficient_le_9047_div_2000_pow` (`Recurrence.lean:321, 327, 457,
477`). Only `buiIterate_le_supersolution` (`:283`) and
`PrefixRecurrence.le_supersolution` (`:309`) are ζ-generic, and
`growthSup_le_of_le_pow` (`Growth.lean:38`) is generic. A formal 4.498 needs a
prefix-corrected variant of that engine and a computable bridge to the
noncomputable `BuiNeighborhood.occurrenceCount` (`Patterns.lean:140`); the
`N = 7` certificate (4.5233, counts through size 7 only) would be a smaller
first target. This is recorded in Section 1.5 as a formalization target, not
a claim.

**Stale claim corrected in the text.** The delivered status box and Sections
1.3 and 2.3 call the geometric lemma "imported from Bui and the pinned
repository"; `[write]` notes there say that in ProveIt it is a Lean theorem
for the actual counts. The article's statement that the repository's endpoint
is 4.5235 is kept: it is the Lean-verified bound, and 4.498 stands beside it
as an unverified improvement. The project's own READMEs, its research note and
the walkthroughs are not edited by this report.

**Bibliography added in the write.** The source compares its bound only with
Bui's 4.5238 and the repository's 4.5235. A `[write]` paragraph in Section 1.1
adds the history recorded in the project's research note: Eden 6.75; Klarner
and Rivest 5, 4.83 and 4.649551; Barequet–Shalah 4.5252. The Barequet–Shalah
entry is copied from that note (Algorithmica 84 (2022), 3559–3586,
doi:10.1007/s00453-022-00948-6). The note names Eden and Klarner–Rivest
without bibliographic data; the entries used (Eden, Proc. Fourth Berkeley
Symp. Math. Statist. Prob., Vol. 4, 1961, 223–239; Klarner–Rivest, Canad. J.
Math. 25 (1973), 585–602) were checked against Project Euclid and Cambridge
Core listings during the write. The research note is itself a new
bibliography entry.

**Neighbouring reports.** No other report in the collection treats Klarner's
constant; the parallelogram polyominoes of
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/skew-partition-continued-fractions/`
are unrelated mathematics.

## Intake verification

All runs were on copies outside the repository (Appendix D.2).

- `code/verify.py --report …` passed ("ALL ARITHMETIC CHECKS PASSED.", 4.3 s
  at intake, 0.7 s on a rerun during the write) and printed exactly
  `data/verification.txt` (up to Windows line endings);
  `code/check_profile.py data/profiles_18.csv` reports "MATCH: sizes 1..18; 18
  unmarked and 306 marked counts."
- **Size-18 regeneration.** `code/enumerate.cpp` was compiled afresh
  (`c++ -O3 -std=c++17`, g++ 16.1.0, MinGW-w64 UCRT) and run as
  `enumerate 18` (8 min 23 s on one core). After CSV parsing its output equals
  `data/profiles_18.csv` in all 19 columns of all 18 rows (the raw files
  differ only in CRLF line endings). Fresh runs for sizes 11–14, 16 and 17
  (8 min 48 s) and `enumerate_direct 12` matched as well.
- An independent set-based Python enumerator, with pattern coordinates taken
  from the project's `Patterns.lean` rather than from this package, matched all
  10 unmarked and 170 marked entries through size 10.
- An independent transcription of the map from the project's research note
  reproduced the first defect (13), the `N = 18` residual minimum (≥ 9.9e−8),
  tail minimum (0.014724) and `v_G`, and confirmed the 4.5235 vector.
- Table 1 was compared with `Patterns.lean` entry by entry; `A_1 … A_18`
  equal OEIS A001168 (`A_18 = 1,540,820,542`, total through 18
  2,083,404,030).
- A 50-digit evaluation of `log 𝒞` gave 1.000668023145208770…, inside (20).
- The proofs of Lemma 3.2 and Theorems 3.3, 3.4, 3.6, 5.1, 6.3 and 8.2 were
  checked and that of Theorem 8.1 read; no gap was found. This is not an
  independent proof review.

**Re-scoped caveat.** `VALIDATION.md` (lines 31–35) says that no fresh size-18
run was made after the enumerators' final command-line changes. That run has
now been made from the final source, and matched. What remains: the
regeneration uses the same program and algorithm; the arithmetic checker
verifies arithmetic and necessary consistency conditions only; the
correctness of the enumeration rests on Proposition 4.2 and the
incremental-update argument together with this regeneration. The size-18
row also matters numerically: every `N = 18` residual is about 1e−7 and
`ζ^18 ≈ 1.8e−12`, so the certificate tolerates an error of only about
5.6 × 10^4 (relative 1e−5) in a single size-18 entry. The `N = 17` bound
4.5009 does not depend on that row.

## Build

MiKTeX or TeX Live with newpx, amsmath, mathtools, geometry, microtype,
booktabs, longtable, enumitem, fancyhdr, titlesec, listings, tcolorbox, xurl,
hyperref and cleveref. `article.tex` `\input`s the five `tex/*.tex` tables by
relative path, so build from the report directory (or copy `tex/` along):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX 26.2, pdfTeX 1.40.29) has 32 pages and no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull boxes; two underfull
boxes remain in narrow cells of the audit table (Appendix C). The delivered
text builds to 27 pages with no warnings or overfull boxes and twelve
underfull boxes (the audit table and long bibliography URLs; `xurl`, added in
the write, removed the latter).

## Rerunning the checks

Every command runs from the report root under the shipped names, but three
scripts **rewrite shipped files**, so work on a copy of the whole directory:

- `code/verify.py --report data/verification.json` rewrites
  `data/verification.json` (with CRLF line endings on Windows);
- `code/make_tables.py` rewrites all five `tex/*.tex` (it hardcodes the
  "1–6" row value 4.523499228 in `tex/progress_table.tex` rather than
  deriving it);
- `code/discover_certificates.py` overwrites `data/upper_N*.json` and
  `data/dual_original.json`.

`code/research.py` writes `critical_estimates_new.json` (no arguments) or the
named output file into the working directory. `verify.py` and
`check_profile.py` need only the Python standard library; the exploratory
scripts need NumPy, SciPy and SymPy (`data/requirements-discovery.txt`).

On this machine (`python3` is spelled `py`; GNU make is not installed):

```sh
cp -r <report-dir> <scratch>/kfp && cd <scratch>/kfp
py code/verify.py --report data/verification.json
py code/check_profile.py data/profiles_18.csv
c++ -O3 -std=c++17 code/enumerate.cpp -o enumerate
./enumerate 11 > prefix11.csv && py code/check_profile.py prefix11.csv
./enumerate 18 > regenerated.csv && py code/check_profile.py regenerated.csv   # ~8–9 min
```

Where GNU make exists, the moved Makefile works from the (copied) report
root as `make -f code/Makefile verify` (or `tables`, `article.pdf`); it calls
`python3`.

## Delivered files that use delivery names or name unshipped files

- The delivery README (not shipped) named `SHA256SUMS` and `article.pdf`,
  `Makefile` at the root, `requirements-discovery.txt` at the root and
  `python3`. `SHA256SUMS` is not shipped; `article.pdf` is a new build;
  the other two files are in `code/` and `data/`.
- `code/Makefile` is written for the package root (`python3 code/verify.py`,
  `article.tex`); see above.
- `VALIDATION.md` uses `python3`, describes the delivered 27-page PDF (with
  contact-sheet inspections that are not shipped), and states the size-18
  caveat re-scoped above.
- `article.tex` Section 9.2 speaks of "the archive" and its PDF and uses
  `python3`; a `[write]` note there gives the shipped layout.
- `research.py`'s default output and `discover_certificates.py`'s
  certificate files are not shipped outputs; see "Rerunning".

## Provenance

- **Pin** `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9` (delivery README and
  `article.tex` preamble). The project was unchanged between the pin and the
  placement commit `1a1396d4d`.
- **Placement.** Placed in `1a1396d4d` as a new single-source report, first
  under `Combinatorics/Polyominoes/KlarnerConstant/Research/finite-prefix-corrections/`
  and then moved into this collection; the archive was delivered in
  `e13affd32` and retired in the placement commit. Manuscript 06 of batch 36.
- **What the write changed.** Labels prefixed (`eq:map` kept); cleveref type
  hints on three labels; Sections 1.4 (notation) and 1.5 (formal status) and
  Appendix D (provenance, intake verification, non-claims) added; `[write]`
  notes in the title-page box, the "three levels" box, Section 1.1 (earlier
  bounds), Section 2.3 (twice), Section 4.4 (intake regeneration), Section 9.2
  (layout), Section 9.3 (Lean plan), Research question 1 and three rows of
  Appendix C; four bibliography entries; `xurl` and two macros in the
  preamble. No delivered sentence was deleted and no statement changed. A
  single source required no merge choices.
