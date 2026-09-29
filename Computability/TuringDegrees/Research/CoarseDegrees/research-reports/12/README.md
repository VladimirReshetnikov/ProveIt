# Every Countable Turing Ideal as Coarse Common Information

**Exact spectra and Turing-cone embeddings with a fixed core; effective exact pairs, layered recovery, and prescribed jumps**

Research report 12 of the CoarseDegrees programme, built from three
AI-assisted manuscripts dated 28 September 2026. Author lines: "Prepared for
Vladimir Reshetnikov" (sources 10 and 12; "Research manuscript prepared for
Vladimir Reshetnikov" in their PDF metadata) and "Research draft prepared for
Vladimir Reshetnikov" (source 08). All three attack plan target **C4** ("Is every countable Turing
ideal a core?") and the "Classification" item of the synthesis's "What is not
settled".

| Source | Manuscript | Archive (inner directory) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 12 (base) | batch 37, manuscript 12 | `ProveIt_Coarse_Ideal_Realization` (same), *Every Countable Turing Ideal as Coarse Common Information*, 22-page PDF | `1a1396d4d` | `0e53d1034` | Part I: Sections 1–11, Appendices A–B |
| 08 | batch 37, manuscript 08 | `ProveIt_Coarse_Core_Realization` (same), *Every Countable Turing Ideal Is a Coarse Core: Effective perfect exact pairs and rich fibres of the core map*, 22-page PDF | `1a1396d4d` | `0e53d1034` | Part II: Sections 12–19 |
| 10 | batch 37, manuscript 10 | `coarse_core_realization` (same), *Every Countable Turing Ideal Is a Coarse Core: Layered realization, exact pairs, and order embeddings with fixed common information*, 22-page PDF | `1a1396d4d` | `0e53d1034` | Part III: Sections 20–29 |

The pin is `1a1396d4d3a2ac6812692df520517d86ba3a4785` for all three. The
archives arrived in `37e61c1fd`. The directory number 12 follows the
programme's numbering by archive modification time (earliest member of the
merge, source 08); it is not a manuscript number. Appendix C of the article
is the provenance record.

**Status: AI-assisted, unrefereed, not formalized.** Every result, proof,
example, remark, question and limitation of the three manuscripts is printed.
Results proved by more than one source are printed once and credited;
genuinely different proofs are kept as marked second routes. The merge adds
two observations that no source makes (Remarks 13.5 and 17.7), marked
`[merge]` and unrefereed.

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 71 pages
README.md                                    this guide
12-ideal-realization-PROOF_AUDIT.md          source 12's proof audit, as delivered
12-ideal-realization-SOURCE_LEDGER.md        source 12's source ledger, as delivered
08-effective-exact-pairs-PROOF_AUDIT.md      source 08's proof audit, as delivered
08-effective-exact-pairs-SOURCES.md          source 08's source ledger, as delivered
10-layered-realization-proof_audit.md        source 10's proof audit, as delivered
10-layered-realization-sources.md            source 10's source ledger, as delivered
code/12-ideal-realization-finite_checks.py   source 12's finite checks (Python standard library)
code/12-ideal-realization-build.sh           source 12's three-pass pdflatex build (delivery layout; see below)
code/08-effective-exact-pairs-verify.py      source 08's finite checks (Python standard library)
code/08-effective-exact-pairs-build.sh       source 08's check-then-build script (delivery layout; see below)
code/10-layered-realization-check_finite.py  source 10's finite checks (Python standard library)
code/10-layered-realization-build.sh         source 10's latexmk build (delivery layout; see below)
data/12-ideal-realization-results.json       source 12's recorded run: 7 groups passed
data/12-ideal-realization-validation.json    source 12's build and PDF-inspection record
data/08-effective-exact-pairs-verification.json  source 08's recorded run: 552,927 checks passed
data/08-effective-exact-pairs-document_qa.json   source 08's build and PDF-inspection record
data/10-layered-realization-results.json     source 10's recorded run: 616,836 cases in 8 groups passed
```

Every file except `article.tex`, `article.pdf` and this README is
byte-identical to the delivery. Delivery names map to shipped names as
follows. Source 12: `PROOF_AUDIT.md`, `SOURCE_LEDGER.md`, `build.sh`,
`checks/finite_checks.py`, `checks/results.json`, `validation.json` become the
`12-ideal-realization-` files above; its `article.tex` was staged unprefixed
and is the base of this `article.tex`; its `README.md` was staged and is
replaced by this README; its PDF is not shipped. Source 08: `PROOF_AUDIT.md`,
`SOURCES.md`, `build.sh`, `code/verify.py`, `data/verification.json`,
`data/document_qa.json` become the `08-effective-exact-pairs-` files; its
`article.tex`, `README.md`, PDF and `SHA256SUMS.txt` (verified, dropped by
policy) are not shipped. Source 10: `proof_audit.md`, `sources.md`,
`build.sh`, `checks/check_finite.py`, `checks/results.json` become the
`10-layered-realization-` files; its `article.tex`, `README.md` and PDF are
not shipped. The unshipped files survive in the arrival commit `37e61c1fd`.

Shipped files whose text still uses delivery names or names unshipped files:

- `08-effective-exact-pairs-PROOF_AUDIT.md` names `code/verify.py` and
  `data/verification.json`, and cites source 08's numbering. Its Theorems
  1.1–1.2 are Theorems 12.1–12.2 here; a number in its Sections 3–8 gains 10
  (Theorem 7.3 is Theorem 17.3, Proposition 8.1 is Proposition 18.1); its
  Lemmas 2.2–2.3 are Lemma 2.2 and Proposition 2.3 of Part I, and its
  Appendices A and B are Lemmas 7.1 and 9.1 of Part I.
- `10-layered-realization-proof_audit.md` names `checks/results.json`, its
  "Appendix A" (here Lemma 9.1 of Part I) and the delivered 22-page PDF.
- `12-ideal-realization-PROOF_AUDIT.md` cites source 12's numbering, which
  is unchanged here.
- `data/12-ideal-realization-validation.json` and
  `data/08-effective-exact-pairs-document_qa.json` describe the delivered
  22-page PDFs, which are not shipped.
- `code/*-build.sh`: each changes to its own directory (`code/`) and then
  expects the delivery layout (`article.tex` beside it; source 08's also runs
  `code/verify.py`). They do not work in this layout; use the build and rerun
  instructions below.
- Inside the checkers, docstrings name `article.tex` and (source 10)
  `checks/check_finite.py`, meaning the source's own manuscript and path.

## Labels and numbering

Every label carries the prefix `cr12:`. Source 12's 78 labels are kept
unchanged after the prefix; the write added `cr12:sec:earlier`,
`cr12:rem:shortcode`, `cr12:sec:assembly`, `cr12:sec:notation`,
`cr12:app:provenance` and the three part labels `cr12:part1`–`cr12:part3`
(86 in all). Source 08's labels carry `cr12:ep:` (68), source 10's
`cr12:lr:` (61). **215 labels in total**, none duplicated (the staged
`article.tex` had 78). Labels of statements printed only once, in Part I
(source 08's `lem:core-basics`, `lem:spectra`, `cor:infimum`, `lem:limit`,
`thm:inversion` and their sections; source 10's `lem:spectra`, `lem:joins`,
`prop:necessary`, `lem:limit`, `thm:dyadic`, `lem:rmonotone`, `thm:fjiproof`
and their equations), were not carried over; source 08's `app:verification`
became `cr12:ep:subsec:verification`. The questions of sources 08 and 10,
unlabelled in the delivery, were labelled.

Part I keeps source 12's numbering exactly: the merge notes carry no
counter, and the two added subsections (1.4, 1.5) contain no numbered
statement. Source 08's Section *n* is Section *n* + 10 for *n* = 3, …, 9, so
its Theorem *n.m* is Theorem (*n* + 10).*m*; its Sections 1–2 are Section 12
(its Theorems 1.1–1.3 are Theorems 12.1–12.3), its Section 10 is Section
19.1, and its Appendix C is Section 18.5. Source 10's Section *n* is Section
*n* + 18 for *n* = 3, …, 11; its Sections 1–2 are Section 20 (Theorems
1.1–1.3 are 20.1–20.3), its Section 12 is Section 29.1. Remarks 13.5 and 17.7
are the merge remarks, placed last in their sections so that no source number
moves. Parts II and III each start on a new page.

## Setting and notation

Binary sets, total binary coarse descriptions `CD(X)`,
`Core(X) = ⋂_{D ∈ CD(X)} Low(D)`, `Spec(X)` the Turing degrees computing a
description (equivalently, of descriptions), and the uniform and nonuniform
coarse reducibilities `≤uc`, `≤nc`. Section 1.5 of the article fixes one
notation for all three parts; the main collisions it resolves:

- **Three block codes.** `J` (Part I; `J(B)(0) = 0`,
  `J(B)(t) = B(⌊log₂ t⌋)`, blocks `[2^k, 2^{k+1})`) is the plan's `J` and the
  Lean `blockCode`. Source 08's `𝖩`, here `J^sh`, uses blocks
  `[2^k − 1, 2^{k+1} − 1)`: `J^sh(U)(t) = J(U)(t + 1)`, **not** `J`. Source
  10's `𝒥`, here `J^!`, uses factorial blocks `[(m+1)!, (m+2)!)` with labels
  `ν₂(m+1)`, every label recurring infinitely often.
- **Three carriers.** Part I's ideal code `X_A` puts `E(A_i) = J(R(A_i))` on
  column `i`, for any sequence; source 08's `Q(A)` puts `J^sh(A_n)`; source
  10's layered carrier puts `J^!(A_n)`, for an increasing chain. **Source 10
  calls its carrier `X_A`; here it is `Λ_A`, and it is not Part I's `X_A`.**
- **Presentation oracles.** `A_⊕ = ⊕_n A_n` and `A_{<m} = ⊕_{n<m} A_n`
  (source 12's `S`, source 08's `B` and `B_m`, source 10's `Z`);
  `Θ_A = ⊕_m A_{<m}'` is source 08's `H_A`.
- **Parameters.** The dyadic parameter is `H` (with `K`) throughout: source
  10's `B, C` and source 08's `C, E` are renamed. `T_X(H) = X ⊕ R(H)` is Part
  I's filter, and source 10's `F_{A,B}` is `T_Λ(H)`. Source 08's `F_C`, here
  `𝖥_H = Q(W^H)`, puts the parameter in constant rows *inside* the code: it is
  not `T_X(H)` (Remark 17.7 shows the two are uniformly coarsely equivalent
  for `X = Q(A)`). The jump cone `{b : H ≤_T B'}` is `𝒬_H` (source 08:
  `𝒥(deg H)`, a clash with the block code).
- **Other renames.** Source 08's columns `P_n` are `C_n`; source 10's
  `c_n(k)`, `Σ(X)`, truncations `T_s`, `U_s(B)`, `V_s`, the robust-lemma sets
  `A_s` and the common function `H` of Lemma 23.2 are `p(n,k)`, `Spec(X)`,
  `Λ_{A,<s}`, `U_s(H)`, `Λ^H_{A,<s}`, `Ã_s` and `G`. Source 08's "fibre" is
  spelled "fiber". No normalization changed.

## What the report claims

Theorem numbers are those of the built `article.pdf`.

### Part I (source 12)

- **Theorem 3.1 (robust radius), proved from Baire category** in the
  prefix-density metric: `A ∈ Core(X)` iff some `η > 0` has `A ≤_T Y` for
  every `Y` with `δ(X, Y) < η`. It is an equivalent form of HJKS (2016)
  Theorem 3.7; Corollary 3.4 is finite-stage capture.
- **Theorem 5.1 (ideal realization).** For every sequence `(A_i)`,
  `Core(X_A) = ⋃_k Low(A_0 ⊕ … ⊕ A_{k−1})` and `X_A ≡_T ⊕ A_i`; the cores of
  binary sets are exactly the countable Turing ideals.
- **Theorem 6.2 (whole-row spectrum).** `Spec(X_A) = Row(A)`: the degrees
  computing a binary array `f(i,s,n)` with `∀i ∃s_i ∀s ≥ s_i ∀n
  f(i,s,n) = A_i(n)`; Corollary 6.3 bounds it; Example 6.4 shows the
  presentation matters (constant rows give `Spec = {b : H ≤_T b'}` with core
  `Comp`).
- **Theorems 8.2 and 8.4.** If `γ(Y) = 1` then `Core(X ⊕ Y) = Core(X)` for
  every `X`; hence `Core(T_X(H)) = Core(X)` and
  `Spec(T_X(H)) = Spec(X) ∩ 𝒬_H`; Corollary 8.5 gives strict extensions and
  unattained or absent infima.
- **Theorem 9.2 (fixed-core upper-cone embedding).** For `H, K ≥_T X'`,
  `H ≤_T K ⇔ T_X(H) ≤uc T_X(K) ⇔ T_X(H) ≤nc T_X(K)`, join-preserving, above
  `[X]`, with distinct spectra; Corollary 9.3 (continuum many spectra per
  core) and Corollary 9.4 (no maximal member and no countable cofinal family
  in a fiber).

### Part II (source 08)

- **Theorem 13.2 (computable retraction normal form).** Descriptions of
  `Q(A)` are Medvedev equivalent to arrays whose rows are finite variants of
  the `A_n`; Corollary 13.3 computes `Spec(Q(A))` from it.
- **Theorem 12.2 (effective perfect exact pairs), proved in Section 15.** A
  `Θ_A`-computable continuous injection `P ↦ D_P` into `CD(Q(A))` with
  `Low(D_P) ∩ Low(D_Q) = I_A` and `D_P' ≤_T Θ_A ⊕ P`, one common
  `Θ_A`-computable null envelope with an explicit modulus and prefix density
  at most `2^{−m₀}`; Corollary 15.2: a computable common mask forces a
  principal core.
- **Theorem 12.1 / Section 16.** Realization by row-finite forcing (no Baire
  argument, no compactness), and a second route from HJKS Theorem 3.7;
  Corollary 16.2; the arithmetical pair with `D', E' ≤_T ∅^(ω)`.
- **Section 17.** Spectrum factorization `Spec(𝖥_H) = Spec(Q(A)) ∩ 𝒬_H`
  (17.1), uniform monotonicity (17.2), the upper-cone embedding above `A_⊕'`
  (17.3), oracle accounting (17.4), **prescribed-jump exact pairs**
  `H ≤_T D_P' ≤_T H ⊕ P` in one class, equality for computable `P` (17.5),
  and continuum many no-least classes per core (17.6).
- **Proposition 18.1.** One functional extracting a fixed set from every
  description exists only for computable sets (the uniform exact core is
  `Comp`).

### Part III (source 10)

- **Lemma 21.2.** `J^!` recovers `A` from any `D` with `δ(D, J^!(A)) < 1/2`.
- **Theorem 20.1 / Section 22.** Realization for the layered carrier from
  HJKS Theorem 3.7 via the ideal approximation Lemma 22.2.
- **Theorem 23.4 (ideal-protected fusion).** For any set with an
  ideal-protected presentation, a `W'`-computable splitting system of pairwise
  exact descriptions, close in the prefix metric; a proof of realization
  without compactness.
- **Theorem 24.1 and Theorem 20.3.** Core-preserving spectral cuts for
  `T_Λ(H)` by approximants in the ideal, and perfect exact-pair families in
  `CD(T_Λ(H))` with splitting systems computable in `(A_⊕ ⊕ H)'`.
- **Theorem 25.1** (the case `X = Λ` of Theorem 9.2 on the cone above
  `A_⊕'`), Theorem 26.2 (continuum many no-least classes per core),
  Corollary 26.3 (perfect antichains of descriptions).
- **Theorem 27.1 (fourfold localization).**
  `𝒦_{2^{−n}}(Λ) ⊆ Low(A_n) ⊆ 𝒦_{2^{−n−2}}(Λ)`; Example 27.2; Proposition
  27.3 (noncanonical carriers).

### What the merge settles

Plan target C4's tasks: the sketch is checked (four routes: the robust
radius in Theorem 5.1; HJKS Theorem 3.7 as a black box in Sections 16.1 and
22; row-finite forcing in Section 16; ideal-protected fusion in Theorem
23.4); the literature check finds HJS (2021),
Lemma 3.10 and Theorem 3.11; for which sequences the class of the code has a
least degree is decided for `X_A` by Theorem 6.2 with Corollary 2.5; the
uniform exact core is `Comp` (Proposition 18.1). The synthesis's
"Classification" item is answered for cores and stays open for spectra.

## What the report does not claim

- **Priority.** All three sources present realization as answering a
  question the synthesis left open. The programme's research plan, at the
  same pin, already stated the theorem as target C4 with a proof sketch (tier
  V: "proof sketch supplied; novelty unchecked";
  `research-plan/turing_degrees_unified.tex`, problem heading C4 and
  `prop:idealcore`). None of the sources cites the plan. The column mechanism
  has the antecedent Hirschfeldt–Jockusch–Schupp, arXiv:2106.13118 (2021),
  Lemma 3.10 and Theorem 3.11, which source 12 credits and sources 08 and 10
  omit; the robust radius is HJKS (2016) Theorem 3.7. No source claims
  established worldwide priority; each says its literature check was
  targeted, not exhaustive. Source 08: the classification "should not be
  advertised as a previously unknown general theorem"; ordinary exact-pair
  existence, the no-splitting method, the limit lemma and jump inversion are
  classical.
- **Spectra.** No source classifies all coarse spectra, or all spectra with a
  prescribed core; the spectrum formulas describe the constructions only.
- **Minimal elements.** Absence of a least representative is proved, never
  absence of minimal ones.
- **Effective density.** No source answers the effective-dense
  least-representative question (C2) or transfers its constructions to
  error-free descriptions; none transfers the Turing arguments to
  hyperarithmetic reducibility.
- **Thresholds and bounds.** The upper-cone thresholds are sufficient, not
  claimed optimal; the embeddings are not claimed injective below them;
  Theorem 9.2 does not map the bottom of the cone to `[X]` and does not claim
  the fiber is closed under joins; the factor four of Theorem 27.1 and the
  jump bounds of Parts II and III are not claimed optimal; no computable
  rates, arithmetical bounds or counting budgets are given; a perfect family's
  members are not all below its construction oracle.
- **Uniformity.** No source claims a general equivalence of `≤uc` and `≤nc`;
  the equivalences hold only for the displayed families.
- **Assurance.** The finite Python checks test finite arithmetic and coding
  geometry, not Baire category, Turing reducibility, convergence, jump
  inversion or any full theorem. No source is refereed; none is
  Lean-verified.

## Relation to the programme and to the Lean library

- **Plan and synthesis** (`../../research-plan/`, `../../research-synthesis/`):
  C4 is answered as above. C5 (minimal elements, shape of spectra) and C8
  (uniform classes) stay open; the synthesis's "What is not settled" items
  Classification (spectra half), Minimal elements, Uniform classes and
  Effectivity remain open, the last partly addressed by the jump bounds of
  Parts II and III. The plan and synthesis are not edited by this report.
- **Report 11** (batch-37 manuscript 07) verifies C4 through HJKS Theorem 3.7
  and answers part of Question 11.4 here: two sets with computable cores can
  have any countable ideal as the core of their join. Its relativized uniform
  exact core extends Proposition 18.1.
- **Report 13** (manuscript 09) proves C4 again as an application of a
  layered-reservoir theorem close to Theorem 23.4, and treats target C6.
- **Report 14** (manuscript 11) treats C2, which no part of this report
  answers.
- **Report 10** (hyperdegrees) is cited by source 10 to delimit its
  Turing-theoretic claims; it shows that cone-avoiding compactness fails for
  `≤_h`.

**Placement beside the Lean/Rocq project `Computability/TuringDegrees`
confers no formal status.** None of the new theorems is formalized. The Lean
library `Computability/TuringDegrees/Lean/CoarseDegrees` proves, with nothing
admitted according to its README, these ingredients the report uses:
`card_tail` and `densityZero_of_bounded_columns` (`Columns.lean`: the exact
tail count and the bounded-column density criterion of Lemma 4.1),
`errCnt_div_tendsto` (`Majority.lean`: restriction of density-zero errors to
a column), `blockCode_decode` (`Block.lean`: every description of `J(A)`
computes `A`; the library's `blockCode` is `J`, not `J^sh` or `J^!`),
`description_iff_limit` (`Majority.lean`) and `spectrum_Rc` (`Spectrum.lean`:
Theorem 7.2 in limit form, without the jump), `exists_description_of_degree`
(`BlockChar.lean`: the sparse-coding step of Proposition 2.3, markers
`2^k − 1`), and `isLeastNC_iff_blockCode` (`BlockChar.lean`: classes with a
least degree are exactly block-code classes). For the last one the library
README says nothing is admitted, while its `#print axioms` line in
`Audit.lean` sits under the heading that expects `sorryAx`; this report did
not rebuild the audit. The library has no jump operator, no prefix-density
metric, no statement of HJKS Theorem 3.7 and no use-bounded model of Turing
functionals, so the robust radius, the limit lemma, jump inversion, every
realization, spectrum, neutrality and embedding theorem, and every
construction of Parts II and III are unformalized.

## Rerunning the finite checks

Run each checker from this directory with an explicit output path outside
the report (the defaults would create `code/results.json` or
`data/verification.json`, which are not shipped names):

```sh
py code/12-ideal-realization-finite_checks.py --output <scratch>/12-results.json
py code/08-effective-exact-pairs-verify.py --output <scratch>/08-verification.json
py code/10-layered-realization-check_finite.py --output <scratch>/10-results.json
```

Python 3.10 or later, standard library only. Rerun for this write
(Python 3.14.4, on 28 September 2026), each matched its recorded output
except for fields that record the run: `generated_at_utc` in source 12's
file and `"python": "3.13.5"` in source 08's. Rewritten files come out with
CRLF line ends on Windows; the shipped ones are LF.

## Build

TeX Live or MiKTeX with geometry, newpx (`newpxtext`, `newpxmath`), amsmath/amsthm,
mathtools, microtype, xcolor, booktabs, tabularx, xltabular, array, enumitem,
fancyhdr, titlesec, needspace, tcolorbox, xurl and hyperref. No external
figures, bibliography database or downloads.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 71 pages, with no errors, undefined
references or citations, multiply defined labels, duplicate destinations,
LaTeX or package warnings, or overfull or underfull boxes. Source 12's
delivered text, rebuilt for this write, gives the 22 pages its
`validation.json` records, with no warnings, and every one of its 78 labels
has the same number there as here. The
delivered builds and their inspection records (`validation.json`,
`document_qa.json`, and the audits' notes on rendering) concern the delivered
PDFs, which are not shipped; these production checks do not verify the
mathematics.

## Other discrepancies

- `12-ideal-realization-SOURCE_LEDGER.md` gives the pinned commit's UTC
  date as 29 September 2026; that is correct (17:32 −0700 on 28 September).
- The source ledgers of sources 08, 10 and 12 describe the synthesis's
  "What is not settled" as the open question without mentioning the research
  plan's C4 entry; see "What the report does not claim".
- Source 12's delivered README said that rerunning its checks "replaces only
  `checks/results.json`"; in this layout the default output is
  `code/results.json` (a new file), so pass `--output`.
