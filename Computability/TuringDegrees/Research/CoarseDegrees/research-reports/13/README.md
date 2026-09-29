# Exact Ideals and Optimal Jumps in Coarse Description Classes

**Countable ideal realization, fixed-oracle exact partners, and a uniform classification of the guarded diagonal set**

Research report 13 of the CoarseDegrees research programme, dated
28 September 2026, built from one manuscript (author line: "Prepared for
Vladimir Reshetnikov"). It belongs to round 2 (batch 37), which continues
the programme's research plan (`../research-plan/turing_degrees_unified.tex`)
after the nine round-1 reports on C1 and report 10. Its main target is C6;
it also proves C4.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batch 37, manuscript 09 | `Exact_Ideals_and_Optimal_Jumps` (inner directory `exact_ideals_coarse/`, main file `article.tex`, 26-page PDF) | `6c9175a54` | `37e61c1fd` | `0e53d1034` | the whole article, Sections 1–11 and Appendices A–B |

The pin is the full commit `6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0` (a
batch-36 reciprocal-notes commit; the article's `\snapshot` macro). Between
the pin and the placement commit, `Computability/TuringDegrees/` changed
only by the addition of reports 11–14, so the plan, the synthesis and the
coverage ledger the article cites (blobs `ebecd2e15…`, `c88062125…`) are
those of the current tree.

**Status: AI-assisted, unrefereed, not formalized.** The proofs are
conventional and use no published theorem as a black box. Placement in the
research programme of a Lean/Rocq project confers no formal status (see
"Relation to the Lean library").

```
article.tex              the report, standalone LaTeX with an internal bibliography
article.pdf              the compiled report, 29 pages (unnumbered title page, then
                         pages 1-28: contents page 1, text from page 2)
README.md                this guide
PROOF_AUDIT.md           the delivery's proof audit (delivered as audit/PROOF_AUDIT.md)
SOURCES.md               the delivery's source and provenance record (delivered as
                         audit/SOURCES.md; see "Discrepancies")
code/build.sh            the delivery's build script (see "Build")
code/finite_checks.py    finite combinatorial diagnostics (Python standard library)
data/results.json        recorded run of finite_checks.py: PASS
data/validation.json     the delivery's build and inspection record of its 26-page PDF
                         (delivered as audit/validation.json)
```

Every file under `code/` and `data/`, and both audit files, are
byte-identical to the delivery. The delivered `README.md` and PDF are not
shipped: this README replaces the first, and `article.pdf` is a build of the
written text. Delivery names map to shipped paths as follows:
`checks/finite_checks.py` → `code/finite_checks.py`, `checks/results.json` →
`data/results.json`, `audit/validation.json` → `data/validation.json`,
`audit/PROOF_AUDIT.md` → `PROOF_AUDIT.md`, `audit/SOURCES.md` →
`SOURCES.md`, `build.sh` → `code/build.sh`. The package had no checksum
file.

## Labels and numbering

Every label in `article.tex` carries the prefix `cr13:`. The 74 delivered
labels keep their names after the prefix. The write added fifteen: the new
Sections 1.4–1.7 (`cr13:sec:wnotation`, `cr13:sec:wprov`,
`cr13:sec:wformal`, `cr13:sec:wtargets`), Subsections 8.3, 8.4, 9.2 and 9.3
(`cr13:sec:density`, `cr13:sec:ednot`, `cr13:sec:implementation`,
`cr13:sec:diagnostics`), Questions 10.1–10.5 and 10.8 (`cr13:q:generic`,
`cr13:q:c7`, `cr13:q:intrinsic`, `cr13:q:profilespectrum`,
`cr13:q:minimal`, `cr13:q:c2`) and Appendix B (`cr13:app:sources`): 89 in
total. Every theorem, equation and section number is that of the delivered
PDF: the `.aux` numbers of all 74 delivered labels were compared with a
build of the delivered text, with no change.

Text added in the write is marked `[write]`: a note below the contents,
Sections 1.4–1.7, and notes after Corollary 6.3, in Section 9.3 and in
Appendix B. No statement of the manuscript was changed.

## Setting and notation

`D ≈ F` means that `D △ F` has density zero; `CD(F)` is the set of coarse
descriptions of `F`; `Core(F)` the sets computed by all of them; `𝓛(B)` the
lower Turing cone of `B` (the `Low(B)` of the plan and of report 11, in
another typeface). The columns are `C_i = {c(i,t) = 2^i(2t+1) − 1}`, and
`𝓡(A)(c(i,t)) = A(i)` is the dyadic code (the plan's `R`, Lean `Rc`). `X` is
the guarded diagonal set of the synthesis (Definition "Guarded diagonal
set") and of the plan's (K5) and C6. `TOT` is the index set of total
functions.

Section 1.4 of the article is a dictionary against the plan, the synthesis,
the Lean library and the other round-2 reports. The readings most likely to
mislead:

- **J is shifted.** Here `J(A)(t) = A(n)` on `I_n = [2^n − 1, 2^(n+1) − 1)`,
  i.e. the plan's `J(A)(t + 1)`. The plan's `J` and the Lean `blockCode` use
  blocks `[2^n, 2^(n+1))`. So the profile `F(c(i,t)) = J(A_i)(t)` of
  Section 6 is not literally the plan's C4 set; the core formula is the
  same.
- **Z and F.** `Z = ⊕_i D_i` is the join of the *constructed descriptions*,
  and `F` is the target (in Section 6, the ideal code). In report 11 the
  ideal code is called `Z`.
- `H` is the presentation oracle (in Section 7, `H = X ≡_T ∅'`), `P_k` are
  protected regions, `B_k` local oracles; report 11's `P` and `H` are
  different objects.
- "High spectrum" means `{d : 0'' ≤ d'}` with no bound `d ≤ 0'`.

No symbol was renamed and no normalization changed.

## What the report claims

Numbers are those of `article.pdf` (and of the delivered PDF).

- **Theorem 3.5 (guarded set).** `X ≡_uc 𝓡(TOT)`, by two uniform
  algorithms (Lemmas 3.2–3.4: a limit approximation to `TOT` from any
  description; a dominating function from such an approximation; a
  description from a dominating function). The description spectrum and
  both coarse-class spectra of `X` equal `{d : 0'' ≤ d'}`; in particular
  `∅'' ≤_T D'` for *every* `D ≈ X`.
- **Theorem 5.1 (layered exact ideals with joint jump control).** For a
  target `F ≤_T H` with increasing protected regions `P_k` (uniformly
  `H`-computable, complements infinite with upper density → 0), local
  oracles `B_k ≤_T H` computing `P_k` and `F ∩ P_k`, and
  `I = ⋃_k 𝓛(B_k) ⊆ Core(F)`: there are `D_i ≈ F` with `Z = ⊕_i D_i`,
  `𝓛(Z) ∩ 𝓛(H) = I`, `D_i ≰_T H`, `(Z ⊕ H)' ≡_T H'`, `Z ≤_T H'`, and
  `𝓛(W_S) ∩ 𝓛(W_T) = I[W_(S∩T)]` for all nonempty finite joins.
  Corollary 5.2 (finite joins realize the finite-subset order, meets on
  overlaps), Corollary 5.3 (a literal description exact against `H`).
- **Theorem 6.2, Corollary 6.3 (C4).** For the robust column profile,
  `Core(F) = ⋃_k 𝓛(A_0 ⊕ … ⊕ A_(k−1))`; the possible cores are exactly the
  countable Turing ideals. Corollary 6.4: every countable ideal is the
  common lower cone of an exact pair inside one density-zero class, with
  `(E ⊕ F)' ≡_T H'`; Corollary 6.5: strict chains have no least upper bound
  but exact upper bounds in one class.
- **Theorem 7.1 (C6).** There are `D_i ≈ X` with
  `𝓛(Z) ∩ 𝓛(∅') = Comp` and `D_i' ≡_T Z' ≡_T (Z ⊕ ∅')' ≡_T ∅''`; each
  `D_i ≤_T ∅''`, `D_i ≰_T ∅'`; finite joins have the pattern of
  Corollary 5.2. The first-jump bound is optimal by Theorem 3.5.
  Corollary 7.2: neither coarse class of `X` has a least degree (not new).
- **Examples 8.1–8.2.** The arithmetical sets as a core; two presentations
  of the computable ideal, one with a least degree and one (`F = 𝓡(TOT)`)
  without, so the core does not determine attainment.
- **Section 10**: ten research questions (10.1–10.10).

## What the report does not claim

- **Not formalized** (next sections). The Python diagnostics check finite
  combinatorics only (dyadic counts, block majority, reservoir preservation,
  shared-coordinate amalgamation); they implement no halting oracle and
  certify no Turing-degree statement.
- **The source's own non-claims.** The guarded set, the dyadic criterion
  (relativized Jockusch–Schupp Theorem 2.19), robust coding, reservoir
  methods and the C4 formula are attributed to their sources; exact pairs
  and the negative answer to C1 are not claimed as new; bibliographic
  priority for the extensions is not established. Not solved: the
  prescribed-`Δ⁰₂`-1-generic half of C6, C2, C7, C8, the absence of minimal
  elements; no arbitrarily prescribed computable disagreement budget; no
  uniform computable selector of the guarded sections; no perfect family
  below one fixed oracle. Theorem 3.5 concerns *the* guarded set, not every
  complete c.e. set; the partner is low over `∅'`, not low; the density
  cutoffs are `H'`-computable, not computable; the effective-dense case is
  not obtained by relabelling errors as omissions.
- **Priority relative to the round.** The manuscript does not cite
  Hirschfeldt–Jockusch–Schupp 2021 (Theorem 3.11(2)), which reports 11 and
  12 identify as a close published antecedent of the column code; a
  `[write]` note after Corollary 6.3 says so.
- **Review at intake.** Lemmas 3.2–3.4 and the fixed-oracle lemma were read
  and found sound, and the suite was rerun on a copy. That is not an
  independent proof review.

## Programme targets addressed, and what stays open

Line numbers are those of the current tree (identical at the pin).

- **C6** (`research-plan/turing_degrees_unified.tex:603-604`; `:1647` names
  "the ∅'' bound in C6" among the quickest gains). The plan proposes a
  partner `D ≤_T ∅''` of the guarded set with computable common lower cone
  and asks "whether D can have D' ≤_T ∅''". Theorem 7.1 gives both, with
  `D' ≡_T ∅''` optimal. "What replaces ∅'' for a general approximable X" is
  answered only for targets with a layered presentation (Theorem 5.1, bound
  `H'`) and stays open in general (Question 10.3). The exploratory half, a
  prescribed `Δ⁰₂` 1-generic, stays open (Question 10.1).
- **C4** (`:585-598`). Theorem 6.2 and Corollary 6.3 prove the plan's core
  formula for the shifted code. The upper inclusion comes from the
  exactness clause of Theorem 5.1, not from the robust radius (HJKS
  Theorem 3.7) of the plan's sketch. Of the tasks at `:598`: the conclusion
  is checked by a different route; the literature antecedent HJS 2021 is not
  cited here (see reports 11 and 12); whether the class has a least degree
  depends on the presentation, not only on the ideal (Example 8.2), and
  stays open in general (Question 10.4); the uniform core is not addressed.
  The exact-pair consequence proposed at `:598` is obtained for a pair and a
  countable family in one class (Corollaries 5.2, 6.4), not for a perfect
  family.
- **Classification** (`research-synthesis/Turing_Degrees_Synthesis.tex:973`):
  the ideal half is answered (also by reports 11 and 12); Theorem 3.5 adds
  that the guarded set's spectrum is the jump-cone `{d : 0'' ≤ d'}`, a shape
  the synthesis already realizes; the general spectra question stays open.
- **Effectivity** (`:972`): for the guarded set an exact partner is now
  bounded by `∅''` with jump `∅''`; the `Δ⁰₂` generic case, arithmetical
  bounds for perfect families, and budget witnesses below `0'` stay open.
- **Not addressed**: minimal elements (`:970`) and C5 (plan `:600`); C2
  (plan `:563`, synthesis `:969`; report 14 is the round's C2 report); C7
  (plan `:606`); C8 (plan `:609`, synthesis `:971`).

The plan's C6 text still lists the first-jump question as residual, and the
synthesis items above are unchanged; this report does not edit them.

## Relation to the Lean library

Nothing in this report is formalized. It relies on none of the eight
statements admitted by the Lean library `CoarseDegrees`
(`Computability/TuringDegrees/Lean/CoarseDegrees`), since it uses no
published theorem as a black box.

- **Proved in Lean with nothing admitted, reproved here.** The column facts
  of Lemma 2.5: `card_tail`
  (`Computability/TuringDegrees/Lean/CoarseDegrees/Columns.lean:74`),
  `densityZero_of_bounded_columns` (`Columns.lean:85`) and
  `errCnt_div_tendsto` (`Majority.lean:166`). Proposition 2.6 in limit form:
  `description_iff_limit` (`Majority.lean:297`) and `spectrum_Rc`
  (`Spectrum.lean:137`); the library has no jump operator, so the
  `A ≤_T B'` form and the limit lemma (Lemma 2.1) are not stated. The
  sparse coding of Lemma 2.3 is `exists_description_of_degree`
  (`BlockChar.lean:42`).
- **Same argument, different code.** Lemma 2.7 is the majority argument of
  `blockCode_decode` (`Block.lean:254`), which is stated for the unshifted
  code; the shifted statement is not in Lean.
- **Not formalized**: the guarded set (the library has none) and Section 3,
  the reservoir lemmas and Theorem 5.1 (they need a use-bounded model of
  Turing functionals, which the library does not have), Sections 6–8.
  Section 9.2 is a formalization plan: no Lean or Rocq code was delivered or
  is shipped. The ledger the article cites, `Computability/TuringDegrees/COVERAGE.md`,
  tracks the separate `TuringDegrees` library.

## Relation to the other reports

Round 2 (batch 37) filed four reports: `../11` (finite profiles of
coalition cores; proves C4 for the plan's literal code via HJKS 3.7),
`../12` (a merge of three manuscripts: every countable Turing ideal is a
core, core-neutral insertion, an upper cone in every core fibre), this
report, and `../14` (C2). The three C4 proofs are independent and use three
different routes; none contradicts another. Theorem 3.5 and Theorem 7.1
refine the synthesis's guarded-set results (Theorem "Properties of the
guarded diagonal set" and the corollary that an exact partner cannot be
`Δ⁰₂`).

## Build

From a scratch copy of the directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

pdfLaTeX with newpx, AMS, mathtools, microtype, booktabs, tabularx,
enumitem, xcolor, fancyhdr, titlesec, xurl, needspace and hyperref; no
bibliography processor. The build of `article.pdf` has no errors, undefined
references or citations, multiply defined labels, duplicate destinations,
or overfull or underfull boxes (as for the delivered text). The delivered
`code/build.sh` changes to its own directory and runs
`python3 checks/finite_checks.py` and `latexmk` there, so it fails in the
shipped layout; use the commands here.

## Rerunning the diagnostics

The script writes `results.json` next to itself, so never run it in place
(it would add `code/results.json`). On a copy:

    mkdir <scratch>; cp code/finite_checks.py <scratch>/
    cd <scratch>; py finite_checks.py
    # compare <scratch>/results.json with data/results.json

Python 3.10 or later, standard library only. At intake the copy run passed
(exit 0) and its `results.json` equals `data/results.json` apart from line
endings (the script writes CRLF on Windows).

## Discrepancies in the delivered files

- **False repository statement.** `SOURCES.md` line 8 records an "Initial
  discovery tree: 1a1396d4d3a2ac6812692df520517d86ba3a4785", and line 10
  says it "is a TREE object, not a commit". It is a commit (the batch-36
  placement commit, whose tree is `c3a58d9d3502…`). The "Commit tree"
  `246be5549…` on line 7 is correct for the pin. Shipped unchanged; Section
  1.5 of the article says so.
- `data/validation.json` describes the delivered 26-page PDF (335,092 bytes)
  and names `checks/results.json`; `article.pdf` has 29 pages.
- Appendix B of the article names `checks/finite_checks.py` and says the
  archive contains `article.pdf`; a `[write]` note there gives the shipped
  names.
- `code/build.sh` refers to the delivery layout (see "Build").
