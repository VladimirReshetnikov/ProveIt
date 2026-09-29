# Finite Realization of Coarse-Information Profiles

**Countable Turing ideals, generic secret sharing, and simultaneously unattained representative spectra**

Research report 11 of the CoarseDegrees research programme, dated
28 September 2026, built from one manuscript (author line: "Prepared for
Vladimir Reshetnikov with ChatGPT"). It is the first report of round 2,
which continues the programme's research plan
(`../research-plan/turing_degrees_unified.tex`) after the nine round-1
reports on C1 and report 10.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batch 37, manuscript 07 | `Coarse_Information_Profiles` (inner directory `coarse_information_profiles/`, main file `article.tex`, 28-page PDF) | `1a1396d4d` | `37e61c1fd` | `0e53d1034` | the whole article, Sections 1–14 and Appendices A–B |

The pin is the full commit `1a1396d4d3a2ac6812692df520517d86ba3a4785`
(the batch-36 placement commit), which the article displays in Section 2.1.
Between the pin and the placement commit, `Computability/TuringDegrees/`
changed only by the addition of reports 11–14, so the plan, the synthesis,
reports 01–10 and the Lean library are byte-identical at the pin and at
`0e53d1034`, and every repository statement in the article is true of the
files it names.

**Status: AI-assisted, unrefereed, not formalized.** The proofs are
conventional; two published theorems of Hirschfeldt–Jockusch–Kuyper–Schupp
are used as black boxes. Placement in the research programme of a Lean/Rocq
project confers no formal status (see "Relation to the Lean library").

```
article.tex              the report, standalone LaTeX with an internal bibliography
article.pdf              the compiled report, 31 pages (title and abstract page 1,
                         contents and reading guide page 2, text from page 3)
README.md                this guide
PROOF_AUDIT.md           the delivery's dependency and quantifier audit, as delivered
SOURCES.md               the delivery's repository and literature sources, as delivered
code/build.sh            the delivery's three-pass pdflatex script (see "Build")
code/verify_finite.py    finite algebra and counting checks (Python standard library)
data/results.json        recorded run of verify_finite.py: all finite checks passed
data/validation.json     the delivery's build and layout record of its 28-page PDF
```

Every file under `code/` and `data/`, and both audit files, are
byte-identical to the delivery. The delivered `README.md` and PDF are not
shipped: this README replaces the first, and `article.pdf` is a build of the
written text. The delivered checksum file `CHECKSUMS.sha256` (9 entries, all
verified at placement) is not shipped, by repository policy. Delivery names
map to shipped paths as follows: `checks/verify_finite.py` →
`code/verify_finite.py`, `checks/results.json` → `data/results.json`,
`validation.json` → `data/validation.json`, `build.sh` → `code/build.sh`.

## Labels and numbering

Every label in `article.tex` carries the prefix `cr11:`. The 84 delivered
labels keep their names after the prefix. The write added ten:
`cr11:sec:wnotation`, `cr11:sec:wprov`, `cr11:sec:wformal`,
`cr11:sec:wtargets` (the new Sections 2.4–2.7), `cr11:def:relgeneric`
(Definition 3.5), `cr11:app:notation` (Appendix A), and four on existing
subsections (`cr11:sec:quantifiers` 5.2, `cr11:sec:nonattain` 9.2,
`cr11:sec:checks` 12.2, `cr11:sec:route` 12.3): 94 in total. Every
theorem, equation and section number is that of the delivered PDF: the
`.aux` numbers of all 84 delivered labels were compared with a build of the
delivered text, with no change.

Text added in the write is marked `[write]`: a note on the title page,
Sections 2.4–2.7, and notes after Theorem 5.2, in Section 12.2 and in
Appendix B. No statement of the manuscript was changed.

## Setting and notation

`X`, `Y`, `D` are binary sequences; `δ(X,Y)` is the upper density of
`X △ Y`, and `D ≈ X` means `δ(D,X) = 0`. `Core(X)` is the class of sets
computed by every `D ≈ X` (the `X^𝔠` of HJKS), `Core^B(X)` its
relativization to a background oracle `B`, `Low(B)` the lower cone of `B`,
`Comp` the computable sets. For participants `[n]`, `X_C` is the specified
periodic interleaving of the `X_i`, `i ∈ C`. `J` is the block code, `R_k`
the `k`th dyadic column `{2^k(2t+1) − 1}`, `Z` the ideal code of a generator
sequence, `P` an oracle presenting all generators.

Section 2.4 of the article is a dictionary against the plan, the synthesis,
the Lean library and the other round-2 reports. The readings most likely to
mislead:

- **J** is the plan's `J` and the Lean `blockCode` exactly (blocks
  `[2^n, 2^(n+1))`, `J(A)(0) = 0`). Reports 12 and 13 also use other block
  conventions, for example blocks `[2^n − 1, 2^(n+1) − 1)`.
- **R_k is a column, not a code.** `R_k = {x : ν₂(x+1) = k}` (the fibre of
  the Lean column index `col`). It is *not* the dyadic code
  `R(A)(n) = A(ν₂(n+1))` of the plan, the synthesis and Lean `Rc`, which this
  article never uses. `R` alone (Theorem 6.1) is a generic real, and
  `R_{S,j}` are mask streams.
- **Z is the plan's X.** The ideal code `Z` is the set `X` of the plan's
  proposed C4 proposition; the presentation oracle is `P`, which need not
  belong to the ideal.
- `⊕` is oracle join and `△` symmetric difference; `Spec_nc`, `Spec_uc` are
  Turing spectra of coarse classes, not report 14's effective-dense spectra.

No symbol was renamed and no normalization changed.

## What the report claims

Numbers are those of `article.pdf` (and of the delivered PDF).

- **Theorem 1.1 (finite profile realization).** An assignment
  `(I_C)_{C ⊆ [n]}` equals `(Core(X_C))_C` for some `X_1, …, X_n` iff every
  `I_C` is a countable Turing ideal, `I_∅ = Comp`, and `C ⊆ D` implies
  `I_C ⊆ I_D`. The realization can make every nonempty coalition's
  density-zero, uniform and nonuniform coarse classes lack a least Turing
  degree, and, for a presentation `P` of the ideals, the full join `H`
  satisfies `P <_T H <_T P'` and `H' ≡_T P'`.
- **Theorem 5.2 (C4).** For the column code `Z(r_k(t)) = J(A_k)(t)`,
  `Core(Z) = ⋃_m Low(A_0 ⊕ … ⊕ A_(m−1))`; every countable Turing ideal is a
  core, and `Z ≡_T ⊕_k A_k` uniformly. This verifies the plan's C4 sketch.
- **Proposition 5.3.** The uniform *exact* core (one functional for all
  descriptions) of `X` over `B` is `Low(B)`; unrelativized it is `Comp`.
- **Theorem 6.1, Corollaries 1.2 and 6.2 (two-share synergy).** For every
  countable ideal `I` there are `X`, `Y`, both 1-generic relative to a
  presentation, with `Core(X) = Core(Y) = Comp` and `Core(X ⊕ Y) = I`; so no
  operation on cores computes the core of a join.
- **Lemma 7.2 (coalition normal form)** with `q_C = |C|L − (2^|C| − 1)` free
  coordinates, `L = 2^(n−1) + 1` streams per participant and
  `Q = n + (n − 2)2^(n−1) + 1` master coordinates; **Lemma 7.3** the
  approximation bound; **Propositions 8.1–8.2** the two inclusions.
- **Section 9.** Spectrum identity (Lemma 9.1) and least-representative
  criterion (Proposition 9.2), both already in the synthesis; Theorem 9.4
  (no least representative in any nonempty coalition), Corollary 9.5 (the
  infimum is unattained for principal ideals and absent for nonprincipal
  ones), Theorem 9.6 (`H ≡_T P ⊕ G`, and `(P ⊕ X_C)' ≡_T P'`).
- **Theorem 10.2 (access structures).** For any access structure, cores are
  `I` on authorized and `Comp` on unauthorized coalitions, and every
  nonempty unauthorized view is itself 1-generic relative to `P`, so
  `Low(X_C) ∩ Low(P) = Comp`; threshold and two-of-three examples.
- **Proposition 11.1.** Least representatives are closed under joins; hence
  the coalitions with least representatives form a union-closed family.
- **Section 13**: ten research questions (13.1–13.10).

## What the report does not claim

- **Not formalized** (next section). The Python program checks finite
  identities only: no genericity, no infinite quantifier, no compactness, no
  jump bound, no novelty.
- **The source's own non-claims.** No new solution of the retired C1; the
  minimal-element question (C5) is not settled — least is not minimal; the
  single-ideal construction is the plan's C4 sketch and uses an architecture
  already in HJS 2021 (Lemma 3.10, Theorem 3.11(2)), so it is verified and
  expanded, not presented as new; the finite additive sharing is classical
  (Ito–Saito–Nishizeki); "secret sharing" is mathematical, not a claim of
  cryptographic security; the lowness is relative to the chosen
  presentation `P`, not absolute, and `X_C' ≡_T P'` is not claimed for
  proper coalitions; the full spectra are not computed; the effective bound
  is not an algorithm taking an abstract ideal as input; countably many
  participants, the extension property and mixed leastness profiles are
  open (Questions 13.2–13.4); the literature search was bounded and
  priority is not established; nothing was refereed.
- **Review at intake.** The proofs were read, the counts `L`, `Q`, `q_C`,
  the 247 coalitions and 167 monotone access families on four points, and
  the three-participant example (15 streams, 7 relations, 8 free) were
  recomputed, and the suite was rerun on a copy. That is not an
  independent proof review.

## Programme targets addressed, and what stays open

Line numbers are those of the current tree (identical at the pin).

- **C4** (`research-plan/turing_degrees_unified.tex:585-598`, "V: proof
  sketch supplied; novelty unchecked"; proposed Proposition at `:588`):
  verified by Theorem 5.2. Of the tasks at `:598`: the sketch is checked
  (unrefereed); the literature check finds HJS 2021 as a close antecedent;
  *for which `(A_k)` the class has a least degree* is not answered beyond
  Proposition 9.2 (report 12, `../12`, takes it up for its own code); the
  *uniform core* is settled only for exact recovery (Proposition 5.3), not
  for uniform coarse reducibility. The quantitative exact-pair remark at
  `:598` is not addressed. Plan `:1647` named C4 among the quickest gains;
  reports 12 and 13 are the round's other proofs of it.
- **Classification** (`research-synthesis/Turing_Degrees_Synthesis.tex:973`,
  "Which countable ideals occur as cores, and which upward-closed sets of
  degrees occur as spectra, is not determined"): the ideal half is answered
  (all of them); the spectra half stays open.
- **Minimal elements** (`:970`) and **C5** (plan `:600`): not settled.
- **C2** (plan `:563`, synthesis `:969`) and **C8** (plan `:609`, synthesis
  `:971`): not addressed; report 14 is the round's C2 report.
- The finite profiles, two-share synergy, access structures and
  union-closure answer no plan target; they are the manuscript's proposed
  contribution.

The plan, synthesis and reports index are not edited by this report; the
synthesis item and the plan's C4 status are left to the programme's own
revision.

## Relation to the Lean library

Nothing in this report is formalized. The Lean library `CoarseDegrees`
(`Computability/TuringDegrees/Lean/CoarseDegrees`), which admits eight
published statements, relates to it as follows.

- **Relied on, admitted in Lean as well.** Theorem 3.6 (HJKS Theorem 4.2,
  relativized) is `OneGenericRel.core_le`
  (`Computability/TuringDegrees/Lean/CoarseDegrees/Cone.lean:221`,
  admitted); with computable background it is `OneGeneric.core_trivial`
  (`Published.lean:48`, admitted). Theorem 3.3 (HJKS Theorem 3.7) and the
  robust radius, Corollary 3.4, have no Lean statement.
- **Proved here informally, admitted in Lean.** Lemma 4.2 proves (as
  `δ(G,E) = 1`) the admitted `OneGenericRel.not_coarselyComputableIn`
  (`Cone.lean:228`): a set 1-generic relative to `P` has no `P`-computable
  coarse description. The unrelativized case is proved in Lean
  (`OneGeneric.not_setCoarselyComputable`, `GenericDensity.lean:124`). The
  informal proof does not discharge the Lean admission.
- **Proved in Lean with nothing admitted, reproved here.** Lemma 5.1 is
  `blockCode_decode` (`Block.lean:254`); the tail count (5.3) is `card_tail`
  (`Columns.lean:74`); the upward closure in Lemma 9.1 is
  `exists_description_of_degree` (`BlockChar.lean:42`, implanting on
  `{2^k − 1}` rather than `{2^k}`); relatively 1-generic sets exist by
  `exists_oneGenericRel` (`Cone.lean:196`), without the bound `G ≤_T P'` of
  Lemma 4.4 (the library has no jump operator). Proposition 9.2 is the
  core-member clause of the synthesis's least-representative theorem; the
  library proves its block-code clause (`isLeastNC_iff_blockCode`,
  `BlockChar.lean:67`), not this one.
- Everything else — Theorem 1.1, Theorem 5.2 (C4), Proposition 5.3, the
  sharing, normal-form, access-structure and jump results — is not
  formalized. Section 12.3 is a route to a formalization, not one: no Lean
  or Rocq code was delivered or is shipped.

## Relation to the other reports

Round 2 (batch 37) filed four reports: this one, `../12` (every countable
Turing ideal is a core, with core-neutral insertion and upper cones in
every core fibre; a merge of three manuscripts), `../13` (target C6 and
exact ideals; it also proves C4) and `../14` (target C2). Reports 12 and 13
prove Theorem 5.2's identity for other codes; nothing in them contradicts
this report. Report 10's hyperarithmetic failure of the robust-radius
principle is cited in Question 13.10.

## Build

From a scratch copy of the directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

pdfLaTeX with newpx, AMS, mathtools, microtype, booktabs, tabularx,
longtable, enumitem, xcolor, titlesec, fancyhdr, xurl and hyperref; no
bibliography processor. The build of `article.pdf` has no errors, undefined
references or citations, multiply defined labels, duplicate destinations or
overfull boxes; its seven underfull-box warnings are all present in a build
of the delivered text. The delivered `code/build.sh` changes to its own
directory and runs `pdflatex` on `article.tex` there, so it does not work
from `code/`; use `latexmk` as above.

## Rerunning the finite checks

The script writes `results.json` next to itself, so never run it in place
(it would add `code/results.json`). On a copy:

    mkdir <scratch>; cp code/verify_finite.py <scratch>/
    cd <scratch>; py verify_finite.py
    # compare <scratch>/results.json with data/results.json

Python 3.10 or later, standard library only. At intake the copy run passed
(exit 0) and its `results.json` equals `data/results.json` apart from line
endings (the script writes CRLF on Windows).

## Discrepancies in the delivered files

- `PROOF_AUDIT.md` says the article isolates the two published inputs as
  "Theorems 3.3 and 3.5"; in the article they are **Theorem 3.3 and
  Theorem 3.6** (Definition 3.5 shares the counter). The audit is shipped
  unchanged.
- `PROOF_AUDIT.md`, `data/validation.json` and Section 12.2 and Appendix B
  of the article name the delivery paths `checks/verify_finite.py` and
  `checks/results.json`; the shipped paths are above. `[write]` notes in
  Section 12.2 and Appendix B say so.
- `PROOF_AUDIT.md` ("All 28 pages were rendered") and
  `data/validation.json` (`pdf_pages: 28`, `pdf_bytes: 347941`) describe the
  delivered PDF, which is not shipped; `article.pdf` has 31 pages.
- `code/build.sh` refers to `article.tex` in its own directory (see "Build").
- `code/build.sh` is byte-identical to the `build.sh` of the research-report
  collection's `enumerative-combinatorics/adjacency-bounded-132-avoiders`; a
  generic script, not a repeated delivery.
