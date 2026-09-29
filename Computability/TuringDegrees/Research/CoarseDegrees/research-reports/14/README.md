# Sparse Computable Erasures and Least-Degree Obstructions

**Low counterexamples, finite meets, and descending chains in effective-dense equivalence classes**

Research report 14 of the CoarseDegrees research programme, dated
28 September 2026, built from one manuscript (author line: "Research draft
prepared for Vladimir Reshetnikov"). It belongs to round 2 (batch 37), which
continues the programme's research plan
(`../research-plan/turing_degrees_unified.tex`) after the nine round-1
reports on C1 and report 10. It is the round's report on target **C2**
(least Turing degrees in effective-dense classes).

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batch 37, manuscript 11 | `proveit_effective_dense_research` (inner directory `proveit_effective_dense/`, main file `article.tex`, 22-page PDF) | `1a1396d4d` | `37e61c1fd` | `0e53d1034` | the whole article, Sections 1–11 and Appendices A–B |

The pin is the full commit `1a1396d4d3a2ac6812692df520517d86ba3a4785` (the
batch-36 placement commit), which the article prints in Section 1.1 and
Appendix A. Between the pin and the placement commit,
`Computability/TuringDegrees/` changed only by the addition of reports
11–14; the plan blob `ebecd2e15…` and its lines 552–573 that the article
quotes are those of the current tree.

**Status: AI-assisted, unrefereed, not formalized.** The proofs are
conventional; the low refinement uses one published theorem
(Kjos-Hanssen–Merkle–Stephan, Theorem 5.1) as an external input. Placement
in the research programme of a Lean/Rocq project confers no formal status
(see "Relation to the Lean library").

```
article.tex              the report, standalone LaTeX with an internal bibliography
article.pdf              the compiled report, 24 pages (unnumbered title page, then
                         pages 1-23: contents pages 1-2, text from page 3)
README.md                this guide
PROOF_AUDIT.md           the delivery's dependency and quantifier audit, as delivered
SOURCES.md               the delivery's repository and literature ledger, as delivered
REPOSITORY_UPDATE.md     the delivery's proposed C2 status text, as delivered;
                         NOT applied (see below)
code/build.sh            the delivery's build script (see "Build")
code/check_finite.py     finite invariant checks (Python standard library)
data/results.json        recorded run of check_finite.py (delivered as checks/results.json)
data/run.txt             recorded stdout of the same run (delivered as checks/run.txt);
                         byte-identical to data/results.json
```

Every file under `code/` and `data/`, and the three delivered markdown
files, are byte-identical to the delivery. The delivered `README.md` and PDF
are not shipped: this README replaces the first, and `article.pdf` is a
build of the written text. The delivered checksum file `SHA256SUMS` (10
entries, all verified at placement) is not shipped, by repository policy.
Delivery names map to shipped paths as follows: `checks/check_finite.py` →
`code/check_finite.py`, `checks/results.json` → `data/results.json`,
`checks/run.txt` → `data/run.txt`, `build.sh` → `code/build.sh`.

## REPOSITORY_UPDATE.md: filed, not applied

The delivery includes `REPOSITORY_UPDATE.md`, a suggested replacement for
the plan's C2 entry. It is shipped verbatim as a record of the delivery and
has **not** been applied: the plan, its README and the synthesis are
unchanged since the pin. It proposes:

- a new status for C2: "Negative answer supplied by a new conventional
  proof draft; not yet independently refereed or Lean-checked. Priority
  remains unverified";
- a summary of the result (every 1-generic computing no eventually different
  function, in particular every 2-generic and, via
  Kjos-Hanssen–Merkle–Stephan, every non-high 1-generic, has no least
  representative in either effective-dense class; low `Δ⁰₂` examples) and of
  the mechanism that bypasses the plan's gap (a bounded least-missing-offset
  function, infinitely-often computable agreement, and a decidable
  one-point-per-block selector escaping the omission set);
- the additional results (every-prefix budgets, the descending chain,
  exact finite meets, Boolean patterns, low representatives);
- to keep as separate questions: the high 1-generic case, minimal elements,
  arbitrary countable coinitiality, the common lower cone of all
  computable-null erasures, and c.e. counterexamples;
- that reviewers audit the selector lemma, the full-class quantifiers, the
  nonuniform listing of total functions in the packed chain, and the
  dependency of the low refinement on the published theorem.

Every mathematical sentence of the file matches the article. Whether and
how to amend the plan and the synthesis is separate programme work; this
report does not do it.

## Labels and numbering

Every label in `article.tex` carries the prefix `cr14:`. The 67 delivered
labels keep their names after the prefix. The write added seven: the new
Sections 1.4–1.7 (`cr14:sec:wnotation`, `cr14:sec:wprov`,
`cr14:sec:wformal`, `cr14:sec:wtargets`) and Subsections 9.2, 11.2 and 11.3
(`cr14:sec:gap`, `cr14:sec:formal`, `cr14:sec:checks`): 74 in total. Every
theorem, equation and section number is that of the delivered PDF (the
equations are numbered (1)–(14) through the whole article): the `.aux`
numbers of all 67 delivered labels were compared with a build of the
delivered text, with no change.

Text added in the write is marked `[write]`: a note below the contents,
Sections 1.4–1.7, and notes after equation (3), in Section 9.2 and in
Section 11.3. The write also brackets the title page with
`\hypersetup{pageanchor=false}` … `{pageanchor=true}`; the delivered source
produced a duplicate `page.1` PDF destination because its title page resets
the page counter. No statement of the manuscript was changed.

## Setting and notation

An effective-dense description of `f` is a total `d : ℕ → ℕ ∪ {⊥}` with
`d(n) ∈ {f(n), ⊥}` and a density-zero omission set `S_d` (the strong-domain
convention of Astor–Hirschfeldt–Jockusch). `≤_ned` and `≤_ued` are the
nonuniform and uniform reducibilities, `[f]_r` the classes, `Spec_T([f]_r)`
their Turing spectra. `CA(G)` (local notation) says that `G` computes no
function eventually different from every computable function. `G_T` is `G`
with the computable mask `T` set to 0.

Section 1.4 of the article is a dictionary against the plan and the other
round-2 reports. The readings most likely to mislead:

- **G_T is not the plan's G_T.** The plan's line of attack
  (`research-plan/turing_degrees_unified.tex:570`) sets `G_T(n) = 2` on `T`;
  here `G_T(n) = 0` on `T`, so `G_T` stays binary. For computable null `T`
  both are `≡_ued G` and Turing equivalent to `G ↾ (ℕ ∖ T)`, so the degree
  statements hold for either; only the binary one is a set representative.
  A `[write]` note after equation (3) prints this.
- **Effective-dense, not coarse.** Reports 11–13 and the synthesis study
  coarse descriptions (errors allowed); here only explicit omissions are
  allowed. `Spec_T` here is an effective-dense spectrum.
- **C_i and T are masks**, not the dyadic columns `C_i` of the synthesis and
  report 13 or report 13's tails `T_k`; `I_n = [m_n, 2m_n)` and
  `J_n = [2^n, 2^(n+1))` are blocks of positions, not block codes.
- "Low" means `G' ≡_T ∅'`, not report 13's "low over `∅'`".

No symbol was renamed and no normalization changed.

## What the report claims

Numbers are those of `article.pdf` (and of the delivered PDF).

- **Theorem 1.1 = Theorem 6.2 (+ Corollary 5.4, Proposition 5.5).** If `G`
  is 1-generic with `CA(G)`, neither `[G]_ued` nor `[G]_ned` has an element
  of least Turing degree, even among binary representatives. This holds for
  every 2-generic (Theorem 5.1, proved directly) and every non-high
  1-generic (Corollary 5.4, via the external Theorem 5.2 and Lemma 5.3, "no
  1-generic computes a DNR function"); a 1-generic `G ≤_T ∅'` exists and is
  low (Proposition 5.5).
- **Lemma 3.1, Lemma 3.2, Corollary 3.3.** Computable-null erasure preserves
  the uniform class; a 1-generic's deleted coordinates cannot be predicted
  infinitely often from `G_T`; so a description below `G_T` omits almost all
  of `T`.
- **Theorems 3.4–3.5 (mask lattice).** `G_C ≤_T G_D ⇔ D ⊆* C`;
  `G_C ⊕ G_D ≡_T G_(C∩D)` and `Low(G_C) ∩ Low(G_D) = Low(G_(C∪D))` (an actual
  meet in all Turing degrees); `(Comp ∩ 𝒵₀)/Fin` embeds order-reversingly in
  `Spec_T([G]_ued)`.
- **Lemma 4.1, Lemma 4.3, Theorem 4.4 (budgeted sparse escape).** With
  `CA(G)`, every null `S ≤_T G` is escaped infinitely often by a computable
  one-point-per-block mask obeying any unbounded computable every-prefix
  budget `b`.
- **Theorem 6.1 = 1.2, Corollaries 6.3–6.4, Proposition 6.5.** Local
  avoidance within budget; the countable test family `𝓜_b(G)` has no
  in-class lower bound; no finite coinitial family; bounded budgets cannot
  work.
- **Lemma 7.1, Theorem 7.2.** Uniform null upper bounds; one mask defeats a
  uniformly `G`-computable family of descriptions.
- **Theorem 8.2 = 1.3.** A strictly descending chain `G_0 >_T G_1 >_T …` in
  one uniform class, within budget, with no lower bound in `[G]_ned`; all low
  if `G` is.
- **Corollary 9.1.** Boolean lattices of `2^k` degrees inside `[G]_ued`.
- **Section 10**: twelve research questions (10.1–10.12).

## What the report does not claim

- **Not formalized** (see below). The Python checks test finite coordinate
  and counting invariants only; they do not test genericity, density limits,
  or any degree statement.
- **The source's own non-claims.** The high 1-generic case is open; the
  existence of minimal elements of the full classes is not settled; no
  arbitrary countable coinitial family is excluded (only finite and
  uniformly presented ones); the common lower cone of all computable
  erasures and c.e. counterexamples are open; arbitrary null changes need
  not preserve effective-dense equivalence; there is no uniform algorithm
  extracting masks from oracle descriptions and no effective enumeration of
  the total computable functions (the chain uses a nonuniform listing); the
  chain is not claimed coinitial, and lower bounds outside the class are not
  denied; the strict chain is of Turing degrees, not of effective-dense
  degrees; the low refinement depends on Kjos-Hanssen–Merkle–Stephan
  Theorem 5.1, and only the 2-generic route is self-contained; the
  no-eventually-different-function fact for 2-generics and the high-or-DNR
  characterization are classical; the plan's sketch is **not** completed for
  every 1-generic; the literature search was targeted and priority is not
  established; nothing was refereed.
- **Review at intake.** Lemma 3.2, Theorem 3.5, Lemma 4.3/Theorem 4.4 and
  Theorem 6.2 were read and found sound, the block budget
  `Q_n = (n+1)(n+2)` was recomputed, and the suite was rerun on a copy. That
  is not an independent proof review.

## Programme targets addressed, and what stays open

Line numbers are those of the current tree (identical at the pin).

- **C2** (`research-plan/turing_degrees_unified.tex:563-572`;
  `research-plan/README.md:20-22`;
  `research-synthesis/Turing_Degrees_Synthesis.tex:969`, "None of the
  reports bears on the effective-dense question in general"; plan `:1647`
  lists "C2 along the line of attack" among the first choices). Theorem 6.2
  refutes the universal C2 statement, uniform and nonuniform, for every
  1-generic with `CA`. Of the plan's line of attack (`:570`), step (i) is
  Lemma 3.1 (with 0 in place of 2) and step (ii) is Corollary 3.3; step
  (iii), "the gap", is **bypassed, not proved**: `CA(G)` and Theorem 4.4
  replace the forcing argument. The 1-generics without `CA` are exactly the
  high ones, and for them step (iii) is still open (Question 10.1). So C2 is
  answered negatively (unrefereed), and the gap of the plan's sketch is
  re-scoped to high 1-generics, not closed. The "weaker, still informative
  result" suggested at `:572` is exceeded for these `G`; the positive test
  on the guarded c.e. set suggested there is not attempted; the literature
  audit suggested there was done for Astor–Hirschfeldt–Jockusch and Gerdes
  (bounded).
- **C3** (plan `:574`): not solved; Question 10.11 notes a connection.
- Minimal elements and coinitiality of effective-dense classes: open
  (Questions 10.4, 10.5). The coarse items of the synthesis (`:970-973`) and
  C4–C8 are not addressed.

The plan's C2 entry and the synthesis item `:969` are not edited here (see
"REPOSITORY_UPDATE.md" above).

## Relation to the Lean library

Nothing in this report is formalized. The Lean library `CoarseDegrees`
(`Computability/TuringDegrees/Lean/CoarseDegrees`) formalizes coarse
descriptions only: it has no `⊥`-valued descriptions, no effective-dense
reducibilities, no eventually different or DNR functions, no highness and
no jump operator. The report relies on none of its eight admitted
statements. The shared basics: the library's `OneGeneric`
(`Computability/TuringDegrees/Lean/CoarseDegrees/Sets.lean:136`) has the
definition of 1-genericity used here, and `exists_oneGeneric`
(`Generic.lean:122`) proves that 1-generic sets exist, without the bound
`G ≤_T ∅'` of Proposition 5.5. Theorem 5.2 (Kjos-Hanssen–Merkle–Stephan)
has no Lean statement. Question 10.12 and Section 11.2 are a formalization
plan; no Lean or Rocq code was delivered or is shipped.

## Relation to the other reports

Round 2 (batch 37) filed four reports; the other three, `../11`, `../12`
and `../13`, are about coarse cores (C4, C6) and share no theorem with this
one. Report 13 also declines to transfer its coarse construction to the
effective-dense case (its Section 8.4 and Question 10.8). The synthesis's
positive effective-dense examples (dyadic codes have least effective-dense
degrees) are the comparison family of Question 10.7.

## Build

From a scratch copy of the directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

pdfLaTeX with lmodern, AMS, mathtools, microtype, booktabs, tabularx,
longtable, xcolor, enumitem, fancyhdr, titlesec, xurl, hyperref and
bookmark; no bibliography processor. The build of `article.pdf` has no
errors, undefined references or citations, multiply defined labels,
duplicate destinations, or overfull or underfull boxes. The delivered
`code/build.sh` changes to its own directory, runs
`python3 checks/check_finite.py > checks/run.txt`, compiles `article.tex`
there and copies the result to `article.pdf`; it fails in the shipped
layout and must not be run in place.

## Rerunning the finite checks

The script writes `results.json` next to itself and prints the same text,
so never run it in place (it would add `code/results.json`). On a copy:

    mkdir <scratch>; cp code/check_finite.py <scratch>/
    cd <scratch>; py check_finite.py > run.txt
    # compare results.json with data/results.json, run.txt with data/run.txt

Python 3.10 or later, standard library only. At intake the copy run passed
(exit 0), and both outputs equal the recorded files apart from line
endings.

## Discrepancies in the delivered files

- `data/run.txt` duplicates `data/results.json` byte for byte (the script
  prints what it writes).
- Section 11.3 of the article and `code/build.sh` use the delivery paths
  `checks/check_finite.py`, `checks/results.json`, `checks/run.txt` and say
  the archive contains the final PDF; a `[write]` note in Section 11.3 gives
  the shipped names. `PROOF_AUDIT.md`, `SOURCES.md` and
  `REPOSITORY_UPDATE.md` name no shipped file.
- The subsection title "The repository gap, resolved at the required
  quantifier level" (9.2) is qualified by the manuscript's own last sentence
  there and by a `[write]` note: the gap is bypassed for 1-generics with
  `CA`, not closed for all 1-generics.
- The delivered source's title page produced a duplicate PDF destination;
  fixed as described under "Labels and numbering".
