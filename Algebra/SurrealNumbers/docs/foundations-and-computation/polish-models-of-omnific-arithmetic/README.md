# Polish Models of Omnific Arithmetic

**Polish Presburger models for Glazer's Question 2, and Borel presentations and support barriers**

Merged research report, 3 October 2026, built from three manuscripts written
independently on that day in answer to one research brief: Elliot Glazer's
*A Topological Tennenbaum Theorem* (arXiv:2311.13699) meets the repository's
omnific arithmetic. They are manuscripts 03, 04 and 05 of batch 86, which
arrived in `31fdc6571` and were placed in `3d2177df4`.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| **05** (base) | batch 86, manuscript 05: *Polish Presburger Arithmetic inside the Omnific Integers: An affirmative construction for Glazer's Question 2, effective Baire-space models, and structural obstructions* (24 pages, A4) | `polish_presburger_glazer` | `a11efab09` | `3d2177df4` | Part I, unmarked text (Sections 2–15), Appendix A |
| 04 | batch 86, manuscript 04: *Polish Presburger Arithmetic: A positive construction for Glazer's question, an effective Baire-space model, and exact regularity boundaries* (25 pages, letter) | `Polish_Presburger_Glazer_ProveIt` | `3ad5f878c` | `3d2177df4` | Part I, every passage marked [04]; Appendices B, C |
| 03 | batch 86, manuscript 03: *Borel Presentations and Support Barriers in Omnific Arithmetic: Scattered exponent orders, Hahn fields, and the exact discontinuities of finite normal forms* (23 pages, letter) | `glazer_proveit_research` | `c5b4881fa` | `3d2177df4` | Part II (Sections 16–29), Appendix D |

The pins are 35, 31 and 28 commits before the placement; every repository
file the sources inspected is unchanged between its pin and the placement.

**Status.** All three sources are AI-assisted (03: "prepared with ChatGPT"),
unrefereed research drafts. **Nothing in this report is formalized**, and
priority of its main result is **not established**.

## Files

```
article.tex                                   the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf                                   the compiled report, 81 pages (unnumbered title page, then pages 1-80)
README.md                                     this guide
05-omnific-presburger-CLAIM_LEDGER.md         05's claim ledger, as delivered (05's own theorem numbers)
05-omnific-presburger-SOURCES.md              05's sources and priority record, as delivered
08-local-compactness-proof_audit.md           placed in 0bd0e5527 for Part IV; not yet written into the report
08-local-compactness-sources.md               placed in 0bd0e5527 for Part IV; not yet written into the report
09-hahn-polishability-SOURCES.md              placed in 0bd0e5527 for Part V; not yet written into the report
code/
  03-borel-presentations-verify.py            03: exact-rational checks (84,388 assertions), stdlib only
  04-polish-presburger-Makefile               04: delivered Makefile (names delivery paths)
  04-polish-presburger-verification.py        04: exact checks (75,079 assertions) and the Baire stream API, stdlib only
  05-omnific-presburger-build.sh              05: delivered three-pass build (names polish_presburger_glazer.tex)
  05-omnific-presburger-polish_presburger.py  05: finite-rank arithmetic and the Baire codec
  05-omnific-presburger-verify.py             05: checks (17,930); imports polish_presburger by its delivery name
  08-local-compactness-build.sh               placed in 0bd0e5527 for Part IV
  08-local-compactness-verify.py              placed in 0bd0e5527 for Part IV
  09-hahn-polishability-build.sh              placed in 0bd0e5527 for Part V
  09-hahn-polishability-verify.py             placed in 0bd0e5527 for Part V
data/
  03-borel-presentations-provenance.json      03's pin, inspected paths, theorem locations, PDF and test record
  03-borel-presentations-verification.json    recorded run of 03's checks
  04-polish-presburger-source_provenance.json 04's pin, inspected files with blob hashes, literature, proof status
  04-polish-presburger-verification_results.json  recorded run of 04's checks
  05-omnific-presburger-verification_results.json recorded run of 05's checks
  08-local-compactness-verification_results.json  placed in 0bd0e5527 for Part IV
  09-hahn-polishability-verification.json     placed in 0bd0e5527 for Part V
```

Every delivered file of sources 03, 04 and 05 is byte-identical to the
delivery. Not shipped (they survive in the archives of `31fdc6571`): the three
delivered PDFs, the three checksum manifests (all verified at placement), and
the manuscripts and READMEs of 03 and 04, which are merged into `article.tex`.

**Further manuscripts placed here.** Commit `0bd0e5527` (batch 86C) assigned
five later manuscripts to this report: 06 and 07 (continuous Presburger
arithmetic) to a Part III (labels `pma:cp:`, no staged files), 08 (local
compactness) to a Part IV (`pma:lc:`), and 09 (Polishability at the
Hahn–Puiseux–Levi-Civita boundary) to a Part V (`pma:ser:`). Their staged
files are listed above. **They are not part of the present text**, which has
only Parts I and II; this README describes those two parts.

## Labels

Every label carries the prefix `pma:`. Part I (05 and 04) uses `pma:pr:`,
Part II (03) `pma:bor:`, and text written for the merge bare `pma:`
(for example `pma:sec:boundary`, `pma:prop:stratum`). The report has 199
labels: all 60 of 05 (`thm:main` is `pma:pr:thm:main`), all 50 of 03
(`thm:glazer` is `pma:bor:thm:glazer`), 60 of 04's 67, and 29 new. Ten labels of
04 coincide with labels of 05; they take the sub-prefix `pma:pr:s04:`
(`pma:pr:s04:thm:qe`, `pma:pr:s04:thm:baire`, and six section labels), except
`eq:cone` and `eq:division`, whose displays are identical to 05's and are
printed once under 05's labels. Four further displays of 04 (`eq:divisionformula`,
`eq:monuslocus`, `eq:surrealR`, `eq:surrealQ`) are printed once as 05's, and
04's Definition 2.1 (`def:split`) is 05's setup. Where 04 states a theorem
that 05 also states, 04's label is a second label of 05's statement (for
example `pma:pr:thm:monuslocus` is Theorem 8.3). The staged text was 05's
manuscript with bare labels (60).

The delivered records number results in their own manuscripts. Part I's
sections are 05's plus one (05's Section k is Section k+1); numbers inside a
section change because 04's statements are interleaved:

| 05 (`05-omnific-presburger-CLAIM_LEDGER.md`) | here | 03 (`data/03-borel-presentations-provenance.json`) | here |
|---|---|---|---|
| Theorem 2.1 | Theorem 3.1 | Theorem 3.4 | Theorem 18.4 |
| Prop. 3.2; Lemma 3.4; Thm 3.5; Cor. 3.6; Prop. 3.7 | 4.2; 4.7; 4.9; 4.11; 4.12 | Theorem 4.1 | Theorem 19.1 |
| Lemma 4.1; Theorem 4.2; Section 4.2 | 5.1; 5.2; Section 5.3 | Theorem 5.2 | Theorem 20.2 |
| Theorems 5.1, 5.2 | 6.1, 6.2 | Theorem 6.2 | Theorem 21.2 |
| Theorems 6.1, 6.2, 6.3 | 7.1, 7.3, 7.4 | Theorem 7.1 | Theorem 22.1 |
| Props. 7.1, 7.2; Theorem 7.3 | 8.1, 8.2; 8.3 | Theorem 8.2 | Theorem 23.2 |
| Theorem 8.1 | 9.1 | Theorem 9.3 | Theorem 24.3 |
| Theorem 9.2; Cor. 9.3 | 10.4; 10.5 | Theorem 10.2 | Theorem 25.2 |
| Theorems 10.1, 10.2, 10.3 | 11.1, 11.2, 11.7 | Appendix A | Appendix D |
| Lemma 11.1; Cor. 11.2 | 12.1; 12.2 | | |
| Sections 12, 13; Appendix A | Sections 13, 14; Appendix A | | |

## Glazer's question, his speculation, and priority

Glazer's Question 2 (p. 8) asks whether some uncountable Polish space
supports a model of Presburger arithmetic with continuous addition. Part I
answers it **as printed** affirmatively. Immediately after the question
Glazer writes that he speculates that an affirmative answer to his Question 1
(is his Theorem 2 provable in ATR₀?) "would lead to a negative answer to
Question 2". Neither 04 nor 05 mentions this; the report quotes it (Section
1.1) and explains the difference: the affirmative models have every
definable relation Borel (Δ⁰₂), admit no semiring multiplication at all, and
sit inside 03's ring, where Glazer's Corollary 1 does forbid continuous
addition. The report draws no conclusion about Question 1, and does not know
whether Glazer intended a further hypothesis. **Priority is not
established**: 05 searched and found no earlier answer without excluding one,
04 says historical priority has not been established, and on 3 October 2026
the arXiv record still had one version (v1) and no journal reference.

## What the report claims

**Part I** (05, with 04). The cone `M_R = (R_{>0} × Z) ∪ ({0} × N)` of the
lexicographic group `R ×→ Z` (real coordinate dominant, unit `(0,1)`), with the
usual topology on `R` and the discrete one on `Z`, is an uncountable, perfect,
locally compact Polish model of `Th(N;0,1,+,<)` with continuous addition
(Theorem 3.1; 04's statement Remark 3.2). Its full theory follows from
quantifier elimination for Z-groups, proved again with the coset-invariant
finite search (Lemma 4.7, 04's Theorem 4.8) that replaces the one-step
periodicity of integer proofs (Example 4.4, 04's Proposition 4.6). For a
divisible `D` with a Polish group topology, `M_D` is Polish iff `D_{>0}` is
G_δ (Theorem 5.2); under 04's stronger admissibility hypothesis, division by
standard integers is continuous too (Theorem 5.4). With `D = Q^N` (discrete
coordinates, lexicographic) the model is homeomorphic to Baire space, with
Type-2 computable addition, successor and division (Theorems 6.1, 6.2; 04's
charts in Section 6.3). Every definable relation is Δ⁰₂, with a computable
mind-change bound in the Baire model (Theorems 7.1, 7.3); an open or closed
order forces discreteness under continuous successor (Theorem 7.4, 05), and a
closed order forces discreteness in any Hausdorff model (Theorem 7.5, 04),
so continuous truncated subtraction forces countability. Predecessor and
truncated subtraction are discontinuous exactly at `0` and on an explicit
closed nowhere dense locus (Proposition 8.2, Theorem 8.3); no
translation-invariant complete metric exists (Proposition 8.4, 04). Both
models embed additively in `Oz` as `rω + n` and `Σ a_j ω^{1/(j+1)} + n`
(Theorem 9.1). No unital semiring multiplication exists on either
(Theorem 10.4); 04's Laurent model `M_L` has no cofinal infinite element yet
also no semiring expansion, by a growth-order obstruction (Proposition 10.6,
Corollary 10.8). Unital additive maps reduce to the divisible part
(Proposition 11.3, 04); the real model's endomorphisms are the positive
dilations and its elementary submodels are the `M_E` for Q-subspaces `E`,
only two of them Polish (Theorems 11.1, 11.2); the self-embeddings of the
Baire model are the row-finite matrices with increasing positive pivots, all
automatically continuous (Theorem 11.4, Corollary 11.5, 04), with proper
clopen elementary self-copies (Theorem 11.7). No compact Hausdorff model
has continuous addition (Corollary 12.2).

**Part II** (03). For a countable linear order `L`, `WO(L)` is Borel iff `L`
is scattered, else Π¹₁-complete (Theorem 18.4); `WO(Z)` is Σ⁰₂-complete and
`WO(Z^d_lex)` Π⁰₃-complete for `d ≥ 2` (Theorem 19.1); `R((t^Γ))` has a
coefficient-observable standard Borel parametrization iff `Γ` is scattered,
with Borel field operations on that side (Theorem 20.2), so a nontrivial
square-root-closed full Hahn field is on the non-Borel side (Corollary 20.4);
every Borel observable family has a countable support bound (Theorem 21.2);
the obstruction already occurs for 0–1 codes in `[X,2X)` (Theorem 22.1). The
finite principal-part ring `A_fin` is an integer part of the Puiseux field
(Lemma 23.1), its cone satisfies `Q + IOpen` (Theorem 23.2), addition and
multiplication are continuous off explicit closed nowhere dense cancellation
loci of a Polish presentation (Theorem 24.3), and no Borel-compatible Polish
recoding makes addition continuous (Theorem 25.2, from Glazer's Corollary 1).

**Merge** (Section 26). `M_R` is the clopen stratum `{n + aX}` of 03's cone,
on which addition is continuous also for 03's topology; that topology agrees
with `M_R`'s off the standard numerals and isolates them (Proposition 26.1).
The Baire model lies in 03's rational Hahn ring and is a coefficient-observable
family with support types at most `ω + 1`, consistent with Theorem 21.2.

## What the report does not claim

Appendix F keeps every limitation, source by source (05: 9 items, 04: 8,
03: 9, merge: 4). In short: no priority; no answer to Glazer's Question 1, and
no conclusion about variants of Question 2 with further hypotheses; no model of
PA, no continuous order, no ring embedding into `Oz`, no canonical topology on
`Oz`; classical Z-group elimination, Hausdorff's characterization,
analytic boundedness and Shepherdson-type models are not claimed as new;
Glazer's multiplication obstruction (his Theorem 2) is not transferred to
03's ring; the full-Hahn results need observable coefficients; the finite
checks are finite. Part I has 17 questions (four asked by both 04 and 05,
merged in Section 14.1) and Part II 8; all are open.

## Printed by citation, not reprinted as new

All labels exist at HEAD and at the three pins.

- `exr:prop:division` (exponential-relations-over-omnific-integers): `Oz` is a
  Z-group, hence a Presburger model; Part I reproves the classical facts for
  the split groups.
- `isg:cf:main:presburger` (discrete-initial-subgroups-and-omnific-normalization):
  a set-sized Z-group has an initial realization in `Oz` iff it splits as
  `G^dv ×→ Z`; Part I's groups split, so it applies to them (Section 1.4).
- `onot:neg:lem:kbtree`, `onot:neg:thm:pionesone`, `onot:neg:rem:secondroute`
  (omnific-notations): the lightface Π¹₁ results of which Lemma 18.2 and
  Theorem 22.1 are boldface counterparts (notes after them).
- `odg:thm:floor` (omnific-diophantine-geometry), **proved in Lean** for every
  surreal (`omnificFloor_spec`, `existsUnique_omnific_integerPart`,
  `omnificFloor_of_integer_negative_tail` in
  `Algebra/SurrealNumbers/Surreal/Foundations/OmnificFloor.lean`): Lemma 23.1
  is its restriction to the Puiseux field; the lemma as stated is not
  formalized.
- `dsn:cor:openinduction` (definable-surreals-and-omnific-integers) and the
  Shepherdson paragraph of omnific-diophantine-geometry: the route of
  Theorem 23.2. Pending in `docs/FORMALIZATION.md`.

## Corrections and stale statements

- The placement record (`3d2177df4`) and the intake dossier said that 03's
  topology restricts on the real stratum to the topology of 04 and 05. It
  agrees with it off the standard numerals and isolates the numerals
  (Proposition 26.1(iii)); both make addition continuous there, so the
  placement's conclusion stands.
- 03 cites Alvir–Rossegger only as arXiv:1810.11423; its journal version
  (J. Symb. Log. 85 (2020), 1079–1101) is added. Paran–Vo's issue number (no. 2)
  is added. No source statement was found false.
- The sources' statements that the repository has no result on these
  subjects were true at their pins; nothing was added before the placement.

## Relations to the formal project and to neighbouring reports

- **`Logic/PresburgerArithmetic`** (formal project; it gets a pointer at
  catalogue time). Its Lean `Cooper.lean` (`periodic_shift_of_mod`,
  `periodic_interval`, `periodic_has_residue`, `periodic_unbounded_above`,
  `periodic_unbounded_below`, `cooper_finite_criterion`, namespace
  `PresburgerArithmetic`), its decision procedure
  `PresburgerArithmetic.Formula.presburgerArithmetic_decidable` with
  `Formula.decideSentence_eq_true_iff`, and its Rocq `Cooper.v` (`periodic`,
  `periodic_shift`, `periodic_has_residue`, `periodic_interval`,
  `cooper_finite_criterion`, `cooper_step_decidable`) are about the ordinary
  integers and correct there. 05 read the Lean file, 04 the Rocq file; both
  show that the one-step periodicity hypothesis cannot be carried verbatim to
  nonstandard Z-groups and give the coset-invariant replacement (Section 13.5).
  This is a porting requirement, not a defect. **Placement beside a formal
  project confers no formal status: no statement of this report is
  formalized**, and `docs/FORMALIZATION.md` maps none of its labels.
- [`omnific-notations`](../omnific-notations/): Part II's Lemma 18.2 and
  Theorem 22.1 are boldface counterparts of its Π¹₁ validity results; 03
  answers none of its named questions.
- [`exponential-relations-over-omnific-integers`](../exponential-relations-over-omnific-integers/):
  the collection's other Presburger report (`Oz` as a Presburger group).
- [`discrete-initial-subgroups-and-omnific-normalization`](../../surreal/discrete-initial-subgroups-and-omnific-normalization/):
  split Z-groups and initial realizations (`isg:cf:main:presburger`).
- [`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/)
  and [`omnific-diophantine-geometry`](../../surreal/omnific-diophantine-geometry/):
  open induction and the floor.
- [`surreal-well-orders`](../surreal-well-orders/): its `WO_μ(X)` (well-orderings
  of type μ) is a different object from 03's `WO(L)` (well-ordered subsets).

## Notation

Section 1.3 has the full table. Renamed: 04's `G(D)`, `M(D)`, `D_ω`, `M_ω`,
`⊕_lex` are 05's `G_D`, `M_D`, `D_B`, `M_B`, `×→` (the same objects); 04's
Baire homeomorphism `H` (charts `H_≥`, `H_>`) and integer code `h` are `Ψ`,
`Ψ_≥`, `Ψ_>`, `ζ`; 03's ring `𝒜`, cone `𝒜_{≥0}`, rational Hahn ring `H`,
Kleene–Brouwer embedding `h` and two local sets `D` are `A_fin`, `A_fin,≥0`,
`H_Q`, `μ_KB`, `W` and `𝒵`. Both `\B` macros (04: Baire space; 03: unused
`𝓑`) are replaced by `N^N`. No normalization changed.

## Delivered files that use delivery names

- `05-omnific-presburger-CLAIM_LEDGER.md` refers to
  `polish_presburger_glazer.pdf` and its source, and to 05's own numbering
  (table above); `05-omnific-presburger-SOURCES.md` describes 05's PDF build.
- `code/05-omnific-presburger-verify.py` imports `polish_presburger` and
  writes `verification_results.json` next to itself; its docstring names
  `polish_presburger_glazer.tex`. `code/05-omnific-presburger-build.sh` builds
  `polish_presburger_glazer.tex` in its own directory.
- `code/04-polish-presburger-Makefile` names `polish_presburger.tex`,
  `verification.py` and `verification_results.json`; 04's program writes
  `verification_results.json` in the working directory unless `--output` is
  given.
- `data/03-borel-presentations-provenance.json` describes 03's own 23-page
  PDF and its numbering; `data/04-polish-presburger-source_provenance.json`
  refers to `verification_results.json`.
- The source texts merged into `article.tex` give their delivery names in
  their reproduction boxes; notes after each give the shipped names.

## Build

From a copy in a scratch directory:

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with `newpxtext`/`newpxmath`, `tcolorbox`, `cleveref`, `aliascnt`.
The build has no errors, no LaTeX, package or hyperref warnings, no overfull
or underfull boxes, no undefined or multiply defined references and no
duplicate destinations; 81 pages. Commit only `article.pdf`, not the
auxiliary files.

## Rerunning the finite checks

All three programs need only Python 3.10+ and the standard library. Run them
**on a copy** with the delivery names restored, never in this directory (05's
runner writes beside itself, 04's into the working directory):

```
D=/path/to/this/report; S=/path/to/scratch     # a fresh directory
mkdir -p $S/03 $S/04 $S/05
cp $D/code/05-omnific-presburger-polish_presburger.py $S/05/polish_presburger.py
cp $D/code/05-omnific-presburger-verify.py            $S/05/verify.py
cp $D/code/04-polish-presburger-verification.py       $S/04/verification.py
cp $D/code/03-borel-presentations-verify.py           $S/03/verify.py
cd $S
python 05/verify.py                                   # writes 05/verification_results.json
python 04/verification.py --output 04/verification_results.json
python 03/verify.py --output 03/verification.json
```

Tested for this report with Python 3.14.4 on Windows (2, 9 and 6 seconds):
05 reports `"status": "PASS"` and 17,930 checks in 18 families; 04
`"status": "passed"` and 75,079 assertions in 13 categories; 03
`"status": "PASS"` and 84,388 assertions in 11 groups. The new records equal
the shipped ones except for the interpreter version (05, 03) and, on
Windows, CRLF line endings. 04's stream API (`from verification import
Stream, baire_add, ...`) works from `$S/04`. The checks verify finite
instances and stream prefixes only; Polishness, induction, completeness and
the descriptive-set-theoretic theorems are proved in the text.

## Provenance

Appendix E. The merge printed 05's text as the base; printed each shared
result once, crediting both sources, with 04's genuinely different proofs as
marked second proofs (Propositions 4.2, 8.2, Lemma 4.7 via Theorem 4.8,
Theorems 4.9, 6.1, 7.1, 8.3, 10.4, 11.1); printed both of the incomparable
order obstructions (Theorems 7.4 and 7.5, Remark 7.7); merged four questions;
and added Glazer's speculation, the stratum proposition (26.1) and the notes
citing the collection. Citation details checked on 3 October 2026: Glazer's
arXiv record; Tserunyan's notes (dated November 26, 2025); Paran–Vo, Israel
J. Math. 273 (2026), no. 2, 979–1000 (online 11 December 2025);
Enayat–Hamkins–Wcisło, Fund. Math. 256 (2022), 171–193; Jeřábek, MLQ 65 (2019),
108–115; Haase, ACM SIGLOG News 5(3) (2018), 67–82; Alvir–Rossegger, J. Symb.
Log. 85 (2020). The other classical references were not re-checked.
