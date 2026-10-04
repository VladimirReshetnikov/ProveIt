# Polish Models of Omnific Arithmetic

**Polish Presburger models for Glazer's Question 2, Borel presentations and support barriers, continuous Presburger arithmetic, local compactness, and Polish series fields**

Merged research report, built from seven manuscripts dated 3 and 4 October
2026 on one subject: Elliot Glazer's *A Topological Tennenbaum Theorem*
(arXiv:2311.13699) meets the repository's omnific arithmetic. They are
manuscripts 03 to 09 of batch 86. Manuscripts 03, 04 and 05 arrived in
`31fdc6571` and were placed in `3d2177df4` (Parts I and II); manuscripts 06,
07, 08 and 09 arrived in `fb8414869` and were placed in `0bd0e5527` (Parts III
to V).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| **05** (base of Part I) | batch 86, manuscript 05: *Polish Presburger Arithmetic inside the Omnific Integers: An affirmative construction for Glazer's Question 2, effective Baire-space models, and structural obstructions* (24 pages, A4) | `polish_presburger_glazer` | `a11efab09` | `3d2177df4` | Part I, unmarked text (Sections 2–15), Appendix A |
| 04 | batch 86, manuscript 04: *Polish Presburger Arithmetic: A positive construction for Glazer's question, an effective Baire-space model, and exact regularity boundaries* (25 pages, letter) | `Polish_Presburger_Glazer_ProveIt` | `3ad5f878c` | `3d2177df4` | Part I, every passage marked [04]; Appendices B, C |
| 03 | batch 86, manuscript 03: *Borel Presentations and Support Barriers in Omnific Arithmetic: Scattered exponent orders, Hahn fields, and the exact discontinuities of finite normal forms* (23 pages, letter) | `glazer_proveit_research` | `c5b4881fa` | `3d2177df4` | Part II (Sections 16–29), Appendix D |
| **07** (base of Part III) | batch 86, manuscript 07: *Continuous Presburger Arithmetic on Polish Spaces: An affirmative construction for Glazer's question, Baire-space models, and omnific realizations* (27 pages, letter; dated 4 October) | `polish_presburger_research` | `0f95145cb` | `0bd0e5527` | Part III, unmarked text (Sections 30–43), Appendices G, H |
| 06 | batch 86, manuscript 06: *Continuous Presburger Arithmetic on Polish Spaces: Lexicographic models, an isolated-zero obstruction, and a boundary between additive and semiring arithmetic* (21 pages, letter) | `polish_presburger_article` | `fa2f3e419` | `0bd0e5527` | Part III, every passage marked [06] (Sections 38 and 39 entirely); Appendices I, J |
| 08 | batch 86, manuscript 08: *Local Compactness Forces Arithmetic Rigidity: Borel ordered groups, Presburger models, and multiplication without regularity assumptions* (23 pages, A4) | `glazer_proveit_local_compactness` | `883e0b3b2` | `0bd0e5527` | Part IV (Sections 44–58), Appendix K |
| 09 | batch 86, manuscript 09: *Polishability at the Hahn–Puiseux–Levi-Civita Boundary: Automatic order bounds, local Polish hulls, and countable omnific integer parts* (30 pages, letter) | `Polish_Hahn_Puiseux_Levi_Civita_Research` | `4af956fe0` | `0bd0e5527` | Part V (Sections 59–74), Appendices L, M |

The pins of 03–05 are 28 to 35 commits before `3d2177df4`, those of 06–09 33
to 43 commits before `0bd0e5527`; every repository file a source inspected is
unchanged between its pin and the placement. Manuscripts 06 and 07 have the
same title but are independent texts (at most 0.74% shared word 8-grams among
manuscripts 03–10). Manuscript 10 of the same arrival (the standard cut in one
infinite interval) was written into
[`discrete-initial-subgroups-and-omnific-normalization`](../../surreal/discrete-initial-subgroups-and-omnific-normalization/).

**Status.** Unrefereed research drafts: 03 and 08 "prepared with ChatGPT",
09 "prepared with AI assistance", 05 "AI-assisted"; 04, 06 and 07 describe
themselves as research reports prepared for Vladimir Reshetnikov. **Nothing
in this report is formalized**, and priority of its results is **not
established**.

## Files

```
article.tex                                   the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf                                   the compiled report, 191 pages (unnumbered title page, then pages 1-190)
README.md                                     this guide
05-omnific-presburger-CLAIM_LEDGER.md         05's claim ledger, as delivered (05's own theorem numbers)
05-omnific-presburger-SOURCES.md              05's sources and priority record, as delivered
08-local-compactness-proof_audit.md           08's proof audit and dependency map, as delivered
08-local-compactness-sources.md               08's source provenance and scope of inspection, as delivered
09-hahn-polishability-SOURCES.md              09's source record and audit limits, as delivered
code/
  03-borel-presentations-verify.py            03: exact-rational checks (84,388 assertions), stdlib only
  04-polish-presburger-Makefile               04: delivered Makefile (names delivery paths)
  04-polish-presburger-verification.py        04: exact checks (75,079 assertions) and the Baire stream API, stdlib only
  05-omnific-presburger-build.sh              05: delivered three-pass build (names polish_presburger_glazer.tex)
  05-omnific-presburger-polish_presburger.py  05: finite-rank arithmetic and the Baire codec
  05-omnific-presburger-verify.py             05: checks (17,930); imports polish_presburger by its delivery name
  08-local-compactness-build.sh               08: delivered build (latexmk article.tex, then verify.py), names delivery paths
  08-local-compactness-verify.py              08: exact checks (24,470 cases), stdlib only
  09-hahn-polishability-build.sh              09: delivered build (three pdflatex passes, then verify.py), names delivery paths
  09-hahn-polishability-verify.py             09: exact checks (20,116 assertions, seed 20261003), stdlib only
data/
  03-borel-presentations-provenance.json      03's pin, inspected paths, theorem locations, PDF and test record
  03-borel-presentations-verification.json    recorded run of 03's checks
  04-polish-presburger-source_provenance.json 04's pin, inspected files with blob hashes, literature, proof status
  04-polish-presburger-verification_results.json  recorded run of 04's checks
  05-omnific-presburger-verification_results.json recorded run of 05's checks
  08-local-compactness-verification_results.json  recorded run of 08's checks
  09-hahn-polishability-verification.json     recorded run of 09's checks
```

Every delivered file is byte-identical to the delivery. Not shipped (they
survive in the archives of `31fdc6571` and `fb8414869`): the seven delivered
PDFs, the checksum manifests of 03, 04, 05 and 08 (all verified at placement;
06, 07 and 09 shipped none), the manuscripts of 03, 04, 06, 07, 08 and 09 (all
merged into `article.tex`; 05's was the staged base), and the delivery READMEs
of 03, 04, 06, 07, 08 and 09. Sources 06 and 07 shipped no code or data.

## Labels

Every label carries the prefix `pma:`. Part I (05 and 04) uses `pma:pr:`,
Part II (03) `pma:bor:`, Part III (07 and 06) `pma:cp:`, Part IV (08)
`pma:lc:`, Part V (09) `pma:ser:`, and text written for the merge bare `pma:`
or a part prefix (for example `pma:sec:boundary`, `pma:prop:stratum`,
`pma:cp:sec:meet`, `pma:cp:prop:meet`). The report has 422 labels: the 199 of
the Parts I–II write (all kept), all 49 of 07, all 40 of 06, all 56 of 08,
all 70 of 09, and 8 new (three part labels, `pma:cp:sec:meet`,
`pma:cp:prop:meet`, and `pma:lc:q:removelc`, `pma:lc:q:completion`,
`pma:ser:q:cones` added to unlabelled questions so that notes can cite them).

In Part I, ten labels of 04 that coincide with labels of 05 take the
sub-prefix `pma:pr:s04:` (`pma:pr:s04:thm:qe`, `pma:pr:s04:thm:baire`, and six
section labels), except `eq:cone` and `eq:division`, whose displays are
identical to 05's and are printed once under 05's labels. Four further
displays of 04 (`eq:divisionformula`, `eq:monuslocus`, `eq:surrealR`,
`eq:surrealQ`) are printed once as 05's, and 04's Definition 2.1
(`def:split`) is 05's setup. Where 04 states a theorem that 05 also states,
04's label is a second label of 05's statement (for example
`pma:pr:thm:monuslocus` is Theorem 8.3). In Part III, the six labels of 06
that coincide with labels of 07 (`eq:realmodel`, `sec:baire`, `sec:real`,
`thm:baire`, `thm:continuum`, `thm:real`) take the sub-prefix `pma:cp:s06:`.

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

In Parts III–V, 07's Section k is Section 29+k, 08's Section k is Section
43+k, and 09's Section k is Section 58+k; 06's Sections 1–6 and 9 are
subsections of 07's Sections 1, 2, 3, 6, 6, 8 and 9 (30.4, 31.3, 32.3,
35.5, 35.6, 37.5, 40.4), and its Sections 7 and 8 are Sections 38 and 39.
Statement numbers inside a section change where statements are interleaved
(in Section 35, 06's Theorem 5.1 is 35.8); questions now share the theorem
counter. The appendices of 07 (A, B), 06 (A, B), 08 (A) and 09 (A, B) are
Appendices G, H, I, J, K, L and M. The delivered records of 08 and 09 cite
no theorem numbers.

## Glazer's question, his speculation, and priority

Glazer's Question 2 (p. 8) asks whether some uncountable Polish space
supports a model of Presburger arithmetic with continuous addition. Part I
answers it **as printed** affirmatively, and 06 and 07 prove the same again
(Theorems 32.1, 32.2). Immediately after the question Glazer writes that he
speculates that an affirmative answer to his Question 1 (is his Theorem 2
provable in ATR₀?) "would lead to a negative answer to Question 2". None of
the seven sources quotes this; the report does (Section 1.1) and explains the
difference: the affirmative models have every definable relation Borel (Δ⁰₂),
admit no semiring multiplication at all, and sit inside 03's ring, where
Glazer's Corollary 1 does forbid continuous addition. For Parts III–V it adds
that 07 comes closest (its remark after Question 43.1: the affirmative
construction blocks a route to a *negative* answer to Question 2 as stated,
so only a variant with further hypotheses could carry the speculation), that
06's isolated-zero theorem (39.1) removes a hypothesis from Glazer's
Theorem 1 (PA weakened to PA⁻) and does not bear on Question 1, and that 08
and 09 concern rings and answer neither question. The report draws no
conclusion about Question 1. **Priority is not established** for any source;
on 3 October 2026 the arXiv record still had one version (v1) and no journal
reference.

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

**Merge of Parts I and II** (Section 26). `M_R` is the clopen stratum
`{n + aX}` of 03's cone, on which addition is continuous also for 03's
topology; that topology agrees with `M_R`'s off the standard numerals and
isolates them (Proposition 26.1). The Baire model lies in 03's rational Hahn
ring and is a coefficient-observable family with support types at most
`ω + 1`, consistent with Theorem 21.2.

**Part III** (07, with 06). A translation-invariant order with Borel positive
cone on a Polish abelian group has Δ⁰₂ sign cones and a countable chain of
closed convex subgroups (Theorem 33.1); the cone closure rank takes every
countable value (Proposition 33.4). Hence (merge note) for a divisible Polish
`D`, `M_D` is Polish iff `D_{>0}` is Borel iff it is Δ⁰₂, and every divisible
Polish `A` with Borel cone gives a Polish model `M_A` with continuous
addition, standard division and partial subtraction and Δ⁰₂ definable
relations (Theorem 34.1); in every Polish Presburger presentation with
continuous addition, definable relations and functions are Borel
(Proposition 34.3). For countably infinite α, `M_α = (Q^α ×→ Z)_{≥0}` is
homeomorphic to Baire space (Theorem 35.1) with Archimedean classes of type
α+1, giving ℵ₁ nonisomorphic models (Theorem 35.4; 06's Theorem 35.9); there
are exactly 2^ℵ₀ isomorphism types on Baire space (07's Theorem 35.5 with
Δ⁰₂ relations and continuous division; 06's Theorem 35.8 with topology,
order, 0 and 1 fixed). The formula `x < p` has boundary oscillation rank
exactly β+1 in `M_α`, α = ω·β + n (Theorem 36.1), with continuum many models
at each rank (Corollary 36.2). `min`, `max` and monus are each discontinuous
(Corollary 37.2); a second Polish topology on `M_R`, isolating exactly the
standard numerals, makes successor and truncated predecessor continuous
(Proposition 37.4). 06 shows that the multiplicative unit of any unital
semiring on a Presburger monoid is forced (Lemma 37.9, Theorem 37.10); that
the cone of `Z + tR[t]` (`t` positive infinite) with the degree and constant
topology is an uncountable locally compact Polish model of Presburger
arithmetic and of PA⁻ with continuous addition and multiplication
(Theorem 38.1) that fails open induction at `x² < t` (Theorem 38.2); and that
in every Polish topological cone of a discretely ordered ring with continuous
addition and multiplication `0` is isolated, so no perfect Polish space
carries such a PA⁻ model (Theorem 39.1, Corollary 39.2). The omnific
realization extends to every countably infinite α (Theorem 40.1).
Theorems 32.1, 32.2, 35.6, 35.7, 37.7, Propositions 37.1, 37.3, 37.5 and
Appendices G and I repeat Part I's results, each flagged in its title.

**Merge in Part III** (Section 42). The degree-≤1 part of 06's cone, 07's
second topology on `M_R` and Part II's stratum (Proposition 26.1) are one
space; 06's topology on its cone is strictly coarser than 03's and makes
addition continuous where 03's does not (Proposition 42.1). So inside 03's
ring the integer-exponent subcone, which fails open induction, carries a
Polish topology with both operations continuous, while the whole cone, with
open induction, carries none with continuous addition (Glazer's Corollary 1).

**Part IV** (08). A discretely ordered ring whose additive group has a
Hausdorff locally compact second-countable group topology with Borel order is
discrete and countable, with no regularity assumed of multiplication
(Theorem 44.1), by an amplification theorem: an integer-free subgroup with
an order unit `u` injects into `A/V` by `v ↦ uv + V` (Theorem 46.2), while
Borel order and local compactness give an open real component `R^d` with
countable quotient (Theorem 47.2, from the imported LCA structure theorem).
Locally compact Borel Z-groups are `R^d × E` as pointed topological groups
(Theorem 50.1); their cones are Polish with continuous addition, Δ⁰₂, and
locally compact exactly when `d ≤ 1` (Theorem 51.2); definable relations are
Δ⁰₂ and standard division continuous (Theorem 52.1). An integral-domain
multiplication unrelated to the order has only countably many Borel scalars,
exactly `Z1` on `R^d × Z` (Theorem 53.4). Examples 54.1 and 54.2 show that
second countability and Borelness of the order are needed; Corollaries 55.1
and 55.2 apply to set-sized subrings of `Oz` such as `Z + ωR[ω]` and to
`Z + Rω + … + Rω^d`.

**Part V** (09). A Polish additive topology with Baire-property cone and Borel
scalar maps on an ordered field refines the order topology (Theorem 61.4);
on a discretely ordered ring it is discrete (Theorem 62.1), and every integer
part of such a field is countable and closed discrete (Theorem 62.3).
`k((t^Γ))` (`t` positive infinitesimal) admits one iff `k` is countable and
`Γ ≅ Z`, uniquely (Theorem 63.3); the Puiseux field over countable `k` admits
none (Theorem 64.3); its Levi-Civita completion admits exactly one
(Theorem 65.3). Order separability is characterized by countable prefixes
(Theorem 66.1); the code domains are Σ⁰₂-, Π⁰₃- and Π¹₁-complete
(Theorems 67.1–67.3). Over real algebraic coefficients the Puiseux and
Levi-Civita fields are real closed (Theorem 68.2). Countable-parameter Polish
hulls exist, have uniform support bounds individually but none overall, have
no maximal member, can be real closed and truncation-closed, and exactly
2^ℵ₀ of them are needed to cover the Hahn field (Theorems 69.2, 69.3, 69.5, 69.6, Corollary 69.4). The
common integer part `I_k` has the floor formula of `odg:thm:floor`
(Theorem 70.1), a Baire-class-one floor with discontinuity set exactly `I_k`
(Theorems 70.2, 70.4), and open induction (Proposition 70.6).

## What the report does not claim

Appendix F keeps every limitation, source by source (05: 9 items, 04: 8,
03: 9, 07: 10, 06: 10, 08: 9, 09: 8, merge: 7). In short: no priority for any
source; no answer to Glazer's Question 1, and no conclusion about variants of
Question 2 with further hypotheses; no model of PA, no continuous order, no
ring embedding into `Oz`, no canonical topology on `Oz` or on the class `No`;
classical Z-group elimination, Hausdorff's characterization, analytic
boundedness, Shepherdson-type models, the LCA structure theorem, the category
toolkit, Newton–Puiseux and the Levi-Civita construction are not claimed as
new; Glazer's multiplication obstruction (his Theorem 2) is not transferred
to 03's ring; the full-Hahn results need observable coefficients; 08 assumes
a group topology on the signed ring, not an arbitrary topology on the cone;
the real-coefficient Levi-Civita field is not claimed Polish; the failure of
open induction in `Z + tR[t]` does not transfer to `Oz`; the finite checks are
finite.

Part I has 17 questions (four asked by both 04 and 05, merged in Section
14.1), Part II 8, Part III 11 of 07 with 06's twelve numbered projects
attached to the questions of the same subject, Part IV 8, Part V 12. One
sentence of Question 14.4 is answered by 06's Theorem 38.1 (note after the
question); 07's question on uniform definability bounds is answered for
locally compact signed presentations by 08's Theorem 52.1; 08's Question 57.1
is answered under 09's Borel-scalar hypothesis by Theorem 62.1. Everything
else is open. 08's Question 57.2 and 09's Question 73.11 are the same
question.

## Printed by citation, not reprinted as new

All labels exist at HEAD.

- `exr:prop:division` (exponential-relations-over-omnific-integers): `Oz` is a
  Z-group, hence a Presburger model; Part I reproves the classical facts for
  the split groups.
- `isg:cf:main:presburger` (discrete-initial-subgroups-and-omnific-normalization):
  a set-sized Z-group has an initial realization in `Oz` iff it splits as
  `G^dv ×→ Z`; Part I's groups split, so it applies to them (Section 1.4).
  06 also cites `isg:thm:suspension` and `isg:cf:thm:PA`.
- `onot:neg:lem:kbtree`, `onot:neg:thm:pionesone`, `onot:neg:rem:secondroute`
  (omnific-notations): the lightface Π¹₁ results of which Lemma 18.2 and
  Theorem 22.1 are boldface counterparts; 09's Theorem 67.3 proves them again.
- `odg:thm:floor` (omnific-diophantine-geometry), **proved in Lean** for every
  surreal (`omnificFloor_spec`, `existsUnique_omnific_integerPart`,
  `omnificFloor_of_integer_negative_tail` in
  `Algebra/SurrealNumbers/Surreal/Foundations/OmnificFloor.lean`): Lemma 23.1
  and 09's Theorem 70.1 are restrictions of it; neither is formalized as
  stated.
- `dsn:cor:openinduction` (definable-surreals-and-omnific-integers) and the
  Shepherdson paragraph of omnific-diophantine-geometry: the route of
  Theorem 23.2 and of 09's Proposition 70.6. Pending in
  `docs/FORMALIZATION.md`.
- `odg:frac:sub:models`, `odg:frac:prop:intersection`, `odg:frac:ex:workspace`
  (omnific-diophantine-geometry): the ring `Z + tR[t]` of 06's Section 38 and
  08's Example 54.1; `odg:thm:induction` and `odg:rem:ringinduction`: the
  existential induction failures in `Oz`, which 06's bounded failure in
  `Z + tR[t]` does not replace.

## Corrections and stale statements

- The placement record (`3d2177df4`) and the intake dossier said that 03's
  topology restricts on the real stratum to the topology of 04 and 05. It
  agrees with it off the standard numerals and isolates the numerals
  (Proposition 26.1(iii)); both make addition continuous there, so the
  placement's conclusion stands.
- 07's audit (Appendix H) says that the repository's `.tex`, `.md` and `.lean`
  files never mention Glazer or Tennenbaum. True at its pin `0f95145cb`;
  stale since `0f3b760ae` (the word occurs in archive names in the
  Hilbert's-tenth programme's scope note) and `3d2177df4` (this report). A
  note after the statement corrects it.
- 09's bibliography and `09-hahn-polishability-SOURCES.md` cite the root and
  surreal READMEs by unversioned `blob/main` addresses beside the pin
  `4af956fe0`; the note in Appendix M gives the pinned address, and both files
  are unchanged between the pin and `0bd0e5527`.
- 08 and 09 cite 05 and 03 as "user-library" PDFs (`polish_presburger_glazer.pdf`,
  `glazer_proveit_article.pdf`); they are Parts I and II here (notes in the
  bibliography).
- Source 05's part of Question 14.4 asked for a Polish continuous-addition
  Presburger model whose additive structure admits a unital semiring
  expansion; 06's Theorem 38.1 gives one. A dated note after the question
  re-scopes it; its `Q + IOpen` clause and 04's part stay open.
- 03 cites Alvir–Rossegger only as arXiv:1810.11423; its journal version
  (J. Symb. Log. 85 (2020), 1079–1101) is added. Paran–Vo's issue number (no. 2)
  is added. Ehrlich–Kaplan's journal reference as given by 07 (J. Symb. Log.
  83 (2018), 617–633) is recorded but not re-checked; the arXiv record lists
  none. No source statement was found false.

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
  nonstandard Z-groups and give the coset-invariant replacement (Section 13.5);
  08 says the same (Remark after Theorem 49.3). 06 and 07 note that
  `Formula.holds` (`Syntax.lean`) and `holds_iff_quantifierEliminate`
  (`Decision.lean`) are stated over `List Int`, which holds at HEAD; 06 also
  reads `Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean`. This is a
  porting requirement, not a defect. **Placement beside a formal project
  confers no formal status: no statement of this report is formalized**, and
  `docs/FORMALIZATION.md` maps none of its labels.
- [`omnific-notations`](../omnific-notations/): Part II's Lemma 18.2 and
  Theorem 22.1 and Part V's Theorem 67.3 are boldface counterparts or second
  proofs of its Π¹₁ validity results; no source answers its named questions.
- [`exponential-relations-over-omnific-integers`](../exponential-relations-over-omnific-integers/):
  the collection's other Presburger report (`Oz` as a Presburger group).
- [`discrete-initial-subgroups-and-omnific-normalization`](../../surreal/discrete-initial-subgroups-and-omnific-normalization/):
  split Z-groups and initial realizations (`isg:cf:main:presburger`); batch
  86's manuscript 10, on the standard cut, was written there. Its ring
  `Z + XQ[X]` fails open induction at the same formula as 06's Theorem 38.2,
  and its Shepherdson ring is 09's integer part `I_k` for `k = R_alg`.
  Manuscript 10 is that report's source 03 (Sections 19–22); its obstruction
  precedes any topology (`isg:sc:thm:nochar`, `isg:sc:cor:omnific`,
  `isg:sc:cor:fragment`), and it answers neither of Glazer's questions (a
  sentence added in the batch-86 reciprocal notes, in the paragraph "The
  same failed instance elsewhere" of Section 42).
- The batch-86 reciprocal notes added pointers to this report in
  `omnific-notations` (after its Remark 23.4: Parts II and V),
  `exponential-relations-over-omnific-integers` (after its Proposition 2.2:
  Part I), `omnific-diophantine-geometry` (after its Proposition 15.43:
  Parts II–V) and `definable-surreals-and-omnific-integers` (after its
  Corollary 4.6: Parts II and V), and README pointers there and in
  `discrete-initial-subgroups-and-omnific-normalization`.
- [`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/)
  and [`omnific-diophantine-geometry`](../../surreal/omnific-diophantine-geometry/):
  open induction, the floor, and the polynomial models `Z + tR[t]`.
- [`surreal-well-orders`](../surreal-well-orders/): its `WO_μ(X)` (well-orderings
  of type μ) is a different object from 03's `WO(L)` (well-ordered subsets).
- The Hilbert's-tenth programme triaged the two arrivals for its own search
  (`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_recent_incoming_glazer_scope.md`,
  `recent_incoming_substrate_triage_20261003.md`); these are routing notes,
  not proof audits, and Appendix E cites them.

## Notation

Section 1.3 has the full table, in two blocks. Parts I–II: 04's `G(D)`,
`M(D)`, `D_ω`, `M_ω`, `⊕_lex` are 05's `G_D`, `M_D`, `D_B`, `M_B`, `×→` (the
same objects); 04's Baire homeomorphism `H` (charts `H_≥`, `H_>`) and integer
code `h` are `Ψ`, `Ψ_≥`, `Ψ_>`, `ζ`; 03's ring `𝒜`, cone `𝒜_{≥0}`, rational
Hahn ring `H`, Kleene–Brouwer embedding `h` and two local sets `D` are `A_fin`,
`A_fin,≥0`, `H_Q`, `μ_KB`, `W` and `𝒵`. Both `\B` macros (04: Baire space; 03:
unused `𝓑`) are replaced by `N^N`. Parts III–V: **`t` is positive infinite in
Part III (06's `Z + tR[t]`, `t ↦ ω`) and positive infinitesimal in Part V
(09's Hahn convention, `t^q ↦ ω^{-q}`)**; 03's `X = t^{-1}` is infinite, and
08 writes `X` for 06's `t`. 06's family `M_s`, `G_s`, `H_s` (`s ∈ 2^N`) is
`M'_s`, `G'_s`, `H'_s`, because 07's `M_s` is a different family; the
lexicographic subscripts of 06, 07 and 08 are printed as `×→`; 09's macros
for `𝒫_k`, `ℒ_k`, `ℋ_k`, `ℐ_k` are renamed in the source only (the printed
symbols are unchanged; `𝒫_k` is not 03's cone `A_fin,≥0`); 09's `WF` and 08's
`IOpen` use the report's sans-serif forms; 07's `ProveIt`, indicator and
monus macros are the report's. No normalization changed.

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
- `code/08-local-compactness-build.sh` changes to its own directory, runs
  `latexmk` on `article.tex` and `python3 verify.py --output
  verification_results.json`; `code/08-local-compactness-verify.py` says
  "Run: python3 verify.py --output verification_results.json" and writes that
  file in the working directory by default. `08-local-compactness-sources.md`
  names the two "user-library" PDFs and "this ZIP"; `08-local-compactness-proof_audit.md`
  describes 08's own PDF build.
- `code/09-hahn-polishability-build.sh` changes to its own directory, runs
  three `pdflatex` passes on `article.tex` and `python3 verify.py --output
  verification.json`; `code/09-hahn-polishability-verify.py` describes itself
  as checks "for article.tex" and writes `verification.json` in the working
  directory by default. `09-hahn-polishability-SOURCES.md` names the
  "user-library" PDFs and unversioned `blob/main` URLs.
- The source texts merged into `article.tex` give their delivery names in
  their reproduction sections; notes after each give the shipped names.

## Build

From a copy in a scratch directory:

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with `newpxtext`/`newpxmath`, `tcolorbox`, `cleveref`, `aliascnt`,
`tikz` (07's figure). The build has no errors, no LaTeX, package or hyperref
warnings, no overfull or underfull boxes, no undefined or multiply defined
references and no duplicate destinations; 191 pages. Commit only
`article.pdf`, not the auxiliary files.

## Rerunning the finite checks

All five programs need only Python 3.10+ and the standard library. Run them
**on a copy** with the delivery names restored, never in this directory (05's
runner writes beside itself, the others into the working directory, and the
build scripts of 05, 08 and 09 would build an `article.tex` and rerun the
checks in place):

```
D=/path/to/this/report; S=/path/to/scratch     # a fresh directory
mkdir -p $S/03 $S/04 $S/05 $S/08 $S/09
cp $D/code/05-omnific-presburger-polish_presburger.py $S/05/polish_presburger.py
cp $D/code/05-omnific-presburger-verify.py            $S/05/verify.py
cp $D/code/04-polish-presburger-verification.py       $S/04/verification.py
cp $D/code/03-borel-presentations-verify.py           $S/03/verify.py
cp $D/code/08-local-compactness-verify.py             $S/08/verify.py
cp $D/code/09-hahn-polishability-verify.py            $S/09/verify.py
cd $S
python 05/verify.py                                   # writes 05/verification_results.json
python 04/verification.py --output 04/verification_results.json
python 03/verify.py --output 03/verification.json
python 08/verify.py --output 08/verification_results.json
python 09/verify.py --output 09/verification.json
```

Tested with Python 3.14.4 on Windows: 05 reports `"status": "PASS"` and
17,930 checks in 18 families; 04 `"status": "passed"` and 75,079 assertions in
13 categories; 03 `"status": "PASS"` and 84,388 assertions in 11 groups; 08
`"status": "PASS"` and 24,470 cases in 4 families; 09 `"status": "passed"` and
20,116 assertions in 29 families (seed 20261003), about one second each for
08 and 09. The new records equal the shipped ones except for the interpreter
version (05, 03) and, on Windows, CRLF line endings. 04's stream API (`from
verification import Stream, baire_add, ...`) works from `$S/04`. To rebuild a
source's own PDF, re-extract its archive from the arrival commit (for
example `git show fb8414869:docs/incoming/glazer_proveit_local_compactness.zip`)
and run its build script there. The checks verify finite instances and stream
prefixes only; Polishness, induction, completeness, local compactness and the
descriptive-set-theoretic theorems are proved in the text.

## Provenance

Appendix E. For Parts I and II the merge printed 05's text as the base;
printed each shared result once, crediting both sources, with 04's genuinely
different proofs as marked second proofs (Propositions 4.2, 8.2, Lemma 4.7 via
Theorem 4.8, Theorems 4.9, 6.1, 7.1, 8.3, 10.4, 11.1); printed both of the
incomparable order obstructions (Theorems 7.4 and 7.5, Remark 7.7); merged
four questions; and added Glazer's speculation, the stratum proposition (26.1)
and the notes citing the collection. For Part III it printed 07's text as the
base and 06's as marked sections; printed the results of Part I that 06 and
07 prove again with their proofs and a flag naming the Part I statement;
printed both continuum theorems (35.5, 35.8); attached 06's projects to 07's
questions; and added Section 42 and the notes. Parts IV and V are 08 and 09
whole, with notes citing Parts I–III and the collection. Citation details
checked on 3 October 2026: Glazer's arXiv record; Tserunyan's notes (dated
November 26, 2025); Paran–Vo, Israel J. Math. 273 (2026), no. 2, 979–1000
(online 11 December 2025); Enayat–Hamkins–Wcisło, Fund. Math. 256 (2022),
171–193; Jeřábek, MLQ 65 (2019), 108–115; Haase, ACM SIGLOG News 5(3) (2018),
67–82; Alvir–Rossegger, J. Symb. Log. 85 (2020); Block, arXiv:2601.21118v3
(16 June 2026); Chen, arXiv:2109.12721v1 (2021, no journal reference). The
other classical references were not re-checked.
