# Surreal Fields Across Set-Theoretic Universes

**Omitted cuts, fresh-sign gaps and saturation spectra of old surreal fields;
first new birthdays; surcomplex real forms; a Boolean completion of reverse
simplicity; and (Part VIII) full gap spectra, relative grounds and
classification**

Merged research report built from ten manuscripts. Parts I–VII (22 September
2026) merge four manuscripts, 01 (the base), 03, 04 and 08, all pinned to
commit `4f2645599121fa872c7104995e47f86f0382351f`. Part VIII (added
28 September 2026) merges six manuscripts of that date, numbered **09–14** in
this report's local sequence, all pinned to ProveIt commit
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`. Author lines: 01, 03, 04, 08 as in
the merge of 22 September; 09, 12, 13 "prepared with ChatGPT"; 10, 11, 14
"prepared (with ChatGPT) for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (base of I–VII) | Surreal batch 21, manuscript 01 (25-page PDF) | one of the nine archives of `cd99d4c` | `4f26455` | `d4e71b7`, written `3a2d35d` | Parts I–VII (spine, Boolean completion) |
| 03 | Surreal batch 21, manuscript 03 (21 pages) | as above | `4f26455` | `d4e71b7` | Part II and parts of IV–V |
| 04 | Surreal batch 21, manuscript 04 (25 pages) | as above | `4f26455` | `d4e71b7` | Section 5.2 and parts of IV–V |
| 08 | Surreal batch 21, manuscript 08 (24 pages) | as above | `4f26455` | `d4e71b7` | Section 5.3, Part III and parts of IV–V |
| 09 | batch 37, manuscript 01, *Full Gap Spectra of Old Surreal Fields* (23 pages) | `proveit_gap_spectra` | `e21766d` | `0e53d1034` (arrived `37e61c1fd`) | Sections 22–24, 27 (second route), 28, 30.1 |
| 10 | batch 37, manuscript 02, *Exact Gap Spectra of Ground-Model Surreal Fields* (22 pages) | `ProveIt_Exact_Surreal_Gap_Spectra` | `e21766d` | `0e53d1034` | Sections 22–25, 30.2 |
| 11 | batch 37, manuscript 03, *Beyond the First Omitted Cut* (25 pages) | `ProveIt_Full_Gap_Spectra` | `e21766d` | `0e53d1034` | Sections 22–25, 29, 30.3 |
| 12 | batch 37, manuscript 04, *Beyond Gap Spectra: real traces and embeddability of old surreal fields* (22 pages) | `proveit_beyond_gap_spectra` | `e21766d` | `0e53d1034` | Sections 22, 23.3, 27, 30.4 |
| 13 | batch 37, manuscript 05, *Cofinality Compression and Coordinate Spectra of Old Surreal Fields* (22 pages) | `Surreal_Gap_Spectra_Research` | `e21766d` | `0e53d1034` | Sections 22–26, 30.5 |
| 14 | batch 37, manuscript 06, *Beyond the First Gap: Exact Spectra and Boolean Families of Old Surreal Fields* (26 pages) | `Surreal_Gap_Spectra_Research (1)` (a different package from 13) | `e21766d` | `0e53d1034` | Sections 22–26, 30.6 |

The batch-37 sources are called 09–14 in the text, because this report already
uses 01, 03, 04 and 08 for its own manuscripts; the batch-37 manuscript numbers
and archive names appear only in the table above and in Section 21.1.

**Status:** AI-assisted, unrefereed research report. **Nothing in it is
formalized or Lean-verified**, and Part VIII's statements are not indexed in the
formalization ledger.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 106 pages (title page, 3 contents pages, 102 numbered pages)
README.md     this guide
03-fresh-sign-gaps-PROOF_STATUS.md        source 03: proof and verification status
09-cohen-amplification-PROOF_STATUS.md    source 09: attribution, imports, sensitive points, checks
10-isolated-coordinates-PROOF_STATUS.md   source 10: scope, imports, hypotheses, excluded claims
11-finite-complements-PROOF_STATUS.md     source 11: proof status, inputs, review priorities
11-finite-complements-SOURCE_AUDIT.md     source 11: repository and literature audit
12-real-traces-SOURCES.md                 source 12: sources and attribution boundaries
13-coordinate-spectra-PROOF_AUDIT.md      source 13: proof and dependency audit
13-coordinate-spectra-SOURCES.md          source 13: pinned sources and literature
13-coordinate-spectra-BUILD_REPORT.md     source 13: build and PDF-inspection report (of its own 22-page PDF)
14-relative-cutoffs-PROOF_STATUS.md       source 14: claims, imports and review priorities
code/
  01-forcing-omitted-cuts-Makefile               source 01's LaTeX Makefile (see "Build and reproduce")
  03-fresh-sign-gaps-check_finite_signs.py       source 03 finite sign and block-code checks
  04-universe-saturation-Makefile                source 04's Makefile (written for its own file names)
  04-universe-saturation-verify_finite_models.py source 04 finite interval-code checks
  08-forcing-saturation-verify_sign_code.py      source 08 finite sign-code checks
  09-cohen-amplification-Makefile                source 09's Makefile (its own file names; do not run here)
  09-cohen-amplification-verify_finite.py        source 09 finite sign-order and block-code checks
  10-isolated-coordinates-Makefile               source 10's Makefile (its own file names; do not run here)
  10-isolated-coordinates-check_finite.py        source 10 delimiter-code, cone and profile checks
  11-finite-complements-build.sh                 source 11's build script (its own layout; do not run here)
  11-finite-complements-finite_checks.py         source 11 finite checks (always writes results.json beside itself)
  12-real-traces-verify_finite.py                source 12 finite checks (writes beside itself by default)
  13-coordinate-spectra-Makefile                 source 13's Makefile (its own file names; do not run here)
  13-coordinate-spectra-verify_finite.py         source 13 finite checks
  14-relative-cutoffs-Makefile                   source 14's Makefile (its own file names; do not run here)
  14-relative-cutoffs-verify_finite.py           source 14 finite checks (writes finite_checks.json in the CWD by default)
data/
  03-fresh-sign-gaps-finite_checks.json          recorded run of the source 03 checks
  04-universe-saturation-finite_check_results.txt  recorded run of the source 04 checks
  08-forcing-saturation-verification_results.txt   recorded run of the source 08 checks
  09-cohen-amplification-verification_results.json recorded run of the source 09 checks
  10-isolated-coordinates-verification_results.json recorded run of the source 10 checks
  11-finite-complements-results.json             recorded run of the source 11 checks
  11-finite-complements-validation.json          source 11's build/layout record (of its own 25-page PDF)
  12-real-traces-verification_results.json       recorded run of the source 12 checks
  13-coordinate-spectra-verification_results.json recorded run of the source 13 checks
  14-relative-cutoffs-finite_checks.json         recorded run of the source 14 checks
  14-relative-cutoffs-pdf_validation.json        source 14's PDF-layout record (of its own 26-page PDF)
```

## Labels

The article has **286 labels**. The 142 labels of Parts I–VII carry the prefix
`univ:`; source 01's labels keep their names behind it (for example
`univ:thm:main-summary`). Part VIII added **144** labels, all with the sub-prefix
`univ:gs:` (a plain `univ:` prefix would have collided with twelve existing
labels, and the six sources share 43 bare label names). No label was renamed or
removed, and no theorem, section, equation or question number of Parts I–VII
changed: the `.aux` numbers of all 142 earlier labels were compared with a build
of the committed text (page numbers of twelve of them moved). All 57 `univ:`
labels cited by [`docs/FORMALIZATION.md`](../../FORMALIZATION.md) still resolve in
`article.tex`; none is mapped to a Lean declaration.

Code, data and audit files keep the numbers of the sources they came from and are
byte-identical to the delivered files. No source manuscript, source README or
source PDF is shipped.

## Why one report

**Parts I–VII.** All four manuscripts of 22 September prove the same spine in the
same setting: transitive universes `M ⊆ N` of ZFC with the same ordinals, the old
field `No^M` viewed as a proper class of `N`, and all sizes computed in `N`. They
share the cut and saturation criterion, the regular first new length `δ`, an
omitted `(δ,δ)` gap, the `ω` boundary, the pure/conjugation contrast, the
distributivity corollary and the Cohen and Prikry examples. **01 is the base**: it
has the weakest hypotheses (plain ZFC with a definable inner model; Global Choice
only for one negative Boolean result) and the strongest criterion (one small side
suffices). The other sources' unique results form their own parts and sections:

- **03**: the fresh-sign classification of all set-presented gaps (Part II), old
  ordinal bounds, the ordinal-bound cut criterion, the Prikry fresh sign, and the
  real-form invariant with agreement on `C^N` and finite forcing towers.
- **04**: the absolute all-ordinal interval code with closed finite-branch
  formulas (Section 5.2), cuts inside `(0,1)`, `Add(κ,1)` under `κ^{<κ}=κ`,
  elementarily equivalent nonconjugate involutions, open cones, and
  nowhere-denseness of `No^M[i]` in `No^N[i]`.
- **08**: the ordinal block code with its exact separator class (Section 5.3),
  the dense-linear-order clause, the first new birthday `β` with
  `δ ≤ cf^N β ≤ β` (Part III), `β` in the forcing examples, the lottery-sum
  caution, non-definability of conjugation, and the saturated back-and-forth
  route.

Results proved by two or more sources are printed once with every proving source
named at the statement (Section 1.6 lists them). The converse direction of the
spine has three genuinely different constructions: 01's interval tree is the main
route (Section 5.1), and 04's absolute code and the block codes of 08 and 03
(Section 5.3, Proposition 9.1) are marked second routes. Two existence proofs for
`δ` and two class back-and-forth routes are also kept.

**Part VIII (sources 09–14).** Each of the six answers one or more of this
report's named questions 19.2 (`univ:q:cutspectrum`), 19.4
(`univ:q:completeness`) and 19.7 (`univ:q:families`), so they are one merged
*addition* rather than a rival report. All six prove the same spine, the
outer-cofinality transfer from fresh functions to gap characters, and all six
re-prove the fresh-sign correspondence of Part II and the class back-and-forth of
Part V (not reprinted; Remarks 22.2 and 30.1 record their variants). Part VIII is
placed after Section 20, so every earlier number that other reports cite stays
fixed. Bases per result family (Section 21.1): transfer 11; density ceiling 10
(cofinal filter base; 09, 11, 13, 14 special cases, 12's square chain condition a
second route); generalized Cohen spectrum 11 (second routes 10 and 12); Easton
realization 09; name localization 14 (distributivity suffices; the closure proof of
10, 11, 13 kept as a second route); intersections 13; countable coordinate spectra
13 (14's `κ_n = ℵ_{n+1}` case and its own preservation proof kept as a second
route); real trace 12 (09's rational-cut invariant a second route); local ubiquity
13 (14's affine route kept). The three constructions of equal full spectra without
isomorphism (12, 09, 11) are all kept and compared in Section 29.1.

## Notation

**Parts I–VII** (Section 1.3, with a table of every renaming): `No^M`, `No^N` for
the old and new fields; `SC^M = No^M[i]`, `SC^N` for the surcomplex fields (`K` is
not used for these proper classes, since the collection reserves `K` for set-sized
fields); `δ` for the first new *length* of an ordinal-valued sequence (03's `ν`,
04's `d(M,W)`); `β` for the first new *birthday*, as in 08; `ρ` for the measurable
cardinal. The sibling report also writes the first new birthday as `β`; several of
its source manuscripts wrote `δ` for it, and that `δ` is this report's `β`, not its
`δ`.

**Part VIII** (Section 21.3, with a table): `Char_N(F)` is the scalar (diagonal)
gap spectrum and `GapSpec_N` the pair spectrum; `𝔉(M,N)` is the fresh-function
spectrum of one pair (not the union-over-generics `FRESH(P)` of
Fischer–Koelbing–Wohofsky, and not the report's `Fresh(M,N)`, which is the class of
fresh *signs*); `Ecl` the Easton closure; `Tr_R` the real trace; `bcode`, `dcode`
and `code^+` the three block codes. **Subscripts on intermediate grounds always
list retained coordinates** (`M_A = V[G↾A]`); sources 10, 11 and 13 indexed by
omitted coordinates and are rewritten, and omitted sets are written `B`. Renamed to
keep this report's reservations: 03's `g(M,N)` (now `Char`), Cohen reals `c_n`
(now `y_n`, since `c_M, c_N` are conjugations), generic filters `H` (since
`H = Φ(No^M)`), 10's and 11's index cardinal `θ` (now `χ`), 12's `θ = 2^{<κ}` (now
`σ_κ`), 14's final universe `W` (now `N`), range bounds `ρ` (now `θ`). Old class
fields are written out as `No^{M_A}`, never `K_A` or `F_A`. The letter `ν` is not
used in the report's own notation.

## Hypotheses

- **(H)**: `N ⊨ ZFC` and `M` a parameter-definable transitive inner class
  containing all ordinals and satisfying ZFC (or an available class predicate with
  the needed Separation and Replacement instances). Everything is proved under (H)
  except what is listed next.
- **(GC)**: `GBC` with Global Choice, `M` a class. Needed only for the class
  isomorphisms and real forms of Part V and of Section 30 (except Theorem 30.11, a
  ZFC theorem about one set field), and for the impossibility of a class-complete
  Boolean algebra (Theorem 17.3).

Sources 03 and 08 were written in `GBC` with Global Choice. Their proofs used
outside Part V were re-read for this merge and use only set-sized choices, Choice
in `M` and Replacement for `M`; source 03's gaps, which it quantified over as class
partitions, are given by their set presentations (Definition 6.1). Part VIII's
forcing statements are relative (ground/extension) and use set forcing only; its
imported forcing theorems need GCH (Easton products, the countable products and
source 10's Boolean family), CH (Namba) or a measurable cardinal (Prikry, the
Cohen–Prikry tower), as stated at each result.

## What the report claims

- **Theorem 1.1 (main spectrum; 01, 03, 04, 08).** For every infinite `N`-cardinal
  `κ`: no new ordinal-valued sequences of length `< κ` ⇔ every `N`-set cut
  `L < R` in `No^M` with `min(|L|,|R|) < κ` is filled ⇔ every such cut with
  `|L ∪ R| < κ` is filled. For uncountable `κ` these are equivalent to
  `κ`-saturation of `No^M` as an ordered field and as a dense linear order. Failing
  cuts can be chosen inside `(0,1)`. The key lemma is Theorem 3.5: a cut with one
  side in `M` is always filled.
- **Theorem 1.2 and Sections 4–7.** `δ` is a regular cardinal of both universes
  (Proposition 4.2); `No^M` has a set-presented gap of exact cofinality pair
  `(δ,δ)` and none smaller (Theorem 6.2); it is `κ`-saturated for uncountable `κ`
  exactly when `κ ≤ δ`, and set-saturated only if `M = N` (Corollary 6.4); it is
  `ω`-saturated exactly when no reals are added, while the pure order is always
  `ω`-saturated (Theorem 7.1).
- **Codings (Section 5).** The interval tree and branch decoder (Lemma 5.1,
  Theorem 5.2); the absolute all-ordinal code (Theorems 5.3, 5.4, Proposition 5.5);
  the block code whose separators are exactly `Cone(code(f))` (Lemma 5.6,
  Theorem 5.8).
- **Fresh signs (Part II, source 03).** Set-presented gaps correspond bijectively
  to fresh signs; each gap is symmetric with both cofinalities `cf^N b(s)`
  (Theorem 8.4); its fillers are exactly `Cone(s)` and `No^N \ No^M` is the disjoint
  union of fresh cones (Theorem 8.5); the gap spectrum (Corollary 8.6); the least
  omitted pair has size `δ`, also the least cofinality of a fresh sign
  (Theorem 9.2).
- **First new birthday (Part III, source 08).** `β` is the least birthday of a new
  surreal, a cardinal of `M` and `N`, and `δ ≤ cf^N β ≤ β` (Proposition 10.2). A
  merge remark observes that `β` is also the least length of a fresh sign
  (Remark 10.4).
- **Surcomplex (Section 11).** `SC^M` is saturated over every `N`-set in the pure
  field language (Theorem 11.2); `(SC^M, c_M)` has exactly the spectrum of `No^M`
  and is an elementary substructure of `(SC^N, c_N)` (Theorem 11.4); no order or
  field isomorphism `No^M ≅ No^N` with set-sized images exists (Corollary 11.6).
- **Bounded fragments (Theorem 12.1, source 01).** For uncountable regular `κ` of
  `M` that stays a cardinal, `(No_{<κ})^M` is `κ`-saturated in `N` iff `κ` stays
  regular and no binary signs shorter than `κ` are new.
- **Forcing (Section 13).** The distributivity characterization (Corollary 13.1);
  `Add(κ,1)` gives `δ = β = κ` with no cardinal arithmetic (Proposition 13.2);
  Prikry at a measurable `ρ` gives `δ = ω`, `β = ρ`, `ω`- but not
  `ω₁`-saturation, identical fragments below `ρ`, and a separator of birthday
  exactly `ρ` (Corollary 13.4).
- **Topology (Section 14).** Every `N`-set of old numbers is uniformly discrete and
  closed, and set-indexed Cauchy nets are eventually constant (Proposition 14.1);
  if `M ≠ N`, `No^M` is closed and nowhere dense in `No^N` with its own order
  topology as subspace topology, and likewise `SC^M` in `SC^N` (Theorem 14.3).
- **Real forms under Global Choice (Part V).** `SC^M ≅ SC^N` fixing any `N`-set
  (Theorem 15.2); the transported involution `j` has gap spectrum equal to the
  fresh-sign spectrum and least omitted pair `δ`, no set-sized cofinal subset, and
  is not conjugate to `c_N` (Theorem 16.2); `(SC^N,c_N)` and `(SC^N,j)` are
  elementarily equivalent with different spectra (Theorem 16.3); `j` can agree
  with `c_N` on `C^N` (Corollary 16.5); several grounds give several
  nonconjugate forms (Theorem 16.6), realized by finite `Add(κ_a,1)` towers with
  no large cardinals (Corollary 16.7).
- **Boolean completion (Section 17, source 01).** A set-complete class Boolean
  algebra in which reverse simplicity is dense (Theorem 17.1), answering a
  precisely interpreted Question 2 of Berenbeim's 2020 notes; no class-complete
  one under Global Choice (Theorem 17.3).

**Part VIII (sources 09–14).**

- **Transfer (Theorem 22.7; all six, base 11).** For every same-ordinal pair,
  `Char_N(No^M) = { cf^N λ : λ ∈ 𝔉(M,N) }`: the gap characters are the *outer*
  cofinalities of the *ground* regular cardinals carrying fresh ordinal-valued
  functions. Compression (Lemma 22.4) and three block codes (Lemmas 22.5, 22.6,
  Proposition 9.1); every omitted set cut of an old field is a genuine gap
  (Lemma 22.3); lower barrier and saturation read off the least character
  (Corollaries 22.10, 22.11).
- **Density ceiling (Theorem 23.2; base 10).** A fresh function's domain has outer
  cofinality at most the `N`-size of any cofinal base of the generic filter, hence
  at most `|D|^N` for a ground dense set; the character spectrum of a set-forcing
  extension is a set.
- **One Cohen subset or one collapse (Theorem 23.6; base 11, routes of 10, 12, 13,
  14).** For `Fn_{<κ}(κ,A)^M`, any ground alphabet `|A| ≥ 2`: the full spectrum is
  `{(κ,κ)}` and the first new birthday is `κ`, with no cardinal arithmetic; this
  completes Proposition 13.2. Collapse (Corollary 23.8); the square chain
  condition and any number of Cohen reals give `{(ω,ω)}` (Lemma 23.9,
  Propositions 23.11, 23.12); explicit collapse of `[κ, 2^{<κ}]` to cofinality `κ`
  (Lemma 23.14).
- **Easton products (Theorem 24.3; base 09).** Under GCH the spectrum is exactly
  the Easton closure of the coordinates (Mahlo exception kept); a hole
  `{ℵ₁, ℵ₃}` and an extra character `ℵ_{ω+1}` (Examples 24.4, 24.5).
- **Relative spectra (Section 25).** Name localization and intersections of
  mutually generic extensions (Lemmas 25.1, 25.3); isolated coordinates
  (Theorem 25.5, source 10); finite complements of sparse products (Theorem 25.8,
  source 11); finite Boolean cubes (Theorem 25.10, source 14); **every coordinate
  ground of a countable GCH product** (Theorem 25.15, base 13): the characters are
  `κ_n` for the omitted `n`, plus `λ^+` exactly when infinitely many are omitted;
  binary intersections and recovery of the index (Proposition 25.17); one threshold
  for continuum many (Corollary 25.19); `2^χ` fields with one threshold
  (Theorem 25.21, source 10) and families of any length `χ` (Theorem 25.26,
  source 11).
- **Cutoffs and ubiquity (Section 26, sources 14, 13).** Exact gap pairs of set-sized
  cutoffs `(No_{<θ})^M`, including asymmetric boundary pairs `(μ,θ)`, `(θ,μ)`
  (Lemma 26.1, Theorem 26.2); every occurring character occurs in every interval a
  proper class of times (Proposition 26.4).
- **Equal full spectra without isomorphism (Question 19.4, negative for fields).**
  Source 12 (Theorem 27.4, ZFC and Cohen forcing only): old fields with spectrum
  `{(ω,ω)}`, equal saturation at every cardinal, and field embeddability exactly
  inclusion of index sets, distinguished by the real trace `Tr_R(No^M) = R^M`
  (Theorem 27.3); every ground set-sized partial order is realized
  (Corollary 27.8). Source 09 (Theorem 28.5): Cohen amplification of any no-new-reals
  extension adding a countable sequence gives continuum many old fields with one
  full spectrum, nonisomorphic as pure fields, via common-small-forcing invariance
  (Theorem 28.3); exact Prikry `{(ω,ω)}` and Namba (CH) `{(ω,ω),(ω₁,ω₁)}` spectra
  (Corollaries 28.8, 28.10). Source 11 (Theorem 29.2, a measurable): a Cohen–Prikry
  tower with equal spectra `{ω}` and different `ω`-saturation.
- **Real forms (Section 30, Global Choice except 30.11).** Nonconjugate involutions of
  one `SC^N` from each family: with one identical spectrum agreeing on `C^M`
  (Theorem 30.3; agreement on `C^N` impossible there, Proposition 30.4); agreeing
  on any set-sized conjugation-stable core, elementarily equivalent over it
  (Theorem 30.5); agreeing on `C^N` with one saturation spectrum (Theorems 30.7,
  30.9, 30.12); conjugacy and equivariant embeddings mirroring the Boolean order
  (Theorem 30.8); a ZFC theorem for one set field of size `ℵ_{ω+2}`
  (Theorem 30.11).

**Questions (Section 19).** Source 01's question on asymmetric gap pairs is
answered by source 03 (Corollary 8.6). Source 01's question on `SC^M ≅ SC^N` is
settled under Global Choice (Theorem 15.2); only weaker assumptions stay open
(Question 19.3). Source 08's remark that it lacks "a complete spectrum of all
omitted cut characters" is answered for a fixed pair by source 03. Questions 19.1,
19.5 and 19.6 are open; the finite version of 19.7 is answered by Corollary 16.7.
Batch-32 status notes: in a single universe, the clause of 19.7 on infinite
collections of regular thresholds is answered without forcing by
[first-kappa-coefficients](../../surcomplex/first-kappa-coefficients/)
(`fkc:sb:thm:involutions`, `fkc:sb:rem:univ`, under Global Choice). Question 19.6
is related to, not answered by, the classification of valued `Oz[i]`-preserving
involutions in surcomplex-field-automorphisms (`saut:fs:thm:main-involutions`,
`saut:fs:prop:conjugacy`). **Batch-37 status notes (dated pointers; no question
renumbered):**

- **19.2** is answered for one Cohen subset or collapse, any number of Cohen reals,
  GCH Easton products, Prikry, Namba under CH, and the intermediate grounds of
  sparse and countable GCH products. Open: arbitrary forcings, intermediate grounds
  of products with uncountable index sets at their accumulation points, the
  constructions without GCH, and the Fischer–Koelbing–Wohofsky realization
  questions.
- **19.4** is answered **negatively for real closed fields** (and pure fields):
  equal full gap spectra do not imply isomorphism (sources 12, 09, 11). What stays
  open: whether **equal real traces and equal full spectra** imply isomorphism
  (Question 31.2), the **pure-order version** (Question 31.4), and positive
  classification under further hypotheses. Within the countable coordinate family
  the full spectrum does classify (Proposition 25.17).
- **19.7** is answered for multicharacter spectra and families of actual old
  fields, of any set size, with one threshold and agreement on `C^N` or on any
  set-sized conjugation-stable core. Open: arbitrary prescribed spectra,
  infinitely many real forms with one identical full spectrum agreeing on `C^N`
  (Question 31.7), and any classification of real forms.

Section 31 records the 58 questions of sources 09–14, merged into 22: answered
inside the cluster are equal-spectra nonisomorphism for fields (31.1), the family
sizes asked by 11 and 14 (31.8 a, b) and the countable case of relative spectra at
accumulation points (31.11); richer inclusion patterns are partly answered (31.18);
the rest are open.

## What the report does not claim

Section 20 keeps every limitation of the four sources of Parts I–VII, per source:
15 items from 01, 16 from 03, 13 from 04, 11 from 08, and 5 added by the merge (60
in all). Section 32 does the same for Part VIII: 10 items from 09, 8 from 10, 8 from
11, 6 from 12, 7 from 13, 6 from 14 and 4 added by the merge (49 in all). In brief:

- The results are proposed contributions with written proofs. Priority is not
  certified, no named published conjecture is claimed solved, the report is not
  refereed, and **nothing is Lean-verified or formalized**.
- Classical surreal facts, quantifier elimination, standard forcing facts
  (distributivity, closure, the Prikry properties), the forcing notion of fresh
  functions (Fischer–Koelbing–Wohofsky), Ehrlich's absolutely saturated models,
  and the collection's class back-and-forth, conjugacy criteria and countably
  cofinal real form are credited, not claimed. The Boolean construction may be
  folklore in class forcing; Berenbeim's question comes from research notes, not
  a published conjecture.
- Part VIII imports, without reproof, Fischer–Koelbing–Wohofsky's Easton spectrum
  (Theorem 4.24, Propositions 4.3, 4.10), Prikry and Namba spectra (Theorems 7.21,
  7.23), the singular-product witness (Corollary 4.21, from Shelah 2000), the
  generalized Cohen spectrum (Proposition 6.1, used only for comparison), and
  Lévy–Solovay; the square chain condition (their Proposition 2.2) is reproved and
  credited. It does not classify all forcings, pure orders, real forms or
  involutions; it does not claim that equal real traces and equal spectra suffice
  for isomorphism; its class maps preserve no valuation, simplicity, exponential,
  derivation, Hahn summation or omnific integers; its continuum is `ℵ₁` in the
  GCH product constructions; Namba needs CH and Prikry a measurable.
- External means computed in `N`, not in a larger metatheory. No unrestricted class
  truth predicate, class Zorn lemma or class-valued recursion is used. The
  ground-bound lemma is not a covering property. Field elementarity is not
  `M ≼ N`.
- The gap invariant excludes cuts with proper-class cofinality; it recovers
  threshold and cofinality data, not the inner model, the forcing or sign lengths.
  `Add(κ,1)` is analysed at its first gap in Part IV and fully in Part VIII.
- The class isomorphisms are noncanonical. The real-form results do not classify
  real forms or involutions.
- Exponential and differential expansions are not treated. No topological
  completion theorem is claimed; an omitted cut is not a Cauchy sequence.
- The finite checks verify finite sign, interval, coding and index-set formulas
  only; there are no finite fresh signs, and no check tests freshness, forcing,
  cofinality, regularity, saturation or any class argument.

## Corrections to the sources' repository statements

Appendix A records those of sources 01–08, keeping the pin as provenance: the "no
matches" for `forcing`/`saturation` searches reported by 01 and 08 (the foundations
report contains "saturation for small cuts" and a subsection on class forcing,
neither of which contains these results); 01's count of forty reports plus four
drafts (the collection then had 44 report directories, including this report and
its sibling); the automorphism report's rewrite after the pin (its results are
cited here by current numbers and `saut:` labels); and the set-cut interpolation
criterion `saut:prop:conjugacycriterion`, which no source cites.

Section 33.2 records those of sources 09–14. This report was unchanged between
their pin and their placement, and every label and number they cite is present.
Two sentences overstate what the report said and are corrected where they are
printed: 09's "implication proposed as a possible classification principle in the
repository" (Remark 28.11) and 10's "suggestion that the least gap size … could
classify the fields" (Remark 25.25); Question 19.4 only *asked*. 11's shipped
`SOURCE_AUDIT.md` calls
`large-cardinal-embeddings-and-normal-forms/07-critical-point-defects-PROOF_STATUS.md`
a "guide"; it is a proof-status file, and nothing from it is used.

## Relation to the neighbouring reports and the formal project

**[surcomplex-field-automorphisms](../../surcomplex/surcomplex-field-automorphisms/)**
proves the class back-and-forth used in Part V (its Theorem 9.1,
`saut:thm:acfhomogeneity`), the fixed-field conjugacy criterion of its Section 10,
a real form with a countable cofinal subset (Theorem 10.2), and the criterion that
an involution is conjugate to `c` iff its fixed field has the set-cut interpolation
property (Proposition B.1, `saut:prop:conjugacycriterion`). That criterion already
implies the non-conjugacy statements of Theorems 16.2 and 16.3. What is new here
(Remark 16.4): real forms with no set-sized cofinal subset, several forms separated
from one another by the gap invariant, agreement with `c_N` on `C^N`, and
elementary equivalence with different spectra. Part VIII (Section 30) adds
arbitrarily large families of such forms, with one threshold and different spectra,
or one spectrum and different real traces. These continue, but do not settle,
that report's open real-form classification (its Section 14). Its batch-32
finite-symmetry sections classify, up to conjugacy, the involutions preserving the
valuation, Hahn summation and `Oz[i]` (`saut:fs:thm:main-involutions`,
`saut:fs:prop:conjugacy`); a note after Remark 16.4 and the status of Question
19.6 record that this concerns a different class and does not answer 19.6.

**[first-kappa-coefficients](../../surcomplex/first-kappa-coefficients/)** (`fkc:`;
batch 32) builds, in one universe and without forcing, a proper class of pairwise
nonconjugate pure-field involutions of `No[i]` from fields of surreals with fewer
than `κ` terms (`fkc:sb:thm:involutions`); its `fkc:sb:rem:univ` answers the
regular-threshold clause of Question 19.7 (status note there; Section 1.7). Part
VIII's families differ: actual old fields, multicharacter spectra, one common
threshold (Section 30.7).

**[foundations](../foundations/)**: Proposition 14.1 is an external version of
its Theorem 12.1 (`found:thm:discrete`). It needs only old positive lower bounds,
which hold where cut filling fails; the Lean form of that theorem's Cauchy clause
assumes small cut filling (`HasSmallCutFillers`). Remark 14.4 also relates the
results to its Section 7.7 (`found:sub:countable`): for same-ordinal outer
universes, bounds of outer sets of old numbers are absolute while cut filling is
not.

**[birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)**,
the sibling report of the same batch, studies bounded birthday fields with a
birthday symbol and their interpretation of hereditary sets. It proves, for every
same-ordinal outer model, that the first new birthday is the least ordinal
acquiring a new subset; this report keeps source 08's proof because 08 adds
`N`-cardinality and `δ ≤ cf^N β` (Remark 10.5). Part VIII's Section 26 computes
the gap pairs of the pure ordered cutoff fields `(No_{<θ})^M`, without a birthday
symbol, including asymmetric boundary gaps that also occur internally.

**[surreal-well-orders](../surreal-well-orders/)** (batch 81, its source 17)
computes the gap pairs of `No_{<θ}` for every infinite cardinal θ, singular θ
and θ = ω included (its Theorem 29.4, `swo:gs:thm:alphabet-gaps`); at regular
uncountable θ this is the case M = N of Lemma 26.1 (`univ:gs:lem:boundary`). A
dated note, "[Added 3 October 2026, batch 81: …]", after the paragraph following
that lemma records it (no label, number or page count changed).

**[cantor-families-of-surreal-subfields](../cantor-families-of-surreal-subfields/)**
(batch 90, `csf:`) also indexes real closed fields by the subsets of a set,
countable relative real closures `K_A` inside one countable surreal field, but
there embeddability is not inclusion as in Theorem 27.4
(`univ:gs:thm:boolean`): it is embeddability of colored rank orders
(`csf:thm:colored-coding`) and a complete analytic quasiorder
(`csf:thm:main`). Different objects, no shared proof; a dated note after the
paragraph following the proof of Theorem 27.4 records the contrast.

**[computable-surreals](../computable-surreals/)**: its `prop:topology` is the
universe-relative form of set-indexed convergence; the same-ordinal setting here
needs no lower-universe smallness. **[genetic-gaps-and-primitives](../../surreal/genetic-gaps-and-primitives/)**
uses "gap" for a proper-class gap of `No`; the gaps here are set-presented gaps of
`No^M` seen from `N`.

**Formal project.** The report sits in the surreal collection beside the Lean
library `Algebra/SurrealNumbers/Surreal/`. That placement confers no formal
status: the ledger `docs/FORMALIZATION.md` indexes the 57 numbered statements of
Parts I–VII, all **Pending**, with no Lean declaration mapped to any `univ:` label,
and Part VIII's statements are not indexed. No statement of this report is
formalized.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 106 pages with zero errors, zero LaTeX or package warnings, zero
overfull or underfull boxes, zero undefined references or citations, zero
multiply defined labels and zero duplicate PDF destinations. The log contains three
TeX information lines, `ignored: Infinite glue shrinkage found in box being split`,
which the `longtable` package emits when a long table breaks across pages (the
build of Parts I–VII alone had one; the delivered source 01 produces the same line).
The batch-32 cross-report notes (Section 1.7, after Remark 16.4, after Questions
19.6 and 19.7) are unnumbered; they took the build from 50 to 51 pages. Part VIII
took it from 51 to 105 pages; all 142 earlier labels keep their numbers.
The four batch-93 notes on Part II and Part III of the definable-surreals
report (after Proposition 3.1, Remark 10.5, Corollary 13.4 and Remark 28.11)
took it from 105 to 106 pages; all 572 labels and 24 citation numbers keep
their numbers.

Source 01's Makefile runs the same `latexmk` command on `article.tex` in the
current directory, so `make -f code/01-forcing-omitted-cuts-Makefile` from this
directory should build the report in place (not tested, since no `make` was
available; its `clean` target removes auxiliary files). The other Makefiles and
`code/11-finite-complements-build.sh` are kept only for provenance and **must not
be run here**: they name their packages' unprefixed files (`verify_finite.py`,
`code/check_finite.py`, `checks/finite_checks.py`, `verification_results.json`,
`finite_checks.json`), which are not shipped under those names, and their
`article.tex` targets would build this report in place: 10's runs `pdflatex` three
times and would leave auxiliary files here, and 11's `build.sh` changes to its own
directory (`code/`) and fails there.

The finite checks use only the Python standard library. **Run them on a copy of
this directory**, and pass explicit output paths: several scripts write output by
default, which would overwrite recorded files or leave new ones. From the root of a
copy, with the shipped names:

```sh
python code/03-fresh-sign-gaps-check_finite_signs.py                        # prints the JSON record only
python code/03-fresh-sign-gaps-check_finite_signs.py --output rerun-03.json # writes a new file
python code/04-universe-saturation-verify_finite_models.py > rerun-04.txt  # prints only
python code/08-forcing-saturation-verify_sign_code.py > rerun-08.txt       # prints only
python code/09-cohen-amplification-verify_finite.py --output rerun-09.json # prints only without --output
python code/10-isolated-coordinates-check_finite.py --output rerun-10.json # default: verification_results.json in the CWD
python code/11-finite-complements-finite_checks.py                         # ALWAYS writes code/results.json beside itself; no option
python code/12-real-traces-verify_finite.py --output rerun-12.json         # default: code/verification_results.json
python code/13-coordinate-spectra-verify_finite.py --output rerun-13.json  # prints only without --output
python code/14-relative-cutoffs-verify_finite.py --output rerun-14.json    # default: finite_checks.json in the CWD
```

(`py` or `uv run --no-project python` may replace `python` on Windows.) Source 03's
documented command `python check_finite_signs.py --output finite_checks.json`, and
the documented commands of sources 09–14 (`--output verification_results.json`,
`--output finite_checks.json`, `python3 checks/finite_checks.py`), would overwrite
recorded outputs if run in a delivered layout; source 11's script cannot be
redirected at all, so it must be run on a copy.

Recorded runs: source 03, 127 sign strings, 16,129 comparisons, 127 cone checks,
340 block-code cases and 1,744 nested endpoint pairs; source 04, 1,365 interval
nodes, 20,475 child pairs, 1,364 decodings and 65,025 cut/prefix comparisons;
source 08, 304,000 checks; source 09, 260,865 cone cases, 260,865 antisymmetry cases,
5,704 block round trips, 183,103 block-prefix cases and three symbolic examples;
source 10, 5,461 delimiter round trips, 36,409 prefix checks, 3 rejected inputs,
16,065 cone equivalences, 511 profile checks and 87,381 reversed-inclusion pairs;
source 11, 469,107 checks; source 12, 65,025 + 65,025 sign checks, 5,698 + 129,400
block checks, 2,047 + 11 ternary checks and the down-set embedding for the 1, 1, 3,
19, 219 labelled partial orders on at most four points (3,688 pair checks); source
13, 64,897 cone pairs, 1,365 + 22,302 + 5 block checks, 7,533 condition extensions
and 16,384 mask pairs; source 14, 619,026 assertions. All pass. For the merge of 22
September the suites of 03, 04 and 08 were rerun on a copy with Python 3.14.4; for
Part VIII the suites of 09–14 were rerun on a copy with Python 3.14.4 and the
commands above. Each output matched its recorded file except for line endings.

## Delivered files that still use delivery names

The shipped audit and record files of sources 09–14 are byte-identical to the
delivery and describe each source's **own** package: `article.tex`, `article.pdf`,
section and theorem numbers, and file names in them (`verify_finite.py`,
`verification_results.json`, `code/check_finite.py`, `checks/finite_checks.py`,
`checks/results.json`, `finite_checks.json`, `SHA256SUMS`, `README.md`, `Makefile`)
refer to that manuscript and its unprefixed files, not to this report. The
manuscripts, READMEs and PDFs are not shipped; the checksum manifests of 09, 10 and
11 (`SHA256SUMS`, `SHA256SUMS.txt`, `SHA256SUMS`) were verified and dropped at
placement. `13-coordinate-spectra-BUILD_REPORT.md` (22 pages, 121 link
destinations), `data/11-finite-complements-validation.json` (25 pages, 10 research
questions) and `data/14-relative-cutoffs-pdf_validation.json` (26 pages) describe
their sources' own PDFs, which are not shipped. `03-fresh-sign-gaps-PROOF_STATUS.md`
likewise describes source 03's own 21-page manuscript. The theorem numbers these
files cite are the sources' own; Section 21.1 and the statements of Part VIII give
the correspondence (for example, source 14's Theorem 9.1 is Theorem 25.15 here, in
the generality of source 13).
