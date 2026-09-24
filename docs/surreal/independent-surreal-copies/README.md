# Independent Surreal Copies and Arithmetic Intersections

**Prescribed Hahn cores, algebraic independence, and two transcendental descent obstructions**

This is a single-source research report dated 23 September 2026. It is built
from one manuscript, manuscript 06 of batch 31 (archive
`Surreal_Independent_Copies`, main file `independent_surreal_copies.tex`,
a 25-page PDF). The manuscript is pinned to repository commit `bcac55a` and
was placed in commit `9d28e28`. Author line: AI-assisted research draft.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed. The
report is AI-assisted and unrefereed. **Independent proof review and
formalization are pending.**

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 34 pages (unnumbered title page, contents
              page 1, then pages 2–33)
README.md     this guide
```

The package contained only the article, its PDF and a README. It shipped no
code, recorded data, audit or checksum list, so this report has no
verification suite to rerun. The delivered README and PDF are not shipped:
this README replaces the delivered one, and `article.pdf` is a build of this
text. The delivered README names the files `independent_surreal_copies.pdf`
and `independent_surreal_copies.tex`, which are shipped only as the rewritten
`article.tex` and its new build. It also mentions rendered pages and contact
sheets from its visual check; these are not shipped.

Every label in `article.tex` carries the prefix `isc:`. The source's 62
labels are kept, unchanged after the prefix. Twenty were added: three new
sections (`isc:sec:conventions`, `isc:sec:collection`, `isc:sec:nonclaims`),
seven appendix labels (`isc:app:report`, `isc:app:onesource`,
`isc:app:pinned`, `isc:app:literature`, `isc:app:checked`,
`isc:app:numbers`, `isc:app:files`), and ten labels on existing unlabelled
remarks and subsections (`isc:rem:base`, `isc:rem:floor`, `isc:warn:omega`,
`isc:rem:join`, `isc:rem:scaling`, `isc:rem:infinite`, `isc:sub:model`,
`isc:sub:bounded`, `isc:sub:formal`, `isc:sub:notmade`). That makes 82
labels. No theorem, section or equation number changed: the `.aux` numbers
of all 62 source labels were compared with a build of the delivered text.
No `isc:` label has a Lean mapping in the
[formalization ledger](../../FORMALIZATION.md).

Text added when the manuscript joined the collection is marked `[write]`.
Sections 1.5, 1.6 and 14 and Appendix A are new. Short `[write]` notes sit
after Proposition 4.4, Corollary 6.1, Theorem 6.2, equation (7.3),
Lemma 9.1 and Propositions 9.2 and 9.3, at the start of Section 10, after
Corollary 10.3, after research questions 1, 2, 6, 7, 8, 9 and 10, and in
Sections 1.4 and 13.3. No mathematical statement was changed and no symbol
was renamed.

## Setting and notation (Section 1.5)

The work is in NBG with global choice, with ZFC for sets. Every support is a
set, even when an exponent group or a field is a proper class, and the cut
property is never applied to proper-class sides. `K_k(G) = {x : supp x ⊆ G}`
is the **full** Hahn field on an additive subgroup `G ⊆ No`, written in
Conway's decreasing large-`ω` convention. `H` is a set-sized divisible
subgroup (not necessarily convex), and `L_k = K_k(H)`.
`A_k(H) = D_k ⊕ Π_k(H)`, with `D_R = Z` and `D_C = Z[i]`, is the integer
ring, so that `A_R(H) = L_R ∩ Oz`. `B_k(H)` is the ring of series whose
support is bounded above **in the t-exponents**.

Watch for these readings:

- **Convention switch.** From Section 9.1 to the end of Section 10 the source
  uses `t^h = ω^{-h}`. There the purely infinite part has *negative*
  `t`-exponents, and "bounded above" in `B_k(H)` means Conway exponents
  bounded **below**. Everywhere else `Oz` sits at *positive* Conway
  exponents.
- **Integer ring.** `A_k(H)` is the omnific-preserving report's `𝓡_Γ`
  (Part III) and the Diophantine report's `𝓡_{D_k}(k,Γ)`. It is **not**
  `𝓐_Γ = R ⊕ Π` there, and not the Diophantine report's `𝒜_k(Γ)`. `D_k` is
  a ring of integers, never a derivation.
- **Bounded-support ring.** `B_k(H)` is the bounded-support report's
  `𝓑_H(k)`, with the arguments in the other order.
- **Maps.** `Φ_h` is `M_{1,h} = J_{h,id}` of the omnific-preserving report.
  It is not the surcomplex-automorphisms report's Taylor map `Φ_d`, and not
  the large-cardinal report's `J`. The letters `h_α, G_α, Φ_α, K_α` name the
  abstract family of Theorem 3.4 in Sections 3–6, and the explicit family in
  Sections 7–8, where `h_α` is an *inner* map. `h_α` fixes `H` as a set of
  exponents, while `Φ_α` fixes `K_R(H)`.
- **Monomial-preserving** means that a Conway monomial goes to a Conway
  monomial with coefficient one (the omnific-preserving report's
  "exact-monomial"). It does **not** mean commuting with the omega-map:
  `Φ_0(ω) = ω^{ω^{1/2}}`, while `ω^{Φ_0(1)} = ω`.
- **Other letters.** `ψ(x) = 1/2 + x/(2(1+|x|))` is not that report's `μ_12`
  (its source 12's `ψ`). `κ` is `cf(H)` in Section 10, and an arbitrary
  uncountable regular cardinal in Section 11; it is never the large-cardinal
  report's critical point. `H` is not a convex subgroup `H_g`. `M = K_0K_1`
  is an ordinary compositum, not a monomial map `M_{χ,τ}`. `E`, `F`, `L`,
  `A`, `B`, `D` and `S` are local letters; Section 1.5 lists every use.
- **Strong** means that Hahn summability of set-indexed families is
  preserved. It is not convergence.

## What the report claims

Theorem numbers are those of the built `article.pdf`. They agree with the
delivered PDF. Remarks and warnings share the theorem counter, so the
classification is Proposition 4.4 and the set-sized theorem is Theorem 11.2.

- **Theorem A: prescribed independent copies.** For every set-sized
  divisible subgroup `H ⊆ No`, there are class maps `Φ_α : No → No`,
  `α ∈ On`. Each is a proper, strong, real-fixing, monomial-preserving
  ordered field embedding that fixes `L_R` pointwise. The images `K_α`
  satisfy `K_α ∩ K_β = L_R`, and every finite subfamily is jointly linearly
  disjoint over `L_R`. The rings `R_α = Φ_α(Oz)` satisfy `R_α = K_α ∩ Oz`,
  `R_α ∩ R_β = L_R ∩ Oz` and `Φ_α^{-1}(Oz) = Oz`. The complexifications give
  the same assertions over `L_C`; they commute with conjugation and preserve
  and reflect `Oz[i]`.
- **Theorem B: transcendental failure of fraction-field descent.**
  `Frac(R_α) = K_α`, but `Frac(R_α ∩ R_β)` is a proper subfield of
  `K_α ∩ K_β = L_R`. The extension is transcendental for every set-sized
  `H`, including `H = 0`. For `H ≠ 0` the smaller field already contains
  every real constant. For `H = Q`, `1 + Σ_{n≥1} ω^{-n!}` is a
  transcendental witness. Each copy separately supplies one denominator for
  the whole common field (Proposition 9.2), but no shared one does
  (Corollary 10.4). The same holds for the Gaussian copies.
- **Theorem C: a transcendental gap above the compositum.** For two explicit
  copies with `H = 0`, the full Hahn join `E = K(G_0 + G_1)` contains the
  countably supported
  `S = Σ_{n≥1} ω^{ω^{ψ(n)} - n ω^{7/2}}`, which is transcendental over the
  ordinary compositum `K_0K_1`. So the relative real algebraic closure of the
  compositum is a proper subfield of the join. The same `S` works after
  complexification. The proof uses a finite coefficient-field bound
  (Lemma 8.2, Theorem 8.3), not the invalid inference that every infinite
  sum lies outside a compositum.
- **Supporting results.**
  - Lemma 3.1 (a cut that avoids a set), Lemma 3.2 (a one-point ordered
    extension with avoidance) and Theorem 3.4 (an `On`-indexed family of
    ordered additive embeddings fixing `H`, with ranges independent over
    `H`, built by a set-state recursion).
  - Theorem 4.1 (the monomial lift `Φ_h`, whose image is exactly the full
    field `K_R(h(No))`, preserving and reflecting summability).
    Proposition 4.2 (it preserves and reflects `Oz`, and commutes with the
    omnific floor, the standard part and the modulus). Proposition 4.4
    (every strong, real-fixing, monomial-preserving embedding is a unique
    `Φ_h`).
  - Section 5: coset slices (Lemmas 5.2, 5.3), the theorem that
    `K(G_1)` and `K(G_2)` are linearly disjoint over
    `K(G_1 ∩ G_2) = K(G_1) ∩ K(G_2)` (Theorem 5.4, any coefficient field,
    set or class groups, no convexity), joint disjointness (Corollary 5.5)
    and polynomial-relation descent (Corollary 5.6).
  - Corollary 6.1 (any set of parameters lies in such a common field
    `L ⊇ R ∪ A`). Theorem 6.2 (the set-sized intersections in this class are
    exactly the `K_R(H)`). Theorem 6.3 (the Boolean meet diagram
    `E_J ∩ E_T = E_{J∩T}`, linearly disjoint, with Hahn join `E_{J∪T}`).
    Corollary 6.5 (independent choices are algebraically independent), and
    elementarity in the ordered-field language only.
  - Lemma 7.1 and Theorem 7.2 (the explicit family, with
    `Φ_0(ω) = ω^{ω^{1/2}}` and `Φ_1(ω) = ω^{ω^{7/2}}`, intersections `R`,
    `Z`, `C`, `Z[i]`). Lemma 8.1 (iterated Hahn coordinates at separated
    scales).
  - Lemma 9.1 (`Frac(Oz) = No`, uniformly over a set). Proposition 9.3
    (`Frac A_k(H) = Frac B_k(H)` for `H ≠ 0`). Lemma 10.1, Theorem 10.2
    (`1 + Σ t^{a_α}` is transcendental over `Frac B_k(H)` for any field `k`)
    and Corollary 10.3 (the factorial witness).
  - Theorem 11.2 (a conditional set-sized version in an `η_κ`-ordered
    divisible group of cardinality `κ`).
- **Research questions 1–10** (Section 12) and a proposed formalization
  decomposition (Section 13.2).

## What the report does not claim

Section 14 collects every non-claim with its location. It has 24 from the
source (S1–S24) and 8 added when the report joined the collection (W1–W8).
In brief:

- **The common field.** It is a full Hahn field on a set-sized divisible
  subgroup. It is not an arbitrary real closed or set-sized subfield, not
  the field generated by a parameter set, and not a non-Hahn subfield.
  Group sums are finite sums, and the joins are Hahn joins, not composita.
- **Strongness** is Hahn summability, not convergence.
- **Elementarity** is claimed only in the languages of ordered fields and of
  fields, formula by formula. Nothing is claimed in `(No, Oz)`, with the
  omega-map or with a derivation.
- **No compatibility** is claimed with the omega-map, the exponential,
  derivations, birthdays or simplicity. There is not even omega-map
  commutation: `Φ_0(ω) ≠ ω^{Φ_0(1)}`.
- **Scope.** No proper-class base `H` is treated. Theorem 11.2 is
  conditional on the existence of its group. No normalization, Picard group
  or projective module is computed. There is no class tensor product, class
  truth predicate or class-state recursion.
- **Not new.** The bounded-support transcendence mechanism of Section 10 is
  not new. It is reproved for the one-witness application. The non-fraction
  obstruction is L'Innocente–Mantova's Proposition 2.4.5. The ingredients
  are classical: the cut property, normal forms, Hahn arithmetic, the
  closedness criteria, a concrete saturation construction and standard
  Hahn functoriality. The coset slice is an elementary lemma, not a
  certified new theorem.
- **Status.** No priority is certified, no named conjecture is claimed
  solved, and there has been no peer review. There is no Lean code and no
  machine verification; the identifiers of Section 13.2 are proposals only.
  The delivered production checks (compiling, rendering and visual
  inspection) do not verify the mathematics.
- **Added at the write.**
  - (W1) No `isc:` Lean mapping, and no verification suite shipped.
  - (W2) The lifts, the Oz clauses and the classification are the
    real-fixing case of the omnific-preserving report's classification (no
    priority is claimed relative to it). Corollary 6.1 extends its
    parameter theorem without its topological assertions.
  - (W3) Lemma 9.1, Proposition 9.3, the coset slice and Section 10
    duplicate results of the Diophantine and bounded-support reports.
  - (W4) Real fixing is a choice; nothing is claimed about intersections of
    exact-monomial copies that move reals.
  - (W5) The large-cardinal report's joint-dependence question is not
    answered.
  - (W6) No question of the omnific-preserving or bounded-support reports is
    answered.
  - (W7) The source's statements about the collection are those of its pin.
  - (W8) The proofs were read during the write, but that reading is not an
    independent proof review.

## Relation to the neighbouring reports

Section 1.6 of the article gives these relations with labels.

**[omnific-preserving-automorphisms](../omnific-preserving-automorphisms/)**
(`opa:`). At the pin this report had no part on embeddings, so the source's
description of it as concerning "stabilizers and rigidity" was accurate.
Its Part III (`opa:as:`) was written in `20c4c9f`, after the pin.

- **Lifts.** The lifts `Φ_h` are the `ρ = id` case of the bottom-gap
  classification `opa:as:thm:classification`. Proposition 4.2's `Oz`
  clauses are its Step 5 (`opa:as:eq:classprops`). Proposition 4.4 is its
  uniqueness clause for real-fixing maps. The floor, standard-part and
  modulus clauses are not stated there.
- **Inner and outer levels.** Section 7's inner and outer levels are
  `opa:as:eq:innerlift` and `opa:as:lem:inner`, with
  `Φ_α = M_{1,ι_{σ_α}}`. The source's `ψ` is not `μ_12`.
- **Parameters.** Corollary 6.1 extends `opa:as:thm:parameters`, which gives
  two proper copies fixing `A ∪ R`. Here there is an `On`-indexed family
  whose exact intersection is a full Hahn field, jointly linearly disjoint
  over it.
- **Complex version.** The complex clauses are the `ε = 1`, `ρ = id` case of
  `opa:as:thm:complexembed`, parallel to `opa:as:cor:complexcopies`.
- **Real fixing is a choice.** The explicit ranges have a nonzero bottom
  gap, which contains `ω^{3α}` and, for `α = 0`, is the group of finite
  surreals. By `opa:as:thm:taylorcriterion`, copies with the same exponent
  map could therefore also move reals. The source takes `ρ = id`, which is
  consistent. Theorem 6.2 depends on this hypothesis
  (`opa:as:prop:overlap`).
- **Questions.** None is answered.
  - Research question 2 is the pair version of `opa:as:q:conjugacy`.
  - Research question 9 is `opa:as:q:elementary` for these maps.
  - Research questions 6 and 7 lie inside `opa:as:q:exp`.
  - Theorem 6.3 touches `opa:as:q:composition` (image inclusion) inside one
    family only.
  - Research question 1 is related to `opa:as:q:units`, but asks about
    intersections.

**[transcendence-over-bounded-support](../transcendence-over-bounded-support/)**
(`bst:`), unchanged between the pin and batch 31; batch 32 added its Galois
part (its Sections 11–19), which is not used here.

- Section 10's one-witness gap duplicates `bst:cor:onegap`, and the
  one-series case of `bst:thm:mainintro` (`bst:thm:independent`), as the
  source says. The single-series form at uncountable cofinality over an
  arbitrary coefficient field, finite fields included, is not stated
  there; its proof is that report's tail estimate and root count.
- The factorial witness is also used in `bst:thm:actualreal`, and, as a mere
  non-fraction, in `opa:as:ex:smallfrac`.
- Proposition 9.3 is the localization of `bst:prop:localdensity`. Since
  batch 32 that report also prints the general form, for every field `K` and
  every unital subring `D ⊆ K`, as `bst:gr:prop:fractions`.
- The coset slice is `bst:eq:projection`, and its linearity is
  `bst:lem:projection`. Theorem 5.4 (disjointness over the full Hahn field
  of the intersection group, with no cofinality hypothesis) is not stated
  there.
- Research question 8 is that report's programme.

**[omnific-diophantine-geometry](../omnific-diophantine-geometry/)**
(`odg:`). Lemma 9.1 is `odg:thm:fractions`.

**[large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)**,
placed after the pin, with its write phase in progress. It is cited by
name and question title, not by label.

- Its strong map `H_j` is the lift `Φ_h` with `h = J`.
- Its question "Joint algebraic dependence of the images" asks whether
  `J(No)` and `H_j(No)` are linearly disjoint over the common field. That
  question is related to Theorem 5.4 but **not answered**: `J(No)` is not a
  full Hahn field on a subgroup, and the common field there is not one
  either.

**New research questions.** Questions 1, 3, 4, 5 and 10 are new. Question
10 overlaps `opa:as:q:formal` in its Hahn-field kernel.

## Provenance (Appendix A)

- **Pin and placement.** The pin is
  `bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59`. The manuscript was placed as a
  new report because it answers no named question and because its spine
  (independence, exact intersections and descent of full copies) belongs to
  no existing report.
- **Repository statements at the pin.** The source compared itself with the
  catalogue, the omnific-preserving report and the bounded-support report at
  that revision. Its statements about them stand as of the pin
  (Appendix A.2); the later Part III of the omnific-preserving report is
  what Section 1.6 adds.
- **L'Innocente–Mantova.** This reference was checked on arXiv version 5 of
  22 January 2024. The journal DOI `10.1016/j.aim.2024.109513` is listed
  there; the volume number was not checked. Fact 2.1.1 is the closedness
  criterion. Proposition 2.4.5 states, for the `κ`-bounded Hahn field, that
  `Frac(Z + K((G^{<0})))` is the whole field if and only if `cf(G) ≥ κ`.
  For a set-sized `G` it therefore gives the non-fraction obstruction (not
  transcendence), with `Frac(Oz) = No` as the class case. The source's
  citations of it are accurate.
- **Ehrlich–Kaplan.** Only the title and authors were checked. Gonshor, van
  den Dries–Ehrlich, Marker and the encyclopedia page were not checked.
- **Checks during the write.** The main proofs (Lemmas 3.1–3.2, Theorem
  3.4, Section 4, Section 5, Theorems 6.2–6.3, Sections 7–10 and Theorem
  11.2) were read when the report was written, and no error was found. The
  only finding is an understatement: Proposition 9.2 says that no common
  denominator satisfies both containments, and in fact it satisfies
  neither.

## Build

TeX Live or MiKTeX with lmodern, microtype, geometry, amsmath/amssymb/amsthm,
mathtools, mathrsfs, enumitem, booktabs, array, longtable, xcolor, fancyhdr,
xurl, hyperref and cleveref. No external figures, bibliography database or
downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX 1.40.29) has 34 pages. It has no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull or underfull boxes. The
delivered text builds equally cleanly to 25 pages. Running pdflatex three
times instead of latexmk also resolves the references and the table of
contents.

The delivered README reports its own build with pdfTeX 1.40.26 and latexmk,
with no undefined references, overfull boxes or compilation warnings. It
also reports a visual inspection of all 25 rendered pages, using contact
sheets and selected full-size pages. Those renderings are not shipped.
These production checks do not verify the mathematics. There is no
verification suite to run.
