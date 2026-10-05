# Naming Elementary Embeddings

**Atom components, Replacement and reflection: exact criteria and sharp
cofinality thresholds (Part I); commuting actions and Replacement: exact
cofinality thresholds, definable kernels and uniform naming (Part II);
relations among injections: definable atoms, connected types and Replacement
(Part III)**

A research report dated October 2026, built from four manuscripts on
expanded-language axiom schemes in urelement set theory, prompted by Elliot
Glazer and Bokai Yao's *Reflection Principles in ZFU* (arXiv:2602.21970) and
Glazer's *Global choice is not conservative over local choice for Zermelo set
theory* (arXiv:2312.11902). Part II is written as a continuation of Part I
and answers its Question 10.4. Part III merges two independent manuscripts
written against Parts I–II, which answer Part II's Question 23.3 and, with
pure real parameters, its Questions 23.1–23.2 and Part I's Question 10.1. All
four author lines read "Research manuscript prepared with ChatGPT", except
that Part I's also reads "Prepared for Vladimir Reshetnikov" and source 04's
reads "Research manuscript prepared for Vladimir Reshetnikov" (its PDF
metadata: "prepared with ChatGPT").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 89, manuscript 05 | `Naming_Elementary_Embeddings_Research.zip` (330,868 bytes; inner directory `Naming_Elementary_Embeddings/`, main file `article.tex`, 1041 lines, 27-page US Letter PDF), arrival commit `8ea27d6c0` | `2b7b388ba` (`2b7b388ba81a3355b19a7c2d2fe797e92f572355`, "Catalogue batches 81 to 86", quoted in Section 9.1 and in the repository URLs of the bibliography) | `23adb85f9` | Part I (Sections 1–11, Appendices A–C), numbering unchanged |
| 02 | batch 93, manuscript 01 | `commuting_actions_replacement.zip` (690,120 bytes; inner directory `commuting_actions_replacement/`, main file `commuting_actions_replacement.tex`, 1,283 lines, 31-page US Letter PDF), arrival commit `2faa3b37a` | `a9ab9a698` (`a9ab9a69872c2fb7464097af32fd7b76c75cb030`, "Audit eight arithmetic compiler reports and the complete degree-12 matrix DAG", 4 October 2026; quoted in Section 12.3, Appendix E and the bibliography) | `47a77daba` | Part II (Sections 12–23, Appendices D–E), in full |
| 03 | batch 96, manuscript 05, *Relations, Definable Atoms, and Replacement* | `atom_actions_research.zip` (594,987 bytes; inner directory `atom_actions/`, main file `atom_actions.tex`, 1,761 lines, 45 labels, 28-page US Letter PDF), arrival commit `26e036956` | `715a716a3` (`715a716a3002b1e9f28daa2d81c009a392851b94`, "Construct a non-dyadic outer family with actual compiler constants fixed", 4 October 2026; quoted in Section 24.1 and the bibliography) | `27f200305` | Part III (Sections 24–37, Appendices F–G), merged with 04; the base |
| 04 | batch 96, manuscript 06, *Relations among Commuting Injections* | `commuting_injections_research.zip` (309,489 bytes; inner directory `commuting_injections/`, main file `commuting_injections.tex`, 1,887 lines, 51 labels, 24-page US Letter PDF), arrival commit `26e036956` | `715a716a3` (the same commit; quoted in Section 24.2 and the bibliography) | `27f200305` | Part III, merged with 03 |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection, beside the formal projects it continues, confers no formal
status. The finite checks of all three Parts were executed (by the packages
and again at the writes); the infinite theorems rest on the written proofs
only. **Historical priority is not established.** Part II imports one
existence theorem from group theory without proof (Remark 18.4, below). Part
III answers Questions 23.1 and 23.2 of Part II and Question 10.1 of Part I
**only with pure real parameters**; in their ordinary form they stay open
(Section 24.2 of the article).

## The question

Let `A` be an external set of atoms, `κ` an infinite cardinal with `|A| ≥ κ`,
and `M_κ(A)` the objects whose transitive closures involve fewer than `κ`
atoms: Yao's kernel-ideal model of urelement set theory with Replacement and
choice (`ZFCU_R`, without Collection). Every injection `f : A → A` lifts to a
canonical amenable elementary self-embedding `j_f` fixing every pure set.
When finitely many such lifts are *named*, so that axiom schemes range over
formulas containing their symbols, which set-existence schemes survive?
Part II asks what commutation, invertibility and group structure of the named
maps contribute, and what happens when a whole group action is named by one
uniform evaluator. Part III asks what *relations* among commuting named
injections (such as `f^m = g^n`) do to the number of connected component types
and so to the thresholds, and which atoms and objects are definable once the
maps are named.

## What it proves

### Part I (batch 89)

- **Theorem 2.4** (Yao's theorem, specialized and credited): `M_κ(A)` satisfies
  `ZFCU_R`; internal and external cardinalities agree.
- **Theorems 3.2, 3.4, Proposition 3.5:** the lifts `j_f` are elementary and
  amenable; the initial elementary self-embeddings are exactly the `j_f`;
  `M_κ(C) ≼ M_κ(A)` iff `|C| ≥ κ`. **Theorem 3.6:** `j_f` is
  parameter-definable iff `f` moves fewer than `κ` atoms.
- **Lemma 4.1:** countably many component types for one injection, continuum
  many for two (already for two permutations).
- **Theorem 5.1 (component-profile criterion, the principal claim):** for
  `κ > ω`, Replacement in the expanded language holds iff the union
  `D_κ(f)` of the small type blocks has size `< κ`; for `κ = ω`, iff every
  component is finite and `D_ω(f)` is finite.
- **Theorem 6.1:** every one-name expansion preserves Replacement iff
  `cf(κ) > ω`; every expansion by `r ≥ 2` names iff `cf(κ) > 2^ℵ0`.
  **Corollary 6.3:** at the cutoff `ℵ2`, universal two-name preservation is
  equivalent, externally, to CH; a characterization, **not a proof or
  refutation of CH**. **Corollary 6.4:** the same threshold for countably many
  names.
- **Lemma 7.2, Corollaries 7.3 and 7.6, Theorem 7.5:** the exact domain-size
  spectrum of Collection, with failure at limit cutoffs already in the
  `Δ0` fragment of the base language; full Collection iff `κ` is an
  uncountable successor and fewer than `κ` component types are realized.
  **Theorem 7.7:** full transitive reflection has the same criterion.
  **Corollary 7.9:** two individually safe automorphisms can be jointly unsafe
  (at `ℵ1`); Example 7.10: joint Replacement can survive while joint
  Collection fails.
- **Proposition 8.1:** two superficially similar partial-reflection schemes
  differ (one is `Δ0` Collection).
- Section 9: a six-layer ProveIt formalization route (a proposal); Section 10:
  twelve research questions; Appendices A (an explicitly bounded
  injection-to-atoms formula), B (dependency audit), C (finite checks).

### Part II (batch 93)

Manuscript item `n.k` is item `(n+11).k` here.

- **Lemmas 15.1–15.2:** components of `r` commuting permutations are the
  `ℤ^r`-sets `ℤ^r/K`, countably many types; each stabilizer class is
  parameter-free definable at every cutoff.
- **Theorem 15.3 (answers Part I's Question 10.4 in full):** every `r`-tuple of
  commuting permutations keeps expanded Replacement iff `cf(κ) > ω`, with the
  boundary cases `κ = ω` and singular `κ` of countable cofinality.
  Corollary 15.4: a finite group of named permutations is harmless at every
  cutoff.
- **Lemmas 16.1–16.2, Theorem 16.3:** commuting `s` permutations and `t`
  injections: threshold `cf(κ) > ω` for `t ≤ 1`, `cf(κ) > 2^ℵ0` for `t ≥ 2`,
  witnessed by rigid lattice staircases `U_S` (Figure 1). **Theorem 16.4:**
  for `ω < κ`, `cf(κ) ≤ 2^ℵ0`, two commuting proper injections, each harmless
  alone, with only pure fixed points, jointly destroy Replacement.
- **Theorem 17.1 (answers Part I's Question 10.1 for commuting
  permutations):** the atom kernel of definable closure of `ā` is exactly
  `G·⋃ker(a_i) ∪ D_κ`, at every cutoff; Example 17.4: false for a ray at `κ = ω`.
- **Theorem 18.2:** for a finitely generated group named by generators, every
  action keeps Replacement iff `G` is finite (`κ = ω`), iff
  `cf(κ) > τ(G)`, the number of conjugacy classes of subgroups (`κ > ω`).
  Proposition 18.3: `τ(G)` is finite, `ℵ0` or `2^ℵ0` for countable `G`.
- **Propositions 19.1–19.2, Theorem 19.3, Proposition 19.4, Corollary 19.5:**
  separate names versus one uniform evaluator `E(g,x)` for a countable group;
  for `⊕_ω C_2` acting with orbits of at most two atoms, separate names keep
  Replacement at every cutoff while the amenable evaluator destroys it
  whenever `cf(κ) ≤ 2^ℵ0` (and preserves it when `cf(κ) > 2^ℵ0`); for finitely
  generated groups the evaluator is definable; finite-orbit actions are
  governed by `τ_fin(G)`, at `κ = ω` by finiteness of the profinite
  completion.
- **Theorem 20.1:** commuting tuples with at most one injection: full
  Collection iff full reflection iff `κ` is an uncountable successor (a
  consequence of Part I's Theorems 7.5 and 7.7).
- **Theorem 21.1 (answers the fixed-action part of Part I's Question 10.10):**
  set forcing that keeps `κ` a cardinal preserves the expanded-Replacement
  verdict of a fixed ground action.
- Section 22: formalization milestones (proposals) and the finite checks;
  Section 23: thirteen questions (twelve of the manuscript and one added at
  the write, Question 23.13); Appendices D (conventions and explicit
  witnesses) and E (source and verification record).

### Part III (batch 96)

Two manuscripts merged (union): every result, proof, example, remark,
question and non-claim of both is printed; a result proved by both is printed
once, with source 04's proof as a marked second route. A "Sources" line after
each numbered item names the manuscript items it prints. Notation follows
source 03 (`M` presented monoid, `P` its cancellative image, `G` its group
completion, `U = P ∩ (−P)`, `d = rank(G/U)`; source 04 swaps `M` and `P`).

- **Theorem 26.2, Lemma 26.3** (source 03): one formula `Code(c,a)` defines a
  pure real `c_a` (the signed-word equality diagram at `a`); `c_a = c_b` iff
  the rooted components are isomorphic iff `b` is in the centralizer orbit
  `𝒵a`, at every cutoff including `κ = ω` for infinite components; and
  `|𝒵a| = μ_t δ_t` (multiplicity times automorphism-group order), which
  generalizes Lemma 56.3 of Part VIII of `birthday-cutoffs-and-hereditary-sets`.
- **Theorem 27.1, Corollary 27.2** (source 03): for every finite tuple of
  injections, commuting or not, and every infinite `κ`, the atom kernel of
  the objects definable from `ā` **and finitely many pure reals** is
  `Sat(B) ∪ D^pt_κ` (component closure of the parameter kernels, plus the atoms
  whose centralizer orbit has size `< κ`); `D^pt_κ = D_κ(f)` for `κ > ω`.
  **Theorem 27.3:** the atoms definable from finitely many atoms and pure
  reals; **Proposition 27.4:** at `κ = ω` ordinary definability reduces to the
  definability of rooted codes; **Theorem 27.5:** at `κ = ω` the objects
  definable from arbitrary parameters and arbitrary pure parameters are exactly
  those fixed by the centralizer elements fixing the parameters.
- **Corollary 28.1** (source 03): for group actions, through `N_G(H)/H`; the
  infinite dihedral example (Section 28.1) and two involutions, each harmless
  alone, jointly failing Replacement at `κ = ω` (Section 28.2).
- **Lemma 29.1, Theorem 29.2, Corollary 29.4** (both sources): injective actions
  see only the cancellative image; a connected injective action is a
  `P`-stable subset of some `G/H`, up to translation; local automorphisms are
  translation periods.
- **Lemma 30.1, Theorem 30.4 (answers Part II's Question 23.3; both sources):**
  the number of connected labelled types is `|Sub(G)|` (`G` finite), `ℵ0`
  (`G` infinite, `d ≤ 1`), `2^ℵ0` (`d ≥ 2`), with a rigid continuously coded
  Cantor family in the last case (**Theorem 30.6**, source 04; Figures 2–3);
  Example 30.7: finite generation is necessary (`ℚ≥0`).
- **Theorem 31.1, Corollary 31.2** (source 04): at a fixed localization
  stabilizer the count is one, finite or continuum; finitely many rigid types
  iff `d ≤ 1`.
- **Theorem 32.1** (both sources): `d = dim span` of the nonnegative rational
  kernel cone of the relation matrix, `G/U ≅ ℤ^J/row(B_J)`, unit certificates;
  the trichotomy is decidable from a finite commutative presentation.
  Lemma 32.2: positive circuits of size at most `rank + 1` suffice. Table 6:
  fourteen example presentations.
- **Theorem 33.1** (both sources): for commuting injections with `f^m = g^n`,
  `g_0 = gcd(m,n)`: `σ_1(gcd(g_0,k))` finite types of size `k`; `div(g_0)`
  bilateral types; `Σ_{e|g_0} Neck(m/e, n/e)` proper types (cyclic weak
  compositions); rational Catalan in the coprime case. **Theorem 33.4**
  (source 03): the automorphism group of a proper component is `C_δ`;
  **Theorem 33.5** (source 04): exactly `Neck(m/δ, n/δ)` proper types have it;
  Proposition 33.6 (defects `n/e`, `m/e`); Corollary 33.7 (generating
  functions of all finite actions).
- **Theorem 34.1** (both; Part I's Theorem 5.1 reproved); **Theorem 34.3**
  (both): every action keeps Replacement for all `κ` (`G` finite), iff
  `cf(κ) > ℵ0` (`G` infinite, `d ≤ 1`), iff `cf(κ) > 2^ℵ0` (`d ≥ 2`), with
  faithful witnesses; it contains Part I's one-name threshold and Part II's
  Theorem 16.3 (`d = t` there). **Proposition 34.4, Corollary 34.5:** Collection
  and reflection, fixed and universal; Example 34.6.
- **Theorem 35.1** (source 04): for `d ≤ 1` forcing adds no new connected
  types; for `d ≥ 2` it adds one iff it adds a real.
- Section 36: what was checked, formalization orders (proposals); Section 37:
  seventeen questions (the 24 of the sources merged into 16, plus Question
  37.17 added at the write); Appendices F (notation, reproducibility) and G
  (source audit).

## What is not claimed

- The kernel-ideal construction is Yao's (Definition 24, Theorems 26–27 of
  arXiv:2303.14274), credited; the lifting idea is not claimed new. The
  component-profile criterion and its consequences are proposed
  contributions, unreviewed, with literature priority unverified. Part II
  reproves Part I's foundations and the profile criterion as prior work, and
  its Collection/reflection theorem is a consequence of Part I's. Part III
  reproves the same foundations and the fixed-action Replacement, Collection
  and reflection criteria with attribution.
- No Lean development; Glazer and Yao are cited researchers, not authors or
  endorsers. No open problem of Glazer's or of Glazer–Yao is claimed solved,
  and their choiceless separation diagram is neither reproduced, recovered,
  strengthened nor contradicted. Part II claims the resolution of the
  repository's question only, not worldwide priority; the "independent
  review" in its preparation is not external review. Part III's sources say
  the same: their "separate ChatGPT agents" and "multiple internal proof
  reviews" are process statements, not external review.
- The models are defined externally over a set of atoms in a well-founded
  ambient universe **with choice**; the atoms are internally a proper class.
  Elementarity, reflection and definable closure are schemes; no truth
  predicate and no set of all class maps are assumed.
- The classification is local to this model family: not all urelement
  models, all amenable classes, or all elementary embeddings (noninitial
  embeddings are not classified).
- The CH corollary is a characterization only; nothing contradicts results
  about embeddings of pure universes.
- Part II's group-theory section does not classify groups with countably many
  subgroups or solve subgroup-space problems. **Remark 18.4 is imported, not
  proved:** the existence of a finitely generated infinite group with all
  proper nontrivial subgroups conjugate (so `τ(G) = 3`), due to Ivanov and
  Ol'shanskii, was read in Smith (Glasgow Math. J. 37, 1995, p. 69); the
  primary construction was not consulted by the manuscript or at the write.
  The write checked Smith's attribution on the publisher's freely visible
  first page and moved the missing primary check to Question 23.13. Only the
  claim that the two clauses of Theorem 18.2 genuinely differ depends on it.
- Theorem 21.1 does not assert that the old class model is unchanged,
  formula-by-formula absoluteness, or absoluteness of Collection under
  collapses. Theorem 35.1 likewise asserts no preservation of the schemes of a
  fixed expansion under forcing.
- **Part III's definability theorems are with pure parameters.** Theorems 27.1
  and 27.3 use finitely many pure real parameters, Theorem 27.5 arbitrary pure
  parameters and only `κ = ω`; ordinary definability is open (Question 37.4).
  Source 03's argument that the *parameter-free* definable kernel of a rigid
  continuum family is countable is metatheoretic, not a theorem of the
  framework; it is kept as prose with a dated note and recorded as Question
  37.17.
- Part III's type-count theorem assumes a finitely generated **commutative**
  monoid (Example 30.7 shows finite generation is needed); its decision
  procedure is for commutative presentations only and decides no cofinality
  inequality. **Source 04's "commutative answer" to Question 23.5 is not
  one:** Theorem 32.1 decides the commutative-*monoid* analogue; the
  commutative case of Question 23.5 itself (finitely generated abelian
  groups) was immediate before, and the question stays open beyond it.
- Part III's sources do not strengthen the Glazer–Yao separations and say
  nothing about noninitial embeddings or noninjective maps; source 03's "no
  inspected source states the trichotomy" is a limited literature search,
  and the localization, cone, group-action, necklace and rational Catalan
  ingredients are classical and credited.
- The finite Python checks of all Parts are regression tests (component
  swaps and real-marker coding; staircase prefixes, subgroups of `(ℤ/4)^2`,
  characters of `F_2^5`; presentation matrices, cyclic compositions,
  subgroup counts, commuting permutation pairs), **not** verification of any
  infinite-cardinal theorem, of Replacement, of a forcing theorem or of any
  independence claim. The PDF build is not claimed bit-reproducible.

## Checks made at the writes

Part I, on 3 October 2026:

- **Repository claims.** The three files the manuscript read are
  byte-identical at the pin and at the write:
  `SetTheory/ZF/Lean/ZF/Zf.lean` (blob `b33db57cf`),
  `SetTheory/BoundedConsistency/README.md` (`ebb5d1bfa`) and
  `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings/README.md`
  (`554357db9`). The manuscript's descriptions of them (Sections 1.1, 8, 9.1)
  are accurate: the declarations `Sep_form`, `Func_form`, `Image_form`,
  `Repl_form`, `ZFax`, `ZFprov`, `ZFax_s` exist; the bounded-consistency
  README states a numeralwise endpoint reached by partial satisfaction
  rather than reflection, and says its quantifier-group rank is strictly
  finer than the Levy hierarchy; the self-embedding report is marked
  unrefereed and not formalized. No repository statement is contradicted;
  nothing needed retraction.
- **arXiv.** arXiv:2602.21970 (Glazer–Yao) lists one version, v1 of
  25 February 2026 (math.LO), with the cited title and authors;
  arXiv:2303.14274 (Yao) lists three versions, the cited v3 of 18 June 2023;
  arXiv:2312.11902 (Glazer) lists three, the last of 7 January 2024. The
  page references to Yao's dissertation were not rechecked.
- **Delivered hashes.** `data/BUILD_AUDIT.json` lists seven delivered files;
  all seven hashes match the delivery, and the four of them shipped
  unchanged (`SOURCE_AUDIT.md`, `code/build.sh`, `code/verify_finite.py`,
  `data/verification_results.json`) still match; the record does not list
  itself.
- **Finite checks** rerun on a scratch copy (Python 3.14.4, under a second):
  125,582 assertions passed; the report equals the recorded one except for
  `python_version` (3.14.4 against the delivered 3.13.5).
- **Personal data.** `SOURCE_AUDIT.md` mentions that "the requested LinkedIn
  page did not provide usable content"; it gives no URL, and no LinkedIn URL
  or e-mail address is in any shipped file.

Part II, on 4 October 2026:

- **Repository claims.** The manuscript's quoted blob `5426fc8da5f…` is this
  report's `article.tex` at its pin; it differs from Part I as printed only by
  the two batch-90 dated notes (`e50dde15b`), so every number it quotes
  (Theorems 5.1, 6.1, 7.5, 7.7; Questions 10.1, 10.4, 10.10) is Part I's.
  `Zf.lean` is blob `b33db57cf` at both pins and at the write, and declares
  `Sep_form`, `Func_form`, `Image_form`, `Repl_form`, `ZFax`, `ZFprov`; no
  urelement model is formalized. "Twelve proposed questions remain
  unanswered" was true at the pin. No repository statement is contradicted.
- **Overlap unknown to the source.** Part VIII of
  `birthday-cutoffs-and-hereditary-sets` (labels `hset:ns:`) was written in
  `1404038df` (10:57), after this manuscript's pin (10:45); its files were
  staged in `12076b2e8` without its text. See "Relation to the repository".
- **Smith 1995.** The publisher's freely visible first page of
  doi:10.1017/S0017089500030408 attributes to Ivanov and Ol'shanskii
  finitely generated infinite simple groups with all proper nontrivial
  subgroups conjugate. The paper itself and Ivanov–Ol'shanskii's chapter
  (doi:10.1017/CBO9780511661846.004) are paywalled and were not read.
- **Finite checks** rerun on a scratch copy (Python 3.14.4, about 2 s):
  `PASS`, 347,278 explicit checks; the output is byte-identical to
  `data/02-commuting-actions-verification_output.txt`.
- **Figure** regenerated on a scratch copy with Matplotlib 3.10.8
  (`uv run --no-project --with matplotlib==3.10.8`, about 14 s with the
  environment cached): `staircases.pdf` byte-identical to
  `figures/02-commuting-actions-staircases.pdf` (34,717 bytes; fonts
  embedded as TrueType, no Type 3); `staircases.png` pixel-identical to
  `figures/02-commuting-actions-staircases.png` (RGBA, 1970×1659; Pillow
  difference box empty) but differently compressed (116,011 against 127,971
  bytes).
- **Numbering.** A build of the pristine manuscript was compared label by
  label with this build: every non-equation item `n.k` became `(n+11).k`,
  Appendices A–B became D–E, Figure 1 stayed Figure 1; the manuscript's
  consecutive equations (1)–(17) became (12.1), (13.1)–(13.2),
  (14.1)–(14.2), (15.1), (16.1)–(16.5), (17.1), (18.1)–(18.2),
  (19.1)–(19.3). All 66 labels of Part I keep their numbers (compared
  against a build of the committed text).
- **Personal data.** Appendix E says that a LinkedIn page "identifies the
  researcher" (Glazer); it gives no address, and none is recorded anywhere
  in the report.

Part III, on 4 October 2026:

- **Repository claims.** Both sources are pinned to `715a716a3`, an ancestor
  of the placement; this report's `article.tex` at the pin is blob
  `af39ad7c6`, identical to the text before Part III was added, so every
  number the sources quote (Questions 23.1–23.3, 23.5; Theorems 5.1, 7.5, 7.7)
  is this report's; `birthday-cutoffs-and-hereditary-sets` is unchanged since
  the pin. Their statements about the repository are true: Part II's questions
  carry the labels source 03 names; Part II "settles free commuting
  signatures" (Theorem 16.3); the fixed-action criteria are Part I's Theorems
  5.1, 7.5, 7.7 and Part II's Theorem 14.2, the reservoir argument Part I's Section 7;
  Part VIII's Theorem 59.1 classifies kernel-bounded Replacement for uniformly
  named group actions at `κ = ω`; the root README says that exploratory
  computations enter the trusted boundary only through proved checkers. No
  repository statement is contradicted.
- **Proofs.** The placement (`27f200305`) read the main proofs of both
  sources and checked, by an independent program, the automorphism spectra of
  proper types for `m, n ≤ 8` (source 03's drop sequences against source 04's
  gap words and Theorem 33.5), the subgroup counts `σ_1(gcd(k,g_0))`, the
  labelled commuting pairs of (33.8) for `N ≤ 5`, the rational Catalan counts
  to `(5,7)` and every table entry; no wrong claim was found. The write
  checked the consistency of Theorem 27.1 with Part II's Theorem 17.1 and
  Example 17.4 (note after Corollary 27.2), a finite-cutoff step of the proof
  of Theorem 34.1 (note after it), the index ranges of Theorem 33.5 (note
  after it) and Theorem 34.3 against Parts I–II's thresholds (note after it).
- **Finite checks** rerun on scratch copies: source 04's
  `verify_results.py` (Python 3.14.4, standard library, under a second):
  `PASS: 148 exact cases`, output byte-identical to
  `data/04-commuting-injections-verification.json`; source 03's
  `verify_presentations.py` (`uv run --no-project --with sympy==1.14.0`,
  Python 3.13.5, about 5 s): assertions pass, "Verified 14 presentation
  examples", ideal counts 2, 5, 7, 14, 30, 64 composition pairs, infinite-type
  totals 3, 5, 6, 7, 13, 16; the output equals
  `data/03-atom-actions-verification_results.json` after removing CR bytes,
  except for the field `"python"` (3.13.5 against the delivered 3.12.14).
- **Figure.** Source 03's `make_figure.py`, run on a scratch copy with
  Matplotlib 3.10.8, regenerated `antichain_upsets.pdf` equal to
  `figures/03-atom-actions-antichain_upsets.pdf` except for its
  `CreationDate` (fonts embedded as TrueType, no Type 3) and
  `antichain_upsets.png` pixel-identical to
  `figures/03-atom-actions-antichain_upsets.png` (RGBA, 1436×752; Pillow
  difference box empty; 45,890 against 49,920 bytes). Source 04's figure is
  TikZ code in the article.
- **Union.** Every 6-word sequence of running text was compared between each
  source and Part III: 96% of source 03's and 88% of source 04's sequences
  appear verbatim; the rest are headings, the statements merged from both
  sources, the merged table, bibliography entries and source 04's text
  rewritten in source 03's letters. Every numbered item of both sources is
  accounted for in a "Sources" line.
- **Numbering.** All 146 labels of Parts I–II keep their numbers (compared
  via `.aux` against a build of the committed text); Part II now starts on
  page 30 (29 before), because Part I gained dated notes.
- **Personal data.** Source 03 says that "the LinkedIn address supplied with
  the research request did not provide readable contents"; it gives no
  address, and none is recorded anywhere in the report.

## Relation to the repository

**Formal status.** No statement is formalized in Lean or Rocq, and no
urelement theory is formalized anywhere in ProveIt. The report continues two
formal projects without adding to them:

- `SetTheory/ZF` formalizes pure first-order ZF:
  `SetTheory/ZF/Lean/ZF/Zf.lean` (a port of `SetTheory/ZF/Coq/Zf.v`, which
  declares `Sep_form`, `Repl_form`, `ZFax` and `ZFax_s` likewise) gives the
  schema constructors above, the bridges `bridge_Sep` and `bridge_Repl`, and,
  inside every model of Extensionality, Separation, Pairing, Union, Infinity
  and Replacement, the closure theorem `ClosureFO_of_ZF`.
- `SetTheory/BoundedConsistency` proves, by partial satisfaction, the
  numeralwise endpoint `BoundedZFCConsistency.Endpoint.zfc_proves_conZFC`
  (`ZFC ⊢ Con_n(ZFC)` for each metatheoretic `n`) for pure ZFC.

Both use the formula type `Form` of
`Logic/FirstOrder/Lean/FirstOrder/Fol.lean`, which has only the atomic
formulas `∈` and `=`: there is no atom predicate and there are no function
symbols, so neither the base language `{∈, At}` nor the expanded languages of
this report exist there. The "first task" and the six layers of Section 9,
the milestones of Section 22 and the formalization orders of Section 36 are
proposals; the report's questions on bounded consistency with atoms and on
Lean interfaces for failed scheme instances (Questions 10.11, 10.12, 23.12,
37.12) are open in ProveIt. No monoid localization, cone certificate or
necklace enumeration of Part III is formalized either.

**Review in the Hilbert's-tenth research tree.** Before placement, another
session routed all five batch-89 archives (commit `6aadaa4f2`):
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_topology_surreal_arrivals_20261003.md`,
with the receipt `review_topology_surreal_arrivals_20261003.json` beside it.
For Part I's manuscript it read the delivered README, the source audit, the
recorded finite-check scope and the delivered `article.tex` lines 118–133,
183–211, 807–865, 911–927 and 988–994 (abstract, Section 2.1 through
Remark 2.1, Section 9, the last two questions with the conclusion,
Appendix C). It records that "finitely many names" is a language parameter,
not a bound on Diophantine witnesses, that the finite checks are regression
evidence only, and that the proposed formalization is not an implemented
compiler; the Hilbert's-tenth programme's 84-operation universal polynomial
is unaffected. It claims no theorem audit, literature check or replay, and
made no correctness finding; no scope correction was needed. No review of
Part II's or Part III's manuscripts exists there.

**The same Collection theorem in a surreal report.** Batch-89 manuscript 03,
*Surreal Cuts, Replacement, and Atom-Support Spectra*, written against the
same pin as Part I and placed in the same commit, became Part VI of
`Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets`
(labels `hset:zr:`, written concurrently with Part I). For the same
kernel models (written `M^ker_κ` there, manuscript 03's `M_κ`) it proves, in
its delivered numbering (Part VI numbering in brackets), kernel confinement
(Lemma 9.1 [32.1, `hset:zr:lem:confinement`] = Lemma 2.3 here), the base
model theorem (Theorem 9.2 [32.2, `hset:zr:thm:supportbase`] = Theorem 2.4,
and Proposition 13.3 of Part II) and the Collection spectrum (Lemma 10.1,
Theorems 10.2–10.3, Corollary 10.4 [Lemma 33.1, Theorems 33.2–33.3,
Corollary 33.4, `hset:zr:cor:classification`]; that report's Remark 24.6,
`hset:zr:rem:nee`, records the overlap): the unexpanded case (`f = id_A`) of
Lemmas 7.1–7.2, Corollary 7.3 and Theorem 7.5 here. The two proofs are
independent and **both stand**; neither manuscript cites the other or
claims priority for the unexpanded spectrum. They differ in the failing
instance (manuscript 03 collects atom sets of prescribed cardinalities;
this report a `Δ0` injection graph, Appendix A, so its failure is one of
`Δ0` Collection) and in the successor case (this report's reservoir must
consist of whole components so that the permutations commute with the named
maps). Manuscript 03's Theorem 11.2 (Theorem 34.2 there), naming an
enumeration `e : κ → A_0` of `κ` atoms, makes Replacement fail at `cf κ`,
even at `ℵ1`, where every one-lift expansion here keeps full Collection; no
conflict, since `e` is not an elementary lift. The dated note after
Corollary 7.6 of the article gives the details. Part XV of
`Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders`
(batch-89 manuscript 01) finds the same cofinality threshold for class
Replacement in the full-class rank models `(V_λ, P(V_λ))`: different models,
no shared proof.

**Named group actions at the finite cutoff (batch 90) and Part II.** Part VIII
of the same surreal report (its source 12, batch-90 manuscript 05, *Named
Symmetries and Replacement*, labels `hset:ns:`; pinned to `8dc2592e9`, an
ancestor of Part I's placement, so it does not cite Part I) proves at the
finite cutoff the Replacement criterion for uniformly named actions of
arbitrary pure set-sized groups; for finitely many named permutations its
Theorem 58.1 (`hset:ns:thm:full`) is Theorem 5.1(2) here (independent proofs,
neither claimed first; Part I also covers non-surjective injections and
every uncountable cutoff). It adds the graded levels `R_k` (Theorem 59.1),
the observation that the one-cycle-of-each-length example of Example 5.5
satisfies every `R_k` (Theorem 60.1, Example 60.2), two involutions realizing
every finite level (Theorem 61.3, a finite-cutoff counterpart of Corollary
7.9), and the survival of pure-valued Collection under every such naming
(Theorem 63.1). A dated note at the end of Section 5 records this. Its
Questions 65.1, 65.3, 65.6 and 65.12 are the finite-cutoff counterparts of
Questions 10.7, 10.5, 10.9 and 10.12 here, and its Question 65.4 meets
Question 10.4; Theorems 5.1(1) and 6.1 answer its Question 65.2 in part, and
Theorems 7.5 and 7.7 its Question 65.11, for finitely many named injections.

Part VIII is **prior in the repository** to Part II, whose manuscript was
pinned twelve minutes before Part VIII's text was written and so does not
cite it. Part II meets it at `κ = ω`, with independent proofs: Corollary 15.4
is its Corollary 58.2 (`hset:ns:cor:finitegroup`); the `κ = ω` clause of
Theorem 18.2 follows from its Theorem 58.1 with Proposition 62.1
(`hset:ns:prop:finitewords`); Proposition 19.1 is its Proposition 62.2
(`hset:ns:prop:language`) with Corollary 58.2; Proposition 19.2 at `κ = ω` is
its Theorem 58.1; Proposition 19.4 is its Proposition 62.1; Theorem 19.3 makes
the separation of its Theorem 62.3 (`hset:ns:thm:evaluator`) for the same
group `⊕_ω C_2`. New in Part II: everything at uncountable cutoffs (Theorem
18.2 for `κ > ω`, Proposition 19.2 for `κ > ω`, which answers in part Part
VIII's Question 65.2 for countable groups, Corollary 19.5) and Theorem 19.3's
witness, whose orbits have at most two atoms, which works for every `κ` with
`cf(κ) ≤ 2^ℵ0`, whose evaluator is amenable, and which has a converse; Part
VIII's witness is the regular action, with infinite orbits, at `κ = ω` only,
and fails `R_1`. A dated note after Theorem 19.3 adds an observation of the
write, by Part VIII's Theorem 59.1: at `κ = ω` Part II's witness keeps `R_1`
and fails `R_2`. Dated notes after each overlapping result record the
overlap.

**Part III and the earlier Parts and Part VIII (batch 96).** Part III's two
sources were written against Parts I–II at the same pin and both answer Part
II's Question 23.3; source 03 also cites Part VIII's Theorem 59.1. Part III
reproves, with attribution, Part I's foundations and its fixed-action
criteria (Propositions 25.2–25.3, Lemma 26.1, Theorem 34.1, Proposition 34.4) and contains the
earlier universal thresholds as special cases (the note after Theorem 34.3):
one injection (Part I's Theorem 6.1, `r = 1`), `ℤ^s × ℕ^t` (Part II's Theorem
16.3, `d = t`), finite and infinite finitely generated abelian groups (Part
II's Corollary 15.4 and the abelian case of Theorem 18.2). Its Theorem 27.1
extends Part II's Theorem 17.1 from commuting permutations to every finite
tuple of injections, but with pure real parameters; the two agree where both
apply (the write's check, note after Corollary 27.2). Its Lemma 26.3
generalizes Part VIII's Lemma 56.3 (`hset:ns:lem:centralizer`) to injections
and infinite components; its two-involution example (Section 28.2) has an
infinite joint orbit, unlike Part VIII's finite-orbit pairs of Theorem 61.3,
and answers none of Part VIII's questions. Reciprocal notes for Part VIII are
proposed with this write and are not yet in that report. Part III's Example
34.6 is the commuting-injection counterpart of Part I's Example 7.10, and its
Theorem 35.1 (the supply of types under forcing) complements Part II's Theorem
21.1 (the verdict of a fixed action).

**Neighbouring reports.**

- `birthday-cutoffs-and-hereditary-sets`, subsection "Transfer of Kunen's
  inconsistency" (`hset:sub:kunen`, Theorem `hset:thm:kunen`): no nontrivial
  class elementary self-embedding of the birthday-expanded surreal class,
  under Kunen hypotheses that admit the embedding as a class parameter in
  Separation and Replacement. Here nontrivial amenable elementary lifts exist
  and naming them may or may not keep Replacement (Theorem 5.1); no conflict,
  since every `j_f` fixes the whole pure universe. A dated note at the end of
  that subsection (4 October 2026, batch 89) records this report's lifts
  (Theorems 3.2, 3.4, 5.1) there. Part VII of the same
  report (batch-89 manuscript 04) works in choiceless permutation models with
  atoms, on surreal coding and universality; it shares no theorem with this
  report.
- `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings` (cited as a
  "control example", Section 1.1; its Remark `sse:pf:rem:kunen` makes the
  analogous point for field self-embeddings; a dated note after that remark,
  4 October 2026, records this report).
- Not to be confused with Part X of
  `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic`
  (batch 89, the same batch), whose "elementary embeddings" are embeddings of
  models of Presburger arithmetic, not of set-theoretic universes; the two
  share no theorem.
- In this category, `../measurable-box-games/` also answers a Glazer paper
  and cites arXiv:2312.11902 but shares no theorem or notation;
  `../lexicographic-well-orderings-of-reals/` concerns pure ZFC. Apart from
  Parts VI–VIII of `birthday-cutoffs-and-hereditary-sets` (above) and Part XII
  of `polish-models-of-omnific-arithmetic` (batch 90, which cites Glazer–Yao
  as context for its class theory without Foundation), no report in ProveIt
  treats urelements or cites Glazer–Yao or Yao's dissertation. (Corrected 4
  October 2026, batch 90: this sentence had said "no other report", which was
  already stale for Parts VI–VII; the article's sentence in Section 1.4 named
  them and gains a dated note for Parts VIII and XII.)

**Stale claims.** Part I's dated note "Status of the questions" (Section 10)
said that none of its twelve questions is answered in ProveIt; a dated
addition (4 October 2026, batch 93) corrects it, and dated notes after
Questions 10.1, 10.4 and 10.10 and after the conclusion record Part II's
answers. Part II's own repository statements are true at its pin and at the
write. Added 4 October 2026, batch 96: Part III made four statements stale,
each now corrected by a dated note, never by an edit of the old text. Part
II's "Status of the questions" note (Section 23) said none of its thirteen
questions is answered; Part I's note after Question 10.1 said that question
stays open "for injections, for non-commuting tuples, and for the
atom-valued part of definable closure"; Part I's status note listed Question
10.1 as open beyond commuting permutations; and the pointer after the title
page said the report has two Parts. Dated notes after Questions 23.1, 23.2,
23.3 and 23.5 and after Question 10.1 (a second note) record what Part III
settles: 23.3 answered; 23.1, 23.2 and 10.1 answered with pure real
parameters only, re-scoped and still open in ordinary form; 23.5 not
answered (source 04's "commutative answer" decides the monoid analogue).

## Notation

`M_κ(A)` (Part VI of `birthday-cutoffs-and-hereditary-sets` writes `M^ker_κ`,
manuscript 03's `M_κ`, for the same class; not the rank models `M_λ` of
`surreal-well-orders` Part XV nor the Presburger models `M_α` of
`polish-models-of-omnific-arithmetic`), `N_{κ,f}`, `ker`, `mov`,
`ZFCU_R`/`ZFU_R` (R = Replacement), `B_t`, `D_κ(f)`, `I(f)`, `H` (a protected
set of atoms, not `H_κ`), `V`, `V_α(C)`, `Collection_{≤μ}` (manuscript 03
writes `Collection_{<τ}`), `Rob_r`, `RP`, `𝔠`; "limit cardinal" includes `ω`.
The table of Section 1.5 fixes each one, with the tempting false reading.

Part II keeps these meanings and adds `ℕ` (not Part I's macro `𝒩_{κ,f}`),
staircases `U_S` (not `U(A)`), `F, G` (staircase maps; elsewhere `G` is a
group), `H` (four uses: `ℤ^s`, the hull `H(ā)`, a subgroup, a reservoir),
`K` (subgroups), `p_i` (named permutations), `B_K`, the uniform evaluator
`E(g,x)` (Part VIII's `T(i,a,b)` and action graph; not Part VI's enumeration
predicate `E`), `τ(G)`, `τ_fin(G)` (not Part VIII's involution `τ` nor Part
VI's `τ = cf κ`) and the scheme notation `𝒦(dcl(ā))`. The table of
Section 12.5 fixes them. No symbol was renamed in Parts I–II.

Part III unifies its two sources on source 03's letters and keeps the
earlier meanings. Renamed (Section 24.6 lists every case): source 03's atom
kernel `ak` is `ker`, its expanded structure `𝓜` is `𝒩_{κ,f}`, its necklace
count `𝒩(a,b)` is `Neck(a,b)` (source 04's name, so that it is not read as
the expanded model); source 04 **swaps `M` and `P`** (its `P` presented, `M`
the cancellative image), and its type count `θ(P)` is `τ(M)`, its `δ = gcd(m,n)`
is `g_0`, its divisor count `τ` is `div`, its stabilizer order `h` is `e`, its
repetition order `e` is `δ`, its Möbius `μ` is `μ_Möb`, its Cantor family
`B_r, S_r` is `A_R, S_R`, its matrix `A_0` is `B`, its cone `W` is `𝒲_B^ℚ`, its
universe `V(A)` is `U(A)`; `2^ℵ0` is printed `𝔠`. Letters with several
meanings in Part III (`M, P, G`; `U`; `τ(M)` versus Part II's `τ(G)`; `A_t`,
`A_R`; `B`; `μ`; `δ`; `e`; `H`; `W`; `ℓ, v`; `c_i`) are fixed in the table of
Section 24.6, with the false readings.

## Labels

Every label carries the prefix `nee:`: 66 before Part II, 146 before Part III,
284 after.

- Part I: the manuscript's 64 labels were prefixed before anything cited
  them and every reference updated (38 `\cref` keys, 13 `\eqref`); the
  batch-89 write added `nee:sec:provenance` and `nee:sec:notation`. The
  batch-93 write added three labels to Part I's text without changing any
  number: `nee:part:one` (the Part heading) and `nee:q:commuting`,
  `nee:q:forcing` (Questions 10.4 and 10.10, previously unlabelled).
- Part II: the manuscript's 61 labels prefixed `nee:ca:` (unprefixed
  `sec:`, `thm:`, `lem:`, `eq:`, `grp:`, `uni:` … in the source), plus
  `nee:ca:part`, `nee:ca:sec:provenance`, `nee:ca:sec:notation`, twelve
  question labels `nee:ca:q:*` and `nee:ca:q:primary`: 77.
- Part III: 138 labels, `nee:aa:` (73) for source 03's material and
  `nee:ci:` (65) for source 04's (two sub-prefixes for two sources, as in
  Part II of `definable-surreals-and-omnific-integers`). Each source label
  `x` became `nee:aa:x` or `nee:ci:x`; an item printed once for both sources
  carries both labels (for example `nee:aa:thm:types` and
  `nee:ci:thm:summary` on Theorem 30.4), except the two shared equations,
  source 04's (6.1) and (6.3), which amsmath allows one label each:
  they are `nee:aa:eq:necklace` and `nee:aa:eq:infinitecount` only. Added
  at the write: `nee:aa:part`, `nee:aa:sec:provenance`,
  `nee:aa:sec:notation`, `nee:aa:sec:questions-answered`, subsection labels,
  labels for unlabelled items of both sources (remarks, examples, figures,
  tables, the seventeen questions).

Part I's and Part II's numbering was checked unchanged against a build of the
committed text (all 146 labels). The batch-93 write also:

- wrapped Part I as `\part` I (after the table of contents) and added Part II
  as `\part` II after Part I's appendices, with section numbers continuing
  (`\theHsection` prefixed `ca.` so that no PDF destination repeats);
- added `graphicx` and Part II's macros (`\Mk`, `\NN`, `\ZZ`, `\QQ`, `\FF`,
  `\Ord`, `\dcl`, `\Stab`, `\Sub`, `\id`) and a `cleveref` name for
  questions (Part I's questions are now cited by `\cref`);
- moved the bibliography after Part II, one list for both Parts: Part II's
  entries for Glazer–Yao and Yao are Part I's; its `RepoZF`, pinned at
  `a9ab9a698`, is cited as `RepoZFca`; `RepoNaming`, `Mitchell2014`,
  `CGP2010`, `Smith1995` and `IO1991` are new;
- added a `[write]` pointer after the title page and at the head of Part II,
  dated notes in Part I (Section 1.4, after Questions 10.1, 10.4, 10.10, the
  status note of Section 10, after the conclusion) and in Part II
  (Sections 12.4–12.5, after Theorems 15.3, 17.1, 18.2, 19.3, 21.1, after
  Corollary 15.4's example, Remark 18.4, Propositions 19.2 and 19.4, Section
  22.2 and the questions), and Question 23.13.

The batch-96 write:

- added Part III as `\part` III after Part II's appendices, sections from 24
  and appendices from F (`\theHsection` prefixed `aa.` and `aa.app.`);
- added the packages `mathrsfs` (source 03's `\mathscr`) and `tikz` (source
  04's figure) and Part III's macros (`\RR`, `\rank`, `\Sat`, `\Aut`, `\Per`,
  `\spanR`, `\Code`, `\Eval`, `\Pure`, `\Neck`, `\im`, and `\srcs` for the
  "Sources" lines);
- merged the bibliographies: the sources' Glazer–Yao and Yao entries are
  Part I's; their entries for this report, pinned at `715a716a3`, are cited as
  `RepoNamingIII`; `RepoBirthday`, `RepoRoot`, `GlazerThesis`,
  `BaileyRenshaw`, `Boardman`, `Koch`, `Anderson`, `ChanLevine`,
  `GorskyMazin`, `Johnson` are new;
- added dated notes to Parts I–II (the pointer after the title page; a second
  note after Question 10.1; the status notes of Sections 10 and 23; after
  Questions 23.1, 23.2, 23.3, 23.5) and to Part III (Sections 24.2, 24.5,
  24.6; after Theorem 26.2, Lemma 26.3, Corollary 27.2, Section 27.2, Section
  28.1, Section 28.2, Theorem 32.1, Theorem 33.5, Theorem 34.1, Theorem 34.3,
  Theorem 35.1, Section 36.1, Section 36.2, in Section 37 and Appendix G),
  and Question 37.17.

No statement, proof, number or non-claim of any manuscript was changed, apart
from the renamed symbols of Part III (Section 24.6), the merging of each
shared result into one statement containing every clause of either source,
and two typographical changes made to avoid bad boxes (a list of counts set
as separate formulas; the title of one second proof). Parts I–II keep their
numbers; Part II's equation numbering within sections is the batch-93
change, and Part III's numbering is new (the "Sources" lines map it).

## Files

```text
README.md                                          this guide (replaces the delivered README.md of Part I's package)
SOURCE_AUDIT.md                                    Part I: delivered source and proof audit: literature used, pin, files inspected, limits
article.tex                                        the report (Part I: delivered article.tex, labels prefixed; Part II: batch-93 manuscript 01; Part III: batch-96 manuscripts 05 and 06 merged; [write] notes)
article.pdf                                        compiled report, 128 pages (unnumbered title page, pages i-iv, then pages 1-123; Part II from page 30, Part III from page 65)
code/build.sh                                      Part I: delivered three-pass pdfLaTeX build of the article.tex in its own directory
code/verify_finite.py                              Part I: finite regression checks: component swaps and real-marker coding (standard library)
code/02-commuting-actions-verify_examples.py       Part II: exact finite sanity checks (standard library; prints its report)
code/02-commuting-actions-make_figure.py           Part II: generator of Figure 1 (Matplotlib 3.10.8)
code/03-atom-actions-verify_presentations.py       Part III, source 03: exact presentation, composition and semigroup checks (SymPy)
code/03-atom-actions-make_figure.py                Part III, source 03: generator of Figure 2 (Matplotlib)
code/04-commuting-injections-verify_results.py     Part III, source 04: 148 exact finite checks (standard library)
data/verification_results.json                     Part I: recorded run of verify_finite.py (Python 3.13.5, 125,582 assertions)
data/BUILD_AUDIT.json                              Part I: delivered build record: engine, PDF checks, visual review, hashes of the seven delivered files
data/02-commuting-actions-verification_output.txt  Part II: recorded run of verify_examples.py (PASS, 347,278 checks)
data/03-atom-actions-verification_results.json     Part III: recorded run of verify_presentations.py (Python 3.12.14, SymPy 1.14.0)
data/04-commuting-injections-verification.json     Part III: recorded run of verify_results.py (148 cases PASS)
figures/02-commuting-actions-staircases.pdf        Part II: Figure 1, vector (included by article.tex)
figures/02-commuting-actions-staircases.png        Part II: Figure 1, 1970x1659 preview
figures/03-atom-actions-antichain_upsets.pdf       Part III: Figure 2, vector (included by article.tex)
figures/03-atom-actions-antichain_upsets.png       Part III: Figure 2, 1436x752 preview
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Placement moved Part I's `build.sh` and
`verify_finite.py` to `code/` and its two JSON files to `data/`, and staged
Part II's `make_figure.py`, `verify_examples.py`, `verification_output.txt`
and `figures/staircases.{pdf,png}`, source 03's `verify_presentations.py`,
`figures/make_figure.py`, `verification_results.json` and
`figures/antichain_upsets.{pdf,png}`, and source 04's `verify_results.py` and
`verification.json` under the names above. Not shipped: Part I's delivered
27-page `article.pdf` (300,041 bytes) and README; Part II's
`commuting_actions_replacement.tex` (printed here as Part II),
`commuting_actions_replacement.pdf` (31 pages, 526,831 bytes) and
`README.txt`; source 03's `atom_actions.tex` and source 04's
`commuting_injections.tex` (merged here as Part III), `atom_actions.pdf`
(28 pages, 504,887 bytes), `commuting_injections.pdf` (24 pages, 277,207
bytes), both `README.txt`, and source 03's checksum manifest `SHA256SUMS.txt`
(eight entries, all verified at placement). Parts I–II's packages had no
checksum manifest, and nothing was excluded as heavy. All survive in the
archives:

```sh
git show 8ea27d6c0:docs/incoming/Naming_Elementary_Embeddings_Research.zip > <scratch>/Naming_Elementary_Embeddings_Research.zip
git show 2faa3b37a:docs/incoming/commuting_actions_replacement.zip > <scratch>/commuting_actions_replacement.zip
git show 26e036956:docs/incoming/atom_actions_research.zip > <scratch>/atom_actions_research.zip
git show 26e036956:docs/incoming/commuting_injections_research.zip > <scratch>/commuting_injections_research.zip
```

Delivered text that names the delivery layout or a file not shipped:

- `code/build.sh` changes to its own directory and builds the `article.tex`
  there, then copies `article.pdf` beside it: run in place it fails (there is
  no `code/article.tex`); run it on a copy (below). It predates Parts II–III
  and does not copy `figures/`.
- `data/BUILD_AUDIT.json` records the delivered 27-page PDF, the delivered
  `article.tex` (now rewritten), the delivered `README.md` and `article.pdf`
  (not shipped) by their flat names and hashes, and "no final-pass
  warnings" under TeX Live 2025; under MiKTeX the delivered source gives
  one duplicate-destination warning (see Labels).
- `data/verification_results.json` names no paths; its `script_sha256` is
  the hash of the shipped `code/verify_finite.py`.
- The article's Appendix C names `verify_finite.py` and the JSON file by
  their delivered names; a note there gives the shipped paths. The delivered
  README told readers to run `bash build.sh` and
  `python3 verify_finite.py --output verification_results.json` in one flat
  directory.
- `SOURCE_AUDIT.md` says the repository was inspected "through the GitHub
  connector" at the pin; it names repository paths only.
- `code/02-commuting-actions-make_figure.py` writes `figures/staircases.pdf`
  and `figures/staircases.png` in a `figures/` directory **beside itself**
  (here that would create `code/figures/`), replacing them atomically; run it
  on a copy. Section 22.2 and Appendix E of the article name
  `verify_examples.py`, `make_figure.py`, `verification_output.txt` and
  `figures/staircases.pdf` by their delivered names (a note in Section 22.2
  gives the shipped paths), and the delivered `README.txt` (not shipped) told
  readers to run `python3 verify_examples.py > verification_output.txt`,
  which would overwrite the record.
- `data/02-commuting-actions-verification_output.txt` names no paths.
- `code/03-atom-actions-verify_presentations.py` (its usage text says
  `python verify_presentations.py`) writes `verification_results.json`
  **beside itself** when run without `--output` (here that would create
  `code/verification_results.json`); it writes with the platform's line
  endings (CRLF on Windows, so compare with `tr -d '\r'`); it checks with
  `assert`, so never run it under `python -O`.
- `code/03-atom-actions-make_figure.py` writes `antichain_upsets.pdf` and
  `antichain_upsets.png` **beside itself**; run it on a copy.
- `code/04-commuting-injections-verify_results.py` (its docstring says "Run
  `python verify_results.py` to write verification.json next to this file")
  writes `verification.json` **beside itself** when run without `--output`;
  the delivered `README.txt` (not shipped) told readers to run it that way,
  which in the delivered layout overwrote the record.
- Section 36 and Appendix F of the article name `verify_presentations.py`,
  `verification_results.json`, `figures/make_figure.py`,
  `figures/antichain_upsets.pdf`, `verify_results.py`, `verification.json`,
  the delivered `atom_actions.tex`, `commuting_injections.tex` and
  `README.txt` by their delivered names (a note in Section 36.1 gives the
  shipped paths). The two JSON records name no paths.

## Rerun the checks

Python 3.10 or newer. Run everything from this directory, in Git Bash (on a
POSIX host use `python3` for `py`). None of the commands below writes into the
report directory.

Part I: `verify_finite.py` without arguments only prints its report, so it can
run in place; with `--output` it writes the file named, so never point that at
`data/`.

```sh
py code/verify_finite.py                     # read-only; prints "status": "passed"
T=$(mktemp -d)
py code/verify_finite.py --output "$T/verification_results.json" > /dev/null
tr -d '\r' < "$T/verification_results.json" | diff - data/verification_results.json
```

At the Part I write (3 October 2026, Python 3.14.4, Windows) the run took under
a second and the only difference was the `python_version` line (3.14.4 against
3.13.5). The recorded run covers all permutations on at most seven points
(5,913 structures), all ordered pairs of permutations on at most five points
(15,017), 4,456 isomorphic component swaps, the 64 six-bit marker codes and
69,632 marker-translation cases.

Part II: `verify_examples.py` takes no arguments and prints its report;
`make_figure.py` writes beside itself, so copy it first.

```sh
T=$(mktemp -d)
py code/02-commuting-actions-verify_examples.py > "$T/out.txt"
tr -d '\r' < "$T/out.txt" | diff - data/02-commuting-actions-verification_output.txt
cp code/02-commuting-actions-make_figure.py "$T/"
(cd "$T" && uv run --no-project --with matplotlib==3.10.8 python 02-commuting-actions-make_figure.py)
cmp "$T/figures/staircases.pdf" figures/02-commuting-actions-staircases.pdf
```

At the Part II write (4 October 2026, Python 3.14.4, Windows) the checks took
about 2 s and printed `Result: PASS` with 347,278 checks, byte-identical to the
record; the figure PDF was byte-identical and the PNG pixel-identical (its
bytes differ: PNG compression is not reproducible across library builds). The
checks cover all 256 eight-bit staircase prefixes, translated boundary
windows, all 15 subgroups of `(ℤ/4ℤ)^2` and all 31 nonzero characters of
`(F_2)^5`.

Part III: always pass `--output` to the two verifiers (their default output is
beside the script), and run the figure script on a copy.

```sh
T=$(mktemp -d)
uv run --no-project --with sympy==1.14.0 python code/03-atom-actions-verify_presentations.py --output "$T/03.json"
tr -d '\r' < "$T/03.json" | diff - data/03-atom-actions-verification_results.json   # only the "python" line differs
py code/04-commuting-injections-verify_results.py --output "$T/04.json"
cmp "$T/04.json" data/04-commuting-injections-verification.json
cp code/03-atom-actions-make_figure.py "$T/"
(cd "$T" && uv run --no-project --with matplotlib==3.10.8 python 03-atom-actions-make_figure.py)
```

At the Part III write (4 October 2026, Windows) source 04's checks took under a
second (Python 3.14.4) and printed `PASS: 148 exact cases (8 rank, 36
necklace, 24 subgroup, 80 permutation)`, byte-identical to the record; source
03's took about 5 s (Python 3.13.5, SymPy 1.14.0), passed, and differed from
the record only by line endings and the `"python"` field (3.12.14 delivered);
the regenerated `antichain_upsets.pdf` differed from the shipped one only in
its `CreationDate`, and the PNG was pixel-identical. Source 03's checks cover
fourteen presentation matrices, all 24,301 weak compositions for
`1 ≤ a, b ≤ 8` in 3,521 rotation classes and five coprime numerical
semigroups; source 04's eight rank examples, 1,709 compositions, 3,759
candidate subgroups and 9,888 permutation-pair checks.

## Build the PDF

pdfLaTeX with mathpazo, geometry, amsmath/amssymb/amsthm/mathtools,
microtype, aliascnt, booktabs/tabularx/array/longtable, enumitem, xcolor,
fancyhdr, graphicx, mathrsfs, tikz, hyperref and cleveref; the bibliography
is inline. The article includes `figures/02-commuting-actions-staircases.pdf`
and `figures/03-atom-actions-antichain_upsets.pdf`, so copy the figures too.
Build in a scratch copy:

```sh
B=$(mktemp -d); mkdir "$B/figures"
cp article.tex "$B/"; cp figures/02-commuting-actions-staircases.pdf figures/03-atom-actions-antichain_upsets.pdf "$B/figures/"
cd "$B"; latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The delivered `code/build.sh` also works on such a copy (copy it beside
`article.tex` and run `bash build.sh`); it was not rerun after Parts II–III
were added.

The committed PDF was built this way with MiKTeX on 4 October 2026:
128 pages (34 before Part II, 69 before Part III); no errors or warnings, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. The delivered Part I source,
built the same way, gives 27 pages and one duplicate-destination warning
(`page.1`), removed as described under Labels.

## Provenance

- Sources cited by Part I: Glazer–Yao, arXiv:2602.21970v1; Glazer,
  arXiv:2312.11902v3; Yao, *Set Theory with Urelements*, doctoral
  dissertation, University of Notre Dame, 2023 (arXiv:2303.14274v3); the
  three ProveIt files above at its pin. Part II adds this report at its pin,
  `Zf.lean` at its pin, Mitchell's lecture notes on `G`-sets, de Cornulier–
  Guyot–Pitsch on subgroup spaces of abelian groups, Smith (1995) and
  Ivanov–Ol'shanskii (1991). Part III adds this report and Part VIII of
  `birthday-cutoffs-and-hereditary-sets` at its pin, the repository root,
  Glazer's thesis, Bailey–Renshaw on acts over monoids, Boardman's notes on
  `G`-sets, Koch's thesis on affine monoids, Chan–Levine on abelian networks,
  and Anderson, Gorsky–Mazin and Johnson on rational Catalan combinatorics.
- Repository inputs: Part I's pin `2b7b388ba` (3 October 2026, "Catalogue
  batches 81 to 86"), Part II's pin `a9ab9a698` (4 October 2026) and Part
  III's pin `715a716a3` (4 October 2026), each an ancestor of its placement.
- Part I: batch 89 of `docs/incoming`, manuscript 05 of five; arrival
  `8ea27d6c0`, placement `23adb85f9`, written in the batch-89 write phase
  (3 October 2026). Single source, so its write made no merge choices.
- Part II: batch 93, manuscript 01 (the dossier's numbering); arrival
  `2faa3b37a`, placement `47a77daba` (which records the placement decision:
  an addition to this report, which it continues, rather than to Part VIII
  of `birthday-cutoffs-and-hereditary-sets`), written in the batch-93 write
  phase (4 October 2026). Single source, printed in full, so no merge
  choices; the choices of the write were where to print the overlap with
  Part VIII (as dated notes, Part II's proofs kept in full) and the numbering
  scheme (continuing Part I's sections, as in `../measurable-box-games/`).
- Part III: batch 96, manuscripts 05 (source 03) and 06 (source 04), arrival
  `26e036956`, placement `27f200305` (which records the decision: one
  addition, merged, base 05, because both answer Question 23.3 and 05 is more
  general and answers three questions), written in the batch-96 write phase
  (4 October 2026). Where the merge had to choose (Section 24.5 of the
  article): source 03's section order, source 04's sections inserted by
  subject; shared results printed once with every clause of either source,
  source 04's proofs as second routes; source 04's summary theorems printed
  once, as Theorems 30.4 and 34.3; one torsion remark and one `ℚ≥0` example
  for both; both figures and abstracts kept; the two presentation tables
  merged, the two power tables kept; the 24 questions merged into 16, with
  Question 37.17 added; notation on source 03's letters.
