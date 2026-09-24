# Discrete Initial Groups and Omnific Normalization

**Sign-tree surgery, a sharp image classification, an Ehrlich–Kaplan
question, and convex factors**
Two-source research report, 23 September 2026: source 01, *Discrete Initial
Groups and Omnific Normalization* (batch 28, manuscript 09, placed in
`c6359e4`), and source 02, *Convex Factors and Profinite Obstructions for
Initial Surreal Groups* (batch 29, manuscript 09, placed in `66d7e55` as an
addition). AI-assisted draft prepared for Vladimir Reshetnikov.

```
article.tex                     the report, standalone LaTeX with an internal bibliography
article.pdf                     the compiled report, 53 pages
README.md                       this guide
source_audit.md                 source 01: source and verification audit, as delivered
02-convex-factors-PROVENANCE.md source 02: provenance and proof-status record, as delivered
code/
  verify.py                     source 01 checks (Python 3.10+, standard library only)
  build.sh                      source 01's delivered build script (see "Rerunning the checks": copy only)
  02-convex-factors-verify.py   source 02 checks (Python 3.10+, standard library only)
data/
  verification_report.json               recorded run of verify.py: PASS, 450,862 assertions
  02-convex-factors-verification.json    recorded run of 02-convex-factors-verify.py: PASS
```

Every label in `article.tex` carries the prefix `isg:`; source 02's material
uses the sub-prefix `isg:cf:`. The report had 84 labels after source 01 was
written and has 166 now: the merge of source 02 renamed, removed or moved no
label and added 82, all `isg:cf:`. Every theorem-like number of Sections 1–10
and Appendices A–B is unchanged; the old Sections 11, 12 and 13 (audit,
questions, conclusion) are now Sections 19, 20 and 21. The source
manuscripts themselves, their PDFs and their delivery READMEs are not
shipped. `code/`, `data/`, `source_audit.md` and
`02-convex-factors-PROVENANCE.md` are byte-identical to the deliveries (the
source 02 files carry the placement prefix; the provenance record still
names them `code/verify.py` and `data/verification.json`, their delivered
names).

## Status

Source 01 proposes an **affirmative answer** to a published question of
Ehrlich and Kaplan: *is every discrete initial subgroup of `No` isomorphic to an
initial subgroup of `Oz`?* It is Question 2 of arXiv:1512.04001v1 (Section 9,
printed page 18) and Question 9.1 of the journal version, *J. Symbolic Logic* 83
(2018), 617–633.

Source 02 answers, completely, the two questions that source 01 left open
about quotients (Questions 20.1 and 20.2 here, `isg:q:convex` and
`isg:q:limit`): every convex quotient of an initial group has an explicit
initial realization, and limit stages of iterated bottom-layer removal need
no extra hypothesis. **Source 02 answers none of Ehrlich and Kaplan's
questions.** In particular it does not answer their Question 1 (journal
Question 8.1), the set-model version of their optimality theorem, which
concerns theories between ordered and divisible ordered abelian groups;
source 02 says so itself (Section 18.2).

Both are **proposed results in an unrefereed AI-assisted draft**. When each
manuscript was placed, its proofs were checked by hand and no gap or error
was found (Section 19.5); those checks are not a refereeing, and each covers
only its own source (plus, for source 02, the consistency statements of
Sections 13.2–13.3). The literature searches were **targeted, not
exhaustive**; no prior resolution or matching formulation was found, which
is limited evidence. No priority is claimed and nothing is verified in Lean.

Both sources rest on one imported result, the Ehrlich–Kaplan criterion for
initial subgroups (arXiv v1 Theorem 1, journal Theorem 5.1; Imported fact
2.2 here), used in its concrete form: the *specified canonical normal-form
image* is initial. The journal statement says this outright ("via the
canonical isomorphism"); in the arXiv version it is the content of the
sufficiency proof. The criterion was checked as a statement against both
texts, not re-proved. Source 02 also imports Ehrlich's theorem that every
divisible ordered abelian group has an initial realization (Imported fact
11.1).

## Numbering of the cited paper

The article uses the arXiv v1 numbering throughout (as both manuscripts
did). The correspondence with the journal version was read in the
author-hosted text of the journal version (the publisher's typeset pages were
not compared) and is printed in Section 1.1:

| arXiv v1 | journal | role here |
|---|---|---|
| Lemma 3 | Lemma 5.1 | initial subgroups of `R` (Imported fact 2.3) |
| Theorem 1 | Theorem 5.1 | the initiality criterion (Imported fact 2.2) |
| Proposition 9 | Proposition 5.2 | shape of the least positive element |
| Question 2 | Question 9.1 | the question addressed by source 01 |
| Question 3 | Question 9.2 | the initial-monoid problem, not addressed |
| Theorem 6 | Theorem 8.1 | optimality with class models (source 02, Section 18.2) |
| Question 1 | Question 8.1 | set-model optimality, not answered |

The two versions state the optimality theorem differently: the arXiv
version for theories between `T_OAG` and `T_DOAG`, the journal version for
theories containing the theory `T_D` of nontrivial densely ordered abelian
groups. Remark 18.1 (a merge remark) records what source 02's dense example
gives in each formulation: nothing in the first, and the set-model "only if"
part for the theories that hold in `W = Qω² + Zω + Q` in the second; the
question stays open in both.

## What the report claims

Let `A ⊆ No` be a nonzero discrete initial additive subgroup. *Initial* means
closed under proper sign-sequence prefixes; *isomorphic* means as ordered
abelian groups.

### Source 01 (Sections 1–10, Appendix A)

- **Bottom structure** (Proposition 3.2, Corollary 3.3). The least positive
  element is `ε = 2^(−n) ω^(−α)` for unique `α ∈ On`, `n ∈ N`; the exponent
  class has minimum `p = −α`, the bottom coefficient group is `2^(−n) Z`, and
  every `D ω^(−β)`, `β < α`, lies in `A` (`D = Z[1/2]`).
- **Root relocation** (Definition 4.1, Theorem 4.4). An explicit order
  isomorphism `Θ_α` from the cone `[−α, ∞)` onto `No_{≥0}` sends `p` to `0`
  and satisfies `Pred(Θ_α x) = Θ_α[Pred x ∪ {p}]` for `x > p`; right ancestors
  are preserved away from `p`, and the right ancestors of `p` itself are lost
  exactly (Remark 4.5). Inverse initiality holds exactly when the spine
  `{0} ∪ {q_β : β < α}` is present (Proposition 4.7), `q_β = +⌢−^β`.
- **Ambient transport** (Theorem 5.2). The map `N_{α,n}`, which reindexes
  exponents by `Θ_α` and multiplies only the bottom coefficient by `2^n`, is a
  real-linear order isomorphism of Hahn spaces that preserves support order
  types, leading truncations and set-indexed strong summability in both
  directions.
- **Theorem A (omnific normalization)** and **Corollary 6.2**. `N_{α,n}`
  restricts to an ordered-group isomorphism of `A` onto an initial subgroup
  `H ⊆ Oz` with `N(ε) = 1`. Hence every discrete initial subgroup of `No` is
  isomorphic to an initial subgroup of `Oz`: the proposed answer.
- **Theorem B (sharp image classification).** For fixed `α, n`, the images are
  exactly the initial `H ⊆ Oz` containing the dyadic-spine group
  `K_α = Z ⊕ ⊕_{β<α} D ω^(q_β)` (Lemma 7.1); the correspondence preserves and
  reflects inclusion. Counterexamples `H = Z` and `H = Z + Zω` at `α = 1`
  show that both the exponent and the coefficient part of the condition are
  needed (Section 10.5).
- **Extremal groups and scales** (Theorem 7.3, Corollaries 7.4, 7.6). The
  smallest and largest initial groups with least positive element `ε` are
  `L_{α,n}` and `M_{α,n} = ε Oz`, with images `K_α` and `Oz`;
  `|A| ≥ max(ℵ0, |α|)`, attained; and `N^(−1)[H]` is initial exactly for
  `α ≤ d(H)`, the dyadic-spine depth.
- **Theorem C (bottom cyclic layer)** with Lemma 8.1 and Proposition 8.3.
  `Zε` is convex, `A ≅ B ×_lex Z` for an explicit initial `B ⊆ No` realizing
  `A/Zε`, and the splitting is canonical relative to the normal forms. Finite
  iteration follows (Corollary 8.4).
- **Suspension** (Theorem 8.5, Corollary 8.6). `B ↦ Z ⊕ σ_*[B]` is an
  inclusion-preserving bijection between initial subgroups of `No` and nonzero
  initial subgroups of `Oz`; a nonzero discrete ordered group is initially
  realizable iff its quotient by the least positive cyclic subgroup is and the
  extension splits.
- **Surcomplex modules** (Theorem 9.2, Corollary 9.3). The coordinatewise map
  is a `Z[i]`-linear isomorphism `A[i] → H[i] ⊆ Oz[i]` with the same exact
  range; integral and Gaussian-integral linear systems transport exactly.
- Worked examples (Section 10): Ehrlich and Kaplan's own example
  `D + Z ω^(−1)`, where the construction recovers their map `d + mω^(−1) ↦ dω + m`;
  why scalar rescaling (`½Z + Zω`) and exponent translation (an exponent class
  containing `ω`) fail; a support of order type `ω + 1`; failure of
  multiplicativity.

### Source 02 (Section 1.5, Sections 11–18, Appendix C)

A group is *initially realizable* (`G ∈ Init`) if it is order-isomorphic to
an initial subgroup of `No`. Several of source 02's symbols are renamed to
avoid collisions with source 01 (table in Section 11.1): its residue map
`ρ_G` is `res_G`, its `D(G)` is `G^div`, its profinite parameter `α` is `ζ`,
its type `p_*` is `τ_*`, its `K` is `W`, its compression `c_E` is `♭_E`, its
convex subgroups `C_1 ⊆ C_2` are `C ⊆ C'`, and its Theorems A–C are
Theorems D–F.

- **Exponent cuts and canonical splitting** (Lemmas 11.3–11.4, Theorem 11.5,
  Proposition 11.7). A convex subgroup `C` of an initial `G` corresponds to a
  lower segment `Γ_C` of the exponent class; coefficient restriction to a
  convex exponent interval is a difference of two leading truncations and
  stays in `G`; `G = C^♮ ⊕ C` lexicographically, with `C^♮ = G[Γ ∖ Γ_C]`, and
  `C'/C ≅ G[Γ_{C'} ∖ Γ_C]`.
- **Compression** (Definition 12.1, Theorem 12.4, Proposition 12.6). On a
  meet-closed class `E` (every convex interval of an initial class is one,
  Lemma 12.2), retaining exactly the signs whose preceding prefix lies in
  `E` is the unique order- and prefix-isomorphism onto an initial class; it
  reflects meets and right ancestors and is coherent under nested
  restriction, at limit lengths as well.
- **Theorem D (convex-factor closure)** with Theorem 13.1 and Corollaries
  13.2–13.3. Every convex subquotient of an initially realizable group is
  initially realizable, explicitly; `Init` is closed under convex subgroups,
  convex quotients, and unions and intersections of chains of convex
  subgroups; every convex subgroup sequence of an initial group splits, and
  the compressed factor realizations are coherent under nested restrictions.
  This answers Question 20.1 (`isg:q:convex`).
- **Consistency with source 01** (Proposition 13.5, [merge]). For
  `C = Zε`, compressing away the bottom exponent gives exactly source 01's
  `ρ ∘ Θ_α` (root relocation followed by root deletion), with the same
  coefficients; the quotient realization is source 01's group `B` and the
  splitting is that of Theorem C. Two proofs: the explicit formula, and the
  uniqueness of compression.
- **Limit stages** (Corollary 13.6, [merge]). The iteration of Corollary 8.4
  continues through all ordinals; at every stage, limit stages included, the
  quotient has the explicit realization of Theorem D, which is source 01's
  at finite stages and is related to every earlier stage by compression. No
  hypothesis is needed. This answers Question 20.2 (`isg:q:limit`).
- **Theorem E (Presburger criterion)** with Proposition 14.3 and Corollary
  14.4. For a set-sized `Z`-group `G` (a model of additive Presburger
  arithmetic) with least positive `e`: `G ∈ Init` ⇔ `G` has an initial
  realization in `Oz` ⇔ `Ze` is a direct summand ⇔ `res_G(G) = Z ⊆ Ẑ` ⇔
  `G ≅ G^div ×_lex Z`. The only rigid initially realizable `Z`-group is `Z`.
- **Factorial family** (Section 15). Explicit rank-two groups
  `G_ζ ⊆ Q ×_lex Q` for `ζ ∈ Ẑ`, with `res(x_1) = −ζ`; `G_ζ ∈ Init` ⇔
  `ζ ∈ Z` (Theorem 15.2); `ζ_* = Σ k!` is not an integer (Lemma 15.3);
  endpoint-marked isomorphism classes are `Ẑ/Z` (Proposition 15.5); there are
  `2^ℵ0` pairwise nonisomorphic countable rigid `Z`-groups that are not
  initially realizable (Theorem 15.6).
- **Theorem F and model theory** (Section 16). Initial realizability is not
  elementary (Corollary 16.1); the countable dense group `G_ζ ×_lex Q` is
  elementarily equivalent to the initial group `W = Qω² + Zω + Q` but not
  initially realizable (Theorem 16.2); the recursive type `τ_*` is omitted by
  every initially realizable `Z`-group, so recursively saturated, countably
  saturated and nonprincipal-ultrapower `Z`-groups are not initially
  realizable (Theorems 16.3, 16.5, Corollary 16.4); nor is the additive group
  of any nonstandard model of Peano arithmetic (Theorem 16.6).
- **Omnific and surcomplex consequences** (Section 17). `res_Oz = ct`
  (Proposition 17.1); a set-sized `Z`-group is initially realizable iff some
  additive map to `Oz` sends `e` to `1` (Corollary 17.2); rectangular
  convex-factor transport (Theorem 17.4) and Gaussian residues
  (Proposition 17.5).
- **Period groups** (Corollary 17.3, [merge]). For a phase `Ψ` of the
  trigonometry report on `No` or on a set-sized field `F`, the normalized
  period group is initially realizable ⇔ its profinite defect `∂_Ψ` vanishes
  ⇔ its period sequence splits; then it is `≅ Π_F ×_lex Z` (and `≅ Oz ∩ F`
  for `F = No`, `No(λ)`).
- **Boundaries** (Section 18). Convex splitting is necessary, not proved
  sufficient; arbitrary subgroups of initial groups need not be initially
  realizable (`G_ζ ⊆ Qω + Q`); a convex subgroup need not be literally
  initial (`Zω^(−1) ⊆ D + Zω^(−1)`, realized as `Z`); the extension converse
  fails (`G_ζ`).

## What the report does not claim

Section 20.1 collects every limitation as N1–N15 (source 01, with its audit)
and N16–N29 (source 02, with its provenance record); each also stands at its
place in the text. In brief:

- Source 01's solution is **proposed, unrefereed**, with no certified
  correctness, novelty or priority (N1). The literature and repository
  searches were targeted; a question posed in 2015 and 2018 is not thereby
  shown to have been open on the review date (N2).
- The Ehrlich–Kaplan criterion is imported, not re-proved, and is never
  replaced by the false shortcut that an initial exponent class suffices (N3).
  The two-level example, the criterion, the classification of initial real
  groups and Conway normal forms are not claimed as new (N4).
- `N_{α,n}` is **not** a simplicity isomorphism (already `½Z → Z` cannot be),
  not multiplicative, not norm preserving, and does not fix ordinary constants
  (N5); `Θ_α` is not an exponent-group homomorphism, and Proposition 4.8 bounds
  exponent lengths, not birthdays (N7). Strong sums live in the ambient spaces,
  with no internal summation on `A` (N8). `α` is not an invariant of the abstract
  group, and uniqueness in Theorem B is relative to the fixed map (N9).
- No classification of all ordered abelian groups with initial embeddings; the
  initial-monoid problem (arXiv Question 3, journal Question 9.2) is not
  addressed (N6). Source 01 made no claim about other convex quotients or
  limit stages (N10); source 02 now proves both, and N10 is kept as a
  statement about source 01.
- The surcomplex statements are Gaussian-linear and coordinatewise only: no
  field isomorphism, no simplicity relation on `No[i]`, no modulus (N11, N24).
- The finite checks of both sources are regression tests: they do not verify
  limit cases, arbitrary ordinals or Hahn supports, class comprehension, the
  imported criterion, Presburger completeness, recursive saturation or the
  Peano argument; building a PDF establishes its integrity, not its
  correctness (N12, N25). No Lean formalization or Lean build (N13, N16).
  Both repository reviews were targeted (N14, N27); the questions of Section
  20 are not claimed to be published open problems (N15).
- Source 02: its results are proposed, with no certified priority (N16); the
  Ehrlich–Kaplan and Ehrlich theorems, Jeřábek's residue theory, `Ext(Q,Z) ≅
  Ẑ/Z` and the existence of rigid Presburger models are classical and
  credited, with no new Ext computation (N17); there is no classification of
  initially realizable groups (N18); it does **not** resolve Ehrlich–Kaplan
  Question 1 / 8.1 and answers none of their questions (N19); its splitting
  depends on the realization (N20); it concerns realizability, not literal
  initiality (N21); no identification with a Hahn product and no strong-sum
  closure (N22); additive only, the compression need not respect exponent
  addition (N23); the arithmetic fragment for the Peano obstruction is not
  optimized (N26); its predecessor was cited without an invented path (N28);
  finite solvability of the retraction systems is not a global splitting
  (N29).

The open questions are Questions 20.3–20.8: multiplicative compatibility of
the normalization, formal certification and uniqueness (source 01), and an
intrinsic characterization of `Init`, the obstruction in every intermediate
theory of the optimality question, the weakest arithmetic fragment, and
multiplicative compatibility of compression (source 02). Questions 20.1
(other convex quotients) and 20.2 (limit iteration) are answered.

## Relation to neighbouring reports

At the placement of source 01, no other report named Ehrlich–Kaplan Question
2 / 9.1, and none treated initial subgroups: a search of `docs/` and of the
Lean sources for "initial subgroup", "discrete initial" and "discretely
ordered initial" found nothing outside this directory.

- **[trigonometry](../../surcomplex/trigonometry/)** studies the normalized
  period groups `𝓘(Ψ)` of surcomplex phases with the same Jeřábek residue
  theory for `Z`-groups: its `res_𝓘` and `𝓘^div`
  (`trigonometry:per:sec:defect`) are `res_G` and `G^div` here, and its
  profinite defect `∂_Ψ` (`trigonometry:per:thm:defect`) is that residue
  modulo `Z`. Corollary 17.3 ([merge]) shows that a period group is initially
  realizable exactly when its defect vanishes, via
  `trigonometry:per:thm:split`. No conflict: that report's initiality
  statements concern kernel-multiplier rings and the initial integer part
  `Oz ∩ F`, not period groups.
- **[omnific-diophantine-geometry](../omnific-diophantine-geometry/)** and
  **[set-sized-quotients-of-omnific-integers](../set-sized-quotients-of-omnific-integers/)**
  study the ring `Oz = Z ⊕ Π`. This report uses the same `Oz`
  (`odg:def:rings`, `osq:eq:Ozdef`), its discreteness (`odg:prop:units`) and the
  constant coefficient `ct` (`osq:lem:ct`), but only additively: its groups
  `H ⊆ Oz` are additive subgroups and its normalization is not multiplicative.
  The Diophantine report cites a *different* Ehrlich–Kaplan paper, *Surreal
  ordered exponential fields*, Lemma 11.1 (the initial integer part of an
  initial subfield; status note after `odg:thm:floor`); there is no overlap or
  conflict. Its "initial forms" (`odg:prop:initial`) are leading forms, a
  different use of the word.
- **[foundations](../../foundations-and-computation/foundations/)** cites
  Ehrlich–Kaplan II as background on initial embeddings next to its sign-tree
  categoricity (`found:sub:signtree`), and has `Oz = Π ⊕ Z` as
  `found:eq:omnific`.
- **[definable-surreals-and-omnific-integers](../../foundations-and-computation/definable-surreals-and-omnific-integers/)**
  cites Ehrlich–Kaplan II for simplest separators (`dsn:sec:foundations`, where
  "initial" is defined as here). Its maximal initial elementary exponential core
  (`dsn:thm:core`) concerns initial *subfields* of definable surreals; related
  in spirit, no overlap.
- **[exponential-relations-over-omnific-integers](../../foundations-and-computation/exponential-relations-over-omnific-integers/)**
  (batch 33) reads `Oz` as a Presburger `Z`-group: its division with remainder
  (`exr:prop:division`) is Lemma 14.1 for `G = Oz`, re-derived independently,
  its splitting `Oz = Π ⊕ Z` is the split form of Main Theorem E, and with
  rational-slope exponential predicates it is a definitional expansion of
  Presburger arithmetic with `Z` elementary in `Oz` (`exr:thm:rational`).
  Nothing there concerns initiality. An unnumbered note at the end of the
  collection section records this; it changed no number and no page count.
- The symbols `Θ_α`, `Ψ_α`, `q_β`, `N_{α,n}` are local (Section 1.4) and
  unrelated to theta series or the nome `q` of the surcomplex reports; `♭_E`
  and `res_G` are local to Sections 11–18.

No `isg:` statement has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md).

## Provenance

Two manuscripts (Section 19.5 gives the details and the merge choices).

- **Source 01**, *Discrete Initial Groups and Omnific Normalization* (24
  pages, 23 September 2026), delivered with a README, `source_audit.md`,
  `verify.py`, `verification_report.json` and `build.sh`; placed in
  `c6359e4`, written in `3d9dbe9`. It has **no pinned commit**; it records
  the blobs it read (`README.md` `391afd7…`, `docs/FORMALIZATION.md`
  `6a89497…`) and a later commit `173eb52`, an ancestor of `c6359e4`. It
  makes no claim about the content of any report. Its first write added,
  without changing any mathematical statement, proof or example: the `isg:`
  prefix; the journal numbering and the wording of journal Theorem 5.1
  (Sections 1.1 and 2.2); the shared conventions (Section 1.4); the
  provenance and placement review (Section 19.5); the collected non-claims
  (Section 20.1); a definition of `ct`; the shipped file names; labels on
  unlabelled statements; correct cross-reference names; a one-page title
  page. The citations of Kaplan's thesis (Sections 6.2, 7.1) and of the
  Oberwolfach Report 60/2016 (pp. 3355–3356) are the manuscript's and were
  not re-checked.
- **Source 02**, *Convex Factors and Profinite Obstructions for Initial
  Surreal Groups* (23 pages, 23 September 2026), delivered with a README,
  `PROVENANCE.md`, `code/verify.py` and `data/verification.json`, and no
  checksum manifest; placed in `66d7e55` with the prefix `02-convex-factors-`.
  Its repository pin is `9693b28`, an ancestor of `c6359e4`; at its pin it
  correctly cited source 01 as a preceding project draft with no repository
  path, which is now Sections 1–10 of this report (its "Section 8" is Section
  8 here). Its citations of Jeřábek, Strickland, Enayat–Hamkins–Wcisło and
  Bagayoko–van der Hoeven were not re-checked.
- **The merge.** Results in both sources are printed once: the
  Ehrlich–Kaplan criterion and real coefficient groups (Imported facts
  2.2–2.3), the Hahn-completion caution (Remarks 5.3, 11.2), the suspension
  (Theorem 8.5, which source 02 re-proves by the same argument), `Oz` and the
  rectangular convention. Colliding symbols of source 02 were renamed
  (Section 11.1). Three statements were added with complete proofs and
  marked [merge]: Proposition 13.5, Corollary 13.6 and Corollary 17.3; Remark
  18.1 compares the two versions of the optimality theorem. Source 01's
  passages saying that convex quotients and limit stages were not covered
  (after Corollaries 8.4 and 8.6, Questions 20.1–20.2, N10) now say which
  source proves what; no mathematical statement of source 01 changed.

## Build

From this directory, with a TeX distribution providing pdfLaTeX, `newtx`,
`microtype`, `tikz`, `tcolorbox`, `aliascnt`, `hyperref` and `cleveref`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 53 pages with no errors, warnings, overfull or underfull
boxes, undefined references, multiply defined labels or duplicate
destinations; the title page is one page. Remove the auxiliary files
afterwards (`latexmk -c`).

## Rerunning the checks

**Run both suites only on a copy.** Source 01's `code/verify.py` writes its
report to `--output`, whose default is `verification_report.json` *in the
current directory*; the delivered `build.sh` calls it with exactly that name,
and in the delivered flat layout both overwrote the shipped record (and
`build.sh` also rebuilt the PDF in place). In this directory `build.sh`
changes into `code/`, writes a stray `code/verification_report.json`, and
then stops, because it compiles `omnific_normalization.tex`, the delivered
name of `article.tex`. Source 02's program prints its report and writes a
file only with `--output`; its delivered README's rerun command,
`python3 code/verify.py --output data/verification.json`, names the delivered
record and would overwrite it (here: `data/02-convex-factors-verification.json`).
Use scratch output names:

```sh
cp -r . /path/to/scratch/isg && cd /path/to/scratch/isg
python code/verify.py --output rerun01.json
python -c "import json; print(json.load(open('rerun01.json')) == json.load(open('data/verification_report.json')))"
python code/02-convex-factors-verify.py --output rerun02.json
python -c "import json; print(json.load(open('rerun02.json')) == json.load(open('data/02-convex-factors-verification.json')))"
```

At this write both suites were rerun on a copy: source 01 passed with
450,862 assertions in about 6 seconds, source 02 printed `PASS` in about 10
seconds, and both comparisons printed `True`. Run source 02's program
without Python's `-O` flag, because its checks use assertions. To use
`build.sh`, first restore the delivery layout in a scratch directory: put
`code/verify.py`, `code/build.sh` and `data/verification_report.json` side
by side with `article.tex` copied to `omnific_normalization.tex`, then run
`sh build.sh` there.

Source 01's suite covers finite sign words up to length seven, all 677
prefix-closed trees of depth at most three (the empty tree included),
inverse-spine and coefficient-spine conditions in those finite ranges, and
1,500 random pairs of finite rational normal forms (seed 20260923). Source
02's suite covers all 2,016 nonempty convex intervals of the sign tree of
lengths at most five and all 61 meet-closed subsets of lengths at most two
(1,398,609 order, prefix and meet pairs; 145,740 initial-image prefix
checks), 46,376 nested interval pairs of lengths at most four (324,632
coherence points), the factorial transitions and residues, integer-parameter
splittings, finite retraction systems through sixty stages, and 24,300
projection composition identities. Both are regression tests of the
formulas, not verifications of the transfinite arguments.
