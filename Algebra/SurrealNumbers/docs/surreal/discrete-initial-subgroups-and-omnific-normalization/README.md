# Discrete Initial Groups and Omnific Normalization

**Sign-tree surgery, a sharp image classification, an Ehrlich–Kaplan
question, convex factors, the standard cut in bounded arithmetic, and
perfect transcendence gaps in Borel arithmetic**
Four-source research report. AI-assisted drafts prepared for Vladimir
Reshetnikov; unrefereed; nothing in it is formalized in Lean or Rocq.

| Source | Title | Batch, manuscript | Archive | Pin | Placed | Printed in |
|---|---|---|---|---|---|---|
| 01 | *Discrete Initial Groups and Omnific Normalization* (24 pp., 23 Sep 2026) | batch 28, ms 09 | (Surreal-era `docs/new`) | none (read `173eb52`) | `c6359e4`, written `3d9dbe9` | Sections 1–10, Appendix A |
| 02 | *Convex Factors and Profinite Obstructions for Initial Surreal Groups* (23 pp., 23 Sep 2026) | batch 29, ms 09 | (Surreal-era `docs/new`) | `9693b28` | `66d7e55` (addition) | Section 1.5, Sections 11–18, Appendix C |
| 03 | *Standard Integers in a Single Infinite Interval: Residue Characters, Bounded Induction, and Omnific Arithmetic* (20 pp., 3 Oct 2026) | batch 86, ms 10 | `Glazer_ProveIt_Arithmetic_Research.zip`, arrival `fb8414869` | `883e0b3b2` | `0bd0e5527` (addition, prefix `03-standard-cut-`) | Section 1.6, Sections 19–22 |
| 04 | *Perfect Transcendence Gaps in Borel Arithmetic: Standard Systems, p-adic Shadows, Hahn Fields, and Omnific Integers* (26 pp., 3 Oct 2026) | batch 90, ms 06 | `Perfect_Transcendence_Gaps_Package.zip`, arrival `a162e4386` | `7d9b8b957` | `12076b2e8` (addition, prefix `04-transcendence-gaps-`) | Section 1.7, Sections 23–26 |

```
article.tex                     the report, standalone LaTeX with an internal bibliography
article.pdf                     the compiled report, 108 pages
README.md                       this guide
source_audit.md                 source 01: source and verification audit, as delivered
02-convex-factors-PROVENANCE.md source 02: provenance and proof-status record, as delivered
03-standard-cut-SOURCE_AUDIT.md source 03: source, correction and novelty audit, as delivered
04-transcendence-gaps-theorem_ledger.md  source 04: theorem and dependency ledger (its own numbering), as delivered
04-transcendence-gaps-source_audit.md    source 04: source and novelty audit, as delivered
code/
  verify.py                     source 01 checks (Python 3.10+, standard library only)
  build.sh                      source 01's delivered build script (see "Rerunning the checks": copy only)
  02-convex-factors-verify.py   source 02 checks (Python 3.10+, standard library only)
  03-standard-cut-verify.py     source 03 certificate checks (Python 3.10+, standard library only)
  03-standard-cut-compile_interval.py  source 03 single-bound compiler and its audit (standard library only)
  03-standard-cut-build.sh      source 03's delivered build script (delivery layout only; see below)
  04-transcendence-gaps-verify.py  source 04 finite checks (Python 3.10+, standard library only)
data/
  verification_report.json               recorded run of verify.py: PASS, 450,862 assertions
  02-convex-factors-verification.json    recorded run of 02-convex-factors-verify.py: PASS
  03-standard-cut-verification.json      recorded run of 03-standard-cut-verify.py: PASS, 20,322 checks
  03-standard-cut-compiler_report.json   recorded run of 03-standard-cut-compile_interval.py: PASS, 5 sentences, 768 gate checks
  03-standard-cut-BUILD_AUDIT.json       source 03's build record of its delivered (unshipped) 20-page PDF
  04-transcendence-gaps-verification.json  recorded run of 04-transcendence-gaps-verify.py: PASS
```

Every label in `article.tex` carries the prefix `isg:`; source 02's material
uses the sub-prefix `isg:cf:`, source 03's the sub-prefix `isg:sc:`, and
source 04's the sub-prefix `isg:ptg:`. The report had 84 labels after
source 01 was written, 166 after the merge of source 02 (82 `isg:cf:`
added), 236 after the write of source 03 (70 `isg:sc:` added), and has 313
now: the write of source 04 renamed, removed or moved no label and added
77, all `isg:ptg:`. Every theorem-like number of Sections 1–22 and of
Appendices A–C is unchanged. Source 03 occupies Sections 19–22, inserted
after Section 18; source 04 occupies four new Sections 23–26, inserted
after Section 22, and a new Section 1.7. So the audit, questions and
conclusion (Sections 11–13 in source 01, 19–21 after the merge of source
02, 23–25 after the write of source 03) are now Sections 27, 28 and 29,
and their questions, numbered 24.x at the write of source 03, are now
28.x; the old Question 24.11 (`isg:sc:q:images`), which source 04 answers
for Peano arithmetic, is now Question 28.11. Cite labels, not these
numbers. The source manuscripts themselves, their PDFs and their delivery
READMEs are not shipped. `code/`, `data/`, `source_audit.md`,
`02-convex-factors-PROVENANCE.md`, `03-standard-cut-SOURCE_AUDIT.md` and
the two `04-transcendence-gaps-` records are byte-identical to the
deliveries (the source 02, 03 and 04 files carry the placement prefixes;
the source 02 provenance record still names its files `code/verify.py` and
`data/verification.json`, and source 03's `build.sh` names `code/verify.py`,
`code/compile_interval.py`, `verification.json`, `compiler_report.json`
and `article.tex`, their delivered names; source 03's `SOURCE_AUDIT.md`
names no file, and its `BUILD_AUDIT.json` describes the delivered PDF,
which is not shipped; source 04's ledger names `article.tex` and
`verify.py`, uses source 04's own theorem numbers, which Section 23.2 maps
to this report's, and refers to Sections 12 and 13 of source 04, now part
of Section 27 and Questions 28.17–28.27; source 04's program names its
record `verification.json`; its source audit names only repository paths
and says that it did not use "the supplied LinkedIn page", which is not
shipped and has no address in the text).

## Status

Source 01 proposes an **affirmative answer** to a published question of
Ehrlich and Kaplan: *is every discrete initial subgroup of `No` isomorphic to an
initial subgroup of `Oz`?* It is Question 2 of arXiv:1512.04001v1 (Section 9,
printed page 18) and Question 9.1 of the journal version, *J. Symbolic Logic* 83
(2018), 617–633.

Source 02 answers, completely, the two questions that source 01 left open
about quotients (Questions 28.1 and 28.2 here, `isg:q:convex` and
`isg:q:limit`): every convex quotient of an initial group has an explicit
initial realization, and limit stages of iterated bottom-layer removal need
no extra hypothesis. **Source 02 answers none of Ehrlich and Kaplan's
questions.** In particular it does not answer their Question 1 (journal
Question 8.1), the set-model version of their optimality theorem, which
concerns theories between ordered and divisible ordered abelian groups;
source 02 says so itself (Section 18.2).

Source 03 is weak arithmetic of discretely ordered rings with an additive
map to `Z`; it never mentions initial subgroups. Combined with source 02's
Presburger criterion (Theorem E) it **partly answers** source 02's question
on arithmetic fragments (Question 28.7, `isg:cf:q:fragment`): the additive
group of every nonstandard model of `IΔ0` is not initially realizable,
while open induction does not suffice (Corollary 20.11 and Proposition
20.12, marked [write]: stated and proved at the write, not in any source).
The question is re-scoped in a dated note after its statement; the exact
weakest fragment, and exclusion by the factorial type itself, stay open.
Source 03 also **corrects an external preprint**: Lemma 2.7 of
Enayat–Łełyk–Visser, arXiv:2508.14758v2 (pages 11–12), asserts that the
ideal `J` with `R/J ≅ Z` of a Dorroh ring is unique; `(X)` and `(X − 1)` in
`Z[X]` are two such ideals, also under their ordered condition
(Proposition 21.1). Its repair, uniqueness under division by 2
(Proposition 21.2), is correct. The correction is local: it does not claim
that the preprint's main theorems fail.

Source 04 is about standard systems of nonstandard models of Peano
arithmetic and never mentions initial subgroups. Its exact profinite image
(Theorem 25.3) **answers source 03's question on canonical residue images
(Question 28.11, `isg:sc:q:images`) for Peano arithmetic**: for every
nonstandard `M ⊨ PA`, `im res_{R_M} = Ẑ(SSy M)`, the profinite integers
whose factorial residue sequences are computable from one member of the
standard system, and the idempotents of this ring recover `SSy M`
(Corollary 25.4). The question asks about `IΔ0`, so it stays open there; it
is re-scoped in a dated note after its statement. Combined with Scott's
classical theorem, the images of the countable nonstandard models of PA are
exactly the rings `Ẑ(𝒮)` of countable Scott sets `𝒮` (Corollary 25.5,
marked [write 04]: stated and proved at the write, not in any source). Its
other results (a perfect transcendence gap over analytic subfields of `R`
and `Q_p`, the real and p-adic fields computable from the standard system of
a Borel model, the p-adic residue image, a coefficient-preserving Hahn
transfer and an omnific family) answer no question of this report. Several
of its statements were already in the collection or the Lean development;
see "What the report claims".

All four are **proposed results in an unrefereed AI-assisted draft**. When
each manuscript was placed or written, its proofs were checked by hand and
no gap or error was found (Section 27.5); those checks are not a
refereeing, and each covers only its own source (plus, for source 02, the
consistency statements of Sections 13.2–13.3). The literature searches were
**targeted, not exhaustive**; no prior resolution or matching formulation
was found, which is limited evidence. No priority is claimed and nothing is
verified in Lean. Source 04 rests on an external theorem that it cites
from seminar slides: Glazer's theorem that Borel models of arithmetic do not
have full standard system (Imported fact 23.6; MOPA seminar, 27 February
2024, slide 4). Every source-04 statement about Borel models depends on it;
the exact residue images do not.

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
  This answers Question 28.1 (`isg:q:convex`).
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
  hypothesis is needed. This answers Question 28.2 (`isg:q:limit`).
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

### Source 03 (Section 1.6, Sections 19–22)

`R` is a discretely ordered commutative ring (1 least positive), `ED_n` is
Euclidean division by the ordinary integer `n`, *standard division* is
`ED_n` for every `n`, and a *normalized integer character* is an additive
map `χ : R → Z` with `χ(1) = 1`, **not** assumed order-preserving. Symbols
renamed from source 03 (table in Section 19.2): its character `ρ` is `χ`
(`ρ` is root deletion here), its `κ_R` is `res_R` (source 02's `res_G`), its
`D` is `R^div`, its formulas `P`, `S` are `Pow^dy`, `Std^dy` (the Diophantine
report's `Std` is a different, existential formula), its bound `H` is `Ω`,
its rings `A, A_0, A_Sh, A(k,Γ)` are `𝒜, 𝒜_0, 𝒜_Sh, 𝒜(k,Γ)`, its retraction
`ε` is `χ_𝒜`, and its ideals `J_a` are `𝔧_c`.

- **Dyadic detector** (Theorem 19.4). With `ED_2`, `ED_3` and a normalized
  character, the parameter-free bounded formula `Pow^dy(y)` ("no odd divisor
  `≥ 3`") defines exactly the ordinary powers of 2 in `R_+`, and `Std^dy(x)`
  (`x = 0` or a `Pow^dy` element in `(x/2, x]`) defines exactly `N`; the
  nonstandard case is a finite odd-factor certificate.
- **Inductiveness and one induction sentence** (Lemma 19.6, Theorem 19.7).
  `Std^dy` contains 0 and is closed under successor in every ring with `ED_2`
  alone, character or not; in the detector's class, `R = Z` ⇔ `R_+ ⊨ ∀x
  Std^dy(x)` ⇔ the single instance `Ind(Std^dy)` ⇔ `R_+ ⊨ IΔ0`. Sharpness
  (Proposition 19.8): in `Z + XZ[1/2][X]` and `Z + XZ[1/3][X]` the detector
  fails (division by 2 alone or 3 alone is not enough for this formula).
- **Integer characters** (Theorem 20.1, Proposition 20.2). With standard
  division, `Hom(R, Z)` is `0` or `Zχ` with `χ` a unital ring map, and then
  `R = Z ⊕ R^div` with `R^div = ⋂ nR` a divisible ideal; a character exists
  iff `res_R(R) ⊆ Z ⊆ Ẑ`. (The additive content is source 02's Proposition
  14.3.)
- **No unit-preserving additive map from bounded arithmetic** (Lemma 20.3,
  Theorem 20.4, Corollaries 20.6–20.7, 21.4). For nonstandard `M ⊨ IΔ0`,
  `Hom((R_M)_add, Z) = 0`; hence no additive map `M → 𝒜` with `1 ↦ 1` into
  any ring with a unital retraction onto `Z`, in particular into `Oz`, and
  every ring map into a domain is zero. No regularity of the maps is
  assumed. Corollary 20.9: every positive infinite `Pow^dy` element has a
  non-diagonal residue profile.
- **[write] Initial realizability** (Definition 20.10, Corollary 20.11,
  Proposition 20.12, Remark 20.13). `T^dy` = `PA^-` + all `ED_n^+` + the one
  sentence `Ind(Std^dy)`, provable in `IΔ0`. For every nonstandard
  `M ⊨ T^dy` (so every nonstandard model of `IΔ0` or of PA), `G(M)` is a
  `Z`-group with `Hom(G(M), Z) = 0`, `res ≠ Z`, not initially realizable, with
  no additive map to `Oz` sending 1 to 1: source 02's Theorem 16.6 holds with
  `IΔ0`, even `T^dy`, in place of PA. Shepherdson's countable ring `𝒜_Sh`
  satisfies `IOpen` and every `ED_n^+`, and its additive group `V_Sh ×_lex Z`
  is initially realizable; so the threshold is strictly above `IOpen`.
  Remark 20.5 ([write]) gives a second route to Theorem 20.4 through the
  four-square formula of Enayat–Łełyk–Visser's Theorem 2.9.
- **Correction and repair** (Propositions 21.1–21.2), as in "Status".
  For `Oz`, the ring-homomorphism case of the repair is
  `odg:prop:canonicalct` and the Lean theorem
  `Surreal.Foundations.SignSequence.omnific_int_hom_eq_constant`.
- **Examples** (Section 21). `𝒜_0 = Z + XQ[X]` (computable, not `IOpen`:
  `x² < X` defines the standard cut), with explicit certificates;
  `𝒜_Sh` (imported `IOpen`); principal-part rings `𝒜(k, Γ)`; `Oz`, where
  `Pow^dy`, `Std^dy` define `2^N` and `N` (Corollary 21.4); the
  set-sized/class reading (Section 21.6).
- **Compiler and complexity** (Section 22). Every arithmetic sentence
  compiles effectively to a formula all of whose quantifiers are bounded by
  one positive infinite `Ω`, with atoms of degree at most 2, true in `R_+`
  iff the sentence is true in `N` (Theorem 22.2); for the computable `𝒜_0`
  (and `𝒜_Sh`) this bounded truth set, and parameter-free `Σ_1` and `Π_1`
  truth, are many-one equivalent to true arithmetic (Theorem 22.4,
  Corollary 22.5). It is not a single truth predicate; no conflict with
  Tarski. Diophantine retractions do not bound it (Section 22.6).

### Source 04 (Section 1.7, Sections 23–26)

ZFC throughout; *analytic* means Σ¹₁ (a continuous image of a Polish
space), never power-series analyticity; `p` is always an ordinary prime;
`F` is `R` or `Q_p`. A *Borel model* of PA has a standard Borel carrier and
Borel `+`, `·`. `SSy(M)` is the standard system (standard binary traces of
elements), a Turing ideal for nonstandard `M ⊨ PA`. Symbols renamed from
source 04 (table in Section 23.2, which also maps its theorem numbers to
these): its Turing ideals `S, T` are `𝒮, 𝒯`, its oracles `A, B` are sans-serif,
its fields `K_F(S)` are `𝒦_F(𝒮)`, its generic field `K` and hulls `H_C` are
`k` and `k_Y` with the parameter set `C` written `Y`, its `D = M − M` is the
difference ring `R_M` of Section 20.3, its residue maps `ρ_p, ρ̂` are
`res_p, res_{R_M}`, its `A_p(S)` and `B(S)` are `Z_p(𝒮)` and `Ẑ(𝒮)`, its
idempotents `e_A` are `𝟏_A`, its tail ring `R_L = Z + I_L` is source 03's
`𝒜(k,Q) = Z + Π_k`, and its exponent group `G` is `Γ`.

- **Perfect gap after countably many parameters** (Theorem 23.1, proved in
  Section 24). If `k ⊊ F` is an analytic subfield, relatively algebraically
  closed, then for every countable `Y ⊂ F` the hull `k_Y = acl_F(k(Y))` is a
  proper, dense, null and meager analytic field, every finite dependence
  relation `Dep_n(k_Y)` is null and meager, every nonempty open set contains
  a Cantor set algebraically independent over `k_Y`, and
  `trdeg(F/k_Y) = 𝔠`. The mechanism (Lemma 24.1): an analytic subfield of
  `R` or `Q_p` cannot have positive finite or countable transcendence
  degree, since a countable basis would give a nonzero derivation with
  analytic graph, hence Borel, hence continuous, hence zero on the dense `Q`.
  Remark 24.3: the analytic hypothesis excludes an actual failure mode. Real
  hulls have Hausdorff dimension zero (Corollary 24.6, Edgar–Miller,
  imported).
- **Standard systems and scalar fields** (Section 23). Trace and
  Turing-ideal lemmas (Lemmas 23.3–23.4, full induction); `SSy(M)` is
  analytic for Borel `M` (Lemma 23.5) and, by Glazer's theorem (Imported fact
  23.6), proper, hence dense, null and meager in `2^N` (Corollary 23.7). The
  points `𝒦_F(𝒮)` with a fast name computable from a member of `𝒮` form a
  field (Definition 23.8), analytic for analytic `𝒮` (Lemma 23.9);
  `𝒮 ⊆ 𝒯 ⇔ 𝒦_F(𝒮) ⊆ 𝒦_F(𝒯)` (Proposition 23.10); individual roots are
  oracle-computable, nonuniformly (Lemma 23.11); `𝒦_F(𝒮)` is relatively
  algebraically closed, and elementary in `(R,+,·,<)` and `(Q_p,+,·)`
  (Theorem 23.12, with Macintyre's quantifier elimination imported).
- **Arithmetic consequences** (Theorem 23.2, Corollary 24.7, Theorem 24.8).
  For a nonstandard Borel `M ⊨ PA` the fields `𝒦_F(SSy M)` satisfy the
  perfect-gap theorem, even after adjoining any countable set of constants;
  continuous injections `2^N → (1,2)` and `2^N → Z_p` for all primes, from
  one Cantor parameter space, have images independent over the respective
  fields.
- **Exact residue images** (Section 25, no Borel hypothesis). For every
  nonstandard `M ⊨ PA`: `res_p(R_M) = 𝒦_p(𝒮) ∩ Z_p =: Z_p(𝒮)`, with
  fraction field `𝒦_p(𝒮)`, each value realized by an element of `M`
  (Theorem 25.1); for Borel `M` it is a proper, dense, null and meager
  valuation ring (Corollary 25.2). `res_{R_M}(R_M) = res_{R_M}(M) = Ẑ(𝒮)`
  (Theorem 25.3, by an explicit overspill); its idempotents are exactly the
  `𝟏_A`, `A ∈ 𝒮`, as Boolean algebras, and `Ẑ(𝒮) ⊊ ∏_p Z_p(𝒮)` when `𝒮` is
  proper (Corollary 25.4); `Ẑ(𝒮)/mẐ(𝒮) ≅ Z/mZ`.
- **[write 04] Residue images of countable Peano models** (Section 25.4,
  Corollary 25.5). Distinct standard systems give distinct images; a subring
  of `Ẑ` is `im res_{R_M}` for a countable nonstandard `M ⊨ PA` iff it is
  `Ẑ(𝒮)` for a countable Scott set `𝒮`, which it determines. This combines
  Theorem 25.3 and Corollary 25.4 with Scott's 1962 theorem, imported.
- **Equal completions, different images** (Proposition 25.6, Theorem 25.7,
  Corollary 25.8). `𝒜(k,Q)` has `ct` as a ring retraction with kernel `Π_k`,
  `𝒜(k,Q)/n ≅ Z/n`, and every finite-target map factors through `ct`; `R_M`
  and `𝒜(k,Q)` have the same finite quotients and p-adic completions `Z_p`,
  but canonical images `Z_p(𝒮)` and `Z` (`1/(p+1)` separates them); there is
  no unital ring map `R_M → Z`, hence none `R_M → 𝒜(k,Q)`.
- **Hahn transfer and the omnific family** (Section 26). Independence over
  `k` persists over `k((t^Γ))` for every set-sized ordered group `Γ`, also
  after multiplying by units (Theorem 26.1, Corollary 26.2). With
  `t = ω^(−1)`: for a Cantor set `P ⊂ (1,2)` independent over `k_{R,Y}`,
  the `𝔠` omnific integers `rω`, `r ∈ P`, are purely infinite, algebraically
  independent over `k_{R,Y}((t^Q))`, divisible by every ordinary integer
  and killed by every map to a finite ring (Theorem 26.3); they are
  **discrete** in the surreal order topology (Section 26.3), and not
  independent over `R` (`sX_1 − rX_2 = 0`).

What was already in the collection or in Lean (recorded at the statements
and in Section 27, as the write's comparisons): Corollary 25.8 is weaker than
source 03's Theorem 20.4 and Corollaries 20.6 and 21.4, which exclude every
additive map sending 1 to 1, already for `IΔ0`; Theorem 26.1 follows at once
from `isc:cp:lem:coeffld` of
[independent-surreal-copies](../independent-surreal-copies/) (linear
disjointness of `k'` and `k((t^Γ))` over `k`); `𝒜(k,Q)` is source 03's
`𝒜(k,Γ)` at `Γ = Q` (Section 21.4), and Proposition 25.6 and the `𝒜`-half of
Theorem 25.7 are set-sized versions of `Oz` facts proved in Lean,
`omnificQuotientZModEquiv` (`OmnificResidues.lean`),
`omnific_finite_hom_kills_purelyInfinite` and `omnific_finite_hom_factors`
(`OmnificFiniteQuotients.lean`), `omnificPadicCompletionEquiv_of`
(`OmnificPadicCompletion.lean`) and `omnificProfiniteCompletionEquiv_of`
(`OmnificProfiniteCompletion.lean`), all in
`Algebra/SurrealNumbers/Surreal/Foundations/`, namespace
`Surreal.Foundations.SignSequence` (`odg:thm:finitequotients`,
`odg:eq:profinite`, Proposition 17.1 here); and the moral of Theorem 25.7 is
the remark after Proposition 20.2. Each `rω` is separately transcendental
over `R` by the Lean theorem `omnific_transcendental_of_not_finite`
(`OmnificPolynomialRoots.lean`). Theorem 25.3 strengthens Corollary 20.9
(`im res_{R_M} ⊄ Z`) to an exact description for PA.

## What the report does not claim

Section 28.1 collects every limitation as N1–N15 (source 01, with its audit),
N16–N29 (source 02, with its provenance record), N30–N41 (source 03,
with its source audit; N41 limits the [write] statements) and N42–N56
(source 04, with its source audit and theorem ledger; N56 limits the
[write 04] statement); each also stands at its place in the text. In
brief:

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
  28 are not claimed to be published open problems (N15).
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
  optimized (N26; source 03 reaches `IΔ0` by another argument, and the
  fragment for the factorial type itself is still not optimized); its
  predecessor was cited without an invented path (N28); finite solvability
  of the retraction systems is not a global splitting (N29).
- Source 03: AI-assisted and unrefereed, no Lean or Rocq (N30).
  Standard-cut definability and the failure of induction beyond open
  induction in `Oz` were already known (Jeřábek 2011; Enayat–Łełyk–Visser,
  whose Theorem 2.9 already gives a parameter-free bounded definition of `N`
  in every ordered Dorroh ring, including `Oz` with ideal `Π`); its
  contribution is the dyadic formula, its inductiveness, the character
  results and the compiler, with no established priority (N31). The
  correction of the preprint is local, with no dependency audit of the
  preprint and no claim that the error was unnoticed (N32). Characters are
  not order-preserving (N33); only unit-preserving additive maps are
  excluded (N34); existence, not regularity, so no strengthening of
  Glazer's theorem and no answer to his questions (N35); the sharpness
  examples concern this detector only, with no minimality claim (N36); the
  compiler is per sentence, not a truth predicate, and needs a genuinely
  infinite bound (N37); `IOpen` of `𝒜_Sh` is imported, and Phillips is
  context only (N38); finite checks are not proofs (N39); the repository
  review was targeted, and Elliot Glazer is not an author or endorser
  (N40). The [write] statements do not determine the weakest fragment,
  do not separate `T^dy` from `IΔ0`, and do not address the factorial type
  in `IΔ0` models (N41).
- Source 04: AI-assisted and unrefereed; no Lean or Rocq for its new
  deductions, and the repository was not rebuilt for it (N42). Glazer's
  standard-system theorem (cited from seminar slides), Mycielski's
  theorem, classical descriptive set theory, both quantifier eliminations and
  Edgar–Miller are imported; the new deductions use full PA, not `EFA` (N43).
  No priority, for the assembled theorem or any component; Fatalini–Schindler
  (crediting de Bondt and Glazer) is a close precursor, and Lemma 24.1 is
  near Ye–Yu–Zhao's Proposition 2.6, not compared at the write (N44). Not
  Scott's problem, not Glazer's topological questions, and no arbitrary
  Turing ideal is claimed to be a standard system (N45). The omnific family
  is Cantor-parameterized by real coefficients but **discrete** in the
  surreal order and valuation topologies (N46); its independence is over
  `k_{R,Y}((t^Q))`, not over `R` or `No` (N47); set-sized Hahn fields only,
  `No` never a set (N48). No uniform root selector, no computable member,
  parametrization or injection of the Cantor sets, no common digit sequence
  across places (N49); no positive-measure independent Cantor set, the real
  dimension statement is inherited, no p-adic dimension claim (N50). It does
  **not** embed the Peano ring into `Oz` (N51). Countable advice concerns
  field generation, not Turing-ideal enlargement; no completeness,
  computable selector, Polish topology on `R_M` or continuous arithmetic
  (N52). Its eleven questions are its own (N53); its finite checks certify
  no infinitary claim (N54); its repository review read two guides at its
  pin, knew neither this report nor independent-surreal-copies, and Elliot
  Glazer is not an author or endorser (N55). The [write 04] corollary covers
  countable PA models only and imports Scott's theorem (N56).

The open questions are Questions 28.3–28.27: multiplicative compatibility of
the normalization, formal certification and uniqueness (source 01); an
intrinsic characterization of `Init`, the obstruction in every intermediate
theory of the optimality question, the weakest arithmetic fragment (28.7,
partly answered and re-scoped with source 03), and multiplicative
compatibility of compression (source 02); source 03's eight (28.9–28.16):
minimal detector complexity, the induction threshold, residue images of
`IΔ0` models (28.11, **answered for Peano arithmetic by source 04** and
re-scoped in a dated note: open for `IΔ0`), fixed syntactic resources,
weaker division hypotheses, integer parts inside surreal fields, regularity
of residue maps, and a focused proof-assistant milestone; and source 04's
eleven (28.17–28.27): the weakest arithmetic for its package (bears on
28.11), effective strength, descriptive complexity of the scalar fields, a
shared digit family at all places, p-adic dimension, realization of local
shadows, reconstructing Turing reducibility from `Ẑ(𝒮)`, regularity below
analyticity, beyond coefficient-preserving Hahn extensions, completions with
a distinguished image, and a machine-checked bridge. Questions 28.1 (other
convex quotients) and 28.2 (limit iteration) are answered.

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
  and `res_G` are local to Sections 11–18, source 03's renamed symbols
  (Section 19.2) to Sections 19–22, and source 04's (Section 23.2) to
  Sections 23–26.

Source 03 (Section 27.5, "Place in the collection") adds these relations:

- **omnific-diophantine-geometry** defines `Z` in `Oz` by an *existential*
  quartic (`odg:thm:standarddef`, macro `Std`) and has failed *existential*
  induction instances (`odg:thm:induction`, `odg:rem:ringinduction`).
  Source 03's `Std^dy` is bounded, not existential, and is printed with a
  different symbol for that reason; it bears neither on the guard question
  `odg:q:guard` nor on those definitions. The uniqueness of `ct`
  (`odg:prop:canonicalct`) is the `Oz` case of Proposition 21.2, and the
  existence transfer behind Hilbert's tenth problem over `Oz`
  (`odg:cor:H10`) is the Diophantine retraction of Section 22.6. The open
  induction of `Oz` (after `odg:thm:induction`) and of the definable integer
  part `I_A` (`dsn:cor:openinduction`, with `dsn:prop:ct`) is consistent with
  Theorem 19.7: these rings fail the bounded instance `Ind(Std^dy)`.
- **[polish-models-of-omnific-arithmetic](../../foundations-and-computation/polish-models-of-omnific-arithmetic/)**
  was placed from the same delivery (batch 86, arrival `fb8414869`; its
  Parts III–V were written from manuscripts 06–09 alongside this write, in
  `c3661c2ee`). It is motivated by the same paper of Elliot Glazer and proposes an
  affirmative construction for his Question 2; source 03 is not topological,
  answers neither of Glazer's questions, does not discuss his speculation
  after Question 2, and its obstruction precedes any topology (Remark 20.8).
  Manuscript 06 there proves the same failed open-induction instance
  `x² < t` in `Z + tR[t]` that source 03 gives for `Z + XQ[X]` (Section
  21.2). Placing source 03 there, as a further part, was the alternative
  considered at placement; it was placed here because it answers part of a
  question this report names. Now that it is written (batch-86 reciprocal
  notes): its Part I models `D ×_lex Z` are split `Z`-groups, so Main
  Theorem E (`isg:cf:main:presburger`) applies to them, as its Section 1.4
  says without checking whether its embeddings into `Oz` are initial
  realizations; its Part III sources cite `isg:thm:suspension`,
  `isg:cf:main:presburger` and `isg:cf:thm:PA`; the failed instance `x² < t`
  in `Z + tR[t]` is its `pma:cp:thm:openfailure`; and the Shepherdson ring
  `A_Sh` used here is its Part V integer part `I_k` for `k = R_alg`, with
  `t = X^(-1)` (`pma:ser:thm:commonip`, `pma:ser:prop:iopen`). A sentence in
  its Section 42 ("The same failed instance elsewhere") names source 03's
  `isg:sc:thm:nochar`, `isg:sc:cor:omnific` and `isg:sc:cor:fragment`.
  Batch 87 added its Parts VI–IX (reciprocal notes, 3 October 2026). Its
  source 13 presents `G_{ε₂}` of this report's factorial family, with `ε₂`
  the profinite integer with 2-adic coordinate 1 and odd coordinates 0, as
  `Z_(2) × Z[1/2]` and says so (`pma:nsp:prop:nonsplit-core`); its source 14
  builds `G_{ζ*}` again, coordinates exchanged, without citing this report
  (`pma:atr:lem:D`). Placed below `R` or `Q^N` such groups give nonsplit
  Polish Presburger models (`pma:nsp:thm:countable-core-transfer`), which by
  `isg:cf:cor:unit` admit no unit-preserving additive map to `Oz`, as both
  sources prove again (`pma:atr:prop:surreal`). A dated note after the
  paragraph following `isg:cf:cor:unit` records this.
- **Formal projects.** The `Oz` ingredients of source 03 are formalized in
  `Algebra/SurrealNumbers/Surreal/Foundations/OmnificResidues.lean`
  (`omnific_int_dvd_iff`, `omnific_prime_pow_dvd_iff`,
  `omnific_dvd_all_pos_int_iff`, `iInf_omnific_int_multiples`, namespace
  `Surreal.Foundations.SignSequence`; blob `aacd3cac`, the one source 03
  read, unchanged at this write), with the constant term
  `omnificConstantCoeff` (`OmnificIntegers.lean`) and its uniqueness
  `omnific_int_hom_eq_constant` (`OmnificConstantRigidity.lean`). No
  statement of source 03 and no [write] statement is formalized; placing
  the report in this collection confers no formal status. The arithmetic
  syntax `Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean` has
  `SetTheory.PA.PreModel` (no axioms) and `SetTheory.PA.Model`, whose
  induction for every Lean predicate makes it standard, so a nonstandard
  `IΔ0` model would be a `PreModel`; `Logic/PresburgerArithmetic` decides
  additive arithmetic over the ordinary integers. Neither formalizes
  anything here.

Source 04 (Section 27.5, "Place in the collection") adds these relations:

- **[independent-surreal-copies](../independent-surreal-copies/)** proves the
  coefficient-extension lemma `isc:cp:lem:coeffld` (`F` and `F_0((t^Γ))`
  linearly disjoint over `F_0`, same small-`t` convention), from which
  Theorem 26.1 follows at once; source 04's fields `k_{R,Y}` are a new
  instance, not a new method.
- **[omnific-diophantine-geometry](../omnific-diophantine-geometry/)** proves
  `Oz/nOz ≅ Z/nZ` and the p-adic and profinite completions of `Oz` with
  kernel `Π` (`odg:thm:finitequotients`, `odg:eq:profinite`, Lean-proved);
  Proposition 25.6 and the `𝒜`-half of Theorem 25.7 are their set-sized
  versions. Its example `ω`, `√2 ω`, `0`, identical in every finite
  quotient, is of the same kind as the family of Theorem 26.3, whose members
  are moreover independent over a large coefficient field.
- **[polish-models-of-omnific-arithmetic](../../foundations-and-computation/polish-models-of-omnific-arithmetic/)**
  (Borel and Polish models of arithmetic after Glazer's *Topological
  Tennenbaum Theorem*) was the alternative considered at placement; source
  04 uses a different result of Glazer's (standard systems), assumes no
  topology on `R_M`, and answers none of its questions. Batch-90
  manuscripts 01 and 03 became its Parts XI–XII.
- **[cantor-families-of-surreal-subfields](../../foundations-and-computation/cantor-families-of-surreal-subfields/)**,
  written from batch-90 manuscript 04, studies Cantor families of countable
  subfields of one countable surreal field: shared words (Cantor families,
  subfields), no shared theorem.
- **Formal projects.** The `Oz` analogues of Proposition 25.6, Theorem 25.7
  and Theorem 26.3 are Lean theorems (named under "What the report claims");
  no statement of source 04 and not the [write 04] corollary is formalized,
  and the repository has no Lean development of nonstandard models of PA (a
  nonstandard model would be a `SetTheory.PA.PreModel`, as above). Source 04
  cites `Logic/PeanoArithmetic/ListCoding/README.md` for the distinction
  between standard-natural evaluation of PA formulas and internal PA
  derivability, which its exact-residue theorem needs on the internal side;
  that project formalizes nothing here.

No `isg:` statement has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md).

## Provenance

Four manuscripts (Section 27.5 gives the details and the merge choices; the
source table is at the top of this README).

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
  provenance and placement review (now Section 27.5); the collected
  non-claims (now Section 28.1); a definition of `ct`; the shipped file names; labels on
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
  (after Corollaries 8.4 and 8.6, Questions 28.1–28.2, N10) now say which
  source proves what; no mathematical statement of source 01 changed.
- **Source 03**, *Standard Integers in a Single Infinite Interval: Residue
  Characters, Bounded Induction, and Omnific Arithmetic* (20 pages, 3
  October 2026), batch-86 manuscript 10, archive
  `Glazer_ProveIt_Arithmetic_Research.zip` (inner directory
  `standard_integers_in_infinite_interval/`) in the arrival commit
  `fb8414869`, placed in `0bd0e5527` as an addition. Repository pin
  `883e0b3b2` (an ancestor of the placement). Delivered with a README, the
  source audit, two programs, two run records, a build audit, a build script
  and a checksum manifest `SHA256SUMS`; the seven staged files are listed at
  the top, the manifest was verified (10/10) and dropped, and the LaTeX
  source, PDF and README are not shipped (they survive in `fb8414869`:
  `git show fb8414869:docs/incoming/Glazer_ProveIt_Arithmetic_Research.zip`).
  Its claim about the repository (the Diophantine-retraction observation
  underlies related claims) is true (`odg:cor:H10`), and the
  `OmnificResidues.lean` blob it read is unchanged. Its bibliography was
  checked as far as Section 27.5 records (arXiv records of
  Enayat–Łełyk–Visser and Raffer; the cited pages 11–12 of the
  Enayat–Łełyk–Visser v2 PDF; Glazer's v1 text); Jeřábek's MathOverflow
  answer, Phillips and Shepherdson were not re-checked.
- **How source 03 was written in.** Its material is printed as it stands in
  Sections 19–22 (plus a summary as Section 1.6), with the symbols renamed
  in Section 19.2; its verification, Lean plan, "hypotheses that must not be
  weakened" and novelty material are source-03 paragraphs of Section 27, its
  eight questions are 28.9–28.16, its limitations N30–N40, its conclusion a
  paragraph of Section 29. Added at the write, each marked: Definition
  20.10, Corollary 20.11, Proposition 20.12 and Remark 20.13 ([write], the
  combination with source 02's criterion); Remark 20.5 ([write], the second
  route through Enayat–Łełyk–Visser's Theorem 2.9, checked in their v2 text);
  bracketed comparisons with source 02's Proposition 14.3, with the Lean
  theorem `omnific_int_hom_eq_constant`, and with the four-square formula
  for the sharpness rings; the narrowed novelty statement (bounded
  definability of `N` in `Oz` is Enayat–Łełyk–Visser's Theorem 2.9, so source
  03's novelty is the dyadic formula, its inductiveness, the character
  results, the compiler and the correction); the pointer to batch-86
  manuscript 06; a dated note re-scoping Question 28.7; three bracketed
  pointers in source 02's text (after Theorem 16.6, after Corollary 17.2,
  in N26); N41; six checklist rows in Appendix B. No mathematical statement,
  proof or example of sources 01 or 02 changed.
- **Source 04**, *Perfect Transcendence Gaps in Borel Arithmetic: Standard
  Systems, p-adic Shadows, Hahn Fields, and Omnific Integers* (26 pages, 3
  October 2026; "research manuscript prepared for Vladimir Reshetnikov",
  marked AI-assisted and unrefereed), batch-90 manuscript 06, archive
  `Perfect_Transcendence_Gaps_Package.zip` (inner directory
  `perfect_transcendence_gap/`) in the arrival commit `a162e4386`, placed in
  `12076b2e8` as an addition. Repository pin `7d9b8b957` (a merge commit,
  an ancestor of the placement). Delivered with a README, a theorem ledger,
  a source audit, `verify.py`, its record `verification.json` and a checksum
  manifest `SHA256SUMS`; the four staged files are listed at the top, the
  manifest was verified (7/7) and dropped, and the LaTeX source, PDF and
  README are not shipped (they survive in `a162e4386`:
  `git show a162e4386:docs/incoming/Perfect_Transcendence_Gaps_Package.zip`).
  It read `Algebra/SurrealNumbers/README.md` and
  `Logic/PeanoArithmetic/ListCoding/README.md` at its pin, through a
  connector; both are unchanged at this write, and what it says about them
  is true (the `Oz` facts it cites from the first are moreover Lean
  theorems). It did not know this report, `isg:sc:thm:nochar` or
  `isc:cp:lem:coeffld`. Its bibliography was not re-checked at this write;
  in particular the Glazer seminar slides on which it depends, and
  Ye–Yu–Zhao's Proposition 2.6, were not consulted.
- **How source 04 was written in.** Its material is printed as it stands in
  Sections 23–26 (plus a summary as Section 1.7), with the symbols renamed
  and the numbering correspondence in Section 23.2; its dependency ledger,
  checks, formalization plan and novelty material are source-04 paragraphs
  of Section 27, its eleven questions are 28.17–28.27, its limitations
  N42–N55, its conclusion a paragraph of Section 29. Added at the write,
  each marked or bracketed: Section 25.4 with Corollary 25.5 ([write 04],
  the Scott-set description of the images of countable PA models); the
  paragraph "Relation to this report and its neighbours" (Section 23.1);
  bracketed comparisons after Imported fact 23.6 (what depends on Glazer's
  theorem), after the residue map (standard division, `res_{R_M}`), after
  Proposition 25.6 and Theorem 25.7 (source 03's `𝒜(k,Γ)`, the `Oz`
  statements and their Lean declarations, the remark after Proposition
  20.2), after Corollary 25.8 (weaker than source 03's Theorem 20.4), after
  Theorem 26.1 (`isc:cp:lem:coeffld`) and Theorem 26.3 (the Lean
  transcendence theorem), and in Questions 28.17, 28.26 and 28.27; the
  narrowed novelty statement; the dated note re-scoping Question 28.11; N56;
  six checklist rows in Appendix B. No mathematical statement, proof or
  example of sources 01–03 changed, and no label was renamed or removed.

## Build

From this directory, with a TeX distribution providing pdfLaTeX, `newtx`,
`microtype`, `tikz`, `tcolorbox`, `aliascnt`, `hyperref` and `cleveref`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 108 pages with no errors, warnings, overfull or underfull
boxes, undefined references, multiply defined labels or duplicate
destinations; the title page is one page. Remove the auxiliary files
afterwards (`latexmk -c`).

## Rerunning the checks

**Run every suite only on a copy.** Source 01's `code/verify.py` writes its
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
Source 03's two programs write `verification.json` and
`compiler_report.json` in the current directory unless `--output` is given,
and its delivered `build.sh` (here `code/03-standard-cut-build.sh`) changes
into its own directory, runs `code/verify.py` and `code/compile_interval.py`
with those default names, and rebuilds `article.tex` in place; in this
directory it changes into `code/` and stops at once, because
`code/code/verify.py` does not exist. Source 04's program prints its report
and writes `verification.json` *beside itself* unless `--output` is given;
here that would be a stray `code/verification.json`, not the shipped record.
Use scratch output names:

```sh
cp -r . /path/to/scratch/isg && cd /path/to/scratch/isg
python code/verify.py --output rerun01.json
python -c "import json; print(json.load(open('rerun01.json')) == json.load(open('data/verification_report.json')))"
python code/02-convex-factors-verify.py --output rerun02.json
python -c "import json; print(json.load(open('rerun02.json')) == json.load(open('data/02-convex-factors-verification.json')))"
python code/03-standard-cut-verify.py --output rerun03v.json
python -c "import json; print(json.load(open('rerun03v.json')) == json.load(open('data/03-standard-cut-verification.json')))"
python code/03-standard-cut-compile_interval.py --output rerun03c.json
python -c "import json; print(json.load(open('rerun03c.json')) == json.load(open('data/03-standard-cut-compiler_report.json')))"
python code/04-transcendence-gaps-verify.py --output rerun04.json
python -c "import json; print(json.load(open('rerun04.json')) == json.load(open('data/04-transcendence-gaps-verification.json')))"
```

At the write of source 04 its program was rerun this way on a copy (Python
3.14.4): it printed `PASS` in a few seconds and the comparison printed
`True` (on Windows the file it writes has CRLF line ends, so compare the JSON
content, not the bytes). It does not use `assert`, so `-O` is harmless. It
checks 23,941 base-p digit words (p = 2, 3, 5, 7; lengths 0–5) with 139,168
prefix-residue comparisons and 23,941 uncontrolled-tail recodings, 38,000
exact finite Laurent-tail identities on 1,000 seeded pairs (seed 20261003),
seven exact Newton stages for a 7-adic root of `X² − 2` (the checked modulus
is capped at `7^12` by design, so iterations 4–6 show the same modulus while
the valuations 16, 32, 64 are checked exactly), 720 factorial-residue
samples (4,320 decoded checks), 15,120 finite coherence comparisons, all 16
idempotents modulo `8!`, 64 prime-coordinate recoveries and 272
Boolean-operation identities. These are finite exact identities: nothing in
them checks a perfect set, independence over an uncountable field, a Borel
model, overspill or Glazer's theorem.

On Windows use `py` for `python`. At the write of source 03 its two programs
were rerun this way on a copy (Python 3.14.4): they printed `PASS` in about
two seconds and under one second, and both comparisons printed `True`. Like
source 02's, they check with `assert` statements, so do not run them with
`-O`. To use source 03's `build.sh`, restore its delivery layout in a
scratch directory (`code/verify.py`, `code/compile_interval.py`, `build.sh`
and `article.tex` side by side as in the archive, or simply re-extract the
archive from the arrival commit with
`git show fb8414869:docs/incoming/Glazer_ProveIt_Arithmetic_Research.zip`).

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
formulas, not verifications of the transfinite arguments. Source 03's
suite (seed 20261003) checks 2,000 odd-factor certificates for positive
infinite polynomials of `Z + XQ[X]` (zero and negative constant terms
included), 12,000 division certificates, 4,000 character identities, 1,025
finite cases each of `Pow^dy` and `Std^dy`, and 272 pairs of distinct
evaluation kernels; its compiler audit checks five compiled sentences (all
quantifiers bounded by `H`, the report's `Ω`; atoms of degree at most 2; no
other free variable) and 768 local gate evaluations. These are finite exact
checks, not proofs of the universal theorems, and nothing evaluates a
quantifier at an infinite bound.
