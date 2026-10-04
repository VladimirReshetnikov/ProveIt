# Birthday Cutoffs and Hereditary Sets

**The set-theoretic content of bounded surreal arithmetic: bi-interpretations, elementary inclusions, axiom spectra, outer models, and surcomplex orientation**
Merged research report, 22 September 2026, from five manuscripts written
independently on the same day, all pinned to repository commit
`4f2645599121fa872c7104995e47f86f0382351f` and placed by commit `d4e71b7`;
extended on 3 October 2026 (batch 89) by Parts VI and VII, which print two
further manuscripts pinned to commit `2b7b388ba` and placed by commit
`23adb85f9`; extended on 4 October 2026 (batch 90) by Part VIII, which prints
one more manuscript pinned to commit `8dc2592e9` and placed by commit
`12076b2e8`. Prepared for Vladimir Reshetnikov.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 143 pages
README.md        this guide
02-birthday-cutoffs-SOURCE_AUDIT.md                source 02's source and novelty audit, as delivered
10-cuts-replacement-PROOF_STATUS.md                source 10's proof and provenance status note, as delivered
11-choiceless-universality-SOURCES_AND_STATUS.md   source 11's sources, scope and provenance note, as delivered
12-named-symmetries-source_audit.md                source 12's source and proof audit, as delivered
code/            02-birthday-cutoffs-verify_finite.py            (source 02)
                 05-birthdays-recover-sets-check_finite_models.py (source 05)
                 05-birthdays-recover-sets-build.sh              (source 05, see "Build")
                 06-hereditary-size-orientation-finite_checks.py (source 06)
                 07-birthday-expansion-finite_checks.py          (source 07)
                 09-bounded-arithmetic-finite_checks.py          (source 09)
                 09-bounded-arithmetic-Makefile                  (source 09, see "Build")
                 10-cuts-replacement-verify_finite.py            (source 10)
                 10-cuts-replacement-build.sh                    (source 10, see "Build")
                 11-choiceless-universality-verify_finite.py     (source 11)
                 12-named-symmetries-verify_orbit_spectra.py     (source 12)
                 12-named-symmetries-Makefile                    (source 12, see "Build")
data/            02-birthday-cutoffs-verification.json, -verification_summary.tex, -build.json
                 05-birthdays-recover-sets-finite_checks.json, -repository_audit.json
                 06-hereditary-size-orientation-finite_checks.txt
                 07-birthday-expansion-finite_checks_output.json
                 09-bounded-arithmetic-verification_report.json, -build_report.json
                 10-cuts-replacement-finite_checks.json, -build_validation.json
                 11-choiceless-universality-verification_results.json
                 12-named-symmetries-verification_results.json
```

Every label in `article.tex` carries the prefix `hset:` (372 labels). Batch 37
added `hset:rem:cutoffgaps` and changed no other number. Batch 89 added 140:
65 `hset:zr:` labels in Part VI (source 10's 42 delivered labels with the
prefix, its ten questions, and thirteen for the added numbered theorems,
convention, remarks and sections), 74 `hset:kw:` labels in Part VII (source
11's 52 delivered labels, its twelve questions, and ten added), and
`hset:q:axiomatics` on the existing Question 21.7. Batch 90 added 76, all
`hset:ns:` labels in Part VIII: source 12's 51 delivered labels with the
prefix, its twelve questions, and thirteen for the added part, sections,
convention, remarks and subsections. No earlier label was
renamed or removed and no earlier number changed. All 69
labels of the delivered base text (source 09) survive with that prefix; three of
them (`hset:prop:powerset`, `hset:sec:extensions`, `hset:app:verification`) now
sit, as second labels, on the unit into which that material was merged. No
`hset:` label has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md).

## Five sources, one report (Parts I–V)

| | Manuscript | Contributes |
|---|---|---|
| **09** | *The Set-Theoretic Content of Bounded Surreal Arithmetic* | The base: the cutoff theorem at every epsilon number (Sections 2–6), the elementary-inclusion classification (Section 9), eternity, packing and worldly cutoffs (Sections 10–11), cross-model coherence, the old-power-set detector and extension rigidity (Sections 14, 16), the orientation obstruction, and most of Section 20. Files prefixed `09-bounded-arithmetic-`. |
| **02** | *What a Birthday Cutoff Remembers* | The one-way theorem at epsilon numbers (a case of the base), ring cutoffs including `No_{<ω}` (Section 8), the collector sentence, the translated Power Set sentence at every epsilon number, preservation at epsilon cutoffs and its countable corollary, the Prikry theorem with preserved `H_κ` and the onset above the cutoff (Section 17), the example of Appendix C. Files prefixed `02-birthday-cutoffs-`, and its `SOURCE_AUDIT.md`. |
| **05** | *Birthdays Recover Sets* | The second route by graphs modulo bisimulation (Section 7), the explicit embedding formula, the `ω₁`/`ω₂` separation, nondefinability of birthday, the row-search detector `New`, `B^M ≺ B^N ⟺ M = N`, the first new birthday for any same-ordinal outer model, the countably closed example, the surcomplex forcing contrast. Files prefixed `05-birthdays-recover-sets-`. |
| **06** | *What Birthday-Enriched Surreal Fields Remember* | Singular cutoffs, the second arithmetic route by prefix-pair tables (Section 3.4), definitional equivalence with `(No_{<κ}; <, b, G_ϖ)` (`G_ϖ` the graph of the pairing polynomial `ϖ(α,γ) = (α+γ)² + α`), transfer of `≡`, the `ℶ_ω` Replacement instance, the ZF range theorem (Section 13), the four-way preservation criterion, the Prikry corollaries, two complex lifts, the orientation threshold. Files prefixed `06-hereditary-size-orientation-`. |
| **07** | *The Birthday Expansion of the Surreal Field* | The written proof of the announced full-class theorem (Theorem 18.1), the radix pairing, the `ε₀` localization, recovery of models of ZFC, stage agreement at every ordinal, the two-parameter outer-model witness, the independence property and an omitted type, o-minimal nondefinability, Kunen transfer (Section 18.2) and the surcomplex elementary self-embeddings. Files prefixed `07-birthday-expansion-`. |

The source manuscripts themselves are not shipped; their code, data and source
02's audit are, under the prefixes above. Source numbers are the placement
batch's and are local to this directory. Source 02's delivered `SHA256SUMS.txt`
and all delivered PDFs were dropped at placement.

## Two later parts (batch 89)

| Source | Batch-89 manuscript | Archive (arrival `7c0f2d9f9`) | Pin | Placement | Printed as |
|---|---|---|---|---|---|
| **10** | 03, *Surreal Cuts, Replacement, and Atom-Support Spectra: Exact principles for definable families, weak set theories, and changes of language* ("Prepared for Vladimir Reshetnikov with ChatGPT", 3 October 2026) | `Surreal_Cuts_Replacement_Atom_Support_Spectra.zip` | `2b7b388ba` | `23adb85f9` | Part VI, Sections 24–39, labels `hset:zr:`, files `10-cuts-replacement-` |
| **11** | 04, *Surreal Universality Without Choice: Exact coding strength, set-sized universal fields, and finite-transcendence collapse* (3 October 2026) | `Glazer_Surreal_Choice_Research.zip` | `2b7b388ba` | `23adb85f9` | Part VII, Sections 40–53, labels `hset:kw:`, files `11-choiceless-universality-` |

The pin `2b7b388ba` is the commit "Catalogue batches 81 to 86"; source 11
calls it a "main-tree" identifier "not asserted to be a commit identifier"
(its `SOURCES_AND_STATUS.md` keeps that wording), but it is a commit. Both
manuscripts were written independently of this report and of each other, and
cite no report of the collection. Each part prints its source in full, in its
order: the title-page status box and the abstract, then every section and
appendix, with labels prefixed, questions labelled, and the renamed symbols of
Conventions 24.4 and 40.1. No mathematical statement or proof was changed. Not
shipped (they survive in the arrival commit `7c0f2d9f9`): the two manuscripts
(`article.tex`, 926 and 911 lines), their READMEs, their PDFs (23 and 22
pages) and their checksum files `SHA256SUMS` (8 of 8 and 6 of 6 entries
verified at placement). Sections 39 and 53 hold each part's non-claims and
provenance.

**Why here.** Source 10's spine is the weak-base (Zermelo, no Replacement)
form of Theorem 10.4 (`hset:thm:eternity-replacement`): bounding the
birthdays of definable surreal families is Replacement (Remark 24.5 compares
the two; they do not contain each other). Source 11 answers in part the open
item of Question 21.7 (`hset:q:axiomatics`), "a universal embedding theorem
without Global Choice", beside the choice-free Section 13
(`hset:thm:choice`; Remark 40.3 compares the two codings).

**Why one report.** All five prove one spine: the ordered field of surreals below
a cutoff, expanded by birthday, interprets the hereditary sets `H_κ` through sign
bits read from order and birthday, a bounded ordinal pairing polynomial and
pointed well-founded relation codes. Source 09 is the base because it covers the
widest cutoff class (all epsilon numbers) with the strongest conclusion (two-way,
with a pointed target at noncardinal cutoffs).

**Printed once, credited to all.** Prefix and bit formulas (all five); bounded
pairing (four variants, Remark 4.4); rooted collapse and exact range (02, 06, 07,
09); the bi-interpretation at cardinal cutoffs (05 regular; 06, 07, 09 all); the
`ε₀` case (02, 07, 09); the collector sentence (02, 09); the elementary-inclusion
classification (02 one direction; 05, 06, 07, 09); the Power Set threshold (02,
06, 09); absoluteness of old arithmetic (02, 05, 07, 09); the preservation
criterion (02, 06, 07, 09); the first new birthday (02, 05, 07); outer-model
non-elementarity (05, 07, 09); Prikry invisibility (02, 06); rigidity of the
bounded structures (05, 06, 07, 09); real-axis recovery (all five); the
two-element automorphism group (05, 06, 07, 09).

**Kept twice, as different proofs.** Arithmetic certificates: 09's option graphs
(Theorem 3.3) and the prefix-pair tables of 05, 06, 07 (Theorem 3.6). Set codes:
09's extensional codes with isomorphism (Section 5) and 05's graphs modulo
bisimulation (Section 7). Existence of the first new birthday: the new-subset
lemma of 05 and 07, and 02's generic-filter argument for set forcing (Remark
15.5). Three distinct new-subset detectors (Section 16).

**Renamed to avoid collisions** (Convention 1.5 lists every rename). The carrier is
`No_{<λ}` (02's `F_λ` and 09's `K_λ` would clash with the collection's Hahn
workspaces `F_Γ`, `K_Γ` and with `K` for a complex field). 02's pairing length
`B_θ` is `Λ(θ)`; the coordinate birthday (`β` in 02, 05, 09; `B` in 06, 07) is
`cb`; conjugation is `c` everywhere (09's `σ`, the overline in 05 and 07). **`β`
is reserved for the first new birthday of an outer model**, as in the sibling
report; sources 02, 05, 07 wrote `δ` for it, and here `δ` is only a code domain.
09's ordinal code `O(a)` is `OC(a)` (the collection's `𝒪` is a valuation ring).
06's `𝒜_κ` is `B_κ`. "Collect" meant two different sentences: 02's
`CollectOrd` is the collector sentence `∃C Coll(C)`, and 06's `Collect_ℶ` is the
Replacement instance `Rep_ℶ`. The sans-serif `P` meant fiber packing in 09 and
Power Set in 02 and 06: they are `Pack` and `Pow^I`, and `Pack` is not the Power
Set axiom. 09's eternity bound `β` is `ϱ`. `H_κ` is always a hereditary-size
universe, not the collection's value-group subgroup `H_α`.

**Renamed in the later parts** (Conventions 24.4 and 40.1, each with the
tempting false reading). Source 10: its hierarchy axiom `H` is `Hier` (not
`H_κ`); its set-graph scheme `SG` is `Gr` (not the operator `SignGraph`); its
kernel models `M_κ` are `M^ker_κ` (not the outer models `M`, `N` of Part III);
its countermodel `M = V_{ω+ω}` is written `V_θ`; its generic ordinals `β`, `δ`
are `ζ`, `σ` (`β` and `δ` are reserved here). Source 11: `S_κ = {−,+}^κ` is
`𝕊_κ` (sources 05 and 06 used `S_κ` for the carrier `No_{<κ}`); its free field
`K_κ` is `𝓡_κ`; its sign code `C_α` is `enc_α` (not a relation code `C`); its
code and birthday levels `ρ(X)`, `β(X)` are `cl(X)`, `bl(X)`; its acting group
`H` is `G_0`; its generic `β` is `ζ`. Its `No_{≤α}` is `No_{<α+1}`, not the
carrier `No_{<λ}`; its `c` (an injection) and source 10's `c` (a separator) are
not the conjugation. Macro names only: source 10's `\SG`, `\Coll`, `\Ord`,
`\ZFC` and `\bday` clashed with this report's macros and were mapped.

## A further part (batch 90)

| Source | Batch-90 manuscript | Archive (arrival `a162e4386`) | Pin | Placement | Printed as |
|---|---|---|---|---|---|
| **12** | 05, *Named Symmetries and Replacement: An exact orbit criterion, a strict kernel hierarchy, and invariance of the pure surreal universe* ("Prepared for Vladimir Reshetnikov with ChatGPT", 3 October 2026) | `Named_Symmetries_and_Replacement.zip` (335,558 bytes) | `8dc2592e9` | `12076b2e8` | Part VIII, Sections 54–66, labels `hset:ns:`, files `12-named-symmetries-` |

The pin `8dc2592e9` is a merge commit of 3 October 2026 and an ancestor of the
batch-89 placement `23adb85f9`: at the pin neither Part VI nor
[naming-elementary-embeddings](../../../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/)
existed. Source 12 read source 10 (its "earlier companion working note")
outside the repository and assumes none of its theorems; it does not cite that
report. It inspected the surreal README, whose blob `18478d586` is the same at
the pin and now. Part VIII prints it in full, in its order (status box and
abstract, then every section, its two appendices as subsections of Section 66),
with labels prefixed, its twelve research questions labelled as Questions
65.1–65.12, and the renamed symbols of Convention 54.1. No mathematical
statement or proof was changed. Not shipped (they survive in the arrival
commit `a162e4386`): the manuscript (`article.tex`, 915 lines, 51 labels), its
README, its PDF (23 pages) and its checksum file `MANIFEST.sha256` (7 of 7
entries verified at placement). Section 66 holds its non-claims and
provenance.

**Why here.** Source 12 answers source 10's Question 38.6
(`hset:zr:q:expansions`, "Classify predicates P for which (M^ker_κ, P) retains
Replacement ... How much of the permutation group must remain available to
force kernel confinement?") for κ = ω and the graphs of uniformly named
actions of pure set-sized groups (Remark 54.2); its Section 63 continues Part
VI's Section 35 (its Theorem 63.1 is the case κ = ω of Theorem 35.2,
`hset:zr:thm:purecollection`, by a second route); and it has surreal content
(the pure sign-sequence `No` and set-indexed cut interpolation survive every
naming). The alternative, a second part of naming-elementary-embeddings, was
considered at placement: that report's principal theorem is source 12's full
criterion for finitely many named permutations (Remark 54.4).

**Renamed in Part VIII** (Convention 54.1, each with the tempting false
reading). Source 12's named-action predicate `E` is `Act` (not source 10's
enumeration predicate `E`, Section 34), its structure `𝓜_E` is `𝓜_Act` and its
exceptional set `X_E` is `X_Act`; its finite-kernel universe `M = M_fin(A)` is
`M^ker_ω` (the kernel model of Part VI at κ = ω, not the ground model `M` of
Part III); its ambient universe `U` is `𝒰`; its centralizer `H = Aut_Γ(A)` is
`𝒵` (not `H_κ`); its pure rank bound `β` is `ζ` (`β` is reserved). Its
involutions `σ`, `τ` and its `c`, `C_n`, `B(q)`, `D_k`, `I`, `V` keep their
letters, with the readings to avoid listed in the convention.

## What the report claims

Numbers refer to the built `article.pdf`. `B_λ = (No_{<λ}; 0,1,+,−,·,<,b)` with
`b` the birthday as a surreal ordinal; `κ(λ)` is the least cardinal `≥ λ`.

1. **Cardinal rounding and cutoff recovery (Theorem 1.1, proved as Theorems 5.3,
   6.2, 6.3).** For every epsilon number `λ`, one parameter-free interpretation
   gives `I(B_λ) ≅ H_{κ(λ)}`. At cardinal cutoffs, singular ones included, this is
   a uniform bi-interpretation with `H_λ`; at noncardinal cutoffs it is one with
   `(H_{κ(λ)}, ∈, λ)`, and `λ` is recovered by a collector (Theorem 6.2: the
   collector sentence holds exactly at noncardinal epsilon cutoffs). Corollary
   6.4: `B_{ε₀}` is parameter-free bi-interpretable with `H_{ω₁}`. Reverse
   arithmetic without Replacement in `H_κ`: Theorems 3.3 and 3.6. Second route
   by bisimulation: Theorem 7.2. Ring cutoffs, forward only, including
   `No_{<ω}` onto the hereditarily finite sets: Proposition 8.1.
2. **Elementary inclusions and embeddings.** For epsilon `λ < η`,
   `B_λ ≺ B_η ⟺ λ, η are cardinals and H_λ ≺ H_η` (Theorem 9.3); comparison
   with the full class (Corollary 9.9); `B_{ω₁} ≢ B_{ω₂}` (Example 9.6);
   transfer of `≡` (Corollary 9.7); elementary embeddings between cardinal
   cutoffs correspond to those of the `H_κ`, with an explicit formula (Theorem
   9.10, Corollary 9.12).
3. **Axiom spectra.** Eternity fails at noncardinal cutoffs and is Replacement
   at cardinal ones (Theorems 10.2, 10.4); the translated Power Set sentence and
   fiber packing hold exactly at strong-limit cardinals (Theorems 10.7, 10.9);
   eternity plus packing holds exactly at worldly cardinals (Theorem 11.2); the
   `ℶ_ω` examples (Example 11.4, Theorem 11.5: `B_{ℶ_ω} ⊀ B_{ℶ_ω⁺}`); singular
   worldly cutoffs from an inaccessible (Proposition 11.7).
4. **Model theory.** Full second-order arithmetic is interpreted (Proposition
   12.1); undecidability (Corollary 12.2); independence property and an omitted
   type (Proposition 12.3); birthday is not definable in any o-minimal expansion
   of the field (Proposition 12.5); `(No_{<κ}; <, b, G_ϖ)` (`G_ϖ` the graph of the pairing polynomial `ϖ(α,γ) = (α+γ)² + α`) is definitionally
   equivalent to `B_κ` (Corollary 12.6).
5. **Choice (ZF).** The graph coding reaches exactly the sets with well-orderable
   transitive closure; surjectivity onto `V` is equivalent to Choice (Theorem
   13.2); internal Choice is a different statement (Proposition 13.3).
6. **Outer models** (`M ⊆ N` transitive, same ordinals). Old arithmetic is
   absolute and the field reducts include elementarily (Proposition 14.2);
   cross-model coherence (Proposition 14.3); exact preservation criterion at
   every ordinal, epsilon number and cardinal (Theorem 15.1); first new birthday
   `β(M,N)` = least ordinal with a new subset, an infinite cardinal of `M`
   (Theorem 15.4); old-power-set detector and its sharp cost (Theorem 16.1,
   Proposition 16.2); strong-limit extension rigidity (Theorem 16.4);
   `B^M ≺ B^N ⟺ M = N` (Theorem 16.5) and the row-search formula `New`
   (Theorem 16.6).
7. **Prikry (assuming a measurable cardinal in `M`).** `B_κ^M = B_κ^{M[G]}` and
   `H_κ^M = H_κ^{M[G]} = V_κ^M ⊨ ZFC` while `cf(κ)` becomes `ω` (Theorem 17.1);
   hence no uniform regularity detector (Corollary 17.2); the first new birthday
   is `κ` and the new sequence lives in `H_{κ⁺}` (Proposition 17.3).
8. **Full class.** The announced Chen–Hamkins–Yang bi-interpretation, with
   source 07's written proof (Theorem 18.1); under GBC, no nontrivial class
   elementary self-embedding of the full birthday structure (Theorem 18.3).
9. **Surcomplex** (with conjugation `c` and coordinate birthday `cb`).
   Real-axis recovery and bi-interpretation once `i` is named (Proposition
   19.2); `Aut = {id, c}` and mutual interpretation without bi-interpretation
   (Theorem 19.4, after Jeřábek); exactly two elementary lifts of each real
   elementary embedding (Theorem 19.5); one nonreal parameter, but no set of real
   parameters, defines an orientation (Theorem 19.6); under GBC the elementary
   self-embeddings of the full structure are `id` and `c` (Theorem 19.7);
   outer-model contrast (Theorem 19.8).
10. **Part VI: Replacement-free cuts and atom-support spectra (source 10).**
    Over `Z_f` (Zermelo with Foundation, no Replacement, no Choice): every set
    cut has a unique simplest separator, of birthday at most the supremum of
    the endpoint birthdays plus one, sharp (Theorem 27.1, Proposition 27.3);
    six definable-family schemes — ordinal bounding `OB`, set graphs `Gr`,
    upper bounds `UB`, surreal Collection `SC`, definable-cut interpolation
    `DCI`, bounding inside `(−1,0)` `NIB` — are equivalent (Theorem 28.2), and
    over `Z_f + Hier` each is full Replacement and full Collection (Theorem
    29.1); `V_{ω+ω}` satisfies `Z_f + Hier + AC` and fails `OB`, Replacement and
    `NIB` (Proposition 30.1). For kernel models `M^ker_κ` over a set of at least
    κ atoms with ambient Choice: `ZFU_R + AC` with the same pure sets (Theorem
    32.2); Collection holds below `cf κ` and fails at `cf κ` for limit κ (ω
    included), and holds in full for successor κ (Theorems 33.2–33.3,
    Corollary 33.4); naming an enumeration of κ atoms makes Replacement and
    Collection both fail first at `cf κ` (Theorem 34.2), while pure-valued
    Collection and all six surreal schemes survive (Theorem 35.2, Corollary
    35.3), so no pure-surreal principle characterizes ambient Collection
    (Corollary 35.4).
11. **Part VII: choiceless universality (source 11).** Over ZF: `X ↪ No` iff
    `X ↪ P(α)` for some ordinal α (Theorem 42.1; also in ZFA with pure
    surreals); `No_{≤κ} ≈ P(κ)` (Proposition 42.3); the double monomials
    `ω^(ω^j(x))` are algebraically independent positive infinite omnific
    integers (Theorem 43.1); coordinate universality of `No` and `Oz` for free
    rings and fields on all sets is exactly `KWP_1` (Theorem 43.5); a set-sized
    real-closed `U_κ ≈ P(κ)` realizes exactly the free fields on sets injecting
    into `P(κ)` (Theorem 44.3); order embeddability reduces to the free ordered
    field (Theorem 45.2) and is characterized by convex resolutions (Theorem
    46.2); well-orderable linear orders embed (Proposition 45.3). In ZFA
    permutation models: orbit factorization (Theorem 47.1) gives the sharp
    transcendence bounds `s+1` (basic Fraenkel) and `2s+1` (ordered Mostowski)
    for maps with atom support of size s (Theorems 48.1, 48.3), and in the
    ordered model an ordered field all of whose finite coordinate subfields
    embed has no embedding into the internal `No` (Theorem 49.1); a global
    embedding is exactly a compatible family (Theorem 49.3).
12. **Part VIII: named symmetries and Replacement (source 12).** In the
    finite-kernel model `M^ker_ω` over an infinite set of atoms (ambient Choice,
    Replacement, Collection), expanded by the graph `Act` of a uniformly named
    action of a pure set-sized group Γ: the base axioms and expanded Separation
    hold and full Collection fails (Propositions 55.2–55.3); a unique output's
    kernel is a union of orbits of the centralizer `𝒵` (Lemma 56.1), and
    `𝒵`-orbits of a type with `m_t` copies have size `m_t d_t` (Lemma 56.3).
    Replacement holds iff every Γ-orbit is finite and the union `X_Act` of the
    finitely repeated finite orbit types is finite (Theorem 58.1); every finite
    group is harmless (Corollary 58.2). For `k ≥ 1`, Replacement for outputs
    with at most `k` atoms, `R_k`, holds iff every orbit is finite and only
    finitely many atoms have `𝒵`-orbit of size at most `k` (Theorem 59.1),
    which fixes the first failing level (Corollary 59.3). One permutation:
    finite cycles give every `R_k`, one cycle of each length gives every `R_k`
    but not Replacement (Theorem 60.1, Example 60.2). For every `d ≥ 1`, two
    involutions, each harmless alone and with finite joint orbits, give exactly
    the levels `k < d` (Theorem 61.3). Separately named involutions are safe
    while their uniform evaluator destroys `R_1` (Theorem 62.3); lifts to the
    membership universe are definable (Proposition 62.4). Pure-valued
    Collection survives every naming (Theorem 63.1), so the pure universe, the
    sign-sequence `No`, surreal-valued Replacement and set-indexed cut
    interpolation are unchanged (Proposition 63.2, Corollary 63.3), and no
    pure-surreal scheme implies `R_1` (Corollary 63.4). For finitely many named
    permutations Theorem 58.1 is not new in ProveIt: it is Theorem 5.1(2) of
    naming-elementary-embeddings (Remark 54.4).

## What the report does not claim

Section 20.6 lists every non-claim of sources 02–09, and Subsections 39.4,
53.3 and 66.4 those of sources 10, 11 and 12; none was dropped.

- **Part VIII.** Source 12 is an unrefereed draft prepared with ChatGPT, not
  Lean- or Rocq-checked; the finite-kernel model and its symmetry method are
  classical (Lévy, through Hamkins–Yao); its classifications are proposed
  refinements without established priority; it solves no named conjecture and
  neither strengthens nor reopens Glazer–Yao's separations; Glazer is not a
  coauthor or endorser. Its 203 finite checks validate finite centralizer
  calculations only, and a finite truncation of an example refutes nothing.
  Its ambient metatheory has Choice; formulas are relativized one at a time,
  with no truth predicate; the models already fail Collection in the reduct, so
  only expanded Replacement changes. Pure invariance validates no unrefereed
  repository claim and does not identify an atom-enriched presentation with
  the pure one. It inspected the repository read-only and audited or built
  nothing.

- **Later parts.** Sources 10 and 11 are unrefereed and AI-assisted (source 11
  calls itself AI-generated), not Lean- or Rocq-checked, and claim no
  priority; their classical inputs (simplicity, small-kernel models after
  Hamkins–Yao, Lévy, Glazer–Yao and Yao; Kinna–Wagner principles after
  Karagila–Schilhan; permutation models) are credited. Source 10's full
  Replacement conclusion assumes `Hier`; Replacement for a reduct is not
  Replacement for an expanded language; pure-valued Collection is not
  Collection; its models are relative interpretations, not consistency
  proofs. Source 11's counterexample is in ZFA, with no ZF transfer;
  prescribed-order universality from `KWP_1` is not proved; no birthday bound
  for `U_κ` is claimed. Neither solves Glazer–Yao's reflection questions or any
  named problem. The Part VI Collection spectrum is proved independently in
  the research-report collection (below); neither is claimed first.

- **Priority.** The full-class bi-interpretation is the announced work of
  Chen, Hamkins and Yang, recorded in the foundations report
  (`found:sub:announcement`). Theorem 18.1 prints source 07's argument as a proof
  of that announced theorem, **not** as a new result; sources 05 and 07 omitted
  the credit and it is restored. The conjugation/named-`i` obstruction is
  Jeřábek's (2021); only source 06 credited it, and the credit now covers every
  version. The local refinements are proposed, "not located in the inspected
  sources", and may overlap unpublished details of the Chen–Hamkins–Yang project.
- The proofs are written arguments, not refereed and **not formalized in Lean**.
  The finite programs check finite analogues only. No named conjecture is
  resolved.
- Hypotheses stay attached: the Prikry results assume a measurable cardinal and
  are relative-consistency statements about fixed first-order sentences; Theorems
  18.3 and 19.7 assume GBC (or class-parameter Separation and Replacement);
  Proposition 11.7 assumes an inaccessible; source 02's first-new-birthday
  theorem assumed set forcing (the printed theorem uses any same-ordinal outer
  model, from 05 and 07); source 05 worked only at regular cardinals.
- `H_κ` is not `V_κ` in general; interpreting `H_{κ(λ)}` does not assert that it
  satisfies ZFC; `Et` and `Pack` are explicit schemes, not identified with any
  formulation of a surreal-arithmetic theory; the Power Set sentence does not
  detect regularity; the `ℶ_ω` theorem does not show that every singular cardinal
  fails Replacement.
- Detectors show failure of elementarity with old parameters, not different
  parameter-free theories; the old-power-set bound is sharp only for that
  parameter; no quantifier-complexity claim is made across the translation.
- The surcomplex conjugation and coordinate birthday are stated structure, not
  definable in the pure field; nothing classifies automorphisms or embeddings of
  the pure surcomplex field.
- No choice-free version of the cutoff theorems (Part VII works over ZF, but
  on injections and universality, not on the cutoff structures); nonstandard
  models are handled internally only; cutoffs that are not epsilon numbers are not classified (ring
  cutoffs forward only).
- No product-birthday bound `b(xy) ≤ b(x) ⊗ b(y)` is used; that is Gonshor's
  conjecture, which [gonshor-product-birthdays](../../surreal/gonshor-product-birthdays/)
  proves on a specified ring and states is not settled in general.

## Open questions, re-scoped (Section 21)

Answered inside the report: source 02's sufficiency question for elementary
inclusions (by 09, Theorem 9.3); 02's caution about a two-way theorem (by 09's
pointed bi-interpretation); 05's optimal cutoffs at singular cardinals (by 06, 07)
and at noncardinal epsilon numbers (by 09); 06's and 07's noncardinal-cutoff
questions (by 09, for epsilon numbers); 09's choice-free target (by 06's Theorem
13.2, for the full-class coding). Still open: cutoffs that are not epsilon
numbers; the minimal signature (06's Corollary 12.6 is partial progress);
explicit criteria for `H_κ ≺ H_τ` and bounded elementary self-embeddings (reduced
to `H_κ`); changes of parameter-free bounded theories under forcing; quantifier
complexity of a detector; surcomplex reducts without conjugation and `i`;
axiomatic comparison with a finalized surreal-arithmetic theory; formalization.

Since batch 89, the item "a universal embedding theorem without Global
Choice" of Question 21.7 (source 06's) is **answered in part** by source 11
(dated notes after Question 21.7, in the answered list of Section 21, after
source 06's non-claims in Section 20.6 and after Theorem 13.2): over ZF,
coordinate universality is exactly `KWP_1`, with optimal targets `U_κ`;
well-orderable orders embed; a ZFA ordered field with all finite stages
embeddable has no embedding. Still open: prescribed-order universality,
general ordered fields, and a ZF transfer (Questions 51.1, 51.2, 51.5). Parts
VI and VII add their own questions (Questions 38.1–38.10 and 51.1–51.12, labels
`hset:zr:q:` and `hset:kw:q:`); dated notes record that Question 38.3 is
answered for full-class rank models only (`surreal-well-orders` Part XV), and
that Questions 38.6 and 38.7 are answered for one family of expansions, or
bear on it, in `naming-elementary-embeddings`; all stay open.

Since batch 90, Question 38.6 (`hset:zr:q:expansions`) is also answered at
κ = ω for a second family, the graphs of uniformly named actions of pure
set-sized groups, by source 12 (Theorems 58.1 and 59.1; dated note after the
question, Remark 54.2); arbitrary predicates and group actions at uncountable
κ stay open. A dated note after Theorem 35.2 records that source 12's Theorem
63.1 is its case κ = ω. Part VIII adds Questions 65.1–65.12
(`hset:ns:q:`); dated notes record that Questions 65.2 (infinite kernel
bounds) and 65.11 (Collection and reflection in expanded models) are answered
in part, for finitely many named injections, by naming-elementary-embeddings
(its Theorems 5.1(1), 6.1, 7.5 and 7.7), that Question 65.1 is Question 38.4
and that report's Question 10.7 for named group actions, and that Question
65.4 meets that report's Question 10.4. All twelve stay open.

## Stale statements corrected (Section 1.5)

- Sources 05 and 07 quote the catalogue at the pin as "forty catalogued reports
  and four newly placed drafts". True at the pin; before this batch the
  catalogue listed 44 research reports in five families.
- Sources 05 and 07 report no matching reconstruction theorem in the inspected
  material (05 read only 230 lines of the foundations report, 07 its
  introduction). The Chen–Hamkins–Yang announcement is recorded there; the
  full-class statement is now credited to it.
- Sources 05 and 06 cite section structure and line ranges of the surcomplex
  automorphisms report at the pin; that report has since been rewritten. The
  cited subsection "Simplicity restores the canonical surreal numbers" is in its
  section `saut:sec:exponential`, and the relative result is `saut:thm:axis`.
- Source 06's empty GitHub search for "Hamkins" was a search-index artefact.
- 02's `SOURCE_AUDIT.md` is kept byte-identical. None of its repository
  statements is false; its closing "necessary, not claimed sufficient" describes
  source 02 and is superseded inside the report by Theorem 9.3.

## Relation to the neighbouring reports

**[foundations](../foundations/)** records the Chen–Hamkins–Yang announcement
(`found:sub:announcement`), the epsilon-number cutoffs (`found:sub:cutoffs`) and
the difference between simplicity and birthday precedence
(`found:rem:simplicity`). This report proves local versions of the announced
theorem and a written proof of the global one; it does not settle the
announced axiomatization.

**[surcomplex-field-automorphisms](../../surcomplex/surcomplex-field-automorphisms/)**
already covers the bounded automorphism statements: `Aut(F(i)/F) = {id, c}`
(`saut:thm:axis`) and simplicity rigidity (section `saut:sec:exponential`), since
order and birthday define prefix. Lemma 19.3 and Theorem 19.4 print them once
with that credit. New relative to that report are only source 07's
classification of non-surjective class elementary self-embeddings (Theorem 19.7,
under GBC) and source 06's two-lift theorem (Theorem 19.5). Its question on
`Aut_L` is untouched.

**[surreal-fields-across-universes](../surreal-fields-across-universes/)**, the
sibling report of this batch, studies external saturation of the *pure* field
`No^M` in an outer universe. It shares the setting of Part III, the first new
birthday (also written `β` there) and the forcing examples; it writes `δ` for the
first new ordinal-sequence length, which this report does not use. The pure
inclusion is elementary but can lose saturation; the birthday inclusion loses
elementarity (Remarks 12.4, 15.8). Its batch-37 Part VIII computes the exact
external gap pairs of the pure cutoff fields `(No_{<θ})^M` (its Lemma 26.1),
including asymmetric boundary pairs `(μ,θ)`, `(θ,μ)` that already occur in the
internal field `No_{<θ}`, and uses them at `θ = ℵ_{ω+2}` for `2^{ℵ₀}`
nonisomorphic real closed fields with one saturation spectrum; Remark 15.9
(`hset:rem:cutoffgaps`, added in batch 37) records this.

**[surreal-well-orders](../surreal-well-orders/)** (batch 80) proves and uses
the order-theoretic case of Remark 12.4 (`hset:rem:saturation`): for every
regular infinite κ, ω included, `No_{<κ}` fills every cut of fewer than κ
points, avoiding any fewer than κ given points (its Lemma 7.2,
`swo:sw:stageeta`; its Note 7.4, `swo:sk:prop:cutoffeta`, cites the remark).
Its Theorem 13.1 (`swo:cf:choice`) is a class-level counterpart of Theorem 13.2
(`hset:thm:choice`): over GB without set choice, Global Choice holds iff `No`
has a class well-order; its Remark 13.4 compares the two codings. Two dated
notes, bracketed "[Added 2 October 2026, batch 80: …]", after Remark 12.4 and
after Remark 13.4 (`hset:rem:answered-choice`) record this; they change no
label or number, and the open problems of Remark 13.4 are not affected. Since
batch 81 its source 17 computes the gap pairs of `No_{<θ}` itself for every
infinite cardinal θ, singular θ and θ = ω included (its Theorem 29.4,
`swo:gs:thm:alphabet-gaps`), the case M = N of the lemma quoted in Remark 15.9
(`hset:rem:cutoffgaps`) extended; a dated note, "[Added 3 October 2026,
batch 81: …]", after Remark 15.9 records it (no label, number or page count
changed).

Since batch 89 (Remark 40.4), its Part XV (batch-89 manuscript 01, its source
31) studies countable global choice over Zermelo set theory and full-class
rank models `(V_λ, P(V_λ))`; there class Replacement and Collection hold
exactly on domains of size below `cf λ`, which contains the failure of
Proposition 30.1 at `λ = ω+ω` for one definable family (Remark 24.7). Source
11's ZF bijection `No_{≤κ} ≈ P(κ)` (Proposition 42.3) sits beside that report's
ZFC count `|No_{<κ}| = 2^{<κ}`. A dated note, "[Added 4 October 2026,
batch 89: …]", after Proposition 30.1 gives that part's labels (Lemma XV.9.2,
`swo:gcz:lem:domain`; Theorem XV.9.3, `swo:gcz:thm:replacement`; Section
XV.11, `swo:gcz:sec:examples`).

**[naming-elementary-embeddings](../../../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/)**
(research-report collection, batch-89 manuscript 05, written in `aa9a7ec80`)
proves, independently and on the same pin, the same Collection spectrum for
the same kernel models (its Lemmas 7.1–7.2, Corollary 7.3, Theorem 7.5, with
kernel confinement and the base model as its Lemma 2.3 and Theorem 2.4), adds
that the failing instance at a limit cardinal is `Δ0`, and decides Replacement,
Collection and full reflection after naming canonical lifts of atom injections.
Remark 24.6 records the overlap; Part VI prints source 10's own proofs, and
neither is claimed first. Its dated note after its Corollary 7.6 compares the
two proofs. A dated note, "[Added 4 October 2026, batch 89: …]", at the end of
Section 18.2 (transfer of Kunen's inconsistency) records that its lifts of atom
injections are amenable elementary self-embeddings fixing every pure set
(`nee:thm:lifts`, `nee:thm:initial`, `nee:thm:profile`), so they do not bear on
Theorem 18.3.

Since batch 90 (Remark 54.4) Part VIII bears on that report more directly.
Naming finitely many atom permutations and naming their lifts are
definitionally equivalent (Propositions 62.1 and 62.4), so that report's
Theorem 5.1(2) (`nee:thm:profile`, at the finite cutoff) is source 12's
Theorem 58.1 for finitely many named permutations; that report printed it
first in ProveIt, with an independent proof, and also treats non-surjective
injections and every uncountable κ. Source 12, written without knowing it,
extends the finite-cutoff criterion to actions of arbitrary pure set-sized
groups and adds the graded levels `R_k`. Its Example 60.2 is that report's
Example 5.5 (`nee:ex:finite`), with every `R_k` added; its Theorem 61.3 is a
finite-cutoff, graded counterpart of that report's Corollary 7.9
(`nee:cor:jointunsafe`, at ℵ₁). Neither is claimed first.

**[definable-surreals-and-omnific-integers](../definable-surreals-and-omnific-integers/)**:
source 11's double-monomial independence (Theorem 43.1) is the case `K = R`,
`G = {0}` of its Lemma 8.1 (`dsn:lem:cosets`, "Disjoint support cosets");
Remark 40.4 records this. New beside it are the omnific-integer conclusion,
the free-algebra calibration and the ZF framing.

**[gonshor-product-birthdays](../../surreal/gonshor-product-birthdays/)**: see
above; no argument here depends on it.

**[computable-surreals](../computable-surreals/)** is a different program
(countable effective subfields); the undecidability remarks here are standard.

[single-dilation-hahn-support](../../surcomplex/single-dilation-hahn-support/)
obtains the same kind of arithmetic interpretation and undecidability, and a
TP₂ witness, for a Hahn field expanded by one exponent dilation
(`dsup:thm:undecidable`, `dsup:thm:tp2`); neither result implies the other.

## Formal status

Nothing in this report is formalized, and placement in the Surreal
collection, beside its Lean library, confers no formal status. Sources 10 and
11 name `Algebra/SurrealNumbers/Surreal/Foundations/`, `SetTheory/ZF/`,
`SetTheory/ClosureAxiomatization/` and `Algebra/SurrealNumbers/README.md`
(all present and unchanged since their pin) only as possible homes for a
future development; none of the modules they propose
(`WeakSignSequences`, …, `OrdinalSignCoding`, …) exists. The `SetTheory/ZF`
development formalizes ZF itself (for example `Repl_form`, `ZFax` in
`SetTheory/ZF/Lean/ZF/Zf.lean`), not Zermelo set theory without Replacement,
urelements or permutation models.

Source 12 names the surreal README and formalization ledger
(`Algebra/SurrealNumbers/README.md`, `docs/FORMALIZATION.md`) as entry points and
proposes a five-stage Lean/Rocq development (Section 64.3); none of it exists,
and no urelement theory is formalized anywhere in ProveIt (the formula type
`Form` of `Logic/FirstOrder/Lean/FirstOrder/Fol.lean` has `∈` and `=` only, no
atom predicate).

## What was run

- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX):
  143 pages (116 before the batch-90 Part VIII;
  115 after the batch-89 write, before its two reciprocal notes;
  62 before batch 89; 61 before the batch-37 Remark 15.9; still 62 after the
  two batch-80 notes and the batch-81 note); no errors, undefined
  references or citations, multiply defined labels, duplicate destinations,
  LaTeX or package warnings, or overfull or underfull boxes. Cross-references
  are typed (lemma, proposition, ...) through alias counters.
- Sources 10 and 11 (batch 89), with Python 3.14.4, on copies: both passed and
  reproduced their recorded files exactly apart from line endings: 10 (127 sign
  words of length at most 6, 8,256 endpoint intervals, 2,187 depth-two
  assignments of which 576 separated, 1,050 negative-code comparisons, 4,032
  atom transpositions; the record embeds the script's SHA-256, unchanged by
  byte-identical staging), 11 (20,595 assertions, seed 20261003).
- Source 12 (batch 90), with Python 3.14.4, on a copy with an explicit
  `--output`: passed 203 checks, 35 of them brute-force comparisons against
  every permutation of domains of at most seven points (seed 20261003), and
  reproduced `data/12-named-symmetries-verification_results.json` exactly
  apart from line endings. Its checks cover finite centralizer and witness
  calculations only.
- All five finite programs, with Python 3.14.4, on copies (commands below). Each
  passed and reproduced its delivered record exactly apart from line endings
  (CRLF on Windows): 02 (65,025 prefix comparisons, 1,538 bits, 173,880
  addresses, 687 relabellings, 1,024 code pairs, 4 invalid codes rejected); 05
  (65,025 prefix pairs, 4,096 graph pairs with 65,536 root-pair checks each for
  equality and membership, 64 round trips, 49 rectangles, 30 detector tests); 06
  (16,129 prefix and 642 bit instances, 10,000 pairing pairs, 1,570 rooted
  relations, 15 codes, 225 pairs); 07 (16,129 prefix, 642 sign, 819 radix
  addresses, 42,849 graph pairs each for isomorphism and membership); 09 (16,129
  prefix, 642 bit, 11,440 pairing checks, 530 relations, 1,570 rooted, 15 codes,
  225 pairs, and the negative regression of Appendix B).

A clean compile and passing finite checks prove nothing about the infinite
arguments.

## Build and reproduce

TeX Live or MiKTeX with lmodern, amsmath/amsthm, mathtools, microtype, booktabs,
longtable, enumitem, xcolor, fancyhdr, xurl, aliascnt, hyperref and cleveref. No
external figures or bibliography file.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

**Run the programs on a copy, never in this directory.** Sources 02 and 05 write
unprefixed files into `data/` beside their own `code/` directory
(`verification.json`, `verification_summary.tex`, `finite_checks.json`), and
source 09 writes `verification_report.json` into `code/` beside itself. Source 06
only prints; source 07 writes only the file named by `--output`. For example,
with a fresh empty directory `/tmp/hset`:

```
mkdir -p /tmp/hset/code /tmp/hset/data
cp code/02-birthday-cutoffs-verify_finite.py code/05-birthdays-recover-sets-check_finite_models.py \
   code/09-bounded-arithmetic-finite_checks.py /tmp/hset/code/
python /tmp/hset/code/02-birthday-cutoffs-verify_finite.py
#   compare /tmp/hset/data/verification.json and verification_summary.tex
#   with data/02-birthday-cutoffs-verification.json and -verification_summary.tex
python /tmp/hset/code/05-birthdays-recover-sets-check_finite_models.py
#   compare /tmp/hset/data/finite_checks.json with data/05-birthdays-recover-sets-finite_checks.json
python /tmp/hset/code/09-bounded-arithmetic-finite_checks.py
#   compare /tmp/hset/code/verification_report.json with data/09-bounded-arithmetic-verification_report.json
python code/06-hereditary-size-orientation-finite_checks.py > /tmp/hset/06.txt
#   compare with data/06-hereditary-size-orientation-finite_checks.txt
python code/07-birthday-expansion-finite_checks.py --output /tmp/hset/07.json
#   compare with data/07-birthday-expansion-finite_checks_output.json
python code/10-cuts-replacement-verify_finite.py --output /tmp/hset/10.json
#   compare with data/10-cuts-replacement-finite_checks.json
python code/11-choiceless-universality-verify_finite.py --output /tmp/hset/11.json
#   compare with data/11-choiceless-universality-verification_results.json
python code/12-named-symmetries-verify_orbit_spectra.py --output /tmp/hset/12.json
#   compare with data/12-named-symmetries-verification_results.json
```

Always pass `--output` to source 12's program as well: without it, it writes
`verification_results.json` into the current directory.
`code/12-named-symmetries-Makefile` is source 12's delivered Makefile, kept
byte-identical: its `verify` target runs `python3 verify_orbit_spectra.py
--output verification_results.json` and its `pdf` target runs `latexmk` on
`article.tex`, both in the delivery layout. In the shipped layout the first
names an unshipped file and the second would build this report, not source
12's manuscript; do not run it here. `12-named-symmetries-source_audit.md`
also uses delivery names (`verify_orbit_spectra.py`), and records that "the
PDF was compiled", meaning source 12's own 23-page PDF, which is not shipped;
source 12's manuscript and PDF are in
`git show a162e4386:docs/incoming/Named_Symmetries_and_Replacement.zip`.
Section 66.3 prints its reproducibility record with the shipped names.

Always pass `--output` to the programs of sources 10 and 11: without it,
source 11's program writes `verification_results.json` into `code/` beside
itself (source 10's prints only). `code/10-cuts-replacement-build.sh` is source
10's delivered build script, kept byte-identical: it changes to its own
directory and runs `code/verify_finite.py --output data/finite_checks.json` and
three `pdflatex` passes of `article.tex`, all in the delivery layout (in the
shipped layout it would look for `code/code/verify_finite.py` and would build
this report, not source 10's manuscript; do not run it here). To rerun it as
delivered, re-extract the archive from its arrival commit:
`git show 7c0f2d9f9:docs/incoming/Surreal_Cuts_Replacement_Atom_Support_Spectra.zip > /tmp/s10.zip`.
`data/10-cuts-replacement-build_validation.json` is source 10's record of its
own 23-page build, not of this report; its pointer to `finite_checks.json`
means the shipped `data/10-cuts-replacement-finite_checks.json`. "The article"
in source 11's script and record means source 11's manuscript, printed here as
Part VII. Source 11 shipped no build script; its
manuscript is `git show 7c0f2d9f9:docs/incoming/Glazer_Surreal_Choice_Research.zip`.

All programs use the Python standard library only. `diff --strip-trailing-cr`
ignores the line-ending difference on Windows. The delivered build files
`code/05-birthdays-recover-sets-build.sh` and `code/09-bounded-arithmetic-Makefile`
build their source manuscripts in their original layouts (`birthdays_recover_sets.tex`,
`surreal_cutoffs.tex`, not shipped) and do not build this report; the Makefile's
`check` target also expects the unprefixed script name. They are kept only as
delivered. `data/02-birthday-cutoffs-build.json` and
`data/09-bounded-arithmetic-build_report.json` are the sources' own build records
(25 and 31 pages, before the merge); `data/02-birthday-cutoffs-verification_summary.tex`
is source 02's generated paragraph and is not used by `article.tex`.

## Repository audits recorded by the sources

All five sources inspected `4f2645599121fa872c7104995e47f86f0382351f` read-only
and modified nothing: 02 in `02-birthday-cutoffs-SOURCE_AUDIT.md`, 05 in
`data/05-birthdays-recover-sets-repository_audit.json` (requested ranges, some
truncated), 06, 07 and 09 in their audit appendices (summarized in Section 22.1).
All audits were targeted; none treats the repository's unrefereed manuscripts as
established foundations.

Sources 10 and 11 inspected `2b7b388ba` read-only (READMEs and directory
organization; neither built the repository) and modified nothing. Source 10
records its boundaries in `10-cuts-replacement-PROOF_STATUS.md` and its build
in `data/10-cuts-replacement-build_validation.json`; source 11 in
`11-choiceless-universality-SOURCES_AND_STATUS.md`, which keeps two delivered
statements to read with care: it calls `2b7b388ba` a tree identifier, not a
commit (it is a commit); and it says a profile URL supplied to its authoring
session served only as an identifying pointer (no URL is in the file). Neither
note names a delivered file of its package, so none of their text refers to
unshipped files. Source 11's bibliography linked the surreal README through the
branch `main`; the report's entry gives the pinned commit. All their
repository statements are true at the pin and at the placement. The
Hilbert's-tenth programme routed the batch-89 archives in `6aadaa4f2`
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_topology_surreal_arrivals_20261003.md`):
bounded reads, nothing run, no correctness finding, and no Diophantine
compiler or arithmetic saving in either source.

Source 12 inspected `8dc2592e9` read-only (the surreal README, blob
`18478d586`, and the root README for orientation; no audit or build) and
modified nothing, as its `12-named-symmetries-source_audit.md` records. Its
repository statements (the sign-sequence construction and the distinction
between formalized results and AI-assisted reports) are true at the pin and
now. Its companion note is now Part VI, not a project-local file; its
`MANIFEST.sha256` is not shipped. The Hilbert's-tenth programme routed the
batch-90 archives in `bcc1a4438`
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_polish_partx_c9bc70d8f.md`):
for this archive it verified the ZIP hash and read only the delivery README
(lines 1–71), ran nothing, made no correctness finding, and found finite
centralizer diagnostics but no arithmetic compiler.
