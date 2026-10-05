# Birthday Cutoffs and Hereditary Sets

**The set-theoretic content of bounded surreal arithmetic: bi-interpretations, elementary inclusions, axiom spectra, outer models, and surcomplex orientation**
Merged research report, 22 September 2026, from five manuscripts written
independently on the same day, all pinned to repository commit
`4f2645599121fa872c7104995e47f86f0382351f` and placed by commit `d4e71b7`;
extended on 3 October 2026 (batch 89) by Parts VI and VII, which print two
further manuscripts pinned to commit `2b7b388ba` and placed by commit
`23adb85f9`; extended on 4 October 2026 (batch 90) by Part VIII, which prints
one more manuscript pinned to commit `8dc2592e9` and placed by commit
`12076b2e8`; extended on 4 October 2026 (batch 95) by Part IX, which merges two
more manuscripts, pinned to commits `722337445` and `bd1de458b` and placed by
commit `350b9a954`. Prepared for Vladimir Reshetnikov.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 212 pages
README.md        this guide
02-birthday-cutoffs-SOURCE_AUDIT.md                source 02's source and novelty audit, as delivered
10-cuts-replacement-PROOF_STATUS.md                source 10's proof and provenance status note, as delivered
11-choiceless-universality-SOURCES_AND_STATUS.md   source 11's sources, scope and provenance note, as delivered
12-named-symmetries-source_audit.md                source 12's source and proof audit, as delivered
14-surreal-only-nbg-SOURCES_AND_STATUS.md          source 14's sources, provenance and proof-status audit, as delivered
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
                 14-surreal-only-nbg-verify_finite.py            (source 14)
                 14-surreal-only-nbg-build.sh                    (source 14, see "Build")
data/            02-birthday-cutoffs-verification.json, -verification_summary.tex, -build.json
                 05-birthdays-recover-sets-finite_checks.json, -repository_audit.json
                 06-hereditary-size-orientation-finite_checks.txt
                 07-birthday-expansion-finite_checks_output.json
                 09-bounded-arithmetic-verification_report.json, -build_report.json
                 10-cuts-replacement-finite_checks.json, -build_validation.json
                 11-choiceless-universality-verification_results.json
                 12-named-symmetries-verification_results.json
                 14-surreal-only-nbg-verification.json, -build_validation.json
```

Every label in `article.tex` carries the prefix `hset:` (525 labels). Batch 37
added `hset:rem:cutoffgaps` and changed no other number. Batch 89 added 140:
65 `hset:zr:` labels in Part VI (source 10's 42 delivered labels with the
prefix, its ten questions, and thirteen for the added numbered theorems,
convention, remarks and sections), 74 `hset:kw:` labels in Part VII (source
11's 52 delivered labels, its twelve questions, and ten added), and
`hset:q:axiomatics` on the existing Question 21.7. Batch 90 added 76, all
`hset:ns:` labels in Part VIII: source 12's 51 delivered labels with the
prefix, its twelve questions, and thirteen for the added part, sections,
convention, remarks and subsections. Batch 95 added 151, all `hset:sf:` labels in
Part IX: its part, sections, results, equations, conventions, remarks and twenty
questions, labelled at the write (a result proved by both sources carries one
label, so the delivered labels, 59 and 54, are not kept one to one); the dated
notes of batches 93 and 95 in earlier parts add none. The later review adds
two `hset:sf:` correction remarks, for effectivity and delivered label counts. No earlier label was
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

## A ninth part (batch 95)

| Source | Batch-95 manuscript | Archive (arrival `ec91f8c7c`) | Pin | Placement | Printed as |
|---|---|---|---|---|---|
| **13** (base) | 01, *Surreal and Omnific Foundations: Bi-Interpretations with Set Theory and the Boundary at Classes* ("Research study prepared for Vladimir Reshetnikov", 4 October 2026) | `surreal_omnific_foundations.zip` (566,548 bytes) | `722337445` | `350b9a954` | Part IX, Sections 67–80, the spine; labels `hset:sf:`; prefix `13-omnific-foundations-` reserved, no file shipped |
| **14** | 02, *Surreal-Only Foundations and the Set–Class Boundary: Explicit axiomatizations, omnific quotient birthdays, bi-interpretations, and the obstruction at NBG* ("Prepared for Vladimir Reshetnikov", "developed with ChatGPT", 4 October 2026) | `Surreal_Only_Foundations_and_NBG.zip` (381,702 bytes) | `bd1de458b` (search excerpts at `fb2287290`) | `350b9a954` | Part IX, inserted by subject and marked "(source 14)"; files `14-surreal-only-nbg-` |

Both archives were staged into the shared index while the batch-94A placement
`ec91f8c7c` was being committed, so that commit added them although its message
does not mention them. All three pins are ancestors of the placement, and at each
this report's `article.tex` was the one of Parts I–VIII. The two manuscripts answer
one assignment independently (shared 8-grams under 0.6 %, almost all
bibliography). Not shipped (they survive in `ec91f8c7c`): source 13's manuscript
(`surreal_omnific_foundations.tex`, 2,765 lines, 59 labels, 12 questions; a 34-page
PDF) and `README.txt`; source 14's manuscript (`article.tex`, 1,836 lines, 54
labels, 11 questions; a 27-page PDF), `README.md` and `SHA256SUMS` (8 of 8 entries
verified at placement). Section 80 holds the non-claims and provenance.

**Why here.** Both re-derive Theorem 18.1 (`hset:thm:chy`), whose status note
says its proof "is not an audit" of the Chen–Hamkins–Yang axiomatization, and give
it a theory-level form; both bear on Question 21.7 (`hset:q:axiomatics`) and on
Question 21.2 ("Minimal signature"). The alternatives considered at placement were
a part of definable-surreals-and-omnific-integers (whose Part III uses a different
signature, without a map back), the foundations report, or a new report.

**How the merge reads.** Source 13 is the base because its omnific theory uses the
weaker language `{0,1,+,−,·,<,≺_b}`, where source 14 needs the quotient birthday
`h(a,b) = b(a/b)`. Printed once, credited to both (Section 67 and the result
headings name the duplicates): the graph interpretation (Theorem 71.1 = 14's
Theorem 71.3), the round trip (Theorem 72.2 = Proposition 72.4), the round-trip
axiom recipe (Theorem 73.1 = Lemma 73.2), the theories (Theorem 73.4 and Theorem
73.6), fractions (Proposition 74.3), the `RCF` obstruction (Proposition 74.10), the
NBG obstruction (Theorem 75.2, proved by 14's sharper reflection Lemma 75.1, with
13's proof as second proof), the diagonal (Theorem 75.7) and the class lift
(Theorem 76.5 = Theorem 76.6, with 14's arbitrary-class round trip). Only in 13:
native omnific bit storage (Theorem 70.2), the tuple codec, definability transfer
(Corollary 74.1), fraction birthdays from `≺_b` (Corollary 74.4), the automorphism
obstruction for the pure ring (Proposition 74.12, Corollary 74.13), the GBC model
with countably many sets and ℵ₁ classes and its no-go (Lemma 75.5, Theorem 75.6),
the KM diagonal (Proposition 75.9). Only in 14: the quotient-birthday route and
`OA_qb` (Section 74.3), finite-axiomatizability transfer (Lemma 75.4), packing
(Lemma 76.1), inclusion preservation of class realizations, birthday-bounded ⇔ set
(Theorem 77.1), cuts and branches, the inaccessible example, and the only
program.

**Added in this merge, with proofs.** Proposition 74.5: the quotient birthday is
definable from unary birthday on `Oz` (from 13's Corollary 74.4), which answers
14's main open question, Question 79.6, positively. Proposition 74.2: a structure
on `No` or `Oz` with set-definable primitives is bi-interpretable with `V` by a
comparison sending each number to codes of itself exactly when it defines `≺_b` and
the ring operations. Proposition 74.14: 13's prose argument that the pure omnific
ring has no bi-interpretation with `V` on the canonical numbers, made a numbered
proposition with its three steps written out. Lemma 73.8 and Corollary 76.7: the
`GBc`, KM and `ETR` class lifts that both sources sketched. Remark 74.8: 14's
O1–O4 is an instance of the recipe, not an alternative to it. The Hamkins–Yao
attribution (13's "Section 4") was checked against arXiv v2 and is correct.

**Renamed in Part IX** (Convention 67.2, each with the tempting false reading). 13's
birthday precedence `≺` is `≺_b` (this report's `≺` is elementary substructure);
14's birthday `𝔟` is `b` and its structure `𝒮` is `B`; 13's domain `D` is `𝐃`;
13's interpretations `I_D`, `K_D` are `𝓘_𝐃`, `𝓙_𝐃`; 13's comparison `C_D` is
`Cmp_𝐃`, its predicate `B(a,b,c,d)` is `FB` (not `B`, `B_λ`, dsn's pairing `B(a,b)`
or Part VIII's `B(q)`), its unary code class `C` and 14's packed codes `D` are `UC`,
its block interval `I_β` is `W_β`, its map code `H_h` is `Y_h` (not `H_κ`), its base
`K` is `ν_cd`, its shear `θ`, coefficient `c_δ` and ordinal `Ω` are `ϑ`, `co_δ`,
`o_δ` (not the conjugation `c` or dsn's omega map `Ω`); 14's pairing `π` is source
06's `ϖ`, its bound `Λ(δ) = (δ+δ)² + δ + 1` is `Λ_14` (not `Λ(θ) = θ² + θ`), its
ordinal code `O(α)` is `c^ord_α` (not `OC`), its `Coll(c,a)` is `col(c) = a` (not
the collector `Coll(C)`), its `Code`, `∼_*`, `ε_*` are `Valid`, `Eq`, `Mem`. Class
theories follow the foundations report (Convention 68.1): `GB` no choice, `GBc`
set Choice, `GBC` Global Choice; 13's "GB" is `GB`, 14's "GB" (printed GBc) is
`GBc`.

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
13. **Part IX: surreal-only foundations (sources 13 and 14).** In `B` and natively
    in `(Oz; 0,1,+,−,·,<,≺_b)`: ordinals, birthdays, prefixes and signs are
    definable (Lemmas 69.1–69.3; the `Oz` case uses initiality); every subset of an
    ordinal α is stored in one omnific integer of birthday `ωα+ω`, one ω-block per
    bit, gaps filled with minus (Theorem 70.2); pointed well-founded extensional
    graph codes interpret `(V,∈)` (Theorem 71.1; over ZF the range is `HWO`,
    Proposition 71.5), and a signwise comparison recovers every original number
    (Theorem 72.2), so both structures are parameter-free bi-interpretable with
    `V` (Corollary 72.3). A general recipe (Theorem 73.1) gives recursively
    axiomatized theories `T_No`, `T_Oz` (13) and `SA_rt` (14), each
    bi-interpretable with ZFC, not finitely axiomatizable (Theorems 73.4, 73.6);
    every set-theoretic relation on `No` or `Oz` is `≺_b`-definable, formula by
    formula (Corollary 74.1), in particular the fraction-birthday predicate
    (Corollary 74.4) and hence 14's quotient birthday (Proposition 74.5); 14's
    `OA_qb` in `{0,1,+,−,·,<,h}` is bi-interpretable with ZFC (Theorems 74.6,
    74.7). The pure field interprets no Robinson arithmetic (Proposition 74.10);
    the pure ordered ring `Oz` defines neither ordinals nor `≺_b`, even with
    parameters (Corollary 74.13), and has no bi-interpretation with `V` on the
    canonical numbers (Proposition 74.14). Assuming `Con(ZFC)`, no theory uniformly
    interpretable in ZFC interprets NBG (Theorem 75.2, Corollary 75.3); assuming
    `Con(GBC)`, no uniform bi-interpretation of GBC has a forward domain coded by
    finitely many original sets (Theorem 75.6, via a GBC model with countably many
    sets and ℵ₁ classes, Lemma 75.5); no elementary evaluator codes every class in
    GB, and no formula does in KM (Theorem 75.7, Proposition 75.9). Retaining
    classes of numbers, a two-sorted lift is bi-interpretable with GBC (Theorem
    76.5), with `GBc`, with KM and with `GBC + ETR` (Corollary 76.7), and preserves
    inclusion of class realizations; in GB a class of surreals is a set iff
    birthday-bounded (Theorem 77.1). For `𝐃 = No` the structural theorems are
    Theorem 18.1 again (Remark 67.3).

## What the report does not claim

Section 20.6 lists every non-claim of sources 02–09, and Subsections 39.4,
53.3, 66.4 and 80.6 those of sources 10, 11, 12, 13 and 14; none was dropped.

- **Part IX.** Sources 13 and 14 are unrefereed, AI-assisted (14 with ChatGPT),
  not Lean- or Rocq-checked, and claim no priority; the global theorem is
  Chen–Hamkins–Yang's, and neither source verifies their intrinsic axioms, so
  `T_No`, `T_Oz`, `SA_rt`, `OA_qb` are round-trip axiomatizations built from the
  interpretation, not the announced theory, and are not complete, categorical or
  finitely axiomatized. `HWO` is the limit of this decoder only; definability
  transfer is per formula, with no truth predicate; the pure-`Oz` result excludes
  only the canonical number side, not every interpretation of set theory; rigidity
  is for the actual universe; the NBG obstruction needs "uniformly interpretable
  in ZFC" and excludes neither external relabelling, added predicates nor a
  larger universe; the reflection argument is classical (Hamkins–Yao, Section 4);
  the class lift keeps a class sort; GB without set Choice is open; the shear
  automorphisms answer none of Kaplan–Krapp–Serra's Questions 5.4, 5.6, 5.7; the
  inaccessible example is not a same-universe solution or a consistency proof;
  nothing independent of ZFC is decided. Every native `Oz` result, and
  Proposition 74.5, depend on the omnific sign criterion and initiality, imported
  from Ehrlich–Kaplan (arXiv v1, §2.2) and Gonshor (Theorem 8.1) and not re-proved;
  Section 79.4 lists this and the other imported inputs (Hahn lifting after
  Kaplan–Krapp–Serra, Williams's class-forcing and finite-axiomatizability facts,
  Lévy reflection, Gödel, Jeřábek, the `(V_κ, P(V_κ))` model). No claim of either
  source was found wrong. Source 14's finite checks validate finite encodings only.

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

Since batch 93 (dated notes of 4 October 2026, applied with batch 95), Part II of
naming-elementary-embeddings bears on Part VIII's questions: it answers Question
65.2 ("actions of arbitrary pure groups at uncountable κ") for countable groups and
full Replacement (its Proposition 19.2, Theorem 18.2), answers that report's
Question 10.4 that meets Question 65.4 (its Theorem 15.3) and gives the prescribed
finitely generated group case (graded hierarchy still open), answers Question 65.8
in part (its Proposition 19.4, Theorem 19.3, Corollary 19.5), and asks Questions
65.1, 65.6 and 65.12 again for its own actions (its Questions 23.9, 23.10, 23.12);
all twelve stay open. Since batch 96 (dated notes of 4 October 2026), Part III
of that report bears on Questions 65.1, 65.2, 65.6, 65.7 and 65.12: it
answers Question 65.2 further in part (a centralizer-orbit formula at the level
λ = κ > ω for finitely many named injections, its Corollary 27.2), gives a
two-involution example outside the finite-orbit scope of Question 65.7, and
asks Questions 65.1, 65.6 and 65.12 again (its Questions 37.6, 37.8, 37.12);
all twelve still stay open.

Since batch 95, Part IX adds Questions 79.1–79.20 (`hset:sf:q:`), merging the
twelve of source 13 and the eleven of source 14 (intrinsic axioms, pure `Oz`,
selection of codes, native class axioms and proof cost were asked by both).
Answered inside the report: 14's Question 79.6 (is the quotient birthday
definable from unary birthday on `Oz`?) positively, by 13's Corollary 74.4
through Proposition 74.5, with a long definition (a short one is Question 79.5);
the set-recovery part of 14's Question 79.9 ("Removing Choice") by Theorem 13.2
(`hset:thm:choice`), already at its pin. Answered in part: Question 79.4 (pure
`Oz`) by Proposition 74.14 and the collection's arithmetic results (Remark 74.11).
Re-scoped: Question 79.3 (reducts) by Proposition 74.2, which reduces the
bi-interpretation form to a definability question. Under the standing rule,
Section 79.4 lists the inputs imported without proof, and Question 79.13 is GB
without set Choice. Dated notes record the bearing of Part IX on Question 21.2
("Minimal signature", whose one-way form is not answered), on Question 21.7
(`hset:q:axiomatics`, whose comparison with `Et` and `Pack` stays open, the theories
of Part IX not being the finalized formulations it asks about) and on the status
note after Theorem 18.1, which stands.

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

Part II of naming-elementary-embeddings (batch 93, labels `nee:ca:`, pinned to
`a9ab9a698`, written later and independently) extends Part VIII's finite-cutoff
group-action results to every kernel bound for countable groups (its Theorem
18.2: for a finitely generated group named by generators every action keeps
Replacement iff `cf κ > τ(G)`, the number of conjugacy classes of subgroups;
Proposition 19.2 with a uniform evaluator), answers that report's Question 10.4
(commuting permutations, Theorem 15.3), and gives a two-point-orbit witness of the
separate-names/uniform-evaluator separation (Theorem 19.3). At κ = ω several of
its results are results of Part VIII, which is prior in the repository: dated
notes after Remark 54.4, Corollary 58.2 and Theorem 62.3, and after Questions
65.1, 65.2, 65.4, 65.6, 65.8 and 65.12, record each correspondence.

Part III of naming-elementary-embeddings (batch 96, labels `nee:aa:` and
`nee:ci:`, two manuscripts merged, pinned to `715a716a3`, written later and
independently) classifies the connected types of finitely generated
commutative monoids acting by injections (finitely many, `ℵ0` or `2^ℵ0`,
according as the group completion `G` is finite, infinite with `d ≤ 1`, or has
`d ≥ 2`, where `d` is the rank of `G/U`; its Theorem 30.4) and the resulting
Replacement thresholds, and generalizes Lemma
56.3 to injections and infinite components (its Lemma 26.3) for an exact
pure-real definable kernel at every cutoff (its Theorem 27.1). Dated notes
(4 October 2026) after Lemma 56.3 and after Questions 65.1, 65.2, 65.6, 65.7
and 65.12 record what it bears on; it answers none of Part VIII's questions in
full.

**[definable-surreals-and-omnific-integers](../definable-surreals-and-omnific-integers/)**
(Part III, batch 93, labels `dsn:op:`, its source 06): it interprets `(V,∈)`
parameter-free in `(No; +, ·, <, Oz, Ω)`, a signature without birthday, by the same
three validity clauses as Part IX but with supports of unit-coefficient series as
vertex sets (its Theorem 37.1, `dsn:op:thm:V-interpretation`), proves
`M ≡ N ⟺ 𝔖_Ω^M ≡ 𝔖_Ω^N` and a nested clause (its Theorem 40.4,
`dsn:op:thm:theory-faithful`), and asks for the missing comparison map (its Question
42.1, `dsn:op:q:biinterpretation`). A dated note after Theorem 16.5 (batch 93)
records this. Part IX is the birthday-enriched comparison target that question
names; it does not answer it, but its Proposition 74.2 shows that the specific form
asked there is equivalent to the definability of `≺_b` in that signature (Remark
67.5). Part IX also credits that report's ambient codes and hulls
(`dsn:thm:bounded-code`, `dsn:thm:hull`) and its `dsn:op:prop:native-omnific`
(the pure ring `Oz` is bi-interpretable with `(No, Oz)`).

**[omnific-preserving-automorphisms](../../surreal/omnific-preserving-automorphisms/)**
and **[omnific-diophantine-geometry](../../surreal/omnific-diophantine-geometry/)**:
Part IX's shear automorphism (Proposition 74.12) is a weaker consequence of
`opa:thm:parameters` and `opa:sc:thm:undef`, credited; its fraction fact
(Proposition 74.3) is `odg:thm:fractions`, and `odg:def:cor:arithmetic`,
`odg:def:thm:realrecovery` show that the pure ring `Oz` has arithmetic strength
(Remark 74.11). The [foundations](../foundations/) report's GB convention
(`found:sub:gbconvention`) is Part IX's, its `found:rem:conservativity` is
Part IX's conservativity paragraph, and its `found:prop:allcuts` is the failure in
Corollary 77.2.

**[definable-surreals-and-omnific-integers](../definable-surreals-and-omnific-integers/)**
(Part I): source 11's double-monomial independence (Theorem 43.1) is the case `K = R`,
`G = {0}` of its Lemma 8.1 (`dsn:lem:cosets`, "Disjoint support cosets");
Remark 40.4 records this. New beside it are the omnific-integer conclusion,
the free-algebra calibration and the ZF framing.

**[cantor-families-of-surreal-subfields](../cantor-families-of-surreal-subfields/)**
(batch 90, `csf:`): its Lemma 3.2 (`csf:lem:independence`) is the analogue of
Theorem 43.1 with exponents `b ω^q`, `q ∈ Q`, `b ∈ {1, √2, √3, √5, …}`, over
the real algebraic numbers, by the same leading-term argument, and is also a
case of `dsn:lem:cosets`; that report works in ZFC and uses the family as a
transcendence basis of a countable real closed field, not for free-algebra
universality. **[polish-models-of-omnific-arithmetic](../polish-models-of-omnific-arithmetic/)**
(batch 90): its Part XII (source 18), in a class theory with Foundation
omitted and without Global Choice, uses the birthday stages as an ordinal
exhaustion to prove that connected real class manifolds coded into or from
`No^m` are sets (`pma:gcm:thm:surreal`), and bounds the birthdays of their
points by the Replacement step that opens the proof of Theorem 42.1
(`pma:gcm:cor:birthdaybound`); no uniform cutoff is claimed and no theorem is
shared. One dated note after Remark 40.4 records both.

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

Part IX: only its fraction-field fact (Proposition 74.3) is formalized, as
`omnific_monomial_clearing`, `surreal_eq_omnific_fraction` and
`omnificSurrealIsFractionRing` in
`Algebra/SurrealNumbers/Surreal/Foundations/OmnificSupportBounds.lean` (namespace
`Surreal.Foundations.SignSequence`), mapped as proved in the formalization ledger;
source 13 names them correctly and reports no fresh build, and none was made here.
The finite PA/HF analogy both sources discuss is formalized in
`Logic/Interpretability/PAHF/` (deductive bi-interpretation of PA with a
finite-generation HF theory; `AckermannHFCore.lean`). Nothing else of Part IX is
formalized; sources 13 and 14 propose staged developments (Section 78), none of
which exists.

## Review corrections, 4 October 2026

Lemma 73.8 now states the effective-source, enumerable-extension and computable-
translation hypotheses needed for an effective axiom presentation. Remark 73.9
retains the former unrestricted claim and the identity interpretation of true
arithmetic as a counterexample. Remark 80.1 retains the former delivered-label
counts 76/70 and records the correct literal counts 59/54. These corrections
add two labels; the publication's original 151 new labels remain intact.

Fresh review validation used three direct installed `pdflatex` passes with
`-no-shell-escape`, all successful. The rebuilt PDF still has 212 pages; its
final log has no warnings, undefined references/citations or bad boxes. A fresh
literal census gives 525 distinct labels, 1,100 resolved reference occurrences,
129 resolved citation-key occurrences and 41 bibliography keys. The correction
pages (physical pages 171 and 206, printed pages 166 and 201) were visually
inspected. No supplied program or builder was executed in this review. The
historical execution records below remain separate from this fresh validation.

## What was run

- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX):
  212 pages (unchanged by the batch-96 reciprocal notes in Part VIII, which
  changed no label or citation number in the `.aux` comparison with a build
  of the committed text; 143 before the batch-95 Part IX and the batch-93 reciprocal notes
  in Part VIII and after Theorem 16.5; the title page was set
  `\enlargethispage` and two title-page spaces were shortened to keep its
  provenance line on the page; 143 was
  unchanged by the batch-90 reciprocal note after Remark 40.4,
  which changed no label number; 116 before the batch-90 Part VIII;
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
- Source 14 (batch 95), with Python 3.14.4, on a copy outside the repository:
  passed in about two seconds and reproduced
  `data/14-surreal-only-nbg-verification.json` exactly apart from line endings
  (16,129 prefix pairs, 642 sign bits, 6,400 finite and 4,096 Cantor-normal-form
  ordinal pairs, 75 increasing DAG candidates, 207 valid rooted graphs, 42,849
  equality and 42,849 membership comparisons, 961 packing round trips, 511 dyadic
  sign-birthday and 1,225 fraction-invariance checks, 66,066 diagonal matrices).
  Source 13 ships no program.
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

**Source 14 (batch 95): run its program on a copy, never in this directory.**
`code/14-surreal-only-nbg-verify_finite.py` takes no arguments and writes
`verification.json` next to itself (its docstring says "Output: verification.json
next to this script" and calls itself checks "for article.tex", meaning source 14's
manuscript, now Part IX). For example:

```
mkdir -p /tmp/s14
cp code/14-surreal-only-nbg-verify_finite.py /tmp/s14/
python /tmp/s14/14-surreal-only-nbg-verify_finite.py
#   compare /tmp/s14/verification.json with data/14-surreal-only-nbg-verification.json
```

Use normal Python, not `python -O` (the checks are assertions). On Windows the
regenerated file has CRLF line endings; `diff --strip-trailing-cr` ignores that.
`code/14-surreal-only-nbg-build.sh` is source 14's delivered build script, kept
byte-identical: it changes to its own directory and runs `python3 verify_finite.py`
and three `pdflatex` passes of `article.tex`, then greps `article.log`, all delivery
names; in the shipped layout it would find no `verify_finite.py` and would build
this report, not source 14's manuscript; do not run it here. To rerun it as
delivered, re-extract the archive on a POSIX host:
`git show ec91f8c7c:docs/incoming/Surreal_Only_Foundations_and_NBG.zip > /tmp/s14.zip`.
`data/14-surreal-only-nbg-build_validation.json` is source 14's record of its own
27-page build (pdfTeX 1.40.26, Python 3.13.5), with SHA-256 hashes of its unshipped
`article.pdf` and `article.tex`; it does not describe this report.
`14-surreal-only-nbg-SOURCES_AND_STATUS.md` says that "a proof and provenance
ledger appears in Appendix B" and that "full bibliographic entries ... appear in the
PDF": both mean source 14's manuscript, whose ledger and bibliography are printed in
Section 80.4 and in this report's bibliography. Source 13's manuscript is
`git show ec91f8c7c:docs/incoming/surreal_omnific_foundations.zip`; it ships no
program.

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

Sources 13 and 14 inspected the repository read-only and modified nothing.
Source 13 inspected `722337445` (this report, the foundations, definable-surreals
and omnific-preserving-automorphisms reports, the formalization ledger and the Logic
README) and records its targeted audit in Section 80.5; every statement in it is
true at the pin and at the placement (dated note there). Source 14 fetched this
report's README at `bd1de458b` and saw search excerpts of
`02-birthday-cutoffs-SOURCE_AUDIT.md` and the definable-surreals article at
`fb2287290`, as its `14-surreal-only-nbg-SOURCES_AND_STATUS.md` records; its
statements (CHY credited, no Lean mapping for `hset:` labels) are true. Neither
built or audited the whole report. The Hilbert's-tenth programme authenticated both
archives at their arrival in `196e11d19`
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_foundations_f300069cf.md`;
its "archive 1" is source 14, "archive 2" source 13): bounded reads, nothing run, no
correction found; source 13's prefix and block arguments check out conditional on
the imported omnific sign facts; it flagged the cross-source answer to 14's unary
question as a lead (Proposition 74.5 now proves it) and found no arithmetic
compiler or operation-count saving (Remark 67.7).
