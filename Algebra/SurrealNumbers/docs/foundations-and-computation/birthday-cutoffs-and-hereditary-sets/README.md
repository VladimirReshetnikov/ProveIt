# Birthday Cutoffs and Hereditary Sets

**The set-theoretic content of bounded surreal arithmetic: bi-interpretations, elementary inclusions, axiom spectra, outer models, and surcomplex orientation**
Merged research report, 22 September 2026, from five manuscripts written
independently on the same day, all pinned to repository commit
`4f2645599121fa872c7104995e47f86f0382351f` and placed by commit `d4e71b7`.
Prepared for Vladimir Reshetnikov.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 61 pages
README.md        this guide
02-birthday-cutoffs-SOURCE_AUDIT.md        source 02's source and novelty audit, as delivered
code/            02-birthday-cutoffs-verify_finite.py            (source 02)
                 05-birthdays-recover-sets-check_finite_models.py (source 05)
                 05-birthdays-recover-sets-build.sh              (source 05, see "Build")
                 06-hereditary-size-orientation-finite_checks.py (source 06)
                 07-birthday-expansion-finite_checks.py          (source 07)
                 09-bounded-arithmetic-finite_checks.py          (source 09)
                 09-bounded-arithmetic-Makefile                  (source 09, see "Build")
data/            02-birthday-cutoffs-verification.json, -verification_summary.tex, -build.json
                 05-birthdays-recover-sets-finite_checks.json, -repository_audit.json
                 06-hereditary-size-orientation-finite_checks.txt
                 07-birthday-expansion-finite_checks_output.json
                 09-bounded-arithmetic-verification_report.json, -build_report.json
```

Every label in `article.tex` carries the prefix `hset:` (155 labels). All 69
labels of the delivered base text (source 09) survive with that prefix; three of
them (`hset:prop:powerset`, `hset:sec:extensions`, `hset:app:verification`) now
sit, as second labels, on the unit into which that material was merged. No
`hset:` label has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md).

## Five sources, one report

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

## What the report does not claim

Section 20.6 lists every non-claim of every source; none was dropped.

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
- No choice-free version of the cutoff theorems; nonstandard models are handled
  internally only; cutoffs that are not epsilon numbers are not classified (ring
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
elementarity (Remarks 12.4, 15.8).

**[gonshor-product-birthdays](../../surreal/gonshor-product-birthdays/)**: see
above; no argument here depends on it.

**[computable-surreals](../computable-surreals/)** is a different program
(countable effective subfields); the undecidability remarks here are standard.

[single-dilation-hahn-support](../../surcomplex/single-dilation-hahn-support/)
obtains the same kind of arithmetic interpretation and undecidability, and a
TP₂ witness, for a Hahn field expanded by one exponent dilation
(`dsup:thm:undecidable`, `dsup:thm:tp2`); neither result implies the other.

## What was run

- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX):
  61 pages; no errors, undefined references or citations, multiply defined
  labels, duplicate destinations, LaTeX or package warnings, or overfull or
  underfull boxes. Cross-references are typed (lemma, proposition, ...) through
  alias counters.
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
```

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
