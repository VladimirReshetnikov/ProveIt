# Self-Embeddings of the Surreal Numbers

**Rigidity, Hahn lifts, topology, and size-safe foundations — with order and simplicity, algebra, analysis, exponential and model-theoretic structure, large cardinals, and omega-series**

This is a merged research report built from six independent manuscripts,
all titled *Self-Embeddings of the Surreal Numbers*, all dated
3 October 2026 and all answering one research prompt (batch 84 of the
collection's intake). Manuscript 03 is the base; manuscripts 02, 04, 05, 06
and 07 are printed as Parts II–VI. Manuscript 01 of the same batch is an
earlier edition of 05 and is not a source (see *Provenance*). Author lines
as delivered: "Prepared for Vladimir Reshetnikov" (02, 03, 05, 07), "A study
of the ProveIt development" (06), and "Research article prepared with
ChatGPT" (04, on its title page and in its PDF metadata; the only one of the
seven to name the tool).

| Source | Batch-84 manuscript | Archive (main file, delivered PDF) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 03 (base) | 03 | `Surreal_Self_Embeddings (2).zip` (`article.tex`, 33 pp) | `b0d4af4f3` | `e1395c66c` | Part I: Sections 2–16 (its Section *n* is Section *n* + 1 here) and Appendices A, B |
| 02 | 02 | `surreal_self_embeddings (1).zip` (`surreal_self_embeddings.tex`, 36 pp) | `af04de3fa` | `e1395c66c` | Part II, Sections 17–29 |
| 04 | 04 | `Surreal_Self_Embeddings_Atlas.zip` (`surreal_self_embeddings.tex`, 35 pp) | `a006a77a0` | `e1395c66c` | Part III, Sections 30–41 |
| 05 | 05 | `surreal_self_embeddings_comprehensive.zip` (`article.tex`, 39 pp) | `51b0a69d7` | `e1395c66c` | Part IV, Sections 42–53 |
| 06 | 06 | `surreal_self_embeddings (3).zip` (`surreal_self_embeddings.tex`, 47 pp) | `79049d58c` | `e1395c66c` | Part V, Sections 54–63 |
| 07 | 07 | `surreal_self_embeddings (4).zip` (`surreal_self_embeddings.tex`, 42 pp) | `b0d4af4f3` | `e1395c66c` | Part VI, Sections 64–76 |

All seven archives arrived in `06395052a`. The placement commit `e1395c66c`
removed them from `docs/incoming`; each can be recovered with
`git show 06395052a:"docs/incoming/<archive>.zip" > <scratch>/<archive>.zip`.
The same placement commit was preceded by `f06e67d10`, which corrected a
false sentence of
[omnific-preserving-automorphisms](../omnific-preserving-automorphisms/README.md)
(its Section 27.2: "the ordinary Taylor section alone is not a map on
arbitrary normal forms") after source 07's Section 12.1 showed it false as
stated; source 07's correction is printed in Part VI with that note.

**Status.** AI-assisted, unrefereed. **Not formalized**: no statement of
this report is proved in Lean as part of it, and its place beside the Lean
development confers no formal status (see *Relation to the Lean
development*). Independent proof review is pending.

## Files

```
article.tex                                     the merged report, standalone LaTeX (pdfLaTeX), internal bibliography
article.pdf                                     the compiled report, 167 pages (unnumbered title page, then pages 1-166)
README.md                                       this guide
02-paradox-free-PROOF_STATUS.md                 source 02's proof and verification status, as delivered
03-hahn-lifts-SOURCE_AUDIT.md                   source 03's source audit, as delivered
04-atlas-SOURCE_AUDIT.md                        source 04's source audit (declarations and blob ids it read), as delivered
05-comprehensive-SOURCE_AND_PROOF_AUDIT.md      source 05's source and proof audit, as delivered
code/02-paradox-free-build.sh                   source 02's build script (runs its checks, then its PDF)
code/02-paradox-free-validate.py                source 02's exact finite checks (Python standard library)
code/03-hahn-lifts-build.sh                     source 03's LaTeX build script
code/03-hahn-lifts-verify.py                    source 03's exact finite checks (Python standard library)
code/04-atlas-build.sh                          source 04's LaTeX build script (three pdflatex passes)
code/04-atlas-finite_checks.py                  source 04's exact finite checks (prints JSON to stdout, writes nothing)
code/05-comprehensive-build.sh                  source 05's build script (runs its checks, then its PDF)
code/05-comprehensive-verification.py           source 05's exact finite checks (option --output)
data/02-paradox-free-build_validation.json      source 02's build record (pages, check count, SHA-256 of its .tex, .pdf, validate.py)
data/02-paradox-free-validation_results.json    source 02's recorded run: 198,220 assertions, seed 20261003
data/03-hahn-lifts-verification.json            source 03's recorded run: 195,579 checks
data/04-atlas-finite_check_results.json         source 04's recorded run: 22,169 checks (Python 3.13.5)
data/05-comprehensive-BUILD_AUDIT.json          source 05's build and PDF-inspection record
data/05-comprehensive-verification.json         source 05's recorded run: 146,914 assertions, seed 20261003
```

These are the 20 files staged by the placement commit (with `article.tex`
and `README.md` rewritten) plus `article.pdf`. Every file under `code/` and
`data/` and the four audit files are byte-identical to the delivery.
Sources 06 and 07 delivered no code or data.

### Delivery names and files not shipped

| Shipped | Delivered as |
|---|---|
| `article.tex` | source 03's `article.tex`, rewritten as the merged report |
| `README.md` | this guide; replaces the delivered READMEs of all six sources |
| `02-paradox-free-PROOF_STATUS.md` | `PROOF_STATUS.md` (02) |
| `03-hahn-lifts-SOURCE_AUDIT.md`, `04-atlas-SOURCE_AUDIT.md` | `SOURCE_AUDIT.md` (03, 04) |
| `05-comprehensive-SOURCE_AND_PROOF_AUDIT.md` | `SOURCE_AND_PROOF_AUDIT.md` (05) |
| `code/02-paradox-free-validate.py`, `data/02-paradox-free-validation_results.json`, `data/02-paradox-free-build_validation.json`, `code/02-paradox-free-build.sh` | `validate.py`, `validation_results.json`, `build_validation.json`, `build.sh` (02) |
| `code/03-hahn-lifts-verify.py`, `data/03-hahn-lifts-verification.json`, `code/03-hahn-lifts-build.sh` | `verify.py`, `verification.json`, `build.sh` (03) |
| `code/04-atlas-finite_checks.py`, `data/04-atlas-finite_check_results.json`, `code/04-atlas-build.sh` | `finite_checks.py`, `finite_check_results.json`, `build.sh` (04) |
| `code/05-comprehensive-verification.py`, `data/05-comprehensive-verification.json`, `data/05-comprehensive-BUILD_AUDIT.json`, `code/05-comprehensive-build.sh` | `verification.py`, `verification.json`, `BUILD_AUDIT.json`, `build.sh` (05) |

Not shipped (all recoverable from `06395052a`): every delivered PDF; the
manuscripts and READMEs of 02, 04, 05, 06 and 07 (their text is in Parts
II–VI) and README.txt files of 06 and 07; the checksum manifests of 03, 04,
05 and 06 (`SHA256SUMS.txt`; all entries verified at placement; 02 and 07
shipped none); source 03's `verification.txt`, a byte copy of its
`verification.json`; and all of manuscript 01.

Shipped files whose text still uses delivery names: the four build scripts
`cd` into their own directory (`code/`) and call the delivered names
(`validate.py`, `verify.py`, `verification.py`, `article.tex`,
`surreal_self_embeddings.tex`), none of which exists there, so **they do not
run as shipped**; the audits name `article.tex`, `README.md`,
`verification.py`, `SHA256SUMS.txt`, `verification.txt`; source 02's
`build_validation.json` hashes its delivered `.tex` and `.pdf`, which are not
shipped (its `validate.py` hash equals `code/02-paradox-free-validate.py`);
source 05's `BUILD_AUDIT.json` describes its delivered 39-page PDF, and
source 04's `SOURCE_AUDIT.md` reports that `FORMALIZATION.md` "returned an
empty content field", which was an artefact of its fetch (the ledger exists).

## Labels and numbering

Every label carries the prefix `sse:` (unused elsewhere in the collection and
the Lean tree before this report). Source 03's 96 labels are kept with the
prefix added and every reference updated. The write added 12 labels for the
Parts and the merged sections (`sse:part:*`, `sse:sec:merged`,
`sse:sec:sources`, `sse:sec:conventions`, `sse:sec:status`,
`sse:sec:nonclaims`, `sse:app:provenance`). The members use sub-prefixes:
`sse:pf:` (02, 68 labels), `sse:at:` (04, 62), `sse:co:` (05, 70), `sse:sr:`
(06, 92), `sse:an:` (07, 68); 468 labels in all. A member label is its
source's own label after the sub-prefix wherever the source had one.
cleveref type hints (`\label[proposition]{…}` and so on) are inserted for
every labelled environment on the shared theorem counter, so that references
name the right kind of statement.

Source 03's Section *n* is Section *n* + 1 here, and its numbered statements
keep their positions within their sections. Each member Part opens with a
*correspondence table* sending every numbered item of its source, in the
source's own numbering, to the place where it is printed. All 92 research
questions of the six sources are printed (18 + 15 + 14 + 16 + 11 + 18).
Text added when the report was written is marked **[write]**.

## Setting and notation

Surreals are sign sequences of set length; normal forms have set supports;
the cut property is never applied to proper-class sides. Proper-class maps
are read in GBC (global choice only for back-and-forth) or formula by
formula; set-sized cutoffs `No_{<κ}` are sets. Section 1.2 fixes one
notation for all six texts and lists every collision. The ones to watch:

- `A_f` (additive lift of an increasing `f`) is **not** a field embedding;
  `H_τ` (field lift of an additive `τ`), `J_f = H_{A_f}` (double lift),
  `H_{τ,χ}` (weighted). Sources 02 and 05 wrote `E_f` for the double lift,
  05 `H_φ`, 07 `F_τ`, 06 `T_h`, `H_g`, `J_{g,χ}`, 07 and the
  omnific-preserving report `J_{τ,ρ}`, `M_{1,ι_μ}`.
- `D_m` (sign repetition), `D(a) = σ(a) − a` (displacement) and the
  derivation `Δ` inside the Taylor shift `T` are distinct; `T_{>c}` is
  truncation; `S_c` is the exponent dilation (05's `T_q`, 07's `D_c`).
- `E(A)` is the two-level exponent footprint of a set, not the abstract
  exponential `E` of Section 11.
- `𝒥_j` is the map induced by an elementary `j : V → M` (02's `J_j`, the
  large-cardinal report's `J`), not a double lift.
- `Ω(x) = ω^x` is Conway's omega-map, not Gonshor's `exp`.

## What the report claims

Numbers are those of the built `article.pdf`.

### Part I (source 03, the base)

- Order and simplicity: interval compression, prefix maps, sign repetition
  `D_m` (proper, cofinal, discrete image, nowhere continuous); birthday
  rigidity (Theorem 4.5); canonical-cut rigidity (Proposition 4.7); closed
  sign images have a fixed-point substructure (Theorem 4.9, after
  Bagayoko–van der Hoeven); an order embedding with simplicity-initial image
  is onto, without assuming simplicity preservation (Theorem 5.2).
- Hahn lifts: additive lift `A_f`, field lift `H_τ`, faithful double lift
  `J_f` with image, composition, fixed-field and cofinality formulas
  (Theorems 6.1–6.3); weighted monomial classification (Theorem 6.4).
- Flexibility: `J_−` fixes every real and every ordinal (Theorem 7.1); for
  every set `A`, a proper cofinal strongly `R`-linear field embedding and a
  nonidentity automorphism fixing `A ∪ R ∪ On` (Theorem 7.4); bounded copies
  fixing `A ∪ R` and `ω` (Theorem 7.6).
- Fixed fields are real closed; fixed fields do not detect surjectivity;
  iterated-image cores (Proposition 8.4); set-sized subsets are closed and
  discrete; continuity iff cofinality for field embeddings; monomial images
  closed and nowhere dense; a dilation with derivative zero everywhere.
- Valuation: value action; a leading-term-fixing strong unit twist `U_β`
  fixing `R`, `On` and any set (Proposition 10.2); Taylor shift; ω-map and
  valuation rigidity.
- Exponential: displacement amplification, profile rigidity in any ordered
  exponential field, exponential valuation rigidity for embeddings,
  cofinal value displacement, and uniqueness of cofinal exponential
  embeddings with the same value action (Lemma 11.6, Theorem 11.7).
- Elementarity, o-minimal definability rigidity (Theorem 12.2), surcomplex
  extensions, necessary differential conditions, cutoff transfer,
  formalization layers, 18 questions, ledger and source audit.

### Part II (source 02)

Sign blocks `D_δ` of any ordinal length; tree embeddings fixing a set and
all ordinals; the converse "`A_f` multiplicative only if `f` additive";
`J_c` with exact fixed field `R((ω^R))` (source bound `ω^{ω²+1}`, sharpened in
a note to `ω^ω`); `Frac(Oz) = No` (credited); elementarity of ordered group
embeddings; a second proof of definability rigidity; `|No_{<κ}| = 2^{<κ}`;
the claim that `No_{<λ}` is a subfield exactly at epsilon numbers, with a
**[write]** proof of the converse (Remark 23.2 and the note after it; it
rests on Gonshor's sign expansion of `ω^y`, unrefereed); **conditional on
an amenable elementary `j : V → M` with critical point `κ`**: the induced
map `𝒥_j` (re-proving `lce:prop:J`), its first pointwise cut failure at `κ`
and the summation defect; the lexicographic word action and iterates; its
formalization plan, audit and 15 questions.

### Part III (source 04)

`J_c` with image `R((ω^{R((ω^{(−1,1)})}))` and bound `ω^ω`; an embedding
with fixed field exactly `R`; the core of every double lift; **under GBC
with elementary transfinite recursion and a class satisfaction relation**:
bounded and cofinal proper elementary self-embeddings of o-minimal
expansions, including the exponential field; abstract exponential value
displacement and cofinal pair rigidity for an ordered exponential field
`(F, E, w)` (Theorem 35.3 strengthens the surjectivity hypothesis of the
exponential-rigidity report's `cor:two-profiles` to cofinality); a criterion
for an exponent lift to commute with `exp`; rational dilations are not
differential; the converse for conjugation-commuting surcomplex
embeddings; a Lean integration plan (Stages A–E), an audit of ten invalid
arguments, its ledger and 14 questions.

### Part IV (source 05)

A description of every order-and-simplicity embedding by local padding data
(home of this result; 06 and 07 prove it too); least moved birthday; an
explicit bounded annulus `ω^{−1} < |j(x)| < ω`; uniform radius for set
discreteness; the embedding form of the derivative dichotomy and an
**exact criterion** for a weighted lift to have derivative zero; the
two-map lemma for `F → K` and the profile theorem without exponential
compatibility; rational dilations do not lift for embeddings; a continuous
automorphism that is not strong (GBC); diagonal derivations and their
commutants; **under its class-satisfaction framework**: small types,
omission, bounded elementary exponential copies with range below
`log^n ω`; its formalization architecture, ledger, audit and 16 questions.

### Part V (source 06)

A credited synthesis of the omnific-pair results of
`omnific-preserving-automorphisms` (automatic strongness, bottom-gap
classification, proper embeddings moving a real), the Diophantine and
large-cardinal reports; an automorphism fixing `R ∪ On` and moving
`ω^{ω^{1/2}}`, which is transcendental over `Q(R ∪ On)`; the exponential
defect cocycle `α_j` of a derivation-compatible embedding; additivity of the
translation parameter `c_j`; an exponential automorphism moving `ω` to any
infinite positive `a` (from KKS homogeneity); club localization of class
maps to birthday stages; `Fix(f) = ⋂ fⁿ(No)` (Bagayoko–van der Hoeven); a
Lean status table (claims re-checked at `e1395c66c`); 11 questions.

### Part VI (source 07)

Convex classes that are order-and-simplicity images (attribution to
Bagayoko–van der Hoeven unchecked); every increasing `h : On → On` is the
birthday map of a tree embedding; strong additivity versus truncation
compatibility for exact-monomial maps; continuity iff cofinality for
embeddings between arbitrary ordered fields; the omega-map clause for
derivation-compatible embeddings; **conditional on Berarducci–Mantova,
Bagayoko and Mantova (imported, not re-proved)**: the strong exponential
self-embeddings of the omega-series field are the substitutions `C_g`;
homogeneity, omission and the unavoidable points of a set as its relative
real closure (GBC); the correction concerning Taylor supports; two alleged
sign slips in KKS v3 Examples 4.3–4.4 (**not checked**); a staged
formalization program and 18 questions.

## What the report does not claim

- No priority: every source disclaims publication priority, and about half
  of each re-proves results already in the collection. Those are printed
  once with the existing labels credited (Section 1.3 and each Part), never
  as new. Sentences of the sources presenting them as their own
  developments (05's "developments assembled here", 04's "the proof here
  establishes the non-surjective extension") are corrected in [write] notes.
- No completeness: no classification of all field, exponential, omega-map or
  differential self-embeddings; the weighted classification covers one
  strong monomial sector; the double lift is a construction, not a
  classification; the uniqueness of bounded exponential embeddings with the
  same value action is open; KKS Questions 5.6–5.7 are not solved.
- Conditional results stay conditional: the elementary embeddings of Parts
  III and IV (GBC with elementary transfinite recursion, a class
  satisfaction relation, definable Skolem functions; sufficient, not shown
  minimal; the copies preserve no strong sums, monomials, simplicity, `Oz`
  or derivation), Part II's large-cardinal section, and Part VI's omega-series
  classification.
- Finite checks (sources 02–05) are regression tests on finite sign words
  and finite Hahn polynomials; they verify no class-sized statement.
- No new Lean code, Lean build or kernel check was made by any source.
- Each Part ends with its source's full list of status statements and
  non-claims.

## Relation to neighbouring reports

- [omnific-preserving-automorphisms](../omnific-preserving-automorphisms/README.md)
  (`opa:`): Part III of that report already has the inner and double lifts
  (`opa:as:lem:inner`, `opa:es:prop:lifts`), exact fixed supports
  (`opa:es:thm:fixedsupport`), parameter-fixed bounded and cofinal copies
  (`opa:as:thm:parameters`, with the same compression), closed images and the
  continuity dichotomy (`opa:as:thm:closed`, `opa:as:thm:topology`). New here:
  fixing all ordinals and the automorphism clause (Theorem 7.4). Source 05
  read only its README; 06 reprints its omnific-pair theorems with credit.
- [independent-surreal-copies](../independent-surreal-copies/README.md)
  (`isc:`): the field lift (`isc:thm:lift`) and the χ = 1 case of the weighted
  classification (`isc:prop:classification`).
- [surcomplex-field-automorphisms](../../surcomplex/surcomplex-field-automorphisms/README.md)
  (`saut:`): set discreteness, the derivative dichotomy and zero-derivative
  dilations, the monomial automorphisms, the Taylor coefficient flow,
  ordered homogeneity, exponential faithfulness, `Fix Aut(No) = Q^rc`
  (generalized by Part VI's unavoidable points). None of the six sources
  cited it.
- [exponential-automorphism-rigidity](../exponential-automorphism-rigidity/README.md)
  (bare labels): all six sources credit and re-prove `lem:amplify`,
  `cor:embedding`, `thm:no`, `thm:cofinal`. The cofinal two-map uniqueness
  (base Lemma 11.6, Theorem 11.7; Part III's abstract Theorem 35.3)
  strengthens its `cor:two-profiles`, which needs a surjective map.
- [large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/README.md)
  (`lce:`): Part II's `𝒥_j` re-proves `lce:prop:J`; its summation defect is
  `lce:thm:witness`, an instance of `lce:thm:defect`; the first pointwise cut
  failure is new at remark level.
- [omnific-diophantine-geometry](../omnific-diophantine-geometry/README.md):
  `Frac(Oz) = No` is its `odg:thm:fractions`.
- [discrete-initial-subgroups-and-omnific-normalization](../discrete-initial-subgroups-and-omnific-normalization/README.md):
  its `isg:cf:prop:coherence` gives the identity form of the initial-image
  theorem.
- [birthday-cutoffs-and-hereditary-sets](../../foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md)
  and [foundations](../../foundations-and-computation/foundations/README.md):
  epsilon-number cutoffs (`found:sub:cutoffs`), rigidity of cutoffs
  (`hset:lem:rigidity`), surcomplex lifts (`hset:thm:two-lifts`).
- [surreal-well-orders](../../foundations-and-computation/surreal-well-orders/README.md):
  universality of `No` as a target, a different question.

Reciprocal notes in those reports are not part of this write.

## Relation to the Lean development

Nothing in this report is formalized as part of it. The project
(`Algebra/SurrealNumbers/Surreal/`) formalizes these parts of the
surrounding mathematics, for automorphisms or for abstract fields only:

- The field lift for ordered additive **automorphisms** of the exponent
  group, on the actual surreal carrier:
  `Surreal.Foundations.SignSequence.exponentAutomorphism`
  (`Surreal/Foundations/NormalFormExponentAutomorphisms.lean:109`), built
  from `Surreal.Foundations.SmallNormalForm.mapExponents` and
  `exponentRingEquiv`; its order, strong sums and valuation:
  `exponentOrderAutomorphism`, `stronglySummable_exponentAutomorphism_iff`,
  `valuation_exponentAutomorphism`
  (`Surreal/Foundations/ExponentAutomorphismStrongSums.lean`); exponent
  dilations `exponentDilation`
  (`Surreal/Foundations/OmnificExponentAutomorphisms.lean:116`). These are
  the automorphism case of `H_τ` (Theorem 6.2) and of `S_c`. The generic
  Hahn-field version is `Surreal.ValueGroupLifts.hahnLift`
  (`Surreal/HahnSeries/ValueGroupLifts.lean:329`, `Γ ≃+o Γ`); embeddings of
  small groups into Hahn workspaces are `Surreal.HahnSeries.workspaceEmbedding`
  and `SignSequence.hahnEmbedding`. No proper self-embedding of `No`, no
  first lift of a non-additive map and no map preserving `IsPrefix` or
  `Simpler` is formalized.
- Generic exponential rigidity for a unital endomorphism of an ordered
  field with an ordered exponential and a convex valuation:
  `Surreal.ExponentialProfile.eq_id_of_abs_displacement_le`,
  `eq_id_of_commute`, `eq_id_of_profile`, `cofinal_value_displacement`
  (`Surreal/Algebra/ExponentialProfile.lean`). The two-map comparison is
  formalized only with one map an automorphism (`eq_of_profile_eq`, `τ : F ≃+* F`);
  the cofinal strengthening of this report is not. The instantiation with the
  actual surreal exponential is pending there.
- `Frac(Oz) = No`: `surreal_eq_omnific_fraction`,
  `omnificSurrealIsFractionRing`
  (`Surreal/Foundations/OmnificSupportBounds.lean`).
- The simplest-separator theorem used by the sign-tree arguments:
  `existsUnique_simplest_separator`
  (`Surreal/Foundations/SignSequenceSimplicity.lean:72`).

No `sse:` label has a row in the formalization ledger.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

run in a scratch copy of this directory (pdfLaTeX; MiKTeX was used). The
build has no errors, no undefined references or citations, no multiply
defined labels, no duplicate destinations and no overfull boxes. Packages:
newtx, amsmath/amsthm/mathtools/amssymb, geometry, microtype, booktabs,
longtable, enumitem, fancyhdr, tcolorbox, xurl, hyperref, cleveref.

## Rerunning the finite checks

Never run the programs in this directory: 02's and 03's write their records
next to themselves under the delivered names. Copy them to a scratch
directory and run there (Python 3.10+, standard library only):

```sh
mkdir -p /tmp/sse && cp code/*.py /tmp/sse/ && cd /tmp/sse
py 02-paradox-free-validate.py   # writes ./validation_results.json; compare with data/02-paradox-free-validation_results.json
py 03-hahn-lifts-verify.py       # writes ./verification.json;       compare with data/03-hahn-lifts-verification.json
py 04-atlas-finite_checks.py > 04.json   # compare with data/04-atlas-finite_check_results.json
py 05-comprehensive-verification.py --output 05.json   # compare with data/05-comprehensive-verification.json
```

At the write (Python 3.14.4, Windows) all four passed in 0.7–6 s and
reproduced their records byte for byte after converting CRLF to LF, except
the interpreter version line of 04 (`3.13.5` recorded). The delivered build
scripts are not needed: they only run these programs and build the
delivered PDFs, whose sources are not shipped.

## Provenance

Six manuscripts (sources 02–07), base 03; Appendix C of the article gives
the full account. Pins: `af04de3fa` (02), `b0d4af4f3` (03, 07),
`a006a77a0` (04), `51b0a69d7` (05), `79049d58c` (06). Between the pins and
the placement only two files the sources read changed:
`omnific-preserving-automorphisms` (the correction `f06e67d10`) and
`surreal-fields-across-universes` (a reciprocal note, `d68b65ea0`).

- **Base choice.** 03 over 05: 03's stabilizer theorem contains the
  ordinal-fixing examples of 02, 04 and 05 and the ordinal-fixing
  automorphisms of 06 and 07; its initial-image theorem does not assume
  simplicity preservation; its profile rigidity is abstract; it needs no
  elementary transfinite recursion, satisfaction class or large cardinal.
- **Homes.** A result shared by members but absent from the base is printed
  once: local padding (05), local tree embeddings and ordinal blocks (02),
  elementary embeddings and abstract exponential rigidity (04), continuity
  between arbitrary fields and homogeneity (07), club localization, the
  Bagayoko–van der Hoeven fixed points and the translation parameter (06),
  `Frac(Oz) = No` (02). Different proofs are kept as marked second routes.
- **Bibliography.** Entries cited by several members are printed once;
  source 04 lists a third author (H. Mildenberger) for van den Dries and
  Ehrlich's *Homogeneous universal H-fields*, which the other sources and
  the arXiv record do not; the merged entry follows the latter.
- **Manuscript 01** (`Surreal_Self_Embeddings.zip`, pin `20aafb9a5`, 30 pp)
  is an earlier edition of 05: 89% of its distinct eight-word sequences
  recur in 05, all 52 of its labels reappear there, and 05 says it
  "incorporates and extends earlier working notes". Nothing of 01 is
  shipped. Its finite-check program (61,042 assertions; it passes on a copy)
  has groups that 05's rewrite does not keep (prefix cones, repetition by 2
  and 3, dilation difference quotients, two-probe displacement); they
  survive in its archive.
