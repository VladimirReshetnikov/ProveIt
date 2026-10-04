# Definable Surreal Numbers and Omnific Integers

**Ambient definability, reversible and bounded omnific coding, hereditary ordinal definability, a transcendence dichotomy, and the maximal initial core; real parameters, countable assembly and strong symmetries; definable operations and an interpretation of set theory**

A research report in three Parts, prepared for Vladimir Reshetnikov.
AI-assisted, unrefereed and not formalized.

- **Part I** (Sections 1–18, Appendices A–D): merged from two manuscripts
  written independently and dated 23 September 2026 (items 04 and 07 of batch
  27, placed in `a4dcb91`; they keep those numbers here).
- **Part II** (Sections 19–29): merged from manuscripts 02 (base) and 05 of
  batch 93, dated 4 October 2026.
- **Part III** (Sections 30–43): manuscript 06 of batch 93, dated 4 October
  2026, printed in full.

Part I's numbering and labels did not change when Parts II and III were added.

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 161 pages
README.md                                    this guide
04-hod-transcendence-AUDIT.md                source 04's research and verification audit, as delivered
07-initial-core-SOURCE_AND_PROOF_AUDIT.md    source 07's source and proof audit, as delivered
09-countable-assembly-PROOF_AUDIT.md         source 05's proof, source and verification audit, as delivered
10-definable-operations-PROOF_STATUS.txt     source 06's proof-status and contribution summary, as delivered
code/
  04-hod-transcendence-verify_finite.py      source 04 checks (standard library; prints JSON,
                                             writes a file only with --output)
  07-initial-core-verify_finite.py           source 07 checks (standard library; writes
                                             verification.json in the current directory by default)
  07-initial-core-Makefile                   source 07's build/check targets (delivered file names;
                                             they do not build this report)
  08-real-parameters-finite_code_check.py    source 02 checks of the slot code Z_f (standard library;
                                             prints only; no recorded output was delivered)
  08-real-parameters-build.sh                source 02's build script (builds the unshipped
                                             definable_surreals.tex; do not run)
  09-countable-assembly-verify_code.py       source 05 checks of the multiplexer (standard library;
                                             writes a file only with --output)
  09-countable-assembly-Makefile             source 05's build/check targets (delivered file names;
                                             they do not build this report)
data/
  04-hod-transcendence-verification_results.json   source 04's recorded run
  07-initial-core-verification.json                source 07's recorded run
  09-countable-assembly-verification.json          source 05's recorded run
```

Every label in `article.tex` carries the prefix `dsn:` (346 labels). Part I
has 139: 138 from the merge, and `dsn:rem:largecardinal`, added when the
large-cardinal report was written. Batch 93 added 207: the three Part labels
`dsn:part:one`, `dsn:part:rp`, `dsn:part:op`; 69 `dsn:rp:` (source 02 and the
write's notes in Part II); 53 `dsn:ca:` (source 05); 82 `dsn:op:` (source 06
and the write's notes in Part III). The
[formalization ledger](../../FORMALIZATION.md) indexes Part I under its
labels, with all claims **Pending**; it does not index Parts II and III, and it
supplies no checked implementation mapping for this report. Its line numbers
for this report were taken before Parts II and III were added.

## Part I: two sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **04** | *Definable Surreal Numbers and Omnific Integers: Ambient definability, reversible coding, hereditary ordinal definability, and a transcendence dichotomy* | `9a385d3` | The base text. The set-model framework (any set model, `V` as a scheme). The sign code `C` into `U = {z ∈ Oz : ω < z < ω + ω^{1/2}, ct z = 0}` (Theorem 6.2) and the two-term code (Proposition 6.5). The pointwise test for arbitrary set models. Support-subfield amplification and the `HOD` dichotomy (Theorems 8.2, 8.3), localization (Corollary 8.5). The termwise counterexample (Theorem 9.1) and the collector (Proposition 9.5). The first non-`HOD` birthday (Theorem 11.2). The `Σ_n` escape (Theorem 12.3). Forcing (Theorem 13.2), relativization (Proposition 14.1). Files prefixed `04-hod-transcendence-`. |
| **07** | *Definable Surreal Numbers and Omnific Integers: Ambient truth, bounded coding, and the maximal initial core* | `9a385d3` | Works over an externally fixed transitive model. Exponential elementarity (Theorem 4.4), the cut denominator (in Theorem 4.1), the valuation (Theorem 4.10). The monomial code and the local code (Theorems 6.8, 6.9), the birthday escape (Theorem 6.10). The bit code (Theorem 9.3) and the reverse gap (Theorem 9.6). The maximal initial core (Section 10). Hamkins's density theorem and the topology corollary (Theorem 7.5, Proposition 7.6). Language dependence (Section 15) and the arithmetic of the definable omnific ring (Section 16). Files prefixed `07-initial-core-`. |

The pin `9a385d3` is 35 commits before the placement `a4dcb91`. The source
manuscripts are not shipped: no delivered `.tex`, PDF or README is here. Their
code, recorded data and audits are shipped. The theorem numbers in
`04-hod-transcendence-AUDIT.md` are manuscript 04's; its Theorems 8.2–8.3 are
Theorems 8.2–8.3 here too. That audit's "all 51 reports" is the count at the
pin (see below). `07-initial-core-SOURCE_AND_PROOF_AUDIT.md` and the Makefile
name 07's delivered files `definable_surreals.tex` and `verification.json`.

**Why one report.** The two manuscripts have the same title and the same spine:

- the definable field and its integer part, with same-parameter denominators;
- the identification of the ordinal-definable surreals with `No^HOD`;
- bounded omnific tests for `V = HOD` and for pointwise definability;
- the gap between whole normal forms and their terms;
- noncollection;
- the definable closure of the pure field.

04 is the base because its hypotheses are the weaker ones on the shared
theorems: its pointwise test holds for arbitrary set models, including
ill-founded ones. 07's stronger conclusions (exponential elementarity, the core)
keep 07's transitive-model hypothesis. The two manuscripts do not contradict
each other or any report in the collection.

**Printed once**, crediting both sources:

- unique-output closure (Lemma 3.2);
- the omnific floor (Proposition 2.3);
- the definable closure of the pure field (Theorem 3.4);
- the definable field, integer part and fractions (Theorem 4.1);
- whole-family closure (Proposition 4.8);
- the `HOD` identification and the normal-form criterion (Theorem 5.1, Lemma 5.2);
- the `V = HOD` test (Theorem 7.2);
- the pointwise test (Theorem 7.7);
- noncollection (Theorem 12.5);
- set coding (Lemma 7.1);
- the complexification (Proposition 14.2).

**Kept as second routes.**

- 04's least-ordinal denominator and 07's cut denominator (Theorem 4.1).
- 04's sign code and 07's bit code for definable support with a nondefinable
  assignment (Theorems 9.1, 9.3).
- 04's collector and 07's reverse gap for a definable series with a
  nondefinable term (Proposition 9.5, Theorem 9.6).
- 04's two-term code and 07's monomial code (Proposition 6.5, Theorem 6.8).

**Cited, not reprinted.** 04's first-birthday theorem is the case `M = HOD`,
`N = V` of `univ:prop:beta` in the universes report, with the same proof. It is
printed by citation as Theorem 11.2; only 04's definability clause is its own.
07's arithmetic results are restricted duplicates of omnific Diophantine and
quotient results; the full-class labels are named at each statement.

**Added by the merge**, each tagged `[merge]`:

- the fix of a gap in 04's proof that a proper `K_HOD` is not intrinsically
  definable: the interval endpoints need not lie in the subfield
  (Proposition 5.4);
- Remark 2.5, the o-minimality of `No^M_exp` that 07 uses tacitly;
- 07's bounded conditions of the pointwise test for arbitrary set models
  (Theorem 7.7), and 07's bounded noncollection for arbitrary parameter
  families (Theorem 12.5);
- Proposition 15.3, what the collection proves about `(No, Oz)`, and the
  re-scoped Question 17.1;
- Remark 16.6, the relation to `odg:q:size`.

**Notation.** Symbols of 04 are kept where possible and 07's are renamed.
Section 1.5 lists every renaming. The main ones:

- 07's `Def_M(A)`, `D_M(A)`, `I_M(A)` are `D^M_A`, `K^M_A`, `I^M_A`.
- 07's core `K_M(A)` is `Core^M_A`; the letter `K` never denotes the core.
- 07's monomial code `C` is `Q`, its escape `T` is `esc`, its exponents
  `e_β = 1/(β+2)` are `ι_β`, its `B_α` is `No_{≤α}`, its subsets `B ⊆ α` are
  `X`, its width `h` is `ℓ`, and its `𝒥` is `Π`.
- 04's `C`, `T`, `e_β = ω^{-(β+1)}` and `B_n` are kept. Its collector map `h` is
  `ζ`, its set decoder `E` is `Set`, its ordinal code `B` is `X_a`.
- An epsilon number is `ϵ`, an infinitesimal `ε`. `λ_H` (first non-`HOD`
  birthday) and `ρ` (first ordinal not definable from `A`) are different
  invariants.
- `ω^x` is always the Conway map `Ω(x)`, never `exp(x log ω)`.

## What Part I claims

Numbers are those of `article.pdf`.

- **Theorem 4.1** (04, 07). `K_A` is a real closed field closed under `Ω`,
  `Ω^{-1}`, `exp`, `log` and the omnific floor; `I_A` is an integer part;
  `K_A = Frac(I_A)` with a denominator `ω^δ` or `ω^b` chosen by one rule from
  the same parameters; `K_A ≺ No` in the ordered-field language.
- **Theorem 4.4** (07). For transitive `M`, `K^M_A ≺ No^M` in the exponential
  language. **Theorem 4.10**: value group `(K_A, +)`, residue field
  `K_A ∩ R`.
- **Theorem 5.1** (04, 07). `No ∩ OD = No ∩ HOD = No^HOD`, and the same for
  `Oz`. It is an initial real closed field closed under `Ω`, `exp` and the
  floor, and the fraction field of its omnific integers. **Lemma 5.2**: `x` is
  `OD` iff its whole normal form is in `HOD`. **Proposition 5.4**: a proper
  `K_HOD` is not definable in the ordered field.
- **Theorem 6.2** (04). A parameter-free reversible code `C : No → U` with
  leading term `ω`, constant term 0 and coefficients in `{1, 2, 3}`.
  **Proposition 6.5**: the two-term code `ω + ω^{h(x)}`.
- **Theorems 6.8–6.10** (07). The monomial code `x ↦ ω^{τ(x)}`,
  `τ(x) = (1 + x/√(1+x²))/2`, into `Oz ∩ (0, ω)`; the local code in every
  infinitely wide omnific interval; a definable class function
  `esc : Ord → Oz ∩ (0, ω)` with `b(esc(α)) > α`.
- **Theorem 7.2** (04, 07). `V = HOD` iff every member of `U` is `OD`, iff
  every omnific integer in `(0, ω)` is `OD`, iff every monomial `ω^a` with
  `0 < a < 1` is `OD`. **Theorem 7.5** is Hamkins's 2012 density theorem,
  credited; **Proposition 7.6** is the case `M = HOD` of
  `univ:thm:nowheredense`.
- **Theorem 7.7** (04, 07). A set model is pointwise definable iff every
  member of `U^M` is parameter-free definable, iff the same for
  `Oz^M ∩ (0, ω)` or for the monomials `ω^a`, `0 < a < 1`.
- **Theorems 8.2, 8.3 and Corollary 8.5** (04). If `K ⊊ No` contains `ω` and
  every `ω^{-(α+1)}` and the supports of its elements, then for
  `t ∈ (0,1) \ K` the family `ω + ω^{t ω^{-(α+1)}}` is `Ord`-indexed and
  algebraically independent over `K`, inside `U`. Either `V = HOD`, or this
  holds over `K_HOD`. Localization at every definable infinite scale.
- **Theorems 9.1, 9.3, Proposition 9.5, Theorem 9.6** (04, 07). The two
  uniformity gaps.
- **Theorem 10.3** (07; transitive `M`). If `ρ` is the first ordinal of `M`
  not `A`-definable, it is an epsilon number, and `K^M_A ∩ No_{<ρ}` is the
  largest initial subclass of `K^M_A`, an elementary exponential subfield
  with an omnific integer part. **Theorem 10.5**: it is the fraction field of
  its omnific integers, with denominator `ω^{b(x)+1}`. **Corollaries 10.4,
  10.6, Proposition 10.7**: monotonicity, normal-form heredity, and
  finite-parameter discontinuity for externally uncountable `M`.
- **Theorem 11.2** (04; = `univ:prop:beta` with `M = HOD`). The first birthday
  of a non-`OD` surreal is the first ordinal with a non-`HOD` subset; it is a
  cardinal of `HOD` and `V` and parameter-free definable.
- **Theorem 12.3, Theorem 12.5, Corollary 12.6** (04, 07). `Σ_n` escape
  ordinals; no definable set contains its own definable hull, nor all
  definable omnific integers in `(0, ω)`; no uniform collector of the `B_n`.
- **Theorem 13.2** (04). Over `L`, `Add(κ,1)` gives `HOD = L`, first
  non-`HOD` birthday `κ`, and the independent family, with no new reals if
  `κ > ω`. **Example 13.4** (07): a Cohen real gives a non-`OD` omnific
  integer below `ω`.
- **Propositions 14.1, 14.2** (04, 07). Relativization to `OD(p)`; the
  surcomplex pairs.
- **Propositions 15.1, 15.2** (07). The exponential reduct defines only reals
  without parameters; order plus simplicity defines `ω`.
  **Proposition 15.3** (merge): in `(No, +, ·, <, Oz)` the parameter-free
  definable elements are reals (`opa:thm:fixed`), include every real
  definable in `(R, +, ·, <, Z)` (`odg:def:thm:realrecovery`), and no set of
  parameters defines the monomials (`opa:thm:parameters`).
- **Section 16** (07). `I_A = Π_A ⊕ Z`, finite quotients `Z/nZ`, profinite
  completion `Ẑ`, non-Noetherian, integer-coefficient equations transfer from
  `Z`. All are restrictions of `odg:`/`osq:` results; the size-boundary
  observation (Proposition 16.3) is already in `osq:sub:foundations`.

## What Part I does not claim

Appendix B lists every source's non-claims: 24 from 04, 25 from 07, and 4
added by the merge. In brief:

- No refereeing, no Lean formalization, no mapping to Lean declarations, no
  priority certification; the literature searches were limited.
- The codes are not ring homomorphisms and not definable in the ordered
  field; the monomial code uses `Ω`, not `exp`.
- `Ord`-indexed independence is finite-subfamily independence: no
  transcendence basis, Global Choice, class sum or cardinal of a proper class.
- No truth predicate for `V`; `D^V_∅` is not an internal set or class;
  definability is not computability.
- The core theorem is for transitive models only, and `ρ` is external. The
  reverse gap and the finite-parameter discontinuity are conditional.
- The `Σ_n` escape gives no one-step bound, closed form, algorithm or
  cofinality; the BCGHP corollary is a translation.
- Forcing statements do not preserve arbitrary old definitions; `V = HOD` is
  not preserved by arbitrary forcing.
- The full-class quotient theorem does not transfer to definable fragments; no
  Peano arithmetic.
- The finite checks are regression tests; they verify no transfinite, `HOD`,
  cutoff, elementarity or core statement.
- Merge: `dcl_∅(No, Oz)` is not identified exactly; `odg:q:size` is not
  answered; amplification is not claimed for general same-ordinal inner
  models; the agreement of `HOD`'s internal omega map, exponential and normal
  forms with the ambient ones rests on the sources' recursion argument.

## Open questions, re-scoped

- **Question 17.1** merges 04's question on the omnific predicate and 07's
  question on languages between fields and set theory. It is **largely
  answered** from the collection by Proposition 15.3 (`opa:thm:fixed`,
  `opa:thm:parameters`, `odg:def:thm:realrecovery`,
  `odg:def:cor:arithmetic`): only reals can become definable, all reals
  definable in `(R, +, ·, <, Z)` do, and the monomials are not definable with
  set parameters. The exact real closure and the omega-map expansion stay
  open. **Batch 93:** the omega-map half is answered at the level of an
  interpretation: with `Oz` and `Ω` named, every coefficient is definable and
  `(V, ∈)` is interpreted parameter-free (Theorems 36.3, 37.1); the definable
  closures and a bi-interpretation stay open (Questions 42.1, 42.2).
- **Questions 17.2–17.5**: birthday cost of the sign code (04), intermediate
  support fields (04; the universes-report inner models are recorded as an
  unproved instance), possible first omitted ordinals (07), syntactic costs
  (07). All open. **Batch 93:** Question 17.5 is answered in part (`Δ_1`
  graphs of the canonical operations and level preservation by the monomial
  code, Theorem 34.7, Corollary 40.3); Questions 17.2 and 17.4 are refined by
  Questions 42.7, 42.11 and the birthday-cost questions of Section 28.
- **Remark 17.6** (added with the
  [large-cardinal report](../large-cardinal-embeddings-and-normal-forms/)):
  that report's absoluteness lemma `lce:lem:absolute` gives omega-map and
  normal-form absoluteness for transitive inner models with the same ordinals
  and the same reals, so for such a proper `M` the field `No^M` satisfies the
  hypotheses of Theorem 8.2 (`lce:rem:dsnsupport`). This supplies the
  same-reals instance that Question 17.3 recorded as unproved, including the
  targets of elementary embeddings with a critical point. Inner models lacking
  a real (`L` when not every real is constructible, `HOD` when it lacks a real)
  were not covered. **Batch 93:** they are now: Part III proves normal-form
  absoluteness without the same-reals hypothesis (Theorem 34.1), so every
  transitive inner model `M ≠ V` of ZFC gives a support field (Corollary 34.4)
  and the independent family (Corollary 40.2); `K_R` is a further instance
  (Remark 22.10). A dated note after Remark 17.6 records this. The
  classification asked in Question 17.3 stays open (Question 42.11).
- **`odg:q:size`** (omnific Diophantine report): the definable fragments give
  one instance (Remark 16.6). This is partial information; the question stays
  open. The other report was not edited.

## Stale statements corrected

Appendix A.3 records these.

- 04's "all 51 reports": 51 at the pin; at the placement the collection has 53
  written reports, and this report was placed together with two others.
- 04 credited only an "older repository discussion" for its first-birthday
  theorem. The exact theorem is `univ:prop:beta`; the birthday-cutoff report
  has it as `hset:thm:firstbirthday`.
- 04 did not credit Hamkins's 2012 density/`V = HOD` answer; added.
- 07's "external size-boundary warning supplied here" is in the quotient
  report (`osq:sub:foundations`, from its manuscripts 04, 10 and 11).
- 07's formula defining the ordinals from order and prefix is the one in the
  proof of `hset:prop:nondef`; credit added.
- 07 cited van den Dries–Ehrlich without the erratum; the erratum and
  Bournez–Guilmant are added.
- 07's "Theorem 14.3" of the universes report is `univ:thm:nowheredense`. Its
  statement that the universes report develops the compatibility of normal
  forms and exponential is only partly accurate: `univ:prop:absolute` covers
  arithmetic and cuts.
- 07's arithmetic restates `odg:thm:finitequotients`, `odg:prop:notnormal`,
  `odg:thm:transfer`, `odg:def:thm:ideal` and `odg:rem:foursquares`; the
  labels are now named.
- 07 gave Gonshor's book as Lecture Note Series 124; it is 110.
- Neither source knew the automorphisms report or the reconstruction section
  of the omnific Diophantine report; their language questions are re-scoped.

## Part II: real parameters, countable assembly and strong symmetries (batch 93, sources 02 and 05)

Sections 19–29 of `article.pdf`, labels `dsn:rp:` (source 02) and `dsn:ca:`
(source 05). Written 4 October 2026.

| | Manuscript | Batch-93 no. | Archive | Pin | Printed |
|---|---|---|---|---|---|
| **02** | *Definable Surreal Numbers and Omnific Integers: Real Parameters, Countable Closure, and Strong Symmetries* | 02 | `definable_surreals.zip` | `3c25fbb55` | Sections 19–29 in full (base): its Section k is Section k+18, its statement k.m is (k+18).m. Files prefixed `08-real-parameters-`. |
| **05** | *Definable Surreal Numbers and Omnific Integers: Real parameters, ordinal information, and countable assembly* | 05 | `definable_surreals_real_parameters.zip` | `a9ab9a698` | Inserted by subject after source 02's material in each section, marked [05]; Table 5 (Section 19.7) locates every numbered item. Files prefixed `09-countable-assembly-`. |

Both archives arrived in `2faa3b37a`; placement `47a77daba`. The two are not
editions of one text (different pins, under 1% shared 8-grams, neither cites
the other) but prove the same central theorems. **Base 02**: its negative
result needs only Con(ZFC) (Namba forcing over `L`, Theorem 25.6) where 05
needs a measurable cardinal.

**Printed once**, both sources named: the countable-assembly equivalence
(02's Theorem 5.1 = 05's Theorem 7.2: Theorem 23.1, with 05's further clauses
`ROD = COD`, `K_R = K_co`, whole sequences of ROD sets, as Theorem 23.9 and 05's
proof as a second route); the Cohen classification (02's 6.1 = 05's 9.3:
Theorem 24.1, with 05's ring form and proof as a second route); the global
test (05's Proposition 5.4: Proposition 22.9, printed for its invariant
`λ_R`). 05's re-proofs of Part I background are pointers with 05's proofs as
second routes (Section 21.6). **Two codes kept**: 02's slot code `Z_f` and 05's
multiplexer `𝒵(f)` (Theorem 23.5), the same construction with different band
constants. **Prikry**: 02's Theorem 25.4 and 05's Theorem 10.2 (Theorem 25.7,
with its graph-coding proof as a second route).

**What Part II claims** (numbers of `article.pdf`):

- **Theorems 22.2–22.3, Corollary 22.5** (02). `K_r ⊆ K_s` iff `r` is
  `OD(s)`; the varying-real field `K_R = ⋃_r No^{HOD(r)}` is captured by one
  real iff `HOD_R ⊨ AC`; `K_R = No` iff `V = HOD(r)` for one real `r`.
  Source 06 proves Corollary 22.5 independently (Remark 22.7, with its
  monomial clause). Answers 05's Question 13.7 negatively.
- **Theorem 23.1** (02, 05). Every `f : ω → Ord` is ROD iff `HOD_R` is closed
  under ω-sequences iff `K_R` is closed under countable Hahn sums iff sums of
  OD purely infinite omnific integers stay in `I_R` iff `K_R` is `η_1`
  (ambient countable cuts filled). **Theorem 23.9** (05): also iff
  `ROD = COD` iff `K_R = K_co`. **Theorem 23.15** (05): `K_co` is the least
  ambiently stable, countably Hahn-closed subclass containing `K_R`;
  **Remark 23.18** (write): containing `Ord` suffices.
- **Theorems 24.1, 24.4, Corollary 24.2, Proposition 24.3** (02, 05). Cohen
  `Fn(λ×ω, 2)` over `L`: `K_R = ⋃_S No^{W_S}`, an exactly `ω_1`-long chain,
  first omitted birthday `ω_1`, `η_1` but not `η_2`; **Theorem 24.9** (05) adds
  `K_HOD = No^W` and a non-ROD omnific integer below `ω`.
- **Theorems 25.4, 25.6** (02). Prikry over a measurable: a countable sum of
  OD omnific monomials in `(ω, ω+ω^{1/2})` that is not ROD. Namba over `L`:
  `HOD_R = HOD = L = W` yet a countable set of ordinals is not ROD, so
  countable assembly is independent of ZFC (from Con(ZFC)). The no-new-reals
  input is imported (see below).
- **Theorems 26.4–26.5** (02). The common fixed field of the strong
  automorphisms fixing `R ∪ Ord` (also with `Oz` preserved) is
  `Ser(span_Q Ord)`; answers the strong form of `sse:sr:q:stabilizers`.
  Corollary 26.6, Propositions 26.7–26.9, 26.12, Theorem 26.10 (02):
  definable-closure bounds, value groups, the witness `𝓔 = Σ ω^{-n}/n!`, an
  OD independent family not definable from real and ordinal parameters with
  `Oz`, `R`, `Ord` named.
- **Remark 22.10** (write): `K_R` satisfies the hypothesis of Theorem 8.2, so
  the independent family exists over `K_R` when `V ≠ HOD_R`.

## Part III: definable operations (batch 93, source 06)

Sections 30–43, labels `dsn:op:`. Source 06, *Definable Surreals and
Omnific Arithmetic: Parameter hierarchies, absolute normal forms, uniform
coding, and an interpretation of set theory* (archive
`definable_surreal_operations.zip`, arrival `de37a66d1`, pin `1404038df`,
placement `47a77daba`, prefix `10-definable-operations-`), printed in full:
its Section k is Section k+29, its statement k.m is (k+29).m. Its Theorem 4.2
(= 02's Corollary 4.5) and Corollary 4.3 (= 05's Theorem 5.2) are printed once,
in Part II; Remarks 33.2–33.3 keep their numbers as pointers.

**What Part III claims:** the decoder of real codes for countable sign
sequences has an `OD(p)` right inverse iff `ω_1^{HOD(p)} = ω_1`, and the
`κ`-analogue (Theorems 33.4, 33.6, Corollary 33.7); canonical arithmetic,
`Ω`, complete normal forms and set-indexed sums are absolute between nested
transitive ZFC models **without a same-reals hypothesis** (Theorem 34.1), so
every transitive inner model gives a support field (Corollary 34.4) and an
independent family (Corollary 40.2); `Δ_1` graphs of the canonical
operations (Theorem 34.7); every coefficient and truncation is definable in
`(No, +, ·, <, Oz, Ω)` (Theorem 36.3); a parameter-free quotient
interpretation of `(V, ∈)` there, with representatives in `{ω^a : 0 < a < 1}`
(Theorem 37.1); definable Hahn summation of coded families (Theorem 38.3);
coefficient-indexed derivations (Theorem 39.1); elementary-theory transfer
(Theorem 40.4).

**Notes added at the write:** after Theorem 40.4, a proved observation: for
nested models of the same height, both sides of its elementary-inclusion
clause hold only when `M = W` (the argument of `hset:thm:outer`). After the
sign-limit normal-form fact used for Theorem 34.1(3)–(4), a check: it follows
from Gonshor's Theorems 5.11–5.12 as formulated by Bournez–Guilmant
(Definition 2.20, Theorem 2.21; the write did not consult Gonshor's book).

**Batch-95 notes (4 October 2026):** Part IX of
[`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
(batch 95) proves the comparison map for the birthday-enriched signature
`(No; 0, 1, +, −, ·, <, ≺_b)` and natively for `Oz` (its Theorems 71.1, 72.2,
`hset:sf:thm:graph`, `hset:sf:thm:roundtrip`), and shows (its Proposition
74.2, `hset:sf:prop:reducts`) that for `(No, +, ·, <, Oz, Ω)` Question 42.1 in its specific
form, a definable relation sending each surreal to the codes of its own sign
sequence, is equivalent to the definability of birthday precedence there;
whether it is definable is not decided, and the question stays open. A dated
note after Question 42.1 records this; a second, after Question 42.3, records
that the same proposition reduces only the analogue of 42.3 for
interpretations with such a comparison to definability (its Question 79.3,
`hset:sf:q:reducts`, asks which reducts qualify), and leaves 42.3 itself
untouched. These notes move the page count from
160 to 161 (the end of Section 42 and the bibliography shift by about one
page); no label number changed.

## Unproved claims recorded as questions (Vladimir's rule of 4 October 2026)

- **Question 28.17**: 02 imports "Namba forcing in the Laver-style
  presentation adds no reals under CH" from Lietz's exposition and Miller's
  notes. Jech (Ch. 28) and Shelah (*Proper and Improper Forcing*, Ch. XI) are
  added as the standard references, but the write did not consult them or
  confirm which presentation they treat; `univ` imports the theorem for the
  classical presentation from FKW §7.6.
- **Questions 42.13–42.14**: 06's Remark 4.5 (Remark 33.5; `Δ_1` decoder,
  `Σ_2(p)`/`Δ_2(p)` sections) and its description-length bound (40.2) are
  argued as sketches and upper bounds.
- **Superseded, not wrong**: 05's Section 10.3 and Question 13.1 (a
  measurable as the known upper bound for failure of assembly) carry a dated
  note: Theorem 25.6 needs only Con(ZFC). 05's Question 13.7 is answered
  negatively. No claim of 02, 05 or 06 was found to be wrong.

## What Parts II and III do not claim

Each source's non-claims are kept in its text (Sections 19, 23–25, 28–29 and
30, 42–43): no refereeing, no Lean or Rocq verification, no priority
certification (selective searches; Solovay's COD assembly and the
Kanovei–Lyubetsky formulation are prior); the Prikry construction is a
relative-consistency example, not failure in every universe, and the
measurable is an upper bound only; no uniform truth predicate for `V`;
`HOD_R` is not assumed to satisfy Choice; Theorem 22.2's least upper bound is
within the family; Dependent Choice has no converse; ordinal-indexed
independence is finite-subfamily independence; the strong stabilizer theorem
does not compute the nonstrong fixed field (Question 28.1) and Proposition
26.11 does not classify the omega-map expansion; 05's completion is a
minimality statement for a closure scheme, not a Dedekind or topological
completion, and needs ambient stability; Part III proves no bi-interpretation
of `(No, +, ·, <, Oz, Ω)` with set theory and does not determine its definable
closures; over ZF its quotient presents the hereditarily well-orderable sets;
its `D_b` are diagonal Euler derivations, not the Berarducci–Mantova
derivation; sums need whole family codes; the finite scripts check rational
specializations only.

## Relation to the neighbouring reports

- [`surreal-fields-across-universes`](../surreal-fields-across-universes/)
  (`univ:`). Theorem 11.2 is its `univ:prop:beta` at `M = HOD`, printed by
  citation; Proposition 7.6 is its `univ:thm:nowheredense` at `M = HOD`; its
  `univ:prop:absolute` gives the arithmetic part of Theorem 5.1. None of its
  named questions is answered here. Batch 93: Part II's Prikry gap
  (Corollary 25.5) relates to `univ:cor:prikry`; its Namba theorem (25.6) uses
  the Laver-style presentation, `univ:gs:thm:nambainput` the classical one;
  Part III's Section 41 re-proves `univ:prop:beta` for inner models and
  Theorem 34.1(1)–(2) `univ:prop:absolute`.
- [`surreal-self-embeddings`](../../surreal/surreal-self-embeddings/)
  (`sse:`). Part II's Theorem 26.5 answers the strong form of
  `sse:sr:q:stabilizers` (the nonstrong form is Question 28.1); Part III's
  Theorem 34.1(1)–(2) is its `sse:pf:lem:absolute`. That report was not
  edited.
- [`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
  (`hset:`). Batch 93: Part III's interpretation (Theorem 37.1) is for
  `(No, +, ·, <, Oz, Ω)`, not the birthday-enriched structures of
  `hset:thm:biinterpretation`; its Theorem 40.4 is the analogue of
  `hset:rem:internal` and `hset:thm:outer` (a dated note proves that its nested
  clause is trivial for models of the same height). It credits the
  Chen–Hamkins–Yang announcement (`hset:thm:chy`),
  proves the first new birthday (`hset:thm:firstbirthday`), and uses the
  `OrdSign` formula (`hset:prop:nondef`). Its cutoff inputs (erratum,
  Bournez–Guilmant) are the ones Theorem 10.3 uses. Its batch-89 Part VII
  proves the case `K = R`, `G = {0}` of Lemma 8.1 (`dsn:lem:cosets`) again
  (`hset:kw:thm:double`, double monomials `ω^(ω^j(x))`) and calibrates
  free-algebra universality of `No` and `Oz` over ZF by the first
  Kinna–Wagner principle (`hset:kw:thm:equivalences`); an unnumbered note
  after Lemma 8.1 (batch 89) records this. Batch 95: its Part IX proves the
  comparison map for the birthday-enriched signature and reduces
  Question 42.1 for `(No, +, ·, <, Oz, Ω)` to the definability of birthday precedence
  (`hset:sf:prop:reducts`); see the batch-95 notes under Part III above.
- [`cantor-families-of-surreal-subfields`](../cantor-families-of-surreal-subfields/)
  (`csf:`, batch 90). Its Lemma 3.2 (`csf:lem:independence`) proves again the
  case `K = k` (real algebraic numbers), `G = {0}`, exponents `b ω^q` with
  `b ∈ {1, √2, √3, √5, …}` of Lemma 8.1, and uses it as the transcendence
  basis of a countable real closed field whose Cantor family of subfields has
  complete analytic embeddability (`csf:thm:universality`). A second
  unnumbered note after Lemma 8.1 (batch 90) records this; it moves the page
  count from 55 to 56 and changes no label number.
- [`omnific-diophantine-geometry`](../../surreal/omnific-diophantine-geometry/)
  (`odg:`). Full-class antecedents of Theorem 4.1 (`odg:thm:fractions`) and of
  Section 16; its reconstruction section enters Proposition 15.3; its
  `odg:q:size` receives one instance (Remark 16.6). Part III's Proposition
  35.1 and Section 36.1 largely re-prove `odg:def:thm:realrecovery`,
  `odg:def:cor:arithmetic` and `odg:def:cor:internal`.
- [`real-vector-space-structure`](../../surreal/real-vector-space-structure/)
  (`rvs:`). Part III's derivations `D_b` (Theorem 39.1) are instances of
  `rvs:thm:diagonal-derivation`, credited by source 06.
- [`set-sized-quotients-of-omnific-integers`](../../surreal/set-sized-quotients-of-omnific-integers/)
  (`osq:`). Its universal theorem `osq:thm:universal` and its universe-relative
  reading (`osq:sub:foundations`) are the full-class side of Section 16.
- [`omnific-preserving-automorphisms`](../../surreal/omnific-preserving-automorphisms/)
  (`opa:`). Its `opa:thm:fixed` and `opa:thm:parameters` answer most of both
  sources' language questions (Proposition 15.3). Batch 93: without a
  predicate for `Ord`, Part II's Corollary 26.6 and the nondefinability
  statements after Theorem 26.10 follow from `opa:sc:cor:innerbound`,
  `opa:thm:parameters` and `opa:sc:thm:undef` (not cited by source 02; dated
  notes there); Theorem 26.5 is the proper-class analogue of `opa:thm:hull`.
- [`computable-surreals`](../computable-surreals/). Definability is kept
  distinct from its computable representations (Section 3.4, Question 17.5).
- [`large-cardinal-embeddings-and-normal-forms`](../large-cardinal-embeddings-and-normal-forms/)
  (`lce:`). Its absoluteness lemma supplies the same-reals instance of
  Question 17.3 (Remark 17.6). The rest of Part I is unchanged by it.
  Batch 93: Part III removes the same-reals hypothesis of `lce:lem:absolute`
  for normal forms and sums (Theorem 34.1(3)–(5)), which settles the case
  `lce:rem:dsnsupport` leaves open. That report was not edited.
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/)
  (`saut:`). Its batch-34 `saut:gr:prop:finite` and `saut:gr:prop:dio` prove
  the finite-quotient statement of Theorem 16.2, and the transfer of integer
  polynomial systems through `ct`, uniformly for its integer-part rings `R_F`
  over set-sized real closed fields (`Oz = R_R`; `2^𝔠` pairwise nonisomorphic
  among them), and cite Theorem 16.2 for the rings `I_A`. An unnumbered note
  after Theorem 16.2 records this; it changed no number and no page count.
- [`discrete-initial-subgroups-and-omnific-normalization`](../../surreal/discrete-initial-subgroups-and-omnific-normalization/)
  (`isg:sc:`; batch 86, its source 03). By Proposition 16.1, `I_A` has
  division by every ordinary integer and the retraction `ct`, so its
  `isg:sc:thm:boundary` applies: the nonnegative part of `I_A` satisfies
  open induction (Corollary 4.6) but not `IΔ0`, as for `Oz`. That report
  states its theorems for set-sized rings and reads class applications as in
  `isg:sc:sec:classes`; this report does not make `I_A` a set (only the
  externally countable `I^M_A` of a transitive set model `M`), so its
  Presburger initiality criterion is not applied here.
- [`polish-models-of-omnific-arithmetic`](../polish-models-of-omnific-arithmetic/)
  (`pma:`; batch 86): `pma:bor:thm:arithmetic` (Part II) and
  `pma:ser:prop:iopen` (Part V) prove open induction for finite
  principal-part integer parts by the route of Corollary 4.6; Part V's ring
  is countable (real algebraic coefficients) and lives in a Polish ordered
  field. One unnumbered note after Corollary 4.6 records both relations
  (batch 86).

## What was run

For this merge both suites were rerun on copies with Python 3.14.4. Each
reproduced its recorded result (identical to the shipped JSON up to line
endings):

| Suite | Result |
|---|---|
| 04 | `passed`: 8,191 code round trips (lengths ≤ 12), 11 malformed codes rejected, 3,121 rational normalizations, 3,120 order comparisons, 2 endpoints rejected, 2,157 floor cases, 500 coset polynomials with 55,105 noncancelled terms, 1 negative control |
| 07 | `PASS`: 8,191 bit codes (lengths 0–12), 4 malformed codes rejected, 555 compression/inverse pairs, 554 monotonicity pairs, 1,161 floor cases, 24 support-shift cases |
| 02 (batch 93) | `PASS`: 1,104 exact slot-bound and inverse checks, 76,176 adjacent-slot order checks (no recorded output delivered) |
| 05 (batch 93) | `all checks passed`: 20,508 inverse checks, 206 sequence checks, 1,000 band checks, 4 invalid-input rejections; JSON identical to the shipped record up to line endings |

Source 06 ships no code. Source 05's checksum manifest (7 entries) verified
7/7 at placement and is not shipped.

Both suites use exact arithmetic on finite formal normal forms and never
replace `ω` by a real. The floor tests re-implement the floor formula they
test, and the coset test works in a finite group algebra; neither suite
touches definability, `HOD` or transfinite objects.

## Publication review corrections (4 October 2026)

The bounded review of publication `c7d65e30b` completes the promised source 05
band-exponent rename to `b_n` and the two Prikry references to `e_{κ_n}`.
The Part I cost summary and contribution ledger now distinguish established
Levy-level preservation from source 06's proposed additive description-length
bound. Both retain the earlier wording and point to the credited, still-open
Question 42.14; the length claim has not been refuted.

The edited source was built directly with three `pdflatex -no-shell-escape`
passes in a scratch directory. The PDF of that review had 160 pages, 346 unique labels,
823 resolved literal internal references and 190 citations to 45 bibliography
keys. The final log has no warnings, undefined references or bad boxes.
Physical PDF pages 48, 82, 93 and 156 were visually checked. This build and source
check do not certify the full manuscript mathematics or replay supplied code.

## Build and reproduce

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The original publication recorded a standard-package build with no errors,
warnings, overfull or underfull boxes, undefined references, multiply defined
labels or duplicate destinations (160 pages). The publication review build is
recorded above. After the batch-95 notes, `latexmk -pdf` (pdflatex) gives 161
pages with no errors, warnings, overfull or underfull boxes, undefined
references, multiply defined labels or duplicate destinations, and the same
692 `\newlabel` entries with unchanged numbers as the build of the committed
text. Build in a scratch directory; auxiliary files are not kept here.

07's script writes `verification.json` into the current directory unless
`--output` is given, and `make verify` in 07's Makefile does the same; 04's
delivered README told the user to write its output over the recorded file.
So rerun the checks on a copy, with explicit output names:

```
mkdir dsn-checks && cp code/*.py dsn-checks/ && cd dsn-checks
python 04-hod-transcendence-verify_finite.py --output rerun-04.json
python 07-initial-core-verify_finite.py --output rerun-07.json
```

`code/07-initial-core-Makefile` is shipped as delivered. It names 07's own
files (`definable_surreals.tex`, `verify_finite.py`, `verification.json`),
which are not present here under those names, so it does not run as-is.

For Parts II and III (batch 93), likewise on a copy:

```
mkdir dsn-checks-93 && cp code/08-*.py code/09-*.py dsn-checks-93/ && cd dsn-checks-93
python 08-real-parameters-finite_code_check.py
python 09-countable-assembly-verify_code.py --output rerun-09.json
```

and compare `rerun-09.json` with `data/09-countable-assembly-verification.json`
(equal up to line endings). The delivered files keep their delivery names and
are not edited:

- `code/09-countable-assembly-Makefile` and the usage line of
  `09-countable-assembly-verify_code.py` name `article.tex`,
  `code/verify_code.py` and `data/verification.json` (05's delivery layout);
  `make check` would write over a recorded output, and `make pdf`/`make clean`
  act on an `article.tex`, so do not run them here.
- `code/08-real-parameters-build.sh` changes to its own directory and builds
  `definable_surreals.tex`, which is not shipped; it would create `build/`
  there. Do not run it in the repository.
- `09-countable-assembly-PROOF_AUDIT.md` writes source 05's band exponents
  `e_n(a)` (here `b_n(a)`) and names 05's files; its theorem numbers are 05's
  (Table 5 maps them). `10-definable-operations-PROOF_STATUS.txt` uses
  manuscript 06's numbers (add 29 to the section number) and names its
  unshipped source and PDF.
- `08-real-parameters-finite_code_check.py` says it checks "Section 5" of
  manuscript 02, which is Section 23 here.

To rebuild a manuscript as delivered, extract it from the arrival commit
(`git show 2faa3b37a:docs/incoming/definable_surreals.zip`,
`…/definable_surreals_real_parameters.zip`;
`git show de37a66d1:docs/incoming/definable_surreal_operations.zip`) into a
scratch directory on a POSIX host.
