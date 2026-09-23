# Definable Surreal Numbers and Omnific Integers

**Ambient definability, reversible and bounded omnific coding, hereditary ordinal definability, a transcendence dichotomy, and the maximal initial core**
Merged research report from two manuscripts written independently and dated
23 September 2026 (items 04 and 07 of batch 27, placed in `a4dcb91`; they keep
those numbers here). Prepared for Vladimir Reshetnikov.

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 55 pages
README.md                                    this guide
04-hod-transcendence-AUDIT.md                source 04's research and verification audit, as delivered
07-initial-core-SOURCE_AND_PROOF_AUDIT.md    source 07's source and proof audit, as delivered
code/
  04-hod-transcendence-verify_finite.py      source 04 checks (standard library; prints JSON,
                                             writes a file only with --output)
  07-initial-core-verify_finite.py           source 07 checks (standard library; writes
                                             verification.json in the current directory by default)
  07-initial-core-Makefile                   source 07's build/check targets (delivered file names;
                                             they do not build this report)
data/
  04-hod-transcendence-verification_results.json   source 04's recorded run
  07-initial-core-verification.json                source 07's recorded run
```

Every label in `article.tex` carries the prefix `dsn:` (139 labels: 138 from
the merge, and `dsn:rem:largecardinal`, added when the large-cardinal report
was written). The
[formalization ledger](../../FORMALIZATION.md) now indexes the assembled
report under these labels, with all claims **Pending**. It supplies no
checked implementation mapping for this report.

## Two sources, one report

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

## What the report claims

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

## What the report does not claim

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
  open.
- **Questions 17.2–17.5**: birthday cost of the sign code (04), intermediate
  support fields (04; the universes-report inner models are recorded as an
  unproved instance), possible first omitted ordinals (07), syntactic costs
  (07). All open.
- **Remark 17.6** (added with the
  [large-cardinal report](../large-cardinal-embeddings-and-normal-forms/)):
  that report's absoluteness lemma `lce:lem:absolute` gives omega-map and
  normal-form absoluteness for transitive inner models with the same ordinals
  and the same reals, so for such a proper `M` the field `No^M` satisfies the
  hypotheses of Theorem 8.2 (`lce:rem:dsnsupport`). This supplies the
  same-reals instance that Question 17.3 recorded as unproved, including the
  targets of elementary embeddings with a critical point. Inner models lacking
  a real (`L` when not every real is constructible, `HOD` when it lacks a real)
  are not covered, and Question 17.3 itself stays open.
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

## Relation to the neighbouring reports

- [`surreal-fields-across-universes`](../surreal-fields-across-universes/)
  (`univ:`). Theorem 11.2 is its `univ:prop:beta` at `M = HOD`, printed by
  citation; Proposition 7.6 is its `univ:thm:nowheredense` at `M = HOD`; its
  `univ:prop:absolute` gives the arithmetic part of Theorem 5.1. None of its
  named questions is answered here.
- [`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
  (`hset:`). It credits the Chen–Hamkins–Yang announcement (`hset:thm:chy`),
  proves the first new birthday (`hset:thm:firstbirthday`), and uses the
  `OrdSign` formula (`hset:prop:nondef`). Its cutoff inputs (erratum,
  Bournez–Guilmant) are the ones Theorem 10.3 uses.
- [`omnific-diophantine-geometry`](../../surreal/omnific-diophantine-geometry/)
  (`odg:`). Full-class antecedents of Theorem 4.1 (`odg:thm:fractions`) and of
  Section 16; its reconstruction section enters Proposition 15.3; its
  `odg:q:size` receives one instance (Remark 16.6).
- [`set-sized-quotients-of-omnific-integers`](../../surreal/set-sized-quotients-of-omnific-integers/)
  (`osq:`). Its universal theorem `osq:thm:universal` and its universe-relative
  reading (`osq:sub:foundations`) are the full-class side of Section 16.
- [`omnific-preserving-automorphisms`](../../surreal/omnific-preserving-automorphisms/)
  (`opa:`). Its `opa:thm:fixed` and `opa:thm:parameters` answer most of both
  sources' language questions (Proposition 15.3).
- [`computable-surreals`](../computable-surreals/). Definability is kept
  distinct from its computable representations (Section 3.4, Question 17.5).
- [`large-cardinal-embeddings-and-normal-forms`](../large-cardinal-embeddings-and-normal-forms/)
  (`lce:`). Its absoluteness lemma supplies the same-reals instance of
  Question 17.3 (Remark 17.6). The rest of this report is unchanged by it.

## What was run

For this merge both suites were rerun on copies with Python 3.14.4. Each
reproduced its recorded result (identical to the shipped JSON up to line
endings):

| Suite | Result |
|---|---|
| 04 | `passed`: 8,191 code round trips (lengths ≤ 12), 11 malformed codes rejected, 3,121 rational normalizations, 3,120 order comparisons, 2 endpoints rejected, 2,157 floor cases, 500 coset polynomials with 55,105 noncancelled terms, 1 negative control |
| 07 | `PASS`: 8,191 bit codes (lengths 0–12), 4 malformed codes rejected, 555 compression/inverse pairs, 554 monotonicity pairs, 1,161 floor cases, 24 support-shift cases |

Both suites use exact arithmetic on finite formal normal forms and never
replace `ω` by a real. The floor tests re-implement the floor formula they
test, and the coset test works in a finite group algebra; neither suite
touches definability, `HOD` or transfinite objects.

## Build and reproduce

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses standard packages only and gives no errors, warnings, overfull
or underfull boxes, or undefined references. Build in a scratch directory; the
auxiliary files are not kept here.

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
