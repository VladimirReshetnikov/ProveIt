# Critical-Point Defects in Surreal Arithmetic

**Large-cardinal embeddings, exact support thresholds, descent to the target model, omnific independence, surcomplex fields, omnific integers, and measurable first failures of summation**
Merged research report, 23 September 2026, built from four manuscripts:
three of batch 30 (manuscripts 06, 07 and 09, placed in `21375f8`; they keep
those numbers here), pinned to repository commit `0865f04`, and manuscript
05 of batch 32 (local number 10, placed in `7d04483`), pinned to `7af8a30`.
Each was prepared for Vladimir Reshetnikov (07, 09 and 10 with ChatGPT).
Manuscript 07 is the base text; manuscript 10 is Sections 22–26.

Independent proof review and formalization are pending. No statement of this
report has a Lean implementation mapping, and the report was not refereed.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 109 pages (unnumbered title page,
                                            front matter i–iv, then pages 1–104)
README.md                                   this guide
06-critical-supports-PROOF_STATUS.md        source 06's proof status and source audit, as delivered
07-critical-point-defects-PROOF_STATUS.md   source 07's proof, provenance and verification status, as delivered
09-support-geometry-PROOF_STATUS.md         source 09's proof status and assumptions, as delivered
10-measurable-spectrum-PROOF_STATUS.md      source 10's claim inventory, review priorities and non-claims, as delivered
10-measurable-spectrum-SOURCE_AUDIT.md      source 10's repository and literature audit, as delivered
code/
  06-critical-supports-build.sh             source 06's build helper, as delivered (does not run here)
  07-critical-point-defects-build.sh        source 07's build helper, as delivered (does not run here)
  07-critical-point-defects-finite_regression.py
                                            source 07's exact finite checks (standard library only)
  09-support-geometry-build.sh              source 09's build helper, as delivered (does not run here)
  10-measurable-spectrum-build.sh           source 10's build helper, as delivered (does not run here)
  10-measurable-spectrum-finite_regression.py
                                            source 10's exact finite checks (standard library only)
data/
  07-critical-point-defects-build_validation.json         07's record of its delivered PDF build
  07-critical-point-defects-finite_regression_results.json  07's recorded run of the finite checks
  07-critical-point-defects-finite_regression_console.txt   the same run's console output
  10-measurable-spectrum-build_validation.json            10's record of its delivered 24-page PDF
  10-measurable-spectrum-compile_console.txt              10's latexmk transcript of that build
  10-measurable-spectrum-finite_regression_console.txt    10's recorded console output of its finite checks
  10-measurable-spectrum-finite_regression_results.json   10's recorded JSON of the same run
```

Every label in `article.tex` carries the prefix `lce:` (323 labels). The 120
labels delivered with 07 are kept, unchanged after the prefix. The
three-source merge added 134: 56 for 06's material (`lce:cs:`, "critical
supports"), 59 for 09's (`lce:sg:`, "support geometry"), 11 on 07's
previously unlabelled questions (`lce:q:classification` … `lce:q:formal`),
and 8 for merge text (`lce:sub:headlines`, `lce:sub:nonasserted`,
`lce:sec:conventions`, `lce:rem:dsnsupport`, `lce:rem:opa`,
`lce:sub:collection`, `lce:app:nonclaims`, `lce:app:provenance`). Batch 32
kept all 254 and added 69 with the sub-prefix `lce:mf:` ("measurable
failures") for manuscript 10 and its merge text; no label was renamed or
removed, and every pre-existing theorem, section and equation number is
unchanged (the Conclusion, which has no label, moved from Section 22 to
Section 27). The [formalization ledger](../../FORMALIZATION.md) indexed the
placed base under its unprefixed delivered labels (`lem:index`,
`thm:defect`, …); those labels are now `lce:lem:index`, `lce:thm:defect`,
and so on.

Delivered files under `code/` and `data/` and the five proof-status and
audit files are byte-identical to the delivery. Not shipped: the four
manuscripts' PDFs, the `.tex` and README of 06, 09 and 10, and 07's
delivered README (replaced by this one). `article.pdf` is a build of this
text.

## Three sources, one report

| | Archive (in `190d301`) | Manuscript | Contributes |
|---|---|---|---|
| **07** | `Surreal_Large_Cardinals_Research.zip` | *Critical-Point Defects in Surreal Arithmetic: Large-cardinal embeddings, exact support thresholds, surcomplex fields, and omnific integers* (32-page PDF) | The base text: every untagged section. Exact image intersection and projection isomorphism, positive-family threshold and escape theorem, mask algebra and mask criterion, omnific and surcomplex transfers, logarithmic defect, exponential locus and two closures, the supercompact seed, 12 questions, formalization plan, finite regression. |
| **06** | `Surreal_Large_Cardinals_Critical_Supports.zip` | *Critical Supports and Large Cardinals in Surreal Arithmetic: Ultrapower transport, Hahn lifts, and omnific descent* (27-page PDF) | Proof of the critical-point facts; descent of `H_j(x)` to `M`, landing spectrum, seed–closure lemma, cover obstruction and normal-measure trichotomy (Section 9); bounded and omnific measure codes; formal evaluation and the exponential scale corollary; support covers and exact descent (Section 17); the fixed class of `H_j`; 9 questions; audit checklist. |
| **09** | `surreal_large_cardinals_article.zip` | *Large Cardinals and the Support Geometry of Surreal Embeddings: Exact equalizers, additional normal-form terms, and omnific algebraic independence* (30-page PDF) | A second proof of the absoluteness lemma; the short-support field at every uncountable cardinal (Section 3); omnific monomial witnesses and the omega-map incompatibility; order continuity; almost-disjoint omnific independence and the `2^κ` family (Section 13); the compatible-field-embedding criterion; seed coefficients over arbitrary index sets; weak compactness as a prefix principle (Section 18); the visibility hierarchy; 13 questions. |

All three pin `0865f043aec113c14c69ef45006bbc7546a4e75a`, 55 commits before the
placement. Each archive was matched to its number by the `git hash-object` of
its proof status against the staged prefixed files.

**Why one report.** The three manuscripts study the same pair of maps and
prove the same spine independently: an elementary embedding `j : V → M` with
critical point `κ` gives `J` (apply `j` to sign sequences) and its strong
companion `H_j` (apply `J` to the exponents of the Conway normal form); the
difference `J(x) − H_j(x)` is the subseries of the transformed normal form
indexed by `j(θ) \ j″θ`; the equalizer is the field of surreals with fewer than
`κ` normal-form terms; and one coefficient recovers the derived normal measure.
07 is the base: on the shared theorems 06 and 07 have the weakest stated
hypotheses (09's headline assumes a normal-measure ultrapower, though its
arguments need no more) and 07 is the broader of the two. No contradiction
between the sources, and no false theorem, was found.

**Printed once**, with all proving sources named at the statement: the first
missing index, the absoluteness lemma, the induced embedding, the strong
companion, the defect formula and equalizer, the leading-term corollary, the
omega-map locus, the small-family threshold and first failure cardinal, the
derived normal measure, the distinguishing corollary, the zero-probe warning,
the character theorem, the omnific equalizer and constant terms, the
surcomplex transfer, the twisted product law, exponential transfer and the
exponential locus.

**Second routes**, marked in the text: 09's proof of the absoluteness lemma
(limit cylinders and truncation simplicity); 09's embedding-free real
closedness of the short field beside 07's proof through the embeddings; 06's
direct support counting; 09's fiber argument for weighted evaluation; 06's
formal-evaluation proposition for the infinitesimal factor.

**Kept separately** because they are different statements: the three measure
codes (07's `h_A`, 06's `h̃_A = h_κ + h_A`, 09's omnific `Y_A`) and their
omnific shifts; 07's mask criterion and 09's compatible-field-embedding
criterion; 07's supercompact seed coefficient, 06's exact-descent and cover
characterizations and 09's covering and exact seeds; the 34 questions.

**Marking.** `[06]`, `[07]`, `[09]`, `[10]` tag statements by source; `[merge]`
marks text written for the merge. 06's and 09's headline theorems are printed
in Section 1.3 with proof pointers. Section 1.5 has the sources table, the
hypotheses of each source, and the full renaming table for 06 and 09
(Section 22.4 has 10's); Appendix C lists every non-claim by source;
Appendix D records provenance and every merge decision, for 10 in its last
paragraph.

**Notation.** 07's symbols are kept. Renamed from the other sources (no
normalization changed):

- 09's `T`, `D` are `H_j`, `D_j`; 06's `K_{<κ}` and 09's `F_κ` are `𝒮_{<κ}`;
  06's `K_{≤κ}` is `𝒮_{≤κ}`; 09's `I_κ` is `𝓘_{<κ}`; 06's `sc(x)` is `|supp(x)|`;
  06's `ℓ_nf` and 09's `len_NF` are `len`.
- 06's detector `u_λ` and 09's `Q_θ` are 07's `h_λ`; 06's code `c_A` is
  `h̃_A = h_κ + h_A` and its `z_A` is `z̃_A`; 06's `v_λ = ω^λ u_λ` is
  `ζ_λ = ω^λ h_λ` (`v` is 07's valuation); 06's `x^↑` is `p(x)`; 06's binary
  series `Q`, `Q⁺` are `B̂`, `B̂⁺`; 06's `W_s` is `U_s`.
- 09's `e_α` and `q_α` (two names for `ω^{−α}`) are `q_α`; its `u_α = ω^{e_α}`
  is `τ_α`; its masks `Z_θ`, `Z_A`, `W_f`, `Z_{A,h}` are `Y_θ`, `Y_A`, `Y_f`,
  `Y_{A,e}`; its coefficient functional `c_γ` is `[ω^{q_γ}]`; its bijection `h`
  is `e`; its group `E` is `G_κ` and subspace `H` is `Ξ`; its polynomial `P` is
  `Φ`; its `χ(A)` is `χ_E(A)`; in the weak-compactness proof its strings `s`,
  tree `S`, injections `q_α`, lengths `D_α` are `σ`, `ℛ`, `ι_α`, `Δ_α`; its
  index `j` in `⋃_{j≠i} A_j` is `k`.
- Tempting false readings, excluded in the text: the equalizer is not a fixed
  field (`J(κ) = H_j(κ) = j(κ) ≠ κ`); short support is not a birthday bound;
  the Hadamard product `⊙` is not surreal multiplication; `ω^a` is Conway's
  omega-map, never `exp(a log ω)`; `z_A` and `Y_A` are different numbers; the
  landing spectrum `𝓛(j)` is not the logarithmic defect `L_j`.

## Source 10 (batch 32): measurable first failures

| | Archive (in `aa268a4`) | Manuscript | Pin | Contributes |
|---|---|---|---|---|
| **10** | `surreal_measurable_spectrum.zip` (batch 32, manuscript 05) | *Measurable Cardinals and the First Failure of Surreal Summation: Exact failure spectra, canonical strong parts, and omnific-preserving additive symmetries* (24-page PDF, with ChatGPT) | `7af8a30` | Sections 22–26: the first failure of a countably strong linear map is measurable; complete-ultrafilter localization (credited to Bergman); the canonical strong part; measurable transvections of `(No, +, <, Oz)`; the workspace criterion and the `2^κ` bound; the surcomplex transfer; the exact boundary for countably strong embeddings; the target test `ω^κ`; 12 questions; proof audit and review checklist; finite regression. |

**Placement.** Manuscript 10 arrived after the three-source merge. It is
printed as new Sections 22–26, after the questions (Section 21) and before the
Conclusion, so that no existing number changes; its conclusion is a `[10]`
paragraph of the Conclusion (now Section 27). Section 22.4 fixes its
conventions; its labels are `lce:mf:`; untagged text in Sections 22–26 is
10's, and `[merge]` marks text written for the merge. Its pin `7af8a30`
precedes the three-source merge (`de45cee`): 10 saw this report as 07's placed
text and cites its "Sections 2–4" (now Sections 2, 4 and 5), and it did not
see 06's and 09's questions that it answers.

**Renamed symbols** (Section 22.4 has the full table). 10 writes Hahn series
in `t` with `t^γ = ω^{−γ}` and well-ordered supports; everything is printed
here in this report's `ω`-exponents with reverse well-ordered supports, so
every exponent changes sign: 10's `[t^γ]x` is `[ω^{−γ}]x`, its detector
exponents `d − ω^{−α}` with `d ≤ −1` are `δ + q_α` with `δ = −d ≥ 1`, and its
correction monomial `a = t^d` is `ω^δ`. Further: 10's `L = k((t^Δ))` is
`K' = k((ω^{Γ'}))` (`L_j` is the logarithmic defect); `T`, `T_at`, `T_gh` are
`Ψ`, `Ψ_at`, `Ψ_gh`; a ghost map `G` is `Υ` (`G_κ` is 09's group); a field
embedding `F` is `E`; a derivation `D` is `∂` (`D_j` is the defect); `θ` in
"`<θ`-strong" is `ν` (`θ` is a normal-form length) and the least incomplete
partition `ν` of its Lemma 4.4 is `μ_𝒰`; ultrafilters `U`, `U_j` with index
`j` are `𝒰`, `𝒰_p` with index `p` (`U_j` is the derived measure); `ℓ_{S,η}` is
`ψ_{X,b}` (`ℓ_α` is 09's coordinate functional, `𝒮_{<κ}` the short field,
`η` an ordinal); the null ideal `𝓘_ℓ` is `𝒩_ψ` with cells `I_p`; `λ_U`, `N_U`,
`A_{c,U}` are `ϑ_𝒰`, `N_𝒰`, `Θ_{c,𝒰}`; its masks `F_B`, `F = F_κ` are
`ω^δ Y_A`, `ω^δ Y_κ` (09's omnific masks shifted; 09's `F_κ` is `𝒮_{<κ}`); its
`B = Σ_{α<κ} t^α` is 07's `h_κ`; its `Λ` is `Λ_j`; its parameter set `P` is `Z`
(`P_θ` is the missing-index set); `Π_k`, `𝔪_k` are `𝔓_K`, `𝔪_K` (`Π_j` is the
coefficient projection); `M_f` is `mul_y` (`M` is the target model).
Tempting false readings are excluded in Section 22.4: 10's detector `ϑ_𝒰`
reads its input and involves no embedding, whereas 07's `χ_j` reads an image
coefficient; `ω^δ Y_A`, `Y_A` and `z_A` are different numbers; masks are not
field idempotents; countably strong is not valuation continuity; fixing
every monomial is neither being the identity nor omega-map compatibility; an
additive automorphism is not a field automorphism.

**Printed once.** 10's Proposition 10.1 (the construction of `J`, its
`<κ`-strongness and first failure at `κ`, `Oz` reflection, `J_at = H_j`) is
Proposition 26.1 with pointers to Proposition 2.10, Theorems 11.1, 8.1, 7.1,
Corollary 8.3 and Theorem 4.3; 10 itself says it is not new. 10's group and
field of its Theorem 8.2 are exactly 09's `G_κ` and `K_κ` (Theorem 13.5). 10's
Lemma 3.1 is the elementary half of `opa:as:cor:countable`. 10's product law
for `F − F_at` specializes, for `J`, to 06's and 09's product law (14.3).

**Second routes.** `−κ ∉ J(No)` in Theorem 26.4 (10's elementarity argument,
and the defect theorem); the `U_j`-large fiber (10's bisection in Lemma
23.6, and 09's cardinality argument in Proposition 10.8).

**Merge additions** (`[merge]`). Remark 23.10: 07's and 09's character theorem
is the case of 10's representation theorem for `J`. The reflection clause
after Proposition 24.7 (10's proof also gives reflection of `Oz` for the
embedding itself, which 10 states only for the strong part). Remark 26.3: the
Kaplan–Krapp–Serra non-strong automorphism (their Example 4.4) fixes `ℝ` and
every monomial but fails a countable sum, so it is outside Theorem 24.1 and
shows that the countable hypothesis cannot be dropped; it does not preserve
`Oz`. Corollary 26.5: 09's measurability criterion (Theorem 10.10) holds for
an `ℝ`-linear `E` with its conditions (a), (b), (d) alone, no order,
multiplicativity, omega-map or Hadamard condition. Corollary 26.6: the same
for 07's mask criterion, trading the Hadamard homomorphism for small
point-finite sums. Proposition 26.7: partial answers for countably strong
maps. The note after Theorem 26.4 identifies `Λ_j` with the
`ω^{−κ}`-row of `D_j` and with 07's `χ_j` on masks, and records that the
negative answer to `opa:as:q:targettests` already followed from
`opa:as:thm:adjoint` and the non-strongness of `J`.

**Stale in the source.** Besides the pin, 10 claims a "concrete conditional
negative answer" to `opa:as:q:targettests`; that answer was already implied
at its pin (above), and 10's contribution there is the explicit test. No
false theorem was found; every proof was re-read in the converted
convention.

**Verification.** The suite `code/10-measurable-spectrum-finite_regression.py`
was rerun on a copy (below): 11,955 assertions in 18 categories, output
identical to the recorded files. It checks finite algebra only, in 10's
`t`-convention, with a principal functional.

## What the report claims

Numbers are those of `article.pdf`. Hypotheses: an elementary class embedding
`j : V → M` into a transitive class containing all ordinals, with critical
point `κ`, and class-parameter Separation and Replacement (a normal-measure
ultrapower is an instance); where stated, more.

- **Defect and equalizer (Theorem 5.1; 06, 07, 09).** For `x` of length `θ`,
  `D_j(x) = J(x) − H_j(x)` is exactly the subseries of `J(x)` indexed by
  `j(θ) \ j″θ`; its exponents lie outside `J(No)`; `D_j(x) = 0` iff
  `|supp x| < κ`; for `θ ≥ κ` the leading term sits at index `κ`.
  **Corollary 5.3** (09): the first `κ` terms agree. **Corollary 5.6,
  Theorem 5.7**: `H_j(ω^x) = ω^{H_j x}` iff `x ∈ 𝒮_{<κ}`, and no embedding with
  `J`'s monomial action is both omega-equivariant and `κ`-strong (09).
  **Proposition 5.5** (06): the fixed class of `H_j`.
- **The short field without an embedding (Section 3; 09, 06).** `𝒮_{<κ}` is real
  closed for every uncountable `κ`, regular or singular (Theorem 3.1); closed
  and nowhere dense and not definable in the ordered field (Proposition 3.5);
  `Oz ∩ 𝒮_{<κ}` is an integer part (Proposition 3.6); `𝒮_{≤κ}` is also a
  field (Corollary 3.2).
- **Image geometry (Theorems 6.1, 6.4, 7.1; 07).** Exact intersection
  `J(No) ∩ H_j(No) = J(𝒮_{<κ})`; coefficient projection is an isomorphism of
  the two incomparable immediate image fields; `J` and `H_j` are proper
  (Proposition 7.4, 06).
- **Summation (Theorems 8.1, 8.4, 8.6; 06, 07, 09).** `J` preserves strong
  sums of fewer than `κ` terms; for positive families exactly those; the
  omnific family `τ_α = ω^{ω^{−α}}` also fails at `κ` (09); positive strong sums
  of `≥ κ` image elements escape `J(No)` (07). Both maps are order-continuous
  (Proposition 8.5, 09).
- **Descent (Section 9; 06).** `H_j(x) ∈ No^M` iff `j″λ ∈ M`, `λ` the length of
  `x` (Theorem 9.1), independent of coefficients; in a set-ultrapower iff
  `M` is closed under `λ`-sequences (Lemma 9.3, Corollary 9.4); for a
  normal-measure ultrapower iff `|supp x| ≤ κ` (Theorem 9.7), giving the
  trichotomy `< κ` (equal, lands), `= κ` (unequal, lands), `> κ` (unequal, does
  not land), with no GCH. The counting also works for any ultrapower on an
  index set of size `κ`.
- **Measures (Section 10).** One coefficient of `D_j(h_A)` is `1` iff
  `A ∈ U_j` (Theorem 10.1; 06, 07, 09), also with 06's bounded code and a
  standard-part reading (Theorem 10.2) and 09's omnific code (Theorem 10.3);
  distinct normal measures give distinct functionals (Corollaries 10.4,
  10.5). Evaluation is a character of the Hadamard mask algebra (Theorem
  10.7, Proposition 10.8). Measurability is equivalent to a small-union
  character of the mask algebra (Theorem 10.9, 07) and to an ordered field
  embedding of `No` compatible with `⊙` on masks, small strong sums and the
  omega-map (Theorem 10.10, 09). Both criteria keep the coefficient algebra.
- **Omnific and surcomplex (Sections 11, 12).** Preservation and reflection of
  `Oz`, equalizer, intersection, fractions and constant terms (Theorem 11.1);
  purely infinite measure codes (Theorem 11.2, Corollary 11.3); all three
  support regimes occur in `Oz` (Theorem 11.4, 06); transfer to `No(i)` and
  `Oz[i]` (Theorem 12.1) with descent (Theorem 12.3, 06).
- **`Oz`-reflecting, not strong (Remark 11.6, merge).** Given a measurable
  cardinal, `J` is a field embedding of `No` with `J^{−1}(Oz) = Oz` that fixes
  `R`, preserves `ct`, and is not strongly additive; it is not onto. This
  answers the first two clauses of `opa:as:q:embeddingstrong` negatively under
  that hypothesis, as the omnific-preserving-automorphisms report records.
- **Independence without large cardinals (Section 13; 09).** For uncountable
  `κ` and a `κ`-almost-disjoint family, the omnific masks `Y_A` are
  algebraically independent over all of `𝒮_{<κ}` (Theorem 13.3); if
  `2^{<κ} = κ`, one set-sized Hahn field holds `2^κ` of them and
  `trdeg = 2^κ` (Theorem 13.5); also over `𝒮_{<κ}(i)`, and at a measurable
  `κ` all lie outside the equalizer (Corollary 13.6).
- **Logarithm and exponential (Sections 14, 15; 07, 06).** Twisted product law
  (Proposition 14.2); logarithmic defect homomorphism with kernel
  `𝒮_{<κ}^×` (Theorem 14.3); `H_j(exp x)/exp(H_j x) = exp(D_j(p(x)))`, so
  compatibility holds iff the purely infinite part has fewer than `κ` terms
  (Theorem 15.3), and the ratio is `1`, infinitesimal or infinite (Corollary
  15.4); the two closures of the common field (Theorem 15.7).
- **Seeds and compactness (Sections 16–18).** Seed coefficients over any index
  set (Theorem 16.1, 09); the supercompact seed as a missing-index defect
  coefficient (Theorem 16.2, 07); covering and exact seeds (Proposition 16.3,
  09); strong compactness as an internally short binary cover and
  supercompactness as descent of one number, also in `Oz` (Lemma 17.1,
  Theorems 17.2, 17.3, Corollary 17.4, 06); weak compactness at an
  inaccessible as an omnific prefix principle (Theorem 18.2, 09). These are
  credited translations of classical characterizations.
- **Absoluteness (Lemma 2.6; 06, 07, 09)** for transitive inner classes with
  the same ordinals and reals, including normal forms and the omega map; its
  consequence for the definable-surreals report is Remark 2.9 (below).
- **Measurable first failures (Sections 22–26; 10).** Summability of a
  set-indexed family is detected by its countable subfamilies (Lemma 23.3), so
  a countably strong map preserves admissibility (Corollary 23.4). A linear
  functional on `k^I` (`k = ℝ, ℂ`) preserving point-finite sums of fewer than
  `ν` vectors is a unique finite combination of `ν`-complete ultrafilter
  evaluations (Theorem 23.7, Bergman's mechanism, credited); a nonprincipal
  countably complete ultrafilter yields a measurable cardinal (Lemma 23.9).
  **Theorem 24.1:** the first failure of a countably strong coefficient-linear
  map between full real or complex Hahn fields (set-sized or `No`) is a
  measurable cardinal; without measurables countable strongness implies
  strongness (Corollary 24.2); failures at successor or singular cardinals
  are never first (Corollary 24.3). **Theorem 24.4:** every such map is its
  canonical strong part (determined by the monomial images) plus a countably
  strong ghost vanishing on monomials and on short supports; for `J` these
  are `H_j` and `D_j`; the strong part of a field embedding or derivation is
  one (Theorem 24.6), and preserves and reflects `Oz` (Proposition 24.7).
  **Theorem 25.2:** a measure `𝒰` on `κ` gives `Θ_{c,𝒰} = id + c ω^δ ϑ_𝒰`,
  an `ℝ`-linear additive automorphism of `No` preserving order, leading
  terms, constant terms and `Oz`, fixing every monomial, with first failure
  exactly `κ`, not multiplicative; it recovers `𝒰` (Corollary 25.3) and can
  fix any set of parameters (Theorem 25.4); hence multiplication is not
  definable in `(No, +, <, Oz)` with those parameters (Corollary 25.5). For
  a set-sized `Γ`, countable tests suffice iff `Γ` has no reverse
  well-ordered subset of measurable size (Theorem 25.6); the least full real
  Hahn field with first failure `κ` has size `2^κ`, attained by 09's
  `K_κ` (Theorem 25.7); surcomplex transfer (Theorem 25.8). **Theorem
  26.2:** no measurable cardinals iff every countably strong `ℝ`-linear map
  of `No` is strong, iff the same for `Oz`-stabilizing monomial-fixing
  additive automorphisms, iff the same for coefficient-fixing `Oz`-preserving
  field embeddings (with a `<ν` version). **Theorem 26.4:** given a
  measurable, the target test `ω^κ` for `J` has no source multiplier
  representative (`opa:as:q:targettests`, conditional). Merge deductions:
  Corollaries 26.5, 26.6 and Proposition 26.7 (above).
- **Questions.** 46: 07's twelve (21.1–21.12), 06's nine (21.13–21.21), 09's
  thirteen (21.22–21.34), 10's twelve (26.8–26.19). The exponential half of
  Question 21.30 (09) is answered by Theorem 15.3. Batch 32 status notes:
  Question 21.22 (09's "removing coefficientwise multiplication") is answered
  for the criterion by Corollary 26.5 (whether condition (c) of Theorem 10.10
  follows from the others is not decided); Question 21.13 (06's intrinsic
  converse) is partly answered (the ultrafilter is constructed from a null
  ideal, with summation as the only extra structure; pairs `(J, H_j)` are not
  characterized); Questions 21.1, 21.2 and 21.23 get partial progress for
  countably strong maps (Proposition 26.7). Overlaps are cross-referenced.

## What the report does not claim

Appendix C lists every non-claim with its place: 21 from 07, 15 from 06, 16
from 09, and 7 added by the merge (M.7 for batch 32); 10's 19 non-claims and
3 merge items are in Section 26.6 (10.1–10.19, M10.1–M10.3), summarized in
Appendix C. In brief:

- Not refereed, not Lean-verified, no Lean mapping; AI-assisted drafts;
  priority is proposed, not certified; the literature and repository checks
  were targeted; no named published conjecture is claimed solved.
- No existence or consistency of any large cardinal, no new consistency
  result, no nontrivial `V → V`; the compactness statements are translations
  of classical principles; no large cardinal may be inferred from an
  arbitrary non-strong field map.
- The maps are proper embeddings, not automorphisms; the Kaplan–Krapp–Serra
  questions are not answered; no Kunen exception.
- The mask and embedding criteria use a coefficient operation and all subset
  masks; neither is first-order in the bare field or omnific ring; pure field
  sentences cannot detect large cardinals.
- The seed–closure converse is for set-ultrapowers; the no-descent result
  above `κ` needs an index set of size `κ`; `j(κ)` is inaccessible in `M`, not
  asserted in `V`; `H_j(No) ⊄ No^M` and `J(No) ≠ No^M` are not identifications
  (both fail for a normal-measure ultrapower).
- Transcendence, not linear disjointness, between the image fields; the
  independence theorem is over the domain equalizer and does not decide
  Question 21.6.
- The finite checks test finite identities only.
- Merge: Remark 2.9 covers inner models with the same reals only and leaves
  `dsn:q:support` open; Remark 11.6 is conditional on a measurable cardinal and
  leaves open whether a counterexample exists without large cardinals (batch
  32: one fixing `ℝ` would have to fail a countable sum), and the clauses on
  dense images.
- Source 10: the countable hypothesis is essential; nothing is claimed for
  maps or embeddings that fail a countable sum (Question 26.8), for
  unrestricted Gaussian ring automorphisms (`opa:as:q:gaussian`), or for
  target tests of strong embeddings; full Hahn fields only, no classification
  of support-restricted subfields; no global assembly of the local ultrafilter
  data; the transvections are additive, not multiplicative, and do not
  respect the omega-map as a function, the exponential or the
  Berarducci–Mantova derivation, and are only locally translations; no
  claim that a set-sized `𝒪_Γ` has the full Hahn field as fraction field;
  Bergman's mechanism is classical; no existence or consistency of
  measurable cardinals; Section 26 depends on this report's absoluteness
  lemma (Sections 23–25 do not); the finite checks simulate no ultrafilter;
  the scalar sums are finite; Corollary 25.5 concerns the additive reduct
  only; no contradiction with automatic strongness of `Oz` field
  automorphisms; unrefereed, no Lean, priority not certified. Merge items:
  Corollaries 26.5, 26.6 and Proposition 26.7 are merge deductions, not 10's
  statements, and cover countably strong maps only; the Kaplan–Krapp–Serra
  comparison is a reading of their example, not a theorem.
- The sentences "we do not establish that arbitrary non-strong surreal
  embeddings require a measurable cardinal" (Section 1.4) and "one should not
  infer a large cardinal from an arbitrary non-strong field map" (Section
  19.7) stay true for arbitrary maps and carry batch-32 re-scoping notes.

## Relation to the neighbouring reports

Section 20.3 gives these with labels.

- [`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/)
  (`dsn:`). Its question `dsn:q:support` recorded the inner-model instance of
  support-subfield amplification as unproved: the universes report proves
  absoluteness of arithmetic and cuts only. Lemma 2.6 here supplies omega-map
  and normal-form absoluteness for inner models with the same ordinals and
  reals, so a proper such `No^M` satisfies `dsn:eq:Khyp` and
  `dsn:thm:amplify` applies (Remark 2.9). That report now carries the
  reciprocal `dsn:rem:largecardinal` (its Remark 17.6). Inner models lacking a
  real are not covered, and the classification question stays open.
- [`omnific-preserving-automorphisms`](../../surreal/omnific-preserving-automorphisms/)
  (`opa:`). Written concurrently in batch 30, it cites this report by directory
  (writing `J` as `ĵ`) for a negative answer, given a measurable cardinal, to
  the strongness question `opa:as:q:embeddingstrong`; Remark 11.6 states and
  proves exactly the properties it uses (field embedding fixing `R`,
  preserving and reflecting `Oz`, preserving `ct`, not strongly additive, not
  onto), consistent with its automorphism theorem `opa:as:thm:main`. Batch 32
  (source 10): without measurable cardinals a coefficient-fixing
  counterexample to `opa:as:q:embeddingstrong` must fail a countable sum
  (Theorem 26.2); Theorem 26.4 gives the explicit unrepresentable target test
  `ω^κ` for `opa:as:q:targettests`, whose conditional negative answer already
  followed from `opa:as:thm:adjoint` and the non-strongness of `J`;
  `opa:as:q:gaussian` is untouched. No reciprocal note has been added to that
  report yet. The Kaplan–Krapp–Serra automorphism cited in `opa:as:rem:main`
  fails a countable sum (Remark 26.3), so it is consistent with Theorem 24.1.
- [`first-kappa-coefficients`](../../surcomplex/first-kappa-coefficients/)
  (`fkc:`; written concurrently in batch 32, now cited by label). Its Hahn
  fields of series with fewer than `κ` terms are, over all surreal monomials,
  the short field `𝒮_{<κ}` here; a `<κ`-strong linear map agrees with its
  canonical strong part on that field (Theorem 24.4). Its Part II proves for
  `𝒮_{<κ}`, at every uncountable κ and without large cardinals: closedness
  and nowhere density for valuation neighbourhoods (`fkc:sb:prop:closed`),
  gap character `(cf κ, cf κ)` (`fkc:sb:thm:gapcharacter`), saturation
  exactly up to `cf κ` (`fkc:sb:cor:saturation`), the strong-sum threshold
  `cf κ` (`fkc:sb:thm:sums`), exponential without logarithmic closure with
  the same witness `z_κ` (`fkc:sb:thm:expclosure`, `fkc:sb:cor:expsep`), and
  the absence of any surjective ordered exponential (`fkc:sb:thm:noexp`).
  Notes after Proposition 3.5 and Corollary 15.5 record these; `C_j` is not
  treated there.
- [`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
  (`hset:`). Its embedding correspondence (`hset:thm:embeddings`) acts on sign
  sequences as `J` does, with the same warning that `j(A)` is not `j″A`; its
  Kunen transfer (`hset:thm:kunen`) is the birthday-enriched side of Section
  19. Neither is used in the proofs.
- [`surreal-fields-across-universes`](../surreal-fields-across-universes/)
  (`univ:`). `univ:prop:absolute` is the arithmetic part of Lemma 2.6; its
  forcing themes are Questions 21.11 and 21.20. None of its questions is
  answered.
- [`transcendence-over-bounded-support`](../../surreal/transcendence-over-bounded-support/)
  (`bst:`). Order-bounded supports there, cardinality-bounded here (09's own
  comparison); neither result implies the other. Its batch-32 question
  `bst:gr:q:cardinal` asks for its Galois constructions in fields with fewer
  than κ terms; Theorem 3.1 supplies the real closed field `𝒮_{<κ}` at every
  uncountable κ, but the question is not answered.
- [`set-sized-quotients-of-omnific-integers`](../../surreal/set-sized-quotients-of-omnific-integers/)
  (`osq:`). The constant-term discussion is kept apart from its quotients.
- [`independent-surreal-copies`](../../surreal/independent-surreal-copies/)
  (`isc:`; written concurrently in batch 31, `781b19e`; now cited by label).
  It identifies `H_j` as its strong exponent lift (`isc:thm:lift`) and relates
  its linear-disjointness theorem for full Hahn fields
  (`isc:thm:sliceddisjoint`) to Question 21.6 without answering it: the note
  added after Question 21.6 (batch 31) records that `H_j(No)` is the full
  Hahn field on the subgroup `J(No)`, while neither `J(No)` (Theorem 8.6) nor
  `C_j` is a full Hahn field. Question 21.6 stays open.

The sources' repository statements were checked at the placement and at the
time of writing: the reports they cite are unchanged since the pin except the
set-sized-quotients report (07 cites only its catalogue entry), and the
statements stand (Section 20.3).

## Provenance and corrections

Appendix D records these.

- 06's proof status records `0865f043…` as a "tree object", not asserted to be
  a commit. It is a commit ("Merge reviewed documentation after angular
  multiplicity validation").
- 07 cited Gonshor's book as Lecture Note Series 124; 06 and 09 give 110, which
  is correct. The bibliography now says 110.
- 06 links the universes and birthday reports on `main`, 07 and 09 at the pin;
  the merged bibliography keeps 07's entries.
- 06 says its short-field counting uses "regularity and uncountability"; only
  uncountability is needed (note after Corollary 3.2). Not a false statement.
- Source 10 (batch 32): its pin `7af8a30` precedes the three-source merge, so it
  cites this report as 07's text; its target-test "negative answer" was
  already implied at the pin; it states `Oz` reflection only for the strong
  part, although its proof covers the embedding too. Its bibliography's
  Bergman paper (JSL 2014, arXiv 1301.6383) is not 07's Bergman entry (arXiv
  1406.1932); both are cited. Its `RepoCrit` is this report and is replaced by
  internal references. In the Kaplan–Krapp–Serra example it cites, the
  displayed family `Σ_n ω^{−1/n}` has increasing exponents and is not a Conway
  normal form as printed (a sign slip such as `Σ_n ω^{1/n}` appears meant);
  the failing family is countable in any reading (Remark 26.3).

**Delivered files that use delivery names or numbering.** All shipped as
delivered:

- The three proof-status files number results as in their own manuscripts.
  Main correspondences to this report: 07's Lemma 2.3/2.4, Theorems 3.3, 4.1,
  5.1, 5.4, 6.1, 7.1, 7.4, 8.1, 8.4–8.5, 9.1–9.2, 10.1, 11.3, 12.2, 12.5, 13.1
  and Section 16 are Lemma 2.5/2.6, Theorems 4.3, 5.1, 6.1, 6.4, 7.1, 8.1, 8.6,
  10.1, 10.7, 10.9, 11.1–11.2, 12.1, 14.3, 15.3, 15.7, 16.2 and Questions
  21.1–21.12. 06's Lemma 2.3 and 5.3, Theorems 3.3, 3.5, 4.2, 4.6, 5.1, 6.3,
  7.1, 8.2–8.3, 9.1–9.2 are Lemma 2.6 and 9.3, Theorems 5.1, 8.1, 5.1, 15.3,
  9.1, 9.7, 10.2, 17.2–17.3, 12.1/12.3 and 11.4. 09's Lemma 2.2 and Theorems
  4.4, 5.1, 5.2, 6.1, 7.3, 7.5, 8.1, 8.4, 9.1, 10.2, Proposition 9.2 and
  Section 12 are Lemma 2.6 (second route), Theorem 5.1, Theorems 8.1/8.4,
  Corollary 5.6 with Theorem 5.7, Theorems 11.1/12.1, 13.3, 13.5, 10.1/10.3,
  10.10, 16.1, 18.2, Proposition 16.3 and Questions 21.22–21.34. 09's proof status writes `T`, `F_κ`; 06's writes the
  snapshot as a tree object (above).
- 07's proof status names `code/finite_regression.py` and its seed; 07's text
  (Appendix B) and delivered README named the delivery layout; the shipped
  paths are prefixed.
- The three build helpers assume the original flat package layout. Each `cd`s
  to its own directory (`code/`) and looks for its manuscript
  (`article.tex`, `critical_point_defects.tex`, `surreal_large_cardinals.tex`),
  which is not there; 07's also runs `code/finite_regression.py` relative to
  `code/`. None builds this report.
- `data/07-critical-point-defects-build_validation.json` describes 07's
  delivered 32-page PDF (120 labels, no warnings), not `article.pdf` here.
- The recorded results JSON and console text are byte-identical: the program
  prints the JSON it writes.
- Run without arguments, the finite regression writes
  `data/finite_regression_results.json`, a delivery name next to the shipped
  prefixed file; run it on a copy with `--output` (below).
- Source 10's proof status and source audit number results as in its own
  manuscript and write `t^g = ω^{−g}`, `T`, `F`, `λ_U`, `A_{c,U}`, `B`, `S_d`.
  Correspondence: its Theorem 1.1, Definitions 2.1–2.2, Lemma 3.1, Corollary
  3.2, Lemma 3.3, Lemma 4.1, Theorem 4.2, Remark 4.3, Lemma 4.4, Theorem 5.1,
  Corollaries 5.2–5.3, Theorem 6.1, Proposition 6.2, Theorem 6.3, Proposition
  6.4, Lemma 7.1, Theorem 7.2, Corollary 7.3, Theorem 7.4, Corollary 7.5,
  Theorems 8.1, 8.2, 9.1, Proposition 10.1, Theorem 10.2, Remark 10.3,
  Theorem 10.4, Section 11, Questions 12.1–12.12 and Appendices A–B are here
  Theorem 22.1, Definitions 23.1–23.2, Lemma 23.3, Corollary 23.4, Lemma
  23.5, Lemma 23.6, Theorem 23.7, Remark 23.8, Lemma 23.9, Theorem 24.1,
  Corollaries 24.2–24.3, Theorem 24.4, Proposition 24.5, Theorem 24.6,
  Proposition 24.7, Lemma 25.1, Theorem 25.2, Corollary 25.3, Theorem 25.4,
  Corollary 25.5, Theorems 25.6, 25.7, 25.8, Proposition 26.1, Theorem 26.2,
  Remark 26.3, Theorem 26.4, Section 26.4, Questions 26.8–26.19, and the
  checklist in Section 26.4 with the table of Section 22.4.
- Source 10's `build.sh` assumes its flat package. Do not run it here: it
  `cd`s to its own directory (`code/`), creates `code/data/`, pipes
  `python3 code/finite_regression.py` (a path that does not exist from
  `code/`) into `tee`, which without `pipefail` still writes an empty
  `code/data/finite_regression_console.txt`, and then fails at `latexmk` on an
  `article.tex` that is not in `code/`. It does not build this report. Its
  finite regression always writes `<script dir>/../data/finite_regression_results.json`,
  a delivery name next to the shipped prefixed file; it has no output option,
  so run it on a copy (below). `data/10-measurable-spectrum-build_validation.json`
  and `data/10-measurable-spectrum-compile_console.txt` describe 10's delivered
  24-page PDF, not `article.pdf` here.

## Build and reproduce

TeX Live or MiKTeX with newtxtext/newtxmath, amsmath/amsthm, mathtools,
geometry, microtype, booktabs, array, longtable, enumitem, xurl, xcolor,
fancyhdr, needspace, tcolorbox and hyperref. No external figures or
bibliography file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch directory; the auxiliary files are not kept here. The
recorded build (MiKTeX, batch 32) has 109 pages and no errors, undefined
references or citations, multiply defined labels, duplicate destinations,
LaTeX or package warnings, or overfull boxes. It has seven underfull-box
notices, all inside 07's two delivered tables (the literature table of
Section 20 and the Lean interface table of Appendix A), identical to a build
of the committed text before batch 32; all 254 pre-existing labels keep their
numbers in the `.aux` file. A clean compile proves nothing about the proofs.

The finite regression needs Python 3.10 or later and no packages. Run it on a
copy, from this directory:

```sh
T=$(mktemp -d)
cp code/07-critical-point-defects-finite_regression.py "$T"/
(cd "$T" && python 07-critical-point-defects-finite_regression.py --output rerun.json > console.txt)
diff <(tr -d '\r' < "$T/rerun.json") data/07-critical-point-defects-finite_regression_results.json
```

This was run for this report under Python 3.14.4 on Windows: exit code 0,
`"status": "PASS"`, and both the written JSON and the console output agree
with the recorded files except for line endings (CRLF on Windows). The seed is
20260923. The checks are 500 finite exponent-reindexing cases (three identities
each, leading terms for the 432 nonzero inputs), 251 index-deletion and shift
cases, 500 cases of the difference-of-homomorphisms product identity, all
16,384 candidate maps on the four-point Boolean algebra (exactly its 4
principal characters), and one Hadamard-versus-convolution distinction. They
model no elementary embedding, measurability, class recursion, normal-form
absoluteness, transfinite summation or supercompactness. 06 and 09 ship no
programs.

Source 10's finite regression (Python 3.10 or later, standard library only)
always writes `finite_regression_results.json` into `../data/` relative to
the script and has no output option, so run it on a copy laid out as
`code/` and `data/`:

```sh
T=$(mktemp -d); mkdir -p "$T/code"
cp code/10-measurable-spectrum-finite_regression.py "$T/code/finite_regression.py"
(cd "$T" && python code/finite_regression.py > console.txt)
diff <(tr -d '\r' < "$T/data/finite_regression_results.json") data/10-measurable-spectrum-finite_regression_results.json
diff <(tr -d '\r' < "$T/console.txt") data/10-measurable-spectrum-finite_regression_console.txt
```

This was run for batch 32 under Python 3.14.4 on Windows: exit code 0,
`PASS: 11955 exact finite assertions across 18 categories`, seed 20260923,
600 random cases; the written JSON and the console output are identical to
the recorded files after line-ending normalization. The checks are finite
rational models in 10's `t`-convention: nilpotence, group law, inverse,
additivity, scalar linearity, leading term, order on differences, constant
term, omnific-type preservation and its inverse, a finite sum identity, the
coordinate matrix, weighted-coordinate additivity and scaling, and the
nonmultiplicativity formulas. The finite functional is a principal
coefficient projection that does not vanish on every monomial; no
ultrafilter, measurable cardinal, transfinite sum or proof is verified.
