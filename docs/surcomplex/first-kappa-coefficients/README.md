# The First-κ Coefficients

**Omitted types, singular compression, and completion in surreal and
surcomplex Hahn fields, and the support-bounded surreal fields**
Two-source research report. Part I (22 September 2026) is built from one
manuscript (item 04 of batch 22, archive `surreal_first_kappa_types`) whose
repository comparison is pinned at `465a54b`; Part II (23 September 2026) is
built from a second manuscript (manuscript 04 of batch 32, archive
`support_bounded_surreal_fields`) pinned at `343dc2c`. Both are AI-assisted
drafts, not refereed and not formalized in Lean.

```
article.tex                                    the report, standalone LaTeX with an internal bibliography
article.pdf                                    the compiled report, 53 pages
README.md                                      this guide
research_audit.md                              source 01's research audit, as delivered (see below)
02-support-bounded-fields-SOURCE_AUDIT.md      source 02's source and proof audit, as delivered
code/
  verify.py                                    source 01's exact finite checks (Python 3.10+, standard library)
  build.sh                                     source 01's build script, written for a flat layout
  02-support-bounded-fields-verify.py          source 02's exact finite checks (Python 3, standard library)
  02-support-bounded-fields-build.sh           source 02's build script, written for a flat layout
data/
  verification.json                            recorded run of code/verify.py (9,622 assertions)
  build_audit.json                             build and layout record of source 01's delivered 21-page PDF
  02-support-bounded-fields-verification.json  recorded run of source 02's checks (31,672 checks)
  02-support-bounded-fields-BUILD_REPORT.json  build record of source 02's delivered 25-page PDF
```

Every label in `article.tex` carries the prefix `fkc:` (170 labels). The 77
labels of Part I (source 01's 72 and 5 added at assembly) are all kept, and
no number of Part I changed; the 93 labels added in batch 32 carry the
sub-prefix `fkc:sb:` (two part headings and Part II). The
[Lean ledger](../../FORMALIZATION.md) indexes the Part I statements under
`first-kappa-coefficients` as **Pending**; no `fkc:` label is mapped to a
Lean declaration, and the `fkc:sb:` labels are not yet indexed.

## Sources

| Source | Manuscript | Pin | Contributes |
|---|---|---|---|
| 01 | *The First-κ Coefficients: Omitted Types, Singular Compression, and Completion in Surreal and Surcomplex Hahn Fields* (21 pp.; batch 22, item 04; placed `7b5f934`, written `68e2960`) | `465a54b` | Part I, Sections 1–12 and Appendix A: set-sized fields `K_{κ,k} ⊆ k((t^Γ))` with fewer than κ terms; types, omission numbers, empty nests, completion, retractions |
| 02 | *Support-Bounded Surreal Fields: Sharp saturation and spherical thresholds, an exponential obstruction, and indistinguishable omnific quotients* (25 pp.; batch 32, manuscript 04; delivered `aa268a4`, placed `7d04483`) | `343dc2c` | Part II, Sections 13–26 and Appendices B–C: the class version with every Conway monomial; gaps, saturation, strong sums, nests, topology in `No`, exponential, omnific integer part, real forms |

## Source 01 (Part I)

One manuscript, dated 22 September 2026 (21 pages). When assembled the
report was **not a merge**: no other manuscript proves its results, and the
nearest material in the collection is cross-referenced, not merged. The
statements, proofs, limitations and priority caveats are the manuscript's.
The raw files were placed in commit `7b5f934`; the report was assembled in
commit `68e2960`. The editorial changes during assembly (Section 1.4 of the
article) were:

- **Labels** received the prefix `fkc:`. No statement, section or equation
  of the manuscript was renumbered; the added remarks and subsections come
  after the last numbered item of their sections.
- **Added:** Section 1.4 (provenance, notation conventions, neighbouring
  reports); Remark 7.6 (the countable analogues in other reports);
  Remark 9.6 (the groups `Γ_θ` elsewhere); a sentence after the rank-one
  boundary case (Section 9); Section 11.5 (corrections to the manuscript's
  repository statements); Section 11.6 (the collected non-claims N1–N12);
  seven bibliography entries for collection reports; a closing paragraph of
  the abstract; the file paths of Appendix A.
- **Cross-references.** All theorem-like environments share one counter, and
  in the delivered build every `\cref` to a proposition, lemma, corollary or
  example printed "theorem", and the appendix printed "section". The preamble
  now declares the names; no statement changed.
- `code/verify.py`, `code/build.sh`, `data/verification.json`,
  `data/build_audit.json` and `research_audit.md` are byte-identical to the
  delivery. The delivered member README and PDF are not shipped; no checksum
  manifest was delivered. `data/build_audit.json` records the delivered PDF's
  page count (21) and SHA-256, which was checked on placement; it does not
  describe this report's PDF.
- The earlier raw placement chose the family `surcomplex/` over `surreal/`
  because the results are stated uniformly for real and complex coefficients.

`research_audit.md` is verbatim and describes the repository at the pin. Its
"44 reports", its negative search for "spherical" and its comparison with the
Hahn-vector-space report are corrected in Section 11.5 (below); its file names
`verify.py`, `verification.json`, `build.sh` and `build_audit.json` refer to
the delivery's flat layout.

## Source 02 (Part II, batch 32)

| | |
|---|---|
| Manuscript | batch 32, manuscript 04; local number 02 (prefix `02-support-bounded-fields-`) |
| Archive | `support_bounded_surreal_fields` (delivered in `aa268a4`, placed in `7d04483`) |
| Title | *Support-Bounded Surreal Fields: Sharp saturation and spherical thresholds, an exponential obstruction, and indistinguishable omnific quotients*, 23 September 2026, 25 pages, "Research manuscript prepared for Vladimir Reshetnikov" |
| Pin | `343dc2c471212bb9b53ff4623bace2e1943f255b` |
| Contributes | the class version of Part I for `K_{κ,ℝ}(No) = {x ∈ No : |supp_ω x| < κ}`, every uncountable κ, regular or singular (Theorems 13.1, 13.2) |

**Placement.** Part II (Sections 13–26) follows Part I's conclusion
(Section 12), and source 02's two appendices follow Appendix A as Appendices
B and C, so that no theorem, section or equation number of Part I changed
(checked against the `.aux` of a build of the committed text: 77 of 77
unchanged). A `\part` heading was added before Section 1 and before
Section 13. Section 13 is written for the merge: provenance, the main
results, a relation table (Part II result, Part I counterpart, other
reports) and the notation conventions.

**Renamed symbols (Section 13.4).** Source 02's `F_κ` collides with Part I's
full Hahn field `F_k`, so the class field is written in Part I's notation:

| Source 02 | Here | Why |
|---|---|---|
| `F_κ`, `F_λ` | `K_{κ,ℝ}(No)`, `K_{λ,ℝ}(No)` | Part I's `F_k` is the full Hahn field and `K_{κ,k}` the bounded one; = large-cardinal report's `𝒮_{<κ}` |
| `C_κ` | `K_{κ,ℂ}(No)` | class version of `K_{κ,ℂ}`; not large-cardinal's `C_j` |
| `O_κ` | `Oz_{<κ}` | = large-cardinal's `𝓘_{<κ}`, quotient report's `𝒜^{<κ}_{ℤ,ℝ}` |
| `J_κ` | `Π_{<κ}` | large-cardinal's `J` is an embedding lift |
| `G_κ` | `Oz_{<κ}[i]` | no new letter |
| `supp` | `supp_ω` | Part I's `supp ⊆ Γ` is increasing |
| `s_κ`, `s_β` | `h_κ`, `h_β` | Part I's `s_α` are support exponents; large-cardinal's `h_κ` is the same series |
| `p_κ` | `z_κ` | Part I's `p` is a type; large-cardinal's `z_κ` (its `p_κ` is different) |
| prefix `p`, `t_β` | `T`, `T↾β` | Part I's `p` type, `t` Hahn variable; `T_κ(y) = y↾κ` |
| `L = ℝ((ω^H))` | `ℝ((ω^H))` | Part I's `L_{κ,k}` is the completion |
| `(L,R)`, `L_y`, `R_y` | `(𝓛,𝓡)`, `𝓛_y`, `𝓡_y` | gap sides |
| `E`, `E_2` (exponential); `E` (reservoir) | `𝓔`, `𝓔_2`; `W` | Part I's `E_x = K + Kx` |
| `h = g⁻¹`; tail `h`; `h_α`, `h ∈ H` | `g⁻¹`; `w`; `d_α`, `u ∈ H` | `h_κ` is now the series |
| `τ` (cardinal) | `ρ` | `τ_κ` are the involutions |
| `φ`, `φ̄`; `φ_κ` | `χ`, `χ̄`; `ψ_κ` | Part I's `φ`, `Φ` are formulas |
| `c_κ`, `c` | `conj_κ`, `conj` | in Part I `c_κ` is the κ-th coefficient |
| `j_κ` | `τ_κ` | Part I's `j : Γ → No`; large-cardinal's elementary embedding `j` |
| `S` (Lemma 4.1); `D` (proof of 4.4) | `Σ`; `D'` | `S` kept for the target ring; Part I's `D_x` |
| exponent variable `g` | `e` | `g` reserved for Gonshor's bijection |

No normalization changed. The article also prints the tempting false
readings: `K_{κ,ℝ}(No)` is not `ι_j(K_{κ,ℝ})` for any set Γ; the gap
character `(μ,μ)` and the omission number μ are equal cardinals of different
objects; Part II's saturation does not contradict Part I's non-claim N5;
"complete" in Theorem 7.4 is intrinsic to a set workspace; a strong sum is
not a limit.

**Printed once.** Where source 02 re-derives Part I in substance, the
argument appears once with both sources credited: Lemma 15.1 (small exponent
field = Lemma 2.1 with Proposition 2.2 at Γ = H), Lemma 18.3 (ambient gluing
= the first two paragraphs of Lemma 6.1) and Theorem 18.4 (empty-nest
threshold = Theorem 6.2 in the class; its nest `B(h_{β_ξ}, β_ξ)` is Part I's
canonical nest for the missing element `h_κ`). Everything else of source 02
(every result, proof, example, question and non-claim, and its status
paragraph, introduction, tables and appendices) is printed in full.

**Merge additions** (marked `[merge]`): Section 13; the prefix sentence of
Section 14.2; comparison notes after Lemma 14.1, Theorems 15.2, 16.3, 16.4,
18.2, 18.4, 20.1, 20.8, Corollaries 17.2, 20.7, Propositions 19.1, 19.2,
21.1, 22.2, 22.5, Lemma 22.1, Example 23.3, and in Remarks 15.4, 18.5, the
paradox paragraph of Section 19, Section 21.3, Section 25.1 and Appendix B;
the "printed once" proofs of Lemmas 15.1 and 18.3; Remark 21.4 (the quotient theorem was in the collection; a third
route); Remark 22.4 (credits to the automorphism report, the answer to one
clause of `univ:q:families`, and the relation to batch 32's valued
involutions); notes after the eight questions; Section 25.5 (corrections to
source 02's repository statements); Section 25.6 (non-claims N13–N30, the
last two added). In Part I: a pointer after Theorem 1.1, the provenance and
notation sentences of Section 1.4, a closing item of its neighbour list,
status notes in Section 6 (the saturation remark), Section 10.3 (twice),
Section 11.4, the new item (6) of Section 11.5 and non-claims N5–N8, and a
sentence in Appendix A.

**Delivered files.** `code/02-support-bounded-fields-verify.py`,
`code/02-support-bounded-fields-build.sh`,
`data/02-support-bounded-fields-verification.json`,
`data/02-support-bounded-fields-BUILD_REPORT.json` and
`02-support-bounded-fields-SOURCE_AUDIT.md` are byte-identical to the
delivery (checked against a fresh extraction of `aa268a4`). The manuscript,
its README and PDF are not shipped. Discrepancies, not fixed in the files:
the build report describes the delivered 25-page PDF (36 bookmarks, Python
3.13.5), not this report, and lists files that are not shipped; the build
script expects `article.tex` and `verify.py` beside it (see below); the audit's
novelty boundary lists the reservoir extension of the quotient method as a
contribution, which is stale (Section 25.5, item 3).

## Notation (Part I)

No symbol of source 01 was renamed. Section 1.4 fixes the conventions against
[NOTATION.md](../../NOTATION.md):

| Here | Meaning | Not to be confused with |
|---|---|---|
| `F_k = k((t^Γ))`, `k ∈ {R, C}` | the full Hahn field | NOTATION's `F_Γ` is the **real** field (`= F_R` here) and `K_Γ` the **complex** one (`= F_C` here) |
| `K_{κ,k}` | series with fewer than `κ` nonzero terms; `K` from Section 8 on | NOTATION's full complex workspace `K_Γ`; Part II's class field `K_{κ,k}(No)` |
| `L_{κ,k}` | its completion, Theorem 7.1 | |
| `D_x` | the approximation cut of a missing `x` | surquaternions' `D_Γ` |
| `E_x = K + Kx` | a two-dimensional valued space | three-duals' `E_Γ(V)`; the entire-function rings of `ent:` |
| `κ`, `μ = cf(κ)` | an uncountable cardinal and its cofinality | residue fields `κ_n` (`ent:`), the gain `κ = v(q)` (expanding dynamics), measures `μ` |
| `I_D` | an additive subgroup, not an ideal | the error ideal `I_κ` of expanding dynamics |
| `T_κ(x)` | the first-κ prefix, an external invariant | a truncation symbol of the language (there is none) |

`cf(Γ)` is cofinality toward `+∞`, `v = min supp`, and `t^γ ↦ ω^(−j(γ))`,
as in NOTATION. Four words are pinned down explicitly: **bounded** means a
bound on the *cardinality* of the support (in
`transcendence-over-bounded-support` it means bounded above in the exponent
order); **complete** type, complete field and spherically complete field are
three different notions; **closure** in Theorem 7.1 is topological, while
Proposition 2.2 is about real and algebraic closedness; an **omitted** type
is a one-type over the set-sized `K_{κ,k}` realized in `F_k`, not an omitted
cut of a proper-class field (Part II treats those cuts for its class field).

## What the report claims

### Part I (source 01)

Fix an uncountable cardinal `κ` (possibly singular), `μ = cf(κ)`, a nonzero
divisible ordered abelian group `Γ` (a set), `k = R` or `C`, and
`K_{κ,k} = {f ∈ k((t^Γ)) : |supp f| < κ}`. Real types are taken in the
language of ordered rings, complex valued types in the ring language with
valuation divisibility.

- **Theorem 1.1 (`fkc:thm:main`), the package.**
  (i) `K_{κ,R}` is real closed and `K_{κ,C}` algebraically closed, even for
  singular `κ`, and both inclusions in the full Hahn fields are elementary
  (Proposition 2.2).
  (ii) For missing `x, y`: `tp(x/K) = tp(y/K)` iff `T_κ(x) = T_κ(y)`, the
  first `κ` nonzero terms (Theorems 4.1 and 4.3); the realizations of a type
  in `F_k` form the coset `T_κ(x) + I_{D_x}`.
  (iii) The least number of formulas of such a type with no realization in
  `K_{κ,k}` is exactly `cf(κ)`, for arbitrary formulas (Theorem 5.3, via
  eventual agreement, Lemma 5.2, and quantifier elimination).
  (iv) If `K_{κ,k} ≠ F_k`, nests of fewer than `cf(κ)` closed balls meet and
  some nest of `cf(κ)` balls is empty, so it is never spherically complete
  (Lemma 6.1, Theorem 6.2, Corollary 6.3).
  (v) The completion is `L_{κ,k} = {f : |supp f ∩ (−∞, γ)| < κ for all γ}`
  (Theorem 7.1); the new elements have cofinal support of order type exactly
  `κ` (Proposition 7.2); and if `K_{κ,k} ≠ F_k`, it is complete iff
  `cf(Γ) ≠ cf(κ)` (Theorem 7.4, with Lemma 7.3).
- **Theorem 3.1:** the exact approximation-value set of a missing `x` is the
  cut `D_x`, of cofinality `cf(κ)`; no best approximation exists.
  Corollary 4.4: at least `2^κ` missing types when `K_{κ,k}` is proper.
- **Theorem 5.4, pure-field collapse:** in the pure ring language all missing
  elements of `F_C` have one type, with omission number `|K_{κ,C}|`.
  Corollary 5.5: restriction of types along `K_κ ≼ K_λ` is truncation of
  prefixes, so the omission number can drop from `ℵ_1` to `ℵ_0`.
- **Theorem 8.1:** the exact valuation-loss set of every linear retraction
  `K + Kx → K`; none is contractive, and a continuous one exists iff
  `x ∉ L_{κ,k}`. Corollary 8.2: the continuous dual of `K + Kx` has dimension
  0 or 2.
- **Examples (Section 9)** over `Γ_θ = ⊕_{α<θ} Q e_α` (largest-index order,
  `cf(Γ_θ) = cf(θ)`, Lemma 9.1): at `κ = ℵ_ω` a countable missing Cauchy limit
  with `L = F` (Example 9.2); the same countable ball obstruction in a complete
  field over `Γ_{κ+}` (Example 9.3); a strict chain `K ⊊ L ⊊ F`
  (Example 9.4); at `κ = ℵ_1` a sequentially complete but incomplete field
  (Example 9.5); and for `Γ ≤ R`, `K_κ = F` for every uncountable `κ`.
- **Section 10:** transfer to actual surreal and surcomplex subfields through
  Conway normal forms, with the explicit surreal
  `X_κ = Σ_{α<κ} ω^(−ω^α)`.

### Part II (source 02)

In Gödel–Bernays class theory with Global Choice (used only in Section 22),
for every uncountable `κ`, regular or singular, `μ = cf κ`,
`K_{κ,ℝ}(No) = {x ∈ No : |supp_ω x| < κ}`, `K_{κ,ℂ}(No) = K_{κ,ℝ}(No)[i]`,
`Oz_{<κ} = K_{κ,ℝ}(No) ∩ Oz`:

- **Fields (Theorem 15.2, Proposition 15.3):** a truncation-closed real closed
  proper-class field containing every monomial, algebraically closed
  complexification, both inclusions elementary; value group `No`, residue
  fields `ℝ`, `ℂ`; strict hierarchy with union `No`.
- **Gaps (Theorems 16.3, 16.4, Corollary 16.5):** set-presented gaps ↔ normal
  forms of order type exactly `κ` (first-κ prefixes), fillers
  `T + {ε : v(ε) > −a_α for all α < κ}`; every gap has character `(μ,μ)`;
  `cf κ ≠ cf λ` ⇒ `K_{κ,ℝ}(No) ≇ K_{λ,ℝ}(No)`, even as abstract fields.
- **Saturation (Theorem 17.1, Corollary 17.2):** `ν`-saturated iff `ν ≤ cf κ`.
- **Strong sums and nests (Theorems 18.2, 18.4):** threshold exactly `μ` for
  ambient strong sums (witness `h_κ = Σ_{α<κ} ω^(−α)`, omnific witness
  `z_κ = Σ_{α<κ} ω^(κ−α)`) and for empty nests of closed balls.
- **Topology (Propositions 19.1, 19.2):** set-indexed Cauchy nets are
  eventually constant (not new); `K_{κ,ℝ}(No)` is closed and nowhere dense in
  `K_{λ,ℝ}(No)` and in `No`.
- **Exponential (Theorems 20.1, 20.6, 20.8, Proposition 20.2, Corollary 20.7):**
  closed under `exp`, not under `log`; exact image
  `exp(K) = {y > 0 : le(y) ∈ K}`; **no ordered-group isomorphism
  `(K,+) ≅ (K^{>0},·)` at all**; `(K, exp) ≼ (No, exp)` fails; a subfield
  with every monomial closed under `log` is `No`.
- **Omnific integer part (Proposition 21.1, Theorem 21.3, Corollaries 21.5,
  21.6, Section 21.3):** discrete integer part, `Frac = K_{κ,ℝ}(No)`, units
  `±1`; every unital map to a set-sized ring factors through `ct` (already
  `osq:thm:support` (i); new route via a countably supported reservoir);
  quotients `ℤ`, `ℤ/n`; `cf κ ≠ cf λ` ⇒ `Oz_{<κ} ≇ Oz_{<λ}` (new); Gaussian
  version through `ℤ[i]`.
- **Real forms (Theorem 22.3, Propositions 22.2, 22.5):** `K_{κ,ℂ}(No) ≅ No[i]`
  over `ℂ`; the transported involutions `τ_κ` are pairwise nonconjugate for
  distinct `cf κ` and never conjugate to `conj`, a proper-class family without
  forcing; all `(K_{κ,ℂ}(No), conj_κ)` have one theory but saturation exactly
  `ν ≤ cf κ`.
- **Questions 24.1–24.8**, all open: isomorphism at equal cofinality; theories
  with an omnific predicate; support-ideal classification; real-form
  invariants beyond one spectrum; derivations; one-sided exponentials;
  detecting the rings beyond set targets; formal proof architecture.

### Status notes (batch 32)

- **Part I's second further question (Section 11.4, richer languages):**
  partly addressed in the class setting (exponential closure and
  non-elementarity; one theory with named conjugation); no type
  classification; stays open.
- **Section 10.3:** the exponential and named-conjugation paragraphs carry
  notes pointing to Part II; the disclaimers stand for the set subfields.
- **Non-claims N5–N8** carry notes: saturation, topology relative to `No`
  and exponential closure are proved in Part II for the class field; the
  set-field disclaimers stand.
- **`univ:q:families`** (across-universes report): Remark 22.4 answers, in a
  single universe and without forcing, the clause on infinite collections of
  regular thresholds: every class of infinite regular cardinals is realized
  simultaneously by pairwise nonconjugate involutions agreeing with `conj`
  on `ℂ` whose fixed fields have no set-sized cofinal subset. Arbitrary
  saturation spectra, multi-character gap spectra and inner-model versions
  stay open.

## What the report does not claim

Section 11.6 (Part I) and Section 25.6 (Part II) list every limitation, with
one numbering.

1. `κ` is uncountable; the finite-support case is excluded.
2. Cardinally bounded Hahn fields (Kuhlmann–Shelah for regular `κ`;
   Berarducci–Kuhlmann–Mantova–Matusinski), Hahn arithmetic and closedness,
   Conway normal forms, approximation-type theory with its ball formulas
   (F.-V. Kuhlmann, Proposition 4.4), full-Hahn ball gluing (Poonen), and
   RCF and ACVF quantifier elimination (Tarski, Robinson, Yin) are **not
   new**.
3. **The constructions and the quantifier-elimination inputs are established;
   the proposed contribution is the joint first-κ classification** with its
   exact omission number and completion and linear consequences. It was not
   identified in the reviewed material, but the priority search was targeted
   and not exhaustive (no MathSciNet or zbMATH), and expert review may find
   equivalents.
4. No named longstanding conjecture is settled; the repository comparison
   was not exhaustive; there is no Lean build or certification.
5. Only types realized in the fixed `F_k` are classified: no saturation
   theorem, no automorphism homogeneity, and types are not claimed to be
   automorphism orbits. *(Status: stands for the set fields; Part II proves
   saturation for the class field.)*
6. The topology is intrinsic to the set-sized workspace, not the subspace
   topology from `No`; support bounds are cardinalities, not order bounds.
   *(Status: Part II treats the topology relative to `No` for the class
   fields.)*
7. The subfields are not claimed birthday-initial, closed under the surreal
   exponential, compatible with the Berarducci–Mantova derivation, or to
   define the prefix operator. *(Status: Part II proves exponential closure
   for the class field only.)*
8. Languages with conjugation, truncation, exponential or derivation, and
   several-variable types, are not classified (left as questions,
   Section 11.4, unnumbered). *(Status: still not classified.)*
9. No new general Hahn–Banach theorem; the zero dual is over an incomplete
   base and contradicts nothing in finite-dimensional functional analysis.
10. Not a new version of the independence theorem of
    `transcendence-over-bounded-support`.
11. The 9,622 finite assertions do not verify the transfinite theorems,
    quantifier elimination, novelty or any Lean implementation.
12. The assembly comparisons with other reports prove no new theorem.
13. Source 02 is AI-assisted and unrefereed; written proofs, not Lean; no
    independent peer review; no repository build verifies it.
14. Priority is not certified: the review was targeted and guide-level, an
    incomplete code search was not used as evidence, no MathSciNet, zbMATH or
    subscription audit; Wikipedia was orientation only; Conway and Gonshor
    were read through the Mantova–Matusinski survey.
15. No named published conjecture is solved, and the eight questions are not
    claimed to be published open problems.
16. Only set-presented gaps of `K_{κ,ℝ}(No)` are classified: not
    class-cofinal gaps, all surreal gaps, all real forms or all bounded Hahn
    fields.
17. Isomorphism at equal cofinality is open (Question 24.1).
18. `ψ_κ` and `τ_κ` are not claimed to preserve monomials, valuation,
    exponential, Hahn sums or the omnific ring.
19. `κ = ℵ_0` is excluded.
20. Strong sums are support operations, not topological limits.
21. The exponential image and the log-hull collapse follow directly from
    Gonshor; no strong priority is claimed.
22. Credited, not claimed: bounded Hahn fields (Kuhlmann–Shelah;
    Kuhlmann–Kuhlmann–Shelah), the additive-versus-multiplicative exponential
    obstruction, class back-and-forth, set-Cauchy stabilization, forcing-based
    real forms, and the full-`Oz` quotient theorem with scaled collision.
23. Theorem 20.6 contradicts neither Kuhlmann–Shelah's κ-bounded
    exponentials nor the omega-fields of BKMM.
24. Theorem 20.8 needs every monomial; nothing about exp–log closed
    subfields in general.
25. The Gaussian rings `Oz_{<κ}[i]` are not claimed pairwise nonisomorphic.
26. No derivative-support estimate or derivation closure.
27. The 31,672 checks cover finite identities and boundary conventions only:
    not cardinal or cofinality arguments, infinite summability, class
    constructions, saturation, the nonexistence of a surjective exponential,
    novelty or Lean.
28. Global Choice is used only in Section 22; no class Zorn lemma, no truth
    predicate; the "proper-class family" is one class relation.
29. (merge) Source 02's novelty claim for Theorem 21.3 is stale, and several
    of its results were in the collection in set-sized or large-cardinal
    form (Section 25.5).
30. (merge) The comparisons and status notes prove no new theorem;
    Remark 22.4 answers one clause of `univ:q:families` in a single universe
    only.

## Corrections to the sources' repository statements

**Source 01 (Section 11.5)** keeps the pin `465a54b` as provenance and records:

- At the pin the catalogue described 44 reports, as stated; batch 21 and
  batch 22 have since added four, and the collection had 48 report
  directories when Part I was written.
- The manuscript compared its universe-related material with `foundations`;
  the collection now also has `surreal-fields-across-universes`, added after
  the pin (different objects; below).
- The negative indexed search for "spherical" was a false negative:
  spherical completeness of full Hahn fields was already stated in
  `rank-one-berkovich` (`prop:spherical`) and `three-duals-of-hahn-vector-spaces`
  (`duals:prop:spherical`). The manuscript did not rely on the search.
- The comparison with the Hahn-vector-space report omitted its countable
  analogues `duals:thm:completion` and `duals:thm:cofinality-completion`,
  and the Berkovich closure of finite-support series; they do not treat
  cardinally bounded fields, but they belong in the priority context of
  Theorems 7.1 and 7.4.
- Its statements about `transcendence-over-bounded-support` and about the
  two topologies of `foundations` were confirmed.
- (batch 32, new item 6) The confirmation that the collection had no study
  of cardinally bounded Hahn fields describes the collection at assembly;
  since then `large-cardinal-embeddings-and-normal-forms` (`𝒮_{<κ}`,
  `lce:sg:thm:shortfield`), `set-sized-quotients-of-omnific-integers`
  (`osq:thm:support`) and `omnific-preserving-automorphisms`
  (`opa:as:prop:kappa`) have added such material; none studies Part I's
  types or completions.

**Source 02 (Section 25.5)** keeps the pin `343dc2c` and records:

1. Part I (this report) was present at the pin and proves the set-sized
   version; source 02 does not cite it.
2. The large-cardinal report already had, at the pin, the same class
   `𝒮_{<κ}` at a measurable critical point, with the integer part, its
   fraction field, and exponential-but-not-logarithmic closure with the
   witness `z_κ`; the every-κ short-field theorem, closedness in `No`, the
   integer part for every κ and the log-closure collapse were added after the
   pin. Source 02 does not cite it.
3. **Stale novelty:** `osq:thm:support` (i), present at the pin, is Theorem
   21.3 (`D = ℤ`, `k = ℝ`) and the Gaussian factorization (`D = ℤ[i]`,
   `k = ℂ`). Source 02's reservoir is a new (third) route; Corollary 21.6 is
   new.
4. The class back-and-forth is `saut:thm:acfhomogeneity`, and non-conjugacy
   to `conj` also follows from `saut:prop:conjugacycriterion`.
5. Confirmed: the across-universes and quotient reports contain what source 02
   credits to them; `found:thm:discrete` has the set-Cauchy stabilization.

## Relation to the neighbouring reports

- **[large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)**:
  its field of short normal forms `𝒮_{<κ}` **is** Part II's `K_{κ,ℝ}(No)`, and
  `𝓘_{<κ}` is `Oz_{<κ}`. It proves real closedness for every uncountable κ
  (`lce:sg:thm:shortfield`), closedness and nowhere density in `No`
  (`lce:sg:prop:closed-support`, by another proof), the integer part
  (`lce:sg:prop:integerpart`, `lce:eq:Ozfrac`), and, at a measurable critical
  point, exponential closure without logarithmic closure with the same witness
  `z_κ` (`lce:cor:expclosure`) and the log-closure collapse
  (`lce:thm:twoclosures`). Part II proves the exponential results for every
  uncountable κ, and the gap, saturation, strong-sum, nest and quotient
  results, which that report does not have. Its `h_κ = Σ ω^(−α)` and `z_κ`
  are the series of Part II; its `p_κ` is a different series.
- **[set-sized-quotients-of-omnific-integers](../../surreal/set-sized-quotients-of-omnific-integers/)**:
  `osq:thm:support` (i) contains Theorem 21.3 and the Gaussian case; Part II's
  reservoir gives a third route through `osq:lem:collision`, which that report
  records as not applying to the bounded rings with its Hahn-field reservoir.
- **[omnific-preserving-automorphisms](../../surreal/omnific-preserving-automorphisms/)**:
  its `K_{<κ}` (`opa:as:prop:kappa`, regular κ) is Part I's `K_{κ,k}`; for
  singular κ, where it claims no extension, Theorem 18.2's family shows that
  fewer than κ members and ambient summability do not give summability in
  `K_{<κ}`. `opa:as:q:singular` (about automorphisms) is not answered.
- **[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/)**:
  `saut:thm:acfhomogeneity` is Lemma 22.1's back-and-forth;
  `saut:prop:conjugacycriterion` gives non-conjugacy to `conj`;
  `saut:thm:inequivalentrealform` is a real form with a countable cofinal
  subset (a different obstruction). Its batch-32 addition classifies strong
  valued `Oz[i]`-preserving involutions; Part II's `τ_κ` are pure-field
  involutions, and the two families are complementary.
- **[surreal-fields-across-universes](../../foundations-and-computation/surreal-fields-across-universes/)**
  studies saturation and omitted cuts of the proper-class field `No^M` inside
  `No^N` for inner models. Part I answers none of its questions; Part II
  answers one clause of `univ:q:families` in a single universe (above) and
  parallels `univ:thm:firstgap`, `univ:cor:recover`, `univ:cor:spectrum`,
  `univ:prop:topology` and `univ:thm:involutions` for other fields.
- **[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)**
  works over supports **bounded above in order** and explicitly excludes
  cardinal support bounds (`bst:eq:base` and its conventions list). Its
  `bst:cor:optimal` is consistent with this report. No `bst:` question is
  answered.
- **[three-duals-of-hahn-vector-spaces](../three-duals-of-hahn-vector-spaces/)**:
  `duals:thm:completion` (finite coefficient rank below every cut) and
  `duals:thm:cofinality-completion` (completion proper iff `cf(Γ) = ℵ_0`)
  have the shape of Theorems 7.1 and 7.4 at the excluded countable bound, for
  vector spaces (Remark 7.6). Its `duals:prop:spherical` is the full-Hahn
  gluing that Lemma 6.1 refines by a cardinal bound.
- **[rank-one-berkovich](../rank-one-berkovich/)**: spherical completeness of
  `C((t^R))` (`prop:spherical`) and the closure of the finite-support series
  in `C((t^Q))`, the countable analogue of `L_{κ,k}` (Remark 7.6). This
  report's rank-one boundary case (`K_κ = F` for `Γ ≤ R` and uncountable `κ`)
  is consistent with it.
- **[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**:
  its `Γ_∞ = ⊕_{j≥0} Q e_j`, `e_j = ω^j` (`ent:eq:concrete-group`), is the
  **same construction** as `Γ_θ` here, namely `Γ_ω`, with the same embedding in
  `No`; its `Γ_{ω_1}` (`ent:eq:Gamma-omegaone`) is the group of Example 9.5
  (Remark 9.6). The questions asked of these groups differ.
- **[foundations](../../foundations-and-computation/foundations/)** separates
  the intrinsic and full fine topologies (`found:prop:twotopologies`,
  `found:thm:discrete`); Section 10 relies on that distinction, and
  Proposition 19.1 is `found:thm:discrete` for the class fields.
- **[hidden-negative-hermitian-directions](../hidden-negative-hermitian-directions/)**
  asks, in an unlabelled question, about order density and approximant
  degrees for support-family subfields. `K_{κ,R}` is such a subfield, but that
  question is not answered here.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 53 pages (Part I pages 5–25, Part II pages 26–50,
appendices and references 50–53) with zero errors, zero LaTeX or package
warnings, zero overfull or underfull boxes, zero undefined references or
citations, zero multiply defined labels and zero duplicate PDF
destinations. It needs pdfLaTeX with newtx, amsthm, mathtools, microtype,
geometry, enumitem, booktabs, array, longtable, fancyhdr, hyperref,
cleveref, bookmark and xurl; no shell escape, BibTeX, network access or
figures. The LaTeX kernel must provide hooks (2020-10 or later).

**Run the programs on a copy of this directory.** `code/verify.py` always
writes `verification.json` next to itself (so into `code/`), without an
option to change it; `code/02-support-bounded-fields-verify.py` writes
`verification.json` into the **current directory** unless `--output PATH` is
given. Both build scripts expect a flat layout (`article.tex` and
`verify.py` beside them) and write the PDF and auxiliary files there; run on
this report's `article.tex` they typeset this report, not the delivered
manuscripts.

```sh
cp -r first-kappa-coefficients /tmp/fkc-copy
cd /tmp/fkc-copy
python3 code/verify.py > /dev/null      # writes code/verification.json
diff code/verification.json data/verification.json
python3 code/02-support-bounded-fields-verify.py --output /tmp/fkc-copy/sb.json
diff sb.json data/02-support-bounded-fields-verification.json

mkdir /tmp/fkc-flat                     # only to run a delivered build script
cp article.tex code/verify.py code/build.sh /tmp/fkc-flat/
cd /tmp/fkc-flat && bash build.sh
```

Source 01's recorded run (`data/verification.json`, seed 20260922) passed
**9,622 exact-rational assertions** in 18 families over finite
Laurent-polynomial supports in lexicographically ordered `Z²`: first
disagreement, sums and products, leading data of factored polynomials, tail
invariance, nested-ball agreement and gluing, and the retraction-loss
trichotomy. During assembly a rerun on a copy (Python 3.14.4) reproduced it
exactly, up to CRLF line endings on Windows.

Source 02's recorded run (`data/02-support-bounded-fields-verification.json`)
passed **31,672 exact `Fraction` checks** in 14 categories (first-outside
comparison 5,832; later-bracket separation 8,192; prefix reconstruction
5,150; prefix brackets 5,120; closed-ball boundary 1,890; nested balls 1,890;
earlier coefficient forbidden 1,830; constant-term product 729; omnific floor
375; separator support 216; scaled collision 144; shifted positive support
144; positive shift 100; geometric identity 60), standard library only. For
this merge it was rerun on a copy with `--output` (Python 3.14.4, about half
a minute): the output is identical to the record up to CRLF line endings on
Windows. The checks test finite mechanisms only; they prove no transfinite,
cardinal, class, saturation, model-theoretic or priority statement.
