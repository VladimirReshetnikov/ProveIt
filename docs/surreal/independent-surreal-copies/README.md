# Independent Surreal Copies and Arithmetic Intersections

**Prescribed Hahn cores, algebraic independence, two transcendental descent obstructions, composita, and maximal transcendence of Hahn joins**

This is a research report dated 23 September 2026, built from three
manuscripts. Author line of sources 01 and 02: AI-assisted research draft
(prepared for Vladimir Reshetnikov); of source 03: AI-assisted research
manuscript.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 31, manuscript 06 | `Surreal_Independent_Copies` (main file `independent_surreal_copies.tex`, 25-page PDF) | `bcac55a` | `9d28e28` | Sections 1–14, Appendix A.1–A.6 (written in `781b19e`) |
| 02 | batch 34, manuscript 05 | `Surreal_Composita_Research` (*Beyond Composita of Surreal Copies: Exact rank tests, differential transcendence, and omnific witnesses*, 29-page PDF) | `7b256e0` | `a7a435f` | Sections 15–27, Appendix A.7–A.8 |
| 03 | batch 35, manuscript 01 | `Surreal_Hahn_Joins_Research` (*Maximal Transcendence in Hahn Joins: Mixed-support independence and prime omnific integers*, 27-page PDF) | `f388f95` | `dec8d56` | Sections 28–41, Appendix A.9–A.10 |

Every result, proof, example, question and limitation of the three
manuscripts is printed. Material that source 02 re-derives from source 01
(the explicit copies and the re-expansion) is printed once and credited.
Sources 02 and 03 were written from the same snapshot of source 01's text
and do not know each other; source 03 overlaps neither in a theorem. The
report is
AI-assisted and unrefereed. **Independent proof review and formalization are
pending.**

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 108 pages (unnumbered title page,
                                         contents pages 1–4, then pages 5–107)
README.md                                this guide
02-composita-SOURCE_AUDIT.md             source 02's source and novelty audit, as delivered
02-composita-PROOF_AUDIT.md              source 02's author-side proof audit, as delivered
code/02-composita-verify.py              source 02's exact finite checks (SymPy)
code/02-composita-build.sh               source 02's build script (checks, then its PDF; see below)
data/02-composita-verification.json      source 02's recorded run: 2,530 checks in 21 categories
data/02-composita-requirements.txt       source 02's pin, sympy==1.14.0
data/02-composita-BUILD_AUDIT.json       source 02's build and PDF-inspection record
code/03-hahn-joins-verify.py             source 03's exact finite checks (SymPy; prints, writes no file)
code/03-hahn-joins-build.sh              source 03's build script (its PDF, then the checks; see below)
data/03-hahn-joins-verification.txt      source 03's recorded run: five PASS lines
```

Source 01's package contained only the article, its PDF and a README, so it
has no verification suite. For all three sources the delivered README and PDF are
not shipped: this README replaces them, and `article.pdf` is a build of this
text. Source 01's delivered README names `independent_surreal_copies.pdf` and
`independent_surreal_copies.tex`, shipped only as the rewritten `article.tex`
and its new build, and mentions rendered pages and contact sheets from its
visual check, which are not shipped. Source 02's delivered README and audits
name `article.tex`, `article.pdf`, `verify.py`, `verification.json`,
`requirements.txt`, `build.sh`, `BUILD_AUDIT.json`, `SOURCE_AUDIT.md` and
`PROOF_AUDIT.md`: its manuscript, README and PDF are not shipped, and the
other seven files are shipped under the prefixed names above, byte-identical
to the delivery. Its `BUILD_AUDIT.json` describes the delivered 29-page PDF,
which is not in the collection. Source 03's delivered README names
`article.pdf`, `article.tex`, `verify.py`, `verification.txt`, `build.sh`
and `README.md`: its manuscript, README and 27-page PDF are not shipped,
and the other three files are shipped under the prefixed names above,
byte-identical to the delivery. No requirements file was delivered with
source 03 (it needs Python 3 and SymPy; the recorded run used SymPy
1.14.0).

## Labels and numbering

Every label in `article.tex` carries the prefix `isc:`. Source 01's 62 labels
are kept, unchanged after the prefix, with the twenty added when it was
written (`isc:sec:conventions`, `isc:sec:collection`, `isc:sec:nonclaims`,
seven appendix labels `isc:app:*`, and ten labels on unlabelled remarks and
subsections): 82 labels. The merge of source 02 added **111** labels, all
with the sub-prefix `isc:cp:` (193 in total). The merge of source 03 added
**82** labels, all with the sub-prefix `isc:hj:` (275 in total). No label
was renamed or removed, and no pre-existing theorem, section, equation or
question number changed: at each merge the `.aux` numbers of all earlier
labels (82, then 193) were compared with a build of the committed text. No
`isc:` label has a Lean mapping in the
[formalization ledger](../../FORMALIZATION.md).

Source 02's section *n* is Section *n* + 14 here (*n* = 1, …, 12), and every
numbered statement keeps its position: its Theorem *n.m* is Theorem
(*n* + 14).*m* here. Its Questions 1–12 are Research questions 11–22; its
Appendices A and B are Section 27; its notation index is folded into the
table of Section 15.5.

Source 03's section *n* is Section *n* + 27 here (*n* = 1, …, 13), and every
numbered statement and equation keeps its position: its Lemma *n.m* is Lemma
(*n* + 27).*m* here. Its lettered Theorems A, B, C, D share the lettered
counter of source 01's Theorems A–C and print as **Theorems D, E, F, G**.
Its Questions 1–10 are Research questions 23–32; its Appendices A–C are
Section 41, and its Appendix D (sources) is folded into Appendix A.9. The
merge added the numbered Remarks 28.1, 36.2 and 37.6 at the ends of
their sections, so no source number moved; cleveref type hints are on all
new labels.

In the merge, cleveref type hints (`\label[lemma]{…}` and so on) were added
to the labels of 59 lemmas, propositions, corollaries, definitions, examples,
remarks and the warning (26 of source 01, 33 of source 02), with a cleveref
name for `warning`. These environments share the theorem counter, and before
the merge cleveref printed every reference to them as "theorem" (for example
"theorem 8.2" for Lemma 8.2). Only the printed names of those references
change; no label name or number does.

Text added when source 01 joined the collection is marked `[write]`; text
added in the batch-34 merge is marked `[merge]`. Source 01's write added
Sections 1.5, 1.6 and 14 and Appendix A, and short `[write]` notes after
Proposition 4.4, Corollary 6.1, Theorem 6.2, equation (7.3), Lemma 9.1 and
Propositions 9.2 and 9.3, at the start of Section 10, after Corollary 10.3,
after research questions 1, 2, 6, 7, 8, 9 and 10, and in Sections 1.4 and
13.3. The merge added, in source 01's text, `[merge]` notes on the title page,
in Section 1.6 (status of the research questions), after Corollary 6.1 (with
the reciprocal note for the dilation report), after Lemma 8.2, after the proof
of Theorem C, after Research question 3, at the start of Section 14, in item
W1 and in Appendices A.1 and A.6. No statement of source 01 was changed and
no symbol of source 01 was renamed. The batch-35 merge uses the same
`[merge]` tag; its notes in the text of sources 01 and 02 (listed in
Appendix A.9) are the ones that mention source 03 or batch 35.

## Setting and notation

The work is in NBG with global choice, with ZFC for sets. Every support is a
set, even when an exponent group or a field is a proper class, and the cut
property is never applied to proper-class sides. `K_k(G) = {x : supp x ⊆ G}`
is the **full** Hahn field on an additive subgroup `G ⊆ No`, written in
Conway's decreasing large-`ω` convention. `H` is a set-sized divisible
subgroup (not necessarily convex), and `L_k = K_k(H)`.
`A_k(H) = D_k ⊕ Π_k(H)`, with `D_R = Z` and `D_C = Z[i]`, is the integer
ring, so that `A_R(H) = L_R ∩ Oz`. `B_k(H)` is the ring of series whose
support is bounded above **in the t-exponents**.

Watch for these readings (Section 1.5):

- **Convention switch.** From Section 9.1 to the end of Section 10 the source
  uses `t^h = ω^{-h}`. There the purely infinite part has *negative*
  `t`-exponents, and "bounded above" in `B_k(H)` means Conway exponents
  bounded **below**. Everywhere else in Sections 1–14 `Oz` sits at
  *positive* Conway exponents.
- **Integer ring.** `A_k(H)` is the omnific-preserving report's `𝓡_Γ`
  (Part III) and the Diophantine report's `𝓡_{D_k}(k,Γ)`. It is **not**
  `𝓐_Γ = R ⊕ Π` there, and not the Diophantine report's `𝒜_k(Γ)`. `D_k` is
  a ring of integers, never a derivation.
- **Bounded-support ring.** `B_k(H)` is the bounded-support report's
  `𝓑_H(k)`, with the arguments in the other order.
- **Maps.** `Φ_h` is `M_{1,h} = J_{h,id}` of the omnific-preserving report.
  It is not the surcomplex-automorphisms report's Taylor map `Φ_d`, and not
  the large-cardinal report's `J`. The letters `h_α, G_α, Φ_α, K_α` name the
  abstract family of Theorem 3.4 in Sections 3–6, and the explicit family in
  Sections 7–8, where `h_α` is an *inner* map. `h_α` fixes `H` as a set of
  exponents, while `Φ_α` fixes `K_R(H)`.
- **Monomial-preserving** means that a Conway monomial goes to a Conway
  monomial with coefficient one (the omnific-preserving report's
  "exact-monomial"). It does **not** mean commuting with the omega-map:
  `Φ_0(ω) = ω^{ω^{1/2}}`, while `ω^{Φ_0(1)} = ω`.
- **Other letters.** `ψ(x) = 1/2 + x/(2(1+|x|))` is not that report's `μ_12`
  (its source 12's `ψ`). `κ` is `cf(H)` in Section 10, and an arbitrary
  uncountable regular cardinal in Section 11; it is never the large-cardinal
  report's critical point. `H` is not a convex subgroup `H_g`. `M = K_0K_1`
  is an ordinary compositum, not a monomial map `M_{χ,τ}`. `E`, `F`, `L`,
  `A`, `B`, `D` and `S` are local letters; Section 1.5 lists every use.
- **Strong** means that Hahn summability of set-indexed families is
  preserved. It is not convergence.

Source 02 (Section 15.5) uses both conventions, identified by
`t^γ = ω^{-γ}`. In Sections 16–21 the fields are abstract: `E = F((t^Γ))`,
`L = k((t^Γ))`, `M = FL` (an ordinary compositum), `F[L]` the ring generated
by `F` and `L`, and `C_fg(F/k;Γ)` the union of `D((t^Γ))` over finitely
generated coefficient fields `D`. The Euler derivation `∂` multiplies
`t^γ` by `λ(γ)` for an additive weight `λ : Γ → k`. From Section 22 on, `E`,
`M`, `K_j`, `G_j`, `h_j`, `Φ_j` are source 01's explicit copies (`j = 0, 1`),
`g = ω^{7/2} = h_1(1)`, `b = ω^{15/4}`, and `Δ` is the Euler derivation that
extracts the coefficient of the inner monomial `ω^{7/2}` from the dominant
`G_1`-coordinate of an exponent and kills `K_0`.

Symbols renamed from source 02 (the full table is in Section 15.5; no
normalization changed):

| Here | Source 02 | Reason |
|---|---|---|
| `Γ`, `Γ_0`, `Γ'` (outer ordered group) | `H`, `H_0`, `H'` | `H` is the common core of Theorem A, and source 02's own Question 4 uses it so |
| `g` (positive element with `λ(g) = 1`; `ω^{7/2}` in Sections 22–24) | `h` | `h`, `h_α` are embeddings here; source 01 already writes `g = h_1(1) = ω^{7/2}` |
| `ω^b` (shift multiplier) | `s` | `s_n = ω^{g_n}` are the coefficients of `S` |
| `F[L]` (finite coefficient-rank ring) | `T` | `T` also names the inner support set |
| `Θ`, `G_Θ`, `C_Θ` (inner support set, its group, localized field) | `T`, `H_T`, `C_T` | as above |
| `R_0[R_1]`, `R_0[R_1][S]`, `R_0[R_1][i]` | `B`, `B[S]`, `B_C` | `B` is a subgroup in Lemma 8.1; `B_k(H)` is the bounded-support ring |
| `j = 0, 1` (copy index) | `i` | `i = √−1` in Section 24 |
| `𝔄` (private-index family) | `𝒜` | `𝒜_k(H)` is the integer ring |
| `p_ij`, `W_i(X, x)`, `w_i`, `ν` (in the proof of Theorem 19.2) | `A_ij`, `H_i(T, x)`, `R_i`, `D` | clashes with `A_i`, `H`, `T`, `R_j`, the field `D` |
| `γ_0 + γ_1`, `e` (generic exponents from Section 22 on) | `g_0 + g_1`, `g` | `g = ω^{7/2}` |

Source 03 (Section 28.5) is written in the same two conventions. In
Sections 30–31 the fields are abstract: `Γ_0, Γ_1` divisible subgroups of one
ordered group with core `H = Γ_0 ∩ Γ_1`, `K_j = k((t^{Γ_j}))`,
`E = k((t^{Γ_0+Γ_1}))`, `M = K_0K_1`, and `∂_χ` the Euler derivation of an
additive character `χ` (source 02's weight `λ` under another name). From
Section 33 on they are subfields of `No` or `No(i)`. Symbols renamed from
source 03 (the full table is in Section 28.5; no normalization changed):

| Here | Source 03 | Reason |
|---|---|---|
| `M = K_0K_1` (ordinary compositum); `M'`, `M^alg`, `M_*` | `L`; `L'`, `L^alg`, `L_*` | `L` is the common core `L_k`, and source 02's `k((t^Γ))` |
| `Γ_0, Γ_1`; `K_0, K_1`; `K_{0,*}, K_{1,*}` | `Γ_1, Γ_2`; `K_1, K_2`; `K_{1,*}, K_{2,*}` | the factors of a join are indexed 0, 1 here (`G_0, G_1`, `K_0, K_1`) |
| `K_k(G)` | `H_k(G)` | the same full Hahn field |
| `∂_χ`, `∂_i`, `∂_c = Σ c_i ∂_i`; `δ` (relative derivations) | `D_χ`, `D_i`, `D`; `D` | `D` is a field in source 02 and `D_k` a ring of integers |
| `Γ'` (a subgroup in Lemmas 30.1, 30.3) | `Δ` | `Δ` is source 02's Euler derivation |
| `Π_k(G)`, `A_k(G)`; `A^D_k(G) = D ⊕ Π_k(G)` | `I_k(G)`, `R_k(G)`; `S`, `T` | the same objects as in Section 9; `I`, `R_j`, `S`, `T` are taken |
| `A_k(A_κ)[A_k(B_κ)]` etc. | `S_k`, `R_{A,k}`, `R_{B,k}`, `R_{E,k}` | as above |
| `𝒯`, `φ : 𝒯 → E`, `dy` | `T`, `h`, `dt` | as in source 02; `h` is an embedding, `t` the Hahn variable |
| `𝓘_κ`; `𝔅_η`; `Ξ_U`; `Λ_α` | `I_κ`; `B_η`; `Z_U`; `C_α` | `I_α` interval; `B` a group; source 02's `Z_α`; `C_Θ` |
| Theorems D–G; Research questions 23–32 | Theorems A–D; Questions 1–10 | shared counters |

Kept and disclosed (Section 28.5): `λ_n, μ_n, ρ_n` are real exponents, not
the Euler weight `λ`, a slice `λ_{g,H}`, `μ = |F|` or the embedding `ρ`;
`e_α = ω^{-ι_0(α)}`, `f_α = ω^{-ι_1(α)}`, `r_α = e_α + f_α` are surreal
exponents with the **ordinal** product `ι_0(α) = 2·_ord α` (tempting false
reading: `ω^{-2α}` with the surreal `2α`; they differ at `α = ω`), and
`r_α` is not a real coefficient `r_g`; `χ_i` are characters, not those of
`M_{χ,τ}`; `ι_0, ι_1` are not inner lifts; `P_η`, `W_α`, `F_U`, `p_n` are
not `P`, `P_α`, `W_i`, `F`, `p_ij`; `D` in Section 35 is a ring of integers.
Tempting false readings printed there: "the annihilator `∂_c` kills the
compositum" (only a finitely generated part, chosen after a relation is
fixed); "the automorphisms of Theorem 37.5 are automorphisms of `No(i)` or
of `Oz`" (they are automorphisms of one complex Hahn join fixing `M`).

Tempting false readings printed in Section 15.5: "finite coefficient rank is
necessary for membership in `M`" (only for `F[L]`; `M` contains a geometric
series of infinite rank); "`Δ` is a surreal derivation" (it is a diagonal
Euler derivation of the explicit join, not Berarducci–Mantova, Hardy type or
exponential-compatible). This `L` is not the common field `L_k`, `λ` is not a
coset slice `λ_{g,H}`, and `F` is a coefficient field, not the witness `F` of
Theorem B.

## What the report claims

Theorem numbers are those of the built `article.pdf`. For Sections 1–14 they
agree with source 01's delivered PDF, for Sections 15–27 they are source
02's shifted by fourteen, and for Sections 28–40 source 03's shifted by
twenty-seven (its Theorems A–D are Theorems D–G). Remarks and warnings share the theorem counter, so
the classification is Proposition 4.4 and the set-sized theorem is Theorem
11.2.

### From source 01 (Sections 1–14)

- **Theorem A: prescribed independent copies.** For every set-sized
  divisible subgroup `H ⊆ No`, there are class maps `Φ_α : No → No`,
  `α ∈ On`. Each is a proper, strong, real-fixing, monomial-preserving
  ordered field embedding that fixes `L_R` pointwise. The images `K_α`
  satisfy `K_α ∩ K_β = L_R`, and every finite subfamily is jointly linearly
  disjoint over `L_R`. The rings `R_α = Φ_α(Oz)` satisfy `R_α = K_α ∩ Oz`,
  `R_α ∩ R_β = L_R ∩ Oz` and `Φ_α^{-1}(Oz) = Oz`. The complexifications give
  the same assertions over `L_C`; they commute with conjugation and preserve
  and reflect `Oz[i]`.
- **Theorem B: transcendental failure of fraction-field descent.**
  `Frac(R_α) = K_α`, but `Frac(R_α ∩ R_β)` is a proper subfield of
  `K_α ∩ K_β = L_R`. The extension is transcendental for every set-sized
  `H`, including `H = 0`. For `H ≠ 0` the smaller field already contains
  every real constant. For `H = Q`, `1 + Σ_{n≥1} ω^{-n!}` is a
  transcendental witness. Each copy separately supplies one denominator for
  the whole common field (Proposition 9.2), but no shared one does
  (Corollary 10.4). The same holds for the Gaussian copies.
- **Theorem C: a transcendental gap above the compositum.** For two explicit
  copies with `H = 0`, the full Hahn join `E = K(G_0 + G_1)` contains the
  countably supported
  `S = Σ_{n≥1} ω^{ω^{ψ(n)} - n ω^{7/2}}`, which is transcendental over the
  ordinary compositum `K_0K_1`. So the relative real algebraic closure of the
  compositum is a proper subfield of the join. The same `S` works after
  complexification. The proof uses a finite coefficient-field bound
  (Lemma 8.2, Theorem 8.3), not the invalid inference that every infinite
  sum lies outside a compositum.
- **Supporting results.**
  - Lemma 3.1 (a cut that avoids a set), Lemma 3.2 (a one-point ordered
    extension with avoidance) and Theorem 3.4 (an `On`-indexed family of
    ordered additive embeddings fixing `H`, with ranges independent over
    `H`, built by a set-state recursion).
  - Theorem 4.1 (the monomial lift `Φ_h`, whose image is exactly the full
    field `K_R(h(No))`, preserving and reflecting summability).
    Proposition 4.2 (it preserves and reflects `Oz`, and commutes with the
    omnific floor, the standard part and the modulus). Proposition 4.4
    (every strong, real-fixing, monomial-preserving embedding is a unique
    `Φ_h`).
  - Section 5: coset slices (Lemmas 5.2, 5.3), the theorem that
    `K(G_1)` and `K(G_2)` are linearly disjoint over
    `K(G_1 ∩ G_2) = K(G_1) ∩ K(G_2)` (Theorem 5.4, any coefficient field,
    set or class groups, no convexity), joint disjointness (Corollary 5.5)
    and polynomial-relation descent (Corollary 5.6).
  - Corollary 6.1 (any set of parameters lies in such a common field
    `L ⊇ R ∪ A`). Theorem 6.2 (the set-sized intersections in this class are
    exactly the `K_R(H)`). Theorem 6.3 (the Boolean meet diagram
    `E_J ∩ E_T = E_{J∩T}`, linearly disjoint, with Hahn join `E_{J∪T}`).
    Corollary 6.5 (independent choices are algebraically independent), and
    elementarity in the ordered-field language only.
  - Lemma 7.1 and Theorem 7.2 (the explicit family, with
    `Φ_0(ω) = ω^{ω^{1/2}}` and `Φ_1(ω) = ω^{ω^{7/2}}`, intersections `R`,
    `Z`, `C`, `Z[i]`). Lemma 8.1 (iterated Hahn coordinates at separated
    scales).
  - Lemma 9.1 (`Frac(Oz) = No`, uniformly over a set). Proposition 9.3
    (`Frac A_k(H) = Frac B_k(H)` for `H ≠ 0`). Lemma 10.1, Theorem 10.2
    (`1 + Σ t^{a_α}` is transcendental over `Frac B_k(H)` for any field `k`)
    and Corollary 10.3 (the factorial witness).
  - Theorem 11.2 (a conditional set-sized version in an `η_κ`-ordered
    divisible group of cardinality `κ`).
- **Research questions 1–10** (Section 12) and a proposed formalization
  decomposition (Section 13.2).

### From source 02 (Sections 15–27)

- **Exact rank test (Theorem 17.2).** For fields `k ⊆ F` and any ordered
  group `Γ`, `F ⊗_k k((t^Γ)) → F((t^Γ))` is injective with image `F[L]`, the
  series of finite coefficient rank over `k`; `M = Frac F[L]`, so `x ∈ M`
  iff some `q ≠ 0` has `crk_k(q)` and `crk_k(qx)` finite. Example 17.4: the
  geometric series `1/(1 − u t^g)` has infinite rank but lies in `M`.
  Corollary 17.5: `[F:k] < ∞` gives `E = F[L] = M`. For the explicit copies
  this is Corollary 22.1.
- **Base change (Section 18).** Coefficient extension, intermediate base
  change and coset slices (Lemmas 18.1–18.3), so independence proved over
  `k((t))(x)` survives in `F((t^Γ))` over `F k((t^Γ))` (Corollary 18.4).
- **Rapid coefficient degrees (Theorem 19.2).** In characteristic zero, if
  `d_n/d_{n−1} → ∞` and a family of subsets of `N_{>0}` has infinitely many
  private indices relative to every finite subfamily, the series
  `Σ_{n∈A} x^{d_n} t^n` are differentially independent over `k((t))(x)` for
  `t d/dt`; the relation may have arbitrary Laurent coefficients. Corollary
  19.4: continuum many, all with coefficients in `k(x)` (`d_n = n!`, binary
  prefixes). Corollary 19.5: the finite coefficient-field condition (Lemma
  8.2 here) is not sufficient even for algebraicity.
- **Private coefficient blocks (Theorem 20.2).** Series
  `Σ a_{b_i(n)} t^{ng}` with algebraically independent coefficients and
  private labels are differentially independent over the whole envelope
  `C_fg(F/k;Γ)`, via coefficient derivations that kill a finitely generated
  field (Lemma 20.1). Tree amplification gives `κ^{ℵ_0}` such series when
  `trdeg(F/k) ≥ κ` (Corollary 20.4); a set-local form covers class fields
  (Proposition 20.5); `F[L] ⊊ M ⊊ C_fg ⊊ E` (Corollary 20.6).
- **Exact Laurent degrees (Theorem 21.1).** For characteristic-zero set
  fields with `|k| ≤ 2^{ℵ_0}` and `trdeg(F/k) > 0`,
  `dtrdeg(F((t))/F k((t))) = trdeg(F((t))/F k((t))) = |F|^{ℵ_0}`, with no
  cardinal-arithmetic hypothesis; Corollary 21.2 for `k = Q, R, C`.
- **Omnific witnesses (Theorem 22.2).**
  `Y_α = Σ_{n≥1} ω^{ω^{15/4} − n ω^{7/2} + ω^{ψ(ω·α+n)}}` (ordinal
  arithmetic only in the label) is a purely infinite omnific integer with
  support of order type `ω`; `Δ^j Y_α = Σ n^j (…)`; the family
  `(Y_α)_{α∈On}` is differentially independent over `C_fg(K_0/R;G_1) ⊇ M`,
  with subfamilies of every set cardinal. `Y_0 = ω^{ω^{15/4}} S` extends
  source 01's witness. Corollary 22.3: finite-support elements of `E` lie in
  `M`, so `ℵ_0` is the sharp support cardinality. Remark 22.4: independence
  survives algebraic base extension.
- **Tail resilience (Theorem 23.3).** For every set `P ⊆ E` a tail
  `(Y_α)_{α≥α_0}` is differentially independent over `M⟨P⟩`, indeed over
  `C_fg(K_0/C_Θ;G_1)`; so no set generates `E` over `M`, algebraically or
  differentially (Corollary 23.4).
- **Arithmetic and surcomplex (Section 24).** `Frac(R_j) = K_j`,
  `Frac(R_0[R_1]) = M`, `Frac(O) = E` for `O = E ∩ Oz` (Lemma 24.1); for every
  set `S ⊆ O`, `O` is not integral over `R_0[R_1][S]` (Theorem 24.2); the same
  in `No(i)` and `Oz[i]`, with `Z_α = (1 + i)Y_α` (Theorem 24.4).
- **Research questions 11–22** (Section 26) and a proposed formalization
  decomposition (Section 27.2).

### From source 03 (Sections 28–41)

- **Theorem D: mixed-support independence.** Let `k` have characteristic
  zero, `Γ_0, Γ_1` divisible subgroups of one ordered group,
  `H = Γ_0 ∩ Γ_1` (possibly nonzero). If `a_i ∈ Γ_0` have `Q`-independent
  classes mod `H`, `b_i ∈ Γ_1` have distinct classes mod `H`,
  `{a_i + b_i}` is well ordered, and a family `𝒰` of index sets has
  *finite-exclusive infinitude* (every finite subfamily leaves each member
  infinitely many private indices, source 02's private-index property),
  then the `F_U = Σ_{i∈U} t^{a_i+b_i}` are algebraically independent over
  `k((t^{Γ_0})) k((t^{Γ_1}))`. No convex separation is needed. The proof
  (Section 30) uses coset independence (Lemma 30.1), Euler derivations of
  additive characters (Lemma 30.3), coordinate characters vanishing on
  `Γ_1` (Lemma 30.4) and a finite annihilator `Σ c_i ∂_i` with coefficients
  in `K_0` killing `K_1(u_1, …, u_m)` (Lemma 30.5). Also Proposition 30.2
  (`H = 0`: intersection `k`, linearly disjoint), Proposition 31.2 (a
  generator-sensitive form), Corollaries 31.3–31.4 (weights, translations,
  algebraic base extension).
- **Theorem E: maximal gap at every infinite cardinal.** With
  `e_α = ω^{-ι_0(α)}`, `f_α = ω^{-ι_1(α)}` (`ι_0(α) = 2·_ord α`,
  `ι_1(α) = ι_0(α) + 1`), `A_κ = span_Q{e_α}`, `B_κ = span_Q{f_α}`
  (interleaved, `A_κ ∩ B_κ = 0`, each of size `κ`):
  `trdeg(K_k(A_κ+B_κ)/K_k(A_κ)K_k(B_κ)) = 2^κ` for `k = R, C`; the factors
  are linearly disjoint and real closed / algebraically closed; witnesses
  `Ξ_U = Σ_{α∈U} ω^{r_α}` in `Oz` (Lemmas 32.1, 33.1). Corollary 33.2: the
  gap survives relative algebraic closure. Corollary 33.3: the omnific join
  has fraction-field transcendence degree `2^κ` over the ring generated by
  the two omnific factors.
- **Theorem F: an Archimedean family of primes.** With
  `λ_n = p_{2n}^{-3/2}`, `μ_n = p_{2n+1}^{-3/2}`, `ρ_n = λ_n + μ_n`
  (`p_n` the `n`th prime), `A = span_Q{λ_n}`, `B = span_Q{μ_n}` (dense in
  `R`), and binary-branch sets `𝔅_η` (Lemma 32.2):
  `P_η = 1 + Σ_{n∈𝔅_η} ω^{ρ_n}` are algebraically independent over
  `K_C(A)K_C(B)`, the degree is `2^{ℵ_0}` for `k = R, C` (Proposition 34.2),
  and each `P_η` is prime in `Oz` and in `Oz[i]`, pairwise nonassociate
  (Proposition 35.3, Corollary 35.4). Primality is **imported**: Theorem
  35.1 is the one-row theorem of Pitteloud and Biljakovic–Kochetov–Kuhlmann
  as stated by L'Innocente–Mantova (§1.3), pulled back through the constant
  term (Lemma 35.2) and localized to a set group.
- **Theorem G: a class example.** Explicit class groups `A_*`, `B_*` with
  zero intersection; `W_α = Σ_{n<ω} ω^{r_{ω·α+n}}` (ordinal labels) form an
  ordinal-indexed family in `Oz` independent over `K_k(A_*)K_k(B_*)`, with
  `2^κ`-sized independent sets for every `κ`; no set-sized transcendence
  basis (Lemma 36.1: the proof is local).
- **Section 37.** Strong endomorphisms fixing the compositum are the
  identity and strong relative derivations vanish (Proposition 37.2); yet
  `|Der_M(E)| = 2^{2^κ}`, `dim Ω_{E/M} = 2^κ` (Theorem 37.4; `2^c` and `c`
  in the Archimedean case), and for `k = C`, `|Aut(E/M)| = 2^{2^κ}` with
  only the identity strong (Theorem 37.5; `2^c` in the Archimedean case).
- **Merge remarks.** Remark 28.1 compares sources 02 and 03. Remark 36.2
  gives a second proof that source 01's witness `S` is transcendental over
  its compositum (Theorem D with `a_n = -ω^{ψ(n)}`, `b_n = n ω^{7/2}`, in
  the class-local form). Remark 37.6: by `opa:as:cor:setpairs`, an
  automorphism of the real join fixing `M` and preserving its omnific ring
  is the identity, so no nonidentity automorphism of Theorem 37.5 both
  commutes with conjugation and preserves the Gaussian omnific ring.
- **Research questions 23–32** (Section 39), a dependency audit, a finite
  verification model and a formalization roadmap (Section 41).

### What source 02 settles here

- **Research question 3** (exact description of ordinary composita) is
  answered in the separated case with trivial core, which is the case of
  Theorem C: the rank test characterizes `M`, Lemma 8.2's condition is not
  sufficient, the Laurent degrees are `|F|^{ℵ_0}` in the stated cardinal
  cases, and the class-sized join is described by independent families of
  every set cardinal, tail resilience and the absence of set generation, as
  the question asks (no set cardinal is assigned to the class). Open:
  non-separated groups, prescribed nonzero common cores, infinite algebraic
  coefficient extensions, and `|k| > 2^{ℵ_0}` with small positive
  `trdeg(F/k)` (Research questions 11, 14, 13, 12). Status notes sit in
  Section 1.6 and after Research question 3.
- Theorem 8.3 is strengthened for `S`: `S = ω^{−b} Y_0` with `ω^{−b}` a
  `Δ`-constant in `K_1`, so `S` is differentially transcendental over
  `C_fg(K_0/R;G_1)` (real case).
- No other question of this report, and no question of another report, is
  answered.

### What source 03 settles here

- **Research question 11** (non-separated amalgams): its transcendence-defect
  part is answered for explicit non-separated examples: `2^κ` for the
  interleaved groups of Theorem E at every infinite `κ`, `2^{ℵ_0}` for the
  dense Archimedean groups of Theorem F, and no set-sized basis for the class
  groups of Theorem G. The image of the compositum and a denominator
  criterion stay open (Research question 24).
- **Research question 3**, second part, is thereby also answered for these
  non-separated examples; the first part stays answered only in the
  separated case.
- **Research question 14** (nonzero cores) is continued, not answered:
  Theorem D allows `H ≠ 0` algebraically, but every example has `H = 0`.
- Research question 29 (compatibility of the hidden automorphisms) is
  partly answered in the merge by Remark 37.6, which rests on the
  omnific-preserving report's unrefereed `opa:as:cor:setpairs`.
- Status notes sit in Section 1.6, after Research questions 3, 11, 14, 21
  and 22, in Section 15.4, and in item M3. No other question of this report
  and no question of another report is answered.

## What the report does not claim

Section 14 collects source 01's non-claims: 24 from the source (S1–S24) and
8 added when it was written (W1–W8). Section 25.5 collects source 02's: 23
from the source (C1–C23) and 5 added in the merge (M1–M5). Section 38.4
collects source 03's: 25 from the source (J1–J25) and 6 added in the merge
(JM1–JM6). In brief:

- **The common field.** It is a full Hahn field on a set-sized divisible
  subgroup. It is not an arbitrary real closed or set-sized subfield, not
  the field generated by a parameter set, and not a non-Hahn subfield.
  Group sums are finite sums, and the joins are Hahn joins, not composita.
- **Strongness** is Hahn summability, not convergence.
- **Elementarity** is claimed only in the languages of ordered fields and of
  fields, formula by formula. Nothing is claimed in `(No, Oz)`, with the
  omega-map or with a derivation.
- **No compatibility** is claimed with the omega-map, the exponential,
  derivations, birthdays or simplicity. There is not even omega-map
  commutation: `Φ_0(ω) ≠ ω^{Φ_0(1)}`.
- **Scope (source 01).** No proper-class base `H` is treated. Theorem 11.2 is
  conditional on the existence of its group. No normalization, Picard group
  or projective module is computed. There is no class tensor product, class
  truth predicate or class-state recursion.
- **Not new (source 01).** The bounded-support transcendence mechanism of
  Section 10 is not new. It is reproved for the one-witness application. The
  non-fraction obstruction is L'Innocente–Mantova's Proposition 2.4.5. The
  ingredients are classical: the cut property, normal forms, Hahn arithmetic,
  the closedness criteria, a concrete saturation construction and standard
  Hahn functoriality. The coset slice is an elementary lemma, not a
  certified new theorem.
- **Source 02, method and scope.** The rank test is not a decision procedure,
  and the tensor fact is not new (it is `duals:prop:algebraic` of the
  three-duals report; part (iii) is new but immediate). The comparison with
  Krapp–Kuhlmann–Serra is conceptual. Infinite rank obstructs membership in
  `F[L]`, not in `M`. The rapid-degree theorem needs characteristic zero, a
  transcendental coefficient, unbounded degree ratios, private indices and a
  uniform `x`-degree; it does not rest on gaps in the outer support. The
  formula `|F|^{ℵ_0}` is not extended to infinite algebraic coefficient
  extensions, to `Γ = 0`, to groups without a suitable `λ`, or to
  `|k| > 2^{ℵ_0}` with small positive transcendence degree. Characteristic
  zero is essential (`∂^p = ∂` in characteristic `p`), and nothing is settled
  about algebraic transcendence in characteristic `p`.
- **Source 02, derivation and class level.** `Δ` is a diagonal Euler
  derivation: not Berarducci–Mantova, not Hardy type (not identified with
  Kuhlmann–Matusinski's), not exponential-compatible. No class transcendence
  basis and no set cardinal for the class degree; resilience is for set
  parameters only, and independence is not claimed over the
  differential-algebraic closure of `M⟨P⟩`. The algebraic-base remark does
  not compute the relative algebraic closure.
- **Source 02, arithmetic and questions.** Nonintegrality of `O/R_0[R_1][S]`
  computes no normalization, integral closure, Picard or class group or
  projective module. Nothing on Gonshor exponential compatibility,
  simplicity, initiality, birthday optimality, or a general membership
  algorithm. The complex versions use only coefficient separation.
  Research question 3 is not solved for non-separated amalgams, arbitrary
  cardinalities or prescribed common cores. The proofs do not import source
  01's recursion (Theorem 3.4) or the repository's automatic-strongness,
  curve-rigidity or quotient theorems.
- **Status.** No priority is certified for any source (their literature
  comparisons were targeted, and a search that finds nothing is not proof
  of novelty), no named conjecture is claimed solved, and there has been no
  peer review. Source 02's proof audit is author-side. There is no Lean code
  and no machine verification; the identifiers of Sections 13.2, 27.2 and 41.5 are
  proposals only. The production checks (compiling, rendering, visual
  inspection) do not verify the mathematics, and source 02's finite checks
  prove no independence, cardinal or class assertion.
- **Source 03, scope.** Not refereed, not independently reviewed, not
  Lean-checked; priority not certified; no named conjecture solved. New are
  only the mixed-support criterion and its combined maximality and
  arithmetic applications, not the classical ingredients; the incidence and
  almost-disjoint constructions are standard. Only the degree part of
  Research question 3 is answered, only for the constructed examples; no
  characterization of composita and no membership test. Proposition 31.2
  bounds no expression length.
- **Source 03, primality.** The one-row theorem (35.1) is imported, not
  proved; no new one-row theorem; the independence argument does not reprove
  factorization theory; Gaussian primality is proved separately, not
  inferred from real primality; a prime of `Oz[i]` is a unit of `No(i)`.
  Uncountable prime witnesses are not obtained (Research question 28).
- **Source 03, class and maps.** The class example uses explicit support
  subfields, not copies of `No`; no isomorphism `A_* ≅ No`; no
  `trdeg = On`; no class Hamel basis. The derivations are
  additive-character Hahn derivations, not Berarducci–Mantova and not
  exponential-compatible. The false identity `Frac(A_k(G)) = K_k(G)` is not
  used, and Corollary 33.3 is distinct from source 01's descent failure.
  Proposition 37.2 is conditional rigidity, not automatic strongness. The
  automorphisms of Theorem 37.5 are not claimed to preserve the real part,
  conjugation, `Oz`, order or exponentiation, and are not automorphisms of
  `No` or `Oz`.
- **Source 03, boundaries.** An infinite mixed sum need not be new (a
  geometric series); distinct cosets are necessary; finite supports cannot
  work; not every incidence family works; an independent set need not be a
  basis; characteristic zero is used twice (no verbatim characteristic-`p`
  version); no order-topological convergence, continuity classification or
  conjugation compatibility; Archimedean exponent groups do not make the
  fields Archimedean; `No` is not the base. Finite rational rank (Research
  question 23) and examples with `H ≠ 0` are not covered. The cardinal
  results use neither primality nor unreviewed class-embedding theorems.
- **Source 03, evidence.** The questions are not published problems
  (Question 32 is an implementation task). The finite checks prove nothing
  infinite and test no primality; the floating-point check is orientation
  only; a specialization typo was corrected before release. No Lean code;
  the Section 41.5 interfaces are proposals. The encyclopedia page was
  orientation only; there has been no external review.
- **Added at the write and the merge.**
  - (W1) No `isc:` Lean mapping; source 01 shipped no verification suite
    (source 02's suite tests none of source 01's theorems).
  - (W2) The lifts, the Oz clauses and the classification are the
    real-fixing case of the omnific-preserving report's classification (no
    priority is claimed relative to it). Corollary 6.1 extends its
    parameter theorem without its topological assertions.
  - (W3) Lemma 9.1, Proposition 9.3, the coset slice and Section 10
    duplicate results of the Diophantine and bounded-support reports.
  - (W4) Real fixing is a choice; nothing is claimed about intersections of
    exact-monomial copies that move reals.
  - (W5) The large-cardinal report's joint-dependence question is not
    answered.
  - (W6) No question of the omnific-preserving or bounded-support reports is
    answered.
  - (W7) Each source's statements about the collection are those of its pin.
  - (W8, M4, JM5) The proofs of all three sources were read during the write
    and the merges; that reading is not an independent proof review.
  - (M1–M2) Source 02's tensor fact is `duals:prop:algebraic`; its coset
    lemma is a variant of Theorem 5.4; its private-index and tree mechanisms
    are related to `tail:thm:surreal` and `bst:thm:independent`, and its tail
    resilience to `adr:sr:thm:tail`; source 02 cites none of them.
  - (M3) Research question 3 is answered only in the separated case and the
    cardinal cases.
  - (M5) The recorded run was repeated with identical counts; the shipped
    `build.sh` does not run unchanged under the shipped names.
  - (JM1) Research question 11 is answered only in its defect part and only
    for the explicit examples; Research question 14 is continued, not
    answered.
  - (JM2) Source 03 cites no other report; its finite-exclusive infinitude
    is source 02's private-index property, its branch code is
    `tail:eq:binarycode` minus one, its square-root independence is used in
    `tail:thm:surreal`, its one-row primality is cited in the Diophantine
    report, and `bst:cor:exactcard`/`bst:cor:realgroup` concern another base.
  - (JM3) Remarks 28.1, 36.2 and 37.6 are merge observations; 37.6 depends
    on the unrefereed `opa:as:cor:setpairs`.
  - (JM4) Source 03's statements about this report are those of its pin,
    before source 02; `[merge]` notes record where they are now incomplete.
  - (JM5) No `isc:hj:` Lean mapping; the proofs were read in the merge (not
    an independent review); only Theorem 35.1's wording was compared with
    L'Innocente–Mantova.
  - (JM6) The recorded run was repeated on a copy; the shipped `build.sh`
    does not run under the shipped names, and an adapted copy would
    overwrite a PDF and the record in its own directory.

## Relation to the neighbouring reports

Section 1.6 (source 01) and Section 15.6 (source 02) give these relations
with labels.

**[omnific-preserving-automorphisms](../omnific-preserving-automorphisms/)**
(`opa:`). At source 01's pin this report had no part on embeddings, so the
source's description of it as concerning "stabilizers and rigidity" was
accurate. Its Part III (`opa:as:`) was written in `20c4c9f`, after the pin.

- **Lifts.** The lifts `Φ_h` are the `ρ = id` case of the bottom-gap
  classification `opa:as:thm:classification`. Proposition 4.2's `Oz`
  clauses are its Step 5 (`opa:as:eq:classprops`). Proposition 4.4 is its
  uniqueness clause for real-fixing maps. The floor, standard-part and
  modulus clauses are not stated there.
- **Inner and outer levels.** Section 7's inner and outer levels are
  `opa:as:eq:innerlift` and `opa:as:lem:inner`, with
  `Φ_α = M_{1,ι_{σ_α}}`. The source's `ψ` is not `μ_12`.
- **Parameters.** Corollary 6.1 extends `opa:as:thm:parameters`, which gives
  two proper copies fixing `A ∪ R`. Here there is an `On`-indexed family
  whose exact intersection is a full Hahn field, jointly linearly disjoint
  over it.
- **Complex version.** The complex clauses are the `ε = 1`, `ρ = id` case of
  `opa:as:thm:complexembed`, parallel to `opa:as:cor:complexcopies`.
- **Real fixing is a choice.** The explicit ranges have a nonzero bottom
  gap, which contains `ω^{3α}` and, for `α = 0`, is the group of finite
  surreals. By `opa:as:thm:taylorcriterion`, copies with the same exponent
  map could therefore also move reals. The source takes `ρ = id`, which is
  consistent. Theorem 6.2 depends on this hypothesis
  (`opa:as:prop:overlap`).
- **Questions.** None is answered.
  - Research question 2 is the pair version of `opa:as:q:conjugacy`.
  - Research question 9 is `opa:as:q:elementary` for these maps.
  - Research questions 6 and 7, and 17 and 18 of source 02, lie inside
    `opa:as:q:exp`.
  - Theorem 6.3 touches `opa:as:q:composition` (image inclusion) inside one
    family only.
  - Research question 1 is related to `opa:as:q:units`, but asks about
    intersections.

**[transcendence-over-bounded-support](../transcendence-over-bounded-support/)**
(`bst:`), unchanged between source 01's pin and batch 31; batch 32 added its
Galois part (its Sections 11–19), which is not used here.

- Section 10's one-witness gap duplicates `bst:cor:onegap`, and the
  one-series case of `bst:thm:mainintro` (`bst:thm:independent`), as the
  source says. The single-series form at uncountable cofinality over an
  arbitrary coefficient field, finite fields included, is not stated
  there; its proof is that report's tail estimate and root count.
- The factorial witness is also used in `bst:thm:actualreal`, and, as a mere
  non-fraction, in `opa:as:ex:smallfrac`.
- Proposition 9.3 is the localization of `bst:prop:localdensity`. Since
  batch 32 that report also prints the general form, for every field `K` and
  every unital subring `D ⊆ K`, as `bst:gr:prop:fractions`.
- The coset slice is `bst:eq:projection`, and its linearity is
  `bst:lem:projection`. Theorem 5.4 (disjointness over the full Hahn field
  of the intersection group, with no cofinality hypothesis) is not stated
  there.
- Research question 8 is that report's programme.
- `bst:thm:independent` obtains `2^{cf G}` independent series over the
  bounded-support fraction field by coefficient codes at cofinally many
  indices, a private-index device over a different base, with a support-gap
  estimate instead of a derivation; related to source 02's Section 20, not
  cited by it.

Source 03 (Section 28.6) adds these relations; it cites none of these
reports.

- **tail-spans** (`tail:`): the branch sets of Lemma 32.2 are
  `tail:eq:Aalpha` with the code `tail:eq:binarycode` shifted down by one
  (source 03's `code(s) = N(s) − 1`), the family also used by Corollary
  19.4; the square-root independence behind Theorem F's exponents is the
  multiquadratic input of `tail:thm:surreal`, where the roots are
  coefficients.
- **omnific-diophantine-geometry** (`odg:`): the text after
  `odg:prop:irreduciblect` already cites primality of `1 + Σ ω^{1/k}` in
  `Oz` from the same sources; the `P_η` are a new explicit continuum
  subfamily, with constant term 1 as that proposition requires, and their
  primality in `Oz[i]` is new to the collection (a search found no other
  nonconstant prime of `Oz[i]`; this is not a priority claim).
- **set-sized-quotients-of-omnific-integers** (`osq:`): the argument of
  `osq:cor:primeexample` uses only primality and constant term 1, so each
  `Oz/(P_η)` is a proper-class domain with no nonzero set-sized image (a
  merge observation).
- **transcendence-over-bounded-support** (`bst:`): `bst:cor:exactcard` and
  `bst:cor:realgroup` give the same cardinals `2^κ` and `2^{ℵ_0}` over the
  bounded-support fraction field, a different base; consistent.
- **omnific-preserving-automorphisms** (`opa:`): Theorem 37.5's non-strong
  automorphisms are of a complex Hahn join, not of `Oz`, consistent with
  `opa:as:thm:main`; Remark 37.6 combines `opa:as:cor:setpairs` with
  Proposition 37.2.

**[three-duals-of-hahn-vector-spaces](../../surcomplex/three-duals-of-hahn-vector-spaces/)**
(`duals:`). Parts (i)–(ii) of Theorem 17.2 are, for `V = F`, the injectivity
paragraph before `duals:prop:algebraic` and that proposition (finite total
coefficient rank characterizes `K ⊗_k V` inside `V_Γ`). Part (iii), the
fraction-field test, is new but immediate. Source 02 does not cite it.

**[tail-spans-and-differential-transcendence](../tail-spans-and-differential-transcendence/)**
(`tail:`). `tail:thm:surreal` uses the same binary-prefix almost disjoint
family as Corollary 19.4 and private indices with a Vandermonde argument, to
give continuum many differentially independent series over `Q((t^Q))` for
the Berarducci–Mantova derivation, via the tail-span theorem
`tail:thm:tail`. Base, derivation and tool differ from Theorems 19.2 and
20.2. Related, not a duplicate; not cited by source 02.

**[autonomous-dilation-relations](../../surcomplex/autonomous-dilation-relations/)**
(`adr:`). `adr:sr:thm:tail` places a set of surcomplex parameters in the Hahn
field of the real span of their supports and finds a tail of an explicit
ordinal family whose dilation orbits are independent over that field;
`adr:sr:thm:kappa` gives set-sized families over a prescribed base. Both use
the support-closure step of Corollary 6.1 (the reciprocal note after
Corollary 6.1), and Theorem 23.3 has the same shape one normal-form level
deeper, for Euler jets.

**[omnific-diophantine-geometry](../omnific-diophantine-geometry/)**
(`odg:`). Lemma 9.1 is `odg:thm:fractions`.

**[large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)**,
placed after source 01's pin. Source 01's text cites it by name and question
title, not by label.

- Its strong map `H_j` is the lift `Φ_h` with `h = J`.
- Its question "Joint algebraic dependence of the images" asks whether
  `J(No)` and `H_j(No)` are linearly disjoint over the common field. That
  question is related to Theorem 5.4 but **not answered**: `J(No)` is not a
  full Hahn field on a subgroup, and the common field there is not one
  either.

**Research questions.** Questions 1, 3, 4, 5 and 10 were new with source 01;
Question 10 overlaps `opa:as:q:formal` in its Hahn-field kernel. Question 3
is now answered in the separated case, and its degree part also for explicit
non-separated examples (status notes in Section 1.6 and after the question).
Questions 11–22 come from source 02 and are new; 11 and 14 are the open part
of Question 3, 17 and 18 relate to Question 6, 19 to Question 4, 20 to
Question 7, and 22 overlaps Question 10. Questions 23–32 come from source 03
and are new: 23 is the smallest dense case of 11, 24 is the image part of
11, 26 and 27 continue 3 and 14, 29 is partly answered by Remark 37.6, 30
continues 21, and 32 overlaps 10 and 22.

## Source 02: Beyond Composita of Surreal Copies

| | |
|---|---|
| Manuscript | batch 34, manuscript 05; local number 02; archive `Surreal_Composita_Research` (delivered in `a4611ad`, placed in `a7a435f`) |
| Title | *Beyond Composita of Surreal Copies: Exact rank tests, differential transcendence, and omnific witnesses*, 29 pages, 23 September 2026 |
| Pin | `7b256e0792df7718995b816ad12a77bf56731f8f`; this report's `article.tex` was blob `7d5cfe644e7c902f2b594179c337a6c633350fc3` there |
| Contributes | the finite coefficient-rank test; base-change lemmas; rapid coefficient-degree differential independence; private coefficient blocks and trees over `C_fg`; exact Laurent degrees `|F|^{ℵ_0}`; the ordinal family `Y_α` of omnific witnesses; set-parameter tail resilience; nonintegrality after set adjunction; Gaussian versions; 12 research questions; a formalization plan; a 2,530-check finite suite |

- **Placement.** An addition, not a new report: it answers this report's
  Research question 3 in the separated case and extends the witness `S` of
  Theorem C. It is printed as Sections 15–27, after the ledger of
  non-claims (Section 14) and before the appendix, so that no existing
  number changes; its provenance is Appendix A.7 and its files Appendix A.8.
- **Since the pin** only three `[write]` sentences about the bounded-support
  report changed in this report; the sections source 02 used (7, 8 and 12)
  are unchanged, so its description of them is accurate.
- **Printed once.** Source 02's Subsections 8.1–8.2 re-derive the explicit
  copies (`ψ`, `h_j`, `Φ_j`, `G_j`, `K_j`, scale separation, re-expansion)
  with source 01's proofs; they are printed once, in Sections 7–8, with the
  correspondence and source 02's added observations (purely infinite
  elements, `R_j = K_j ∩ Oz`, `E ≅ K_0((t^{G_1}))`) in Section 22.1. The
  first clause of Lemma 24.1 is Proposition 9.2's `Frac(R_α) = K_α` for the
  explicit copies, kept because Lemma 24.1 needs it.
- **Renamed symbols.** See the table above; the formula for `Y_α` is
  verbatim.
- **Merge additions** (`[merge]`): Sections 15.4–15.6, the opening of
  Section 15, the provenance notes, the notes after Theorem 17.2, Lemma
  18.3, Corollary 19.4, Example 19.6, Theorem 22.2 and Lemma 23.1, the
  correspondence in Section 22.1, the list in Section 25.5 (C1–C23, M1–M5),
  notes after Research questions 14, 17, 19 and 22 and in Section 27, the
  reciprocal note after Corollary 6.1 (dilation report), the status notes
  on Research question 3, and the cleveref type hints described above.
- **Verification.** The proofs of Theorems 17.2, 19.2, 20.2, 21.1, 22.2,
  23.3, 24.2, 24.4 and their lemmas were read line by line in the merge; no
  error was found. Rechecked: `g, b ∈ G_1`, `λ(g) = 1`, `λ(b) = 0`,
  `Δτ = τ`, `Δω^b = 0`, `Y_0 = ω^{ω^{15/4}} S`, consecutive exponents of
  `Y_α` differing by `g + g_{α,n} − g_{α,n+1} > 0`. The source's theorem
  numbering was checked against its delivered PDF. This is not an
  independent review. The four new bibliography entries (Krapp–Kuhlmann–
  Serra, Kuhlmann–Matusinski, Berarducci–Mantova, Stacks Project) were not
  checked in the merge.

### Rerunning source 02's checks

`code/02-composita-verify.py` needs Python 3.10 or later and SymPy
(`data/02-composita-requirements.txt` pins `sympy==1.14.0`). It performs
2,530 exact finite checks in 21 categories (polynomial identities, finite
coefficient ranks, Vandermonde determinants, prefix trees, factorial growth,
Taylor coefficients, finite lexicographic models of the witness exponents,
the characteristic-`p` boundary and complex substitutions). It prints a JSON
report and writes a file **only** when given `--output`, so it does not
rewrite its own record unless told to. Run it on a copy, or with an output
path outside the report:

```sh
python code/02-composita-verify.py --output <scratch>/verification.json
```

Do not use `code/02-composita-build.sh` as shipped: it changes into its own
directory and runs `python3 verify.py --output verification.json` and then
`latexmk` on `article.tex`, names that do not exist in `code/` (the
delivered `verify.py` is `02-composita-verify.py`, and source 02's manuscript
is not shipped). An adapted copy would write `verification.json` next to the
script, not over `data/02-composita-verification.json`.

In the merge the program was run on a copy with Python 3.14.4 and SymPy
1.14.0: all 2,530 checks passed with the same 21 category counts as the
recorded run; the only difference in the JSON record is the Python version
(3.13.5 recorded). The checks prove no independence, cardinal or class
assertion.

## Source 03: Maximal Transcendence in Hahn Joins

| | |
|---|---|
| Manuscript | batch 35, manuscript 01; local number 03; archive `Surreal_Hahn_Joins_Research`, inner directory `maximal_transcendence_hahn_joins` (delivered in `267b910`, placed in `dec8d56`) |
| Title | *Maximal Transcendence in Hahn Joins: Mixed-support independence and prime omnific integers*, 27 pages (cover, contents, 23 numbered pages), 23 September 2026; author line "AI-assisted research manuscript" |
| Pin | `f388f950f44664f21f50f04b8ac74dab56c8ff2f`; this report's `article.tex` was blob `7d5cfe644e7c902f2b594179c337a6c633350fc3` there, the same snapshot as source 02's pin, before source 02 was merged |
| Contributes | the mixed-support independence criterion (no convex separation); exact degree `2^κ` for interleaved real closed and algebraically closed factors at every infinite `κ`, with omnific witnesses and an arithmetic-join gap; an Archimedean continuum family `P_η` independent over the compositum and prime in `Oz` and `Oz[i]` (one-row primality imported); a class example with no set-sized transcendence basis; strong rigidity versus `2^{2^κ}` relative derivations and automorphisms; 10 research questions; a dependency audit and a formalization roadmap; a five-check finite suite |

- **Placement.** An addition, not a new report: it takes Research question 3
  as its target and answers the defect part of Research question 11 for
  explicit examples. It is printed as Sections 28–41, after source 02's
  sections and before the appendix, so that no existing number changes; its
  provenance is Appendix A.9 and its files Appendix A.10.
- **Since the pin** source 02 was merged (Sections 15–27). Source 03 did
  not see it; `[merge]` notes in Sections 28.4, 28.6, 38.1 and after
  Research questions 24 and 27 record where its statements are now
  incomplete (the degree question and an exact membership test in the
  separated case, class families in actual copies). The sections of source
  01 it used (8 and 12) are unchanged.
- **Printed once.** Source 03 re-derives no theorem of the report. Its
  Proposition 30.2 is the case `H = 0` of Theorem 5.4 and its Lemma 30.3 is
  Lemma 16.2 for `F = k`; both are printed where the source proves them,
  with a `[merge]` note, because the source's proofs are self-contained.
- **Renamed symbols.** See the table above; the formulas for `P_η`, `Ξ_U`
  (source `Z_U`) and `W_α` are otherwise verbatim.
- **Merge additions** (`[merge]`): Sections 28.4–28.7 and the opening of
  Section 28, Remarks 28.1, 36.2 and 37.6, notes after the fraction-field
  sentence of Section 29.3, Proposition 30.2, Lemma 30.3, Definition 31.1,
  Corollary 31.4, (32.1), Corollary 33.3, Lemma 34.1, Theorem 35.1, Lemma
  35.2, (36.1) and the proof of Theorem G, the note after the table of
  Section 38.1, Section 38.4 (J1–J25, JM1–JM6), notes on Research questions
  23, 24, 26, 27, 29, 30 and 32 and in Section 41, and Appendices A.9–A.10.
  In sources 01 and 02: the title page and subtitle, Section 1.6, after the
  proof of Theorem C, Research questions 3, 11, 14, 21 and 22, Section 15.4,
  the start of Section 14, items W1 and M3, Appendices A.1 and A.6, and five
  bibliography entries (Conway, Hahn, Kaplansky, Pitteloud,
  Biljakovic–Kochetov–Kuhlmann), not checked in the merge.
- **Verification.** The proofs of Section 30 to Theorem 37.5 were read line
  by line in the merge; no error was found. Rechecked: pairwise distinct
  mixed exponents and distinct cosets `b_i + Γ_0`; leading exponent of
  `r_α − r_β`; the code intervals `[2^m − 1, 2^{m+1} − 2]` and the branch sets
  `{1,3,7,15,…}`, `{2,6,14,30,…}`; `ρ_0 ≈ 0.5460`; the cross product and
  `30y_1 − 24y_2 − 6y_3`; `Σ_{r=1}^{4} C(16,r) 2^r = 34,112`; the interleaving
  `e_0 = 1 > f_0 = ω^{-1} > e_1 = ω^{-2}`; the source's numbering against a
  build of its text. Theorem 35.1 was compared with the account in
  L'Innocente–Mantova's arXiv v5, §1.3 (Pitteloud's primes `1 + b` in
  `K((R^{≤0}))` remain prime in `K((G^{≤0}))` for every `G ⊇ R`); the
  original papers were not read. This is not an independent review.

### Rerunning source 03's checks

`code/03-hahn-joins-verify.py` needs Python 3 and SymPy (no requirements
file was delivered; the recorded run used SymPy 1.14.0). It prints five
PASS lines: an exact cross-product annihilator for two generators and a
quotient; the nonvanishing mixed derivative `30y_1 − 24y_2 − 6y_3`; all
34,112 Boolean patterns on up to four subsets of a four-point universe (the
finite analogue of Lemma 32.1, without its `ξ` coordinate); eight periodic
branches through depth 32 with at least 29 exclusive nodes; and the decrease
of the first ten `ρ_n` in floating point (orientation only). It writes no
file; redirect its output outside the report:

```sh
python code/03-hahn-joins-verify.py > <scratch>/verification.txt
```

Do not use `code/03-hahn-joins-build.sh` as shipped: it changes into its own
directory, runs `pdflatex` three times on `article.tex` (overwriting
`article.pdf` there) and then `python3 verify.py > verification.txt`
(rewriting that record). Under the shipped names it stops at the first
`pdflatex` run, since `code/` has no `article.tex` and the script uses
`set -e` (tested on a copy; it leaves a `texput.log`); an adapted copy would
write `verification.txt` next to the script, not over
`data/03-hahn-joins-verification.txt`.

In the merge the program was run on a copy with Python 3.14.4 and SymPy
1.14.0: all five checks passed, and apart from line endings the output
differs from the recorded run only in the Python version line (3.13.5
recorded). The checks prove no infinite, cardinal or primality assertion.

## Provenance (Appendix A)

- **Source 01 pin and placement.** The pin is
  `bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59`. The manuscript was placed as a
  new report because it answered no named question and because its spine
  (independence, exact intersections and descent of full copies) belonged to
  no existing report.
- **Repository statements at the pins.** Source 01 compared itself with the
  catalogue, the omnific-preserving report and the bounded-support report at
  its pin; its statements stand as of that pin (Appendix A.2), and the later
  Part III of the omnific-preserving report is what Section 1.6 adds. Source
  02 compared itself with this report (two line ranges read for substance,
  the README for its inventory) and consulted the catalogue and two other
  READMEs for orientation (its source audit).
- **L'Innocente–Mantova.** This reference was checked on arXiv version 5 of
  22 January 2024. The journal DOI `10.1016/j.aim.2024.109513` is listed
  there; the volume number was not checked. Fact 2.1.1 is the closedness
  criterion. Proposition 2.4.5 states, for the `κ`-bounded Hahn field, that
  `Frac(Z + K((G^{<0})))` is the whole field if and only if `cf(G) ≥ κ`.
  For a set-sized `G` it therefore gives the non-fraction obstruction (not
  transcendence), with `Frac(Oz) = No` as the class case. The source's
  citations of it are accurate.
- **Ehrlich–Kaplan.** Only the title and authors were checked. Gonshor, van
  den Dries–Ehrlich, Marker and the encyclopedia page were not checked.
- **Checks during the write.** The main proofs of source 01 (Lemmas 3.1–3.2,
  Theorem 3.4, Section 4, Section 5, Theorems 6.2–6.3, Sections 7–10 and
  Theorem 11.2) were read when the report was written, and no error was
  found. The only finding is an understatement: Proposition 9.2 says that no
  common denominator satisfies both containments, and in fact it satisfies
  neither.
- **Source 02** is described in the section above and in Appendix A.7.
- **Source 03** is described in the section above and in Appendix A.9. Its
  delivered README and Appendix D state that its repository comparison was
  targeted (this report's compositum result and question, and the catalogue
  for neighbouring topics), that L'Innocente–Mantova's arXiv v5 and a
  publisher record for Pitteloud were consulted for the primality input,
  and that a user-supplied encyclopedia page was orientation only.

## Build

TeX Live or MiKTeX with lmodern, microtype, geometry, amsmath/amssymb/amsthm,
mathtools, mathrsfs, enumitem, booktabs, array, longtable, xcolor, fancyhdr,
xurl, hyperref and cleveref. No external figures, bibliography database or
downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX 1.40.29) has 108 pages. It has no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull or underfull boxes; so
had the committed 70-page text before the batch-35 merge, and the 34-page
text before the batch-34 merge. The title page was tightened (one subtitle
line added, the date joined to the author line) so that it still fits on
one page. Source 01's delivered text
builds equally cleanly to 25 pages. Running pdflatex three times instead of
latexmk also resolves the references and the table of contents.

Source 01's delivered README reports its own build with pdfTeX 1.40.26 and
latexmk and a visual inspection of all 25 rendered pages; source 02's
`BUILD_AUDIT.json` reports a pdfTeX 1.40.26 build of its 29-page PDF with no
undefined references, overfull boxes or LaTeX warnings, and rendering checks.
Source 03's delivered README reports a build with no unresolved references,
missing citations or box warnings and a contact-sheet inspection of all 27
rendered pages. Those renderings and PDFs are not shipped. These production
checks do not verify the mathematics.
