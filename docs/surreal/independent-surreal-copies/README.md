# Independent Surreal Copies and Arithmetic Intersections

**Prescribed Hahn cores, algebraic independence, two transcendental descent obstructions, and composita**

This is a research report dated 23 September 2026, built from two
manuscripts. Author line of both: AI-assisted research draft (prepared for
Vladimir Reshetnikov).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 31, manuscript 06 | `Surreal_Independent_Copies` (main file `independent_surreal_copies.tex`, 25-page PDF) | `bcac55a` | `9d28e28` | Sections 1–14, Appendix A.1–A.6 (written in `781b19e`) |
| 02 | batch 34, manuscript 05 | `Surreal_Composita_Research` (*Beyond Composita of Surreal Copies: Exact rank tests, differential transcendence, and omnific witnesses*, 29-page PDF) | `7b256e0` | `a7a435f` | Sections 15–27, Appendix A.7–A.8 |

Every result, proof, example, question and limitation of both manuscripts is
printed. Material that source 02 re-derives from source 01 (the explicit
copies and the re-expansion) is printed once and credited. The report is
AI-assisted and unrefereed. **Independent proof review and formalization are
pending.**

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 70 pages (unnumbered title page,
                                         contents pages 1–2, then pages 3–69)
README.md                                this guide
02-composita-SOURCE_AUDIT.md             source 02's source and novelty audit, as delivered
02-composita-PROOF_AUDIT.md              source 02's author-side proof audit, as delivered
code/02-composita-verify.py              source 02's exact finite checks (SymPy)
code/02-composita-build.sh               source 02's build script (checks, then its PDF; see below)
data/02-composita-verification.json      source 02's recorded run: 2,530 checks in 21 categories
data/02-composita-requirements.txt       source 02's pin, sympy==1.14.0
data/02-composita-BUILD_AUDIT.json       source 02's build and PDF-inspection record
```

Source 01's package contained only the article, its PDF and a README, so it
has no verification suite. For both sources the delivered README and PDF are
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
which is not in the collection.

## Labels and numbering

Every label in `article.tex` carries the prefix `isc:`. Source 01's 62 labels
are kept, unchanged after the prefix, with the twenty added when it was
written (`isc:sec:conventions`, `isc:sec:collection`, `isc:sec:nonclaims`,
seven appendix labels `isc:app:*`, and ten labels on unlabelled remarks and
subsections): 82 labels. The merge of source 02 added **111** labels, all
with the sub-prefix `isc:cp:` (193 in total). No label was renamed or
removed, and no pre-existing theorem, section, equation or question number
changed: the `.aux` numbers of all 82 earlier labels were compared with a
build of the committed text. No `isc:` label has a Lean mapping in the
[formalization ledger](../../FORMALIZATION.md).

Source 02's section *n* is Section *n* + 14 here (*n* = 1, …, 12), and every
numbered statement keeps its position: its Theorem *n.m* is Theorem
(*n* + 14).*m* here. Its Questions 1–12 are Research questions 11–22; its
Appendices A and B are Section 27; its notation index is folded into the
table of Section 15.5.

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
no symbol of source 01 was renamed.

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

Tempting false readings printed in Section 15.5: "finite coefficient rank is
necessary for membership in `M`" (only for `F[L]`; `M` contains a geometric
series of infinite rank); "`Δ` is a surreal derivation" (it is a diagonal
Euler derivation of the explicit join, not Berarducci–Mantova, Hardy type or
exponential-compatible). This `L` is not the common field `L_k`, `λ` is not a
coset slice `λ_{g,H}`, and `F` is a coefficient field, not the witness `F` of
Theorem B.

## What the report claims

Theorem numbers are those of the built `article.pdf`. For Sections 1–14 they
agree with source 01's delivered PDF, and for Sections 15–27 they are source
02's shifted by fourteen. Remarks and warnings share the theorem counter, so
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

## What the report does not claim

Section 14 collects source 01's non-claims: 24 from the source (S1–S24) and
8 added when it was written (W1–W8). Section 25.5 collects source 02's: 23
from the source (C1–C23) and 5 added in the merge (M1–M5). In brief:

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
- **Status.** No priority is certified for either source (their literature
  comparisons were targeted, and a search that finds nothing is not proof
  of novelty), no named conjecture is claimed solved, and there has been no
  peer review. Source 02's proof audit is author-side. There is no Lean code
  and no machine verification; the identifiers of Sections 13.2 and 27.2 are
  proposals only. The production checks (compiling, rendering, visual
  inspection) do not verify the mathematics, and source 02's finite checks
  prove no independence, cardinal or class assertion.
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
  - (W8, M4) The proofs of both sources were read during the write and the
    merge; that reading is not an independent proof review.
  - (M1–M2) Source 02's tensor fact is `duals:prop:algebraic`; its coset
    lemma is a variant of Theorem 5.4; its private-index and tree mechanisms
    are related to `tail:thm:surreal` and `bst:thm:independent`, and its tail
    resilience to `adr:sr:thm:tail`; source 02 cites none of them.
  - (M3) Research question 3 is answered only in the separated case and the
    cardinal cases.
  - (M5) The recorded run was repeated with identical counts; the shipped
    `build.sh` does not run unchanged under the shipped names.

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
is now answered in the separated case (status notes in Section 1.6 and after
the question). Questions 11–22 come from source 02 and are new; 11 and 14
are the open part of Question 3, 17 and 18 relate to Question 6, 19 to
Question 4, 20 to Question 7, and 22 overlaps Question 10.

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

## Build

TeX Live or MiKTeX with lmodern, microtype, geometry, amsmath/amssymb/amsthm,
mathtools, mathrsfs, enumitem, booktabs, array, longtable, xcolor, fancyhdr,
xurl, hyperref and cleveref. No external figures, bibliography database or
downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX 1.40.29) has 70 pages. It has no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull or underfull boxes; so
had the committed 34-page text before the merge. Source 01's delivered text
builds equally cleanly to 25 pages. Running pdflatex three times instead of
latexmk also resolves the references and the table of contents.

Source 01's delivered README reports its own build with pdfTeX 1.40.26 and
latexmk and a visual inspection of all 25 rendered pages; source 02's
`BUILD_AUDIT.json` reports a pdfTeX 1.40.26 build of its 29-page PDF with no
undefined references, overfull boxes or LaTeX warnings, and rendering checks.
Those renderings and PDFs are not shipped. These production checks do not
verify the mathematics.
