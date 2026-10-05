# Derivative Supports of x^(x^a)

**Leading asymptotics for every integer exponent and for the half exponent; fixed-defect cancellations for rational, algebraic and irrational exponents; Hermite limits on fixed defects at the half exponent**

This is a research report of ProveIt's research-report collection (category
`generating-functions-and-asymptotics`, subcategory
`oeis-sequence-asymptotics`), written on 1 October 2026 and extended by
Part IV on 5 October 2026. It is built from **eight manuscripts**, all dated
1 October 2026 and all carrying the author line "Research note prepared for
Vladimir Reshetnikov with OpenAI":

- **seven of batch 72A** (Parts I–III). Six of them are the archives listed
  below; the seventh, 20r, was never delivered on its own and arrived only
  inside archive 20. All seven arrived in `1512ef835` and were placed in
  `d292c6765`.
- **an eighth, source 35** (Part IV): Report 59 of the session bundle of
  Reports 1–243, which arrived in `60f54ea06`; placed in this report by
  `36571ae0e` (batch 100 of the intake).

| Source | Manuscript | Archive (delivered title, PDF length) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 28 (base) | batch 72A, 28 | `ProveIt_All_Integer_Exponent_Derivative_Supports` (*Derivative Supports of x^(x^a): a common leading asymptotic for every fixed positive integer exponent*, 10 pp.) | `ca81647a9` | `d292c6765` (base of a new merge) | Sections 3–11 |
| 31 | batch 72A, 31 | `ProveIt_A293239_Leading_Asymptotic` (*The Leading Asymptotic of OEIS A293239: sparse zeros of the Lehmer–Comtet triangle*, 8 pp.) | `ca81647a9` | `d292c6765` | Section 12 (second route at a = 1) |
| 34 | batch 72A, 34 | `ProveIt_A290268_Leading_Asymptotic` (*The Leading Asymptotic of OEIS A290268*, 11 pp.; main file plus `tanh_sections.tex`) | `ca81647a9` | `d292c6765` | Section 13 (second route at a = 2) |
| 26 | batch 72A, 26 | `ProveIt_Half_Exponent_Derivative_Supports` (*Derivative Supports of x^(√x): a leading-density theorem with two infinite extra-cancellation families*, 7 pp.) | `ca81647a9` | `d292c6765` | Section 14 |
| 20r | batch 72A, 20r (embedded) | inside `ProveIt_Algebraic_Exponents_and_Cancellation_Frequencies`, as `Algebraic_Exponents_and_Cancellation_Frequencies/rational_companion_source.zip`, folder `Rational_Exponent_Fixed_Defects` (*Reflection and Finite Exceptions: fixed defects in derivatives of x^(x^a) for positive rational a ≠ 1*, 6 pp.) | `ca81647a9` | `d292c6765` | Sections 15, 16 |
| 20 | batch 72A, 20 | `ProveIt_Algebraic_Exponents_and_Cancellation_Frequencies` (*Algebraic Degrees and Exact Cancellation Frequencies: two fixed-defect extensions for derivatives of x^(x^a)*, 4 pp.) | none named | `d292c6765` | Sections 15, 17 |
| 16 | batch 72A, 16 | `ProveIt_Irrational_Exponents_Effective_Cancellation_Bounds` (*Effective Bounds for Irrational Exponents: fixed-defect cancellations in derivatives of x^(x^a)*, 6 pp.) | `ca81647a9` | `d292c6765` | Sections 15, 18 |
| 35 | bundle Report 59 (batch 100) | `ProveIt_Half_Exponent_Hermite_and_Finiteness` (*Hermite Limits and Finite Cancellation: Fixed defects in derivatives of x^(√x)*, 8 pp.), arrived `60f54ea06` | `ca81647a9` | `36571ae0e` (addition) | Part IV, Sections 21–24 |

The pin `ca81647a9` is the commit of the host report
`power-tower-derivative-term-counts` that each source inspected. The zip
entry times show that the notes were written in the order 34, 31, 28, 26,
35, 20r, 20, 16, between 01:24 and 04:21 PDT on 1 October 2026: source 35's
files date from 02:51–03:23, a few minutes before 20r (03:30–03:41). No
source cites another, except that 20 cites 20r as its companion. The number
35 continues the report's file-prefix sequence after 34; no batch-72A
manuscript was numbered 35.

Every result, proof, example, remark, question and limitation of the eight
manuscripts is printed. Duplicated results are printed once, with every
source that proved them named, and genuinely different proofs are kept as
second routes (Section 1.2 of the article; for Part IV, Table 3 in Section
21.2). **Status: AI-assisted and unrefereed. None of the report's results is
formalized in Lean or Rocq.** Placement beside the repository's Lean library
for A290268 confers no formal status on it (see "Relation to neighbouring
material").

```
README.md                                         this guide (replaces source 28's delivered README)
article.tex                                       the report (replaces source 28's delivered article.tex)
article.pdf                                       the compiled report, 71 pages (unnumbered title page,
                                                  contents pages 1-3, text pages 4-69, references page 70)
code/16-irrational-check_low_defect_injectivity.py   source 16: low-defect quadratic forms (SymPy; prints, writes no file)
code/16-irrational-verify.py                         source 16: degree, parity, structural point, elimination (SymPy)
code/20-algebraic-replay_low_counts.py               source 20: congruence-product counts, 102 cases (standard library)
code/20r-rational-replay_independent.py              source 20r: independent discriminant and differentiation replay (standard library)
code/20r-rational-verify.py                          source 20r: symbolic residuals and quartic certificates (SymPy)
code/26-half-exponent-verify_half_coefficients.py    source 26: transform and diagonal identities, scan to N = 150 (standard library)
code/28-all-integer-verify_general_coefficients.py   source 28: 631 exact identities, a = 1..8 (standard library)
code/31-a293239-check_saddle_normalization.py        source 31: numerical Gaussian-factor diagnostics (mpmath)
code/31-a293239-verify_coefficients.py               source 31: 510 tanh identities, recurrences to order 200 (standard library)
code/34-a290268-verify_curvature_seed.py             source 34: rational Taylor inequalities at T = 14/5 (standard library)
code/34-a290268-verify_derivative_counts.py          source 34: exact derivative-count regression to N = 200 (standard library)
code/34-a290268-verify_tanh_identity.py              source 34: 432 tanh-coefficient comparisons (standard library)
code/35-hermite-birational_model.py                  source 35: both birational maps of the defect-four quartic, exceptional points (SymPy)
code/35-hermite-check_bell_normalization.py          source 35: 11,935 Bell-normalization identities, N <= 50, r <= 10 (standard library)
code/35-hermite-check_quartics.py                    source 35: completion of squares, discriminants of the two quartics (SymPy; reads hermite_checks.json)
code/35-hermite-verify_hermite.py                    source 35: residuals, Hermite limit, G_r, odd factor, root shifts, Laguerre edges, r <= 10 (SymPy)
data/16-irrational-checks.json                       recorded output of 16-irrational-verify.py
data/20-algebraic-replay_low_counts.json             recorded output of 20-algebraic-replay_low_counts.py
data/20r-rational-certificates.json                  recorded output of 20r-rational-verify.py (degree-18 discriminant factors)
data/20r-rational-replay_independent.json            recorded output of 20r-rational-replay_independent.py
data/26-half-exponent-half_coefficient_checks.json   recorded output of 26-half-exponent-verify_half_coefficients.py
data/28-all-integer-general_coefficient_checks.json  recorded output of 28-all-integer-verify_general_coefficients.py
data/31-a293239-coefficient_checks.json              recorded output of 31-a293239-verify_coefficients.py
data/31-a293239-saddle_normalization.json            recorded output of 31-a293239-check_saddle_normalization.py (diagnostics, not proof)
data/34-a290268-curvature_seed.json                  recorded output of 34-a290268-verify_curvature_seed.py
data/34-a290268-derivative_counts.json               recorded output of 34-a290268-verify_derivative_counts.py (embeds a timing)
data/34-a290268-tanh_identity_checks.json            recorded output of 34-a290268-verify_tanh_identity.py
data/35-hermite-birational_model.json                recorded output of 35-hermite-birational_model.py
data/35-hermite-check_bell_normalization.json        recorded output of 35-hermite-check_bell_normalization.py
data/35-hermite-check_quartics.json                  recorded output of 35-hermite-check_quartics.py
data/35-hermite-hermite_checks.json                  recorded output of 35-hermite-verify_hermite.py
```

Every file in `code/` and `data/` is byte-identical to the delivery; the
prefix (`NN-short-slug-`) is the only change to its name. The 20r files were
extracted from the members of `rational_companion_source.zip` inside archive
20. Not shipped, and surviving only in `1512ef835`: the manuscripts, READMEs
and PDFs of sources 31, 34 (with its `tanh_sections.tex`, printed in Section
13), 26, 20 and 16; source 28's delivered PDF; source 20r's `article.tex`,
`article.pdf` and `README.md`; archive 20's `rational_companion.pdf` and the
companion zip itself; and the seven copies of the Linux build wrapper
`build_local.sh`, one per package. Not shipped from source 35, and surviving
only in `60f54ea06` (`git show
60f54ea06:docs/incoming/ProveIt_Half_Exponent_Hermite_and_Finiteness.zip >
x.zip`): its `article.tex`, `article.pdf` and `README.md` (printed as Part
IV) and its `build_local.sh`, a byte copy of the same generic build wrapper,
which is already tracked elsewhere in the repository. No package had a
checksum manifest.

## Labels and numbering

Every label in `article.tex` carries the prefix `pte:`; the manuscripts' own
prefixes are kept as sub-prefixes: `pte:ga:` (28), `pte:lc:` (31), `pte:as:`
(34, including its tanh sections), `pte:he:` (26), `pte:rf:` (20r), `pte:ac:`
(20), `pte:ir:` (16) and `pte:hm:` (35). The staged base `article.tex` had
**36** labels (all source 28's, unprefixed). The report written on
1 October 2026 had **210**; with Part IV it has **258**, all distinct:

- **175** of the **186** delivered labels of the batch-72A sources (28: 36,
  31: 28, 34: 42, 26: 27, 20r: 24, 20: 13, 16: 16), each with `pte:` in front
  and otherwise unchanged. Every `\ref` and `\eqref` was updated before
  anything cited them. The integer-triangle lemma, proved identically in 28,
  31, 34 and 26, is printed once as Lemma 9.1 and carries all four labels
  (`pte:ga:lattice`, `pte:lc:lattice`, `pte:as:lattice`, `pte:he:lattice`).
- **11** delivered labels are not printed, because they name equations
  printed once under source 20r's label (Section 15):
  `ac:physical`, `ir:physical` → `pte:rf:physical`;
  `ac:bridge`, `ir:bridge` → `pte:rf:bridge`;
  `ac:residual`, `ir:residual` → `pte:rf:residual`;
  `ac:center`, `ir:K` → `pte:rf:center`;
  `ac:even`, `ir:even` → `pte:rf:even`;
  `ac:edges` → `pte:rf:edgeeven`, `pte:rf:edgeodd`.
- **35** labels for parts, sections and the two tables of Parts I–III
  (`pte:part:*`, `pte:sec:*`, `pte:tab:*`).
- **All 25** delivered labels of source 35 (`hm:*` → `pte:hm:*`), including
  those of equations that specialize earlier ones (for instance
  `pte:hm:bridge` is `pte:rf:bridge` at a = 1/2; the article says so at
  each).
- **23** labels written for Part IV: `pte:part:hermite`, thirteen
  `pte:sec:hm-*`, the tables `pte:tab:hmroutes` and `pte:tab:hmnotation`, the
  remarks `pte:hm:rem:readme` and `pte:hm:rem:contribution`, the window
  equation `pte:hm:window` and the four questions `pte:hm:q:*`.

Part IV was appended after the unnumbered part "Scope, verification and
provenance" (Section 21.4 of the article says why), so no existing label,
section, theorem, equation or citation number changed; this was checked
against the `.aux` of a build of the 1 October text. The build has no
undefined, multiply defined or mistyped references. No label has a Lean or
Rocq mapping. Theorem numbers below are those of the built `article.pdf`.

## How the eight were merged

- **One theorem, three proofs.** Source 28 proves A_a(N) = N²/2 + o_a(N²) for
  every fixed positive integer a (Theorem 3.1). Sources 31 (a = 1, OEIS
  A293239) and 34 (a = 2, OEIS A290268) proved those two cases independently,
  earlier the same day, by the same contour method; none of the three cites
  another. The theorem is stated once. 31's and 34's statements are printed
  as Corollaries 12.1 and 13.1 in their own forms (density zero of
  Lehmer–Comtet zeros; lim a(N)/N² = 1/2), each followed by its complete
  proof as a second route, because those proofs are more explicit at their
  exponent (31: the critical-point classification and the fold
  e^T = 1 + T + T², ρ* ≈ 1.29843; 34: monotone critical curve, real-saddle
  positivity on the whole strict real region, a rational curvature seed).
- **Shared setup.** Sources 20r, 20 and 16 open with the same centered
  coefficient identity, printed once in source 20r's words (Section 15) with
  source 16's degree lemma (Lemma 15.1).
- **Implied theorem.** Source 20's Theorem 17.1 (finiteness on r ≥ 4D+2 for
  algebraic a of degree D) is implied by 20r's Theorem 16.1 (rational a,
  r ≥ 4) and 16's Theorem 18.1 (irrational a, every r ≥ 2). Its proof (field
  degrees, Siegel over Q(a)) is printed as a second route; its counting
  Theorem 17.2 and window Corollary 17.3 are new.
- **One pair of families.** Source 26's Theorem 14.3 (two infinite families of
  non-reflection zeros at a = 1/2) is 20r's residuals (16.12) at a = 1/2, a
  computation recorded after Theorem 14.3, and source 20's endpoint remark
  counts the families. The families are stated once, as Theorem 14.3.
- **Implied clause.** The transcendental clause of 16's Theorem 18.1 also
  follows from 28's Corollary 10.1.
- **Re-derivations of the host** are kept as second routes with the host
  statement cited: 28's Proposition 3.2 at a = 2 (host Theorem 3.7),
  Theorem 11.1 at a = 1, 2 (host Proposition 2.15, Theorems 3.16–3.17) and
  the branch-cut formula (host Proposition 3.30); 31's expansion and count
  (host Theorems 2.3, 2.7); 34's coefficient model, tanh formula (host
  Proposition 3.6, which 34 does not cite) and its upper bound
  (N+1)(N+2)/2, weaker than host Theorem 3.14.
- **Part IV, an addition (5 October 2026).** Source 35 is printed whole, in
  its own order, as Part IV (Sections 22–24), after its provenance and
  notation (Section 21). About half of it re-derives, at a = 1/2 and by the
  same route, results already here, and those are printed as **second
  routes**, never as new (Table 3 of the article): the exact residual and
  its weighted degree ((15.3)–(15.4), Lemma 15.1), the exact odd factor
  ((15.6)), the defect-two and defect-three formulas and counts (Theorem
  14.3 with source 20's endpoint remark), the Laguerre edges ((16.1)–(16.2);
  source 35's odd edge is half of 20r's because it divides by k + 2(r−1) =
  2K), and both finiteness theorems, Theorems 23.1 (defects 4, 5) and 23.3
  (every r ≥ 4), which are 20r's Theorem 16.1 at a = 1/2. New in Part IV: the
  first correction G_r of the Hermite limit (Theorem 22.1), eventual simple
  real roots with explicit shifts (Theorem 22.2), at most ⌊r/2⌋ zeros per
  large order, the O_r(√X) bound by monotone root branches (Corollary 22.3;
  superseded for r ≥ 4), a Weierstrass model of the defect-four quartic,
  the explicit integer quartics and their discriminants (data, not a new
  theorem) and the endpoint window count X + (1 + 1/√3)√X + O_R(1) (23.9);
  Corollary 17.3 is stated for 1/2 < a < 1 only and does not specialize.
  Source 35's own contribution paragraph names the residual, the odd factor
  and finiteness for r ≥ 4 as its contribution; that was fair at its pin
  (this report did not exist) and is kept, with a dated correction, Remark
  24.1. Dated `[write]` notes point to Part IV from Sections 1.1, 2.3, 14.6,
  16 (after Theorem 16.1), 17.2 (after Corollary 17.3), 19.8, 20.1, 20.2,
  the title page and the bibliography.

Text written for the merge is marked **[merge]** in the article, and text
written for Part IV **[write]**. Section 1 records where the merge had to
choose; Section 20.2 is the provenance of Parts I–III, Section 21.1 that of
Part IV.

## Setting and notation

The N-th derivative of x^(x^a) is x^(x^a) times a sum of
p_{N,ℓ,k}(a) x^(aℓ−N) (log x)^k; ℓ counts exponent factors and k is the log
power. Depth d = ℓ − k, factor defect r = N − ℓ, tail offset q, coefficient
index M = N − k. Section 2 of the article fixes the notation and translates
it to the host. Watch for these readings:

- **d is a depth, never an offset.** At a = 1, d is the Lehmer–Comtet column
  (source 31's b(M,d)); the host's Part 2 uses d for the offset M − d, which
  is the defect r here. At a = 2, d is the host's deficit m.
- **r is the factor defect** in Parts II–IV. Sources 28, 31 and 34 used
  r for the ratio a + η; it is written ω here.
- **q is the tail offset.** A rational exponent is written a = 𝔭/𝔮 (sources
  20r and 20 write p/q, colliding with the coefficient p and the offset q).
- **K is the reflection form** ak − (2a−1)N + 2ar − 1, not the host's K_d.
  In Part IV, source 35's K = k + 2(r−1) is written K̃: it is 𝔮K = 2K at
  a = 1/2, not K.
- **U(s,y)** is a partial-fraction kernel, not the host's proposed count U(n).
- **Source 26's η = 2ν + κ − 1 is written η̂**; it is not source 28's η = q/d.
- Other renamings (all listed in Section 2.2): source 28's R_a(x) → 𝓡_a(x);
  in 34, A(s), B(s) → B_1(s), B_2(s), the circle parameter a → α and radius
  ρ → R, the curvature C(κ,η) → Im D²S, K(T), F(T) → 𝒦(T), ℱ(T), and the
  host's r = 2d+q+1 (34's R) → M − k; in 26 the real point z = −r → z = −σ;
  in 20 the field L = Q(a) → 𝕃 and L = qK → K̃; in 16 the leading line
  L_a → Λ_a, C_a → Σ_a, the constant A_a → Γ_a, e = s_r → s_r, and the local
  d, q, t of Corollary 18.2 → δ, ϖ, τ. No normalization was changed.
- **Part IV's renamings** (Table 4 of the article): R_{r,N} → R_{1/2,r,N};
  A, B → A_{1/2}, B_{1/2}; the scaled Hermite variable x (source 35 also
  uses x for the base variable) → ξ, and its roots x_j → ξ_j;
  Q_{r,N} → 𝒬_{r,N} (not Lemma 16.2's Q_r(a,K)); K → K̃; the square
  coordinates Z, Y → Z_4, Z_5 (= −4Y_4, −4Y_5 of (16.7)–(16.8)); the quartics
  f_4, f_5 → φ_4, φ_5 (not the parameter functions f_r of (16.4));
  the Weierstrass U, V, X → 𝖴, 𝖵, 𝖷; F_r, E_r → F̂_r, Ê_r (equal to 20r's
  F_r for even r and F_r/2 for odd r). No normalization was changed.
- The sources call the host's Parts 2 and 3 "Part I" and "Part II"; the
  article says which is meant wherever those words are printed.

## What the report claims

- **Integer exponents (Theorem 3.1).** For every fixed positive integer a,
  A_a(N) = N²/2 + o_a(N²): the nonnegative power columns are strictly
  positive (Proposition 3.2) and only o(N²) of the N²/(2a²) + O(N) tail
  candidates cancel. Ineffective. For a = 1 (Corollary 12.1) this is
  a(N) ~ N²/2 for A293239, equivalently Z(N) = o(N²) for the zeros of the
  first-kind Lehmer–Comtet triangle A008296; for a = 2 (Corollary 13.1) it is
  lim a(N)/N² = 1/2 for A290268.
- **Generic exponents (Corollary 10.1).** Outside a countable set of real
  algebraic numbers, in particular for every transcendental real exponent,
  the count is exactly N(N+3)/2 at every N ≥ 1.
- **First two depths (Theorem 11.1).** For every integer a ≥ 1 and d ∈ {1,2}
  the signs are explicit, and the only zeros are on the reflection line
  q = ad with (a−1)k + d even; the depth generating function (3.6) and the
  symmetry centre q = ad for a ≥ 3 are new.
- **The half exponent (Theorems 14.1, 14.3).** A(N) = N²/2 + o(N²) for
  x^(√x), by circle-only saddle selection; on defects two and three there are
  infinite non-reflection zero families N = (3k²+13k+8)/4 (k ≥ 1,
  k ≡ 0, 1 mod 4) and N = (k²+9k+12)/4 (k ≥ 3, k ≡ 0, 3 mod 4).
- **Rational exponents (Theorem 16.1, Corollary 16.3).** For rational a ≠ 1
  and fixed r ≥ 4, only finitely many cancellations lie off the reflection
  line (Schur, Siegel; r = 4, 5 by two quartics certified squarefree modulo 3
  and 11 for every rational a). For rational 1/2 < a < 1, defects two and
  three have infinitely many non-reflection cancellations.
- **Algebraic exponents (Theorems 17.1, 17.2, Corollary 17.3).** Finiteness
  on r ≥ 4D+2 for degree D (implied, second route); for rational
  1/2 < a < 1 exact square-root counts on defects two and three, and an exact
  linear-plus-square-root count in every fixed window of defects.
- **Irrational exponents (Theorem 18.1, Corollary 18.2).** At most
  (2⌊r/2⌋)² − 1 cancellation cells on each fixed defect r ≥ 2, none on
  r = 1, none for transcendental a or for algebraic degree above 2⌊r/2⌋; at
  most one on each of defects two and three (both attained); an explicit
  order bound and a terminating elimination procedure; for a = 1 ± 1/√3 the
  complete defect-two list is {(N,k) = (3,0)}.
- **Hermite limits at the half exponent (Part IV, Theorems 22.1–22.2,
  Corollary 22.3).** On a fixed defect r of x^(√x),
  (−1)^r r! (12/N)^{r/2} R_{1/2,r,N}(2√N ξ/√3) = He_r(ξ) + N^{−1/2} G_r(ξ) +
  O_r(1/N) with an explicit G_r; for large N the residual has r simple real
  roots k_j(N) = (2ξ_j/√3)√N − ξ_j²/6 − 2(r−1) + O_r(N^{−1/2}); at most
  ⌊r/2⌋ cells vanish per large order and O_r(√X) through order X.
  Finiteness on every defect r ≥ 4 (Theorems 23.1, 23.3) is Theorem 16.1 at
  a = 1/2, proved again with explicit integer quartics (discriminants
  4941729621000000 and 2925054216000); the defect-four quartic is
  birational to V² = U³ − 122400U + 9415000. In a fixed window of defects
  0 ≤ r ≤ R, R ≥ 3, there are X + (1 + 1/√3)√X + O_R(1) cancellations through
  order X (23.9).

## What the report does not claim

- No power-saving remainder and no effective order threshold in any of the
  leading asymptotics (Theorem 3.1, Corollaries 12.1 and 13.1, Theorem 14.1);
  no uniformity when a grows with N.
- No exact support: individual extra zeros are not classified for any
  exponent; it is not proved that the reflection holes and b(8,5) = 0 are
  the only zeros (host Conjecture 2.9 for x^x, the A290268 conjecture), nor
  any proposed exact term-count formula or generating function.
- The explicit lower bounds of the host (n + 1 + ⌊n²/4⌋ for A293239,
  leading term 3N²/8 for A290268) remain the only explicit ones.
- Fixed-defect results give no numerical thresholds and (except source 16's
  effective procedure) no complete finite exceptional lists; nothing is
  claimed when the defect grows with N; the exponent a = 1 is excluded; the
  algebraic-degree threshold is not claimed optimal; singular quartics at
  irrational algebraic parameters are not excluded; no practical complexity
  bound for elimination and no recognition of transcendence from numerical
  data.
- Part IV gives no effective threshold and no complete finite zero list on
  any defect r ≥ 4 of x^(√x), and does not assert that these finite sets are
  empty; the root locations do not assert integer nonvanishing; its
  constants depend on r; integral points of the Weierstrass model are not
  the integral points of the quartic (Remark 23.2), and no integral-point
  completeness is claimed. The finite evidence at the end of Section 23.4
  (no cancellation on defect four for N ≤ 5.5·10^11 and on defect five for
  N ≤ 3.6·10^11, from an exact search of the quartics; none on defects four
  to eight for N ≤ 4000, from a modular recurrence scan) was computed by the
  write, is not shipped and is evidence only.
- No OEIS identifier for the x^(√x) sequence; no exhaustive priority search
  (each source records a bounded source comparison).
- The finite checks in `code/` and `data/` supplement the proofs; they prove
  no infinite statement.

## Further questions

Section 19.8 collects the open questions of sources 28–16. Section 24.3
(Part IV) states those of source 35 under Vladimir's standing rule of
4 October 2026: (1) effective thresholds and the finite exceptional lists
on defects r ≥ 4 at a = 1/2, with the finite evidence; (2) all integral
points of the two quartics Z² = 150K̃⁴ − 120K̃² − 30K̃ + 196 and
Z² = 10K̃⁴ − 40K̃² − 30K̃ + 256 (a model for the second is missing);
(3) estimates uniform in a growing defect; (4) the write's outlook: the
leading Hermite term holds for every 0 < a < 1 in ξ = K√(3/(|c|N)) (proof
given there), and the first correction and root shifts for a ≠ 1/2 are
open. Source 35 has no demonstrably wrong mathematical claim; its
overstated contribution sentence (Remark 24.1) and its README's wording on
the elliptic model (Remark 23.2) are kept on record with corrections.

## Relation to neighbouring material

- **`power-tower-derivative-term-counts`** (the host, same subcategory). This
  report answers its **Question 6** (Section 3.24: a(N) ~ N²/2 for A290268)
  and the **closing remark of its Part 2** (the o(n²) bound on extra zeros
  that would give a(n) ~ n²/2 for A293239, its equation (2.35)). It partly
  answers its Question 8 (x^(x^r), r ≥ 3: leading asymptotic, depth
  generating function, symmetry centre and depths one and two) and Research
  question 3.68 (which x^(x^m) have only symmetry-forced holes). It qualifies
  the host's Section 5 observation that every proved cancellation is a parity
  zero: that remains true of the host's three functions, but x^(√x) and
  every rational 1/2 < a < 1 have infinite non-reflection families. The
  host's dated notes cite this report's Theorems 3.1, 11.1, 14.1, 14.3,
  Corollaries 12.1, 13.1, 16.3 and Section 19.8; Part IV changed none of
  those numbers. Source 35 cites the host's Question 8; it adds nothing to
  the host's own functions.
- **`a290268-unbounded-deficits`** (same subcategory, opened by the same
  placement commit) studies A290268 when the logarithmic deficit grows with
  N. The lower-bound headlines of several of its sources (constants 0.49,
  3/8 + c, 3N²/8 + CN^(3/2)) are implied, ineffectively, by Corollary 13.1.
- **Formal project.** The repository's Lean library for A290268
  (`Combinatorics/DerivativeExpansions/A290268/Lean`) defines the
  coefficients and the count of Corollary 13.1 in the same lattice
  (`LeanProofs.A290268.coeff`, `LeanProofs.A290268.a`) and proves the support
  window, `LeanProofs.A290268.a_values_le_53` (the closed form for n ≤ 53)
  and the conditional reduction
  `LeanProofs.A290268.a_eq_closedForm_of_support_all`. It has no asymptotic
  statement, and nothing here discharges its hypotheses. Nothing for x^x,
  the Lehmer–Comtet triangle or x^(x^a) with a ≠ 2 is formalized, so nothing
  of Part IV is.

## Building

From this directory, in a scratch copy (so that no auxiliary files land in
the repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The source is self-contained (no `\input`, no figures, internal
bibliography) and builds with pdfLaTeX (MiKTeX here): 71 pages, no warnings,
no overfull boxes, no undefined or multiply defined references. The six
underfull lines of the 1 October build are unchanged; Part IV adds none.

## Rerunning the checks

Every script writes its output **beside itself under its delivered name**
(`Path(__file__).with_name(...)` or `with_suffix('.json')`), not under the
shipped `data/` name, and two scripts read a record from their own
directory: `20r-rational-replay_independent.py` reads `certificates.json`
and `35-hermite-check_quartics.py` reads `hermite_checks.json`. Run each one
on a copy with its delivered name, then compare with the shipped record;
never run them inside `code/` (under the shipped names,
`35-hermite-check_bell_normalization.py` and `35-hermite-check_quartics.py`
would write `35-hermite-check_*.json` into `code/`, and the latter would not
find its input). For example:

```
mkdir rerun && cd rerun
cp <report>/code/28-all-integer-verify_general_coefficients.py verify_general_coefficients.py
py verify_general_coefficients.py            # writes general_coefficient_checks.json
cp <report>/code/20r-rational-replay_independent.py replay_independent.py
cp <report>/data/20r-rational-certificates.json certificates.json
py replay_independent.py                     # writes replay_independent.json
for f in verify_hermite check_bell_normalization check_quartics birational_model; do
  cp <report>/code/35-hermite-$f.py $f.py; done
uv run --no-project --with sympy==1.14.0 python verify_hermite.py      # writes hermite_checks.json (run first)
uv run --no-project --with sympy==1.14.0 python check_quartics.py      # reads it, writes check_quartics.json
uv run --no-project --with sympy==1.14.0 python birational_model.py    # writes birational_model.json
py check_bell_normalization.py                                         # writes check_bell_normalization.json
```

Delivered names: 16 `verify.py` → `checks.json`, `check_low_defect_injectivity.py`
(stdout only); 20 `replay_low_counts.py` → `replay_low_counts.json`; 20r
`verify.py` → `certificates.json`, `replay_independent.py` →
`replay_independent.json`; 26 `verify_half_coefficients.py` →
`half_coefficient_checks.json`; 28 `verify_general_coefficients.py` →
`general_coefficient_checks.json`; 31 `verify_coefficients.py` →
`coefficient_checks.json`, `check_saddle_normalization.py` →
`saddle_normalization.json`; 34 `verify_tanh_identity.py` →
`tanh_identity_checks.json`, `verify_curvature_seed.py` →
`curvature_seed.json`, `verify_derivative_counts.py` → `derivative_counts.json`;
35 `verify_hermite.py` → `hermite_checks.json`,
`check_bell_normalization.py` → `check_bell_normalization.json`,
`check_quartics.py` → `check_quartics.json`, `birational_model.py` →
`birational_model.json`.

Use `py` or `uv run --no-project python`. SymPy is needed for both source-16
scripts, for `20r-rational-verify.py` and for three of the four source-35
scripts (no requirements file was delivered and the records name no
version; `uv run --no-project --with sympy==1.14.0 python` works), mpmath
for `31-a293239-check_saddle_normalization.py`; everything else uses the
standard library. At placement each script ran in at most about a minute;
source 35's four take about 35 seconds together.

At placement every script was rerun on a copy and its output equalled the
shipped record apart from line endings; on 5 October 2026 the Part IV write
reran source 35's four again (SymPy 1.14.0, Python 3.13.5) with the same
result. On Windows the scripts write CRLF while the records are LF, so
compare after removing `\r`. `34-a290268-derivative_counts.json` also
records its own running time (`seconds`), so it never reproduces byte for
byte, and it has no final newline.

No shipped program embeds OEIS data as test vectors; OEIS data, wherever
quoted, are licensed CC BY-SA 4.0, not MIT-0.

## Other discrepancies

- Source 28's delivered README (replaced) listed `article.pdf` and
  `build_local.sh` and recorded that the host's latest commit was
  `ca81647a9` and the default-branch head `7421a4ca6` at 09:14 UTC on
  1 October 2026. Source 34 says the same of `ca81647a9` ("its latest file
  commit remains the one cited below"). Both are kept as provenance, not as
  statements about the host's current text.
- Source 20 (Section 19.6 of the article) says its companion "is included as
  a companion PDF and source package"; neither is shipped. The companion is
  Section 16, and its code and data are the four `20r-` files. Source 20r's
  Lemma 16.2 says the coefficient lists and an exact verifier "accompany this
  note": they are `data/20r-rational-certificates.json` and
  `code/20r-rational-verify.py`.
- The sources' READMEs (not shipped) state that each proof received
  independent mathematical review and that every rendered page was
  inspected; source 35's says the proofs and final transcription "were
  independently reviewed before sealing". Those are the sources'
  statements; the repository has not repeated such a review. Every
  manuscript carries an AI author line; none is marked as prepared for
  private review.
- Source 35's README (not shipped) lists `article.pdf`, `article.tex` and
  `build_local.sh`, none of which is shipped (see above), tells the reader
  to run `python …` (here `py` or `uv run`, above), and says the elliptic
  model comes "with its integrality and admissibility conditions
  preserved"; read as "the birational map preserves integrality" that is
  false (the integral quartic point (6, −436) maps to (−3359/9, −47611/27)),
  as Remark 23.2 records. Its "verifies … through defect 10" and "11,935"
  agree with the shipped records.
- Source 26 gives A(150) = 11474, also in its recorded JSON; the placement
  intake rechecked A(50) and A(100) but not A(150).
- Three checks quoted in [merge] notes were run by the batch-72A intake and
  are not shipped: the exact comparison of 34's tanh formula and the host's
  Proposition 3.6 for n ≤ 16, the count of source 20's families at a = 3/4
  to X = 10⁸, and the scan of the recurrence for a = 1, …, 5 and N ≤ 70
  (Section 19.8). The last finds no zero other than structural and
  reflection zeros for a = 2, …, 5, and for a = 1 only the line of copies of
  b(8,5) = 0; it is an observation, not a theorem.
- The checks quoted in Part IV's [write] notes (the identifications of
  Table 3, the quartic search to K̃ = 2·10^6, the modular recurrence scan to
  N = 4000) and the batch-100 placement intake's searches cited there were
  run outside the repository and are not shipped.
