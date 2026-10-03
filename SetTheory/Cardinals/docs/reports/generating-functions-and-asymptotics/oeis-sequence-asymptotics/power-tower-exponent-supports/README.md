# Derivative Supports of x^(x^a)

**Leading asymptotics for every integer exponent and for the half exponent; fixed-defect cancellations for rational, algebraic and irrational exponents**

This is a research report of ProveIt's research-report collection (category
`generating-functions-and-asymptotics`, subcategory
`oeis-sequence-asymptotics`), written on 1 October 2026. It is built from
**seven manuscripts** of batch 72A, all dated 1 October 2026 and all carrying
the author line "Research note prepared for Vladimir Reshetnikov with
OpenAI". Six of them are the archives listed below; the seventh, 20r, was
never delivered on its own and arrived only inside archive 20. All seven
arrived in `1512ef835` and were placed in `d292c6765`.

| Source | Batch-72A manuscript | Archive (delivered title, PDF length) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 28 (base) | 28 | `ProveIt_All_Integer_Exponent_Derivative_Supports` (*Derivative Supports of x^(x^a): a common leading asymptotic for every fixed positive integer exponent*, 10 pp.) | `ca81647a9` | `d292c6765` (base of a new merge) | Sections 3–11 |
| 31 | 31 | `ProveIt_A293239_Leading_Asymptotic` (*The Leading Asymptotic of OEIS A293239: sparse zeros of the Lehmer–Comtet triangle*, 8 pp.) | `ca81647a9` | `d292c6765` | Section 12 (second route at a = 1) |
| 34 | 34 | `ProveIt_A290268_Leading_Asymptotic` (*The Leading Asymptotic of OEIS A290268*, 11 pp.; main file plus `tanh_sections.tex`) | `ca81647a9` | `d292c6765` | Section 13 (second route at a = 2) |
| 26 | 26 | `ProveIt_Half_Exponent_Derivative_Supports` (*Derivative Supports of x^(√x): a leading-density theorem with two infinite extra-cancellation families*, 7 pp.) | `ca81647a9` | `d292c6765` | Section 14 |
| 20r | 20r (embedded) | inside `ProveIt_Algebraic_Exponents_and_Cancellation_Frequencies`, as `Algebraic_Exponents_and_Cancellation_Frequencies/rational_companion_source.zip`, folder `Rational_Exponent_Fixed_Defects` (*Reflection and Finite Exceptions: fixed defects in derivatives of x^(x^a) for positive rational a ≠ 1*, 6 pp.) | `ca81647a9` | `d292c6765` | Sections 15, 16 |
| 20 | 20 | `ProveIt_Algebraic_Exponents_and_Cancellation_Frequencies` (*Algebraic Degrees and Exact Cancellation Frequencies: two fixed-defect extensions for derivatives of x^(x^a)*, 4 pp.) | none named | `d292c6765` | Sections 15, 17 |
| 16 | 16 | `ProveIt_Irrational_Exponents_Effective_Cancellation_Bounds` (*Effective Bounds for Irrational Exponents: fixed-defect cancellations in derivatives of x^(x^a)*, 6 pp.) | `ca81647a9` | `d292c6765` | Sections 15, 18 |

The pin `ca81647a9` is the commit of the host report
`power-tower-derivative-term-counts` that each source inspected. The zip
entry times show that the notes were written in the order 34, 31, 28, 26,
20r, 20, 16, between 01:24 and 04:21 PDT on 1 October 2026.

Every result, proof, example, remark, question and limitation of the seven
manuscripts is printed. Duplicated results are printed once, with every
source that proved them named, and genuinely different proofs are kept as
second routes (Section 1.2 of the article). **Status: AI-assisted and
unrefereed. None of the report's results is formalized in Lean or Rocq.**
Placement beside the repository's Lean library for A290268 confers no formal
status on it (see "Relation to neighbouring material").

```
README.md                                         this guide (replaces source 28's delivered README)
article.tex                                       the report (replaces source 28's delivered article.tex)
article.pdf                                       the compiled report, 58 pages (unnumbered title page,
                                                  contents pages 1-3, text pages 4-57, references page 57)
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
```

Every file in `code/` and `data/` is byte-identical to the delivery; the
prefix (`NN-short-slug-`) is the only change to its name. The 20r files were
extracted from the members of `rational_companion_source.zip` inside archive
20. Not shipped, and surviving only in `1512ef835`: the manuscripts, READMEs
and PDFs of sources 31, 34 (with its `tanh_sections.tex`, printed in Section
13), 26, 20 and 16; source 28's delivered PDF; source 20r's `article.tex`,
`article.pdf` and `README.md`; archive 20's `rational_companion.pdf` and the
companion zip itself; and the seven copies of the Linux build wrapper
`build_local.sh`, one per package. No package had a checksum manifest.

## Labels and numbering

Every label in `article.tex` carries the prefix `pte:`; the manuscripts' own
prefixes are kept as sub-prefixes: `pte:ga:` (28), `pte:lc:` (31), `pte:as:`
(34, including its tanh sections), `pte:he:` (26), `pte:rf:` (20r), `pte:ac:`
(20) and `pte:ir:` (16). The staged base `article.tex` had **36** labels (all
source 28's, unprefixed). The written report has **210**, all distinct:

- **175** of the **186** delivered labels (28: 36, 31: 28, 34: 42, 26: 27,
  20r: 24, 20: 13, 16: 16), each with `pte:` in front and otherwise unchanged.
  Every `\ref` and `\eqref` was updated before anything cited them.
  The integer-triangle lemma, proved identically in 28, 31, 34 and 26, is
  printed once as Lemma 9.1 and carries all four labels (`pte:ga:lattice`,
  `pte:lc:lattice`, `pte:as:lattice`, `pte:he:lattice`).
- **11** delivered labels are not printed, because they name equations
  printed once under source 20r's label (Section 15):
  `ac:physical`, `ir:physical` → `pte:rf:physical`;
  `ac:bridge`, `ir:bridge` → `pte:rf:bridge`;
  `ac:residual`, `ir:residual` → `pte:rf:residual`;
  `ac:center`, `ir:K` → `pte:rf:center`;
  `ac:even`, `ir:even` → `pte:rf:even`;
  `ac:edges` → `pte:rf:edgeeven`, `pte:rf:edgeodd`.
- **35** new labels for parts, sections and the two tables
  (`pte:part:*`, `pte:sec:*`, `pte:tab:*`).

The build has no undefined, multiply defined or mistyped references. No
label has a Lean or Rocq mapping. Theorem numbers below are those of the
built `article.pdf`.

## How the seven were merged

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

Text written for the merge is marked **[merge]** in the article. Section 1
records where the merge had to choose; Section 20.2 is the provenance.

## Setting and notation

The N-th derivative of x^(x^a) is x^(x^a) times a sum of
p_{N,ℓ,k}(a) x^(aℓ−N) (log x)^k; ℓ counts exponent factors and k is the log
power. Depth d = ℓ − k, factor defect r = N − ℓ, tail offset q, coefficient
index M = N − k. Section 2 of the article fixes the notation and translates
it to the host. Watch for these readings:

- **d is a depth, never an offset.** At a = 1, d is the Lehmer–Comtet column
  (source 31's b(M,d)); the host's Part 2 uses d for the offset M − d, which
  is the defect r here. At a = 2, d is the host's deficit m.
- **r is the factor defect** in Parts II and III. Sources 28, 31 and 34 used
  r for the ratio a + η; it is written ω here.
- **q is the tail offset.** A rational exponent is written a = 𝔭/𝔮 (sources
  20r and 20 write p/q, colliding with the coefficient p and the offset q).
- **K is the reflection form** ak − (2a−1)N + 2ar − 1, not the host's K_d.
- **U(s,y)** is a partial-fraction kernel, not the host's proposed count U(n).
- **Source 26's η = 2ν + κ − 1 is written η̂**; it is not source 28's η = q/d.
- Other renamings (all listed in Section 2.2): source 28's R_a(x) → 𝓡_a(x);
  in 34, A(s), B(s) → B_1(s), B_2(s), the circle parameter a → α and radius
  ρ → R, the curvature C(κ,η) → Im D²S, K(T), F(T) → 𝒦(T), ℱ(T), and the
  host's r = 2d+q+1 (34's R) → M − k; in 26 the real point z = −r → z = −σ;
  in 20 the field L = Q(a) → 𝕃 and L = qK → K̃; in 16 the leading line
  L_a → Λ_a, C_a → Σ_a, the constant A_a → Γ_a, e = s_r → s_r, and the local
  d, q, t of Corollary 18.2 → δ, ϖ, τ. No normalization was changed.
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
- No OEIS identifier for the x^(√x) sequence; no exhaustive priority search
  (each source records a bounded source comparison).
- The finite checks in `code/` and `data/` supplement the proofs; they prove
  no infinite statement.

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
  every rational 1/2 < a < 1 have infinite non-reflection families. The host
  is not edited by this change; its dated notes and reciprocal remarks are a
  separate commit.
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
  the Lehmer–Comtet triangle or x^(x^a) with a ≠ 2 is formalized.

## Building

From this directory, in a scratch copy (so that no auxiliary files land in
the repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The source is self-contained (no `\input`, no figures, internal
bibliography) and builds with pdfLaTeX (MiKTeX here): 58 pages, no warnings,
no overfull boxes, no undefined or multiply defined references.

## Rerunning the checks

Every script writes its output **beside itself under its delivered name**
(`Path(__file__).with_name(...)`), not under the shipped `data/` name, and
`20r-rational-replay_independent.py` reads `certificates.json` from its own
directory. Run each one on a copy with its delivered name, then compare with
the shipped record; never run them inside `code/`. For example:

```
mkdir rerun && cd rerun
cp <report>/code/28-all-integer-verify_general_coefficients.py verify_general_coefficients.py
py verify_general_coefficients.py            # writes general_coefficient_checks.json
cp <report>/code/20r-rational-replay_independent.py replay_independent.py
cp <report>/data/20r-rational-certificates.json certificates.json
py replay_independent.py                     # writes replay_independent.json
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
`curvature_seed.json`, `verify_derivative_counts.py` → `derivative_counts.json`.

Use `py` or `uv run --no-project python`. SymPy is needed for both source-16
scripts and for `20r-rational-verify.py` (no requirements file was
delivered and the records name no version; `uv run --no-project --with
sympy==1.14.0 python` works), mpmath for
`31-a293239-check_saddle_normalization.py`; everything else uses the
standard library. At placement each script ran in at most about a minute.

At placement every script was rerun on a copy and its output equalled the
shipped record apart from line endings. On Windows the scripts write CRLF
while the records are LF, so compare after removing `\r`.
`34-a290268-derivative_counts.json` also records its own running time
(`seconds`), so it never reproduces byte for byte, and it has no final
newline.

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
  inspected. Those are the sources' statements; the repository has not
  repeated such a review. Every manuscript carries an AI author line.
- Source 26 gives A(150) = 11474, also in its recorded JSON; the placement
  intake rechecked A(50) and A(100) but not A(150).
- Three checks quoted in [merge] notes were run by the batch-72A intake and
  are not shipped: the exact comparison of 34's tanh formula and the host's
  Proposition 3.6 for n ≤ 16, the count of source 20's families at a = 3/4
  to X = 10⁸, and the scan of the recurrence for a = 1, …, 5 and N ≤ 70
  (Section 19.8). The last finds no zero other than structural and
  reflection zeros for a = 2, …, 5, and for a = 1 only the line of copies of
  b(8,5) = 0; it is an observation, not a theorem.
