# Permutations with Exactly One Occurrence of 1234, 1243 or 12345

**OEIS A217057, A224179 and A224248: half decompositions, leading amplitudes, rational diagonals and asymptotic expansions to every order; the refutation of Conway and Guttmann's conjecture R = 1/2**

This is a research report built on 5 October 2026 (write batch 105) from six
manuscripts of one external research session, Reports 134, 135, 136, 137, 138
and 140 of the session bundle of Reports 1–243, all dated 2 October 2026. A
permutation contains exactly one classical occurrence of a pattern when exactly
one of its subsequences (adjacent or not) is order-isomorphic to the pattern.
The report treats three such counts:

- `u_n`, exactly one `1234`: [A217057](https://oeis.org/A217057)
  (`1, 12, 102, 770, 5545, …` from `n = 4`);
- `b_n`, exactly one `1243`: [A224179](https://oeis.org/A224179)
  (`1, 11, 88, 638, 4478, …`);
- `U_n`, exactly one `12345`: [A224248](https://oeis.org/A224248)
  (`1, 20, 270, 3142, 34291, …` from `n = 5`).

The first two are normalized by `A_n = |Av_n(1234)| = |Av_n(1243)|`
([A005802](https://oeis.org/A005802)), with `A_n ~ C_0 9^n n^{-4}`,
`C_0 = 81√3/(16π)`; the third by `|Av_n(12345)|`
([A047889](https://oeis.org/A047889)) `~ C_A 16^n n^{-15/2}`, `C_A = 1536/π^{3/2}`.

- **Part I** (Report 134): `u_n/A_n → R`, an explicit series of positive
  terms, so `u_n ~ C_0 R 9^n n^{-4}`; a finite rational certificate
  `R ≥ L_{40,10} > 0.50009` that **refutes Conway and Guttmann's conjecture
  `R = 1/2`** (EJC 32(1) (2025) P1.3, Section 5.1 = arXiv:2306.12682v2). The
  write adds `R ≥ Π_44 > 0.50153` (Proposition 6.1, exact rational computed
  in the write).
- **Part II** (Report 135): `Σ u_n zⁿ` is the diagonal of a rational power
  series over ℚ, hence D-finite (via Bostan–Lairez–Salvy, hypotheses checked in
  the write); an explicit 42-variable rational constant term;
  `u_n/A_n = R + S/n + S_2/n² + (43020√3/π) log n/n³ + O(n^{-3})`.
- **Part III** (Report 137, the base): every fixed order,
  `u_n/A_n = Σ_{j≤J} (r_j + κ_j log n) n^{-j} + O_J((1+log n) n^{-J-1})`,
  `κ_0 = κ_1 = κ_2 = 0`, `κ_3 = 43020√3/π`, `κ_4 = −5041845√3/π`, every `κ_j` in
  `(√3/π)ℚ`, `r_3` exists; inverse thresholds to every order.
- **Part IV** (Report 136): `b_n/A_n → R_{1243}` (a positive series), rational
  diagonal, D-finite, not algebraic, `b_n/A_n = R_{1243} + o(n^{-1/2})`
  (square-root cancellation). Conway and Guttmann's suggested `149/160` is
  **open**.
- **Part V** (Report 138): exact four-binomial gluing and six-term formula for
  one `12345`, rational diagonal, `U_n/|Av_n(12345)| → R_5 ≥ 15/32768`, so
  `U_n ~ C_A R_5 16^n n^{-15/2}`.
- **Part VI** (Report 140): every fixed order in powers of `1/n`, **no
  logarithms**, `r_1 = S_5` explicit.

The same method has opposite outcomes: logarithms from relative order three for
`1234` (integer half exponent 4), none for `12345` (half exponent 15/2; products
of the fractional-binomial models are polynomials). The write's Remark 66.1
says this, and answers Report 140's question 5 in the negative for `1234`.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Permutations with exactly one increasing subsequence of length four* (author line "Report 134") | 134 | `A217057_Unique_1234_Asymptotics_and_Conjecture_Refutation_Source.zip` (464,735 bytes, 8 files; `Report134.tex`, 791 lines, 12 pp.) | none | `e85586b7c` | Part I, Sections 1–10, plus the write's Proposition 6.1, Remark 6.2 and Section 10.1 |
| *Rational structure and logarithmic asymptotics for A217057* ("Report 135") | 135 | `A217057_Rational_Structure_Logarithmic_Asymptotics_and_Inversion_Source.zip` (1,087,811 bytes, 20 files, 8 of them Report 134's package under `companion134/`; `Report135.tex`, 1,455 lines, 22 pp.) | none | `e85586b7c` | Part II, Sections 11–22, plus Remark 13.2 and Section 22.1 |
| *All orders logarithmic asymptotics for A217057* ("Report 137"); the base | 137 | `A217057_All_Orders_Logarithmic_Asymptotics_and_Inversion_Source.zip` (1,576,820 bytes, 33 files, 20 of them Report 135's package under `companion135/`; `Report137.tex`, 812 lines, 13 pp.) | none | `e85586b7c` | Part III, Sections 23–29, plus Section 29.1 |
| *Permutations with exactly one classical 1243 occurrence* ("Report 136") | 136 | `A224179_Leading_Amplitude_Diffusive_Cancellation_and_Inversion_Source.zip` (634,761 bytes, 12 files; `Report136.tex`, 1,737 lines, 24 pp.) | none | `e85586b7c` | Part IV, Sections 30–43 (33–34 title only), plus Section 42.1 |
| *Exact formulas and leading asymptotics for unique 12345* ("Report 138") | 138 | `A224248_Exact_Formulas_Leading_Asymptotics_and_Inversion_Source.zip` (637,136 bytes, 15 files; `Report138.tex`, 1,159 lines, 17 pp.) | none | `e85586b7c` | Part V, Sections 44–54, plus Section 54.1 |
| *All orders asymptotics and inverse thresholds for unique 12345* ("Report 140") | 140 | `A224248_All_Orders_Asymptotics_and_Inverse_Thresholds_Source.zip` (1,237,127 bytes, 11 files, one of them Report 138's whole archive as `dependencies/Report138_reproducible.zip`; `Report140.tex`, 1,122 lines, 18 pp.) | none | `e85586b7c` | Part VI, Sections 55–65, plus Section 65.1 |

All six archives arrived unchanged in `60f54ea06` and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `e85586b7c` (batch 105, "Place batch 105: thirteen bundle reports as
four new reports") removed them from `docs/incoming/`. Report 139 of the same
batch (one `1432`, an unrelated method) is the separate report
`../a224182-unique-1432-order`.

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author, a tool or an
addressee, says it is AI-assisted, or carries "prepared for private review"
wording; each sets an empty PDF author field. Every result, proof, remark,
question and limitation of the six manuscripts is printed; Report 136's
Proposition 6 and Lemma 7, which are Report 134's Proposition 4 and Lemma 5
word for word (with `B_p` for `c_p`), are printed once, in Part I.

## Why the Parts are in this order

The base is Report 137, the most general report on `1234`; its `Report137.tex`
was staged as `article.tex`. It is printed third, as Part III, because it
uses the exact gluing, the global bounds, the unitary integral and the first
expansions of Reports 134 and 135 as inputs and restates none of their proofs;
those two reports are printed in full before it. Report 136 (one `1243`)
depends directly on Reports 134 and 135 and shares their normalizer `A_n`, so
it follows the `1234` chain as Part IV. Reports 138 and 140 are the chain for
one `12345` (Report 140 builds on Report 138), Parts V and VI. Within each
chain the order is the order of logical dependence and of writing.

## Files

The directory holds 49 files: 8 at the root, 24 in `code/`, 17 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 134, prefix `134-amplitude-`** (4 files): the certificate path
(hook formula and interlacing), the independent path (Young-lattice branching,
no hook formula), the verifier, and the fixture (A217057 for `n ≤ 15` from
OEIS, and the `T = 40`, `I = 10` certificate fraction).

```
code/134-amplitude-certificate.py
code/134-amplitude-independent.py
code/134-amplitude-verify.py
data/134-amplitude-fixtures.json
```

**Report 135, prefix `135-rational-`** (8 files): its provenance note; the
optional SymPy builder of the factored constant-term kernel; the first- and
second-correction and unitary checks; the verifier; exact data (`u_0 … u_20`,
finite partial sums of `R`, `S`, `S_2`).

```
135-rational-SOURCES.md
code/135-rational-kernel_sympy.py
code/135-rational-refinements.py
code/135-rational-second_refinements.py
code/135-rational-unitary_checks.py
code/135-rational-verify.py
data/135-rational-exact_data.json
data/135-rational-second_exact_data.json
```

**Report 136, prefix `136-unique1243-certificate-`** (7 files): the guide to its
finite certificate; the bundle tool, the object enumerator, the tableau
evaluator and the verifier; the expected replay output and the fixture
(A224179 for `n ≤ 25` from OEIS, the `L_35` fraction).

```
136-unique1243-certificate-README.md
code/136-unique1243-certificate-bundle.py
code/136-unique1243-certificate-objects.py
code/136-unique1243-certificate-tableaux.py
code/136-unique1243-certificate-verify.py
data/136-unique1243-certificate-expected.json
data/136-unique1243-certificate-fixtures.json
```

**Report 137, prefix `137-allorders-`** (9 files): its provenance note; the
verifier; the exact-algebra, Gaussian, inverse, model, regularization and
replay modules; the fixture.

```
137-allorders-SOURCES.md
code/137-allorders-code-exact_algebra.py
code/137-allorders-code-gaussian.py
code/137-allorders-code-inverse.py
code/137-allorders-code-models.py
code/137-allorders-code-regularized.py
code/137-allorders-code-replay.py
code/137-allorders-verify.py
data/137-allorders-checks-fixtures.json
```

**Report 138, prefix `138-leading-`** (11 files): its provenance note; the
verifier; the exact replay module; the C++ object-level validator (optional
`deep` check); the fixture; the source snapshots (OEIS A047889 and A224248
`.seq` files, the first 25 lines of the A047889 b-file, Nakamura and
Zeilberger's Rutgers output `oF12345a`), the inventory recording their URLs,
dates and hashes, and a separate audit's counters.

```
138-leading-SOURCES.md
code/138-leading-code-exact.py
code/138-leading-code-object_check.cpp
code/138-leading-verify.py
data/138-leading-checks-fixtures.json
data/138-leading-sources-A047889.seq
data/138-leading-sources-A224248.seq
data/138-leading-sources-b047889_0_24.txt
data/138-leading-sources-independent_audit.json
data/138-leading-sources-inventory.json
data/138-leading-sources-oF12345a
```

**Report 140, prefix `140-allorders-`** (7 files): its provenance note; the
verifier; the exact replay module; the fixture; two receipts of separately run
checks and their inventory.

```
140-allorders-SOURCES.md
code/140-allorders-code-exact.py
code/140-allorders-verify.py
data/140-allorders-checks-fixtures.json
data/140-allorders-sources-check_avoidance_recurrence.json
data/140-allorders-sources-independent_extension_checks.json
data/140-allorders-sources-inventory.json
```

**Not shipped** (all retrievable from `60f54ea06`): the six PDFs; the
manuscripts of Reports 134, 135, 136, 138 and 140 (printed as Parts I, II,
IV, V, VI) and their delivery READMEs (Report 137's README was staged and is
replaced by this guide); the checksum manifests (`manifest.json` of Reports
134, 135, 137, 138 and 140; Report 136's `bundle-manifest.json` and
`certificate/manifest.json`; all verified at placement; repository policy drops
checksum manifests); the byte copies `companion134/` (8 files, in Report 135)
and `companion135/` (20 files, in Report 137); and Report 140's
`dependencies/Report138_reproducible.zip`, byte-identical to Report 138's
archive (SHA-256 `360c9db7…`).

## Labels and numbering

Label prefix **`upo:`** (none at HEAD before this report): Part I uses
`upo:amp:` (Report 134's 49 labels), Part II `upo:rat:` (Report 135's 92),
Part III `upo:all:` (Report 137's 46), Part IV `upo:1243:` (84 of Report 136's
95), Part V `upo:ex5:` (Report 138's 67), Part VI `upo:all5:` (Report 140's
95). Report 136's other 11 labels sit in its Sections 4–5, which are Report
134's word for word; they resolve to Part I's labels (`prop:F` of Report 136
is `upo:amp:prop:F`). The front matter uses `upo:sec:guide`,
`upo:sec:status`, `upo:sec:notation`, `upo:sec:provenance`,
`upo:sec:neighbours`; the synthesis `upo:sec:together`, `upo:rem:dichotomy`,
`upo:sec:further`. The write added the six Part labels, 13 section labels for
unlabelled sections, the six further-questions labels, and
`upo:amp:prop:sharper`, `upo:amp:eq:Pi44`, `upo:amp:rem:numerics`,
`upo:rat:rem:bls`. 470 labels in all, all distinct. The staged base
`article.tex` (Report 137) had 46.

Sections are numbered continuously, statements and equations within sections:

| Part | Manuscript | Section here | Statements |
|---|---|---|---|
| I | Report 134 | `k` (1–10); 10.1 added | consecutive numbers renumbered: Theorem 1 → 1.1, Lemmas 2, 3 → 2.1, 3.1, Proposition 4 → 4.1, Lemma 5 → 5.1, Lemmas 6, 7 → 7.1, 7.2, Corollary 8 → 9.1; Proposition 6.1 and Remark 6.2 added |
| II | Report 135 | `k + 10` (11–22); 22.1 added | `(k+10).j`; Remark 13.2 added |
| III | Report 137 | `k + 22` (23–29); 29.1 added | `(k+22).j` |
| IV | Report 136 | `k + 29` (30–42); Appendix A → 43; 42.1 added | Theorems 1, 2 → 30.1, 31.1; Lemmas 3, 4, 5 → 31.2, 32.1, 32.2; Proposition 6, Lemma 7 → Part I's 4.1, 5.1; Lemmas 8–10 → 35.1–35.3; Proposition 11 → 36.1; Corollary 12 → 39.1; Lemmas 13, 14 → 40.1, 40.2; Theorems 15, 16 → 40.3, 41.1 |
| V | Report 138 | `k + 43` (44–54); 54.1 added | `(k+43).j` |
| VI | Report 140 | `k + 54` (55–65); 65.1 added | `(k+54).j` |
| — | write | 66 (synthesis), 66.1 | Remark 66.1 |

A comparison of the build's `.aux` with separate builds of the six delivered
`.tex` files confirmed every statement and section number under these maps.
**Equation numbers are not kept**: the manuscripts number equations through each
document, the merged article within sections; every equation keeps its label
name. The delivered READMEs, data and code use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the six
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a reading table. In the write's own text the
avoidance counts are `A^{(4)}_n` and `A^{(5)}_n` and the amplitudes `R`,
`R_{1243}`, `R_5`, because every Part writes `A_n` and most write `R`. The
heaviest collisions: **`A_n`** (A005802 in Parts I–IV, A047889 in V–VI);
**`U`** (the count A224248 in V–VI; `U(z)` and `U ∈ U(3)` in II; arrays `U_j`
in III; bold arrays in VI); **`R`** (amplitude in I–IV; a boundary parameter
`i_3 + 1` in V–VI); **`H`** (two-index half counts in I–IV, four-index ones in
V–VI, harmonic numbers in III); **`P`, `Q`** (polynomials in I; `tr U`, `Σθ²`,
shuffle weights in II–IV; boundary parameters in V–VI); **`B`**, **`T`**,
**`L`**, **`r`**, **`τ`**, **`p`** (a boundary parameter in I–IV; `15/2` in
V–VI), **`w`**, **`d`**, **`κ`** (`log 9` in Part IV's corollary), **`α`**,
**`E`**, **`D`**, **`J`**.

## What the report claims

**Part I (Report 134).** Lemma 2.1: twelve allowed cells and the exact gluing
`u_n = Σ_{s+t=n−4} Σ H_s(i,j) H_t(k,l) C(i+k,i) C(j+l,j)`; Lemma 3.1:
`H_s(i,j) = F_{s+2}(i+1,j+1) − F_{s+1}(i,j)`; Proposition 4.1: three-row
tableau formula; Lemma 5.1: `F_m(p,q)/A_m → d_p d_q`; Section 6:
`liminf u_n/A_n ≥ L_{40,10} > 0.50009` without the existence proof;
Lemmas 7.1–7.2: uniform domination; Theorem 1.1: `R` exists, equals the
positive series (1.4) with factor `1/10368`, `u_n ~ C_0 R 9^n n^{-4}`;
Corollary 9.1: inverse threshold with the error inside the ceilings.

**Part II (Report 135).** Theorem 11.1: rational diagonal over ℚ, D-finite,
P-recursive (24-index binomial encoding, Bostan–Lairez–Salvy Theorem 3.5 and
Corollary 3.6); Theorem 14.1: explicit 42-variable rational constant term with
convergent contours; Lemma 15.1 and (19.9):
`A_m = C_0 9^m m^{-4}(1 − 11/(2m) + 20/m² + O(m^{-3}))`; Proposition 16.1 and
(19.11): uniform boundary expansions; Theorems 11.2 and 19.1:
`u_n/A_n = R + S/n + S_2/n² + κ log n/n³ + O(n^{-3})`, `κ = 43020√3/π`;
Section 18: exact transforms `D_k, E_k, J_k, K_k, L_k, M_k`; Corollary 20.1:
inverse width `O((log T)^{-3})`.

**Part III (Report 137).** Theorem 23.1 (above); Proposition 24.1: weighted
Banach expansion of the half arrays to every order, avoidance coefficients
`1, −11/2, 20, −965/16`; Theorem 25.3: a coefficient-level convolution theorem
in any Banach space with a continuous symmetric bilinear form; Section 26: the
recipe for `r_3`, `ℓ_3 = 40⟨U_0,U_0⟩`, `ℓ_4 = 140⟨U_0,U_1⟩`,
`⟨C,C⟩ = 1393848`, `⟨C,B⟩ = −52348032`; Corollary 27.1: inverse to every
order.

**Part IV (Report 136).** Theorem 31.1: marked-avoider bijection,
`b_n = Σ_σ M(σ)`; Lemmas 32.1–32.2 and Theorem 30.1: shared decreasing spine,
`b_n = Σ_{s+t+k=n−4} J_k(s) J_k(t)`, `R_{1243}` a positive series, rational
diagonal (23-index encoding), not algebraic (Bóna–Burstein Lemma 6.3);
Lemmas 35.1–35.3 and Proposition 36.1: Gaussian strip and endpoint bounds;
Section 37: `L_35 ≈ 0.62144`; Corollary 39.1; Theorem 40.3: `R + O(n^{-1/2})`;
Theorem 41.1: profile `e^{−u²/2}`, `e_t ~ D t^{-3/2}`, `R + o(n^{-1/2})`;
Section 43: a 40-variable rational constant term.

**Part V (Report 138).** Lemmas 45.1–45.2, Theorem 45.3: twenty cells, at most
three-point mixed chains, four-binomial gluing; Proposition 46.1, Theorem 46.2:
explicit boundary bijections; Lemmas 47.1–47.2, Theorem 47.3: harmless corner,
initial-filling saturation, six-term inverse-Cauchy formula,
`H_s(0) = A_{s+2} − A_{s+1}`; Theorem 48.1: rational diagonal, P-recursive;
Proposition 49.1: anisotropic domination; Lemma 50.1, Proposition 50.2:
`H_s(v)/A_s → h(v)`, `h(0) = 240`; Theorem 51.1: `U_n/A_n → R_5 ≥ 15/32768`;
Proposition 52.1: leading inverse.

**Part VI (Report 140).** Theorem 55.1: every fixed order, `r_0 = R_5`,
`r_1 = S_5`, no logarithms; (57.9): `α_1 = −135/8`; Theorem 58.1: weighted
half expansion; Section 59: `h, B` with checks `(240, −3720)`, `(224, −3600)`,
`(144, −2520)`; Proposition 60.1: `R_5 + S_5/n + O(n^{-2})` by an elementary
route; Theorem 61.1 and Lemma 61.2: regularized convolution for exponent
`15/2`, model products polynomial; Theorem 63.1: inverse to every order.

**Added by the write** (all marked `[write]`, dated 5 October 2026):
Proposition 6.1 — `liminf u_n/A_n ≥ Π_T` for the partial sums `Π_T` of the
series for `R`, without the domination lemmas, and the exact rational
`Π_44 > 0.50153` (the write's own program, which also reproduces `u_4 … u_15`
and `L_{40,10}` exactly); Remark 6.2 — why extrapolation pointed to `1/2`
(the terms `κ_3 log n/n³ ≈ 0.016` and `κ_4 log n/n⁴ ≈ −0.009` at `n = 200`
dwarf the margin `R − 1/2 > 0.0015`; exact ratios `u_n/A_n` = 0.70858,
0.73021, 0.71055, 0.69538, 0.69035 at `n` = 20, 30, 40, 46, 48); Remark 13.2 —
the hypotheses of Bostan–Lairez–Salvy Definition 1.1, Theorem 3.5 and
Corollary 3.6 (arXiv v2, read) and why the encodings of Parts II, IV and V meet
them; Remark 66.1 — one method, opposite outcomes; the pinning of Report 138's
two uncited literature claims to Bóna–Burstein Theorems 5.3 and 6.2 and
Waite's Corollary 4.4 (checked); dated supersession and cross-reference notes;
the further-questions subsections and Section 66.1; the front matter.

## What the report does not claim

Every limitation is printed in place. In short: **no closed form and no
certified decimal** for `R`, `S`, `S_2`, `r_3`, `R_{1243}`, `R_5`, `S_5`
(partial sums of the positive series are lower bounds only; partial sums of the
signed series bound nothing); **no effective constants or onsets** anywhere,
so no exact threshold algorithm (a shrinking error interval does not decide a
ceiling near an integer); no convergence, Gevrey bound or summability of the
full expansions, no exponentially small terms; no explicit differential
equation, recurrence or order bound (existence only), and the constant terms of
Parts II and IV are not asserted to be origin-regular rational diagonals; for
one `1243`, no first nonzero correction, no `O(n^{-1})` rate and no value of
`R_{1243}`; for one `12345`, no statement on algebraicity; no theorem for
other patterns, longer monotone patterns or several occurrences. The scoped
prior-art statements (P-recursiveness of A217057 and A224179 "not located"
earlier) are the manuscripts' own, not worldwide priority claims. The
numerical values quoted from the intake dossier (fits for `R`, an
extrapolation consistent with `149/160`, `R_5 ≈ 0.2044`) are uncertified
diagnostics. Finite checks of all six companions prove no asymptotic
statement; manifests and hashes are integrity records, not signatures.

## Further questions, and the standing rule

Each Part closes with "Further questions and research" (Sections 10.1, 22.1,
29.1, 42.1, 54.1, 65.1), which say which of its questions a later Part answers;
Section 66.1 collects the open problems of all six, with sources, what is known
and what is missing (Vladimir's standing rule of 4 October 2026):

1. certified values of `R`, `S`, `S_2`, `r_3` (134; 135 Q1; 137 Q1);
2. whether `R_{1243} = 149/160` (Conway–Guttmann; 136 Q1) — the intake's naive
   extrapolation gives 0.93157–0.93177, consistent, not a proof;
3. certified values of `R_5`, `S_5` (138 Q2; 140 Q1);
4. effective constants and onsets, direct and inverse (all Parts);
5. usable annihilating equations (135 Q2; 137 Q4; 136 Q4; 138 Q1 = 140 Q4);
6. coefficient growth, Gevrey order, summability (137 Q3; 140 Q2–Q3);
7. one `1243` beyond the square-root cancellation (136 Q3);
8. algebraicity for one `12345` (138 Q4);
9. longer patterns, other patterns, several occurrences (134; 137 Q5;
   138 Q5–Q6; 140 Q5–Q6).

Answered inside the merge, with dated notes at the questions: Report 134's first
and higher corrections and all-orders inverse (Parts II–III); Report 135's
question 3 and, in part, 4 (Part III); Report 137's question 5, in part
(Parts IV–VI); Report 138's question 3 (Part VI); Report 140's question 5, in
the negative for `1234` (Part III, Remark 66.1). **Nothing in the six
manuscripts was found to be wrong.** The one wrong claim on record is external:
Conway and Guttmann's `R = 1/2`, refuted with a proof in Part I. Report 138's
two uncited claims ("the known nonrationality result", "the cited even-length
nonalgebraicity theorem") are now cited.

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/`:

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a224182-unique-1432-order`
  (Report 139, same batch): exactly one `1432`, `Θ(9^n n^{-3})` with explicit
  constants, normalized by the same `A_n`; a minima-skeleton method unrelated
  to the half decompositions here; no cross-citation. A sibling, not a host.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a047874-long-increasing-subsequences`:
  permutations by longest increasing subsequence; `A^{(4)}_n`, `A^{(5)}_n` are
  its counts for length at most 3 and 4, and both reports use RSK and strip
  tableaux; it studies another regime. A cross-reference only.
- The transseries volume
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
  every inverse statement here is an instance of `p0:thm:staircase` (parts
  (1)–(2)), and Part I's `W_{-1}` formula of `p0:thm:lambert-core`. No new
  inversion theory is claimed.
- No other report treats A217057, A224179 or A224248 (searched 5 October 2026).

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository concerns
permutation patterns, A217057, A224179 or A224248 (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (all 48 staged files were checked
  against the pristine extraction again at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files). Only
  names changed (tables at the end).
- **Closed inventories: none of the verifiers runs in this directory.** Each
  `verify.py` hard-codes its delivery tree (`checks/fixtures.json`, `code/…`,
  `sources/…`, `manifest.json`, the PDF, and for Reports 135 and 137 the
  companion directories) and refuses missing or extra members; Report 136's
  verifier imports `tableaux` and `objects` by module name. Rerun from the
  archives (below).
- The delivered markdown uses delivery names: `137-allorders-SOURCES.md`
  (`Report137.tex`, `companion135/`, `checks/fixtures.json`),
  `135-rational-SOURCES.md` (`companion134/`), `138-leading-SOURCES.md` and
  `140-allorders-SOURCES.md` (`sources/…`, the nested ZIP),
  `136-unique1243-certificate-README.md` (`verify.py`, `expected.json`,
  `/tmp/…` output paths, `bundle-stage` with `/path/to/report-source`). Use a
  scratch directory outside the repository.
- `137-allorders-SOURCES.md` names an "independently reviewed" underlying proof
  source by SHA-256 (`0070de0a…`); it was never delivered, and the repository
  cannot check that review. It also calls Report 137's theorem "conditional on
  the explicitly inherited … inputs"; in this report those inputs are proved in
  Parts I–II (note in Section 23).
- `140-allorders-SOURCES.md` calls the nested Report 138 ZIP "corrected"; only
  one version of Report 138 exists in the bundle, and it is byte-identical to
  the standalone archive (so "corrected" refers to a revision before delivery).
- Report 140's two `sources/*.json` receipts record separately run checks whose
  scripts were not delivered; its replay does not rerun them (it says so).
- Two delivered JSON files lack a final newline
  (`data/138-leading-sources-independent_audit.json`,
  `data/140-allorders-sources-independent_extension_checks.json`); harmless.

## Rerunning the checks

Run on copies in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit, for example:

```
git show 60f54ea06:docs/incoming/A217057_All_Orders_Logarithmic_Asymptotics_and_Inversion_Source.zip > s137.zip
unzip -q s137.zip -d r137
python -I -B r137/Report137/verify.py check
python -I -B r137/Report137/verify.py replay --output OUT/replay137
python -I -B -O r137/Report137/verify.py replay --output OUT/replay137-opt     # must be byte-identical
python -I -B r137/Report137/verify.py selftest --output OUT/selftest137
```

`OUT` is an existing directory outside the extraction; each output target must
be new. The same `check` / `replay --output` / `selftest --output` commands
work for `Report134/verify.py` and `Report135/verify.py` (from their own
archives, or the companions inside Report 137's), and for
`Report138/verify.py` (plus `deep --output`, which compiles
`code/object_check.cpp` with a C++17 compiler). Report 136: inside
`Report136/certificate`, run `python -I -B verify.py check`, `replay`, `-O
replay` and `guard-test`. `build`, `pack` and `reproduce` compare PDFs and
archives byte for byte with the recorded TeX Live 2025 / pdfTeX 1.40.26
toolchain and are not expected to match elsewhere. Python 3.10 or later and
its standard library suffice (SymPy only for Report 135's optional
`kernel_sympy.py`).

**Windows.** Report 140's verifier rejects every Windows path ("REJECTED:
ambiguous path spelling": it refuses `\` in `str(Path)`), and its `selftest`
relies on POSIX `zipfile` behaviour. At placement it was run through two shims
outside the package (a wrapper that executes the delivered `verify.py` with
that one guard relaxed in memory, the manifest still hashing the file on disk;
and a scratch virtual environment whose `sitecustomize.py` makes `str(Path)`
use `/` and keeps `zipfile` from rewriting `\` in member names). The shims are
not shipped. Use a POSIX system, or such shims. The other five verifiers ran
on Windows without shims.

Results at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-105 intake dossiers): every `check` passed; `replay`
passed for all six (Report 134 about 63 s, 135 about 94 s, 137 about 21 s,
136 about 32 s, 138 about 2.5 min, 140 about 21 s with the shim), with normal
and `-O` outputs byte-identical where compared and equal to the recorded
fixtures (Reports 136, 138, 140); `selftest` passed (Report 134: 30 checks;
135: 31; 137: 49; 138: 55; 140: 47 cases with the shims); Report 136's
`guard-test` passed (25 tests); Report 138's `deep` passed (object round trips
for `n = 5 … 10`); the `pack` commands of Reports 134, 135 and 137 reproduced
the delivered archives byte for byte. At the write (5 October 2026, fresh
extraction from `60f54ea06`, Windows): Report 137's `check` and `replay`
passed, and Report 140's `check` was rejected by its path guard as described.
The write's own independent computation for Proposition 6.1 (a short
standard-library Python program, not shipped) runs in about 4 seconds.

## Rights

Repository contents are MIT-0. **OEIS data** are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)) and occur in
`data/134-amplitude-fixtures.json` (A217057, `n ≤ 15`),
`data/135-rational-exact_data.json` (`u_0 … u_20`; the first 16 agree with the
OEIS fixture, the rest are recomputed), `data/136-unique1243-certificate-fixtures.json`
(A224179, `n ≤ 25`), `data/138-leading-sources-A047889.seq` and
`data/138-leading-sources-A224248.seq` (snapshots of the official `oeisdata`
repository), `data/138-leading-sources-b047889_0_24.txt` (the first 25 lines
of Gheorghe Coserea's A047889 b-file) and the fixtures that repeat them.
**`data/138-leading-sources-oF12345a`** is the output of B. Nakamura and
D. Zeilberger's programs for exactly one `12345` (40 terms), as published at
<https://sites.math.rutgers.edu/~zeilberg/tokhniot/oF12345a> (the URL given in
the package's inventory; captured 2 October 2026); no licence is stated; it is
a list of enumeration counts, credited to its authors and shipped unchanged
because Report 138's checks read it. Credit also goes to Conway and Guttmann
for the conjectures this report refutes or leaves open, to Bóna and Burstein
and to Waite for the order, nonrationality and nonalgebraicity results cited,
to Regev for the avoidance asymptotics, and to Bostan, Lairez and Salvy for the
closure theorem. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 121 pages, no errors, no warnings, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull or underfull
boxes. The six delivered `.tex` files also compile with MiKTeX pdfLaTeX (12,
22, 13, 24, 17 and 18 pages).

## Delivered path → shipped path

| Report | Delivered | Shipped |
|---|---|---|
| 134 | `Report134/Report134.tex` | not shipped; printed as Part I |
| 134 | `Report134/certificate.py`, `independent.py`, `verify.py` | `code/134-amplitude-<name>` |
| 134 | `Report134/fixtures.json` | `data/134-amplitude-fixtures.json` |
| 134 | `Report134/README.md`, `Report134.pdf`, `manifest.json` | not shipped |
| 135 | `Report135/Report135.tex` | not shipped; printed as Part II |
| 135 | `Report135/SOURCES.md` | `135-rational-SOURCES.md` |
| 135 | `Report135/kernel_sympy.py`, `refinements.py`, `second_refinements.py`, `unitary_checks.py`, `verify.py` | `code/135-rational-<name>` |
| 135 | `Report135/exact_data.json`, `second_exact_data.json` | `data/135-rational-<name>` |
| 135 | `Report135/README.md`, `Report135.pdf`, `manifest.json`, `companion134/` (8) | not shipped (`companion134/` = Report 134's files) |
| 137 | `Report137/Report137.tex` | `article.tex` (Part III) |
| 137 | `Report137/README.md` | replaced by this guide |
| 137 | `Report137/SOURCES.md` | `137-allorders-SOURCES.md` |
| 137 | `Report137/verify.py` | `code/137-allorders-verify.py` |
| 137 | `Report137/code/<name>.py` | `code/137-allorders-code-<name>.py` |
| 137 | `Report137/checks/fixtures.json` | `data/137-allorders-checks-fixtures.json` |
| 137 | `Report137/Report137.pdf`, `manifest.json`, `companion135/` (20) | not shipped (`companion135/` = Reports 135 and 134's files) |
| 136 | `Report136/Report136.tex` | not shipped; printed as Part IV (Sections 4–5 in Part I) |
| 136 | `Report136/certificate/README.md` | `136-unique1243-certificate-README.md` |
| 136 | `Report136/certificate/bundle.py`, `objects.py`, `tableaux.py`, `verify.py` | `code/136-unique1243-certificate-<name>` |
| 136 | `Report136/certificate/expected.json`, `fixtures.json` | `data/136-unique1243-certificate-<name>` |
| 136 | `Report136/README.md`, `Report136.pdf`, `bundle-manifest.json`, `certificate/manifest.json` | not shipped |
| 138 | `Report138/Report138.tex` | not shipped; printed as Part V |
| 138 | `Report138/SOURCES.md` | `138-leading-SOURCES.md` |
| 138 | `Report138/verify.py` | `code/138-leading-verify.py` |
| 138 | `Report138/code/exact.py`, `object_check.cpp` | `code/138-leading-code-<name>` |
| 138 | `Report138/checks/fixtures.json` | `data/138-leading-checks-fixtures.json` |
| 138 | `Report138/sources/<name>` (6) | `data/138-leading-sources-<name>` |
| 138 | `Report138/README.md`, `Report138.pdf`, `manifest.json` | not shipped |
| 140 | `Report140/Report140.tex` | not shipped; printed as Part VI |
| 140 | `Report140/SOURCES.md` | `140-allorders-SOURCES.md` |
| 140 | `Report140/verify.py` | `code/140-allorders-verify.py` |
| 140 | `Report140/code/exact.py` | `code/140-allorders-code-exact.py` |
| 140 | `Report140/checks/fixtures.json` | `data/140-allorders-checks-fixtures.json` |
| 140 | `Report140/sources/<name>` (3) | `data/140-allorders-sources-<name>` |
| 140 | `Report140/README.md`, `Report140.pdf`, `manifest.json`, `dependencies/Report138_reproducible.zip` | not shipped (the ZIP = Report 138's archive) |

## Provenance

Six manuscripts (bundle Reports 134, 135, 136, 137, 138, 140) → one report;
base 137, printed as Part III. Arrival `60f54ea06`, placement `e85586b7c`,
write batch 105 (5 October 2026). No manuscript pins a ProveIt commit. Merge
choices (dependency order with the base third; Report 136's repeated Sections
4–5 printed once; the restated inputs of Reports 135, 137 and 140 printed in
full with pointers; Report 136's appendix as Section 43; the merged
bibliography with entries for Reports 134, 135 and 138 pointing to Parts I, II
and V) are listed in the article's front matter, "Provenance and merge
decisions".
