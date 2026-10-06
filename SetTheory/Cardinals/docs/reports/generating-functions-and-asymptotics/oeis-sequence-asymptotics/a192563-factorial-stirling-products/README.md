# Factorial-Weighted Stirling Products

**OEIS A192563 and A192561: diagonal poly-Cauchy numbers at all fixed orders, and matched cycles with exact certificates, all orders and inverses; an identity for the third member, A192562**

This is a research report built on 6 October 2026 (write batch 107) from two
manuscripts of one external research session, Reports 154 and 155 of the
session bundle of Reports 1–243, both dated 3 October 2026. They treat two
members of one OEIS family entered by Emanuele Munarini on 4 July 2011,
sums over `k` of `k!` times a product of two Stirling numbers
(`[n,k]` unsigned first kind, `{n,k}` second kind):

- [A192563](https://oeis.org/A192563): `a_n = Σ_k k! [n+1,k+1] {n+1,k+1} = Σ_m [n,m] (m+1)^n`,
  the diagonal of the poly-Cauchy array [A344639](https://oeis.org/A344639),
  `A_{n,k} = Σ_m [n,m] (m+1)^k`;
- [A192561](https://oeis.org/A192561): `b_n = Σ_k k! [n+1,k+1]²`;
- [A192562](https://oeis.org/A192562): `c_n = Σ_k k! [n,k] {n+1,k+1}` (treated by neither manuscript).

- **Part I** (Report 154, the base): with the exact saddle
  `r = log n − log log n − log log log n + o(1)` of `e^z Γ(n+e^z)/Γ(e^z)`, an
  expansion of `a_n` to every fixed order in `r/n` whose coefficients are
  explicit Gaussian contraction polynomials in exact cumulants; the same
  expansion for `A_{n,k}` uniformly for `α ≤ k/n ≤ β`; a smooth model, eventually
  increasing, whose inverse brackets both threshold indices
  (`⌊ν_R − ε_R⌋ + 1 ≤ T_≥ ≤ T_> ≤ ⌈ν_R + ε_R⌉`, equality cases included); and the
  nested-logarithm inverse `ν = L/(2ℓ)[1 + ((3/2)log ℓ + 1 + log 2)/ℓ + O((log ℓ)²/ℓ²)]`.
- **Part II** (Report 155): `b_n/(n!)²` is the Gaussian Fock norm of
  `∏_{j≤n}(1+z/j)`; an exact positive expansion with an explicit tail at every
  `n ≥ 1` (`S₂ ≤ 1/φ`), a rational-centre certificate that isolates
  `b_10 = 1273270076895432`, the same certificate for finite products with
  negative real zeros, `b_n = (n!)² e^{w²+1}/(2πw) (Σ_{r<R} A_r w^{−r} + O(w^{−R}))`
  with `w = W₀(en)` and rational `A_0, …, A_10` (`1, −1/6, 55/72, 1381/6480, …`), and a
  nested-Lambert inverse with a two-ceiling threshold bracket.
- **Added by the write**: Proposition 23.1, with a complete proof:
  `c_n = a_n − n A_{n−1,n} = Σ_m [n−1,m]((m+2)^n − (m+1)^n) = n! [z^n] (e^z − 1) F_{n−1}(z)`
  for every `n ≥ 1`; and what the two methods suggest for the asymptotics of
  A192562 (an open question, with numerical evidence).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Diagonal poly Cauchy permutations at all fixed orders: Exact saddle expansion and inverse thresholds for OEIS A192563* (author line "Report 154", 3 October 2026); the base | 154 | `Diagonal_Poly_Cauchy_All_Orders_and_Inverse_Thresholds_Source.zip` (24 files, 714,622 bytes unpacked; `Report154.tex`, 1311 lines, 19 pp.) | none | `3988bf5c4` | Part I, Sections 1–11 |
| *Exact positive certificates and all orders for matched cycles: Factorial weighted squared Stirling numbers in OEIS A192561* (author line "Report 155", 3 October 2026) | 155 | `Matched_Cycles_Exact_Certificates_All_Orders_and_Inverses_Source.zip` (22 files, 923,684 bytes unpacked; `Report155.tex`, 1243 lines, 20 pp.) | none | `3988bf5c4` | Part II, Sections 12–22 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `3988bf5c4` (batch 107, cluster 107-STIRL) removed them from
`docs/incoming/`. The write is "Write batch 107
(a192563-factorial-stirling-products): new report, diagonal poly-Cauchy
numbers and matched cycles".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee or
names a ProveIt commit; each sets an empty PDF author field. Every result,
proof, remark, question and limitation of the two manuscripts is printed.

## Why one report, and why this order

The two manuscripts use different methods and do not cite each other (they
share only the DLMF). They are one report because they treat two members of one
OEIS family and fit one frame: with `⟨f,g⟩ = Σ_k k! [t^k]f [t^k]g` (Part II's
(18.3)), `n!P_n(z) = Σ_k [n+1,k+1] z^k` and `T_n(z) = Σ_k {n+1,k+1} z^k`,

`A192561(n) = ⟨n!P_n, n!P_n⟩`, `A192563(n) = ⟨n!P_n, T_n⟩`, `A192562(n) = ⟨z(z+1)⋯(z+n−1), T_n⟩`,

and Part I's coefficient function is Part II's polynomial after `z ↦ e^z − 1`:
`F_n(z) = n! e^z P_n(e^z − 1)`. Part II's sequence is a norm, and Part II uses
the positivity of a translated Gaussian norm; Part I's is a pairing, and Part I
extracts a coefficient on a circle controlled by a positive exponential sum.
Both sequences have the factorial core `2n log n − 2n`; `log(a_n/b_n) =
−n log log n + O(n log log n/log n)`. The front matter's "One family, two
methods" gives the details; the intake's alternative, two single-source
reports, was not taken.

The base is Report 154; its `Report154.tex` was staged as `article.tex` and is
printed first, as Part I: it treats the whole array A344639, and it has the
lower bundle number. There is no dependency between the Parts.

## Files

The directory holds 40 files: 5 at the root, 14 in `code/`, 21 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 154, prefix `154-polycauchy-`** (20 files): the companion README;
`code/`: the PDF builder, archive packer, shared descriptor-pinned I/O helpers
and their 12 release tests, the exact checker, its 33 tests, and the optional
mpmath diagnostics; `data/`: the source provenance record, the companion's
claims, inputs (the 17-term OEIS prefix) and pinned requirement, its recorded
results (exact, numerical and tests, each in normal and `-O` mode, and the run
commands), and the release-test record.

```
154-polycauchy-companion-README.md
code/154-polycauchy-build_pdf.py
code/154-polycauchy-companion-exact_checks.py
code/154-polycauchy-companion-numerical_diagnostics.py
code/154-polycauchy-companion-test_companion.py
code/154-polycauchy-make_zip.py
code/154-polycauchy-release_tools.py
code/154-polycauchy-test_release.py
data/154-polycauchy-SOURCE_PROVENANCE.json
data/154-polycauchy-companion-claims.json
data/154-polycauchy-companion-inputs.json
data/154-polycauchy-companion-requirements-numerical.txt
data/154-polycauchy-companion-results-exact-optimized.json
data/154-polycauchy-companion-results-exact.json
data/154-polycauchy-companion-results-numerical-optimized.json
data/154-polycauchy-companion-results-numerical.json
data/154-polycauchy-companion-results-run_commands.json
data/154-polycauchy-companion-results-tests-optimized.json
data/154-polycauchy-companion-results-tests.json
data/154-polycauchy-release_checks.json
```

**Report 155, prefix `155-matched-`** (17 files): the companion README;
`code/`: the PDF builder, archive packer, release helpers and tests, the exact
Fock companion (`fock_exact.py`: enumeration, certificate, coefficient
generator), its safe-I/O module and its 28 tests; `data/`: the source
provenance record, the companion's claims, the two certificate inputs and the
five recorded results (certificates for `n = 10` and `n = 0`, coefficients
through `A_10`, enumeration to `n = 10`, the verification record).

```
155-matched-companion-README.md
code/155-matched-build_pdf.py
code/155-matched-companion-fock_exact.py
code/155-matched-companion-safe_io.py
code/155-matched-companion-test_companion.py
code/155-matched-make_zip.py
code/155-matched-release_tools.py
code/155-matched-test_release.py
data/155-matched-SOURCE_PROVENANCE.json
data/155-matched-companion-claims.json
data/155-matched-companion-inputs-certificate_n0.json
data/155-matched-companion-inputs-certificate_n10.json
data/155-matched-companion-results-certificate_n0.json
data/155-matched-companion-results-certificate_n10.json
data/155-matched-companion-results-coefficients_A10.json
data/155-matched-companion-results-enumeration_n10.json
data/155-matched-companion-results-verification.json
```

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`Report155.tex` (printed as Part II) and the delivery READMEs (Report 154's was
staged and is replaced by this guide); the `SHA256SUMS` files (Report 154's
root manifest, 23 entries; Report 155's root manifest, 21 entries, and its
companion manifest, 12 entries; all verified at placement; repository policy
drops checksum manifests).

## Labels and numbering

Label prefix **`sfp:`** (none at HEAD before this report): Part I uses
`sfp:pc:` (Report 154's 94 labels), Part II `sfp:mc:` (Report 155's 90). Seven
bare names occur in both manuscripts (`eq:definition`, `eq:main`,
`eq:normalization`, `eq:saddle`, `sec:sources`, `thm:inverse`, `thm:main`);
under the Part prefixes they are distinct. The write added the two Part labels;
labels for the subsections it cites (`sfp:pc:sub:signs`, `…:sub:screen`;
`sfp:mc:sub:protocol`, `…:roots`, `…:complexity`, `…:beyond`, `…:weights`); the
front matter's `sfp:sec:guide`, `…:status`, `…:oeis`, `…:family`, `…:inverses`,
`…:notation`, `…:provenance`, `…:trust`, `…:neighbours`; and Section 23's
`sfp:sec:further`, `sfp:sub:a192562`, `sfp:prop:a192562`, `sfp:eq:a192562`,
`sfp:rem:a192562` and the twelve items `sfp:q:a192562`, `…:effective`,
`…:transition`, `…:laws`, `…:nested`, `…:shifted`, `…:growing`, `…:twoscale`,
`…:roots`, `…:complexity`, `…:weights`, `…:literature`. 219 labels in all, all
distinct (94 in the staged `article.tex` before the write, all bare).

| Part | Manuscript | Section here | Statement and equation `k.j` |
|---|---|---|---|
| I | Report 154 | `k` (1–11, unchanged) | `k.j` |
| II | Report 155 | `k + 11` (12–22); 23 added | `(k+11).j` |

Both manuscripts number statements and equations within sections. Report 155's
Lemma 3.1 and Theorems 3.2, 3.3 are 14.1, 14.2, 14.3; its Theorem 4.1 is 15.1;
its Proposition 6.1 is 17.1; its Theorems 7.1, 7.2 are 18.1, 18.2; its Theorem
8.1 is 19.1; its Table 1 is Table 2. A comparison of the build's `.aux` with
separate builds of the two delivered `.tex` files confirmed all 184 delivered
labels under these offsets and prefixes. The delivered READMEs, code and data
use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed; Part II's macro `\stir` is defined as Part I's
`\sone` (same printed symbol). The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a reading-conventions table. The main
collisions: **`a`** (Part I's sequence A192563; Part II's saddle point
`a = a_n ~ log n`), **`b`, `B`** (Part I's `b = κ₂` and Bernoulli cumulant
polynomials `B_j(p)`; Part II's sequence `b_n`, a centre `b`, `B_n = b_n/(n!)²`,
Bernoulli numbers and polynomials), **`A`** (the array `A_{n,k}`; the
coefficients `A_r`), **`r`, `t`** (Part I's saddle and `e^r`; Part II's index and
translation variable), **`E`** (contraction polynomials `E_q`, `E₁ ~ −r/(12N)`;
Stirling-series coefficients `E_r`, `E₁ = −1/6`), **`C`, `c`**, **`L`**, **`H`, `h`**,
**`P`, `Q`**, **`F`, `Y`, `ν`, `v`** (Part II's `F_R` is a *logarithmic* model),
**`N`, `T`, `X`** (Part II has only the nonstrict threshold `N(T)`), **`q`, `K`, `D`**,
**`λ`, `η`, `ρ`, `δ`**, **`u`, `s`, `w`, `x`**, **`m`, `J`, `M`, `U`, `R`**. Same in both: `n`,
the first-kind Stirling numbers, `ψ`, natural logarithms. The write's own
letters (front matter and Section 23): `c_n` for A192562, `z^{\overline n}` for
the rising factorial, `𝔗_n` for the second-kind row polynomial, `φ_n` for
`(e^z−1)/(e^z+n−1)`.

## What the report claims

**Part I (Report 154).**
- The identities: `a_n/n! = E(C_n+1)^n` for the cycle count `C_n`; the
  Bényi–Ramírez Stirling product (2.1), with a short complete re-proof, so
  that `a_n` equals Munarini's defining form for every `n`; the coefficient
  form (2.4) and double generating function (2.5) (all prior art, credited).
- Lemmas 3.1–3.3: the exact saddle exists, is unique and smooth;
  `r = log N − log log N − log log log N + o(1)`; `κ_j ~ N r^{j−1}`.
- Theorem 1.1: `a_n = n! e^{L_n(r)}/(r^n √(2πb)) (Σ_{q<R} E_q + O_R((r/n)^R))` for
  every fixed `R`, with `E₁ = κ₄/(8b²) − 5κ₃²/(24b³) ~ −r/(12n)` and `E₂` (5.1);
  the whole complementary circle by a positive exponential sum (Lemma 4.2).
- Theorem 1.2: the same for `A_{n,k}`, uniformly for `α ≤ k/n ≤ β`.
- Theorem 1.3: the smooth model `Y_R` is eventually increasing, the bracket
  above for `T_≥` and `T_>` with `ε_R = C_R (log ν)^{R−1}/ν^R` (asymptotic, no
  effective constant or onset), and the nested-logarithm inverse with relative
  remainder `O(m²/ℓ²)`; `a_{n+1} > a_n` (8.1).

**Part II (Report 155).**
- (13.3)–(13.7): the classical Fock identity, the translation identity and a
  global product bound.
- Lemma 14.1 (`S₂ ≤ min{a/(a+1), 1/a} ≤ 1/φ`); Theorem 14.2: for every `n ≥ 1` and
  `K ≥ 2`, `B_n = e^{−a²} P_n(a)² (C_{n,K} + ε)`, `0 ≤ ε ≤ (K+1)((K+1)S₂/K)^K ≤ e(K+1)φ^{−K}`;
  Theorem 14.3: the same for `∏(1+z/λ_j)`, `λ_j > 0`, with only `S₂ < 1`
  (priority not established).
- Theorem 15.1 and Section 15: the rational-centre certificate with rational
  exponential enclosures; `b_10` isolated in an interval of width
  `< 2283679986302/10^30`.
- Section 16: exact-centre asymptotics, the weight-six expansion (16.3), the
  two-dimensional Gaussian approximation.
- Proposition 17.1 (reduction to the universal Gamma norm, error `O(w²/n)`);
  Theorems 18.1, 18.2: every fixed order in `1/w`, coefficients by an exact
  rational recurrence, Table 2 through `A_10`.
- Section 19: strict increase; `log b_n = 2n(log n − 1) + O((log n)²)`; the leading
  inverse `u = L/(2W₀(L/(2e)))`; Theorem 19.1, the centre `v_R` with
  `⌈v_R − C_R D^{−R−1}⌉ ≤ N(T) ≤ ⌈v_R + C_R D^{−R−1}⌉` (constants and onset not
  supplied); a finite certificate protocol.

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter, including the OEIS entries as read on 6 October 2026, the frame of the
family and the status of each inverse relative to the transseries volume;
dated notes; and Section 23 with:
- **Proposition 23.1**: for every `n ≥ 1`, `c_n = a_n − n A_{n−1,n} =
  Σ_{m<n} [n−1,m]((m+2)^n − (m+1)^n) = n![z^n](e^z−1)F_{n−1}(z)`; in particular
  `0 < c_n < a_n`. Proof: the first-kind recurrence
  `[N+1,i] = N[N,i] + [N,i−1]` applied to the diagonal of (2.1) (the first
  equality) and inside (1.1) (the second), and `F_n = (e^z+n−1)F_{n−1}` (the third).
- **Remark 23.2** (numerical, not a bound): at `n = 10, 20, 50, 100, 200, 400`,
  `c_n/a_n` falls from 0.26 to 0.10 and agrees with `φ_n(r) = (e^r−1)/(e^r+n−1)`
  at Part I's saddle to a relative error below 0.006, which divided by `r/n`
  lies between −0.08 and +0.04.

**The OEIS statements.** The three entries were read on 6 October 2026
(A192561 #10 of Jun 25 2024; A192562 #4 of Mar 30 2012; A192563 #13 of May 26
2021; all "_Emanuele Munarini_, Jul 04 2011"), and A344639 #35 of Apr 15 2025
(Stefano Spezia, May 25 2021). Their names are quoted verbatim in the front
matter; e.g. A192563's is "a(n) = Sum_{k=0..n}
abs(Stirling1(n+1,k+1))*Stirling2(n+1,k+1)*k!." and A344639's first formula
"A(n, k) = Sum_{m=0..n} abs(S1(n, m)) * (m + 1)^k". The listed terms of all
four agree with exact recomputation, and A192563's b-file (n ≤ 270) with Part
I's definition. No entry states an asymptotic formula. What Part I proves
about A344639: its identities (credited), and Theorem 1.2, an expansion to
every fixed order uniform for `α ≤ k/n ≤ β`, whose diagonal is Theorem 1.1;
nothing for fixed rows or columns (`k/n → ∞` or `0`, Part I's question 2), nor
for any other regime with `k/n → 0` or `k/n → ∞` (such as `k = n log n`;
widened after the independent check of 6 October 2026), nor for the
antidiagonal sums A344640. **Nothing was submitted to the OEIS.**

**The inverses** (transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
No inverse is an instance of `p0:thm:lambert-core`. Part II's leading inverse
(19.3) is an **instance** of `p0:prop:factorial-core` with `κ = 2`, `d = −2`
(`v = W₀(L/(2e))`, `X = e^{v+1} = L/(2v)`). Part II's Theorem 19.1 and Part I's
bracket (1.17) round smooth models that are not interpolations of the sequences,
so they are **not** instances of `p0:thm:staircase`; they are analogues of its
separation condition (2). Part I's nested inverse (1.18) is **not** an instance
of `p0:prop:factorial-core` (the term `−N log log N`); in the variables
`ξ = log log X`, `Z = log N` its first correction agrees with the first two
coefficients that `plt:thm:lw-template` produces from the truncated datum
`(ρ, μ, β, b₁) = (1, 1, log 2, −λ/2 − 1)` (checked by the write), but the template is
formal and Part I proves its own remainder: an analogue, not an instance.

## What the report does not claim

Every limitation is printed in place. In short: fixed orders only in both
Parts, no estimate uniform in the order, no optimal truncation, no
exponentially small sectors, no convergence of Part II's series in `1/w`, no
Borel summability; no numerical constants or onsets for any asymptotic
remainder or inverse window (Part I's `C_R`, Part II's `C_R`, `T_R`), so neither
asymptotic inverse is a finite-input rounding oracle (Part II's finite Fock
certificate is, for given `n`); `E₁ ~ −r/(12n)` and the nested-log formula must
not replace `E₁` and `ν_R`; no extension of `a_n` to non-integer indices; Part
I's novelty provisional on Yakymiv's 2019 paper (full text not read by the
manuscript) and other uninspected texts; Part II's general certificate
"elementary consequence of classical Fock theory", priority not established,
the golden bound specific to `λ_j = j`, `q = K/(K+1)` not the off-saddle
optimizer, the `1/n`-scale correction not computed; Wilf's unweighted result
and the Fock identity credited as antecedents. **Both companions**: finite exact
checks prove no asymptotic remainder; manifests and hashes detect changes and
validate no theorem.

## Further questions, and the standing rule

Part I's Section 11 and Part II's Section 22 are the manuscripts' own; Section
23 collects them with the stated non-claims (Vladimir's standing rule of 4
October 2026), with sources, sketches and what is missing:

1. the asymptotics of A192562, `c_n = a_n φ_n(r)(1 + O(r/n))`? — Part I's route
   (the extra factor `e^z − 1` on Part I's contour) and why Part II's
   positivity does not transfer to a pairing (the write);
2. effective constants, onsets and certified thresholds (Part I q. 1; Part II §22.3);
3. the regimes `k/n → 0` and `k/n → ∞` of A344639 (Part I q. 2);
4. limit laws under the moment weights (Part I q. 3; Part II §22.4);
5. further explicit nested-log inverse terms (Part I q. 4);
6. restricted and shifted families (Part I q. 5);
7. growing orders, optimal truncation, exponentially small terms, Borel
   summability (Part I q. 6; Part II §22.3);
8. the `1/n`-scale correction for A192561 (Part II §22.3);
9. root classes beyond the arithmetic progression (Part II §22.1);
10. complexity, ball arithmetic and the off-saddle optimizer (Part II §22.2);
11. other factorial weights `(k!)^α` (Part II §22.4);
12. literature and priority: Yakymiv, Komatsu–Szalay, Komatsu 2019, the final
    transform paper; Bender–Richmond, Gao–Laferrière–Panario.

**Refuted or corrected**: nothing; no claim of either manuscript was found
wrong. **Answered inside the merge**: none of the manuscripts' questions.

**Independent check of the write (6 October 2026).** An adversarial check
made by the intake after the write (`774c233c4`) re-proved Proposition 23.1
(A192562) line by line and checked it exactly: the first two forms and
`0 < c_n < a_n` for `1 ≤ n ≤ 300`, the third form by genuine power-series
multiplication in `ℚ[[z]]` for `1 ≤ n ≤ 30`. A192562 has no independent
b-file (the OEIS one is synthesized from the 17 listed terms), so only those
are compared, as the report says. Part I's Subsection 2.1 with the write's
one-line identity `(m+1)^k = Σ_j {k+1, j+1} (m)_j` proves Munarini's form
equal to A192563 for every `n`; exact checks of the Bényi–Ramírez identity
(`n, k ≤ 80`), the one-line identity (`m, k ≤ 60`) and both forms against the
whole A192563 b-file (`n ≤ 270`). Both cited Lean ingredients exist with the
stated content. The instance and analogue classifications were re-derived
(Part II's leading inverse is a factorial-core instance with `κ = 2`,
`d = −2`; the brackets are staircase analogues; Part I's nested-log inverse
agrees with the Lambert template to first order only). All listed terms of
A192561, A192562, A192563 (17 each) and A344639 (55) agree, revisions and
quotations are exact; Theorem 1.1's relative error at `R = 1` is
`−4.834·10⁻³ … −1.101·10⁻³` for `n = 50 … 300` and `−1.49·10⁻⁵ … −4.18·10⁻⁷`
after the first correction; Remark 23.2 reproduces to every printed digit.
No mathematical error was found and no correction is required. One precision
is added (with a dated note keeping the first wording): Theorem 1.2 says
nothing about any regime with `k/n → 0` or `k/n → ∞`, not only about fixed
rows and columns (Part I's note after Theorem 1.2, the front matter, and
above). The record is a dated note at the end of Section 23.

## Relation to neighbouring reports

- No other report treats A192561, A192562, A192563, A344639 or poly-Cauchy
  numbers (searched 6 October 2026).
- `a064856-stirling-catalan-transforms` (same batch): Stirling transforms of
  the Catalan numbers; `a122399-surjection-diagonal`: an all-orders saddle
  expansion of a two-parameter array uniform for compact aspect ratios (as Part
  I's Theorem 1.2); `a139383-iterated-bell-diagonals`: coefficients `n![z^n]` of
  functions that change with `n` (as Part I's (2.4)); `a277364-bell-asymptotics`:
  partial row sums of second-kind Stirling numbers;
  `a124380-signed-moment-asymptotics`: `Σ_k z^k ∏_{j≤k}(1+jz)`. Parallels of
  object or method only; no shared definition, lemma or constant.
- The transseries volume (above), for the inverses.

No reciprocal notes were needed.

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized. The two classical identities that Part I's re-proof of
(2.1) combines are formalized in the FabiusFunction Lean layer:
`Fabius.X_pow_eq_sum_stirlingSecond_succ_mul_descPochhammer_comp`
(`Analysis/FabiusFunction/Lean/FabiusFunction/StirlingShiftedEvaluations.lean`;
`X^n = Σ_k S(n+1,k+1) (X−1)^{\underline k}`) and
`Fabius.stirlingFirst_succ_succ_eq_sum_choose`
(`.../StirlingBasisChange.lean`; `[n+1,k+1] = Σ_j [n,j] C(j,k)`). The product
identity (2.1) itself, Proposition 23.1, and every asymptotic statement are not.

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 39 staged files were checked
  against a fresh extraction from `60f54ea06` at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files).
  Only names changed (tables at the end). The delivered code and markdown use
  delivery paths (`companion/`, `companion/results/`, `companion/inputs/`,
  `Report154.tex`, `Report155.tex`, `README.md`, `SHA256SUMS`,
  `release_tools.py`), which are shipped under other names or not at all.
- **Renamed modules break imports: nothing runs in this directory.** Report
  154's companion imports `release_tools` from its parent directory; Report
  155's tests import `fock_exact` and `safe_io`; both `build_pdf.py` and
  `make_zip.py` hard-code `ReportNNN.tex`, their allowlists, `/proc/self/fd` and
  Debian TeX paths (`/usr/share/texlive/texmf-dist`, `/usr/share/texmf`). Rerun
  from the archives (below).
- The companions' output safety needs POSIX (`O_NOFOLLOW`, `O_DIRECTORY`,
  directory-relative opens; Report 155 also `os.mkfifo` and hard links).
  Report 154's companion README asks for Python 3.10 or later, its delivery
  README (not shipped) for 3.11; Report 155's for 3.11. The releases were run
  with CPython 3.12.
- The companion READMEs give `/tmp/...` example output paths; use a scratch
  directory outside the repository.
- Report 154's bibliography and provenance record say that the A192563
  b-file was not retrieved; the write read it (front matter).

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (both archives are flat):

```
git show 60f54ea06:docs/incoming/Diagonal_Poly_Cauchy_All_Orders_and_Inverse_Thresholds_Source.zip > r154.zip
git show 60f54ea06:docs/incoming/Matched_Cycles_Exact_Certificates_All_Orders_and_Inverses_Source.zip > r155.zip
mkdir x154 x155 && unzip -q r154.zip -d x154 && unzip -q r155.zip -d x155
cd x154
python3 -B companion/exact_checks.py > ../exact154.json
python3 -B -O companion/exact_checks.py > ../exact154-O.json
python3 -B companion/test_companion.py
python3 -B companion/numerical_diagnostics.py > ../numerical154.json    # needs mpmath==1.3.0
cd ../x155/companion
python3 -B fock_exact.py certificate --input inputs/certificate_n10.json --output results/replay_n10.json
python3 -B fock_exact.py certificate --input inputs/certificate_n0.json --output results/replay_n0.json
python3 -B fock_exact.py coefficients --order 10 --output results/replay_A10.json
python3 -B fock_exact.py enumerate --n 10 --output results/replay_enumeration_n10.json
python3 -B -m unittest -v test_companion
python3 -O -B -m unittest -v test_companion
```

Compare `../exact154.json` with `x154/companion/results/exact.json` (and the
`-O` output with `exact-optimized.json`, the diagnostics with `numerical.json`),
and each replay with its delivered result, with `cmp`; on Windows redirected
output has CRLF line ends, so remove carriage returns first. Report 154's
`--output` option and Report 155's `--output` need a POSIX host; on Windows,
use standard output for Report 154, and for Report 155 replace
`safe_io.read_json`/`safe_io.write_new_json` by a plain read and an exclusive
(`"xb"`) write that keep `safe_io.encoded_json` and the JSON validation (the
intake's replay did exactly this). The release tools need the Debian-style TeX
Live of the delivery and were not run.

Results: at placement (5–6 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-107 dossier) Report 154's exact and numerical outputs
reproduced byte for byte and 31 of 33 tests passed with the intake's POSIX
shim; Report 155's four results regenerated byte for byte through the
replacement above and 24 of 28 tests passed unshimmed. At the write (6 October
2026, fresh extractions, Windows): `exact.json`, `exact-optimized.json` and
`numerical.json` (mpmath 1.3.0) reproduced byte for byte after removing CR (about
1 s and 3 s); Report 154's tests unshimmed: 23 of 33 passed, the 10 output-safety
tests stop with "POSIX O_NOFOLLOW is required"; Report 155's four results
regenerated byte for byte (about 3 s); its tests: 24 of 28, the four `SafeIO`
tests stop on POSIX requirements (`O_NOFOLLOW`/`O_DIRECTORY`, `os.mkfifo`). The
delivered records (`tests.json`, `verification.json`) report 33/33 and 28/28 on
Linux. The two delivered `.tex` files compile with MiKTeX pdfLaTeX to 19 and 20
pages with no warnings.

## Rights

Repository contents are MIT-0. Report 154's
`data/154-polycauchy-companion-inputs.json` embeds the 17-term prefix of
A192563 from the official OEIS data mirror; OEIS data are available under
CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). Report 155's tests and
results contain `b_10` and the terms `b_0, …, b_10`, recomputed by the
companion. The OEIS entries are credited for the sequences (Emanuele Munarini;
Stefano Spezia for A344639 and the b-file), Bényi–Ramírez for the poly-Cauchy
interpretation and the Stirling product, and every source as the manuscripts
cite it. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build (52
pages at the write, 53 after the independent check): no errors, no undefined or multiply defined references or citations, no
duplicate destinations, no overfull or underfull boxes, no warnings. The log
carries one "Infinite glue shrinkage found in box being split" message, from
the notation longtable breaking across pages 6–7 (the delivered `.tex` files
have none).

## Delivered path → shipped path

Report 154 (`154-polycauchy-`; delivered flat, no top-level directory):

| Delivered | Shipped |
|---|---|
| `Report154.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/154-polycauchy-<name>` |
| `SOURCE_PROVENANCE.json`, `release_checks.json` | `data/154-polycauchy-<name>` |
| `companion/README.md` | `154-polycauchy-companion-README.md` |
| `companion/exact_checks.py`, `numerical_diagnostics.py`, `test_companion.py` | `code/154-polycauchy-companion-<name>` |
| `companion/claims.json`, `inputs.json`, `requirements-numerical.txt` | `data/154-polycauchy-companion-<name>` |
| `companion/results/<name>` (7 files) | `data/154-polycauchy-companion-results-<name>` |
| `Report154.pdf`, `SHA256SUMS` | not shipped |

Report 155 (`155-matched-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report155.tex` | not shipped; printed as Part II of `article.tex` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/155-matched-<name>` |
| `SOURCE_PROVENANCE.json` | `data/155-matched-SOURCE_PROVENANCE.json` |
| `companion/README.md` | `155-matched-companion-README.md` |
| `companion/fock_exact.py`, `safe_io.py`, `test_companion.py` | `code/155-matched-companion-<name>` |
| `companion/claims.json` | `data/155-matched-companion-claims.json` |
| `companion/inputs/<name>` (2 files) | `data/155-matched-companion-inputs-<name>` |
| `companion/results/<name>` (5 files) | `data/155-matched-companion-results-<name>` |
| `README.md`, `Report155.pdf`, `SHA256SUMS`, `companion/SHA256SUMS` | not shipped |

## Provenance

Two manuscripts (bundle Reports 154, 155) → one report; base 154, printed as
Part I. Arrival `60f54ea06`, placement `3988bf5c4`, write batch 107 (6 October
2026). Neither manuscript pins a commit. Merge choices (one report rather than
two, the base first, the merged bibliography with the two DLMF entries kept
apart, `\stir` defined as `\sone`) are listed in the article's front matter,
"Provenance and merge decisions".
