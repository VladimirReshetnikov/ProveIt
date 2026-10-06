# Pop-Stacked Permutations

**OEIS A307030 and A309993: an explicit exponential generating function, every pole simple, infinitely many positive poles, non-D-finiteness, a quadratic-time recurrence and certified constants; an operator proof of the leading asymptotic with all-orders inversion; the run distribution, Gaussian laws and the fixed-run denominator conjecture; the predictions of Claesson, Guðmundsson and Pantone proved, and their printed pole list corrected**

This is a research report built on 6 October 2026 (write batch 108) from three
manuscripts of one external research session, Reports 164, 161 and 166 of the
session bundle of Reports 1–243, all dated 3 October 2026. A permutation is
*pop-stacked* if it lies in the image of one pass of pop-stack sorting (reverse
every maximal decreasing run); equivalently, its consecutive maximal ascending
runs `(a,b)`, `(c,d)` satisfy `a < d` and `c < b` (Asinowski, Banderier, Billey,
Hackl and Linusson). With `p_n` their number (`p_0 = 1`;
[A307030](https://oeis.org/A307030)) and `p_{n,k}` the number with `k` runs
([A309993](https://oeis.org/A309993)):

- **Part I** (Report 164, the base): `P(z) = Σ p_n zⁿ/n! = N(z)/D(z)` with
  `Q = 4eᶻ − 1`, `B = 2e^{z/2} + 1`, entire `H`, `J₀` (locally
  `cos(zr/4)`, `sin(zr/4)/r`, `r = √Q`), `N = e^{−z}Q(H + BJ₀)`,
  `D = BH − QJ₀`. The pole set is `{D = 0, Q ≠ 0}`; every pole is simple with
  residue `−2e^{−2ζ}(4e^ζ − 1)/(ζ + 2)`; the positive poles are exactly
  `ρ₀ < ρ₁ < …`, one for each `k ≥ 0`, so `P` is not D-finite and `(p_n)` is not
  P-recursive; `P` is differentially algebraic of order at most two; a Riccati
  equation gives `p_0,…,p_N` in `O(N²)` arithmetic operations; and
  `p_n = C n! ρ^{−n}(1 + O(θⁿ))` with `ρ = ρ₀ = 1.11343904173672…`,
  `C = 2e^{−2ρ}(4e^ρ − 1)/(ρ(ρ + 2)) = 0.69568854907063…`, both certified by
  rational intervals (widths `10⁻⁵⁶`, `10⁻⁴⁸`).
- **Part II** (Report 161): the same leading asymptotic by a self-contained
  spectral and analytic Fredholm argument, without the explicit formula;
  `(24/23)^{1/4} ≤ ρ ≤ 2` by elementary counting; fixed-order Stirling
  expansions, a two-ceiling threshold bracket, and every fixed order of the
  continuous inverse by an explicit recursion.
- **Part III** (Report 166): the bivariate EGF
  `P(z,u) = Q(H + BJ₀)/(h₀(BH − QJ₀))` (with `u`-dependent `Q`, `B`, `h₀`; at
  `u = 1` it is Part I's formula); the run count `K_n` of a uniform
  pop-stacked permutation has `E K_n = μn + β + O(ηⁿ)`,
  `Var K_n = vn + γ + O(ηⁿ)`, `μ = 0.44214954918886…`, `v = 0.06008555058270…`
  (closed forms, certified), a central limit theorem and a uniform lattice local
  limit theorem with error `O(1/n)`; and an alternate proof of Conjecture 2 of
  Claesson–Guðmundsson–Pantone (the fixed-run denominators
  `∏_{j≤k}(1 − jx)^{k−j+1}`, numerator degree `k(k+1)/2`, with the leading
  coefficient). A proof by Shivam Patel, posted on MathDB on 20 August 2026,
  came first; Part III credits it.
- **Added by the write**: the front matter; **Remark 5.1**, an interval-arithmetic
  proof that the list of positive poles printed by Claesson–Guðmundsson–Pantone
  omits `ρ₁₂ = 5.338876712720…` and that each of its fifteen values is a correct
  truncation; the check of their three printed complex pairs; the check of
  Patel's proof; the classification of the inverses against the transseries
  volume; dated notes; Section 33.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Exact generating function for pop stacked permutations: Poles differential algebraicity and faster enumeration* (author line "Report 164", 3 October 2026); the base | 164 | `Pop_Stacked_Permutations_Exact_Generating_Function_and_Poles_Source.zip` (464,784 bytes, 16 files; `Report164.tex`, 856 lines, 15 pp.) | none | `602e5bd0f` | Part I, Sections 1–13, plus the write's Remark 5.1 |
| *Factorial exponential growth of pop stacked permutations: An operator proof and asymptotic inversion* (author line "Report 161", 3 October 2026) | 161 | `Pop_Stacked_Permutations_Asymptotics_and_Inverses_Source.zip` (517,332 bytes, 15 files; `Report161.tex`, 806 lines, 13 pp.) | none | `602e5bd0f` | Part II, Sections 14–20 |
| *Run distribution in pop stacked permutations: An explicit bivariate generating function and Gaussian laws* (author line "Report 166", 3 October 2026) | 166 | `Pop_Stacked_Permutations_Run_Distribution_Source.zip` (579,822 bytes, 19 files; `Report166.tex`, 901 lines, 16 pp.) | none | `602e5bd0f` | Part III, Sections 21–32, plus the write's Section 33 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `602e5bd0f` (batch 108, cluster 108-POP) removed them from
`docs/incoming/`. The write is "Write batch 108
(a307030-pop-stacked-permutations): new report, pop-stacked permutations, CGP's
predictions proved".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. No manuscript names an author, a tool or an addressee, says it
is AI-assisted, or carries "prepared for private review" wording; the three PDF
author fields are empty. Every result, proof, remark, question and limitation
of the three manuscripts is printed.

## Why the Parts are in this order

The base is Report 164; its `Report164.tex` was staged as `article.tex`, and it
is printed first, as Part I. It is the fullest statement on A307030: it contains
Report 161's main theorem as its Theorem 9.2 with the amplitude in closed form,
and it has the pole set, residues, non-D-finiteness, differential algebraicity,
the recurrence and the certificate, which neither other manuscript has. Report
161 is Part II (its operator proof is a second route to Theorem 9.2; its
all-orders inverse goes beyond Part I). Report 166 is Part III: its bivariate
formula reduces to Part I's at `u = 1`, but it proves none of the pole results.
The manuscripts were written in the order 161, 164, 166 within about an hour and
a half on 3 October 2026; none cites another in its bibliography.

## Files

The directory holds 41 files: 7 at the root, 21 in `code/`, 13 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 164, prefix `164-egf-`** (12 files): the companion's README; `code/`:
the exact companion (count, quotient verification, certificate), its tests, and
the release tools (PDF builder, ZIP builder, I/O helpers, release tests);
`data/`: the source provenance, the release receipt, the rational certificate,
the count fixture `p_0…p_70` and the two-route verification.

```
164-egf-companion-README.md
code/164-egf-build_pdf.py
code/164-egf-companion-pop_egf.py
code/164-egf-companion-test_pop_egf.py
code/164-egf-make_zip.py
code/164-egf-release_tools.py
code/164-egf-test_release.py
data/164-egf-SOURCE_PROVENANCE.json
data/164-egf-author_review_receipt.json
data/164-egf-data-constant_certificate.json
data/164-egf-data-counts_p0_p70.json
data/164-egf-data-verification_n70.json
```

**Report 161, prefix `161-operator-`** (11 files): the companion's README;
`code/`: the exact companion (counts by the endpoint recurrence, finite checks,
source data, bounded threshold search), its tests, and the release tools;
`data/`: the source provenance, the counts `p_0…p_70`, the finite checks and the
source data.

```
161-operator-companion-README.md
code/161-operator-build_pdf.py
code/161-operator-companion-pop_stacked.py
code/161-operator-companion-test_pop_stacked.py
code/161-operator-make_zip.py
code/161-operator-release_tools.py
code/161-operator-test_release.py
data/161-operator-SOURCE_PROVENANCE.json
data/161-operator-data-counts.json
data/161-operator-data-finite_checks.json
data/161-operator-data-source_data.json
```

**Report 166, prefix `166-runs-`** (15 files): the companion's README and its
computational and fixture provenance; `code/`: the companion (`run_checks.py`
driver and its three modules, the test runner) and the release tools; `data/`:
the source provenance, the release receipt, the test record and the full
verification record (complete rows `p_n(u)` for `n ≤ 40`).

```
166-runs-companion-PROVENANCE.md
166-runs-companion-README.md
code/166-runs-build_pdf.py
code/166-runs-companion-run_checks.py
code/166-runs-companion-run_filtration.py
code/166-runs-companion-run_polynomials.py
code/166-runs-companion-run_slopes.py
code/166-runs-companion-run_tests.py
code/166-runs-make_zip.py
code/166-runs-release_tools.py
code/166-runs-test_release.py
data/166-runs-SOURCE_PROVENANCE.json
data/166-runs-author_review_receipt.json
data/166-runs-data-companion_tests.json
data/166-runs-data-full_verification.json
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs;
`Report161.tex` and `Report166.tex` (printed as Parts II and III) and the
delivered `README.md` of Reports 161 and 166 (Report 164's was staged and is
replaced by this guide); the three `SHA256SUMS` files (checksum manifests,
14/14, 15/15 and 18/18 verified at placement; repository policy drops checksum
manifests).

**One chain between the packages.** Report 164's count fixture
(`data/164-egf-data-counts_p0_p70.json`) names `Report161/data/counts.json` as
its source and records its SHA-256, `d42dae1bbac32f2b…`; the same hash is in
`data/164-egf-data-verification_n70.json` and in the companion
(`_SOURCE_SHA256`). It is the SHA-256 of the shipped
`data/161-operator-data-counts.json` (checked at the write). So `p_26…p_70` in
Report 164's fixture come from Report 161's endpoint-recurrence computation;
only `p_1…p_25` are posted OEIS terms, as the fixture says.

## Labels and numbering

Label prefix **`psp:`** (none at HEAD before this report): Part I uses
`psp:egf:` (Report 164's 58 labels), Part II `psp:op:` (Report 161's 46), Part
III `psp:run:` (Report 166's 55). Sixteen bare names occur in two or three
manuscripts (`eq:overlap`, `eq:resolvent`, `eq:rho`, `lem:perron`, `sec:main`,
`thm:main`, …); under the Part prefixes they are distinct. The write added the
three Part labels `psp:egf:part`, `psp:op:part`, `psp:run:part`; Remark 5.1's
`psp:egf:rem:cgp-poles`; labels for two unlabelled delivered statements of Part
I, `psp:egf:lem:sufficiency` (Lemma 3.1) and `psp:egf:prop:ceil` (Proposition
11.1); the front matter's `psp:sec:guide`, `…:status`, `…:cgp`, `…:oeis`,
`…:inverses`, `…:notation`, `…:provenance`, `…:trust`, `…:neighbours`; and
Section 33's `psp:sec:further` with the twelve items `psp:q:effective`,
`psp:q:threshold`, `psp:q:nonreal`, `psp:q:ode`, `psp:q:complexity`,
`psp:q:polar`, `psp:q:denominators`, `psp:q:limits`, `psp:q:betagamma`,
`psp:q:preimage`, `psp:q:data`, `psp:q:literature`. 187 labels in all, all
distinct (159 delivered, 28 added). The two bibliography keys `oeis` became
`oeisA307030` (Parts I, II) and `oeisA309993` (Part III).

| Part | Manuscript | Section here | Statements and equations |
|---|---|---|---|
| I | Report 164 | `k` (1–13, unchanged) | `k.j`, unchanged; Remark 5.1 added after (5.4) |
| II | Report 161 | `k + 13` (14–20) | `(k + 13).j` |
| III | Report 166 | `k + 20` (21–32); 33 added | `(k + 20).j` |

All three manuscripts number statements and equations within sections, so a
member's numbers move only with their sections: Report 161's Theorem 1.1 →
**14.1**, Lemma 2.1 → **15.1**, Lemma 3.1 → **16.1**, Corollary 6.1 →
**19.1**, Theorem 6.2 → **19.2**, Proposition 6.3 → **19.3**, equations
(1.1)–(7.2) → (14.1)–(20.2); Report 166's Theorems 1.1, 1.2 → **21.1, 21.2**,
Lemma 3.1 → **23.1**, Lemma 5.1 → **25.1**, Theorem 10.1 → **30.1**,
equations (1.1)–(10.3) → (21.1)–(30.3). A comparison of the build's `.aux`
with separate builds of the three delivered `.tex` files confirmed all 159
delivered labels under these offsets and prefixes. The delivered READMEs, code
and data use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: the overlap kernel is **`K`** in Parts I and III and **`J`** in Part
II, while **`K_n`** is Part III's run count and **`J₀`**, **`J₁`** are Part I's
functions; the interval states are **`Δ`** (I, III) and **`D`** (II), while
**`D`** is also Part I's denominator, Part II's Fredholm matrix and Part III's
`D(z,u)` and `D_k(x)`; **`μ`** is the measure in Parts I–II and the mean slope
in Part III (which writes `ν` for the measure); **`H`** is Part I's entire
function, Part II's log-Gamma model (Part I's `𝓗`) and Part III's `H(z,u)`;
**`u`** is Part I's `W(L_y/(eρ))`, Part II's `log(x₀/ρ)` — exactly one more —
and Part III's run marker; **`v`**, **`q`/`θ`/`η`**, **`r`**, **`T`**, **`L`**,
**`C`**, **`B`**, **`𝓕`** (Part I's resultant, Part II's inverse series),
**`h`**, **`d`**, **`β`**, **`δ`**, **`N`**, **`M`**, **`Q`**, **`κ`**,
**`x`/`X`**. The transseries volume's symbols are subscripted `vol` where they
meet these (`h_vol`, `κ_vol`, `d_vol`, …). Same in all Parts: `p_n`, `P`, `ρ`,
`w_z`, `A_z`, `λ`, `lo`, `hi`, `spr`, `B_{2j}`, `W`. Claesson–Guðmundsson–
Pantone write `a_n` for `p_n` and `μ` for `ρ`.

## What the report claims

**Part I (Report 164).**
- Theorem 1.1: the formula above, the local form (1.6), the pole set (1.7),
  simple poles with residue (1.8), infinitely many positive poles,
  non-D-finiteness, non-P-recursiveness, D-algebraicity. Section 2: the
  mixed run-state model and the resolvent (2.4); Section 3: the cumulative
  boundary problem and the sufficiency Lemma 3.1; Section 4: the solution and
  the half-angle cancellation.
- Section 5: the phase `φ(z) = zr/4 + ½ arccos(1/(2e^{z/2}))`, `φ' > 0`, the
  positive poles `φ(ρ_k) = π/2 + kπ`; the ordinary series is not D-finite
  either. Section 6: the Riccati equation (6.1), removable zeros of `Q`, simple
  poles, the exact pole set, finite-radius pole expansions (6.3).
- (7.1): the resultant annihilator (order at most two; not claimed minimal).
- (8.1): the recurrence, `O(N²)` arithmetic operations and `O(N)` storage,
  against `O(N⁴)`/`O(N³)` in the cited papers (constant-cost arithmetic only).
- Theorem 9.2: unique dominant pole, `p_n = C n! ρ^{−n}(1 + O(θⁿ))`, closed `C`.
  (10.1): `L < ρ < U`, `C_L < C < C_U`, by exact rational arithmetic.
- Section 11: Stirling expansions (11.2), Proposition 11.1 (two-ceiling
  bracket), one Newton step (11.4).

**Part II (Report 161).**
- Theorem 14.1 with `ρ` and `C` defined spectrally (14.4)–(14.6) (the same
  numbers as Part I's; proved in a note), `(24/23)^{1/4} ≤ ρ ≤ 2`, meromorphic
  continuation with the single pole `ρ` in a disk of radius `R > ρ`.
- Lemma 15.1 (the image characterization, proved; prior, credited); the
  labelled-simplex normalization; Lemma 16.1 (Perron); Section 17 (analytic
  Fredholm continuation, the simple pole (17.3)); Section 18 (strict
  domination, the elementary bracket).
- Corollary 19.1, Theorem 19.2, Proposition 19.3 (all fixed orders of the
  continuous inverse by the recursion (19.10)); Section 20: the prior endpoint
  recurrence of Claesson–Guðmundsson–Pantone as used by the companion.

**Part III (Report 166).**
- Theorem 21.1 (bivariate EGF), Theorem 21.2 (moments, CLT, local limit);
  Lemma 23.1 (sufficiency of the Robin problem); Section 24 (cancellation);
  Section 25 (isolation); Section 26 (uniform transfer with a moving pole,
  (26.2), the amplitude `C(u)` (26.4)); Section 27 (exact slopes);
  (28.1) (certificates for `ρ`, `μ`, `v`); Section 29 (CLT and lattice local
  limit); Theorem 30.1 (fixed-run representation, leading coefficient
  `(−1)^{k(k+1)/2+1} ∏_{j≤k} j!`).

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter; the dated notes; Section 33; and **Remark 5.1** with its proof. For
real `z > 0`, `D(z) = √((2E+1)² + r²) cos φ(z)`, so the positive poles are the
zeros of `D`, and at `ρ_k` the quantity `zr/(4π)` lies in `(k + ¼, k + ⅓)`. For
each printed value `s` with `d` decimals, interval arithmetic (mpmath `iv`, 120
digits) shows that `D` changes sign on `[s, s + 10^{−d}]` and fixes `k`: the
list is `ρ₀,…,ρ₁₁, ρ₁₃, ρ₁₄, ρ₁₅`, every printed digit correct, and the same
check at `5.3388767127` gives `k = 12`. The remark lists `ρ₀,…,ρ₁₉` to twelve
decimals.

## The predictions of Claesson, Guðmundsson and Pantone

Claesson, Guðmundsson and Pantone, *Counting pop-stacked permutations in
polynomial time* (arXiv:1908.08910, v1 of 23 August 2019; Experimental
Mathematics 2021), was read by the write (arXiv v1 and the 12-page author PDF,
whose SHA-256 `e822a3fc…` is the one Parts I and III record; same pagination).
- Section 1 (p. 2) calls a generating function or closed form an open problem:
  **answered** by Part I's Theorem 1.1 for the exponential generating function.
- Section 3.2, **Conjecture 2** (p. 9): `F_k(x) = N_k(x)/∏_{i=1}^k (1 − ix)^{k−i+1}`
  with `deg N_k = k(k+1)/2`: **proved**, first by Patel, then by Part III.
- Section 3.3 (p. 10): fifteen predicted positive singularities, "predicted to
  have critical exponent −1, making them simple poles"; "may posses an
  infinite number of singularities. If true, this would imply the
  non-D-finiteness of both the ordinary and exponential generating functions":
  **proved** (Part I). Three complex pairs, also simple poles: they are zeros
  of `D` with `Q ≠ 0` (numerically), hence simple poles.
- The constants (pp. 10–11): `μ ≈ 1.11343904…` (75 decimals), `μ⁻¹`, `C ≈
  0.69568854907…` (58 decimals), `a_n ~ C·n!·(0.898118…)ⁿ`: **proved** with an
  exponentially small relative error and `C` in closed form.

**On record (Remark 5.1).** The printed list of positive singularities omits
`ρ₁₂ = 5.33887671271979787…`: it jumps from `5.2155880127…` (`ρ₁₁`) to
`5.4532009642…` (`ρ₁₃`). Every printed value is a correct truncation (interval
proof); the authors' repository file `singularity_estimates.txt` (commit
`9c58ae6`, 20 August 2019, the only commit touching it) lists twenty positive
values including `ρ₁₂`, all within their stated last-digit uncertainty, so the
omission is in the paper's transcription. The three printed complex pairs are
correct to 62–66 decimal places; from there each printed string is the
repository's with two consecutive digits deleted (floating-point Newton
iteration in 220 digits; the repository's values agree to 110 or more digits).
Neither is an error of a theorem: the paper presents experimental estimates.

**Asinowski–Banderier–Hackl** (*Flip-sort and combinatorial aspects of
pop-stack sorting*, DMTCS 22:2, 2021; read by the write): Section 2.4 (p. 18)
calls an exact asymptotic analysis "a challenge" and reports the conjectures
above; Theorem 12 (p. 18) is the interleaving lower bound that Part II
re-proves without citing it (noted in Section 18); the total-count costs
`O(N⁴)`/`O(N³)` are in the discussion after Theorem 11 (pp. 16–17); the
conclusion (p. 37) leaves "the optimal cost of the computation of pop-stacked
permutations" open (still open: Part I lowers the operation count only).

**Patel's proof and priority.** Part III (Section 30) credits Shivam Patel's
inclusion–exclusion proof of Conjecture 2, posted on MathDB on 20 August 2026
(14:02:52 UTC, edited 14:04:08 UTC), and calls its own proof an alternate one.
At intake (6 October 2026) the page returned HTTP 403; at the write it was
reachable and was read in full. The site's progress summary marks the problem
"Claimed solved" and says the posted proof "has not been independently
verified". The write checked each step (word encoding, inclusion–exclusion over
the two failure orientations of each adjacency, first-occurrence
classification `x^k Σ_σ ∏(1 − m_j x)^{−1}`, the probabilistic evaluation of
`lim_{x→∞} F_k = −1`) and found it correct and complete for the denominator, the
exact degree and the leading coefficient, as Part III says. Patel also proves
`N_k(1) = 2(−1)^{k(k+1)/2−1} ∏_{j=1}^{k−1} j!` for `k ≥ 2`; checked against
`N_2,…,N_5`. Priority: Patel (20 August 2026) precedes Part III (3 October
2026); no peer-reviewed proof is known to the write.

**The OEIS entries** (read 6 October 2026). A307030: revision #63 of Nov 18
2021, Cyril Banderier (Mar 20 2019), offset 1, b-file `n ≤ 450` by Bjarki
Ágúst Guðmundsson, no formula or asymptotic. The write ran Part I's recurrence
to `n = 450`: all 450 b-file terms reproduced. A309993: revision #21 of Aug 29
2019, Bjarki Ágúst Guðmundsson (Aug 26 2019), column g.f.s for `k ≤ 5` (the
fixtures Part III uses, from p. 10 of Asinowski–Banderier–Hackl; compared), a
5050-term b-file (`n ≤ 100`), not checked. **Nothing was submitted to the
OEIS.**

**The inverses and the transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
Instances: the initializer `x₀ = L/W(L/(eρ))` (Parts I and II) of the factorial
core `p0:prop:factorial-core` (`κ_vol = 1`, `d_vol = −(1 + log ρ)`; the
proposition's `v_vol` is Part I's `u`, and its slope `v_vol + 1` is Part II's
`u`); Part II's recursion (19.10) of `p0:thm:core-reversion` with
`R_vol = ℚ(u, b)`, `Λ = u`, `h_vol = 0` and `f_vol ∈ tR_vol[[t, E]]` written
out in the front matter (formal series only; the asymptotic statement is Part
II's). Analogue: Part I's (11.4) (= Part II's (19.8)) is the first-order term
of `p0:eq:operator-series` about that core, with its own error bound. Not an
instance: the two-ceiling bracket (Proposition 11.1 = Theorem 19.2), proved
directly at the integers without an interpolation; when its ceilings agree it
reaches the conclusion of `p0:thm:staircase` (2), whose failure mode both Parts
describe.

## What the report does not claim

Every limitation is printed in place. In short: the overlap characterization,
the counting algorithms and recurrences, the numerical estimates and the
spectral, perturbation, quasi-power and Fourier methods are prior, as the
manuscripts say; none makes a worldwide priority claim (bounded searches of 3
October 2026), and Part I says scholarly review is appropriate before any
submission. **Part I**: no effective complex gap, error constant or onset; no
ordering of nonreal poles and no convergent infinite pole sum; the annihilator
is not claimed minimal or to determine `P`; no bit complexity, wall-clock
guarantee, optimality or run-refined bound; the certified intervals give no
complex gap. **Part II**: no certified decimals and no isolation interval
narrower than `[(24/23)^{1/4}, 2]`; no effective `R`, `M`, `n_0`; no
finite-input threshold certificate; no statement on further poles or
non-D-finiteness (both now proved by Part I; dated notes); no fixed truncation
is a rounding rule. **Part III**: uniform on distinct outputs, not on inputs; no
global bivariate polar set, no minimal fixed-run denominator, no refined-count
complexity gain, no Edgeworth expansion, no global large deviations, no
certified onset; `β`, `γ` uncertified; the A309993 b-file unchecked; no
first-resolution claim for Conjecture 2. **All packages**: finite checks prove
no asymptotic statement; manifests and receipts detect changes and validate no
theorem.

## Further questions, and the standing rule

Section 33 collects (Vladimir's standing rule of 4 October 2026), with sources,
sketches and what is missing:

1. effective complex gap, error constants and onsets (all Parts); a
   floating-point argument-principle count by the write finds exactly 1, 2, 3
   zeros of `D` in `|z| < 2, 3, 3.5`, so the second pole by modulus appears to
   be `ρ₁ = 2.417…` (not certified);
2. a finite-input threshold certificate (Parts I, II);
3. the nonreal poles: ordering, distribution, convergent pole sums (Part I);
4. a minimal differential equation (Part I);
5. bit complexity and optimal cost (Part I; Asinowski–Banderier–Hackl's
   question, re-scoped: operation count lowered, optimality open); faster
   run-refined counting (Part III);
6. the bivariate polar set (Part III; answered at `u = 1` by Part I);
7. minimal fixed-run denominators (Part III; Patel's `N_k(1) ≠ 0` keeps
   `(1 − x)^k`);
8. Edgeworth, large deviations, tail-relative errors (Part III);
9. certified `β`, `γ` (Part III; the write's numerics agree with all printed
   digits);
10. the distribution under a uniformly random input (Part III);
11. data not checked (the A309993 b-file; the journal version of the CGP paper);
12. literature and priority.

**Corrected, with proof**: the positive-pole list printed by
Claesson–Guðmundsson–Pantone omits `ρ₁₂` (Remark 5.1, interval proof); their
three printed complex pairs lose two digits after decimal place 62–66
(Remark 5.1, floating-point). **Proved** (by the Parts): their Section 3.3
predictions and their Conjecture 2 (Patel first). **Superseded, sentences
kept** (dated notes): Part II's statements that further poles, non-D-finiteness
and certified decimals are not proved. **Credit added**: Part II's interleaving
bound is Asinowski–Banderier–Hackl's Theorem 12. No mathematical statement of
the three manuscripts was found wrong.

## Relation to neighbouring reports

- No other placed report treats A307030, A309993, pop-stack sorting, or the
  papers of Claesson–Guðmundsson–Pantone and Asinowski et al., and none uses
  the integral-operator method of Ehrenborg–Kitaev–Perry that all three Parts
  credit (searched 6 October 2026).
- Nearest by subject: `a113226-vincular-avoiders` (EGFs and asymptotics of a
  permutation class defined by adjacency conditions); no shared lemma.
- The transseries volume, for the inverses (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file treats pop-stacked permutations
(searched 6 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 38 staged code, data and companion
  files and the two staged base files were checked against a fresh extraction
  from `60f54ea06` at the write: 0 differences; `article.tex` and this README
  then replaced the two staged base files). Only names changed (tables at the
  end).
- **Nothing should be run in this directory.** The companions are written for
  the delivered layout (`companion/…`, `data/…`, run from the package root).
  Report 161's and Report 164's command-line computations read no files and
  write JSON to standard output, so on a copy of this directory
  `python -B code/161-operator-companion-pop_stacked.py counts` and
  `python -B code/164-egf-companion-pop_egf.py verify --n 70` also work under
  the shipped names (checked on a copy at the write); Report 166's
  `run_checks.py` imports its sibling modules by their delivered names and
  fails under the shipped names, and the test suites and release tools expect
  the delivered layout. Rerun from the archives (below).
- The release tools (`build_pdf.py`, `make_zip.py`, `release_tools.py`,
  `test_release.py`) require POSIX descriptor facilities: on Windows 10 of 11
  release tests error (`os.mkfifo`, `O_NOFOLLOW`), as the dossier records; they
  build the PDF and ZIP from `Report16x.tex` and an allowlist checked against
  `SHA256SUMS`, which are not shipped.
- The companion READMEs (`161-operator-companion-README.md`,
  `164-egf-companion-README.md`, `166-runs-companion-README.md`) and
  `166-runs-companion-PROVENANCE.md` use delivered paths (`companion/…`,
  `data/…`, `reproduction/…`, `Report16x.tex`, `/tmp/report16x-…`). The JSON
  provenance and receipt files name delivered paths and the unshipped PDFs and
  manifests.
- On Windows the companions write CRLF line ends to a redirected standard
  output; compare after removing carriage returns.
- The manuscripts' bibliographies differ in detail for the same works (for
  example the links for Asinowski et al. 2019 and for Defant–Williams); the
  merged bibliography keeps all of them, attributed to the Parts.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (all three archives are flat):

```
git show 60f54ea06:docs/incoming/Pop_Stacked_Permutations_Asymptotics_and_Inverses_Source.zip > r161.zip
git show 60f54ea06:docs/incoming/Pop_Stacked_Permutations_Exact_Generating_Function_and_Poles_Source.zip > r164.zip
git show 60f54ea06:docs/incoming/Pop_Stacked_Permutations_Run_Distribution_Source.zip > r166.zip
mkdir x161 x164 x166 && unzip -q r161.zip -d x161 && unzip -q r164.zip -d x164 && unzip -q r166.zip -d x166
cd x161
python -B companion/pop_stacked.py counts  | tr -d '\r' | cmp - data/counts.json
python -B companion/pop_stacked.py verify  | tr -d '\r' | cmp - data/finite_checks.json
python -B companion/pop_stacked.py sources | tr -d '\r' | cmp - data/source_data.json
python -B -m unittest discover -s companion -p 'test_pop_stacked.py' -v
cd ../x164
python -B companion/pop_egf.py verify --n 70 | tr -d '\r' | cmp - data/verification_n70.json
python -B companion/pop_egf.py certify      | tr -d '\r' | cmp - data/constant_certificate.json
python -B -m unittest discover -s companion -v
cd ../x166
python -B companion/run_checks.py all --n 40 --literal 9 --filtration 12 --include-data | tr -d '\r' | cmp - data/full_verification.json
python -B companion/run_tests.py
```

Each also runs with `python -B -O`. Standard library only; Python 3.9 or later.
Results: at placement (dossier of batch 108, 6 October 2026, Python 3.14.4,
Windows, on copies) every computation reproduced its delivered output
(LF-identical), and the companion tests passed (17/17 for Report 161, about
60 s; 16/16 for Report 164; Report 166's test record reproduced), in normal and
`-O` mode; Report 164's `certify` takes about 28 s there. At the write (6
October 2026, fresh extractions) Report 161's `counts`, `verify` and `sources`,
Report 164's `verify --n 70` and `certify`, and Report 166's full
`run_checks.py` check (about 13 s) reproduced the shipped files byte for byte
after removing carriage returns. The PDF and ZIP replays (TeX Live, POSIX)
were not run.

## Rights

Repository contents are MIT-0. OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)): Report 161's
`data/161-operator-data-source_data.json` holds the 25 terms of A307030 shown in
the entry and the 45 terms of Table 1 of Claesson–Guðmundsson–Pantone; Report
164's count fixture contains the 25 OEIS terms `p_1…p_25`; Report 166's
companion and `166-runs-companion-PROVENANCE.md` contain the five fixed-run
numerators published by Asinowski–Banderier–Hackl (p. 10), which are also the
column generating functions of A309993. No paper PDF is shipped. The OEIS
entries are credited for the sequences, Asinowski, Banderier, Billey, Hackl and
Linusson for the characterization, Claesson, Guðmundsson and Pantone for the
counting algorithm, the data and the predictions, Asinowski, Banderier and
Hackl for the fixed-run results and the lower bound, Shivam Patel for the first
proof of Conjecture 2, and Ehrenborg, Kitaev and Perry for the spectral method.
Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy of `article.tex` (no other inputs);
commit only `article.pdf`. The build (59 pages): no errors, no undefined or
multiply defined references or citations, no duplicate destinations, no
overfull or underfull boxes, no warnings. The log carries one "Infinite glue
shrinkage found in box being split" message, from the notation longtable
breaking across pages. The three delivered `.tex` files compile with MiKTeX
pdfLaTeX to 13, 15 and 16 pages with no warnings.

## Delivered path → shipped path

Report 164 (`164-egf-`; delivered flat, no top-level directory):

| Delivered | Shipped |
|---|---|
| `Report164.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `companion/README.md` | `164-egf-companion-README.md` |
| `companion/pop_egf.py`, `companion/test_pop_egf.py` | `code/164-egf-companion-<name>` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/164-egf-<name>` |
| `data/<name>.json` | `data/164-egf-data-<name>.json` |
| `SOURCE_PROVENANCE.json`, `author_review_receipt.json` | `data/164-egf-<name>` |
| `Report164.pdf`, `SHA256SUMS` | not shipped |

Report 161 (`161-operator-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report161.tex` | not shipped; printed as Part II of `article.tex` |
| `companion/README.md` | `161-operator-companion-README.md` |
| `companion/pop_stacked.py`, `companion/test_pop_stacked.py` | `code/161-operator-companion-<name>` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/161-operator-<name>` |
| `data/<name>.json` | `data/161-operator-data-<name>.json` |
| `SOURCE_PROVENANCE.json` | `data/161-operator-SOURCE_PROVENANCE.json` |
| `README.md`, `Report161.pdf`, `SHA256SUMS` | not shipped |

Report 166 (`166-runs-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report166.tex` | not shipped; printed as Part III of `article.tex` |
| `companion/README.md`, `companion/PROVENANCE.md` | `166-runs-companion-<name>` |
| `companion/run_*.py` | `code/166-runs-companion-<name>` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/166-runs-<name>` |
| `data/<name>.json` | `data/166-runs-data-<name>.json` |
| `SOURCE_PROVENANCE.json`, `author_review_receipt.json` | `data/166-runs-<name>` |
| `README.md`, `Report166.pdf`, `SHA256SUMS` | not shipped |

## Provenance

Three manuscripts (bundle Reports 164, 161, 166) → one report; base 164,
printed as Part I. Arrival `60f54ea06`, placement `602e5bd0f`, write batch 108
(6 October 2026). No manuscript pins a commit. Merge choices (base first, then
161 and 166; the repeated normalization, Perron and certificate arguments
printed in each Part as delivered, with pointers; members' numbers offset by
section; the merged bibliography with the two `oeis` keys split) are listed in
the article's front matter, "Provenance and merge decisions".
