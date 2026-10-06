# The Weighted Dyck Newton Triangle

**OEIS A258219, A258220 and A292692: Bala's Riccati and continued-fraction conjecture, Kotěšovec's asymptotic form and growth rate for the Newton diagonal, all fixed orders on the interior, and the upper-edge transition**

This is a research report built on 5 October 2026 (write batch 105) from
three manuscripts of one external research session, Reports 141, 142 and 143
of the session bundle of Reports 1–243, dated 2, 2 and 3 October 2026. They
study one object. Give a peak at `(a,b)` of a Dyck path the weight `k + a/b`
and let `p_N(k)` be the total weight of the paths of semilength `N`
(OEIS [A258219](https://oeis.org/A258219)). Its falling-factorial (Newton)
coefficients `P_{N,m} = [k^(m falling)] p_N(k) = Δ^m p_N(0)/m!` form the
triangle [A258220](https://oeis.org/A258220), whose diagonal
`a_n = P_{2n,n}` is [A292692](https://oeis.org/A292692)
(`1, 6, 217, 13997, 1283817, …`). Throughout, `α = m/N = 2s²/(1+s)`,
`t = 1 − s²`, `R_{N,m} = P_{N,m}/(2N Q_{N,m})` is the connected ratio
(`0 ≤ R ≤ 1`), and `q = N − m` is the deficit.

- **Part I** (Report 141): the Riccati identity
  `F − 1 = kxF + xF² + 2x²F_x` for `F = Σ p_N x^N` and its Stieltjes continued
  fraction — **Peter Bala's conjecture on A258219** (Jul 28 2022) — via an exact
  identity for all weighted prefixes; `F = 1 + 2xZ'/Z` with
  `Z = ₂F₀((k+1)/2, 1/2;; 2x)`; and
  `a_n ~ C dⁿ n!/√n`, `d = (51√17 − 107)/4`, `C = √(2 + 2/√17)/π^{3/2}`,
  proving **Václav Kotěšovec's asymptotic form on A292692** (stated numerically,
  Dec 01 2017) **and his rate conjecture** (Mar 17 2024), with the amplitude in
  closed form; the first relative correction `b₁ = −989/2176 − 907√17/36992`;
  Lambert-W threshold brackets inside integer ceilings.
- **Part II** (Report 142, the base): every fixed order
  `R_{N,m} = Σ_{j<K} R_j(s) N^{−j} + O(N^{−K})` uniformly on every compact
  subset of `0 < m/N < 1`, with `R_j = √(1−s²) r_j`, `r_j ∈ ℚ(s)` given by a
  finite algorithm; every diagonal coefficient `b_j ∈ ℚ(√17)`, explicitly
  `b₂ = −(30800095 + 3912441√17)/80494592`; the Lambert-W inverse at every
  fixed order.
- **Part III** (Report 143): the upper edge `m = N − q`. Bounds
  `L_a(n−2a)₊^{2a} ≤ [k^{n−a}]p_n ≤ L_a(n+a)^{2a}` for all `a, n`; exact
  sandwiches for `P_{N,N−q}` and `Q_{N,N−q}` for every `q ≤ N/2`; the profile
  `√N R_{N,N−q} = F_q {1 + O((q+1)²/N)}` uniformly for `q = o(√N)`, `F_q` a
  binomial smoothing of the four-regular-map sequence
  [A292186](https://oeis.org/A292186);
  `F_q = 2√(q/3){1 − 7/(16q) − 455/(512q²) − …}` to every fixed order; strict
  monotonicity of `F_q`; a ceiling-safe inverse by polynomial reversion (no
  Lambert W).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *A weighted Dyck path Newton diagonal* (author line "Report 141", October 2, 2026) | 141 | `A292692_Weighted_Dyck_Diagonal_Asymptotics_and_Inversion_Source.zip` (718,278 bytes, 10 files; `Report141.tex`, 1,314 lines, 21 pp.) | none | `e85586b7c` | Part I, Sections 1–12 |
| *All orders for the weighted Dyck Newton diagonal* (author line "Report 142", October 2, 2026); the base | 142 | `A292692_All_Orders_Interior_Asymptotics_and_Inversion_Source.zip` (1,022,218 bytes, 11 files, 2 of them Report 141's source and PDF under `foundation141/`; `Report142.tex`, 1,041 lines, 16 pp.) | none | `e85586b7c` | Part II, Sections 13–22, plus the write's Subsection 22.1 |
| *Quantified upper edge transition of a weighted Dyck Newton triangle* (author line "Report 143", October 3, 2026) | 143 | `Weighted_Dyck_Upper_Edge_Transition_All_Orders_and_Inverse_Source.zip` (1,493,566 bytes, 15 files, 4 of them Reports 141 and 142 under `foundation141/` and `comparison142/`; `Report143.tex`, 1,092 lines, 17 pp.) | none | `e85586b7c` | Part III, Sections 23–34, plus the write's Section 35 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `e85586b7c` (batch 105, cluster 105-DYCK) removed them from
`docs/incoming/`. The write is "Write batch 105
(a292692-weighted-dyck-newton-diagonal): new report, the weighted Dyck Newton
diagonal of A292692 and A258219".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author, a tool or an
addressee, says it is AI-assisted, or carries "prepared for private review"
wording; each sets an empty PDF author field. Every result, proof, remark,
question and limitation of the three manuscripts is printed.

## Why the Parts are in this order

The base is Report 142: it proves every analytic statement of Report 141 under
weaker hypotheses (the whole interior instead of Report 141's contraction range
`α < 6 − 3√3`, every fixed order instead of the first correction), and its
`Report142.tex` was staged as `article.tex`. It is printed **second**, as
Part II, because it is not self-contained: it takes the weighted-path bridge
and the convolution `2N z_N = Σ_{j≥1} p_j z_{N−j}` from Report 141. Report 141
is printed in full as Part I: it alone proves Bala's conjecture and the
continued fraction, and its positive-contraction proof of the leading and
first-corrected ratio is an independent route. Report 143 treats a different
regime, starts from the recurrence Part I proves and compares with Part II's
coefficients, so it is Part III. Dependency order, which is also the order of
writing.

**Embedded copies.** Report 142's `foundation141/` and Report 143's
`foundation141/` and `comparison142/` hold the sources and PDFs of Reports 141
and 142; all six files are byte-identical to the standalone deliveries (SHA-256
at placement, `cmp` again at the write). They are printed once, as Parts I and
II, and not shipped. Part II's Section 14 and Part III's Subsection 24.1
restate Part I's convolution, Newton transform and logarithmic derivative in
their own words (no verbatim overlap); they are printed in full with notes
pointing to Part I.

## Files

The directory holds 21 files: 6 at the root, 12 in `code/`, 3 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 141, prefix `141-diagonal-`** (6 files): the public-provenance
note; `code/`: the verifier (`check`, `replay`, `selftest`, `build`, `pack`,
`reproduce`, `seal`), the exact rational-function and `ℚ(√17)` algebra, the
independent path-state and Newton computations, the decimal replay; `data/`:
the typed exact fixtures.

```
141-diagonal-SOURCES.md
code/141-diagonal-code-algebra.py
code/141-diagonal-code-exact.py
code/141-diagonal-code-replay.py
code/141-diagonal-verify.py
data/141-diagonal-checks-fixtures.json
```

**Report 142, prefix `142-interior-`** (5 files): the provenance note; the
verifier; the standard-library finite checks (top coefficients, frozen inverse,
saddle coefficients); the SymPy regeneration of `r₂`, `D₂`, `B₂`, `b₂`, `λ₂`;
the fixtures.

```
142-interior-SOURCES.md
code/142-interior-code-finite.py
code/142-interior-code-second.py
code/142-interior-verify.py
data/142-interior-checks-fixtures.json
```

**Report 143, prefix `143-edge-`** (7 files): the provenance note; the bundle
verifier; the exact checker, the edge polynomial and sandwich computations,
the fixed-order profile and inverse coefficients (`f₀…f₈`, `ξ₀…ξ₇`), the
self-test; the fixtures.

```
143-edge-SOURCES.md
code/143-edge-bundle.py
code/143-edge-code-check.py
code/143-edge-code-edge.py
code/143-edge-code-profile.py
code/143-edge-code-selftest.py
data/143-edge-checks-fixtures.json
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs;
`Report141.tex` and `Report143.tex` (printed as Parts I and III) and the
delivery READMEs of Reports 141 and 143 (Report 142's was staged and is
replaced by this guide); the three `manifest.json` files (pure SHA-256 and size
ledgers of each package, verified at placement, 9/9, 10/10 and 14/14; repository
policy drops checksum manifests); the embedded copies `foundation141/` (in
Reports 142 and 143) and `comparison142/` (in Report 143), byte copies of
Parts I and II.

## Labels and numbering

Label prefix **`wdn:`** (none at HEAD before this report): Part I uses
`wdn:dia:` (Report 141's 112 labels), Part II `wdn:int:` (Report 142's 102),
Part III `wdn:edge:` (Report 143's 98). The manuscripts share many bare names
(11 between Reports 141 and 142, 3 between 141 and 143, 7 between 142 and 143;
for example `eq:fh`, `eq:Q`, `eq:middle`, `eq:cumulants`, and `thm:allorders`
in both 142 and 143); under the Part prefixes they are distinct. The write
added the three Part labels; `wdn:dia:rem:inverse` (the unlabelled Remark
10.2), `wdn:int:thm:inverse` (the unlabelled Theorem 21.1),
`wdn:edge:sub:connected` (Subsection 24.1); `wdn:int:sub:further`
(Subsection 22.1); the front matter's `wdn:sec:guide`, `wdn:sec:status`,
`wdn:sec:oeis`, `wdn:sec:notation`, `wdn:sec:provenance`, `wdn:sec:trust`,
`wdn:sec:neighbours`; and Section 35's `wdn:sec:further`,
`wdn:rem:sqrtscale` and the seven items `wdn:q:gap`, `wdn:q:lower`,
`wdn:q:bridge`, `wdn:q:effective`, `wdn:q:convergence`, `wdn:q:comb`,
`wdn:q:sharper`. 335 labels in all, all distinct.

| Part | Manuscript | Section here | Statement `k.j` | Equation `(k)` |
|---|---|---|---|---|
| I | Report 141 | `k` (1–12, unchanged) | `k.j` | `(k)` |
| II | Report 142 | `k + 12` (13–22); 22.1 added | `(k+12).j` | `(II.k)` |
| III | Report 143 | `k + 22` (23–34); 35 added | `(k+22).j` | `(III.k)` |

For example Report 142's Theorem 1.1 is Theorem 13.1 and its Corollary 1.2 is
13.2; Report 143's Theorems 2.1, 2.2, 2.4, 8.1, 9.1 are 24.1, 24.2, 24.4, 30.1,
31.1 and its Corollary 2.3 is 24.3. A comparison of the build's `.aux` with
separate builds of the three delivered `.tex` files confirmed all 312
delivered labels under these offsets and prefixes. The delivered READMEs,
`SOURCES.md` files, code and data use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`C`** (the amplitude; `C_{N,m}`; Part II's polynomial
`C_a(n) = c_a(n)/(n falling a)`; Part III's number `C_q = (3/2)^q/q!`),
**`B`** (the saddle variance; Part I's opposite endpoint `𝓑_{N,m}`, which Part
II writes `B_{N,m}`; Part II's operator `𝓑_s`; Part III's Bernoulli variable),
**`h`** (`h(t) = f(t) − 1`; Part III's `h_n = n! L_n` and `h = 1/n`), **`λ`**
(Part II's inverse coefficients, `λ₁ = b₁ + 1/12`, which Part I calls `β₁`;
Part III's Stirling coefficients, `λ₁ = −1/16`), **`W`** (Lambert in Parts I,
II; a hypergeometric series in Part III), **`K`**, **`L`**, **`q`** (Part I's
kernel mass `q₀`; Part III's deficit), **`μ`** (`1/α`; Part III's binomial
mean `2q/3`), **`D`**, **`E`**, **`M`**, **`r`**. Part I's kernel
`b_{N,m,ℓ,r}` is Part II's `a_{N,m,ℓ,r}`; Part I's `F(x,k)` is Part III's
`G(x,k)`. `c_a(n) = [k^{n−a}] p_n` means the same in Parts II and III.

## What the report claims

**Part I (Report 141).**
- Theorem 1.1: Riccati identity, recurrence
  `p_N = (2N−2+k)p_{N−1} + Σ p_j p_{N−1−j}`, S-fraction numerators
  `(k+1)x, 3x, (k+3)x, 5x, …` (Bala's conjecture, for indeterminate `k`);
  Proposition 2.2, the stronger prefix identity `H_{2n+y}(y) = [xⁿ]G^{y+1}`;
  Proposition 3.2, the continued fraction by Gauss-type ratios.
- Lemma 3.1: `F = 1 + 2xZ_x/Z`, `2N z_N = Σ_{j≥1} p_j z_{N−j}`; Lemma 4.1:
  `Q_{N,m} = (2N−1)!!/m! · [t^N] f h^m`.
- Theorem 1.2: `a_n ~ C dⁿ n!/√n` with the closed forms above.
- Theorem 7.1: `R_{N,m} → √(1−s²)` on compact subsets of `(9/20, 49/85)`, by a
  positive contraction; Theorem 9.1: the first correction `r₁(s)` for
  `α < 6 − 3√3`, and `b₁`.
- Theorem 10.1, Corollary 10.3: threshold brackets inside ceilings around
  `x₀ = T/W(dT/e)`, half-widths `o(1/log log X)` and `O(x₀^{−2}/log x₀)`.

**Part II (Report 142).**
- Theorem 13.1: every fixed order on every compact `J ⊂ (0,1)`; Lemma 15.1
  (shifted saddle to every order), Lemma 16.1 (middle bound), Lemma 17.1
  (top coefficients `c_a(n)` polynomial with boundary zeros), the opposite and
  principal endpoints to every order, the algorithm and rationality
  (Section 18), the frozen inverse `(I − 𝓑_s)(I + 𝒜_s) = I` with
  `‖𝓑_s‖₁ = 1 − √t < 1`, the one-power improvement Lemma 19.1 and the
  nested-compact bootstrap.
- Corollary 13.2: `b_j ∈ ℚ(√17)`, `b₂` explicit; `r₂`, `D₂`, `B₂` explicit
  (Section 20).
- Theorem 21.1: the inverse at every fixed order, `λ₁`, `λ₂` explicit,
  finitely many Newton steps.

**Part III (Report 143).**
- Theorem 24.1 (all `a ≥ 1`, `n ≥ 0`), Theorem 24.2 (exact `P` and `Q`
  sandwiches), Corollary 24.3 (`e^{−8q²/N} ≤ √N R/F_q ≤ e^{(10q²+1/8)/N}` for
  `q ≤ N/4`; uniform profile for `q = o(√N)`), Lemmas 26.1–26.2 (Stirling and
  elementary-symmetric bounds; the leading `Q` estimate is classical,
  Hsu–Shiue).
- Theorem 24.4: `F_q = 2√(q/3){1 − 7/(16q) + O(q^{−2})}`, resolved as a
  genuine correction of `R` for `q = o(N^{1/3})`; Theorem 30.1: every fixed
  order (`f₂…f₅` printed; the companion carries `f₀…f₈` exactly).
- Section 28: A292186's Riccati equation, logarithmic derivative and factorial
  asymptotic — **prior art** (Martin–Kearney; Ciobanu–Kolpakov; Bala on the
  OEIS, Aug 22 2023), re-derived with the correction `1 − 3/(16n)` and
  remainders, which the manuscript states as its own.
- Theorem 31.1: strict monotonicity of `F_q` and the ceiling-safe inverse
  `J_M(x) = x + 7/8 + 203/(128x) + 3231/(512x²) + …`, `x = 3Y²/4`.
- Section 32: `r₁(s)/N → −7/(16q)` at `s → 1` — algebraic consistency only.

**Added by the write** (all marked `[write]`, dated 5 October 2026): the front
matter (including the OEIS entries as read on 5 October 2026 and the
inverses as instances of the transseries volume); dated notes marking what
later Parts supersede or answer; Subsection 22.1 and Section 35 (further
questions); and **Remark 35.1** with its proof: `R_{N,N−q} ≍ √((q+1)/N)`
uniformly for `q ≤ min(c√N, N/4)`, a direct consequence of Corollary 24.3 and
Theorems 24.4 and 31.1.

**The inverses.** Parts I and II solve `x(log x + log d − 1) = T`: the factorial
core `p0:prop:factorial-core` (`κ = 1`) of the transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
a form of its Lambert core `p0:thm:lambert-core`, with the two-ceiling
separation pattern of `p0:thm:staircase`. Part III's inverse has **no Lambert
W**: a linear core after squaring, inverted by reversion, with the same
ceiling pattern. No manuscript claims novelty for the inversion.

## What the report does not claim

Every limitation is printed in place. In short: no asymptotics for
`√N ≲ q = o(N)` (only Part III's exact bounds, exponentially loose there) or
at the lower edge `m = o(N)`; no uniformity across all
ratios (Part III's Section 32 is consistency evidence, not a bridge); no
effective remainder constants or onsets, so no certified threshold at a given
`X` or `Y`; no convergence or resummation, and no uniformity for a growing
order; Part I asserts nothing beyond the first correction and nothing outside
its contraction range; Part II asserts nothing at `α = 0` or `1`; Part III's
`(III.53)` is not an all-orders finite-`N` expansion, and its inverse is for
the one-variable `F_q` only, not for freely varying `(N, q)`. No manuscript
identifies `a_n` with a class of QED diagrams. The leading `Q` estimate,
A292186's Riccati equation and leading asymptotic, and the continued-fraction
theory (Stokes) are credited as prior art; no worldwide priority or
exhaustive novelty claim is made. **All three companions**: finite exact
checks prove no asymptotic remainder; integrity seals are records relative to
the supplied verifiers, not signatures.

## Further questions, and the standing rule

Part I's Section 12 and Part III's Section 33 are the manuscripts' own;
Subsection 22.1 records Part II's non-claims as questions; Section 35 collects
all of them (Vladimir's standing rule of 4 October 2026), with sources,
sketches and what is missing:

1. **the range `√N ≲ q = o(N)`** between Parts II and III, and a limit at
   `q ≍ √N` (Part I "Other moving regimes"; Part III items 1, 4) — natural
   conjecture `R_{N,N−q} ~ 2√(q/(3N))`, unproved;
2. **the lower edge `m = o(N)`** (Part I) — uncertified observation:
   `N(1 − R_{N,0}) = 0.3226, 0.2599, 0.2548, 0.2524, 0.2512` at
   `N = 10, 50, 100, 200, 400`, suggesting `R_{N,0} = 1 − 1/(4N) + o(1/N)`;
3. a uniform bridge across all ratios (Part III item 4);
4. effective constants, onsets, certified thresholds (all three);
5. convergence, resummation, growing order (Parts II, III) — hints: intake
   residuals suggest `b₃ ≈ −2.6`; the companion's exact
   `f₆ = −1103681053651/268435456 ≈ −4111.6`, `f₇`, `f₈` grow roughly
   factorially;
6. combinatorial meanings of `T(N,m)`, `√t₀`, `K_q` and the probability 2/3
   (Parts I, III);
7. a sharper nonlinear comparison (Part III item 2).

**Answered inside the merge**, with dated notes at the questions: Part I's
"Higher relative orders" and "Beyond the contraction interval" (by Theorem
13.1); Part I's "Other moving regimes" for the upper edge with `q = o(√N)`
(by Corollary 24.3); Part I's "no coefficients beyond `b₁`" (by Corollary
13.2). **Nothing in the three manuscripts was found to be wrong**, and no
claim was refuted.

## Relation to neighbouring reports

- No other report of the collection treats A258219, A258220, A292692,
  A292186 or the weighted Dyck polynomials (searched 5 October 2026); the
  Dyck- and Catalan-path reports of `oeis-sequence-asymptotics/` share no
  statement with this one.
- **Same mechanism, other recurrences** (method parallel, no shared
  statement, no cross-citation), both under
  `Analysis/Transseries/docs/series-and-transseries/`:
  `Factorial_Transseries_OEIS_A006014` (a `₂F₀` logarithmic-derivative
  linearization of the A006014 recurrence, a positive normalized ratio, an
  all-orders factorial expansion) and
  `Late_Coefficients_Factorially_Forced_Catalan_Recurrence` (A229741/A260879,
  positive Stirling transforms, safe integer threshold enclosures).
- The transseries volume `Transseries_And_Inversion` supplies the inversion
  apparatus of which the inverses here are instances (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository treats these
sequences (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 20 staged files were checked
  against a fresh extraction from `60f54ea06` at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files).
  Only names changed (tables at the end). The delivered code and markdown use
  delivery paths (`verify.py`, `bundle.py`, `code/…`, `checks/fixtures.json`,
  `manifest.json`, `README.md`, `Report14N.tex`, `Report14N.pdf`,
  `foundation141/`, `comparison142/`), which are shipped under other names or
  not at all.
- **Closed inventories: none of the verifiers runs in this directory.** Each
  hard-codes its file inventory and reads `manifest.json` and the delivery
  layout. Rerun from the archive (below).
- Report 142's delivered README (replaced by this guide) and the code's
  messages use `/home/alice/…` example paths; use a scratch directory
  outside the repository.
- **Dating slip in two `SOURCES.md`.** `141-diagonal-SOURCES.md` and
  `142-interior-SOURCES.md` (item 3) attribute "the numerical asymptotic form
  and conjectural algebraic rate" of A292692 both to Kotěšovec, 2024-03-17. On
  the OEIS entry the numerical form is dated **Dec 01 2017** and only the
  conjecture `d = (51√17 − 107)/4` is dated Mar 17 2024. Part I's article text
  dates only the rate to 2024, correctly. Not edited (delivered bytes).
- `143-edge-SOURCES.md` and Part III call A292186 "the classical rooted
  connected four-regular-map sequence"; the OEIS name is "rooted unlabeled
  connected four-regular maps on a compact closed oriented surface" (any
  genus). Wording only.
- Part II's bibliography cites only Report 141; its OEIS and literature
  references are in `142-interior-SOURCES.md`, and in the merged
  bibliography through Parts I and III.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/A292692_Weighted_Dyck_Diagonal_Asymptotics_and_Inversion_Source.zip > r141.zip
git show 60f54ea06:docs/incoming/A292692_All_Orders_Interior_Asymptotics_and_Inversion_Source.zip > r142.zip
git show 60f54ea06:docs/incoming/Weighted_Dyck_Upper_Edge_Transition_All_Orders_and_Inverse_Source.zip > r143.zip
mkdir x141 x142 x143 && unzip -q r141.zip -d x141 && unzip -q r142.zip -d x142 && unzip -q r143.zip -d x143
python -I -B <abs>/x141/Report141/verify.py check
python -I -B <abs>/x141/Report141/verify.py replay --output <abs>/out141
python -I -B <abs>/x141/Report141/verify.py selftest --output <abs>/self141
uv run --no-project --with sympy==1.14.0 python -I -B <abs>/x142/report142/verify.py check
uv run --no-project --with sympy==1.14.0 python -I -B <abs>/x142/report142/verify.py replay --output <abs>/out142
python -I -B <abs>/x143/report143/bundle.py check
python -I -B <abs>/x143/report143/code/check.py replay
python -I -B <abs>/x143/report143/bundle.py replay --output <abs>/out143
```

`<abs>` must be an absolute directory outside the bundles; every output must
not exist beforehand. Report 141's and 143's companions need only the Python
standard library (3.11 or later); Report 142's `replay` and `selftest` need
SymPy 1.14.0. `build`, `pack` and `reproduce` need the recorded TeX Live
pdfTeX 1.40.26 for byte-identical PDFs and were not run.

**Windows.** Report 143's `bundle.py` accepts only an output path with one
leading slash (`lexical_absolute`), so on Windows give a drive-relative path
such as `/Users/<you>/out143`. Its `selftest` fails on Windows with
"normal: disposable inputs not restored": `code/selftest.py` restores mutated
sources with `Path.read_text`/`write_text`, which on Windows rewrites LF as
CRLF, so the fingerprint check fails — a platform artifact, not a
mathematical failure; run it on Linux or macOS. Reports 141's and 142's suites
run on Windows as given.

Results: at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-105 dossier) Report 141 `check`, `replay` and `-O replay`
(7 s each, byte-identical outputs) and `selftest` (68 tests, 2 min 35 s)
passed; Report 142 `check`, `replay` (5 min 12 s) and `selftest` (62 tests,
11 min 37 s) passed under SymPy 1.14.0; Report 143 `bundle.py check`,
`code/check.py check`, `replay`, `-O replay` (byte-identical) and `bundle.py
replay` passed; its `selftest` failed only as described above. At the write
(5 October 2026, fresh extractions, Windows) Report 141 `check` and `replay`,
Report 142 `check`, and Report 143 `bundle.py check` and `code/check.py check`
passed, each in about 2 s. The three delivered `.tex` files compile with
MiKTeX pdfLaTeX to 21, 16 and 17 pages with no warnings (one underfull box in
Report 141, at the display reprinted in Section 2.1).

## Rights

Repository contents are MIT-0. `code/141-diagonal-code-replay.py` embeds four
A292692 b-file terms (`n = 40, 80, 160, 290`) from the OEIS, used only for
normalization diagnostics and not enumerated by the package; OEIS data are
available under CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). All
other counts in the companions are recomputed from the recurrence. The OEIS
entries are credited for the sequences, Peter Bala for the A258219 and A292186
Riccati and continued-fraction statements, Václav Kotěšovec for the A292692
form and rate, Martin–Kearney, Ciobanu–Kolpakov, Hsu–Shiue, Borinsky,
Stokes, Arratia–DeSalvo and the DLMF as the manuscripts cite them. Nothing
was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 71 pages, no errors, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull boxes. The log carries one
underfull-box message, at the `multline*` display of Section 2.1 (a build of
the delivered `Report141.tex` has the same one), and one "Infinite glue
shrinkage found in box being split" message from the notation longtable
breaking across a page.

## Delivered path → shipped path

Report 141 (`141-diagonal-`; delivered under `Report141/`):

| Delivered | Shipped |
|---|---|
| `Report141.tex` | not shipped; printed as Part I of `article.tex` |
| `SOURCES.md` | `141-diagonal-SOURCES.md` |
| `verify.py` | `code/141-diagonal-verify.py` |
| `code/algebra.py`, `code/exact.py`, `code/replay.py` | `code/141-diagonal-code-<name>` |
| `checks/fixtures.json` | `data/141-diagonal-checks-fixtures.json` |
| `README.md`, `Report141.pdf`, `manifest.json` | not shipped |

Report 142 (`142-interior-`; delivered under `report142/`):

| Delivered | Shipped |
|---|---|
| `Report142.tex` | `article.tex` (Part II) |
| `README.md` | replaced by this guide |
| `SOURCES.md` | `142-interior-SOURCES.md` |
| `verify.py` | `code/142-interior-verify.py` |
| `code/finite.py`, `code/second.py` | `code/142-interior-code-<name>` |
| `checks/fixtures.json` | `data/142-interior-checks-fixtures.json` |
| `foundation141/Report141.tex`, `.pdf` | byte copies of Report 141; not shipped |
| `Report142.pdf`, `manifest.json` | not shipped |

Report 143 (`143-edge-`; delivered under `report143/`):

| Delivered | Shipped |
|---|---|
| `Report143.tex` | not shipped; printed as Part III of `article.tex` |
| `SOURCES.md` | `143-edge-SOURCES.md` |
| `bundle.py` | `code/143-edge-bundle.py` |
| `code/check.py`, `code/edge.py`, `code/profile.py`, `code/selftest.py` | `code/143-edge-code-<name>` |
| `checks/fixtures.json` | `data/143-edge-checks-fixtures.json` |
| `foundation141/`, `comparison142/` (4 files) | byte copies of Reports 141 and 142; not shipped |
| `README.md`, `Report143.pdf`, `manifest.json` | not shipped |

## Provenance

Three manuscripts (bundle Reports 141, 142, 143) → one report; base 142,
printed as Part II. Arrival `60f54ea06`, placement `e85586b7c`, write batch
105 (5 October 2026). No manuscript pins a ProveIt commit. Merge choices
(dependency order with the base in the middle, Report 141 printed in full,
restatements printed with pointers, embedded copies printed once, the merged
bibliography with Reports 141 and 142 pointing to Parts I and II) are listed
in the article's front matter, "Provenance and merge decisions".
