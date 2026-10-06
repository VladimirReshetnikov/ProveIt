# Subdiagonal and Superdiagonal Partitions

**OEIS A238875 and A238873: the two conjectures of Archibald, Blecher, Elizalde and Knopfmacher proved; the subdiagonal ratio to all orders; the superdiagonal rate, Airy term and limit shape; the full superdiagonal equivalent, conditional on a preprint**

This is a research report built on 6 October 2026 (write batch 107) from five
manuscripts of one external research session, Reports 156, 159, 158, 160 and
162 of the session bundle of Reports 1–243, all dated 3 October 2026. All five
write partitions in weakly increasing order `λ_1 ≤ ⋯ ≤ λ_k` and study the classes
of M. Archibald, A. Blecher, S. Elizalde and A. Knopfmacher, *Subdiagonal and
superdiagonal partitions*, Afrika Matematika 36, article 77 (2025)
([doi:10.1007/s13370-025-01282-0](https://doi.org/10.1007/s13370-025-01282-0),
open access, CC BY 4.0), called ABEK below:

- `s_r(n)` = number of partitions of `n` with `λ_i ≤ i + r` for all `i`;
  `s(n) = s_0(n)` is [A238875](https://oeis.org/A238875) (subdiagonal partitions);
- `A(n)` = number with `λ_i ≥ i` for all `i`, [A238873](https://oeis.org/A238873)
  (superdiagonal partitions).

Throughout, `p(n)` and `q(n)` count all partitions and partitions into distinct
parts, `R` is Dyson's rank, `β = π/√(6n)`, `b = log 2`, `C = π²/12 + log²2`,
`B = 2√C = √(π²/3 + 4 log²2) = 2.2829…`, `a_1 = −ζ = −2.3381…` is the largest zero
of Ai, and `D = ζ b C^(−1/6) = 1.5507…`.

- **Part I** (Report 156, the base) proves **both conjectures of ABEK's
  Section 5**, which are journal conjectures, not OEIS ones. Conjecture 5.3
  (`|S_n|/|P_n| → 1/2`): `0 ≤ P(R ≤ r) − s_r(n)/p(n) = O(1/log n)` uniformly in
  `r ≥ 0` (Theorem 1.1). Conjecture 5.2 (`|Q_n|/|A_n| → 0`):
  `liminf log A(n)/√n ≥ B_* = √(π²/3 + 2 log²2) = 2.0617… > π/√3` (Theorem 1.2). Also
  a uniform logistic crossover in `r/√n` (Corollary 4.1, using Dousse–Mertens)
  and a Lambert-W inverse (Theorem 5.1).
- **Part II** (Report 159): `s(n)/p(n) = Σ_{j≤R} c_j β^j + O(β^(R+1))` for every `R`,
  `c_j ∈ ℚ[π^(−2)]`, `c_0 = 1/2`, `c_1 = −1/8`, `c_2`, `c_3` explicit (Theorem 10.1,
  using Liu–Zhou and Zhou), and integer inverse windows (Theorem 10.2). A
  second, sharper proof of Conjecture 5.3, **at `r = 0` only**.
- **Part III** (Report 158): `B√n − O(n^(1/3)) ≤ log A(n) ≤ B√n + O(1)` (Theorem 20.1),
  elementary; it **replaces Part I's lower rate `B_*`** by the exact rate `B`.
  Inverse to `O((log y)^(5/3))`.
- **Part IV** (Report 160): `log A(n) = B√n − D n^(1/6) + o(n^(1/6))` and its radial
  analogue (Theorem 30.1), using Mallein's published killed-walk estimates;
  the inverse `T(y) = x + ζbC^(−2/3) x^(2/3) + o(x^(2/3))`, `x = (log y/B)²`; and the
  limit shape of a uniform superdiagonal partition (Theorem 30.3).
- **Part V** (Report 162), **conditional on the unrefereed preprint
  [arXiv:2607.27504v1](https://arxiv.org/abs/2607.27504v1)** (Yu-Tian Li, 29 July
  2026; its Theorem 1 and Corollary 2):
  `A(n) ~ K n^(−11/12) exp(B√n − D n^(1/6))`, `K = √2 C^(5/12)/(√π Ai'(a_1)) = 1.2705…`
  (Theorem 39.1), and the inverse to the `√x` term (Corollary 39.2). The
  **unconditional** superdiagonal statements are those of Parts III and IV.
- **Added by the write**: Proposition 1.3, with a complete proof, that a
  partition has *choosable initial intervals* iff it is superdiagonal; this
  settles Gus Wiseman's conjecture in A238873 (the same argument was posted in
  [A387112](https://oeis.org/A387112) by Clément Garrot on 31 August 2026); and the
  defect `P(R ≤ 0) − s(n)/p(n) = β/4 + (7/16 − 3/(2π²))β² + O(β³)` (9.1), from Part II.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Proofs of two conjectures on subdiagonal and superdiagonal partitions: Quantitative rank coupling and exponential separation* (author line "Report 156"); the base | 156 | `Two_Partition_Conjectures_Proofs_and_Quantitative_Extensions_Source.zip` (507,686 bytes, 14 files; `Report156.tex`, 861 lines, 14 pp.) | none | `3988bf5c4` | Part I, Sections 1–9, plus the write's Subsection 1.1 |
| *All orders asymptotics for subdiagonal partitions: Endpoint reductions and integer inverse localization* ("Report 159") | 159 | `Subdiagonal_Partitions_All_Orders_Expansion_and_Integer_Inverses_Source.zip` (568,687 bytes, 15 files; `Report159.tex`, 1,019 lines, 17 pp.) | none | `3988bf5c4` | Part II, Sections 10–19 |
| *Exact exponential growth of increasing superdiagonal partitions: An elementary proof and quantitative threshold inversion* ("Report 158") | 158 | `Superdiagonal_Partitions_Exact_Exponential_Growth_and_Inverse_Source.zip` (513,632 bytes, 14 files; `Report158.tex`, 749 lines, 13 pp.) | none | `3988bf5c4` | Part III, Sections 20–29 |
| *Airy correction and limit shape for superdiagonal partitions: Pointwise enumeration and macroscopic structure* ("Report 160") | 160 | `Superdiagonal_Partitions_Airy_Correction_and_Limit_Shape_Source.zip` (579,886 bytes, 17 files; `Report160.tex`, 1,308 lines, 17 pp.) | none | `3988bf5c4` | Part IV, Sections 30–38 |
| *Full prefactor and refined inverse for superdiagonal partitions: Exact coefficient asymptotics for A238873* ("Report 162") | 162 | `Superdiagonal_Partitions_Full_Prefactor_and_Refined_Inverse_Source.zip` (514,510 bytes, 16 files; `Report162.tex`, 933 lines, 15 pp.) | none | `3988bf5c4` | Part V, Sections 39–46, plus the write's Section 47 |

All five archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `3988bf5c4` (batch 107, cluster 107-DIAGP) removed them from
`docs/incoming/`. The write is "Write batch 107 (a238873-diagonal-partitions):
new report, superdiagonal and subdiagonal partitions, two conjectures proved".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. **Part V's main theorem and corollary are conditional** on an
unrefereed arXiv preprint whose proof nobody verified. None of the manuscripts
names an author, a tool or an addressee, says it is AI-assisted, or carries
"prepared for private review" wording; each sets an empty PDF author field and
pins no repository commit. Every result, proof, remark, question and
limitation of the five manuscripts is printed; six restated proofs are printed
once, with pointers (below).

## Why the Parts are in this order

Report 156 is the base: it is the only manuscript that treats both classes,
every shift `r ≥ 0` and both conjectures. Its `Report156.tex` was staged as
`article.tex` and is printed first. The others follow in dependency order,
grouped by class: Part II (subdiagonal, `r = 0`) cites Part I; Part III
(superdiagonal rate) credits Part I's prefix bound; Part IV uses Part III's
coarse lower bound for its shape theorem; Part V is independent of Parts I–IV
in its proofs but refines their statements under an extra, unrefereed input,
so it comes last. The bundle numbers do not follow this order (159 is Part
II). No archive embeds another (no byte-identical file across the five).

**Printed once, with pointers.** The barrier lemma, the survival lemma, the
monotonicity injection and the dilogarithm evaluation `L(b) = C` are first
printed in Part III, the Dyck representation in Part I. Six later proofs of
them are replaced by pointers, each with a dated note: Part III's proof of
Lemma 23.1 (Dyck); Part IV's proofs of the barrier equivalence (Section 30),
of the dilogarithm evaluation (Section 31.1), of the survival bound (Section
33.1) and of monotonicity (Section 35.1); Part V's proof of monotonicity
(Section 44). Every statement and every labelled display stays. Restatements
woven into longer proofs stay, with notes: Part II's interior step (Section
12.2), Part V's barrier sentence, summation by parts (43.6) and ruin bound. The
local-limit arguments of Part IV (Section 34) and Part V (Section 43) share the
buffer, ruin bound and three-arc Fourier cover but are assembled differently;
both are printed, as two routes.

## Files

The directory holds 59 files: 5 at the root, 30 in `code/`, 24 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 156, prefix `156-conjectures-`** (10 files): `code/`: the companion
(exact counts, finite mechanism checks, threshold search, noncertifying
inverse illustration) and its 37 tests, the PDF builder, archive packer,
release helpers and their 11 tests; `data/`: exact counts `p, q, s_0, A` for
`n ≤ 200`, the finite-check record, the attributed OEIS prefixes, the source
provenance record.

```
code/156-conjectures-build_pdf.py
code/156-conjectures-companion.py
code/156-conjectures-make_zip.py
code/156-conjectures-release_tools.py
code/156-conjectures-test_companion.py
code/156-conjectures-test_release.py
data/156-conjectures-SOURCE_PROVENANCE.json
data/156-conjectures-counts.json
data/156-conjectures-data-oeis_prefixes.json
data/156-conjectures-finite_checks.json
```

**Report 159, prefix `159-subdiag-`** (11 files): `code/`: the companion
(counts, endpoint reduction and coefficient extraction to order 3, threshold
search) and its 31 tests, PDF builder, packer, release helpers and tests;
`data/`: counts for `n ≤ 300`, the finite checks, the order-3 endpoint
expansion, the OEIS prefix, the provenance record.

```
code/159-subdiag-build_pdf.py
code/159-subdiag-companion.py
code/159-subdiag-make_zip.py
code/159-subdiag-release_tools.py
code/159-subdiag-test_companion.py
code/159-subdiag-test_release.py
data/159-subdiag-SOURCE_PROVENANCE.json
data/159-subdiag-counts.json
data/159-subdiag-data-oeis_prefix.json
data/159-subdiag-endpoint_expansion.json
data/159-subdiag-finite_checks.json
```

**Report 158, prefix `158-growth-`** (10 files): `code/`: the companion (counts,
cumulative-barrier and survival checks, rational product bounds, threshold
search) and its 40 tests, PDF builder, packer, release helpers and tests;
`data/`: counts for `n ≤ 200`, the finite checks, the OEIS prefix, the
provenance record.

```
code/158-growth-build_pdf.py
code/158-growth-companion.py
code/158-growth-make_zip.py
code/158-growth-release_tools.py
code/158-growth-test_companion.py
code/158-growth-test_release.py
data/158-growth-SOURCE_PROVENANCE.json
data/158-growth-counts.json
data/158-growth-data-oeis_prefixes.json
data/158-growth-finite_checks.json
```

**Report 160, prefix `160-airy-`** (13 files): the companion README; `code/`:
the companion (counts, finite checks, numerical illustrations, shape
coordinates, threshold search) and its 23 tests, PDF builder, packer, release
helpers and tests; `data/`: the four outputs, the OEIS prefix, the provenance
record.

```
160-airy-companion-README.md
code/160-airy-build_pdf.py
code/160-airy-companion-airy_shape.py
code/160-airy-companion-test_airy_shape.py
code/160-airy-make_zip.py
code/160-airy-release_tools.py
code/160-airy-test_release.py
data/160-airy-SOURCE_PROVENANCE.json
data/160-airy-data-counts.json
data/160-airy-data-finite_checks.json
data/160-airy-data-illustrations.json
data/160-airy-data-oeis_prefix.json
data/160-airy-data-shape_coordinates.json
```

**Report 162, prefix `162-prefactor-`** (12 files): the companion README;
`code/`: the companion (two exact counting routes, Airy-density algebra, tilt
checks, illustrations, threshold search) and its 14 tests, PDF builder,
packer, release helpers and tests; `data/`: counts for `n ≤ 400`, the
generating-function route to `n = 80`, the finite checks, the illustrations,
the provenance record.

```
162-prefactor-companion-README.md
code/162-prefactor-build_pdf.py
code/162-prefactor-companion-prefactor.py
code/162-prefactor-companion-test_prefactor.py
code/162-prefactor-make_zip.py
code/162-prefactor-release_tools.py
code/162-prefactor-test_release.py
data/162-prefactor-SOURCE_PROVENANCE.json
data/162-prefactor-data-counts.json
data/162-prefactor-data-finite_checks.json
data/162-prefactor-data-illustrations.json
data/162-prefactor-data-series_counts.json
```

**Not shipped** (all retrievable from `60f54ea06`): the five PDFs; the
manuscripts `Report159.tex`, `Report158.tex`, `Report160.tex`, `Report162.tex`
(printed as Parts II–V) and their delivery READMEs (Report 156's was staged and
is replaced by this guide); the five `SHA256SUMS` files (pure SHA-256 ledgers,
verified at placement; repository policy drops checksum manifests).

**Delivery names.** Each shipped file is its delivered path with `/` replaced
by `-`, after the prefix: `.py` files under `code/`, `.json` files under
`data/`, companion READMEs at the root. For example Report 160's
`companion/airy_shape.py` is `code/160-airy-companion-airy_shape.py` and its
`data/counts.json` is `data/160-airy-data-counts.json`; Report 156's
`counts.json` is `data/156-conjectures-counts.json`.

## Labels and numbering

Label prefix **`dgp:`** (none at HEAD before this report), with one sub-prefix
per Part: `dgp:conj:` (Report 156's 64 labels), `dgp:sub:` (159's 63),
`dgp:rate:` (158's 63), `dgp:airy:` (160's 66), `dgp:pre:` (162's 64). Many bare
names occur in several manuscripts (`thm:main`, `thm:inverse`, `eq:constants`,
`eq:inverse`, `eq:riemann`, `eq:survival`, `lem:mono`, `sec:main`, …); under the
Part prefixes they are distinct. The write added the five Part labels
(`dgp:conj:part` … `dgp:pre:part`); `dgp:conj:sub:choosable`,
`dgp:conj:prop:choosable`, `dgp:conj:eq:defect`; the front matter's
`dgp:sec:guide`, `…:status`, `…:conjectures`, `…:notation`, `…:provenance`,
`…:trust`, `…:neighbours`; and Section 47's `dgp:sec:further` with the ten items
`dgp:q:defect`, `…:onset`, `…:series`, `…:fluct`, `…:amplitude`, `…:relative`,
`…:allorders`, `…:inverse`, `…:complex`, `…:literature`. 346 labels in all, all
distinct.

| Part | Manuscript | Section here | Statement and equation `k.j` |
|---|---|---|---|
| I | Report 156 | `k` (1–9, unchanged); 1.1 added | `k.j` |
| II | Report 159 | `k + 9` (10–19) | `(k+9).j` |
| III | Report 158 | `k + 19` (20–29) | `(k+19).j` |
| IV | Report 160 | `k + 29` (30–38) | `(k+29).j` |
| V | Report 162 | `k + 38` (39–46); 47 added | `(k+38).j` |

A comparison of the build's `.aux` with separate builds of the five delivered
`.tex` files confirmed all 320 delivered labels under these offsets and
prefixes (Report 160's Figure 1 stays Figure 1). The write's Proposition 1.3
and equation (9.1) take numbers after every delivered one in their sections,
so no delivered number moved. The delivered READMEs, code and data use the
manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the five
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`b`** (`π/√3` in Part I; Zhou's `π/√(6(n−1/24))` in Part II; `log 2`
in Parts III–V), **`t`** (a Boltzmann variable in Parts I, III–V; the number
`6/π²` in Part II, whose variable is `β`), **`β`** (`c/√n` in Parts I–II; a buffer
constant in Parts IV–V), **`B`** (lower rates `B_*, B_0, B_h` in Part I; rank
coefficients and row counts in Part II; the rate `2√C` in Parts III, V),
**`C`**, **`ζ`/`a`** (Part IV's `ζ = −a_1 > 0`; Part V's `a = a_1 < 0`; Li's `ζ` is an
argument, Part V's `s`), **`D`** (Part IV's and Part V's `D` are the same number;
`D(n)`, `D_h(M)`, `D_M` elsewhere), **`K`** (a length in Part IV, an amplitude in
Part V), **`L`**, **`A`/`H`** (Part V renames Li's `A_q(z)` to `H_q(y)`), **`N`**, **`s`**,
**`q`**, **`R`**, **`M`/`m`**, **`f`/`g`/`h`**, **`W`/`G`/`Q`**, **`p`/`P`/`ℙ`**, **`E`**, **`α`**.
Two LaTeX macros were unified without changing the printed text (`\PP` written
as `\PP_n` in Parts I–II; `\Li` as `\Li_2` in Part V).

## What the report claims

**Part I (Report 156).**
- Theorem 1.1: `0 ≤ P_n(R ≤ r) − s_r(n)/p(n) ≤ C/log n` for all `r ≥ 0`, one constant
  and one onset; hence `s_0(n)/p(n) = 1/2 + O(1/log n)` (one-sided upper error
  `O(n^(−1/2))`) and `s_0(n) ~ e^(π√(2n/3))/(8√3 n)`: **ABEK Conjecture 5.3**.
  Elementary: a fixed-rank extension of ABEK's Lemma 5.4 injection (Lemma 2.1,
  `N(r,n) ≤ p(n) − p(n−1)`), an interior lemma (Lemma 3.1) and the Hardy–Ramanujan
  formula.
- Theorem 1.2: `liminf log A(n)/√n ≥ B_*`, and `q(n)/A(n) ≤ exp(−(B_* − π/√3 − η)√n)`
  eventually: **ABEK Conjecture 5.2**. Catalan and bounded-height Dyck prefixes
  followed by distinct tails (Section 6, Proposition 6.2; Section 7); the order of
  limits (fixed height first) is stated.
- Corollary 4.1: `s_r(n)/p(n) = 1/(1 + e^(−πr/√(6n))) + O(1/log n)` uniformly in `r`
  (uses Dousse–Mertens' Theorem 1.2 at positive ranks only).
- Theorem 5.1: `T(y) = x_0(y) + O(log y/log log y)` with the `W_{−1}` centre and a
  nested-log initializer; `s_0` strictly increasing for `n ≥ 4`.

**Part II (Report 159).** Theorem 10.1: the expansion of `s(n)/p(n)` to every
fixed order with `c_0 = 1/2`, `c_1 = −1/8`, `c_2 = −11/32 + 3/(4π²)`,
`c_3 = −317/384 + 329/(64π²) − 9/(8π⁴)`, by a uniform endpoint localization, a mixed
row–column insertion bijection (Lemma 13.2) and Zhou's fixed-rank expansion;
the cubic coefficient also from six explicit endpoint patterns. Theorem 10.2:
`⌈X_J − C_J x_0^(−J/2)⌉ ≤ T(y) ≤ ⌈X_J + C_J x_0^(−J/2)⌉` with
`b_0 = 7/24 + 3/π²`, `b_1 = 23/32 + 45/(2π⁴)`.

**Part III (Report 158).** Theorem 20.1:
`C/t − O(t^(−1/3)) ≤ log Σ A(n)e^(−tn) ≤ C/t + O(1)` and
`B√n − O(n^(1/3)) ≤ log A(n) ≤ B√n + O(1)`, by an exponential tilt (upper), a
bounded-height Dyck prefix with a geometric tail of survival probability
`≥ 1 − 2p` (Lemma 24.1) and a growing height through an exact spectral bound
(lower), and Chernoff bounds with the monotonicity injection (Lemma 26.1).
Theorem 20.2: `T(y) = (log y/B)² + O((log y)^(5/3))`.

**Part IV (Report 160).** Theorem 30.1: `log F(t) = C/t − ζbt^(−1/3) + o(t^(−1/3))`
and `log A(n) = 2√(Cn) − ζbC^(−1/6) n^(1/6) + o(n^(1/6))`, pointwise; Mallein's
Lemmas 2.6–2.7 (homogeneous case, `σ² = 2`) for the Airy constant, and a
self-contained exact-weight tail lemma (Lemma 34.1) with a three-arc Fourier
cover. Corollary 30.2: the inverse with the `x^(2/3)` term. Theorem 30.3:
`tK → 2b`, `K/√n → 2 log 2/√C = 1.2144974…`, cumulative profile `g(x) = x` on
`[0, b]`, `2b + log(1 − e^(−x))` beyond, row profile `f = g^(−1)` on compact subsets of
`(0, 2b)`, all deviations `≤ e^(−c/t)`; half of the limiting rows lie on the
diagonal (macroscopically). The shape theorem needs only Part III's coarse
bound.

**Part V (Report 162), conditional on arXiv:2607.27504v1.** Theorem 39.1:
`F(t) = K_F t^(1/3) exp(C/t + b a_1 t^(−1/3))(1 + α t^(1/3) + O(t^(2/3)))`,
`K_F = 2√2/Ai'(a_1) = 4.0336…`, `α = a_1²(1/4 − b/30) = 1.2404…`, and
`A(n) ~ K n^(−11/12) exp(B√n − D n^(1/6))`. Corollary 39.2:
`T(y) = x + (2D/B)x^(2/3) + (11/(6B))√x log x − (2 log K/B)√x + o(√x)`. The
preprint enters through Li's normalized turning-point expansion and the global
indexing of the first two zeros of Ramanujan's entire function (Section
40.3). The first-pole transfer (Lemma 41.1), the cutoff lemma (43.1), the local
limit (Proposition 43.2) and the inverse argument are proved in the Part; the
local limit uses the radial formula and so depends on the preprint too. The
exact generating function (from ABEK's Theorem 2.1, with the empty term
restored) and the zero product (Štampach–Šťovíček) are published inputs.

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter (including the two conjectures quoted from ABEK, the OEIS entries as
read on 6 October 2026, the notation dictionary and the status of each inverse
relative to the transseries volume); dated notes; the reading-conventions
tables; Section 47; and:
- **Proposition 1.3**: a partition `y` has distinct `z_i ≤ y_i` iff its increasing
  arrangement satisfies `λ_i ≥ i`. Proof: the condition depends only on the
  multiset; `z_i = i` works if `λ_i ≥ i`; if `λ_j < j`, the first `j` parts would need
  `j` distinct values in `{1, …, λ_j}`. Hence the count is `A(n)` for every `n ≥ 0`
  (empty partition included), and the complement is `p(n) − A(n)`. This proves
  Wiseman's conjecture in A238873 (Sep 26 2025) and his conjecture in A387118
  (Oct 04 2025). **Not new**: Clément Garrot posted the same argument in A387112
  (revision #19 of Sep 07 2026, comment of Aug 31 2026), saying it proves the
  corresponding conjectures in A238873, A387118 and A388711; A238873 (revision
  #36 of Oct 07 2025) still displays the conjecture. Checked by exhaustive
  search for `n ≤ 24`.
- **Equation (9.1)**: `P_n(R ≤ 0) − s_0(n)/p(n) = β/4 + (7/16 − 3/(2π²))β² + O(β³)`, from
  Part I's (2.5) and Part II's (11.10) at `r = 0` and (10.2). It answers Part I's
  question about the defect at `r = 0` (order `n^(−1/2)`, not `1/log n`).
  Numerically, defect/β = 0.2957, 0.2623, 0.2599 at `n` = 100, 1000, 1500 (exact
  `p(n)` and rank counts).

**The journal conjectures** (ABEK, Section 5, p. 15), quoted verbatim in the
front matter: Conjecture 5.2, `lim |Q_n|/|A_n| = 0` (`Q_n` the partitions with
distinct parts, `Q_n ⊆ A_n`); Conjecture 5.3, "We conjecture that, asymptotically,
half of the partitions are subdiagonal", `lim |S_n|/|P_n| = 1/2`. ABEK prove
`|A_n|/|P_n| → 0` (Proposition 5.1) and `limsup |S_n|/|P_n| ≤ 1/2` (Proposition
5.5), and ask for the asymptotics of `|A_n|`. Neither OEIS entry states these
conjectures. **Nothing was submitted to the OEIS or to the authors.**

**The inverses** (transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
Part I's centre `x_0` is an **instance** of `p0:thm:lambert-core` (branch
`W_{−1}`) after `p0:lem:alpha-reduction` with `α = 1/2` (`ξ = √x`, `a = 2c`, `b = −2`).
Part II's centres `X_J` are an **instance** of the reversion `p0:thm:lambert-centered`
after the same reduction (`Q(τ) = log(1 + Σ a_j c^j τ^j)`), squared back; the write
checked `b_0`, `b_1` against `p0:eq:c-bell`. The integer ceilings of Parts I–II are
**not** instances of `p0:thm:staircase` (no interpolation of the sequence). The
inverses of Parts III–V are not instances of anything in the volume (an
`O(n^(1/3))` error, or the growing term `n^(1/6)`, outside `p0:def:model`); Part V's
power-and-logarithm balance is at most analogous to `plt:thm:lw-template`.

## What the report does not claim

Every limitation is printed in place. In short: no explicit constants or
onsets anywhere, hence no certified threshold or rounding rule (every Part);
no error sensitive to `r/√n`, nothing at fixed `r ≥ 1` beyond `O(1/log n)` (Part I);
no convergence of Part II's series, no uniformity at growing order, no
coefficient beyond `c_3` computed; no optimality of Part III's `O(n^(1/3))`; no
fluctuation theorem, discrete-contact statement, extreme-row law or row
uniformity at `y = 2b` (Part IV); no pointwise relative correction, no
all-orders expansion, no `x^(1/3)` inverse term, no complex-`q` asymptotics, no
fixed-size fluctuation theorem, and no claim independent of Li's preprint
(Part V). Every manuscript reports a bounded literature search and disclaims
exhaustive priority. **All five companions**: finite exact checks prove no
asymptotic statement; numerical illustrations certify nothing.

## Further questions, and the standing rule

Each manuscript's own questions or limits section is printed as delivered;
Section 47 collects them (Vladimir's standing rule of 4 October 2026), with
sources, sketches and what is missing:

1. the defect at fixed `r ≥ 1` and growing `r` (Part I, re-scoped after (9.1));
2. explicit onsets and certified thresholds (every Part);
3. Part II's series: convergence, higher coefficients, removing the ceilings;
4. fluctuations, discrete contacts, extreme rows (Part IV);
5. an unconditional amplitude (Part V);
6. a pointwise relative correction (Part V);
7. all orders for `A(n)` (Parts III–V);
8. finer superdiagonal inverses, the `x^(1/3)` term (Part V);
9. complex-`q` turning points (Part V);
10. literature and priority (every Part).

**Answered inside the merge** (dated notes at the questions): Part I's
"superdiagonal exponential constant" (Part III: the limit is `B`; Parts IV–V for
the next terms, Part V conditionally); Part I's "subdiagonal defect" at `r = 0`
(write's (9.1) from Part II); Part III's non-optimal `O(n^(1/3))` (Part IV: the
true lower error is `D n^(1/6)(1 + o(1))`). **Refuted**: nothing; no claim of any
manuscript was found false. **Source displays repaired by Part V** (both
confirmed at the write): ABEK's Theorem 2.1 display sums from `k ≥ 1` (the empty
term is restored; a convention, giving `A(0) = 1`), and Štampach–Šťovíček's
`q`-Airy example prints an extraneous factor `q` (`A_q(w²) = q 𝔉(…)`, false at
`w = 0`) — confirmed in arXiv:1510.01454v1, Example 19; the journal version was
not read.

## What was checked, and what was not

At intake (dossier of batch 107, 5 October 2026) the five manuscripts were read
in full, the key steps of both conjecture proofs re-derived, `A(n)` recomputed
to `n = 16000` and `s(n)` to `n = 1500` by independent programs, all constants
recomputed to 30 digits, the expansion of Part II and the constants of Part V
tested numerically (front matter, "What was checked"), and Li's Theorem 1 and
Corollary 2 read and matched to Part V's normalization. At the write the
statements of Dousse–Mertens' Theorem 1.2, Liu–Zhou's Theorem 1.3, Zhou's
Theorem 4.1, Mallein's Lemmas 2.6–2.7 and Štampach–Šťovíček's Example 19 were
read in their arXiv versions, the ABEK conjectures and Theorem 2.1 in the
open-access text, and the arXiv record of Li's preprint (only v1, no journal
reference, 6 October 2026). **Not verified**: the proofs of these external
theorems (and of Hardy–Ramanujan–Rademacher), and the manuscripts' analytic
estimates beyond reading them and checking their displayed algebra.

## Relation to neighbouring reports

- No other report treats A238873, A238875, ABEK, or Ramanujan's entire
  function's turning point (searched 6 October 2026; "superdiagonal" elsewhere
  refers to matrices).
- The partition reports (`a022629-distinct-partition-norms`,
  `a033552-catalan-partitions`, `a097356-sqrt-restricted-partitions`,
  `a291698-moving-fugacity-partitions`, …) share only generic Hardy–Ramanujan and
  Boltzmann methods.
- `a082161-airy-amplitudes` meets the first Airy zero through a killed walk
  (Dirichlet operator `−∂² + 8x`): analogous mechanism, no instance either way.
- `a380274-mahonian-growing-powers/literature.md` cites R. Zhang on
  Ramanujan's entire function for a different problem.
- The transseries volume, for the inverses (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository treats these
sequences (searched 6 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 56 staged code, data and companion
  files and the two staged base files were compared with a fresh extraction
  from `60f54ea06` at the write: 0 differences; `article.tex` and this README
  then replaced the two base files). Only names changed (rule above).
- **Renamed modules break imports and paths: nothing runs in this
  directory.** The tests import `companion`, `airy_shape`, `prefactor`,
  `make_zip` and `release_tools` by their delivered names; the companions of
  Reports 156, 158 and 159 read `data/oeis_prefix(es).json` beside themselves;
  `build_pdf.py` and `make_zip.py` expect `ReportNNN.tex`, the delivered
  allowlists and Debian TeX paths (`/usr/share/texlive/texmf-dist`). Rerun from
  the archives (below).
- The `SOURCE_PROVENANCE.json` files record SHA-256 hashes of third-party PDFs
  the authoring session inspected (ABEK, Dousse–Mertens, Liu–Zhou, Zhou,
  Mallein, Štampach–Šťovíček, Li, Li–Wong, …); those PDFs were never part of the
  delivery.
- The delivered README of Report 156 (replaced by this guide) and the
  companion READMEs give `/tmp/...` example paths and POSIX commands; use a
  scratch directory outside the repository.
- Report 160's bibliography calls Report 158 "Exact exponential growth of
  superdiagonal partitions"; its delivered title has "increasing" before
  "superdiagonal" (noted in the merged bibliography).

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. The safe-output
commands (`--out`) and some tests need POSIX (`O_NOFOLLOW`, `O_DIRECTORY`); on
Windows use standard output and expect those tests to fail. The archives are
flat (no top-level directory):

```
for z in Two_Partition_Conjectures_Proofs_and_Quantitative_Extensions_Source \
         Subdiagonal_Partitions_All_Orders_Expansion_and_Integer_Inverses_Source \
         Superdiagonal_Partitions_Exact_Exponential_Growth_and_Inverse_Source \
         Superdiagonal_Partitions_Airy_Correction_and_Limit_Shape_Source \
         Superdiagonal_Partitions_Full_Prefactor_and_Refined_Inverse_Source; do
  git show 60f54ea06:docs/incoming/$z.zip > $z.zip && mkdir $z && unzip -q $z.zip -d $z
done
cd Two_Partition_Conjectures_Proofs_and_Quantitative_Extensions_Source
python3 -B companion.py counts --max-n 200 > ../c156.json && cmp ../c156.json counts.json
python3 -B companion.py threshold --value 1000 --max-n 200        # first_n 26
python3 -B -m unittest -v test_companion
cd ../Subdiagonal_Partitions_All_Orders_Expansion_and_Integer_Inverses_Source
python3 -B companion.py counts --max-n 300 > ../c159.json && cmp ../c159.json counts.json
python3 -B companion.py expansion --order 3 > ../e159.json && cmp ../e159.json endpoint_expansion.json
python3 -B -m unittest -v test_companion
cd ../Superdiagonal_Partitions_Exact_Exponential_Growth_and_Inverse_Source
python3 -B companion.py counts --max-n 200 > ../c158.json && cmp ../c158.json counts.json
python3 -B companion.py threshold --value 1000000 --max-n 200     # first_n 84
python3 -B -m unittest -v test_companion
cd ../Superdiagonal_Partitions_Airy_Correction_and_Limit_Shape_Source
python3 -B companion/airy_shape.py counts > ../c160.json && cmp ../c160.json data/counts.json
python3 -B -m unittest discover -s companion -p 'test_airy_shape.py' -v
cd ../Superdiagonal_Partitions_Full_Prefactor_and_Refined_Inverse_Source
python3 -B companion/prefactor.py counts > ../c162.json && cmp ../c162.json data/counts.json
python3 -B -m unittest discover -s companion -p 'test_prefactor.py' -v
```

Each command runs in under a minute. On Windows, strip the carriage returns
of redirected output before `cmp`. At the write (Python 3.14.4, Windows) the
five `counts` commands reproduced the shipped tables and Report 162's 14 tests
passed; at intake the other data files were regenerated byte for byte and the
only test failures were POSIX output-safety and release tests (none
mathematical). The release scripts (`build_pdf.py`, `make_zip.py`,
`test_release.py`) replay the delivered PDF and ZIP on the recorded Debian
toolchain only.

## Building the article

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX or TeX Live), single file, 90 pages; packages: amsmath,
amssymb, amsthm, mathtools, geometry, booktabs, longtable, array, pict2e,
microtype, hyperref, xurl, lmodern. Build in a scratch directory; only
`article.pdf` is committed.

## Licences

Repository text is MIT-0. ABEK is open access under CC BY 4.0; the two
conjectures and short passages are quoted with attribution. The OEIS prefixes
in `data/*oeis_prefix*.json` and the quoted OEIS lines are from The On-Line
Encyclopedia of Integer Sequences (A238873, A238875, A387112), available under
CC BY-SA 4.0 (https://oeis.org/LICENSE), with attribution URLs in the files.
