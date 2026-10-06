# Diagonal Euler Transforms

**OEIS A252782 and A270917: the n²-th root tends to 3^(1/3), not e^(1/e) (the OEIS conjecture refuted); exact phases, residue-aware inverses, the critical crossover and the growing crossover**

This is a research report built on 5 October 2026 (write batch 106) from two
manuscripts of one external research session, Reports 147 and 148 of the
session bundle of Reports 1–243, both dated 3 October 2026. They study

`A_ε(n, τ) = [xⁿ] ∏_{j≥1} (1 − ε x^j)^(−ε j^τ)`,  `ε = ±1`,

on the diagonal `τ = n` — the Euler transform of the n-th powers,
[A252782](https://oeis.org/A252782) (`ε = +1`), and its distinct-colour
analogue [A270917](https://oeis.org/A270917) (`ε = −1`) — and off it. Throughout
`n = 3m + r`, `z = m²(8/9)^τ`, `s = z/m^(3/4)`, `ρ = 5/√32`,
`δ = 2 log(√32/5)/log(9/8) = 2.0958882…`.

- **Part I** (Report 147, the base): `log A_ε(n) = (log 3/3) n² + O(n log n)`,
  so `A_ε(n)^(1/n²) → 3^(1/3) = 1.4422495703…`. This **refutes** the
  conjecture `A_ε(n)^(1/n²) → exp(exp(−1)) = 1.4446678610…` stated in both OEIS
  entries (Václav Kotěšovec, Mar 25 2016): `log x/x` is maximal at `x = e`
  over the reals but at `j = 3` over the integers. Then an exact expansion
  over logarithmic atoms; the residue amplitudes `L₀ = 3^(mn)/m!`,
  `L₁ = (3/2)4ⁿ3^((m−1)n)/(m−1)!`, `L₂ = 2ⁿ3^(mn)/m!` with every exponentially
  small sector of relative phase ≥ 7/10 (exhaustive rational certificate) and a
  uniform tail bound (onset `n ≥ 192`); the first unrestricted-minus-distinct
  difference; leading inverses to every power-log order; convergent inverses
  of finite sector models; asymptotic residue-aware integer threshold
  brackets; strict increase at every `n ≥ 1`; and a uniform crossover for a
  separately varying exponent `τ` with bounded `z`, with a correction of
  non-integer order `m^(−δ)` from parts of size five.
- **Part II** (Report 148): for `0 < z ≤ S m^(3/4)`,
  `A_ε/(L_r Ψ_r(z)) = e^(−8s^(4/3)/9)[1 − (8/9)s m^(−1/4) + {4(r−1)s^(2/3)/9 + 128s²/81} m^(−1/2) + s^p m^(−β)] + O_S(m^(−3/4))`,
  `β = (5/8)(δ − 1) = 0.6849…`, `p = δ/2 + 5/6`; the attenuation inverse of a
  smooth model on compact windows; exact real-parameter crossings exist and
  are localized (uniqueness not claimed). It answers in part Part I's further
  question 3 ("Beyond compact crossover windows").
- **Added by the write**: the explicit bound
  `3^(mn)/m^m ≤ A_ε(n) ≤ 2^(n−1) 3^(n²/3)` with a complete elementary proof, and
  its consequence `A_ε(n)^(1/n²) < e^(1/e)` for **every `n ≥ 414`**.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Diagonal Euler transforms: Exact phases critical crossover and residue aware inverses* (author line "Report 147", 3 October 2026); the base | 147 | `Diagonal_Euler_Transforms_Corrected_Growth_Crossover_and_Inverses_Source.zip` (661,247 bytes, 14 files; `Report147.tex`, 1,250 lines, 21 pp.) | ProveIt `bb1cb91b7` (its Section 12; exists in the history) | `47fc7a069` | Part I, Sections 1–13, plus the write's Subsection 2.1 |
| *Growing Euler crossover and attenuation inverse: Uniform moderate defect clouds for diagonal Euler families* (author line "Report 148", 3 October 2026) | 148 | `Growing_Euler_Crossover_and_Attenuation_Inverse_Source.zip` (1,028,032 bytes, 13 files, 2 of them Report 147's source and PDF under `foundation/`; `Report148.tex`, 1,061 lines, 17 pp.) | none | `47fc7a069` | Part II, Sections 14–26, plus the write's Section 27 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `47fc7a069` (batch 106, cluster 106-EULERD) removed them from
`docs/incoming/`. The write is "Write batch 106
(a252782-diagonal-euler-transforms): new report, diagonal Euler transforms
grow like 3^(n^2/3)".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee,
says it is AI-assisted, or carries "prepared for private review" wording; each
sets an empty PDF author field. Every result, proof, remark, question and
limitation of the two manuscripts is printed.

## Why the Parts are in this order

The base is Report 147; its `Report147.tex` was staged as `article.tex`, and it
is printed first, as Part I. Report 148 continues Part I's critical crossover
(Section 10) from bounded `z` to `z ≤ S m^(3/4)`. It restates the definitions it
needs and proves its own normalization and estimates (its Section 25 says
so), but takes the setting, the amplitudes and the functions `Ψ_r` from Report
147, so it is printed second, as Part II. Dependency order, which is also the
order of writing.

**Embedded copy.** Report 148's `foundation/Report147.tex` and
`foundation/Report147.pdf` are byte-identical to Report 147's standalone
delivery (SHA-256 at placement, `cmp` again at the write). They are printed
once, as Part I, and not shipped. Part II restates in its own words, and in its
own normalization, the two-parameter product, the formal logarithm, the
amplitudes, `H_k` and `Ψ_r`, the critical-scale atom formula, the real
roots-of-unity filter, the small-activity bad-atom argument with the
exceptional `(1,1)` term, and the Euler recurrence; these are printed in full
with notes pointing to Part I (the list, equation by equation, is in the
article's "Provenance and merge decisions").

## Files

The directory holds 20 files: 5 at the root, 12 in `code/`, 3 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 147, prefix `147-diagonal-`** (10 files): the companion README; `code/`:
the deterministic PDF builder and archive packer, the certificate generator,
the crossover algebra, the exact Euler/product/atom engines, the typed
fixtures, and the two test modules (56 tests); `data/`: the exact certificate.

```
147-diagonal-companion-README.md
code/147-diagonal-build_pdf.py
code/147-diagonal-companion-certificate.py
code/147-diagonal-companion-crossover.py
code/147-diagonal-companion-diagonal_euler.py
code/147-diagonal-companion-fixtures.py
code/147-diagonal-companion-tests-test_crossover.py
code/147-diagonal-companion-tests-test_exact.py
code/147-diagonal-make_zip.py
data/147-diagonal-companion-certificate.json
```

**Report 148, prefix `148-growing-`** (7 files): the companion README; `code/`:
the PDF builder and archive packer, the exact companion (rows, pure-cloud
identities, formal inverse algebra, rational inequality witnesses, certificate
writer and verifier) and its 26 tests; `data/`: the certificate and the source
provenance record.

```
148-growing-companion-README.md
code/148-growing-build_pdf.py
code/148-growing-companion-exact_companion.py
code/148-growing-companion-test_exact_companion.py
code/148-growing-make_zip.py
data/148-growing-SOURCE_PROVENANCE.json
data/148-growing-companion-certificate.json
```

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`Report148.tex` (printed as Part II) and the delivery README of Report 148
(Report 147's was staged and is replaced by this guide); the two `SHA256SUMS`
files (pure SHA-256 ledgers, verified at placement, 13/13 and 12/12; repository
policy drops checksum manifests); Report 148's `foundation/` copies of Report 147.

## Labels and numbering

Label prefix **`det:`** (none at HEAD before this report): Part I uses
`det:dia:` (Report 147's 89 labels), Part II `det:grow:` (Report 148's 78).
Seven bare names occur in both manuscripts (`eq:Psi`, `eq:def`,
`eq:exception`, `eq:model`, `eq:recurrence`, `eq:shift`, `thm:inverse`);
under the Part prefixes they are distinct. The write added the two Part labels;
section labels for unlabelled sections it cites (`det:dia:sec:root`,
`…:inverses`, `…:convergent`, `…:brackets`, `…:companion`, `…:further`;
`det:grow:sec:definitions`, `…:pure`, `…:five`, `…:inverse`, `…:second`,
`…:companion`, `…:background`, `…:further`); Subsection 2.1's
`det:dia:sub:explicit`, `det:dia:prop:explicit`, `det:dia:cor:refute`,
`det:dia:rem:exact`, `det:dia:eq:explicit`, `det:dia:eq:explicitlog`,
`det:dia:eq:refute`; the front matter's `det:sec:guide`, `det:sec:status`,
`det:sec:oeis`, `det:sec:notation`, `det:sec:provenance`, `det:sec:trust`,
`det:sec:neighbours`; and Section 27's `det:sec:further` with the eight items
`det:q:effective`, `det:q:allorders`, `det:q:growing`, `det:q:monotone`,
`det:q:integer`, `det:q:weights`, `det:q:convergence`, `det:q:literature`.
206 labels in all, all distinct.

| Part | Manuscript | Section here | Statement and equation `k.j` |
|---|---|---|---|
| I | Report 147 | `k` (1–13, unchanged); 2.1 added | `k.j` |
| II | Report 148 | `k + 13` (14–26); 27 added | `(k+13).j` |

Both manuscripts number equations within sections, so equations shift with
their sections. Report 148's Theorem 2.1 and Corollary 2.2 are 15.1 and 15.2;
its Propositions 5.1, 6.1 are 18.1, 19.1, its Lemma 5.2 is 18.2; its Theorems
8.1 and 9.1 are 21.1 and 22.1; its Lemma 10.1 is 23.1. A comparison of the
build's `.aux` with separate builds of the two delivered `.tex` files confirmed
all 167 delivered labels under these offsets and prefixes. The delivered
READMEs, code and data use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`τ`/`t`** (Part I's outer exponent is `τ` and its `t` is a
logarithmic threshold; Part II's outer exponent is `t`), **`L`** (Part I's
diagonal amplitudes `L_r(n)`, smooth `L_r(x)` and two-parameter `𝓛_r`; Part II's
`L = log(9/8)` and its `L_r`, which are Part I's `𝓛_r`), **`α`** (`log 3/3`;
`5/(4L)`), **`β`** (Part I's relative phases and bases; Part II's exponent
`(5/8)(δ−1)`), **`𝓑`** (sector bases; bad atoms), **`q`** (`√2/3^(1/3)`; Part
II's residue maps `q_r` and target level `q`), **`κ`** (Part I's `(0,2,1)`,
which is Part II's `q_r`; Part II's exponent `1.618…`), **`W`, `P`** (Part I's
cutoff falling factorial `W_ℓ(m)` is Part II's `P_ℓ(m)`; Part II's `W_ℓ = 4w/9`
is a variance), **`R`**, **`Q`**, **`E`**, **`H`**, **`M`**, **`S`**, **`T`**,
**`Δ`**, **`μ`**, **`h`**, **`d`**, **`p`**, **`u`**, **`v`**. Same in both
Parts: `z`, `a = z^(1/3)`, `ρ`, `δ`, `H_k = [u^k]exp(u+u²)`, `Ψ_r`, `F_q(a)`,
`ω`, the activities `λ_jk`, `D`, `ℓ`.

## What the report claims

**Part I (Report 147).**
- Theorem 2.1: `log A_ε(n) = (log 3/3)n² + O(n log n)`, `A_ε(n)^(1/n²) → 3^(1/3)`,
  different from `exp(1/e)`. The integer-break maximum (2.2) is classical,
  as the manuscript says.
- Theorem 3.1 (exact atom identity); Lemma 4.1 (`μ⁶ ≤ 9^r(8/9)^D`); Theorem 4.2
  (uniform degree and spectral tails, explicit onset `n ≥ 192`, sufficient,
  not sharp).
- Theorem 5.1: `A_ε(n) ~ L_r(n)` with sectors `(8/9)ⁿ`, `(64/81)ⁿ`, `(5/6)ⁿ`;
  Table 1, every common relative phase ≥ 7/10, by an exhaustive rational
  enumeration whose exhaustiveness is proved; the two signs agree there.
- Theorem 6.1: `(A₊ − A₋)/L_r ~ (5/2)(m)₂(4/9)ⁿ, (4/3)(1/2)ⁿ, (1/2)ⁿ`; Table 2.
- Proposition 7.1, Theorem 7.2: the leading inverse to every power-log order;
  Theorem 8.1: the Lagrange–Bürmann series of each finite sector model
  converges, with displacement error `O(x^K β_max^(2x))`; Proposition 8.2
  (compatibility); Theorem 9.1: residue-aware integer brackets, asymptotic
  only; Proposition 9.2: `A_ε(n+1) > A_ε(n)` for every `n ≥ 1` (an explicit
  injection).
- Theorem 10.1: the uniform crossover for `0 < z ≤ M`, with entire `Ψ_r`, two
  algebraic corrections and the term `ρ^τ Φ_r(z) = m^(−δ) z^(δ/2) Φ_r(z)`,
  `2 < δ < 3`.

**Part II (Report 148).**
- Theorem 15.1 and Corollary 15.2: the growing crossover above, uniformly in
  sign and residue, with no lower bound on `z`; `2 < δ < 11/5`,
  `5/8 < β < 3/4` by integer comparisons.
- Proposition 18.1 (pure-cloud depletion with a global falling-factorial
  remainder), Lemma 18.2, Proposition 19.1 (the whole bad-atom sum,
  `𝓢_bad = λ₅{1 + O_S(m^(−κ))}`, `κ = 1.618…`), Section 20 (the size-five term
  and the zero endpoint).
- Theorem 21.1: the smooth model has a unique root on the window, with the
  expansion of `σ_{r,m}(q)` and of the exponent `τ_{r,m}(q)`; Theorem 22.1:
  exact real-`t` crossings exist and every one in the window is localized
  within `O(m^(−3/4))`; uniqueness and monotonicity of the exact ratio are not
  claimed. Lemma 23.1: a second (Gaussian) route to the pure coefficients.

**Added by the write** (all marked `[write]`, dated 5 October 2026): the front
matter (including the OEIS entries as read on 5 October 2026 and the status of
each inverse relative to the transseries volume); dated notes; Section 27
(further questions); and Subsection 2.1 with its proofs:
- **Proposition 2.2**: for either sign and every `n = 3m + r ≥ 3`,
  `3^(mn)/m^m ≤ A_ε(n) ≤ 2^(n−1) 3^(n²/3)` (upper bound for every `n ≥ 1`). Proof:
  `j ≤ 3^(j/3)` for every integer `j ≥ 1` (equality only at 3), so each
  profile weight is at most `∏ j^(n m_j) ≤ 3^(n²/3)`; at most `2^(n−1)`
  partitions; the profile of `m` threes (padded by one 1 or one 2) has weight
  at least `C(3ⁿ, m) ≥ (3ⁿ/m)^m`.
- **Corollary 2.3**: `A_ε(n)^(1/n²) ≤ 2^((n−1)/n²) 3^(1/3) < 2^(1/n) 3^(1/3) < e^(1/e)`
  for every `n ≥ 414`, because `log 3/3 < 1/e` and
  `log 2/(1/e − log 3/3) = 413.73…`. So the conjecture is refuted by the upper
  bound alone, not merely sharpened. (`n = 414` is the least index for the
  factor `2^(1/n)`; the factor `2^((n−1)/n²)` already works at 413. The intake
  record's "`n ≥ 415`" is true but not the least.)
- **Remark 2.4** (finite computation): exact `A_±(n)` for `n ≤ 109` agree with
  both b-files (`n ≤ 80`); `A₊(n)^(1/n²) > e^(1/e)` exactly for `2 ≤ n ≤ 7`,
  `A₋(n)^(1/n²) > e^(1/e)` exactly for `3 ≤ n ≤ 7`; with `log p(n) < (1/e − log 3/3)n²`
  for `110 ≤ n ≤ 413` (exact partition numbers) this gives
  `A_ε(n)^(1/n²) < e^(1/e)` for every `n ≥ 8`.

**The OEIS statements.** Both entries were read on 5 October 2026 (A252782
revision #20 of Mar 22 2017; A270917 revision #15 of Oct 16 2017). A252782's
formula section has "Conjecture: limit n->infinity a(n)^(1/n^2) =
exp(exp(-1)) = 1.444667861... . - _Vaclav Kotesovec_, Mar 25 2016"; A270917's
has the same line unsigned, in the entry Kotěšovec created on Mar 25 2016.
The terms are right (b-files agree with exact recomputation); the conjectured
limit is wrong. **Nothing was submitted to the OEIS.**

**The inverses.** No inverse here is an instance of the transseries volume's
Lambert core `p0:thm:lambert-core` or factorial core `p0:prop:factorial-core`,
and no Lambert W occurs (volume:
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
Part I's Theorem 7.2 has a quadratic phase, outside the volume's
exponential–power model `p0:def:model`; its triangular recurrence is the scheme
of `p0:thm:core-reversion` with log-polynomial coefficients — an analogue.
Part I's Theorem 8.1 is the series of `p0:thm:perturbed-inversion` at
`ε = 1`, with the convergence at `ε = 1` proved in Part I. Part I's Theorem 9.1
has the residue-class form of `p0:thm:staircase` (4) but is proved directly at
the integers, without the interpolation of the sequence that theorem
presupposes — not an instance. Part II's Theorem 21.1 inverts the power core
`−γ s^(4/3)` exactly, and its coefficients are those of the multi-parameter
form `p0:eq:perturbed-multi` (checked symbolically) — an instance of the
coefficient formula. Part II's Theorem 22.1 concerns real `t` only.

## What the report does not claim

Every limitation is printed in place. In short: no effective onsets beyond
Part I's forward-tail `n ≥ 192` and Part II's bad-atom onset, so no
finite-input threshold certificate (Part I's "Operational boundary"); no
all-orders theorem in either crossover regime; no uniform range with
`s → ∞`; no exact monotonicity or uniqueness of exact crossings, no first
crossing, no integer-`t` threshold (Part II); no convergence of the power-log
inverse series and no canonical smooth interpolation (Part I); the real-`τ`
distinct model is a signed formal model, positivity of its factors not
asserted. The integer-break step, Stirling expansion, Lagrange inversion,
conditioning, roots-of-unity, moment and Taylor methods are classical, as the
manuscripts say; no global priority claim is made (Part I's search was
bounded; Part II inspected only abstracts of Arratia–Tavaré and
Arratia–DeSalvo). **Both companions**: finite exact checks prove no
asymptotic remainder; hashes detect changes and validate no theorem.

## Further questions, and the standing rule

Part I's Section 13 and Part II's Section 26 are the manuscripts' own;
Section 27 collects them with the stated non-claims (Vladimir's standing rule
of 4 October 2026), with sources, sketches and what is missing:

1. effective onsets and certified integer thresholds (Part I q. 1 and its
   operational boundary; Part II q. 5); a sharp onset in Theorem 4.2;
2. all orders in both crossover regimes (Part I q. 2; Part II q. 2);
3. beyond `z ≤ S m^(3/4)`, i.e. `s → ∞`, and the bridge to fixed exponents
   (Part I q. 3, re-scoped; Part II q. 1);
4. exact monotonicity and uniqueness of crossings (Part II q. 3);
5. integer exponents (Part II q. 4);
6. other integer weights (Part I q. 4);
7. convergence of the power-log inverse and a canonical interpolation (Part I);
8. literature and priority, including an earlier statement of `3^(1/3)`
   (Part I Section 12; Part II q. 6).

**Answered inside the merge**: Part I's question 3 ("Beyond compact crossover
windows. Analyze growing z with quantitative uniformity"), in part, by Part
II's Theorem 15.1 — dated note at the question. **Refuted**: the OEIS
conjecture of A252782 and A270917 (Theorem 2.1, Corollary 2.3). **Corrected**:
one printed decimal in Part II — `β = 0.684930142718664…` should read
`0.684930142718661…` (`β = 0.6849301427186619…`); dated note at (15.2); nothing
depends on it. No mathematical claim of either manuscript was found wrong.

## Relation to neighbouring reports

- No other report treats A252782, A270917, their parent arrays A144048 and
  A284992, or Euler transforms with exponent equal to the index (searched 5
  October 2026).
- `a290354-iterated-euler-diagonals` (same batch) studies iterated Euler
  transforms by parabolic iteration; it shares no definition, lemma, constant
  or method with this report, only the words "Euler transform".
- `a033552-catalan-partitions` uses the Arratia–Tavaré independent-process
  conditioning that Part II uses (method parallel only).
- The transseries volume `Transseries_And_Inversion` (above), for the inverses.

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository treats these
sequences (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 17 staged companion, code and
  data files and the two staged base files were checked against a fresh
  extraction from `60f54ea06` at the write: 0 differences; `article.tex` and
  this README then replaced the two staged base files). Only names changed
  (tables at the end). The delivered code and markdown use delivery paths
  (`companion/`, `companion/tests/`, `certificate.json`, `Report147.tex`,
  `Report148.tex`, `README.md`, `SHA256SUMS`, `foundation/`), which are shipped
  under other names or not at all.
- **Renamed modules break imports: nothing runs in this directory.** Report
  147's `certificate.py` and tests import `diagonal_euler`, `crossover`,
  `fixtures` and `certificate` by their delivered names, and Report 148's
  tests import `exact_companion`; `build_pdf.py` and `make_zip.py`
  hard-code the delivered file lists and Debian TeX paths
  (`/usr/share/texlive/texmf-dist`, `/usr/share/texmf`). Rerun from the archive
  (below).
- `data/148-growing-SOURCE_PROVENANCE.json` lists SHA-256 hashes of seven
  source notes (`bad_atom_bound_review.md`, `growing_crossover_theorem.md`, …)
  that were never part of the delivery, and of `foundation/Report147.{pdf,tex}`,
  which are not shipped (byte-identical to Report 147's delivery).
- Part I's bibliography records the OEIS pages as "retrieved crawl six days
  earlier" than 3 October 2026; the write's live reading (5 October 2026) is
  recorded in the front matter.
- Report 147's delivered README (replaced by this guide) and Report 148's
  give `/tmp/...` example paths; use a scratch directory outside the
  repository.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (both archives are flat: no top-level
directory):

```
git show 60f54ea06:docs/incoming/Diagonal_Euler_Transforms_Corrected_Growth_Crossover_and_Inverses_Source.zip > r147.zip
git show 60f54ea06:docs/incoming/Growing_Euler_Crossover_and_Attenuation_Inverse_Source.zip > r148.zip
mkdir x147 x148 && unzip -q r147.zip -d x147 && unzip -q r148.zip -d x148
cd x147
python -m unittest discover -s companion/tests -v
python -O -m unittest discover -s companion/tests -v
python companion/certificate.py > ../cert147.json
cd ../x148
python -m unittest discover -s companion -p 'test_*.py' -v
python -O -m unittest discover -s companion -p 'test_*.py' -v
python companion/exact_companion.py --verify companion/certificate.json
python -O companion/exact_companion.py --verify companion/certificate.json
```

Compare `../cert147.json` with `x147/companion/certificate.json` (`cmp` on
Linux or macOS; on Windows the redirected output, and also the `--output`
route, is written in text mode with CRLF line ends, so compare after removing
carriage returns, e.g. `tr -d '\r' < cert147.json | cmp - x147/companion/certificate.json`).
Both companions need only the Python standard library (3.10 or later).
Report 148's `--write-certificate` and two of its 26 tests need POSIX
`O_NOFOLLOW`/`O_DIRECTORY`; on Windows those two tests stop with "safe
certificate creation requires POSIX O_NOFOLLOW/O_DIRECTORY" — a platform
requirement the package README states, not a mathematical failure.
`build_pdf.py` and `make_zip.py` need the Debian-style TeX Live of the delivery
and were not run.

Results: at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-106 dossier) Report 147's 56 tests passed in normal and
`-O` mode (about 3 s) and its certificate regenerated identically after
CRLF→LF; Report 148's tests gave 24 OK and the 2 POSIX errors, `--verify`
passed, and an in-memory regeneration equals the certificate byte for byte. At
the write (5 October 2026, fresh extractions, Windows) the same: 56/56 twice,
certificate equal after removing CR; 24/26 with the 2 POSIX errors; `--verify`
passed in both modes (payload SHA-256 `43a4d5ab…`). The two delivered `.tex`
files compile with MiKTeX pdfLaTeX to 21 and 17 pages with no warnings.

## Rights

Repository contents are MIT-0. Report 147's `fixtures.py` embeds the first
twelve terms of A252782 and A270917 (index 0–11) as hard-coded OEIS
fixtures; OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). All other counts, including the
terms that occur in the two certificates, are recomputed by the packages. The OEIS entries are credited
for the sequences, Václav Kotěšovec for the conjecture this report refutes and
for the fixed-exponent q-series paper Part I cites (arXiv:1509.08708, not read
by the write), Arratia–Tavaré and Arratia–DeSalvo as Part II cites them, and
the DLMF §5.11. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build
(49 pages): no errors, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull or underfull boxes, no
warnings. The log carries two "Infinite glue shrinkage found in box being
split" messages, from the notation longtable and Part I's Table 1 breaking
across pages (the delivered `Report147.tex` alone has none; its Table 1 does
not break there).

## Delivered path → shipped path

Report 147 (`147-diagonal-`; delivered flat, no top-level directory):

| Delivered | Shipped |
|---|---|
| `Report147.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `build_pdf.py`, `make_zip.py` | `code/147-diagonal-<name>` |
| `companion/README.md` | `147-diagonal-companion-README.md` |
| `companion/certificate.py`, `crossover.py`, `diagonal_euler.py`, `fixtures.py` | `code/147-diagonal-companion-<name>` |
| `companion/tests/test_crossover.py`, `test_exact.py` | `code/147-diagonal-companion-tests-<name>` |
| `companion/certificate.json` | `data/147-diagonal-companion-certificate.json` |
| `Report147.pdf`, `SHA256SUMS` | not shipped |

Report 148 (`148-growing-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report148.tex` | not shipped; printed as Part II of `article.tex` |
| `build_pdf.py`, `make_zip.py` | `code/148-growing-<name>` |
| `companion/README.md` | `148-growing-companion-README.md` |
| `companion/exact_companion.py`, `test_exact_companion.py` | `code/148-growing-companion-<name>` |
| `companion/certificate.json` | `data/148-growing-companion-certificate.json` |
| `SOURCE_PROVENANCE.json` | `data/148-growing-SOURCE_PROVENANCE.json` |
| `foundation/Report147.tex`, `.pdf` | byte copies of Report 147; not shipped |
| `README.md`, `Report148.pdf`, `SHA256SUMS` | not shipped |

## Provenance

Two manuscripts (bundle Reports 147, 148) → one report; base 147, printed as
Part I. Arrival `60f54ea06`, placement `47fc7a069`, write batch 106 (5 October
2026). Report 147 pins ProveIt `bb1cb91b7`; Report 148 pins nothing. Merge
choices (dependency order with the base first, restatements printed with
pointers, the embedded copy printed once, the merged bibliography with Report
148's entry for Report 147 pointing to Part I) are listed in the article's
front matter, "Provenance and merge decisions".
