# The Proportional Placement Game (OEIS A398540)

**A computable rate, the leading equivalent `W_n ~ r_* √(2πn) r_*^n`, the logarithmic corrections and every fixed order**

This is a research report built on 5 October 2026 (write batch 105) from
three manuscripts of one external research session, Reports 144, 145 and 146
of the session bundle of Reports 1–243, all dated 3 October 2026. They treat
one sequence. In the continuous placement game, `n` independent uniform values
on `(0,1)` arrive one at a time and must be placed at once into `n` ordered
slots so that the placed values increase; the proportional policy puts a
value into the slot of its containing gap that matches its relative position.
Its winning probabilities `W_n` (`W_0 = W_1 = 1`, `W_2 = 3/4`,
`W_3 = 83/162`, …) satisfy the exact recurrence
`W_n = (1/n) Σ_k W_{k−1} W_{n−k} Q_{n,k}` with beta-binomial weights `Q_{n,k}`,
derived in A. Serra's manuscript *The Number Challenge* (Zenodo record
21946055), and [OEIS A398540](https://oeis.org/A398540) records digits of
`r_* = lim W_{n+1}/W_n = 0.5754723815…`. Throughout `R = 1/r_*`,
`A = r_* √(2π)` and `x_n = W_n R^n / (A √(n+1))`.

- **Part I** (Report 144): `r_* = lim W_n^{1/n}` exists and is computable;
  `527/1000 < r_* < 79/125` by exact rational arithmetic; `W_n ~ r_* √(2πn) r_*^n`
  and `W_{n+1}/W_n → r_*`. The amplitude corrects Serra's `√(2π)`. Also the pole
  and logarithmic second term of `Σ W_n z^n/√(n+1)`, cumulative laws, and
  Lambert-W inverses.
- **Part II** (Report 145): `W_n/(A√n r_*^n) = 1 + 1/(4n) − (7/540) log n/n² + B_2/n² + o(n^{−2})`,
  `B_2` by absolutely convergent series; eventual strict decrease of the
  ratios; no pure inverse-power ratio expansion through `n^{−3}`; a refined inverse.
- **Part III** (Report 146, the base): every fixed order,
  `x_n = 1 + Σ_{j≤M} P_j(log n)/n^j + O_M((1+log n)^M/n^{M+1})` with `deg P_j ≤ j−1`;
  the explicit third order (the squared logarithm cancels); the ratio term
  `(7/270) log n/n³`; a dyadic five-point extrapolation; inverses at every
  fixed order; computable nested rate enclosures with a proved contraction.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Asymptotics and a computable exponential rate for a proportional placement game* (title block "Report 144"; no author line) | 144 | `A398540_Placement_Game_Leading_Asymptotics_and_Inverse_Source.zip` (1,059,711 bytes, 12 files; `Report144.tex`, 979 lines, 21 pp.) | none | `e85586b7c` | Part I, Sections 1–13 (13 = its Appendix A), plus the write's Remarks 10.2, 11.3 and Proposition 10.3 |
| *Pointwise corrections for the proportional placement game* (title block "Report 145"; no author line) | 145 | `A398540_Placement_Game_Logarithmic_Corrections_and_Inverse_Source.zip` (1,034,994 bytes, 16 files, two of them Report 144 under `foundation/`; `Report145.tex`, 995 lines, 21 pp.) | none | `e85586b7c` | Part II, Sections 14–25, plus the write's Remark 23.3 |
| *All fixed orders for the proportional placement game* (title block "Report 146"; no author line); the base; "corrected in place" before delivery | 146 | `A398540_All_Orders_Logarithmic_Asymptotics_and_Inverses_Source.zip` (1,541,057 bytes, 19 files, four of them Reports 144 and 145 under `foundation/`; `Report146.tex`, 950 lines, 22 pp.) | none | `e85586b7c` | Part III, Sections 26–37, plus the write's Remarks 33.3, 34.3 and Section 38 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `e85586b7c` (batch 105, cluster 105-GAME) removed them from
`docs/incoming/`. The write is "Write batch 105
(a398540-proportional-placement-game): new report, the proportional placement
game A398540".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author, a tool or an
addressee, says it is AI-assisted, or carries "prepared for private review"
wording; each sets an empty PDF author field. Every result, proof, remark,
question and limitation of the three manuscripts is printed; the copies of
Reports 144 and 145 embedded in Reports 145 and 146 are byte-identical to the
standalone deliveries and are printed once.

**Report 146 was corrected before delivery.** The bundle's README says:
"Where a saved archive was corrected in place, the latest corrected version is
included: Reports 146 and 205. Their superseded versions are not repeated."
The earlier version of Report 146 was never received (it is in neither the
bundle, the repository history nor this machine), so what the correction
changed cannot be told; the archive has no changelog. The delivered Report 146
is internally consistent: its `SHA256SUMS` verifies (18/18), its receipts'
hashes match the shipped files, and its checker reproduced its receipt byte
for byte on a copy at placement.

## Why the Parts are in this order

The base is Report 146, the strongest manuscript, and its `Report146.tex` was
staged as `article.tex`. It is printed **last**, as Part III, because it is
not self-contained: it imports the leading equivalent, the kernel bounds, the
radius facts and the certified rate bracket from Report 144, and the starting
rate `x_n = 1 − 1/(4n) + O((1+log n)/n²)`, the exact critical inverse and the
series definition of `B_2` from Report 145, without proving them again. Report
145 in turn rests on Report 144. All three are printed in full, in dependency
order, which is also the order of writing.

## Files

The directory holds 31 files: 10 at the root, 11 in `code/`, 10 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

| File | Bytes | What it is |
|---|---|---|
| `README.md` | — | this guide (replaces Report 146's delivered README) |
| `article.tex` | 262,319 | the merged article: front matter, Parts I–III, Section 38 |
| `article.pdf` | 1,084,668 | its build, 83 pages |

**Delivered files**, byte-identical to the delivery (all 28 checked against
the pristine extraction at the write: 0 differences):

| File | Bytes | Delivered as |
|---|---|---|
| `144-leading-SOURCES.md` | 2,604 | Report 144 `SOURCES.md` |
| `144-leading-companion-README.md` | 7,410 | Report 144 `companion/README.md` |
| `144-leading-companion-SCHEMA.md` | 3,349 | Report 144 `companion/SCHEMA.md` |
| `144-leading-companion-PROVENANCE.md` | 1,524 | Report 144 `companion/PROVENANCE.md` |
| `145-logcorr-companion-README.md` | 9,420 | Report 145 `companion/README.md` |
| `146-allorders-SOURCES.md` | 3,055 | Report 146 `SOURCES.md` |
| `146-allorders-companion-README.md` | 14,486 | Report 146 `companion/README.md` |
| `code/144-leading-bundle.py` | 6,118 | Report 144 `bundle.py` (deterministic archive and PDF build) |
| `code/144-leading-companion-verify_certificate.py` | 16,468 | Report 144 `companion/verify_certificate.py` (exact rate certificate) |
| `code/144-leading-companion-test_verifier.py` | 13,679 | Report 144 `companion/test_verifier.py` |
| `code/145-logcorr-build_pdf.py` | 3,417 | Report 145 `build_pdf.py` |
| `code/145-logcorr-build_archive.py` | 3,052 | Report 145 `build_archive.py` |
| `code/145-logcorr-companion-checks.py` | 19,077 | Report 145 `companion/checks.py` (exact algebra checks) |
| `code/145-logcorr-companion-test_checks.py` | 13,391 | Report 145 `companion/test_checks.py` |
| `code/146-allorders-build_pdf.py` | 3,430 | Report 146 `build_pdf.py` |
| `code/146-allorders-build_archive.py` | 3,130 | Report 146 `build_archive.py` |
| `code/146-allorders-companion-checks.py` | 30,789 | Report 146 `companion/checks.py` (exact algebra checks) |
| `code/146-allorders-companion-test_checks.py` | 16,407 | Report 146 `companion/test_checks.py` |
| `data/144-leading-companion-fixtures-rate_certificate.json` | 512,653 | Report 144 `companion/fixtures/rate_certificate.json` (`W_0, …, W_100` as reduced rationals, square-root floors, the certificate inequalities) |
| `data/145-logcorr-companion-fixture.json` | 4,737 | Report 145 `companion/fixture.json` |
| `data/145-logcorr-companion-receipt.json` | 832 | Report 145 `companion/receipt.json` |
| `data/145-logcorr-companion-tests-normal.json` | 279 | Report 145 `companion/tests-normal.json` |
| `data/145-logcorr-companion-tests-optimized.json` | 278 | Report 145 `companion/tests-optimized.json` |
| `data/146-allorders-companion-fixture.json` | 9,573 | Report 146 `companion/fixture.json` |
| `data/146-allorders-companion-receipt.json` | 1,938 | Report 146 `companion/receipt.json` |
| `data/146-allorders-companion-tests-normal.json` | 563 | Report 146 `companion/tests-normal.json` |
| `data/146-allorders-companion-tests-optimized.json` | 563 | Report 146 `companion/tests-optimized.json` |
| `data/146-allorders-toolchain.json` | 387 | Report 146 `toolchain.json` (byte-identical to Report 145's) |

The Report 144 fixture (512,653 bytes) regenerates byte for byte from
`verify_certificate.py`'s `generate_certificate()` in about 20 s (placement
dossier); it is shipped because the verifier validates against it.

## Labels and numbering

Label prefix **`ppg:`** (none at HEAD before this report): Part I uses
`ppg:lead:` (Report 144's 103 labels), Part II `ppg:log:` (Report 145's 132),
Part III `ppg:all:` (Report 146's 120). The front matter uses
`ppg:sec:guide`, `ppg:sec:status`, `ppg:sec:notation`, `ppg:sec:provenance`,
`ppg:sec:neighbours`. The write added the three Part labels
(`ppg:lead:part`, `ppg:log:part`, `ppg:all:part`), labels on six unlabelled
headings (`ppg:lead:sec:model`, `ppg:lead:sub:source`, `ppg:log:sec:model`,
`ppg:log:sub:scope`, `ppg:all:sec:main`, `ppg:all:sub:scope`), one on Report
144's unlabelled Proposition 2.1 (`ppg:lead:prop:recurrence`), the statements
`ppg:lead:rem:serra`, `ppg:lead:prop:op3`, `ppg:lead:rem:inverse`,
`ppg:log:rem:inverse`, `ppg:all:rem:op2`, `ppg:all:rem:inverse`, the section
`ppg:sec:further` and its eight questions `ppg:fq:*`. 385 labels in all (355
delivered, 30 write), all distinct. The manuscripts share bare label names
(`eq:T`, `sec:kernel`, `eq:factor`, `lem:factor`, `eq:normalization`, …); they
are distinct under the Part prefixes and name different statements.

Sections are numbered continuously and statements within sections:

| Part | Manuscript | Section here | Statement `k.j` |
|---|---|---|---|
| I | Report 144 | `k` (1–12); its Appendix A is Section 13 | `k.j` (unchanged); Remarks 10.2, 11.3 and Proposition 10.3 added |
| II | Report 145 | `k + 13` (14–25) | `(k+13).j`; Remark 23.3 added |
| III | Report 146 | `k + 25` (26–37); Section 38 added | `(k+25).j`; Remarks 33.3, 34.3 added |

For example Report 145's Theorem 1.1 is Theorem 14.1, its Theorem 8.6 and
Corollary 8.7 are 21.6 and 21.7, its Theorems 9.1 and 10.1 are 22.1 and 23.1;
Report 146's Theorem 1.1 is 26.1, Theorem 7.1 is 32.1, Corollaries 8.1 and 8.2
are 33.1 and 33.2, Theorems 9.1 and 10.1 are 34.1 and 35.1. The statements
added by the write are the last numbered statements of their sections, so no
delivered statement number moved; a comparison of the build's `.aux` with
separate builds of the three delivered `.tex` files confirmed every
non-equation label under these offsets (0 mismatches). **Equation numbers are
not kept**: the manuscripts number equations consecutively, the merged article
within sections; every equation keeps its label name. The delivered READMEs,
data and code use the manuscripts' own numbers, and the manuscripts cite each
other as "Report 144" and "Report 145" (Parts I and II here).

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every symbol whose meaning changes between or within Parts, and
each Part opens with a short table of its own readings. The traps: Part II's
`c = −7/360` (a covariance coefficient) versus Part III's `c = −7/540` (Part
II's `κ`); `p = 1/4`, `q = −5/12` versus the integer indices `p, q` of Part
III's models `B_{p,q} = u^{p−1}L^q`; `x_0 = 1/A` versus the Lambert root
written `x_0` in Part II's inverse theorem; Part II's `a_i = (b_i−1)x_i`,
which Part III calls `δ_i`; `u = 1 − z` in Part III's Sections 28–32 versus
`u_n = W_n/√(n+1)`; `A`, `B`, `L`, `U` as interval endpoints in Section 35.

## What the report claims

Proved in the manuscripts (Part, statement here):

- The recurrence (I, Prop. 2.1, derived independently of Serra's Theorem 3.12);
  `W_n` are positive rationals; `W_2, …, W_5`.
- Existence and computability of `r_*`, `1/16 ≤ r_* ≤ √3/2`, convergent lower
  and upper certificates (I, Thms 3.4, 5.1); `527/1000 < r_* < 79/125`
  (I, (5.4)–(5.5), by exact rational computation through `n = 100`).
- Kernel bounds `a e^{−2/3} ≤ α_{i,j} ≤ 1`, `α_{i,j} > a = (2π)^{−1/2}` and the
  first expansion (I, Thms 4.1, 4.2); the boundary covariance
  `1 − 7/(360ij)` and boundary-matched kernel (II, Lemma 18.2, Prop. 18.3); the
  endpoint-inclusive factorization and kernel expansions to every order
  (III, Lemmas 27.1, 27.2).
- The pole and logarithmic second term of `F(z) = Σ W_n z^n/√(n+1)`,
  cumulative laws, `G(z) ~ π/(√2 R) (1 − z/R)^{−3/2}` (I, Thms 6.2, 6.3, 7.1).
- `W_n ~ r_* √(2πn) r_*^n`, `W_{n+1}/W_n → r_*` (I, Thm 9.4): Serra's
  Conjecture 6.10 / Open Problem 4, with its constant; any equivalent
  `C n^γ r^n` has `γ = 1/2`, `C = r_* √(2π)` (I, Thm 10.1).
- `1 + 1/(4n) − (7/540) log n/n² + B_2/n² + o(n^{−2})` (II, Thms 14.1, 21.6);
  eventual strict decrease of `W_{n+1}/W_n` and eventual log-concavity
  (II, Cor. 21.7); no ratio expansion `r_* + a_1/n + a_2/n² + a_3/n³ + o(n^{−3})`
  (II, Thm 22.1).
- Every fixed order with `deg P_j ≤ j − 1` (III, Thm 26.1); the third order,
  log coefficient `22/2835 + c S_A` (normalized by `A√n r_*^n`), squared
  logarithm zero (III, Thm 32.1); `W_{n+1}/(r_* W_n) = 1 + 1/(2n) − 3/(8n²) +
  ((7/270) log n + 32/135 − 2B_2)/n³ + O((1+log n)³/n⁴)` (III, Cor. 33.1); a
  five-point dyadic extrapolation with error `O((1+log n)³/n⁴)` (III, Cor. 33.2).
- Inverses: the generating-function inverse `z(Y)` (I, Thm 11.1); the first
  passage `N(ε) = min{n : W_n ≤ ε}` inside ceilings around the Lambert centre
  `−W_{−1}(−2λε²/A²)/(2λ)`, `λ = log(1/r_*)`, with vanishing uncertainty
  (I, Thm 11.2), uncertainty `o(x^{−2})` (II, Thm 23.1), and
  `O((1+log x)^M/x^{M+1})` at every fixed order with Newton centres
  (III, Thm 34.1).
- Nested rational enclosures of `R` with width contraction `313/400` per
  update and a quadratic-times-log width bound (III, Thm 35.1; no run).

Added in the write, with proofs (each tagged **[write]** in the article):

- **Remark 10.2**: Serra's prefactor `C = √(2π) ≈ 2.507` (his Proposition 6.17,
  display (149), printed page 48; restated in Remarks 6.20(ii) and 8.4, his
  abstract and Section 1.3) is wrong: the limit of `W_n/(√n r_*^n)` is
  `A = r_* √(2π) ∈ (1.32, 1.59)`; it is approached from above, with no
  `n^{−1/2}` term, contrary to his "approached from below" and Remark 6.19's
  `C(1 − b/√n + O(1/n))`; the lost factor `r^{−1}` comes from replacing the
  child sizes `k−1, n−k` (sum `n−1`) by `xn, (1−x)n` (sum `n`). His
  Proposition 6.17 is a correct formal computation for his integral equation
  (140); what fails is (140) as a model of the recurrence (47), and every
  statement that transfers `√(2π)` to `W(n)`. Serra does not define
  `C_eff(n)`; it is read as `W(n)/(√n r_∞^n)`, compatible with his (8).
- **Proposition 10.3**: Serra's integral equation (200) (his Open Problem 3),
  with `W(xn)` read through any measurable extension `W̃(t) ≤ K√(t+1) r_*^t`,
  `W̃(t) ~ A√t r_*^t` (his Step-2 ansatz taken with the true amplitude `A`,
  or an interpolation of `W_n`), has
  `E(n)/W(n) → 1 − r_* ∈ (46/125, 473/1000)`, not `o(1)`. With any amplitude,
  `W̃(t) ~ C√t r_*^t`, the limit is `1 − C²/(2πr_*)`: `1 − 1/r_* ≈ −0.738` for
  Serra's own `C = √(2π)`, and zero only for `C = √(2πr_*) ≈ 1.90 ≠ A`.
- **Remark 33.3**: Serra's Open Problem 2, the expansion (199) of
  `W(n+1)/W(n)` in pure inverse powers with `O(n^{−p−1})` remainder, holds for
  `p = 1` (with `a_1 = r_*/2`) and fails for every `p ≥ 2`.
- **Remarks 11.3, 23.3, 34.3**: the Lambert centres are the large root of
  `p0:thm:lambert-core` of the transseries volume (`a = λ`, `b = −1/2`); the
  ceiling brackets are of the kind in the separation condition of
  `p0:thm:staircase`; Theorem 34.1 with `M = 1` implies Theorem 11.2 and with
  `M = 2` implies Theorem 23.1 (explicit centre comparison). The centres with
  `M ≥ 2` have coefficients polynomial in `log x`: `f_M(Z) = L_ε` is of the type
  of the volume's formal template `plt:thm:lw-template` (data
  `(λ, −1/2, −log A, −Σ_{j≤M} 𝓛_j(log Z) Z^{−j})`), which expands formally
  about `(L_ε + log A)/λ`; Section 34 centres at the Lambert root and proves an
  analytic bracket, so it extends the volume's results rather than
  instantiating one.
- Section 38, question 2: Serra's suggested approach calls his inequality
  (198) equivalent to log-convexity; it is equivalent to strict
  log-concavity.
- Part III, note after (30.6), the definition of `S_A`: the identity `S_A = Σ_i (q_i W_i R^{i+1} − 1)`,
  `q_i = (1/i!) ∫_i^{i+1} s^i e^{−s} ds`.

## What the report does not claim

From the manuscripts, kept: no certification of the OEIS digits or of any
digit beyond `527/1000 < r_* < 79/125`; no efficiency or complexity bound for
the computability theorems and no executed rate-enclosure iteration; no
all-index monotonicity of the ratios or effective onset; no effective
remainder constants, onsets or threshold certificates (the inverse brackets are
existence statements, and an arbitrarily small error can change a ceiling); no
decimals of `B_2`, `B_3`; "all orders" means every fixed finite truncation with
order-dependent constants, not a convergent series, an exponentially small
transseries or analytic continuation; the Newton statement is exact-real, not
floating-point; no optimality of the policy and no result for other policies;
the companions check finite algebra and the finite certificate, not the
analytic proofs; the source comparison is "relative to the inspected source",
without a universal priority claim; Report 145's Richardson criticism does not
say that Serra's digits are wrong. From the write: the numerical observations
below are uncertified; nothing here decides whether Serra's numerical digits
are correct.

## Further questions, and the standing rule

Section 38 collects eight open questions with sources and status
(Vladimir's standing rule of 4 October 2026): effective constants (and
certified `B_2`); strict decrease of `W_{n+1}/W_n` at every index (Serra's Open
Problem 1); exact log degrees of `P_j`; growth with the order and a
transseries; practical certified digits; numerical threshold certificates;
other policies and optimality; and **whether `S_A = 1/12`**. Answered inside
the merge and marked by dated notes: Report 144's "pointwise corrections and
logarithms" (Thms 14.1, 26.1), Report 145's "full logarithmic expansion" (Thm
26.1) and first "finer ratio term" (Cor. 33.1), and the eventual monotonicity
of the ratios (Cor. 21.7).

`S_A` (Report 146's constant `Σ_i (b_i x_i − 1)`, (30.6) here) is not given a value by
any Part. The placement dossier found it equal to `1/12` to about 8 digits in
float64. The write computed `x_0, …, x_4000` from the exact kernel
factorization (24-point Gauss–Legendre for each kernel integral, fixed point
with resolution `2^{−200}`, the 18-digit OEIS `r_*`; the exact `W_2, …, W_5`
are reproduced to `10^{−59}`) and fitted the partial sums with four tail orders
(`(log N)^k/N^{j−1}`, `2 ≤ j ≤ 5`; this README first said "five") and a term
for the error in `r_*`: `S_A − 1/12 = −1.9·10^{−19}`
(`600 ≤ N ≤ 4000`), at most `3.8·10^{−18}` over the other windows (with three
tail orders, `2 ≤ j ≤ 4`, at most `4·10^{−14}`); the fitted
`log N/N` coefficient is `7/540` to 12 digits. The independent check below
reproduced these values from its own data and, with five tail orders, found
`|S_A − 1/12| < 10^{−23}`. A fit of `log x_n` confirms the
third-order prediction `5/504` for the `log n/n³` coefficient and the
cancellation of `(log n)²/n³` (about `2·10^{−12}`), and gives
`B_2 ≈ −0.0573920672`, and `ρ_0 > ρ_1 > … > ρ_3999`. Uncertified. If
`S_A = 1/12`, the third-order log coefficients are `199/15120` (for `x_n`) and
`101/15120` (for `W_n/(A√n r_*^n)`).

Refuted (external, with proofs in the article): Serra's prefactor `√(2π)` and
its approach from below (Remark 10.2); his integral equation (200) under the
profile reading (Proposition 10.3); his expansion (199) for `p ≥ 2` (Remark
33.3); his "log-convexity" reading of (198) (Section 38). No claim of the three
manuscripts was found to be wrong.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`0480c6184`) reread every write addition
against Serra's version-1 PDF (rendered pages 1, 8, 24, 48–50, 69–70, not only
the text dump): Remark 10.2, Proposition 10.3, Remark 33.3, the (198) reading
of Section 38, Remarks 11.3, 23.3, 34.3 and the implications between the
inverse theorems, the note after Theorem 22.1, the identity
`S_A = Σ (q_i W_i R^{i+1} − 1)`, every number of Section 38, and the merge
(offsets 0/13/25, all 103/132/120 delivered labels, no delivered sentence
dropped). It found every Serra citation accurate, every correction of Serra
valid, no mathematical error in anything the write added, and the merge
faithful. Five wordings were corrected, each with a dated note keeping the
first wording; the record is an unlabelled dated paragraph at the end of
Section 38, with a pointer in the front matter:

- Remark 10.2 (fairness): Serra's Proposition 6.17 is a correct formal
  computation for his (140); what fails is (140) as a model of (47). The
  undefined `C_eff(n)` is read as `W(n)/(√n r_∞^n)`. A note adds that
  `W_n/(√n r_*^n)` decreases strictly for `1 ≤ n ≤ 4000`, from 1.7377 to
  1.442585, with `n(W_n/(A√n r_*^n) − 1) = 0.24996` at `n = 4000` (uncertified).
- Proposition 10.3: `A√t r_*^t` is Serra's Step-2 ansatz *with the true
  amplitude*, not "Serra's profile" (his carries `√(2π)`); a note gives the
  general limit `1 − C²/(2πr_*)`, which is `1 − 1/r_* ≈ −0.738` for Serra's `C`.
- Remark 33.3: the proof now identifies `r_∞ = r_*` before comparing
  coefficients (a missing step).
- Front matter (neighbours paragraph, merge decisions) and Remark 34.3: the
  inverse theorems "use the mechanics of" / are "related to" the transseries
  volume, not "instances" of it (the paragraph also said the `M ≥ 2` centres are
  not instances); the comparison with `plt:thm:lw-template`, which the write
  had missed, is added, and the label joins the `tsvol` bibliography entry.
- Section 38, question 8: the fit with `2 ≤ j ≤ 4` has three tail orders, not
  four; the note adds `|S_A − 1/12| < 10^{−23}` with five.

The tests, none of which used the delivered or the write's programs: exact
`W_n` for `n ≤ 120` from the definition (`n^n Q_{n,k}` as an integer binomial
sum); `W_n` for `n ≤ 4000` to about 70 digits by a different route
(`Q_{n,k} = (n−1)!/n^{n−1} ∫_0^1 φ_i(s) φ_j(1−s) ds`, `φ_i(s) = (i+s)^i/i!`,
own Gauss–Legendre nodes, 30 and 40 of them, fixed point `2^{−240}`, no value
of `r_*` injected; relative agreement `3.4·10^{−70}` with the exact values and
`4.2·10^{−69}` between node counts); from these its own fit
`r_* = 0.575472381511152252066…`, the coefficients `−1/4`, `−7/540`,
`B_2 = −0.05739206722949`, `5/504` for `log n/n³` and about `10^{−15}` for
`(log n)²/n³`, `ρ_0 > … > ρ_3999`, and the `S_A` fits with three, four and
five tail orders; the third-order rationals checked exactly. The rate-bracket
certificate was not rerun. This was a careful reading with numerical tests, not
a formal verification.

## Relation to neighbouring reports

No other report in the repository treats A398540, the placement game,
Serra's manuscript or this recurrence (searched 5 October 2026); the other
reports placed in batch 105 (`a217057-unique-pattern-occurrences`,
`a224182-unique-1432-order`, `a292692-weighted-dyck-newton-diagonal`) treat
other sequences. The inverse theorems use the mechanics of the transseries
volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
(`p0:thm:lambert-core`, `p0:def:three-inverses`, `p0:thm:staircase`,
`p0:cor:forward-to-inverse`), which the manuscripts neither cite nor need; the
centres with `M ≥ 2` carry polynomials in `log x` and are not instances of
`p0:thm:lambert-centered` and `p0:thm:flattening` (constant coefficients).
The volume's formal template `plt:thm:lw-template` does admit coefficients
polynomial in `log Z`, but it expands formally in the flattened chart, whereas
Section 34 centres at the Lambert root and proves an analytic bracket; so Part
III extends the volume's results rather than instantiating one. (This
paragraph first called the inverse theorems "instances of the transseries
volume"; corrected after the independent check above.) No reciprocal note is
proposed for the volume.

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository mentions the
placement game or A398540 (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (28 shipped files checked against the
  pristine extraction at the write: 0 differences; `article.tex` and this
  README then replaced the two staged base files). Only names changed (tables
  at the end).
- The delivered code and markdown use delivery paths, shipped under other
  names or not at all: `144-leading-companion-README.md` names
  `fixtures/rate_certificate.json`; `146-allorders-SOURCES.md` and
  `146-allorders-companion-README.md` name `foundation/Report144.*`,
  `foundation/Report145.*` and `SHA256SUMS` (not shipped); the build scripts
  `code/14x-*-build_pdf.py`, `code/14x-*-build_archive.py` and
  `code/144-leading-bundle.py` name `Report14x.tex`, `Report14x.pdf`,
  `companion/…`, `foundation/…`, `manifest.json`/`SHA256SUMS` and the Debian
  TeX directories `/usr/share/texlive/texmf-dist`, `/usr/share/texmf`; they
  build the delivered manuscripts, not this `article.tex`, and do not run in
  this layout.
- The companions locate their files next to themselves (`HERE/"fixtures"/…`,
  `fixture.json` beside `checks.py`, `verify_certificate.py` beside
  `test_verifier.py`), so the test suites need the delivered layout (below).
- `code/146-allorders-companion-test_checks.py` uses `/tmp/escape.json` as a
  path that must be rejected; nothing is written there.
- Report 144's delivered README (not shipped) says its adversarial suite has
  130 tests; on Windows 120 run, because the POSIX output-containment tests are
  reported as an unsupported platform that fails closed, as
  `144-leading-companion-README.md` describes. `145-logcorr-companion-README.md`
  says each suite passes 1,142 cases (on POSIX).
- Part III's text describes "unchanged PDF and LaTeX files" of Reports 144 and
  145 accompanying it, and Part II likewise for Report 144: in this report
  those are Parts I and II, and the copies are not shipped.

## Rerunning the checks

Read-only reruns with the shipped names work on any platform for the two
verifiers that accept a fixture path; run them on a copy, in a scratch
directory:

```
cp -r code data <scratch>/ && cd <scratch>
python3 -I code/144-leading-companion-verify_certificate.py --fixture "$PWD/data/144-leading-companion-fixtures-rate_certificate.json"
python3 -I code/145-logcorr-companion-checks.py --fixture data/145-logcorr-companion-fixture.json > receipt145.json
```

The first prints a JSON summary with `"all_mandatory_checks_passed": true`
and the bounds `527/1000`, `79/125` (the fixture path must be absolute); the
second's output is JSON-equal to `data/145-logcorr-companion-receipt.json`. Both
were rerun this way at the write (5 October 2026, Python 3.14, Windows; about
11 s and 1 s). Add `-O` for the optimized mode.

The test suites and Report 146's checker need the delivered layout and POSIX
file operations (Report 146's `checks.py` refuses to run without POSIX
no-follow support, even to read its fixture). Recreate the layout from the
arrival commit on a POSIX system:

```
git show 60f54ea06:docs/incoming/A398540_Placement_Game_Leading_Asymptotics_and_Inverse_Source.zip > s144.zip
git show 60f54ea06:docs/incoming/A398540_Placement_Game_Logarithmic_Corrections_and_Inverse_Source.zip > s145.zip
git show 60f54ea06:docs/incoming/A398540_All_Orders_Logarithmic_Asymptotics_and_Inverses_Source.zip > s146.zip
mkdir r144 r145 r146 && unzip -q s144.zip -d r144 && unzip -q s145.zip -d r145 && unzip -q s146.zip -d r146
(cd r144/Report144/companion && python3 -I verify_certificate.py && python3 -I test_verifier.py)
(cd r145/Report145 && sha256sum -c SHA256SUMS && python3 -I companion/checks.py && python3 -I companion/test_checks.py)
(cd r146/Report146 && sha256sum -c SHA256SUMS && python3 -I companion/checks.py && python3 -I companion/test_checks.py)
```

each also with `-I -O`. Python 3.9 or later and its standard library suffice.
Rebuilding the delivered PDFs byte for byte needs the recorded TeX Live
(`data/146-allorders-toolchain.json`).

Results at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-105 dossier): Report 144's verifier passes in both modes
(17 s, 27 s; vector digest `f6910ee2…` as in its PROVENANCE) and its fixture
regenerates byte for byte; its tests pass (120 on Windows, 1 min 50 s per
mode). Report 145's `checks.py` passes in both modes; its `test_checks.py`
stops at the first POSIX output guard, after 1,126 of its 1,142 cases passed
(the other 16 are POSIX-only). Report 146's `checks.py` refuses on Windows; with
a read-only shim replacing its POSIX file reader it reproduces
`receipt.json` byte for byte; its `test_checks.py` passes 15 of 18 tests (the
three failures are POSIX no-follow and `os.mkfifo` tests). The shims are not
shipped. No mathematical check failed.

## Rights

Repository contents are MIT-0. Serra's manuscript (CC BY 4.0 according to its
Zenodo record) is cited, quoted briefly and not redistributed. No OEIS data
file is shipped: the Report 144 fixture holds `W_0, …, W_100` computed from the
recurrence; the OEIS digits and amplitude quoted in the article's notes are
credited to OEIS A398540 (Serra; Kotěšovec), whose data are available under
CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). Robbins (1955) is
credited for the factorial bounds. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 81 pages, no errors, no warnings, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull or underfull
boxes. The three delivered `.tex` files compile with MiKTeX pdfLaTeX to 21, 21
and 22 pages.

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 83 pages (81 before; the record and the notes add two),
no errors, no warnings, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull or underfull boxes; all 385
labels keep their numbers (`.aux` compared with a build of the committed text,
which reproduced the committed PDF byte for byte; page numbers move by at most
two).

## Delivered path → shipped path

Report 144 (`144-leading-`):

| Delivered | Shipped |
|---|---|
| `Report144.tex` | not shipped; printed as Part I of `article.tex` |
| `SOURCES.md` | `144-leading-SOURCES.md` |
| `companion/README.md`, `companion/SCHEMA.md`, `companion/PROVENANCE.md` | `144-leading-companion-<name>` |
| `bundle.py` | `code/144-leading-bundle.py` |
| `companion/verify_certificate.py`, `companion/test_verifier.py` | `code/144-leading-companion-<name>` |
| `companion/fixtures/rate_certificate.json` | `data/144-leading-companion-fixtures-rate_certificate.json` |
| `README.md`, `Report144.pdf`, `manifest.json` | not shipped |

Report 145 (`145-logcorr-`):

| Delivered | Shipped |
|---|---|
| `Report145.tex` | not shipped; printed as Part II |
| `companion/README.md` | `145-logcorr-companion-README.md` |
| `build_pdf.py`, `build_archive.py` | `code/145-logcorr-<name>` |
| `companion/checks.py`, `companion/test_checks.py` | `code/145-logcorr-companion-<name>` |
| `companion/fixture.json`, `receipt.json`, `tests-normal.json`, `tests-optimized.json` | `data/145-logcorr-companion-<name>` |
| `toolchain.json` | byte copy of Report 146's; not shipped again |
| `foundation/Report144.tex`, `foundation/Report144.pdf` | byte copies of Report 144's delivery; not shipped |
| `README.md`, `Report145.pdf`, `SHA256SUMS` | not shipped |

Report 146 (`146-allorders-`):

| Delivered | Shipped |
|---|---|
| `Report146.tex` | `article.tex` (Part III) |
| `README.md` | replaced by this guide |
| `SOURCES.md` | `146-allorders-SOURCES.md` |
| `companion/README.md` | `146-allorders-companion-README.md` |
| `build_pdf.py`, `build_archive.py` | `code/146-allorders-<name>` |
| `companion/checks.py`, `companion/test_checks.py` | `code/146-allorders-companion-<name>` |
| `companion/fixture.json`, `receipt.json`, `tests-normal.json`, `tests-optimized.json` | `data/146-allorders-companion-<name>` |
| `toolchain.json` | `data/146-allorders-toolchain.json` |
| `foundation/Report144.{tex,pdf}`, `foundation/Report145.{tex,pdf}` | byte copies of the deliveries; not shipped |
| `Report146.pdf`, `SHA256SUMS` | not shipped |

## Provenance

Three manuscripts (bundle Reports 144, 145, 146) → one report; base 146,
printed as Part III. Arrival `60f54ea06`, placement `e85586b7c`, write batch
105 (5 October 2026). No manuscript pins a ProveIt commit. Report 146 is the
version "corrected in place" before delivery; the earlier version was never
received. Merge choices (dependency order with the base last, embedded copies
printed once, the three openings kept with pointers to Part I's derivation,
superseded theorems kept with notes, the merged bibliography with the
manuscripts' entries for Reports 144 and 145 pointing to Parts I and II) are
listed in the article's front matter, "Provenance and merge decisions". The
write read Serra's version-1 PDF and checked every page and equation number the
Parts cite.
