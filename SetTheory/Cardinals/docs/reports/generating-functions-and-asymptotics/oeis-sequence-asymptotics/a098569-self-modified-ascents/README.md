# Self-Modified Ascent Sequences and Positive-Diagonal Tables (OEIS A098569, A121690, A098568)

**Exact saddle expansions, dimension laws, binary probabilities and
inversion; the row distribution of A098568**

A research article dated 5 October 2026 ("Report 242" of a session bundle),
built from one manuscript. Its title page and PDF metadata name no person
(author "Report 242"). The package carries no "prepared for private review"
line (the intake triage's flag was a false positive: the only hits are
negations, such as "no third-party paper, private review, research
correspondence"), no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 242 (batch 102) | `Report242.zip` (wrapper directory `Report242/`, 31 files, 638,320 bytes, SHA-256 `03471f6a…7204`), arrival commit `60f54ea06`; main file `article.tex` with 12 `\input` files `sections/*.tex` | none: the package names no ProveIt commit, path or report | `6ab1f1979` (batch 102) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs. The exact, symbolic and high-precision
checks corroborate identities, indexing and constants; they are not
interval certificates and certify no asymptotic statement.

## Trust boundaries

- **The exact enumeration is inherited, not re-proved here.** The counts
  `T(N,m) = C(M(m)+N−m−1, N−m)`, `M(m) = m(m+1)/2`, and
  `U(N,m) = C(m(m−1)/2, N−m)`, the word/table bijection, the binary (rigid)
  subclass and the multiplicity substitution `B(z,h) = C(z/(1−z),h)` are
  prior results (Bayoumi–El-Zahar–Khamis 1989, Khamis 2004,
  Bousquet-Mélou–Claesson–Dukes–Kitaev 2010, Dukes–McNamara 2019,
  Cerbai–Claesson–Sagan 2025; also Kube–Ruskey 2005, Bean–Claesson–Ulfarsson
  2017, Chen–Fan–Zhao 2010). The manuscript credits each, and its
  `SOURCES.md` gives page-level readings. **The intake consulted none of
  these papers**; the readings are the source's. Stars and bars makes the
  two counts elementary, and the intake checked them against the OEIS terms.
- **The `N log N` scale is prior.** The leading scale is in the 1989 paper
  (for a larger class); the finer logarithmic expressions are Václav
  Kotěšovec's OEIS postings (A121690's dated 1 July 2025), stated there
  without a cited proof or a relative error.
- **Priority is not established.** The source's literature search was
  bounded; its repository comparison (no duplicate) was true at placement.
- **Constants are non-effective, numerics uncertified.** No `O`-constant or
  threshold is explicit; the floating-point diagnostics are not interval
  arithmetic.

## What it proves

`b_N` counts nonnegative upper-triangular integer tables with positive
diagonal and entry sum `N` (dimension `m` = number of rows), `c_N` their
binary members (unit diagonal, 0/1 entries); `b_0 = c_0 = 1`. **Indexing:**
`b_N = A098569(N−1)` and `c_N = A121690(N−1)` for `N ≥ 1`, and
`A098568(n,k) = T(n+1,k+1)`; for example `b_1..b_9 = 1, 2, 5, 14, 43, 143,
510, 1936, 7775`. Equivalently, `b_N` counts self-modified ascent sequences
of length `N` (dimension = 1 + number of ascents), `c_N` the `d = 1`
self-modified difference ascent sequences. Put `L = log N`. Theorem numbers
follow the section counter.

- **Theorem 2.1 (`pdt:thm:main`), exact saddle expansion:** uniformly for
  real marks `|t| ≤ T`, the marked count `B_N(t) = Σ T(N,m) e^{tm}` has a
  unique dominant saddle `r` of the exact gamma phase in
  `[N/(2L), 4N/L]`, `r = 2N/(L − 2 log L + log 2 + 2 − t + O(log L/L))`, and
  `B_N(t) = e^{f(r)+tr} √(2π/A) (Σ_{ℓ<K} C_ℓ + O(N^{−K}))` for every fixed
  `K`, with explicit Gaussian contractions `C_ℓ`; `C_1 ~ 1/(24N)`,
  `C_2 ~ 1/(1152N²)`. Global exclusion (**Lemma 3.1**, `pdt:lem:global`) and
  a uniform Gaussian lattice transfer (**Lemma 4.1**, `pdt:lem:poisson`).
- **Theorem 5.1 (`pdt:thm:dimension`):** the dimension `D_N` of a random
  table (mark `t`) satisfies a local expansion to `O(N^{−3/2})`, a full-span
  local limit theorem and a CLT; **Proposition 5.2 (`pdt:prop:moments`):**
  corrected mean and variance, `E D_N ~ 2N/log N`,
  `Var D_N ~ 2N/(log N)²`. With `N = n+1` and column index `K_n = D_N − 1`
  this **answers the question of OEIS A098568**, "How do the terms of row k
  tend to be distributed as k grows?" (read on OEIS on 5 October 2026).
- **Theorem 6.1 (`pdt:thm:elementary`):** with `u(u+2)e^u = 2N` and
  `P(u) = u² + 4u + 2`,
  `b_N = √(2/P(u)) exp(N u(u+1)/(u+2) + u/2 + u²/4) (1 + O(L⁴/N))`.
- **Theorem 7.1 (`pdt:thm:binary-all`):** `p_N = c_N/b_N` to every fixed
  order at the denominator saddle, with an explicit coefficient recursion
  `Q_k` (`Q_1`, `Q_2` printed) and the binary saddle shift `s − r ~ log N`.
- **Theorem 8.1 (`pdt:thm:rational`):**
  `p_N = e^{−u²/2−u}(1 + 𝓡(u)/N + O(L⁸/N²))` with
  `𝓡(u) = u(u+2)(u⁴+8u³+22u²+20u+8)/(4P(u)²)`; the carrier of `c_N`
  (signs `−u/2 − u²/4`); a Lambert-W form `p_N ~ exp(2 − 2w² − 2w)`,
  `w = W_0(√(N/2))`, with relative error `O(1/log N)`.
- **Theorems 9.1–9.2 (`pdt:thm:inverse`, `pdt:thm:seeds`):** two-ceiling
  brackets for the thresholds `ν_b(X) = min{n : b_n ≥ X}` and `ν_c(X)`
  around the smooth exact-carrier root and around elementary seeds `z_b`,
  `z_c` with vanishing error; all fixed logarithmic orders of the inverse.
  At `X = b_1000` the seed is `1000.0014…`, whose ceiling `1001` is wrong
  (the threshold is `1000`): no exact-ceiling rule is claimed.
- **Section 10:** the computational checks and their scope.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Proposition 5.3 (`pdt:prop:moderate`), moderate deviations of the
  dimension:** uniformly for `|t| ≤ T` and `|m − r| ≤ r/2`,
  `P_t(D_N = m) = √A φ(z) exp(O(|z|³ N^{−1/2} + N^{−1}))`; hence the relative
  Gaussian law for `|z| = o(N^{1/6})`, which the source asserts after
  Proposition 5.2 in two sentences. Proof from the source's derivative
  bound, curvature scale and exact-shape formula.
- **The note after Theorem 9.2:** the "`+1`" of the source's
  `ν_c − ν_b = v/2 + 1 + O(1)` (eq. 9.16) is absorbed by the `O(1)` (a
  point of wording); the write proves the explicit window
  `v/2 − 2δ < ν_c − ν_b < v/2 + 2 + 2δ`, `δ = Cv³/n_0 → 0`, centred at the
  exact seed gap `z_c − z_b = v/2 + 1`.
- **Remark 2.2 (`pdt:rem:C1sign`), the slow approach of `N C_1` to
  `1/24`:** `N C_1 = −0.0113, −0.0016, 0.0056, 0.0109, 0.0206, 0.0257,
  0.0321` at `N = 10³, 10⁴, 10⁵, 10⁶, 10⁹, 10¹², 10²⁰`. So **`C_1` stays
  negative until `N` is between `10⁴` and `10⁵`** (the change occurs at
  `N = 15,865`): on a 51-point logarithmic grid from 10 to `10⁶` there is one
  sign change, which bisection places between `N = 15,864` and `N = 15,865`
  (40-digit polygamma evaluation, uncertified). The cause:
  `N C_1 = −3/8 + 5/12 + O(1/L)`. (Sharpened after the independent check;
  the remark first said "between `10⁴` and `10⁶`", kept in a dated note.)
- **Remark 8.2 (`pdt:rem:slowbinary`):** the rational correction is
  accurate at practical sizes (ratio to the exact correction `0.989–0.998`
  for `N = 100…8000`), but the scaled limits `1/4` and `−1/2` of eq. (8.3)
  read only `0.145` and `−0.284` at `N = 8000`, and the Lambert form is off
  by a factor `0.50–0.63`.
- Notes at the A098568 question (end of Section 5; at `n = 999` the row has
  mean column `314.606` and variance `36.557`, against the leading forms
  `288.5` and `41.9`), at the condensed steps of Theorems 7.1 and 9.2, and
  the provenance, credits, notation and non-claims of Section 1.4.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`3daaab24e`) found all three results the
write supplied valid — Proposition 5.3, the window of the note after
Theorem 9.2, and Remark 2.2 — with no counterexample and no gap in any proof
chain. Two changes followed: the note before Proposition 5.3 now lists
eq. (2.5) (`pdt:eq:rscale`) among the inputs of the proof, which uses it in
its first sentence; and Remark 2.2's "between `10⁴` and `10⁶`", true but
loose, now reads "between `10⁴` and `10⁵` (the change occurs at
`N = 15,865`)", with a dated note keeping the first wording. The check used
neither the delivered programs nor the write's: its own gamma phase, with
derivatives by the Faà di Bruno formula for a composition with a quadratic
(checked against numerical differentiation to `1e−49`), a sign-checked
bisection saddle on `I_N`, and `C_ℓ` by direct enumeration of the
contraction (2.8). It stress-tested Proposition 5.3 against the exact
probabilities for `t = −1, 0, 1` and `N = 10³, 10⁴, 10⁵`, over all `m` with
`|m − r| ≤ r/2` (up to `|z| ≈ 250`): the error divided by the bound
`|z|³N^{−1/2} + 1/N` is at most `0.31`, worst at `m ≈ r/2` and creeping
towards the leading-order value `4√2 (log 2 − 5/8) ≈ 0.385`. It tested the
window of the note after Theorem 9.2 with exact `b_n`, `c_n` to `n = 600`
(4000 sampled `X`: `ν_c − ν_b − v/2` in `[0.035, 1.764]`, both brackets
held with `C = 1`), rebuilt `N C_1` independently (every table entry, the
grid and the sign change between `N = 15,864` and `15,865`; a 600-point grid
on `[10, 10⁶]` has exactly one sign change), and spot-checked the source:
the `N = 1000` table of Section 10 with its residuals, `b_1..b_9`, the
binomial transform (1.9) for `N ≤ 30`, and the rounding counterexample at
`b_1000`. A side finding: `c_n` increases only weakly
(`c_0 = c_1 = c_2 = 1`), consistent with the source, whose injection gives
`c_{n+1} ≥ c_n`; `b_n` is strictly increasing on `1..600`. Separately, a
parallel check of Report 243's write found that this report's credit to
that report overclaimed (see "Relation to the repository"); it is corrected
with a dated note. This was a careful reading with numerical tests (30- to
60-digit floating point, not interval-certified), not a formal verification
or an external review; the end of Section 11.1 of the article records it in
full.

## What is not claimed

From the source, kept in the article (collected in Section 1.4):

- Exact enumeration, the word/table bridge, the rigid binary subclass and
  the multiplicity substitution are prior; the `N log N` scale is prior, and
  the finer logarithmic expressions are Kotěšovec's OEIS postings. "An
  asymptotic equivalence for a displayed logarithmic expression, by itself,
  does not establish all of its lower-order terms with additive error o(N)."
- Historical `N`-freeness is in the directed covering graph; it must not be
  conflated with induced-subposet `N`-avoidance or the series-parallel
  class, so results are stated in table and word language. The 1989
  asymptotic theorems concern the larger class of covering-graph `N`-free
  posets. Fishburn-matrix results (Hwang–Jin) do not transfer automatically.
- Only `d = 0` and `d = 1` of the self-modified difference ascents.
- Fixed order `K` and bounded real marks only: no convergence as `K → ∞`,
  no uniformity in a growing order, no claim about stationary points
  outside `I_N`.
- `O`-constants and thresholds are non-effective; remainders are not
  differentiable in `t` or `N`; no exact-ceiling rule
  `ν_b(X) = ⌈y_K(X)⌉`; floating point certifies no integer threshold.
- The limits of `C_1`, `C_2` cannot replace the exact coefficients.
- The collision expectations of Section 8.2 are "an interpretation, not a
  proof"; no collision-distribution theorem.
- Numerical diagnostics are finite consistency checks; reproducibility is
  claimed only for the recorded toolchain; the manifest proves integrity,
  not authorship or correctness; the guard tests are not a security proof.
- Bounded source search: no worldwide novelty or priority, no external
  peer review, no formal verification; sources read as web-extracted text,
  not page images. (`SOURCES.md` also notes that a 2004 bibliography gives
  the 1989 paper's pages as 219–232; the correct range is 219–225.)

The write adds: the source's readings of the literature and the priority
statements are not checked by ProveIt; the write's numerical remarks are
uncertified.

## Further questions

Section 11.1 of the article ("Further questions and research",
`pdt:sec:further`) states every unproved claim of the source as an open
question, with its sketch and what is missing (Vladimir's standing rule of
4 October 2026). The intake found **no false claim** in the source; the
one point of wording (eq. 9.16) is explained, not corrected.

1. **Effective constants and certified thresholds** (`pdt:q:effective`;
   source Section 11, item 1), including an interval proof of the sign
   change of `C_1`.
2. **Growing expansion order**, optimal truncation (`pdt:q:order`; item 2).
   Data at `N = 1000`: residuals `−1.13e−5`, `6.07e−10`, `−5.56e−13` after
   `K = 1, 2, 3` terms.
3. **Complex dimension marks** (`pdt:q:complex`; item 3).
4. **The joint collision structure** (`pdt:q:collision`; item 4 and the
   interpretation of Section 8.2).
5. **Other difference parameters** `d ≥ 2` and `d → ∞` (`pdt:q:difference`;
   item 5).
6. **Higher moments and local corrections** (`pdt:q:moments`): asserted
   after Proposition 5.2, only the first two moments are proved.
7. **The smooth elementary carrier** (`pdt:q:smooth`): eq. (9.18) and the
   derivative bounds (9.7), asserted or argued in one sentence in the proof
   of Theorem 9.2.
8. **The remainder of Theorem 7.1** (`pdt:q:binaryremainder`): the "slightly
   weakened Gaussian" step.
9. **Moderate deviations** (`pdt:q:moderate`): resolved at the write by
   Proposition 5.3; listed for the record.
10. **External inputs and priority** (`pdt:q:literature`), including whether
    Kotěšovec's finer logarithmic expressions have a published proof.

The dossier's tags map as U1 → Question 9, U2 → 6, U3 → 7, U4 → 8.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, mpmath 1.3.0,
SymPy 1.14.0):

- At placement, on the extracted archive: `sha256sum -c MANIFEST.sha256`
  30/30 OK; `build.py --verify-only` verified 30 entries;
  `exact_counts.py` (7 s), `algebra_checks.py` (9 s) and
  `saddle_diagnostics.py` (43 s) with `--output`: all three receipts
  byte-identical to the delivered ones.
- At the write, on a copy of the **shipped** files (route B below):
  the same three receipts byte-identical again (4 s, 3 s, 21 s).
- Not run: `guard_tests.py` (POSIX-only; its delivered receipt records 241
  passing cases), `build.py --output-dir` (fails on Windows, see below; its
  PDF check needs the recorded TeX Live), `reproduce_zip.py` (needs the
  build).
- Independent intake scripts: `b_1..b_10`, `c_1..c_10` and the row
  `N = 4` against the fixture and the live A098568; the binomial transform
  for `N ≤ 39`; the carriers of Theorems 6.1 and 8.1 at
  `N = 100…8000`; the `N = 1000` table of Section 10 (saddle, mean,
  variance, `p_N`, residuals); `N C_1` up to `10²⁰`; the seed counterexample
  at `b_1000`; `P_1`. All agree. The saddle equation, endpoint signs,
  `λ_j` asymptotics, `N C_1 → 1/24`, the gaps of Lemma 3.1, the moment
  contractions and `Q_1` were rederived by hand.
- The delivered text builds with MiKTeX pdfLaTeX in 24 pages without
  warnings or bad boxes.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats these tables, and the report's
place in the collection confers no formal status.

**Neighbouring reports** (no shared theorem unless stated):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202059-ascent-100-110-growth`
  (batch-102 sibling, bundle Report 243, written concurrently): bounds
  ascent sequences avoiding 100 by **the same triangular sum** (its `b_n`,
  `b_n = A098569(n−1)`) and proves, in its Section 2 (as delivered,
  Lemma 2.1), `log b_n = n(log n − 2 log log n + log 2 − 1) + O(n log log n/log n)`,
  and the same estimate for the single term `m = ⌊2n/log n⌋` (used in its
  Section 7 for a lower bound), with the comparison phase `H_N` (here
  eq. 3.1) and the same two global gaps `4 log 2 − 2`, `2 − 2 log 2` as
  Lemma 3.1 here. The estimate for `b_n` follows from Theorem 6.1 here; the
  single-term statement does not (a relative asymptotic for the sum says
  nothing about one term away from the saddle), and is instead the display
  after eq. (3.5) (`pdt:eq:fixedalpha`) at `x_* = 2N/L`, in Section 3.
  (Corrected 5 October 2026 after an independent check of Report 243's
  write: this paragraph first said "That estimate follows from Theorem 6.1
  here", describing the lemma by its estimate for `b_n` alone, and
  Section 1.4 said the same; the article keeps its first wording in a dated
  note.) Neither
  report cites the other; a reciprocal note for that report is proposed
  separately. *[Dated note, 7 October 2026: true of the two manuscripts only.
  The reciprocal note was applied in that report's own write (`3ed50db4e`,
  the day of this one): its Remark W2 after Lemma 5.1 and its README's
  relation section cite this report's Theorem 6.1 (`pdt:thm:elementary`) and
  Lemma 3.1 (`pdt:lem:global`), with the correction after its independent
  check (`5ada42e2f`) described above.]*
- `a202058-ascent-000-growth`, `a294220-ascent-multiplicity-caps`,
  `a202061-ascent-120-deficit`, `a202062-ascent-201-enumeration`: other
  ascent-sequence models; `a336070-weak-ascents` (batch-102 sibling): weak
  and difference ascent sequences, not their self-modified tables.

**Stale claims.** The manuscript makes no claim about the repository except
that a bounded comparison found no duplicate, which was true at placement
(before batch 102 no file mentioned A098569, A121690, A098568 or
self-modified ascent sequences). Nothing to correct.

## Notation

The manuscript reuses many letters. A table in Section 1.4 fixes each one,
with tempting false readings: `N`/`n` (size, the A098568 row index
`n = N − 1`, the poset shape "N-free"), `T` (the count `T(N,m)` and the mark
bound `|t| ≤ T`), `H` (`H_N` the comparison phase, `H` the binary penalty,
`H_0`; all three in Section 8), `B` (`B(z,h)`, `B_N(t)`, `B = N − 1`,
`B_0 = −F/2 + 1/u`, `𝓑(s,q)`), `C`/`c` (`C(z,h)`, `c_N`, `C_ℓ`, constants
`C_K`, `C_bad`), `D`/`d` (`D_N`, `D = u + 4 + 2/u`, `D_bad`, `D_K`, the
difference parameter `d`, a degree, `d = −B + Bs + qv`), `E` (expectation and
`E = 2u + 6 − 4/u²`), `F` (`F_K`, `F_0`, `F_−`, `F = (u+1)(u+2)`), `G`
(`G_k`, `G = (u+2)(3u+4)`), `K`/`k` (order, the column index `K_n`; the
off-by-one between Theorems 2.1 and 7.1), `P` (`P(u)`, `P_y(x)`, `P_j(s)`,
`ℙ`), `R` (`R(s,q)`, `R_K`, `𝓡(u)`, the window `R`), `h`/`g`, `u`/`v`/`w`
(`w = W_0(√(N/2))` in Section 8.1 against `w = log Λ` in Section 9.3), `z`,
`s`/`q`, `X`/`Λ`, `ε`. No symbol was renamed. (`U1`–`U4` above are the
intake dossier's tags, not symbols of the article.)

## Labels

Every label carries the prefix `pdt:` ("positive-diagonal tables"; `sma:` is
taken by `a124380-signed-moment-asymptotics`). The manuscript's 126 labels
(`sec:`, `eq:`, `thm:`, `lem:`, `prop:`) were prefixed before anything cited
them, and every reference was updated (90 `\eqref`, 13 `\ref`). The write
added 15: `pdt:sec:provenance`, `pdt:sec:further`, `pdt:rem:C1sign`,
`pdt:rem:slowbinary`, `pdt:prop:moderate`, and the ten questions
`pdt:q:effective`, `pdt:q:order`, `pdt:q:complex`, `pdt:q:collision`,
`pdt:q:difference`, `pdt:q:moments`, `pdt:q:smooth`,
`pdt:q:binaryremainder`, `pdt:q:moderate`, `pdt:q:literature`. The report
has 141 labels; a build of the delivered text and of this one give every
delivered label the same number.

The write also added the `[write]` notes: status and trust boundary (title
page); Section 1.4 (provenance, the question answered, credits, repository,
notation, collected non-claims); Remark 2.2; the note before and
Proposition 5.3 itself; the A098568 note at the end of Section 5; notes
after the proofs of Theorems 7.1 and 9.2; Remark 8.2; the shipped layout and
intake reruns (end of Section 10); and Section 11.1. No statement, proof or
number of the manuscript was changed. After the write, the independent check
of 5 October 2026 added an unlabelled dated paragraph at the end of
Section 11.1, completed the input list of the note before Proposition 5.3,
sharpened Remark 2.2 (dated note there) and corrected the credit to
Report 243 in Section 1.4 (dated note there); no label was added or
renumbered (aux files compared).

## Files

```text
README.md                    this guide (replaces the delivery README)
SOURCES.md                   the source's literature and indexing note (delivered)
COMPUTATION.md               the source's computational supplement (delivered)
article.tex                  the report's main file (delivered; preamble additions, title-page note)
article.pdf                  compiled report, 31 pages
sections/01_models.tex       Section 1 (delivered; labels prefixed, Section 1.4 added)
sections/02_saddle.tex       Section 2 (delivered; labels prefixed, Remark 2.2)
sections/03_localization.tex Section 3 (delivered; labels prefixed)
sections/04_transfer.tex     Section 4 (delivered; labels prefixed)
sections/05_dimension.tex    Section 5 (delivered; labels prefixed, Proposition 5.3, A098568 note)
sections/06_elementary.tex   Section 6 (delivered; labels prefixed)
sections/07_binary.tex       Section 7 (delivered; labels prefixed, note after Theorem 7.1)
sections/08_rational.tex     Section 8 (delivered; labels prefixed, Remark 8.2)
sections/09_inverse.tex      Section 9 (delivered; labels prefixed, note after Theorem 9.2)
sections/10_checks.tex       Section 10 (delivered; labels prefixed, shipped-layout note)
sections/11_outlook.tex      Section 11 (delivered; references prefixed, Section 11.1 added, independent-check note)
sections/12_references.tex   bibliography (delivered, unchanged)
code/algebra_checks.py       symbolic Gaussian-contraction checks (delivered code/)
code/build.py                manifest check, immutable build, deterministic ZIP (delivered at the package root)
code/common.py               shared bounds and output guards (delivered code/)
code/exact_counts.py         exact enumeration checks (delivered code/)
code/guard_tests.py          241 finite guard cases, POSIX-only (delivered code/)
code/reproduce_zip.py        actual-archive replay verifier (delivered code/)
code/saddle_diagnostics.py   90-digit saddle diagnostics (delivered code/)
data/algebra_receipt.json    receipt of algebra_checks.py (delivered code/)
data/count_receipt.json      receipt of exact_counts.py (delivered code/)
data/guard_receipt.json      receipt of guard_tests.py (delivered code/)
data/requirements.txt        pinned Python dependencies (delivered at the package root)
data/saddle_receipt.json     receipt of saddle_diagnostics.py (delivered code/)
data/source_prefixes.json    OEIS fixture: 26 terms of A098569, 25 of A121690 (delivered code/); CC BY-SA 4.0
```

Every file except `README.md`, `article.tex`, `article.pdf` and the
`sections/*.tex` files is byte-identical to the delivery (`12_references.tex`
is too). The `sections/` directory is kept as delivered, since
`article.tex` inputs it (as in the batch-102 sibling
`a202059-ascent-100-110-growth`); inlining it would have gained nothing.

**Not shipped**, all recoverable from the arrival commit's archive (next
section): `Report242.pdf`, the delivered 24-page PDF (414,853 bytes);
`MANIFEST.sha256` (2,620 bytes), a checksum manifest of the other 30
delivered files (repository policy ships no checksum manifests; verified
30/30); and the delivery `README.md` (5,644 bytes), staged at placement and
replaced by this guide (its content is kept under "From the delivery
README" below).

**Delivered text that names the delivery layout or files not shipped.**
`COMPUTATION.md` names `code/source_prefixes.json` (here
`data/source_prefixes.json`), `build.py` at the package root,
`requirements.txt`, the receipts in `code/` and the manifest, and gives
commands run from the package root. `SOURCES.md` is self-contained. Section
10 of the article describes "the accompanying package". In the code,
`common.py` sets `ROOT` to the parent of `code/`; `exact_counts.py` reads
`ROOT/code/source_prefixes.json`; `build.py` takes its own directory as the
package root, requires `MANIFEST.sha256`, `Report242.pdf` and an allowlisted
inventory, compares fresh receipts with `code/*_receipt.json`, and checks
that `article.tex` contains `\providecommand{\ReportNumber}{242}`;
`guard_tests.py` loads `ROOT/build.py` and probes `ROOT/code/*_receipt.json`;
`reproduce_zip.py` compares against the package tree. **In the shipped
layout nothing runs in place** (and the written `article.tex` and
`sections/` no longer match the manifest); use the routes below.

**Third-party data.** `data/source_prefixes.json` (and the OEIS terms in
`data/count_receipt.json`) are from The On-Line Encyclopedia of Integer
Sequences (https://oeis.org/A098569, https://oeis.org/A121690; fetched by
the source from the `oeis/oeisdata` repository). OEIS content is published
by The OEIS Foundation Inc. under the Creative Commons
Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); this file is third-party
data under that licence, not MIT-0 like the rest of the repository.

## Retrieving the delivered PDF and manifest

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report242.zip > "$T/Report242.zip"
sha256sum "$T/Report242.zip"     # 03471f6a5825ce4656d822d8f901f488be748c01414cd8746058f9b23e357204
cd "$T" && unzip -q Report242.zip && cd Report242
sha256sum -c MANIFEST.sha256     # 30 OK
ls -l Report242.pdf              # 414,853 bytes, 24 pages
```

## Rerun the checks (on a scratch copy)

Requirements: Python 3.11 or later, mpmath 1.3.0 and SymPy 1.14.0 (for
example `uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python`).
The programs make no network request. Never run anything in the repository.
Every documented invocation passes `-B -X int_max_str_digits=640`, and
`--output` paths must be new files outside the package.

**Route A, delivered layout** (restore `Report242/` as in the previous
section; POSIX host for the guard suite and the full build):

```sh
cd "$T/Report242"
python3 -B -X int_max_str_digits=640 build.py --verify-only
python3 -B -X int_max_str_digits=640 code/exact_counts.py --output "$T/count.json"
python3 -B -X int_max_str_digits=640 code/algebra_checks.py --output "$T/algebra.json"
python3 -B -X int_max_str_digits=640 code/saddle_diagnostics.py --output "$T/saddle.json"
python3 -B -X int_max_str_digits=640 code/guard_tests.py --output "$T/guard.json"
cmp "$T/count.json" code/count_receipt.json    # likewise algebra, saddle (and guard)
```

The intake found the count, algebra and saddle receipts byte-identical; it
did not run the guard suite (POSIX-only, see the Windows notes).

The full build and replay (delivery README):

```sh
python3 -B -X int_max_str_digits=640 build.py --output-dir "$T/new-build"
python3 -B -X int_max_str_digits=640 code/reproduce_zip.py \
  --archive "$T/new-build/Report242.zip" \
  --original-build-dir "$T/new-build" --output-dir "$T/new-replay"
```

The builder's PDF comparison requires byte-identical pdfTeX output from the
source's recorded TeX Live; another TeX installation fails it without any
mathematical consequence.

**Route B, from the shipped files** (recreate the programs'
neighbourhood; tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a098569-self-modified-ascents
T=$(mktemp -d); mkdir -p "$T/pkg/code" "$T/out"
cp "$R"/code/*.py "$R/data/source_prefixes.json" "$T/pkg/code/"
cd "$T/pkg"
python3 -B -X int_max_str_digits=640 code/exact_counts.py --output "$T/out/count_receipt.json"
python3 -B -X int_max_str_digits=640 code/algebra_checks.py --output "$T/out/algebra_receipt.json"
python3 -B -X int_max_str_digits=640 code/saddle_diagnostics.py --output "$T/out/saddle_receipt.json"
for f in count algebra saddle; do cmp "$T/out/${f}_receipt.json" "$R/data/${f}_receipt.json"; done
```

At the write all three were byte-identical (4 s, 3 s and 21 s). The guard
suite, the builder and the replay verifier need route A.

**Windows notes.**

- `--output` paths must use forward slashes (`C:/Users/…/out.json`):
  `common.py` rejects any path containing a backslash. The receipts are
  written with LF line endings, so they compare byte-for-byte on Windows.
- `guard_tests.py` is POSIX-only: it requires an existing `/tmp` and feeds
  native paths to the backslash guard, so it fails on Windows ("backslash
  output components are forbidden").
- `build.py --output-dir` fails on Windows at its first receipt comparison:
  it captures the children's standard output in text mode, which turns LF
  into CRLF, so the captured receipt differs from the frozen one (it is
  identical after stripping CR). `--verify-only` works.
  `reproduce_zip.py` depends on the build and was not run.

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, lmodern,
microtype, geometry, xcolor, enumitem, fancyhdr, needspace, hyperref, and
longtable for the write's notation table); the bibliography is embedded.
Build in a scratch copy that keeps `sections/`:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX (rebuilt 5 October 2026
after the independent check, with four pdfLaTeX passes; every label keeps
its number): 31 pages; no errors or warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. The delivered
source built the same way gives 24 pages, equally clean. The article keeps
the delivered preamble lines that set the font maps and suppress PDF dates
and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) summarized the package as "a
self-contained mathematical article and reproducible checks" in which "the
exact enumeration and combinatorial bridges are prior work", stressed that
"the current indexing is essential" (`b_N = A098569(N−1)`,
`c_N = A121690(N−1)`, `A098568(n,k) = T(n+1,k+1)`), and listed the results
above. It added that the binary probability's proof "uses a standardized
N^epsilon window so that the tails remain negligible relative to the rare
event; a central limit theorem alone would not establish the result", that
"no unconditional exact-ceiling rule is asserted", and that "complex marks,
growing orders, other difference parameters and full collision-distribution
laws are not proved here". Its instructions, translated to the shipped
names:

- *Contents:* `Report242.pdf` (not shipped), `article.tex` and `sections/`,
  `SOURCES.md`, `COMPUTATION.md`, `code/` (here `code/` and `data/`),
  the four receipts (here `data/`), `build.py` (here `code/build.py`),
  `MANIFEST.sha256` (not shipped) and `requirements.txt` (here `data/`).
  "The archive contains no third-party paper, private review, research
  correspondence, credential, repository history or network dependency.
  No upload, publication or external peer review is implied."
- *Reproduce:* `build.py --verify-only`, `build.py --output-dir`, then
  `code/reproduce_zip.py` with `--archive`, `--original-build-dir` and
  `--output-dir`, from the extracted `Report242/` (here route A). Output
  directories "must be new, outside the sources, with existing parents";
  the optional report-number argument must be 242; "Reproducibility on
  other software versions is not promised."
- *Interpretation:* bounded exact enumeration, symbolic contractions and
  exact-phase numerics; "No coefficient is fitted"; guards stay active
  under `-O`; every Python child disables bytecode and caps decimal
  conversion at 640 digits; "The manifest proves integrity relative to the
  supplied package, not authorship, provenance or mathematical
  correctness."

## Provenance

- Sources cited by the manuscript: Bayoumi, El-Zahar and Khamis, Order 6
  (1989) 219–225; Khamis, Discrete Math. 275 (2004) 165–175;
  Bousquet-Mélou, Claesson, Dukes and Kitaev, JCTA 117 (2010) 884–909;
  Dukes and McNamara, JCTA 167 (2019) 403–430; Cerbai, Claesson and Sagan,
  Adv. Appl. Math. 170 (2025) 102929; Kube and Ruskey, JIS 8 (2005);
  Bean, Claesson and Ulfarsson, JIS 20 (2017); Chen, Fan and Zhao,
  arXiv:1009.4535; Hwang and Jin, JCTA 180 (2021) 105413; OEIS A098569,
  A098568, A121690 (checked 5 October 2026); DLMF §§5.11, 5.15.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 102 of `docs/incoming`, bundle Report 242; arrival `60f54ea06`,
  placement `6ab1f1979`, written 5 October 2026. Single source, so the write
  made no merge choices. The delivered `sections/` layout was kept rather
  than inlined into `article.tex`.
