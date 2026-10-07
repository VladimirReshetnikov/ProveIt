# Labelled Outerplanar Graphs to All Fixed Orders (OEIS A097998, A098000)

**`c_n = A n! ρ⁻ⁿ n^{-5/2} (Σ_{j≤J} d_j(0) n^{-j} + O_J(n^{-J-1}))` and
`g_n = e^ν A n! ρ⁻ⁿ n^{-5/2} (Σ_{j≤J} d_j(1) n^{-j} + O_J(n^{-J-1}))` for every
fixed `J`, uniformly in a complex component marker; four corrections, a
total-variation `O(n⁻²)` shifted-Poisson refinement, a two-ceiling inverse
with a Lambert start; and the correction of a published constant: the
amplitude `h ≈ 0.018216` of Bodirsky–Giménez–Kang–Noy (2007), Theorem 5.1,
is `e^ν A = 0.0080960474…`, the printed value being `(9/4) e^ν A`**

A research article dated 3 October 2026 ("Report 170" of a session bundle),
built from one manuscript. Its author line reads "Report 170" and its PDF
author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 170 (batch 109) | `Labeled_Outerplanar_Graphs_Expansions_and_Inverses_Source.zip` (29 files, no wrapper directory, 553,249 bytes, SHA-256 `bfdcc45dce2d…ee19e154abb6f45`), arrival commit `60f54ea06`; main file `Report170.tex` (921 lines, 15 pp.) | none: the package names no ProveIt commit and no repository path | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository's formal developments concerns graph classes or Lagrange
inversion of block decompositions.

## Trust boundaries

- **What is proved by hand.** Proposition 2.1 (the exact marked identity,
  by Lagrange inversion and one coefficient identity), Theorem 3.1 (the
  exact contour integral (4.1), global dominance (4.2) from the nonnegative
  coefficients of `b`, and a Taylor remainder kept inside the Gaussian
  integral, so there is no logarithmic loss), Theorem 6.1 and Corollary 6.2
  (Cauchy estimates), Theorem 7.1 (Stirling's series and the mean value
  theorem). No proof uses a computation.
- **What rests on computation.** The values `d_2(0)`, `d_3`, `d_4` of the
  table of Section 5 and the field formula (5.5) are outputs of the finite
  rule (3.11), computed by the shipped programs in exact `Q(τ)` arithmetic
  and compared there with an independent formal singular route; `d_1(v)`
  and the shape of `d_2(v)` are also derived by hand.
- **What is diagnostic.** Every decimal, every residual table and the
  inverse diagnostics; the source's decimals are "not certified decimal
  intervals". Every remainder constant and threshold is existential.
- **What is prior.** The block decomposition and exact enumeration
  (Bodirsky–Kang 2006), the leading equivalents and the shifted-Poisson
  component limit (BGKN 2007), the correct analytic amplitude relation
  (Kang's 2007 habilitation thesis, p. 55), and the existence of fixed-order
  expansions (the subcritical framework of Drmota–Fusy–Kang–Kraus–Rué 2011).
  The source's novelty statement is "a source coverage statement, not proof
  of worldwide novelty".

## What it proves

`c_n` and `g_n` count connected and all outerplanar simple graphs on the
label set `[n]`, each edge set once (A097998 for `n ≥ 1`, A098000). With
`b(u) = (1+5u−√(1−6u+u²))/8`, `T = z e^{b(T)}`, `C = ψ(T)`,
`ψ(u) = u − u b(u) + ∫₀ᵘ b`, the saddle `τ b'(τ) = 1`
(`τ = 0.1707649868…`), `ρ = τ e^{−b(τ)}`, `ν = ψ(τ)`,
`A = τ/√(2π κ₂)`, `κ_j = (D^j b)(τ)`. Statement and equation numbers are
the delivered ones.

- **Proposition 2.1 (`lop:prop:marked`)**: `f_n(v)/n! = (v/n²) [u^{n−1}]
  e^{vψ}(1 + v u ψ') e^{n b}` for the component-marked polynomial
  `f_n(v) = n! [zⁿ] e^{vC}`.
- **Theorem 3.1 (`lop:thm:main`)**: for every fixed `J` and compact marker
  set, `f_n(v)/(v e^{vν} A n! ρ⁻ⁿ n^{-5/2}) = Σ_{j≤J} d_j(v) n^{-j} +
  O(n^{-J-1})`, `d_j ∈ Q(τ)[v]` of degree `≤ j`, with the exact Gaussian
  moment generator (3.8) and the finite sum (3.11); (3.9)–(3.10) are the
  cases `v = 0, 1`. Section 4 is its proof.
- **Section 5 (`lop:sec:corrections`)**: `d = d_1(0)` (5.1),
  `d_1(v) = d + 5τv/2` (5.3), `d_2(v)` (5.4), the table of `d_1, …, d_4` at
  `v = 0, 1`, `d` in the basis `1, τ, τ², τ³` (5.5); Section 5.1, a formal
  singular expansion (5.6)–(5.8) as an independent coefficient check.
- **Theorem 6.1 (`lop:thm:TV`)**: `d_TV(L(K_n), L(1 + Poisson(ν + 5τ/(2n)))) =
  O(n⁻²)` for the number `K_n` of components; **Corollary 6.2
  (`lop:cor:moments`)**: mean, variance and `c_n/g_n` to `O(n⁻³)`.
- **Theorem 7.1 (`lop:thm:inverse`)**: for `N(X) = min{n ≥ 1 : a_n ≥ X}`,
  `a_n ∈ {c_n, g_n}`, `⌈r − δ⌉ ≤ N(X) ≤ ⌈r + δ⌉`, `δ = K_m r^{-m-1}/log r`,
  about the root `r = r_m(X)` of the logarithmic model (7.2); the Lambert
  start `x₀ = L/W(L/(eρ))` (7.3) with `r_m − x₀ → 2` (7.4).
- **Section 9 (`lop:sec:sources`)**: BGKN's published amplitude is
  `(9/4) e^ν A` to its printed precision; the introduction's stale values;
  the preprint and Kang's thesis.

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.1 (`lop:rem:oeis`)**: the OEIS entries quoted (next section).
- **Remark 7.2 (`lop:rem:onset`)**: `g_{n+1} > g_n` for every `n ≥ 1` and
  `c_{n+1} > c_n` for every `n ≥ 2` (`g_0 = g_1 = 1`, `c_1 = c_2 = 1`), with
  proof; so the monotonicity onset of Theorem 7.1 is explicit.
- **Remark 7.3 (`lop:rem:transseries`)**: Section 7 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `N(X)` is the staircase of
  `p0:def:three-inverses` (`n_1 = 1` for `g`, `2` for `c`), so
  `p0:thm:staircase`(1) applies. (b) Theorem 7.1 is, **as stated and
  proved, an analogue** of `p0:thm:staircase`(2) (a direct bracket about the
  root of a model that does not interpolate the counts); the write adds a
  **second route**: with the interpolation `log 𝒜 = F_m + Ẽ` (`Ẽ` the
  piecewise-linear interpolation of the integer errors), `|ν_𝒜 − r| ≤ δ`, and
  `p0:thm:staircase`(1) gives Theorem 7.1. (c) **Instance**: the Lambert
  start is `p0:prop:factorial-core` with `κ_vol = 1`,
  `d_vol = −(1 + log ρ)`; its large-`L` expansion is a **formal instance of
  `plt:thm:lw-template`** with data `(1, 1, 0, log(1 − (1 + log ρ)t))` after
  `ξ_vol = log L`, `Z_vol = log x₀`. (d) **Formal instance after `x = x₀(1+E)`**
  of `p0:thm:core-reversion` (`Λ_vol = log(x₀/ρ)`,
  `h_vol(E) = (1+E)log(1+E) − E`), whose first coefficient is the displacement
  in (7.4); only formally, with the source's own remainder. (e) The full
  model equation `F_m(x) = L` is **not shown to be** an instance of
  `plt:thm:lw-template`: in the two charts tested the hypotheses fail
  ((H3): terms `Z e^{−Z}`); the write does not claim that no chart works.
  (f) The reversion (5.6) is ordinary power-series reversion, formally the
  case `μ_vol = 0` of the template.
- **Remark 9.1 (`lop:rem:bgkn`)**: **BGKN's Theorem 5.1 corrected, with
  proof** (next section but one).
- **Remark 9.2 (`lop:rem:versions`)**: the preprint, the EuroComb 2005
  extended abstract, Kang's thesis, and the same factor `9/4` in BGKN's
  Theorem 7.1 (graphs with no `K_{2,3}` minor; an observation).
- Section 1.1 (`lop:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); labels on the ten sections and on
  Section 5.1; notes after the abstract and at the ends of Sections 3, 6, 8
  and 10; Questions 5–7 in Section 10; two bibliography entries (A097999;
  the EuroComb 2005 extended abstract).

## The OEIS entries (Remark 1.1)

Read on 6 October 2026 in the internal format; quoted verbatim.

- **A097998** (revision #12, 12 February 2021): "Number of connected
  outerplanar graphs on n labeled nodes.", offset 0, data
  `1, 1, 1, 4, 37, 602, 14436, …` ("a(0)=1 prepended and terms a(17) and
  beyond from _Andrew Howroyd_, Feb 12 2021"); formula "Recurrence known, see
  Bodirsky and Kang."; Howroyd's PARI program inverts `x/exp(b(x))` and
  integrates, i.e. it is the rooted equation (2.3) with the block function
  (2.1), plus the prepended 1.
- **A098000** (revision #14, 12 February 2021): "Number of outerplanar graphs
  on n labeled nodes.", data `1, 1, 2, 8, 63, 893, 19714, …`; "Exponential
  transform of A097998. - _Andrew Howroyd_, Feb 12 2021".
- **A097999** (revision #42, 30 May 2026): "Number of 2-connected outerplanar
  graphs on n labeled nodes."; its 18 printed terms are
  `(n−1)! [u^{n−1}] b(u)`, `3 ≤ n ≤ 20` (the write's computation).

Neither A097998 nor A098000 states an asymptotic formula. Both b-files
(`0 ≤ n ≤ 200`) fetched on 6 October 2026 are byte-identical to the shipped
fixtures; the write recomputed all 401 terms in exact arithmetic (every
`c_n` from the Lagrange identity (2.4), every `g_n` from `G = e^C`): all
agree. Nothing was submitted to the OEIS.

## The correction of BGKN's Theorem 5.1 (Remark 9.1)

BGKN, *Enumeration and limit laws of series–parallel graphs*, Eur. J.
Combin. 28 (2007) 2091–2105, Theorem 5.1 (p. 2102, read on the rendered
author-hosted page): "The number h_n of outerplanar graphs is asymptotically
h_n ∼ h · n^{−5/2} · ρ^{−n} n! where ρ ≈ 0.13659 and h ≈ 0.018216." Its `h_n`
is `g_n` and its `ρ` is `ρ` (same block function, same quartic, on the same
page).

- **Claim.** `lim g_n/(n^{−5/2} ρ^{−n} n!) = e^ν A =
  0.0080960474760807049962… < 0.0084`. The exponent and the radius are right;
  the printed amplitude is wrong, and equals `(9/4) e^ν A =
  0.0182161068…` to its six decimals (`0.018216/(e^ν A) = 2.24998…`).
- **Proof.** (i) Theorem 3.1 at `J = 0`, `v = 1`. (ii) An elementary bound:
  `b''(u) = (1−6u+u²)^{−3/2}`, so `κ₂ = 1 + τ²(1−6τ+τ²)^{−3/2} > 94.4` from
  `τ ∈ (0.17076, 0.17077)`; hence `A < 0.007012`; and `ν ≤ τ` because
  `0 ≤ ∫₀^τ b ≤ τ b(τ)`; so `e^ν A < 0.00832 < 0.0084 < 0.018216/2`. (iii) An
  enclosure in mpmath interval arithmetic (with a closed-form antiderivative
  of `√(1−6u+u²)`): `e^ν A ∈ [0.00809604747608070499620425650036,
  0.00809604747608070499620425650046]`.
- **Corroboration** (not part of the proof): `g_n/(0.018216 n! ρ⁻ⁿ n^{−5/2})
  = 0.48866, 0.46548, 0.45472, 0.45055` at `n = 30, 60, 120, 200`, falling
  towards `0.44444…`; after the four corrections the relative residual of
  `g_n` is `1.37e−5, 4.13e−7, 1.27e−8, 9.81e−10`.
- **The introduction** (pp. 2092–2093) prints `h_n ∼ h · n^{−3/2} σ^{−n} n!`,
  `ξ = 0.14840` and `e^{−ξ} = 0.86208`: wrong too (no positive `h` fits
  `n^{−3/2}`; the component limit is `1 + Poisson(ν)`,
  `ν = 0.1488867426…`, `e^{−ν} = 0.8616666…`), while BGKN's own Theorem 6.1
  has `0.14889` and `0.86166`.
- **The cause is not established** (Question 5).

Remark 9.2 adds: the preprint arXiv:math/0512435v1 prints `h ≈ 0.017657`
(`2.18094… e^ν A`, also wrong) and, in its Theorem 6.1, the `0.14840` and
`0.86208` that the published introduction keeps; the EuroComb 2005 extended
abstract prints the exponent `−3/2` and no amplitude; Kang's thesis has the
correct relation `α₀ = α₁ e^{C(R)}` (p. 55) but the decimal `0.008095`,
neither the rounding nor the truncation of `0.0080960…` (it is the
truncation of `0.006976 · e^{0.148886} = 0.0080959318…`, the product of its
two printed values; how it arose is not known). **And BGKN's Theorem 7.1**
(graphs with no `K_{2,3}` minor, block function `b + u³/6`) prints
`s ≈ 0.018288`; by the same route the write finds `e^{ν'}A' =
0.0081282385507…`, so `0.018288` is `(9/4) e^{ν'}A' = 0.0182885367…`
truncated, and exact counts of that class to `n = 159` approach
`e^{ν'}A' n! ρ'^{−n} n^{−5/2}` (ratio 1.0175 at `n = 159`). That is an
observation, not a theorem here (Question 6).

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- No worldwide priority; the leading equivalents, the shifted-Poisson limit
  and the general machinery are prior; the source "does not announce a new
  leading constant".
- Fixed order only: no convergence of the formal series; marker uniformity
  on fixed compact sets only, not for markers growing with `n`.
- Decimals are not certified intervals; inverse constants and thresholds are
  existential; Theorem 7.1 is not a certified finite-input algorithm, and
  `N(X) = ⌈r_m(X)⌉` does not follow.
- The formal singular route (Section 5.1) is an independent coefficient
  check, not a second analytic (`Δ`-domain) proof.
- The cause of the BGKN discrepancy is not established; numerical tables and
  finite agreement are diagnostics.

The write adds: its checks are floating, finite or interval computations;
Remark 9.1 corrects a published decimal and finds no error in the exponent or
the radius; Remark 9.2(d) is an observation; Remark 7.3 claims no novelty for
any inversion.

## Further questions

Section 10 of the article (`lop:sec:questions`) keeps the source's four
questions (explicit remainder constants and a certified inverse; growth of
`d_j(v)` in `j`; higher signed corrections to the shifted-Poisson law; joint
edge/component marking) and adds, under Vladimir's standing rule of
4 October 2026:

5. **The cause of BGKN's factor** (`lop:q:cause`): locate the slip that makes
   the printed amplitudes `9/4` times the true ones (Theorems 5.1 and 7.1),
   and decide whether the series–parallel constants `c ≈ 0.0067912`,
   `g ≈ 0.0076388` (Theorem 3.7) are affected. Missing: a recomputation from
   BGKN's implicit equations; the preprint's `0.017657` explained.
6. **Graphs with no `K_{2,3}` minor** (`lop:q:k23`): restate Theorem 3.1 for
   `b + u³/6` (the proof uses only nonnegative coefficients, `b_1 = 1`,
   monotone `u b'(u)` and the saddle inside the disc) to turn Remark 9.2(d)
   into a correction of BGKN's Theorem 7.1.
7. **A second analytic route** (`lop:q:singular`): promote Section 5.1 to a
   proof by `Δ`-continuation and transfer, as the source says one "must
   supply".

A dated note there records that Remark 7.2 makes the monotonicity onset of
Question 1 explicit. **Refuted, with proof (Remarks 9.1, 9.2):** BGKN's
published `h ≈ 0.018216`, its introduction's exponent `n^{−3/2}` and decimals
`0.14840`, `0.86208`, and the preprint's `h ≈ 0.017657`; Kang's `0.008095`
confirmed inaccurate. **Nothing in the source was found to be wrong.** Seven
of its decimals printed with "…" (`ν` and `e^ν A` in Section 3; `a`, `q`,
`q + 5τ²/2`, the connectivity coefficient and `e^{−ν}` in Section 6) are
rounded, not truncated, in their last digit (each within one unit of it);
dated notes at the ends of Sections 3 and 6 give the truncated digits.

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS` 28/28 and
  `companion/results/SHA256SUMS` 5/5. The dossier read the manuscript and the
  published BGKN text and found no error in the manuscript; independently
  (own Schröder/Lagrange route, 50 digits) it found the relative residual of
  `c_n` after four corrections `1.71e−7` at `n = 60`, `5.27e−9` at
  `n = 120`; the four companion computations, run through a Windows driver
  (the delivered `build.py` needs POSIX `O_NOFOLLOW`), reproduced all four
  result files byte for byte in 35 s.
- At the write (6 October 2026; same machine; Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0): every proof rechecked line by line (Section 1.1 lists the
  steps); `τ, ρ, ν, A, e^ν A, κ₂, …, κ₁₄` at 80 digits; (5.1), (5.5), `d_1(v)`,
  `d_2(v)` at `v = 1, 2`, all eight table entries (correctly rounded) from the
  finite sum; the Section 6 constants and the connectivity coefficient as a
  ratio; the truncation status of every "…" decimal; the interval enclosure
  and the hand bound of Remark 9.1; the residuals at `n = 30, 60, 120, 200`
  (`n⁵`-scaled: about 130 for `c_n`, 314 for `g_n`, consistent with an
  `O(n⁻⁵)` remainder at `J = 4`); the 401 b-file terms; A097999's terms; the
  `K_{2,3}`-free constants and counts of Remark 9.2(d). The four companion
  computations rerun from the shipped files (Route B below): byte-identical.
- Sources read by the write: the OEIS entries; BGKN published (pp. 2091–2105,
  rendered pages for Theorems 5.1, 6.1 and the introduction), the preprint
  arXiv:math/0512435v1, the EuroComb 2005 extended abstract (Theorem 3),
  Kang's thesis (pp. 9, 55); the transseries volume (labels named above). Not
  read: Bodirsky–Kang (2006), the subcritical framework, Finch's note, the
  unlabelled study.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
7.3(a)–(b) applies is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean` (a
lemma about an arbitrary monotone function); nothing about `c_n` or `g_n` is.

**The transseries volume.** Remark 7.3: the threshold is a staircase
instance; Theorem 7.1 an analogue of `p0:thm:staircase`(2) as proved, and a
consequence of `p0:thm:staircase`(1) with the write's interpolation; the
Lambert start an instance of `p0:prop:factorial-core` and, formally, of
`plt:thm:lw-template`; the displacement (7.4) a formal instance of
`p0:thm:core-reversion` after `x = x₀(1+E)`.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a005975-interval-graphs`, `a156808-circle-graphs` and
`a123448-permutation-graphs` enumerate other graph classes, unlabelled and
by different methods; no shared result, so no reciprocal note is proposed.

**Stale claims.** Before batch 109 no file of the repository named A097998,
A098000 or A097999, and no report counted outerplanar graphs.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: the two `a` (`√κ₂`, `5τ/2`); `e` (`d_2(0)`
against Euler's number); the four `h` (the analytic factor of `R_3`, the
`v`-coefficient of `d_2`, the inverse displacement, BGKN's amplitude);
`k`, `k_*`; `q`, `Q` (moment constant, finite-sum exponent, comparison PGF,
germ); `S`; `A`, `A_v`, `A_*`; `E`, `𝔼`; `K`, `𝒦`, `K_n`, `K_m`; `C`, `C_j`;
`T`, `T_k`, `t_2`; `W` (the function of Section 5.1 and Lambert's);
`X`, `L`; `r`, `r_m`, `N`; `R`, `R_3`; and the dictionary to BGKN (`σ` in its
introduction, `ξ` for `ν`) and to Kang (`u_1 = τ`, `x_1 = R = γ⁻¹ = ρ`,
`C(R) = ν`, `α₁ = A`, `α₀ = c_1 = e^ν A`). No symbol was renamed; the
volume's colliding letters carry the subscript "vol" in Remark 7.3.

## Labels

Every label carries the prefix `lop:` (none existed in the repository). The
manuscript's 49 labels (`eq:` 44, `thm:` 3, `prop:` 1, `cor:` 1) were
prefixed before anything cited them, and the 37 references to them
(32 `\eqref`, 5 `\ref`) updated. The write added 20: eleven section labels
(`lop:sec:scope`, `identities`, `generator`, `proof`, `corrections`, `formal`,
`components`, `inverse`, `checks`, `sources`, `questions`),
`lop:sec:provenance`, five remarks (`lop:rem:oeis`, `onset`, `transseries`,
`bgkn`, `versions`) and three questions (`lop:q:cause`, `k23`, `singular`).
The report has 69 labels; builds of the delivered text and of this one give
all 49 delivered labels the same numbers (aux files compared). The added
statements are the last of their sections, the added subsection follows the
last delivered text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                     this guide (replaces the delivery README)
article.tex                                   the report (delivered Report170.tex; labels prefixed, [write] additions)
article.pdf                                   compiled report, 24 pages
companion-README.md                           the delivered companion guide (delivered companion/README.md)
code/companion-build.py                       builds the four result files; POSIX-only output I/O (delivered companion/build.py)
code/companion-common.py                      JSON and fixture-hash helpers (delivered companion/)
code/companion-exact_counts.py                exact counts, literal enumeration n <= 5, b-file checks (delivered companion/)
code/companion-exact_algebra.py               exact Q(tau) certificates for d_0..d_4 (delivered companion/)
code/companion-independent_series.py          independent formal singular route (delivered companion/)
code/companion-diagnostics.py                 finite moment, remainder and inverse diagnostics (delivered companion/)
code/companion-tests.py                       regression and guard tests; POSIX-only (delivered companion/)
code/release_tools.py                         exclusive, no-follow file I/O (delivered at the root; byte-identical to companion/release_tools.py)
code/build_pdf.py                             deterministic TeX Live PDF builder (delivered at the root)
code/make_zip.py                              deterministic archive builder from SHA256SUMS (delivered at the root)
data/SOURCE_PROVENANCE.json                   sources, versions and hashes of the saved sources (delivered at the root)
data/companion-requirements.txt               sympy==1.14.0, mpmath==1.3.0 (delivered companion/requirements.txt)
data/companion-fixtures-b097998.txt           OEIS A097998 b-file, n = 0..200 (delivered companion/fixtures/)
data/companion-fixtures-b098000.txt           OEIS A098000 b-file, n = 0..200 (same)
data/companion-fixtures-exact_certificates.json  frozen exact certificates (same)
data/companion-fixtures-high_precision.json   100-digit regression values (same)
data/companion-fixtures-provenance.json       fixture sources and SHA-256 values (same)
data/companion-results-exact_counts.json      recorded result (delivered companion/results/)
data/companion-results-exact_algebra.json     recorded result (same)
data/companion-results-independent_series.json  recorded result (same)
data/companion-results-finite_diagnostics.json  recorded result (same)
data/companion-results-manifest.json          input and result hashes, runtime versions (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `data/companion-requirements.txt` is
byte-identical to a generic pin file already in the repository (blob
`de9542d36`); it is shipped here so that this package reruns on its own.

**Not shipped**, recoverable from the arrival commit (next section):
`Report170.pdf` (the delivered 15-page PDF, 398,416 bytes); the checksum
manifests `SHA256SUMS` (2,590 bytes, 28 entries) and
`companion/results/SHA256SUMS` (429 bytes, 5 entries), verified at placement
(repository policy ships no checksum manifests); the second copy
`companion/release_tools.py` (byte-identical to `code/release_tools.py`);
and the delivery `README.md` (3,607 bytes), staged at placement and replaced
by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-README.md` ("From this directory", `build.py`, `tests.py`,
`requirements.txt`, `fixtures/`, `results/`, `SHA256SUMS`);
`code/companion-*.py` (import each other by their delivered names, read
`fixtures/` beside themselves, and `companion-build.py` imports
`release_tools` from its own directory); `code/build_pdf.py`
(`Report170.tex`); `code/make_zip.py` (`SHA256SUMS` and the delivered file
set); `data/companion-results-manifest.json` (input hashes keyed by the
delivered names, including `README.md`); `data/SOURCE_PROVENANCE.json`; and
Section 8 of the article ("the companion's README and source provenance
file", "The release manifest"). So no program runs under the shipped names;
use one of the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Labeled_Outerplanar_Graphs_Expansions_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # bfdcc45dce2d79543243451f72b761446aa89726d714eb957ee19e154abb6f45, 553,249 bytes
cd "$T" && unzip -q a.zip && sha256sum -c SHA256SUMS    # 28 entries OK
```

## Rerun the checks (on a scratch copy)

Python 3.11 or later with SymPy 1.14.0 and mpmath 1.3.0 (for example
`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python …`).
Never run anything in the repository.

**Route A, delivered layout, POSIX** (as the companion README gives it),
from `$T/companion`:

```sh
python build.py --output results-new
python -O build.py --output results-new-optimized
diff -r results-new results-new-optimized
python tests.py
(cd results-new && sha256sum -c SHA256SUMS)
```

`build.py` and `tests.py` refuse to run without POSIX `O_NOFOLLOW` and
`O_DIRECTORY` (Windows fails at once). `results-new/manifest.json` records
the Python version, so it differs from the shipped one under another
interpreter.

**Route B, from the shipped files** (tested at the write on Windows):
rebuild the companion layout under the delivered names, then run the four
computations of `build.py` with ordinary file reads and compare.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a097998-outerplanar-graphs
B=$(mktemp -d)/companion; mkdir -p "$B/fixtures" "$B/results"; cd "$B"
for f in build common diagnostics exact_algebra exact_counts independent_series tests; do cp "$R/code/companion-$f.py" "$f.py"; done
cp "$R/code/release_tools.py" .; cp "$R/companion-README.md" README.md; cp "$R/data/companion-requirements.txt" requirements.txt
for f in "$R"/data/companion-fixtures-*; do n=$(basename "$f"); cp "$f" "fixtures/${n#companion-fixtures-}"; done
for f in "$R"/data/companion-results-*; do n=$(basename "$f"); cp "$f" "results/${n#companion-results-}"; done
python -c "from pathlib import Path; from common import canonical_json, validate_fixtures; import exact_counts as c, exact_algebra as a, independent_series as i, diagnostics as d; validate_fixtures(); k = c.run(200); g = a.run(); r = {'exact_counts.json': k, 'exact_algebra.json': g, 'independent_series.json': i.run(g), 'finite_diagnostics.json': d.run(k, g)}; [print(n, canonical_json(v) == Path('results', n).read_bytes()) for n, v in r.items()]"
```

At the write all 15 input hashes recorded in `results/manifest.json` matched
this layout, and the four lines printed `True` (byte-identical results) in
about 11 s. On a POSIX host Route A also runs in this layout (the checksum
manifest `results/SHA256SUMS` is then missing; take it from the archive).
Use `py` where `python` is not on the path. The PDF and archive builders
(POSIX, TeX Live) were not run.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, array, microtype, longtable, hyperref, enumitem); the bibliography
is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 24
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 15 pages). The
article keeps the delivered preamble lines that suppress PDF dates and
trailer identifiers; the delivered byte-identity claims apply to
`Report170.tex` under the delivering toolchain (pdfTeX, TeX Live 2025/dev),
not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the release ("the
PDF, editable LaTeX source, and reproducible exact-code companion for
connected labeled outerplanar graphs (OEIS A097998) and all labeled
outerplanar graphs (A098000)"); stated the conventions (abstract simple
graphs on a fixed label set, `c_0 = 0` in the EGF although the b-file
prepends 1, `K2` included as a block); listed the contents; said that "The
leading count equivalents, limiting shifted-Poisson component law, and
general expansion machinery are established prior results. No
worldwide-priority claim is made."; that numerical residual tables "are
diagnostics, not proofs of asymptotic convergence or certified decimal
intervals" and the inverse "is not a certified finite-input inverse
algorithm"; gave the POSIX PDF and archive rebuild commands (new output
directories only, no overwriting); and, under "Source normalization", that
"The published BGKN amplitude decimal is inconsistent with its defining
generating functions; it agrees to printed precision with 9/4 times the
amplitude computed here. The origin is not established." and that Kang's
thesis has the correct analytic normalization with an inaccurate decimal
`0.008095`. "No source PDFs are redistributed."

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A097998, A098000 and A097999, and the shipped fixtures are the OEIS
b-files of A097998 and A098000 (Andrew Howroyd); OEIS content is published
by The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE),
and that content remains under that licence. Short quotations of BGKN, its
preprint and Kang's thesis are for correction and attribution. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A097998, A098000; Bodirsky–Kang,
  CPC 15 (2006); BGKN, Eur. J. Combin. 28 (2007) and arXiv:math/0512435;
  Kang, habilitation thesis (2007); Drmota–Fusy–Kang–Kraus–Rué, SIAM J.
  Discrete Math. 25 (2011); Finch, *Planar graph growth constants*;
  Bodirsky–Fusy–Kang–Vigerske (unlabelled). Added by the write: OEIS
  A097999; the EuroComb 2005 extended abstract of BGKN.
- Batch 109 of `docs/incoming`, bundle Report 170; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report170.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
