# All Fixed Order Asymptotics for Square Contingency Tables (OEIS A110058)

**`log(a_n/L_n) = Σ_{j≤K} C_j n^{−j} + O_K(n^{−K−1})` for every fixed `K`,
with `C_1 = −3/2`, `C_2 = 223/32`; coefficient polynomials in `1/[λ(1+λ)]`
for densities in a compact interval; the Canfield–McKay correction
`Δ(n,s;n,s) = (67/6 + 5/(3u))/n + O(n^{−2})`, which proves their conjectured
`0 < Δ < 2` in one regime (square, compact positive density, `n` large),
not the conjecture; and a two-ceiling inverse**

A research article ("Report 236" of a session bundle), built from one
manuscript dated 5 October 2026. Its author line and PDF author field read
"Report 236": it names no person, tool or addressee. The phrase "private
review" occurs in the package only in sentences saying that such material is
not included (Section 10 of the article, `SOURCES.md`, and the delivery
README). The delivered README used generic sandbox example paths for its
build commands; they are not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 236 (batch 108) | `Report236.zip` (35 files in a wrapper directory `Report236/`, 669,911 bytes, SHA-256 `1b73cd6b…5b132059`), arrival commit `60f54ea06`; main file `article.tex` with 12 files `sections/*.tex` (980 lines, 24 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes contingency tables or the Canfield–McKay integral. No
proof uses a floating-point computation.

## The correction-factor conjecture: what is claimed and what is proved

Canfield and McKay (arXiv:math/0703600v2, p. 4), verbatim: "Conjecture 1.
Consider a 4-tuple of positive integers m, s, n, t such that ms = nt. Define
Δ(m, s; n, t) by" `M(m,s;n,t) = G(m,s;n,t) ((m+1)/m)^{(m−1)/2}
((n+1)/n)^{(n−1)/2} exp(−1/2 + Δ(m,s;n,t)/(m+n))` (their (1.4), `G` Good's
binomial estimate). "Then 0 < Δ(m, s; n, t) < 2." They record it as proved
for `m = n ≤ 9` (exact Ehrhart values), for large `m, n` when
`st = o((mn)^{1/5})` (Greenhill–McKay), and for several thousand tuples with
`m, n ≤ 30`.

The manuscript's abstract claimed that its density extension "proves an
eventual square case of the Canfield--McKay correction-factor conjecture";
its Section 9 was titled "An eventual square case of a correction factor
conjecture". **What is proved** (Corollary 9.1, `sqt:cor:delta`): for every
compact `I ⊂ (0,∞)` there is an `n_0(I)`, not effective, such that
`0 < Δ(n,s;n,s) < 2` for all `n ≥ n_0(I)` and all integers `s` with
`s/n ∈ I`. That settles one regime: square tables, density in a fixed compact
interval, `n` large. It verifies the conjecture at no explicitly named tuple,
says nothing about `m ≠ n`, and leaves square tuples with `10 ≤ n < n_0(I)`,
with `s/n → 0` but `s` not `o(n^{1/5})`, and with `s/n → ∞`. The write
(6 October 2026) narrowed the abstract, the section title and one sentence
accordingly, with the first wordings kept in dated notes and in Remark 9.2
(`sqt:rem:cmregime`). Nothing in the manuscript is false; this was an
overstatement of scope.

**Finite data** (Remark 9.2, from the OEIS counts, 60-digit floating
arithmetic): `Δ(n,n;n,n) = 1, 1.416, 1.291, 1.070, 0.950, 0.869, 0.805,
0.751, 0.704, 0.663, 0.627, 0.594, 0.565` for `n = 1, …, 13`, all in
`(0, 2)`; `nΔ` rises from 4.28 (`n = 4`) to 7.35 (`n = 13`) toward the
predicted 12 (so `Δ` drifts toward `12/n`); Richardson extrapolation of `nΔ`
of order `k` (model `c_0 + c_1/n + … + c_k/n^k` fitted exactly on
`n = 13−k, …, 13`) gives `c_0 ≈ 9.94, 10.98, 11.43, 11.66, 11.78` for
`k = 1, …, 5`. Consistent with the corollary, not a proof, and no bound on
`n_0(I)`.

## Trust boundaries

- **Imported, cited, not reproved.** Canfield–McKay's absolute localization
  (Theorem 3 of arXiv:math/0703600v2) and Isaev's complex cumulant theorem
  (Theorem 1.2 of arXiv:2508.16952v2). The write read both statements and
  checked the specializations: at `m = n`, `s = t` the Canfield–McKay
  integrand of their (2.3) is the article's `𝓕_λ`, their `I_0` of (4.1) is
  the article's `I_{0,λ}`, condition (1.1) reads `3 ≤ a log n` at density
  one and `(2/3)(4 + 1/u) ≤ a log n` in general, and their leading formula
  (1.3) gives the article's `𝒢(n,λ) e^{B_0(u)}` (so `L_n` is theirs).
  Proposition 2.1 states the weaker `O(e^{−c n^η}) I_0` of their
  `O(e^{−n^ε}) I_0`.
- **Uniformity in density** (Theorem 8.1). Canfield–McKay state Theorem 3 for
  `m, n → ∞` along admissible parameters, not uniformly in a parameter
  family; the manuscript asserts the uniform rate `O_I(e^{−c_I n^η})` and
  supports it by its own reading of their proof (`sections/07_density.tex`,
  the paragraph before eq. (8.5): "One can also check uniformity directly in
  their localization proof"). The write adds **Lemma 8.2**
  (`sqt:lem:sequential`, with proof): from the *statement* of their Theorem 3
  alone, read sequentially, by a subsequence argument and the monotonicity of
  their region in `ε`, the minor-arc integral is `o(n^{−p}) I_{0,λ}`
  uniformly on `I` for every `p`; that is all Theorem 8.1 and Corollary 9.1
  use. **What the write found in their proof** (pp. 15–20, Remark 8.3,
  `sqt:rem:uniformity`): it bounds exactly the three pieces the manuscript
  displays; `λ` enters only through `λ/(1+λ)`, `A = O(log n)`,
  `N = ⌈6000(1+λ)⌉`, `δ = 2π/N` and their Lemmas 3 and 4 (Lemma 4 stated
  "uniformly for λ > 0"; both stated with proofs omitted), all bounded above
  and below on a compact `I`. So the manuscript's reading agrees with the
  steps read, but the implied constants are not tracked there, and the
  uniform *rate* remains the manuscript's reading (Question 1).
- **Proved in the article.** The gauge and cutoff reduction, the all-order
  mixed-difference bounds, the connected-diagram power counting, the finite
  coefficient algorithm, the density polynomials, the Stirling comparison
  behind Corollary 9.1 and the inverse theorems.
- **Exact computations** (the package): all 18 connected-Wick Laurent
  polynomials through cost three, an independent formal-factorization check
  of each, `n = 1, 2` Gaussian checks, the density coefficients, the
  Canfield–McKay comparison coefficients, the four reversion cancellations,
  and `a_0, …, a_5`. They verify identities and counts; they certify no
  remainder, uniformity, finite-size inequality, inverse ceiling or priority.

## What it proves

`a_n` counts labelled `n × n` nonnegative integer matrices with every row and
column sum `n` (`a_0 = 1`); `T(n,s)` the same with line sums `s`,
`λ = s/n`, `u = λ(1+λ)`. Statement numbers are the delivered ones.

- **Theorem 1.1 (`sqt:thm:main`)**: with
  `L_n = e^{1/4} 4^{n²}/((4π)^{n−1/2} n^{n−1})` (Canfield–McKay's leading
  term), `log(a_n/L_n)` has a rational inverse-power expansion to every fixed
  order; `C_1 = −3/2`, `C_2 = 223/32`; `a_n/L_n = 1 − 3/(2n) + 259/(32n²) +
  O(n^{−3})`.
- **Theorem 7.1 (`sqt:thm:inverse`)**: `⌈x_−⌉ ≤ ν(Y) ≤ ⌈x_+⌉` with
  `x_± − t_K = O(t_K^{−K−2})`, `ν(Y) = min{n ≥ 1 : a_n ≥ Y}`; plus the
  strict monotonicity `a_{n+1} > a_n`, a four-term logarithmic reversion of
  `t_2` and a finite Newton scheme.
- **Theorem 8.1 (`sqt:thm:density`)**: `log(T(n,s)/𝒢(n,λ)) = B_0(u) +
  Σ_{j≤K} P_j(1/u) n^{−j} + O_{I,K}(n^{−K−1})` uniformly for `s/n` in a
  compact `I`, `B_0 = 1/3 − 1/(6u)`, `P_1 = −3/2`,
  `P_2 = (1171u³ + 165u² + 3u + 1)/(180u³)`.
- **Corollary 9.1 (`sqt:cor:delta`)**: `Δ(n,s;n,s) = (67/6 + 5/(3u))/n +
  O_I(n^{−2})`, hence `0 < Δ < 2` for `n ≥ n_0(I)`; `Δ(n,n;n,n) = 12/n +
  O(n^{−2})`.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 1.2 (`sqt:rem:oeis`)**: the OEIS entry, quoted (next section).
- **Lemma 8.2 (`sqt:lem:sequential`)** and **Remark 8.3
  (`sqt:rem:uniformity`)**: the uniformity in density (above).
- **Remark 9.2 (`sqt:rem:cmregime`)**: the conjecture and the claim, quoted;
  what is proved and what remains; the `Δ` table; and the formal agreement of
  the dense coefficient with Greenhill–McKay's sparse `Δ ~ 5(s+t)/(6st)` as
  `λ → 0` (`5/(3un) ~ 5/(3s)`), which proves nothing about the transition.
- **Remark 7.2 (`sqt:rem:transseries`)**: Section 7 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  `ν(Y)` **is** the integer staircase `N_*` of `p0:def:three-inverses`
  (`A_n = a_n`, `n_1 = 1`; `a_n` is strictly increasing from `n = 1`).
  Theorem 7.1 is **not an instance, only an analogue** of `p0:thm:staircase`
  (no admissible interpolation; the brackets come from two envelopes at the
  integers); no Lambert core (`p0:thm:lambert-core`,
  `p0:prop:factorial-core`) occurs. The **formal part of the four-term reversion
  is an instance of `p0:thm:core-reversion` after a change of variables**:
  `t = 1/r`, `x = r(1+E)`, `R = ℚ[a, a^{−1}, b, ℓ, C_1, C_2]`, `Λ = 2a`,
  `h(u) = au²` (checked in SymPy: its first four coefficients are the
  manuscript's `d, e, f, g`); the analytic remainder is the manuscript's own.
  After `G = √(F_2/a)` it is **also a formal instance of
  `plt:thm:lw-template`** (data `(1, −1/(2a), −b/(2a), B)`, the route of
  `a089479-fixed-permanent-matrices` and `a222959-zero-slope-matrices`); the
  write first said that "the quadratic-logarithmic balance is outside
  `plt:thm:lw-template`", corrected after the independent check below.
- **Section 12 (`sqt:sec:further`)**: the open questions.
- Section 1.1 (`sqt:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions) and the status note after the abstract.

## The OEIS entry

The live entry A110058 (revision #30, 30 May 2026, read 6 October 2026),
"Number of nonnegative integer matrices of order n for which all row and
column sums equal n.", has data through `a(13)`, one link (the Combinatorica
version of Canfield–McKay), and one formula, the only asymptotic statement in
the entry, verbatim:

    log a(n) = 2(log 2)*n^2 - n*(log n) - n*(log 4*Pi) + (log n) + O(1). - _Igor Pak_, May 15 2019

Its main terms are exactly `log L_n − (1/2) log(4π) − 1/4`, so it is
consistent with `a_n ~ L_n`, which identifies the `O(1)` as
`(1/2) log(4π) + 1/4 + o(1) = 1.51551… + o(1)`; Theorem 1.1 expands the
`o(1)` to every fixed order. Nothing is corrected. The "b-file" the
manuscript cites is synthesized by the OEIS from the entry's data
(`n ≤ 13`). **Nothing was submitted to the OEIS.**

## What is not claimed

From the manuscript, kept in the article (collected in Section 1.1):

- No numerical remainder constants or starting indices; a Poincaré expansion
  at each fixed `K`, with no convergence, uniformity in `K`, optimal
  truncation, exponentially small terms, resurgence or Stokes behaviour.
- The leading equivalent is Canfield–McKay's (and within Barvinok–Hartigan's
  smooth-margin theory); Isaev's theorem and the connected-Wick toolkit are
  imported; no new general saddle-point or cumulant method.
- A bounded literature review, "not a worldwide priority certificate";
  Greenhill–McKay's sparse result is the antecedent of `−3/(2n)`; the
  comparison with Barvinok–Hartigan's exponent (eq. (11.1)) "is a
  specialization of their formula, not a correction".
- Inverse constants are existential; `⌈t_K⌉` is not a valid rule; the Newton
  statement is for exact-real iteration.
- No uniformity as the density tends to 0 or ∞; no exact margins at an
  irrational density; the correction-factor corollary has no explicit start
  and does not settle finite sizes, nonsquare tables or degenerating
  densities.
- No monotonicity of the diagnostics; computations are identity checks in a
  fixed validated range (cost ≤ 3); byte-identical PDFs are
  toolchain-specific; the manifest is "not a digital signature"; the
  controls are "not a sandbox".

The write adds: the uniform localization *rate* is the manuscript's reading
of Canfield–McKay's proof; Lemma 8.2 gives the weaker uniform bound that the
proofs use.

## Further questions

Section 12 of the article (`sqt:sec:further`) states every unproved claim as
an open question with its source, sketch and what is missing (Vladimir's
standing rule of 4 October 2026). **No false statement was found in the
manuscript**; the conjecture claim was narrowed, not refuted.

1. **The uniform localization rate** (`sqt:q:uniform`): a version of
   Canfield–McKay's Theorem 3 with constants tracked in `λ` (including their
   Lemmas 3–4, stated with proofs omitted). Lemma 8.2 already gives what the proofs
   need.
2. **The conjecture outside the regime** (`sqt:q:regime`): an effective
   `n_0(I)` (which with case (a) and finite computation would settle
   compact-density squares), the range between `s = o(n^{1/5})` and
   `s/n → 0`, `s/n → ∞`, and nonsquare tables.
3. **Monotonicity** (`sqt:q:monotone`, added by the write): `Δ(n,n;n,n)`
   decreases and `nΔ` increases for `2 ≤ n ≤ 13`; for all `n`?
4. **Sources the write did not read** (`sqt:q:literature`).

The manuscript's own six questions (Section 11.2) stay as printed.

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4,
  SymPy 1.14.0, mpmath 1.3.0): the staged files are byte-identical to the
  archive and `MANIFEST.sha256` verified 34/34. The dossier checked the
  conjecture and condition (1.1) against the Canfield–McKay text, reran the
  package on a copy of the delivered layout (`build.py --verify-only`: 34
  files verified; `connected_wick.py`, `verify_coefficients.py`,
  `count_tables.py` reproduce the receipts after line-ending conversion, in
  1–3 s each; `count_tables` gives `1, 1, 3, 55, 10147, 22069251`;
  `diagnostics.py` reproduces Table 2; `guard_tests.py` stops on Windows at
  its own path guard, "backslash output components are forbidden"; PDF and
  ZIP rebuilds not run), computed `Δ(n,n;n,n)` at `n = 4, 5, 6, 8, 10, 13`,
  and found Richardson extrapolations of the diagnostics `D_1, D_2`
  (`6 ≤ n ≤ 13`) of about −1.47 and 6.5 against −3/2 and 223/32.
- At the write (6 October 2026; same machine): read Canfield–McKay pp. 1–6
  and 15–20, Isaev's Theorem 1.2 and definitions, the OEIS entry and b-file
  (above); rechecked by hand `P_2(1/u) − g_2(u) − 5/6 = 67/12 + 5/(6u)`, the
  expansion of `(n−1)log(1+1/n)`, the two normalization identities of
  Section 8.1 and condition (1.1); computed `Δ(n,n;n,n)` for `1 ≤ n ≤ 13`
  and the Richardson table; verified in SymPy the core-reversion instance of
  Remark 7.2; and reran Route B below (three receipts byte-identical after
  line-ending conversion, diagnostics equal to Table 2).
- Sources not read by the write: Barvinok–Hartigan (beyond the arXiv title
  page of 0910.2477v2), Greenhill–McKay, Isaev–McKay (both), Isaev–McKay–Zhang,
  Zipunnikov–Booth–Yoshida, Aw, Isaev–Makai–McKay. What the article says
  about them is the manuscript's.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`d63de7211`), with its own code, after
  fetching the OEIS entry, its b-file, Canfield–McKay v2 and Isaev v2 again.
  Lemma 8.2 re-read and found to hold; against the rendered preprint, region
  (3.1), Theorem 3, the convention of p. 4 and (4.1) (exactly `I_{0,λ}` at
  `m = n`) are as the lemma uses them, and (1.1) at `m = n` is
  `(2/3)(4 + 1/u)` (SymPy). Every quotation and bound of Remark 8.3 found on
  pp. 15–20; Isaev's Theorem 1.2 and `Δ̄_V(f,X) ≤ Δ_V(f)` as quoted. Remark
  9.2: quotations verbatim, first wordings those of the delivered files; all
  thirteen `Δ` and `nΔ`, the margin 0.5651, the ratios 0.36 and 0.61, both
  monotonicities and the Richardson values reproduced at 80 digits. Remark
  1.2: the entry as quoted, Pak's main terms exactly
  `log L_n − (1/2)log(4π) − 1/4`, `1.515512123…`. Remark 7.2 (1), (3) hold.
  One statement too strong: (2)'s "the leading balance … is not of the
  monomial–logarithmic type of `plt:thm:lw-template`" (after
  `G = √(F_2/a)` the reversion is a formal instance, its solution
  reproducing `d, e, f, g` by SymPy); corrected with a dated note keeping
  the first wording, and the instance added to (3). Archive facts and the
  97/87 label and reference counts confirmed. For the record, the intake's
  `D_1`, `D_2` extrapolations (−1.47, 6.5) match fits of order two or three;
  the exact fit through all of `6 ≤ n ≤ 13` gives −1.4964 and 6.9139. This
  README's count of 150 fontmap notices did not reproduce (684 in rebuilds
  of both texts), corrected below. The check is recorded at the end of
  Section 9.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns contingency tables. Placement in
the collection confers no formal status. The ceiling arithmetic of
`p0:thm:staircase`(2) is formalized as `Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; that
lemma concerns arbitrary reals, not `a_n`.

**The transseries volume.** Remark 7.2: `ν(Y)` is an instance of the
staircase definition, the four-term reversion formally an instance of
`p0:thm:core-reversion` after a change of variables and, after
`G = √(F_2/a)`, of `plt:thm:lw-template`, Theorem 7.1 an analogue of
`p0:thm:staircase` only.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a380592-tied-football-seasons` applies the same Isaev Theorem 1.2 to another
complex Fourier integral (reciprocal note proposed in a separate commit);
`a222959-zero-slope-matrices` (batch 108, Report 194) is another torus
integral with Wick corrections for a different, binary model;
`a007716-bipartite-multigraphs` counts matrices up to row and column
permutation (arbitrary margins); `a260700-parabolic-double-cosets` and
`a008608-tesler-matrices` meet contingency tables (A120733; the
Brändén–Leake–Pak capacity bound) in other models. None treats A110058 or the
Canfield–McKay conjecture.

**Stale claims.** Before batch 108 no file of the repository named A110058
or the conjecture; the manuscript made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `Δ` (Isaev's mixed difference against
Canfield–McKay's correction); `D_k`, `D_K`, `D_1`, `D_2`; `G_n`, `G_Good`,
`𝒢`; `A` (matrix) against `A_λ = u/2`; `T` (whitening map) against `T(n,s)`;
`h` (interaction, gauge coordinate, the volume's `h`); `m`, `L`; `ε` against
`η` (Canfield–McKay's `ε` is the article's `η`); `a`, `b`; `r`; `u`;
`d, e, f, g`; `P_j`, `𝒫`; `ν(Y)`; `κ`. No symbol of the manuscript was
renamed; symbols of the transseries volume carry the subscript "vol" in
Remark 7.2.

## Labels

Every label carries the prefix `sqt:` (none existed in the repository). The
manuscript's 97 labels (`eq:` 76, `sec:` 11, `thm:` 3, `lem:` 2, `prop:` 2,
`tab:` 2, `cor:` 1) were prefixed before anything cited them, and the 87
references to them updated. The write added 11: `sqt:rem:oeis`,
`sqt:sec:provenance`, `sqt:rem:transseries`, `sqt:lem:sequential`,
`sqt:rem:uniformity`, `sqt:rem:cmregime`, `sqt:sec:further`, and the questions
`sqt:q:uniform`, `sqt:q:regime`, `sqt:q:monotone`, `sqt:q:literature`. The
report has 108 labels; builds of the delivered text and of this one give all
97 delivered labels the same numbers (aux files compared). The added
statements are the last of their sections, the added section follows the last
delivered one, and the added displays are unnumbered.

## Files

```text
README.md                         this guide (replaces the delivery README)
article.tex                       the report's main file (delivered; labels prefixed, [write] additions)
sections/01_results.tex           Section 1 and the write's Section 1.1 (provenance, non-claims, notation)
sections/02_imported.tex          Section 2, the two imported theorems
sections/03_gauge.tex             Section 3, exact integral and product cutoff
sections/04_cumulants.tex         Section 4, analytic cumulant reduction
sections/05_diagrams.tex          Section 5, connected contractions and power counting
sections/06_coefficients.tex      Section 6, the two coefficients
sections/07_inverse.tex           Section 7, inversion (and Remark 7.2)
sections/07_density.tex           Section 8, density extension (and Lemma 8.2, Remark 8.3)
sections/07_conjecture.tex        Section 9, the correction factor (and Remark 9.2)
sections/08_computation.tex       Section 10, diagnostics and reproducibility
sections/09_outlook.tex           Section 11, context and questions; Section 12 (the write's)
sections/10_references.tex        bibliography
article.pdf                       compiled report, 31 pages
COMPUTATION.md                    algorithms and scope of the exact computations (delivered at the root)
SOURCES.md                        public sources and attribution scope (delivered at the root)
code/build.py                     read-only verification and disposable-copy PDF/ZIP build (delivered at the root)
code/common.py                    input validation, exclusive output, artifact name (delivered code/)
code/connected_wick.py            connected-Wick Laurent evaluator (delivered code/)
code/count_tables.py              exact table counts, n <= 5 (delivered code/)
code/density_coefficients.py      symbolic density coefficients (delivered code/)
code/diagnostics.py               floating-point D1, D2 diagnostics from an OEIS fixture (delivered code/)
code/formal_factorization.py      independent formal-factorization evaluator (delivered code/)
code/guard_tests.py               input, output, manifest and ZIP guard tests (delivered code/)
code/inverse_reversion.py         formal inverse-reversion check (delivered code/)
code/reproduce_zip.py             actual-ZIP replay (delivered code/)
code/small_gaussian.py            n = 1, 2 Gaussian checks (delivered code/)
code/verify_coefficients.py       the independent checks combined (delivered code/)
data/connected_wick_receipt.json  receipt of connected_wick.py (delivered code/)
data/guard_receipt.json           receipt of guard_tests.py (delivered code/)
data/table_count_receipt.json     receipt of count_tables.py (delivered code/)
data/verification_receipt.json    receipt of verify_coefficients.py (delivered code/)
data/requirements.txt             sympy==1.14.0, mpmath==1.3.0 (delivered at the root)
```

Every file except `README.md`, `article.tex`, `sections/*.tex` and
`article.pdf` is byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report236.pdf` (the delivered 24-page PDF, 473,122 bytes);
`MANIFEST.sha256` (3,011 bytes, 34 entries, verified at placement;
repository policy ships no checksum manifests); and the delivery `README.md`
(10,317 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`code/common.py` sets `ROOT` to the parent of `code/` and reads
`code/connected_wick_receipt.json` there, which is shipped as
`data/connected_wick_receipt.json`, so `verify_coefficients.py` does not run
under the shipped names; `ARTIFACT_STEM = 'Report236'`. `code/build.py`
takes its own directory as the package root and reads `MANIFEST.sha256`
there, with the receipts expected in `code/` and `requirements.txt` at the
root; `reproduce_zip.py` and `guard_tests.py` use the same delivered names
and the manifest. `COMPUTATION.md`
and `SOURCES.md` speak of "this package", the PDF and the manifest. Section
10.2 of the article describes "the companion source archive" with "the PDF"
and "an integrity manifest"; those are in the arrival archive only.
`guard_tests.py` rejects Windows paths ("backslash output components are
forbidden"), and the PDF/ZIP builder needs POSIX and the delivering TeX
toolchain.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report236.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 1b73cd6bd55d1d0a837ec6d8370bf4837a7b816c59bd075d3cd7ed045b132059, 669,911 bytes
cd "$T" && unzip -q a.zip && cd Report236 && sha256sum -c MANIFEST.sha256
```

## Rerun the checks (on a scratch copy)

Python 3 (the delivery's reference is 3.12; the intake used 3.14.4); SymPy
1.14.0 and mpmath 1.3.0 for
`verify_coefficients.py` and `diagnostics.py`. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it, from
`$T/Report236`; on a POSIX host for the guard tests and rebuilds):

```sh
python3 -B build.py --verify-only
python3 -B code/connected_wick.py       # compare with code/connected_wick_receipt.json
python3 -B code/verify_coefficients.py  # compare with code/verification_receipt.json
python3 -B code/count_tables.py         # 1, 1, 3, 55, 10147, 22069251
python3 -B code/guard_tests.py
python3 -B code/diagnostics.py          # Table 2 of the article
python3 -B build.py --output-dir "$(mktemp -d)/build"   # PDF, ZIP, receipts; needs the delivering TeX toolchain for byte identity
```

The intake ran the first four and `diagnostics.py` on Windows (outputs equal
to the receipts after converting CRLF); `guard_tests.py` stops there at its
path guard, and the rebuild and ZIP replay were not run.

**Route B, from the shipped files, any OS** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a110058-square-contingency-tables
B=$(mktemp -d); mkdir "$B/code"; cp "$R"/code/*.py "$B/code/"
cp "$R/data/connected_wick_receipt.json" "$B/code/"
cd "$B"
python3 -B code/connected_wick.py      > cw.json   # = data/connected_wick_receipt.json
python3 -B code/count_tables.py        > tc.json   # = data/table_count_receipt.json
python3 -B code/verify_coefficients.py > vc.json   # = data/verification_receipt.json
python3 -B code/diagnostics.py
```

Use `py` where `python3` is not on the path. On Windows the outputs carry
CRLF line endings and equal the receipts after conversion. Outputs must go to
standard output or to a new file outside the copy (`--output`); the programs
refuse anything else.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr,
hyperref); the bibliography is embedded in `sections/10_references.tex`.

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (also 31 pages at the write; label numbers unchanged,
aux files compared): 31 pages; no errors, no LaTeX or package warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. The delivered preamble's `\pdfmapfile` lines
make pdfTeX print 684 "fontmap entry … already exists, duplicates ignored"
notices (log lines; the write's count of 150 was not reproduced at the
independent check, whose rebuilds of this text and of the delivered one
both give 684, as for the sibling reports of batch 108),
as many as in a build of the delivered text (24 pages, otherwise
clean). The delivered byte-identity claims apply to `Report236.pdf` under
the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) introduced `Report236.pdf` as
the mathematical article and the programs as "reproducible finite algebra
and small-size counting checks", stating that "Computational agreement does
not itself prove asymptotic remainder estimates, localization, inversion
error bounds or originality". It listed the files under their delivery names,
gave the fixed validated range (cost ≤ 3, ≤ 6 vertices, degrees 3–8, total
degree ≤ 18), the requirements (Python 3.12, SymPy 1.14.0, mpmath 1.3.0),
the commands of Route A with `-B` and `-O` variants, the logarithmic
coefficients `1/4 − 3/(2n) + 223/(32n²)` (35/8 from costs one and two, 83/32
from cost three), the density coefficients and "the coefficient
67/6+5/(3u) for the stated Canfield--McKay parameter", the table counts, the
output path rules ("not a sandbox against hostile concurrent path
replacement"), the deterministic build and ZIP conventions (members dated
2026-10-05, `SOURCE_DATE_EPOCH=1791158400`) and the ZIP replay. It said "No
third-party PDF or private review report is included" and that the manifest
"is an integrity record, not a digital signature or a proof of authorship".

## Rights

Repository contents are MIT-0. The article and `code/diagnostics.py` quote OEIS
data and text of A110058 (the counts at `n = 6, 8, 10,
13` in the diagnostics fixture; Pak's formula); OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
those terms remain under that licence. No third-party PDF is shipped.
Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A110058; Canfield–McKay,
  Combinatorica 30 (2010) 655–680 (arXiv:math/0703600v2); Barvinok–Hartigan,
  arXiv:0910.2477v2; Isaev, arXiv:2508.16952v2; Isaev–McKay,
  arXiv:2508.18731v1 and RSA 52 (2018); Isaev–McKay–Zhang, JCTB 172 (2025);
  Greenhill–McKay, Adv. Appl. Math. 41 (2008); Zipunnikov–Booth–Yoshida,
  JCGS 18 (2009); Aw, arXiv:2604.08857v1; Isaev–Makai–McKay,
  arXiv:2502.08046v2. The write added no bibliography entry.
- Batch 108 of `docs/incoming`, bundle Report 236; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `article.tex` and `sections/` are shipped under the
  same names; the delivered programs and data as listed above.
