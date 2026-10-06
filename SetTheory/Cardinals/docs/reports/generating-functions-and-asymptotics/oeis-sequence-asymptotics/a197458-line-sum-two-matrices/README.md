# Binary Matrices with Line Sums at Most Two (OEIS A197458)

**`a_n ~ (n!)² e^{2√(2n)} / (2^{5/4} π n^{3/4})` with an expansion to every
fixed order in `n^{-1/2}` (four corrections explicit, a finite Gaussian-moment
rule for all others), a logarithmic expansion, a Lambert-W real inverse and a
two-ceiling enclosure of the integer threshold; with the write's additions:
the generating function as `e^{x+y−xy}` times the OEIS A062154 formula, the
exactly-two family A001499 inside the same decomposition, fixed offsets
`(n+d)×n`, and an independent Poisson(1) limit for zero rows and zero columns**

A research article ("Report 168" of a session bundle), built from one
manuscript dated 3 October 2026. Its author line reads "Report 168" and its
PDF author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 168 (batch 108) | `Sparse_Binary_Matrices_All_Orders_and_Inverses_Source.zip` (24 files at the archive root, no wrapper directory, 523,157 bytes, SHA-256 `b67e3c4e…32a02a9a0b8`), arrival commit `60f54ea06`; main file `Report168.tex` (879 lines, 15 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes these matrix counts. No proof uses a computation.

## Trust boundaries

- **Exact identities.** The component generating function `F(x,y)`, the
  Bessel diagonal `G(t) = P(t) I₀(√t(2−t)/(1−t))`, the order-two ODE and the
  integer recurrence. The first follows in one line from a formula of the
  OEIS entry A062154 (Remark 2.1 below).
- **Proved by hand, self-contained.** Theorem 1.1, Corollary 1.2 and
  Theorems 7.1 and 7.2, by the source's saddle-point argument: a sectorial
  Bessel expansion with remainder (proved in Lemma 4.1), a whole-circle
  bound, explicit connector estimates and an integrable Taylor remainder. No
  external asymptotic theorem is used beyond Stirling's formula. Every
  remainder constant and onset is existential.
- **Identity checks only.** The ODE ansatz that recovers `c₁, …, c₄` (it
  proves neither the existence of the expansion nor its leading constant),
  and the companion's finite exact checks.
- **The companion** computes `a_n` exactly by five methods (the ODE recurrence
  to `n = 2000` in its tests, a compressed column-degree DP, the rational
  generating function, a labelled column-degree DP and literal masks to
  `n = 4`), compares the 17 OEIS terms, and computes `c₀, …, c₈` by two exact
  routes. It proves nothing asymptotic.

## What it proves

`a_n` counts `n × n` binary matrices with at most two ones in every row and
column, `a₀ = 1`; `b_n = a_n/(n!)²`. Statement numbers are the delivered ones.

- **Theorem 1.1 (`sbm:thm:main`)**: for each `J ≥ 0`,
  `a_n = (n!)² e^{2√(2n)} / (2^{5/4} π n^{3/4}) · (Σ_{j≤J} c_j n^{−j/2} + O_J(n^{−(J+1)/2}))`
  with `c_j ∈ ℚ(√2)`, `c₀ = 1`, `c₁ = −17√2/96`, `c₂ = 6409/9216`,
  `c₃ = −18114133√2/13271040`, `c₄ = 13052721749/2548039680`, and every `c_j`
  given by the Gaussian-moment rule (6.4).
- **Corollary 1.2 (`sbm:cor:log`)**:
  `log a_n = 2n(log n − 1) + 2√(2n) + ¼ log n − ¼ log 2 − 17√2/(96√n) + 319/(384n) + O(n^{−3/2})`,
  and a logarithmic expansion to every fixed order.
- **Lemma 4.1 (`sbm:lem:bessel`)**: the sectorial expansion of `I₀` with
  remainder, proved from the integral representation.
- **Theorem 7.1 (`sbm:thm:smooth-inverse`)**: with `L = log y`,
  `N = L/(2W(L/(2e)))`, `q = log N`, the inverse of the smooth comparison
  `F_J` is `x_J(y) = N − √(2N)/q − 1/8 + log 2/(8q) + 1/q² − 1/q³ + O_J(1/(√N q))`,
  and `x_J(a_n) = n + O_J(n^{−(J+1)/2}/log n)`; a Newton procedure gives
  every further fixed order.
- **Theorem 7.2 (`sbm:thm:integer`)**: for `I(y) = min{n : a_n ≥ y}`,
  `⌈x − K_J e(x)⌉ ≤ I(y) ≤ ⌈x + K_J e(x)⌉` with `x = x_J(y)`,
  `e(x) = x^{−(J+1)/2}/log x`, for `y ≥ Y_J` (existential constants); `a_n`
  is strictly increasing.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 2.1 (`sbm:rem:oeis`)**: the four OEIS entries, quoted (next
  section). (a) `F(x,y) = e^{x+y−xy} F₁₅₄(x,y)`, where `F₁₅₄` is the A062154
  formula: `e^{x+y}` adjoins zero rows and columns and `e^{−xy}` removes the
  components consisting of one entry 2. The same extraction gives A062156 a
  Bessel diagonal, `(1−t)^{−1/2} e^{t/2+t/(1−t)} I₀(t^{3/2}/(1−t))`.
  (b) The exactly-two family A001499 is the cycles-only part of the
  decomposition: `Σ A001499(n) tⁿ/(n!)² = (1−t)^{−1/2} e^{−t/2}`
  (Bricard's formula in the entry), so `P(t)` is that times `e^{t/(1−t)}`;
  an elementary dominated-convergence proof gives
  `A001499(n)/(n!)² ~ e^{−1/2}/√(πn)`, i.e. Knuth's equivalent in the entry,
  and with Theorem 1.1
  `a_n / A001499(n) ~ e^{1/2} e^{2√(2n)} / (2^{5/4} √π n^{1/4})`.
- **Remark 7.3 (`sbm:rem:transseries`)**: Section 7 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  (a) `N` is an **instance**, verbatim, of `p0:prop:factorial-core` with
  `(κ, d, L) = (2, −2, L)`: `v = W₀(L/(2e)) = q − 1`, side condition `y > 1`;
  it is the double-factorial core of `p0:rem:factorial-core` at target `L/4`.
  (b) The expansion (7.4) **truncates an instance of the formal theorem**
  `p0:thm:core-reversion`, after `x = N(1+ξ)`, `τ = N^{−1/2}`: master
  equation `qξ + h_vol(ξ) + f_vol(τ, ξ) = 0` with `Λ = q`,
  `h_vol(ξ) = (1+ξ)log(1+ξ) − ξ`,
  `f_vol = √2 τ(1+ξ)^{1/2} + (τ²/8)(q + log(1+ξ) − log 2) + O(τ³)`; the
  first two coefficients reproduce `δ₀` and `δ₁` exactly. Only the general
  part of the theorem applies (not its Bell form, which needs integer
  exponents), the coefficients are Laurent polynomials in `q`, and the
  analytic remainder is the source's own: the volume's theorem is formal.
  (c) Theorem 7.2 is **not an instance** of `p0:thm:staircase` as proved
  (no interpolation is used), but **follows from part (1)** of it with the
  explicit admissible interpolation `F_J ∘ φ`, `φ` piecewise linear through
  `(n, x_J(a_n))`; this gives `K_J = 2C`. (d) Rounding the explicit inverse
  at `y = a_n` returns `n` beyond an existential onset: an instance of
  `p0:thm:staircase`(3). No novelty is claimed for the inversions.
- **Lemma 9.1 (`sbm:lem:transfer`)**: the proof of Theorem 1.1 uses the
  diagonal only through the circle bound (5.2) and a sectorial local
  expansion of the form (4.4); any nonnegative series with these two
  properties gets the same all-orders expansion with its own amplitude.
- **Proposition 9.2 (`sbm:prop:offset`)**: (a) for each fixed `d ≥ 0`,
  `A_{n+d,n}/((n+d)! n!)` has the expansion of Theorem 1.1 with amplitude
  `H_d` (a Bessel function of order `d`; coefficients from
  `T_d(1−w²/2)(1−w²/4)^{−1/2}`), `c₀^{(d)} = 1` and
  `c₁^{(d)} = −√2(17 + 48d(d−1))/96`; (b) the numbers of zero rows and of
  zero columns of a uniform random matrix converge jointly to independent
  Poisson(1) variables, with all mixed moments; the proportion with no zero
  line tends to `e^{−2}`. These settle one case each of the source's first
  two questions.
- Section 1.1 (`sbm:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), notes at the ends of Sections 8 and 10,
  the numbered questions at the end of Section 9, and two bibliography
  entries (OEIS A283500/A247158; Ordentlich, Parvaresh and Roth).

## The OEIS entries, quoted

Read on 6 October 2026 (plain-text format), verbatim:

    A197458 (#25, Apr 08 2020):
    %N A197458 Number of n X n binary matrices with at most two 1's in each row and column, other entries 0.
    A062154 (#14, Aug 18 2024):
    %N A062154 Number T(n,m) of n X m matrices over {0,1,2} with all row and column sums equal to 1 or 2, m=0,..,2*n.
    %D A062154 I. P. Goulden and D. M. Jackson, Combinatorial Enumeration, Wiley, N.Y., 1983,(Problem 3.4.15).
    %F A062154 Sum_{n >= 0, m >= 0} T(n, m)*x^n/n!*y^m/m! = 1/sqrt(1-x*y)*exp(x*y/2+1/(1-x*y)*(x*y+x^2*y/2+x*y^2/2)).
    A062156 (#7, Feb 03 2021):
    %N A062156 Number of n X n matrices over {0,1,2} with all row and column sums equal to 1 or 2.
    A001499 (#130, Sep 21 2026):
    %N A001499 Number of n X n matrices with exactly 2 1's in each row and column, other entries 0.
    %F A001499 a(n) ~ 2 sqrt(Pi) n^(2n + 1/2) e^(-2n - 1/2) [Knuth]
    %F A001499 Sum_{n >= 0} a(n)*x^n/(n!)^2 = exp(-x/2)/sqrt(1-x); a(n) = n(n-1)/2 [ 2 a(n-1) + (n-1) a(n-2) ] (Bricard)

The source's account of these entries (Section 10) is accurate; Remark 2.1
makes its "closely related component EGFs are older" precise: the A062154
formula, times `e^{x+y−xy}`, is the source's generating function. The
A062154 entry dates from June 2001; its formula line is present in the
earliest snapshot of the OEIS data repository (February 2023), and when it
was added was not traced. The entry's only literature reference is Goulden
and Jackson's Problem 3.4.15, which neither the source nor the write
inspected. A197458 still has no asymptotic formula. **Nothing was submitted
to the OEIS**, and no OEIS statement is corrected.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.1):

- No historical priority: general bounded-degree enumeration and
  configuration-model methods are classical, the component generating
  functions are older, the Goulden–Jackson exercise and Knuth's solution
  were not inspected, and the literature check is bounded.
- Theorem 1.1 is a Poincaré expansion at each fixed order: no convergence of
  the coefficient series, no exponentially small terms or transseries, no
  letting `J` grow with `n`.
- No effective remainder constant or onset; Theorem 7.2 is not a certified
  finite-input rounding algorithm, and no universally correct rounding of an
  asymptotic inverse is asserted.
- The ODE route to `c₁, …, c₄` is an identity check; finite exact agreement
  checks implementations, not the theorem; decimal diagnostics are
  uncertified.
- The four research directions of Section 9 are not proved there.

The write adds: Remark 7.3 compares statements and proves no new inverse;
Proposition 9.2 covers bounded offsets `m − n` and zero lines only, with
existential constants; the decimals printed at the ends of Sections 8 and 9
are floating-point observations at finitely many `n`.

## Further questions

Section 9 of the article (`sbm:sec:future`) keeps the source's four
paragraphs and states every unproved claim as a numbered open question with
its source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). **Nothing in the source was found to be wrong**, by the intake or by
the write.

1. **Rectangular aspect ratios** (`sbm:q:rectangular`). *Proved at the
   write:* fixed offsets `|m − n| = d` (Proposition 9.2(a)). Open: `m/n` in a
   compact subinterval of `(0, ∞)`, and the transition as `m/n → 1` with
   `|m − n| → ∞`.
2. **Marked components and distributions** (`sbm:q:marked`). *Proved at the
   write:* zero rows and zero columns, independent Poisson(1) in the limit
   (Proposition 9.2(b)). Open: balanced paths, unbalanced paths and cycles,
   whose marks move the saddle point or change the power of `(1 − t)`, so
   that Lemma 9.1 does not apply as stated.
3. **Effective errors and onset** (`sbm:q:effective`): explicit constants
   that would make Theorem 7.2 (and Remark 7.3(d)) a certified finite-input
   statement.
4. **Exponentially small terms** (`sbm:q:exponential`): secondary saddles and
   Stokes effects of the Bessel factor, the late growth of `c_j`, optimal
   truncation, a transseries.
5. **The literature boundary** (`sbm:q:literature`): Goulden–Jackson
   Problem 3.4.15, Knuth's solution, a specialization of Greenhill–McKay–Wang;
   the write made no search beyond the sources listed here.
6. **At most `k` ones, `k ≥ 3`** (`sbm:q:k`; added by the write, not a claim
   of the source): the next columns of A283500, where the components are no
   longer paths and cycles.

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 20 staged files other than `README.md` and `article.tex` are
  byte-identical to the archive, and so were the staged `Report168.tex` and
  README (rechecked at the write); `SHA256SUMS` 23/23. The dossier read the manuscript, recomputed the
  constants of Corollary 1.2 (`−¼ log 2`, `¼ log n`,
  `319/384 = 85/128 + 1/6`), and on copies reran `exact_matrix.py verify`
  (also under `-O`), `symbolic_coefficients.py --order 4` and the 35
  companion tests (all pass); 10 of the 11 release tests errored (POSIX).
- At the write (6 October 2026; same machine): the four OEIS entries above
  (A197458 still #25 with the 17 terms of `data/oeis_fixtures.json`);
  every proof reread line by line, with the component table, the generating
  function, the loss `D(r,θ)`, the endpoint difference (5.6), the scaling
  (6.1) and the leading constant, the Bessel coefficients, the expansions
  (4.6) (also with SymPy 1.14.0) and the inverse residual (7.6) with `δ₁`
  rederived; no error found. Independent computations (programs of the
  write, not shipped): `a_n` by brute force (`n ≤ 4`), by a row-by-row count
  over the full column-degree vector (`n ≤ 7`) and as
  `(n!)²[xⁿyⁿ] e^{x+y−xy}F₁₅₄` (`n ≤ 16`), all equal to the OEIS terms; the
  17 listed terms of A062156, rows 1–3 of A062154 and A001499 for `n ≤ 16`
  from the entries' formulas; the recurrence (3.3) checked against the exact
  Bessel diagonal for `n ≤ 77` and run in 120-digit arithmetic to
  `n = 4000`. There `n^{5/2}(R_n − Σ_{j≤4} c_j n^{−j/2})` is −11.33, −13.44,
  −14.05 at `n = 100, 1000, 4000` (the companion gives
  `c₅ = −3563067617707√2/342456532992 = −14.714…` and
  `c₆ = 109526487454949291/2465687037542400 = 44.420…` at order 6); the
  logarithmic remainder times `n^{3/2}` is −1.41, −1.63, −1.69; the right
  side of (7.4) at `y = a_n` minus `n` is −0.0103, −0.0036, −0.00088,
  −0.00038 at `n = 20, 100, 1000, 4000`; A001499(4000) over Knuth's
  equivalent is 0.99995. For Proposition 9.2, brute force confirms the
  offset generating functions (`d = 1, 2`, `n ≤ 3`) and the no-zero-line
  one (`n ≤ 4`); `A_{n+2,n}/((n+2)! n! b_n)` is 0.8395, 0.8767, 0.9070 at
  `n = 40, 80, 160`, with `√n` times its distance from 1 equal to −1.01,
  −1.10, −1.18 (limit `−√2`); the proportion with no zero line is 0.2290,
  0.2002, 0.1804, 0.1718 at `n = 20, 40, 80, 120` (limit
  `e^{−2} = 0.1353`). The reruns of the next section were made on copies.
  These are observations; they certify nothing.
- Sources read by the write: the OEIS entries A197458, A062154, A062156,
  A001499, A283500 and A247158; the oeisdata snapshot of A062154 of
  February 2023; the Crossref abstract of Ordentlich, Parvaresh and Roth; the
  transseries volume (`p0:def:core`, `p0:prop:factorial-core`,
  `p0:rem:factorial-core`, `p0:thm:core-reversion`,
  `p0:rem:core-instances`, `p0:def:three-inverses`, `p0:thm:staircase`).
  Not read by the write: Mathar's note, the Math Stack Exchange thread,
  Goulden–Jackson, Knuth's solution, Greenhill–McKay–Wang and
  Caizergues–de Panafieu (what the source inspected is recorded in
  `data/SOURCE_PROVENANCE.json`).

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns these matrices. Placement in the
collection confers no formal status.

**The transseries volume.** `N` is an instance of `p0:prop:factorial-core`;
the inverse expansion truncates an instance of the formal
`p0:thm:core-reversion`; the integer enclosure follows from
`p0:thm:staircase`(1) through an explicit interpolation (Remark 7.3). No
novelty is claimed for the inversions.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
the other binary-matrix reports of batch 108,
`a299907-lonesum-decomposable-matrices`, `a089479-fixed-permanent-matrices`,
`a222959-zero-slope-matrices`, `a110058-square-contingency-tables`,
`a138178-symmetric-packed-matrices` and `a027832-symmetric-sign-matrices`,
and `a261781-matrix-compositions`. None treats A197458, A062154, A062156 or
A001499, none shares a definition or a proof with this report, and none needs
a reciprocal note (the batch-108 dossier found the same).

**Stale claims.** Before batch 108 no file of the repository named A197458,
A062154, A062156 or A001499; the source made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings. The main trap: the source uses `q` both for
the Bessel argument `q(t) = 2√t h(t)` (Sections 2–5, and a complex variable
in Lemma 4.1) and for `q = log N` (Section 7). Others: `a_n`, `b_n`,
`A_{m,n}`; `F`, `F_J`, the write's `F₁₅₄`; `h(t)`, `h_j`, `H`; `L(t) = P'/P`
against `L = log y`; `I₀` against `I(y)`; `p(s)` against `p_i`; `E(s)`
against `E_m`; `N` (a real number) against `n`, `I(y)` and the volume's
`N_*`; `W = W₀`; `ε, u, 𝓜, M`; `D, D_J, δ, δ₀, δ₁`; `e(t), α, z`; the
write's `d, c_j^{(d)}, T_d`. No symbol of the source was renamed. In Remark
7.3 the volume's `h, f, E, t` are written `h_vol, f_vol, ξ, τ`; the write's
marks are `ω₁, ω₂` and its counts `Z_r, Z_c`.

## Labels

Every label carries the prefix `sbm:` (none existed in the repository). The
manuscript's 50 labels (`eq:` 35, `sec:` 10, `thm:` 3, `lem:` 1, `cor:` 1)
were prefixed before anything cited them, and the 45 references to them
updated. The write added 11: `sbm:sec:provenance`, `sbm:rem:oeis`,
`sbm:rem:transseries`, `sbm:lem:transfer`, `sbm:prop:offset`, and the
questions `sbm:q:rectangular`, `sbm:q:marked`, `sbm:q:effective`,
`sbm:q:exponential`, `sbm:q:literature`, `sbm:q:k`. The report has 61
labels; builds of the delivered text and of this one give all 50 delivered
labels the same numbers (aux files compared). The added statements are the
last numbered items of their sections, the added subsection 1.1 is the only
numbered subsection, and the added displays are unnumbered.

## Files

```text
README.md                                     this guide (replaces the delivery README)
article.tex                                   the report (delivered Report168.tex; labels prefixed, [write] additions)
article.pdf                                   compiled report, 23 pages
companion-USAGE.md                            the companion's usage guide (delivered companion/USAGE.md)
code/companion-exact_matrix.py                exact counts by five methods, CLI (delivered companion/exact_matrix.py)
code/companion-symbolic_coefficients.py       exact c_j by Gaussian moments and by the ODE ansatz (delivered companion/symbolic_coefficients.py)
code/companion-test_exact_matrix.py           26 tests (delivered companion/test_exact_matrix.py)
code/companion-test_symbolic_coefficients.py  9 tests (delivered companion/test_symbolic_coefficients.py)
code/build_pdf.py                             deterministic PDF build (delivered at the root)
code/make_zip.py                              allowlist-verified source ZIP (delivered at the root)
code/release_tools.py                         descriptor-pinned output helpers (delivered at the root)
code/test_release.py                          11 tests of the release tools (delivered at the root)
data/SOURCE_PROVENANCE.json                   sources inspected by the source and claim boundaries (delivered at the root)
data/verification_receipt.json                the delivering host's check record, with hashes (delivered at the root)
data/exact_verification.json                  output of exact_matrix.py verify (delivered data/)
data/symbolic_order4.json                     output of symbolic_coefficients.py --order 4 (delivered data/)
data/oeis_fixtures.json                       the 17 OEIS terms, n = 0..16 (delivered data/)
data/oeis_term_records.txt                    the entry's three term lines (%S, %T, %U) (delivered data/)
data/fixture_provenance.json                  retrieval time and hashes of the OEIS record (delivered data/)
data/tests_exact_normal.txt                   test receipt, Python 3.12.14 (delivered data/)
data/tests_exact_optimized.txt                the same under -O (delivered data/)
data/tests_symbolic_normal.txt                symbolic test receipt (delivered data/)
data/tests_symbolic_optimized.txt             the same under -O (delivered data/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report168.pdf` (the delivered 15-page PDF, 389,484 bytes); `SHA256SUMS`
(2,073 bytes, 23 entries, verified at placement; repository policy ships no
checksum manifests); and the delivery `README.md` (5,815 bytes), staged at
placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-USAGE.md` gives its commands as `companion/exact_matrix.py`,
`companion/symbolic_coefficients.py` and `companion/test_*.py` "from the
extracted package root"; the programs read `data/` beside the directory
holding them, and the tests import the programs by their delivered names, so
they do not run under the shipped names (route B below restores them).
`build_pdf.py` compiles `Report168.tex`; `make_zip.py` checks a closed
allowlist of the delivered names (`Report168.pdf`, `Report168.tex`,
`SHA256SUMS`, `companion/…`, …) against `SHA256SUMS`, neither of which is
shipped. `data/verification_receipt.json` hashes the delivered
`Report168.tex` and PDF, not the files here, and records the delivering
host's results (Python 3.12.14, pdfTeX 1.40.26). Section 8 of the article
speaks of "the source archive", "a manifest" and "the release README" (the
delivered ones). The release tools need POSIX (`os.mkfifo`, `O_NOFOLLOW`,
`/proc/self/fd`).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Sparse_Binary_Matrices_All_Orders_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # b67e3c4e515b14796637c541538d4af85acdf4041046fc02e730a32a02a9a0b8, 523,157 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 24 files are at the archive root
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it; every line
was run at the write on Windows):

```sh
cd "$T/pkg"
sha256sum -c SHA256SUMS                                        # 23 OK
python3 -B companion/exact_matrix.py verify > verify.out       # compare with data/exact_verification.json
python3 -B -O companion/exact_matrix.py verify
python3 -B companion/symbolic_coefficients.py --order 4 > sym4.out   # compare with data/symbolic_order4.json
python3 -B companion/symbolic_coefficients.py --order 6        # c_5, c_6 (the program accepts orders 0..8)
python3 -B -m unittest discover -s companion -p 'test_*.py' -v      # 35 tests
python3 -B -O -m unittest discover -s companion -p 'test_*.py' -v
python3 -B -m unittest -v test_release                         # 11 tests; POSIX only
```

On Windows the outputs carry CRLF line endings and equal the frozen files
after conversion (the `-O` `verify` output too); the 35 companion tests pass
in both modes (35–37 s on the intake's loaded laptop); 10 of the 11 release
tests error (`os.mkfifo` missing, "POSIX
O_NOFOLLOW is required"), as the delivery README's POSIX requirement
predicts. The PDF and ZIP rebuilds (`build_pdf.py --output-dir`,
`make_zip.py --output`, each refusing existing destinations) need POSIX and
pdfTeX and were not run by the intake.

**Route B, from the shipped files, any OS** (tested at the write; 35 tests
pass, and `verify` reproduces `data/exact_verification.json`):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a197458-line-sum-two-matrices
B=$(mktemp -d); mkdir "$B/companion" "$B/data"; cd "$B"
for f in exact_matrix symbolic_coefficients test_exact_matrix test_symbolic_coefficients; do
  cp "$R/code/companion-$f.py" "companion/$f.py"
done
cp "$R/data/oeis_fixtures.json" "$R/data/oeis_term_records.txt" "$R/data/fixture_provenance.json" data/
python3 -B -m unittest discover -s companion -p 'test_*.py' -v
python3 -B companion/exact_matrix.py verify
```

Use `py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, array, microtype, hyperref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 23
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 15 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report168.tex` under the delivering toolchain (pdfTeX
1.40.26), not to this build.

## From the delivery README

The delivery README (replaced by this guide) summarized the results as above
and called the research directions "carefully posed … without claiming them
as results"; listed the files under their delivered names; said the archive
excludes "third-party papers, the full OEIS entry, temporary builds,
screenshots, and private working materials"; gave the replay commands of
Route A, with the default verification ranges (17 OEIS terms, ODE to 200,
compressed DP to 40, rational GF to 30, tuple DP to 8, masks to 4) and the
symbolic bound of order 8 ("The mathematical rule itself applies at every
fixed order"); said "Exact finite agreement checks implementations and
identities. It is not a proof of the asymptotic theorem"; described the
POSIX PDF builder (fresh private directory, fixed TEXMF trees, no shell
escape, pinned metadata; "The same bytes are not promised across different
TeX/font versions") and the allowlist ZIP builder; and ended by saying that
the builders "never publish, upload, contact an author, or edit an external
repository".

## Rights

Repository contents are MIT-0. The article, this README and the data quote
OEIS terms, names and formulas of A197458, A062154, A062156, A001499 and
A283500; OEIS content is published by The OEIS Foundation Inc. under
CC BY-SA 4.0 (https://oeis.org/LICENSE), and those terms remain under that
licence. No third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A197458 (revision #25), A062154,
  A062156 and A001499; Mathar, *The number of binary n×m matrices with at
  most k ones in each row or column* (2014); Math Stack Exchange question
  72600; Goulden and Jackson, *Combinatorial Enumeration*, Problem 3.4.15
  (not inspected); Greenhill, McKay and Wang (2006); Caizergues and
  de Panafieu, EuroComb 2023. Added by the write: OEIS A283500 and A247158;
  Ordentlich, Parvaresh and Roth, SIAM J. Discrete Math. 26 (2012)
  1550–1575 (abstract).
- Batch 108 of `docs/incoming`, bundle Report 168; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report168.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
