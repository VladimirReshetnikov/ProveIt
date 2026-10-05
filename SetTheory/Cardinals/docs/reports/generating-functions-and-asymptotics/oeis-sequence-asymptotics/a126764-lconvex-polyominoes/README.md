# L-convex Polyominoes and a Colored-Partition Comparison

**A proof of the A126764 asymptotic, three correction terms, an all-orders
radial expansion, and inverse asymptotics (OEIS A126764). Part II: the
all-orders coefficient theorem. Part III: a complete transfer proof**

A research report dated 1 October 2026, built from three manuscripts, each
printed in full. Part I's author line is "Research manuscript prepared for
Vladimir Reshetnikov"; its PDF metadata and delivery README say "prepared
with ChatGPT". Part II's author line is empty and it names no tool. Part
III's author line and PDF author field read "Research note prepared with
OpenAI".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 05 | `A126764_Lconvex_Research.zip`, arrival commit `4b874cea0` (main file `lconvex_asymptotics.tex`; its PDF and `manifest.json` not shipped) | none: no ProveIt commit is named; the repository input was an overview and a targeted A126764 search on 1 October 2026 | `6ea60e367` (written in `936896776`) | Part I: Sections 1–12, Appendices A–B |
| 02 | batch 77, manuscript 31 | `lconvex-asymptotics-reproducibility.zip`, arrival commit `096ee7b87` (*All order asymptotics and inversion for L convex polyominoes*, main file `article/lconvex-asymptotics.tex`, 11-page PDF; manuscript, PDF, README and manifest not shipped) | none: no ProveIt commit is named and the repository is not mentioned | `4f11bc9c0` | Part II: Sections 13–23 (13 and 23 editorial) |
| 03 | batch 101, bundle Report 95 | `L_Convex_Polyomino_Area_Asymptotics_Source.zip`, arrival commit `60f54ea06` (*All Order Area Asymptotics for L Convex Polyominoes*, 2 October 2026, main file `article.tex` with five `\input` files, 16-page PDF; sources, PDF, README and package verifier not shipped) | none: no ProveIt commit is named and the repository is not mentioned | `f7c612c72` | Part III: Sections 24–34 (24, 33 and 34 editorial) |

**Status:** AI-assisted, unrefereed, not formalized. Part I is backed by exact
integer checks through `n = 2000` and symbolic checks, Part II by an exact
replay through `n = 2000` and `q^96`, Part III by exact coefficients through
`n = 8000`, a comparison with all 2001 b-file terms, a literal expansion
through `n = 400` and symbolic checks of its coefficient and inverse
formulas. These checks corroborate the identities and constants; no
numerical fit enters any proof. Part II's three shipped reviews are the
delivery's own internal checks, not external peer review.

The three manuscripts were written independently. Part II is not a version
of Part I: only 40 of its 380 distinct non-blank source lines occur in Part
I's source, and it uses another proof architecture. Part III knows Part I's
manuscript (it cites it as a separate unpublished manuscript) but not Part
II, and it uses a third architecture. Results proved in more than one part
are printed in each, with its own proof, and cross-referenced (Sections 13.2
and 24.3).

## What it proves

`a_n` counts fixed L-convex polyominoes of area `n` (OEIS A126764,
`a_0 = 1`). In Part I's letters, `K = 13π²/24`, `B = 2√K = π√(13/6)` and
`c = 13√2/768`. Part II calls these constants `κ`, `2√κ` and `C`; Part III
calls them `K`, `β` and `δ`. See "Notation" below.

**Part I**
- **The Guttmann–Kotěšovec asymptotic** recorded as a conjecture in
  A126764: `a_n ~ c n^(-3/2) e^(B√n)`, with three corrections,
  `a_n = c n^(-3/2) e^(B√n) (1 - d/√n + e/n + f/n^(3/2) + O(n^(-7/4)))`,
  `d = B/12 + 3/B = 1.03410521762627…`, `e = -1.95847649289673…`,
  `f = 12.5504457791462…` (closed forms in Theorem 1.1).
- **A coefficient squeeze** against the colored-partition Euler product
  `R(q) = (q²;q²)²/((q;q)⁴(q⁴;q⁴))` (four colors for odd parts, two for
  parts ≡ 2 mod 4, three for multiples of 4): with `p_n = [q^n]R`,
  `0 <= p_n - 4a_n <= 3(p_n - 2p_{n-1} + p_{n-2})` for every `n >= 3`, and
  `n(1 - 4a_n/p_n) → K/2 = 13π²/48`. This alone gives the leading term and
  the first correction.
- A finite-cut identity and a full-circle error estimate giving the two
  further corrections.
- An all-orders **radial** expansion of the generating function at
  `q = e^(-t)`, `t → 0+`, by a finite recurrence (coefficients through `t^8`
  displayed).
- An asymptotic inverse for a specified interpolation of `a_n`, via `W_{-1}`,
  and the rule `N(y) = ⌈ν(y)⌉` for the integer threshold.

**Part II**
- **An exact decomposition** `A = P B² + R`. Here `P` is Part I's Euler
  product, `B` is a partial theta function
  `1 - Σ_{k≥0} q^{k(k+1)} (1 - q^{2k+1})/(1 + q^{2k+1})` (by Heine's and
  Fine's transformations), and the remainder `R` has coefficients
  `O(n^{1/4} e^{π√(2n)})`, exponentially smaller than `a_n`.
- **The all-orders coefficient theorem** (Theorem 14.1): for every fixed
  `M`, with `N = n - 1/6`,
  `a_n = C N^(-3/2) e^(2√(κN)) (Σ_{r<M} c_r N^(-r/2) + O(N^(-M/2)))`. The
  `c_r` come from a finite algorithm; `c_0, …, c_4` are displayed. The case
  `M = 4` re-proves Part I's Theorem 1.1, with remainder `O(n^-2)`
  (re-expansion checked symbolically).
- Eventual strict log-concavity, with
  `log(a_n²/(a_{n-1}a_{n+1})) = √κ/(2N^{3/2}) - 3/(2N²) + O(N^{-5/2})`. An
  injection proves that `a_n` is nondecreasing.
- A Lambert-`W_{-1}` inverse in the shifted coordinate
  `y = 2√(κ(n - 1/6))` to order `y_0^{-3}`, logarithmic inverse polynomials
  to order `L^{-3}`, and integer brackets of width `O(x^{-(M-1)/2})` for
  every order `M >= 2`.
- **A write-phase observation** (Remark 16.2, with proof and a 40-digit
  check): Part I's boundary series `D = L/R` is exactly Part II's partial
  theta function `B`. This partly answers Part I's research question 4.

**Part III**
- **A third proof of the all-orders coefficient theorem** (Theorem 25.1), in
  the unshifted index: for every fixed `m`,
  `a_n = δ n^(-3/2) e^(2√(Kn)) (Σ_{r<m} c_r n^(-r/2) + O(n^(-m/2)))`, with
  `c_1, c_2, c_3 = -d, e, f` of Part I. It is the same theorem as Part II's
  Theorem 14.1; Remark 24.1 converts the coefficients (`c_4` unshifted is
  `5/(16K) - 175/32 - 3775K/864 - 29375K²/31104 = -55.7596598453…`). The
  route is new and every estimate is written out: positivity of the
  generating function, a low-index part that is exponentially smaller, a
  damping bound from the finite partition factor `(q;q)_N` common to all
  later terms, a Chebyshev interpolation lemma that carries the real-axis
  expansion into the saddle window, and a Bessel extraction (completed in
  writing by Lemma 28.1). No complex estimate of the multiplier or of the
  eta quotient is needed.
- **The decomposition** `A = 1 + M h² + R` (Proposition 26.1) by a duality
  argument, with the positive series
  `R = M^{-1} Σ_{n≥1} q^n B_Q(q^{n+1})/((q;q)_{n-1}(q;q)_n)` and the bounds
  `0 <= R <= D q/(1 - q²)`, `R/M <= q (q;q)_∞²/(1 - q²)` on `0 < q < 1`. The
  identity is Part II's `A = P B² + R` (`M = P`, `h = B`, Part III's `R` is
  Part II's `R - 1`); the proof, the positive formula and the bounds are new.
- The multiplier `h` by reduction of order (tail `<= (q;q)_J²/(J + 1)`, and
  `h > 0`), and by an alternating series with an alternating error bound.
- **Strict increase:** `a_{n+1} >= a_n + 1` for every `n >= 1` (the injection
  misses the vertical bar). Part II proves only that `a_n` is nondecreasing.
- **The limit** `n - n_0(a_n) → η = 1/6 + 36/(13π²) = 0.4472484059…` for the
  leading Lambert root `n_0(y) = z_0(y)²/(4K)`, so nearest-integer rounding
  of `n_0(a_n)` recovers `n` for all large `n` (eventual, not effective;
  observed correct for `556 <= n <= 8000` and wrong for `2 <= n <= 555`).
- Coefficients in `z = β√n`, logarithmic coefficients `λ_1, …, λ_4`, a
  power–log inverse in `Y = log y`, and threshold brackets (Part II's
  brackets with the order shifted by one).
- Exact coefficients `a_0, …, a_8000`; all 2001 b-file terms agree.
- **Write-phase results** (proofs printed): the auxiliary polynomials are
  Al-Salam–Chihara polynomials, `Q_n(q) = Q_n(1; i√q, -i√q | q)` (Remark
  26.3); no continuous function `g` has `N(y) - g(y) → 0` for the step
  threshold (Remark 29.2); the coefficient conversion (Remark 24.1); a
  written-out proof of the limit `η` (Remark 29.1).

## What is not claimed

- The area generating function (Castiglione–Frosini–Munarini–Restivo–Rinaldi
  2007, in the recurrence form of Guttmann–Kotěšovec) is a cited input of
  all three parts.
- No part made an exhaustive priority search; targeted searches found no
  earlier proof. Part III did not check W. R. G. James's 2005 thesis in full.
  Part II says that the final display of Section 2 of Guttmann–Kotěšovec
  prints the reciprocal of `C`. This was not checked when Part II was
  written. *Dated note, 5 October 2026 (batch 101):* it is now checked
  against arXiv:2109.09928v3: that display has amplitude `1/C` while the
  quoted decimal is `C`, as Parts II and III say (notes in Sections 14 and
  25).
- **No exponentially small sectors and no complete transseries** for `a_n`.
  Part II's bound on the exact remainder is deliberately coarse. Part I
  disclaimed an all-orders coefficient expansion; Part II now proves it, and
  Part III proves it again. Part I's Section 8.2, research question 1 and
  claim ledger carry dated notes saying so.
- No numerical universal error constants, so no part certifies an integer
  inversion near a threshold. Part II's bracket constants and its
  log-concavity threshold are existential, and no finite starting index is
  given. Part III's rounding rule is eventual: the onset 556 is observed in a
  finite scan, not proved.
- No convergence, optimal truncation or resummation of the formal series
  (Part II, open problem 3; Part III, Section 33, item 3). No modularity
  claim for `B`.
- No four-to-one combinatorial map behind `p_n >= 4a_n`; perimeter
  enumeration and 201-avoiding ascent sequences are not addressed.
- Numerical tables are diagnostics, not proof. Of the 2001 computed
  coefficients, only the first 37 OEIS terms and four b-file anchors were
  compared with an external source by Parts I and II. The two parts compute
  the same 2001 integers by different recurrences. *Dated note, 5 October
  2026 (batch 101):* Part III's checker compares all 2001 terms with a
  snapshot of the b-file that is byte-identical to the live OEIS file
  (checked at intake), so every b-file term now agrees with the coefficients
  of all three parts. Part III's terms `2001 <= n <= 8000` are generated,
  not published data; Part I's `verify.py` reproduced them at intake.
- **The inversions are instances of repository results, and no novelty is
  claimed for the method.** Part I's core `s - 3 log s = ℓ`, Part II's core
  `y_0 - 3 log y_0 = L` and Part III's core `z_0 - 3 log z_0 = log(y/𝒜)` are
  `p0:thm:lambert-core` (`a = 1`, `b = -3`, branch `W_{-1}`). Their
  corrections are `p0:thm:lambert-centered` and
  `p0:thm:perturbed-inversion`. Part I's rounding rule and the integer
  brackets of Parts II and III are `p0:thm:staircase` (1)–(2). The shape of
  the argument is that of the partition chapter `p3:sec:lambert` /
  `p3:thm:core-correction`. All of these are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  Dated `[write]` notes in Sections 9.2, 20 and 29 say so. New in Part III
  is the limit `η` and the eventual rounding rule of the leading model.
- The research directions of Section 11 (eight), Section 22 (five) and
  Section 33 (six, with Part III's own four questions in Section 31) are
  questions, not results.
- Some proofs in Part II are sketched to the level of standard estimates:
  the whole-circle bounds of Lemma 17.1 and the minor arcs of Lemma 17.3.
  Its shipped mathematical audit, items 6–8, spells them out. *Dated note,
  5 October 2026 (batch 101):* Part III proves the same all-orders theorem
  without either lemma, with every estimate written out (Section 28 and
  Lemma 28.1; comparison in Table 3 of Section 24.3). Part II's sketched
  lemmas themselves are unchanged.
- Part III's novelty sentence ("the distinction claimed here is the
  all-orders pointwise coefficient theorem") predates Part II's arrival in
  the report and is stale; Remark 31.1 prints it with the correction (its
  distinction is the route).
- No OEIS edit was made.

## Notation

Parts II and III keep their manuscripts' letters, because their shipped
data and reviews use them. Many of them clash. Table 1 (Section 13.3) lists
every clash between Parts I and II, and Table 4 (Section 24.4) every clash
of Part III with both, with the tempting false reading. The dangerous ones
are these:

- Part II's `P` and Part III's `M` are Part I's `R`, the Euler product.
- Part II's `R` is the exact remainder, which has no counterpart in Part I;
  Part III's `R` is Part II's `R - 1`.
- Part II's `κ` is Part I's and Part III's `K`, and Part II's `K = C(2√κ)³`
  is Part I's `cB³` and Part III's constant `𝒜` (not Part I's generating
  function `𝒜(q)`).
- Part II's `B(q) = D(q)` is a partial theta function, and so is Part III's
  `h(q)`. Part I's `B` is the constant `2√K` (Part III's `β`), and Part I's
  `D(q) = L/R` is the same function as Part II's `B(q)`. **Part III's `D(q)`
  is another function**, `(-q;q²)_∞/(q;q)_∞`.
- Part II's `C` is Part III's `δ`; Part III's `C` is `1/(4(2π)^{3/2})`.
- Part II's `p_n = [q^n]PB² ~ a_n`; Part I's `p_n = [q^n]R ~ 4a_n`; Part
  III's `p_n = (q;q)_n`.
- Part II's `N = n - 1/6` and its coefficients `c_r` are shifted; Part III's
  `c_r` are unshifted (Remark 24.1 converts them). Part I's `N(y)` and Part
  III's `N(y)` are the threshold index.

No symbol was renamed and no normalization changed. Write notes mark a
clashing object of another part with a superscript `I` or `II`.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq. Its place in the collection gives it no formal status, and no
manuscript used a ProveIt theorem. The generic staircase lemmas named in
Sections 9.2, 20 and 29 are formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
They concern an arbitrary monotone interpolation, not `a_n`.

**Stale sentences.** Section 1.1 says that a targeted repository search for
A126764 returned no matching file. That was true at the inspection; the only
match now is this report (dated note added). Part III's novelty sentence is
corrected in Remark 31.1. Part III's Section 31 calls the growth constant of
A202058 conjectural and suggests late-term growth for A229741/A260879 as a
target; the repository now has `a202058-ascent-000-growth` (the constant
proved, stretched-exponential scales excluded) and the volume
`Analysis/Transseries/docs/series-and-transseries/Late_Coefficients_Factorially_Forced_Catalan_Recurrence`
(the A260879 equivalent proved with every fixed correction). Dated notes in
Sections 31 and 33 re-scope the item.

**Neighbouring reports.**
`enumerative-combinatorics/polyomino-growth-finite-prefix-corrections`
bounds **Klarner's constant** for all polyominoes (`λ <= 2249/500`; its Lean
project `Combinatorics/Polyominoes/KlarnerConstant` proves
`λ <= 9047/2000`). That is an exponential growth rate of a different class:
L-convex polyominoes grow like `e^(B√n)`, so the constants are unrelated and
no theorem is shared. `enumerative-combinatorics/skew-partition-continued-fractions`
touches parallelogram polyominoes (A006958) only. Among the OEIS-sequence
asymptotics reports, the closest in method are the partition-type
`e^(C√n)` reports, such as `a022629-distinct-partition-norms` and
`a097356-sqrt-restricted-partitions`, which treat different products. The
batch-101 report `a196275-column-convex-permutominoes` treats another
convexity class (column-convex permutominoes, factorial growth); it shares
no theorem with this one. These pointers are made here only; those reports
are not edited.

**Ascent sequences (batch 77, dated 2 October 2026).** Section 1.1 leaves
the asymptotics of 201-avoiding ascent sequences, which Guttmann and
Kotěšovec discuss beside L-convex polyominoes, to other work. The sibling
report `a202062-ascent-201-enumeration` (batch 77P1) proves their cubic
generating function for A202062 and its all-orders asymptotics; the two
problems share only the Guttmann–Kotěšovec paper (dated note in
Section 1.1).

**Z-convex polyominoes (batch 101, dated 5 October 2026).** Part I's
research question 7 proposes the Z-convex area asymptotics of
Guttmann–Massazza (2024) as a target. Its first author's publication list
now says that the paper's series data are wrong, and so is the analysis
based on them (checked at intake; notes in Sections 11 and 31 and in the
bibliography).

## Labels

Part I's labels carry the prefix `lcp:`. The manuscript's 59 labels were
prefixed in batch 75 before anything cited them. Part II's labels carry the
prefix `lcp:ao:`: the manuscript's 50 labels, plus 15 added in writing (12
section and subsection labels, the notation table and two remarks). Part
III's labels carry the prefix `lcp:tr:`: the manuscript's 54 labels (its
`tr:2` is `lcp:tr:tr:2`), plus 26 added in writing (16 section and
subsection labels, two tables, five remarks, a lemma and two equations).
The report now has 204 labels, and no earlier label was renamed, removed or
renumbered (checked against the `.aux` of the committed text).

In Part I, batch 75 added three dated `[write]` notes. Batch 77P5 added
eight dated notes: after the scope box, in Section 1.1, at the end of
Section 8.2, in research questions 1, 4, 5 and 7, and after the claim
ledger. It also added a title line, contents entries for the two parts, two
preamble macros (`\ii`, `\dd`), one bibliography entry (`lcp-ao-dlmf`) and
notes in the entries `zconvex` and `lcp-tai`. Part II prints the manuscript
verbatim, apart from its labels, its macro `\e` (now Part I's `\ee`)
and its citation keys (mapped to the merged entries). The additions are
the editorial Sections 13 and 23, two remarks headed "write" and seven
`[write]` notes. No statement, proof or number of either manuscript was
changed.

Batch 101 added Part III and ten dated notes in Parts I and II: after the
scope box, in Section 1.1, at the end of Section 8.2, in Section 10.1, in
research question 7, and in Sections 14 (the reciprocal display, now
checked), 17 (the sketched lemmas), 20 (strict increase and `η`), 21 (the
complete b-file) and 23. It also added a title line, a contents entry,
notes in the entries `castiglione` and `zconvex`, and six bibliography
entries (`lcp-tr-earlier`, `lcp-tr-dlmf`, `lcp-tr-bjm`, `lcp-tr-conway`,
`lcp-tr-borinsky`, `lcp-tr-kls`). Part III prints the manuscript verbatim
apart from its labels, its citation keys and the pandoc command
`\tightlist`; its Appendix A is Section 32, whose heading says so. The
additions are the editorial Sections 24, 33 and 34, five remarks and a
lemma headed "write", the paragraph after the lemma that completes the
extraction step, and fourteen `[write]` notes.

## Files

```text
README.md                                     this guide (replaces the three delivery READMEs)
article.tex                                   the report (Part I delivered as lconvex_asymptotics.tex; the manuscripts
                                              of Parts II and III are printed inside it)
article.pdf                                   compiled report, 71 pages
02-all-orders-mathematical-audit.md           Part II's internal analytic audit of its proof note (as delivered)
02-all-orders-final-source-review.md          Part II's internal review of its final source (as delivered)
02-all-orders-computational-review.md         Part II's code and reproducibility review (as delivered)
03-transfer-exact-checks-README.md            Part III: note on the exact checks and diagnostics (delivered as checks/exact/README.md)
code/verify.py                                Part I: exact integer checks (standard library); writes into --out
code/verify_symbolic.py                       Part I: SymPy/mpmath checks; reads and writes checks/ beside itself
code/02-all-orders-replay.py                  Part II: exact replay (standard library), optional SymPy/mpmath extras
code/03-transfer-multiplier-derive_multiplier.py   Part III: exact multiplier expansion d_0..d_8, both formulas for h (SymPy)
code/03-transfer-symbolic-check_inverse.py    Part III: Gaussian-saddle and formal inverse checks; rewrites symbolic_results.json beside itself
code/03-transfer-exact-verify_exact.py        Part III: exact coefficients, b-file and literal checks; writes beside itself
code/03-transfer-exact-check_diagnostics.py   Part III: 100-digit diagnostics from exact_coefficients_<N>.json beside itself
code/03-transfer-exact-scan_lambert_rounding.py  Part III: finite scan of rounding n_0(a_n); writes beside itself
code/03-transfer-run_checks.sh                Part III: the delivered driver (delivery layout, bare python)
data/coefficients.csv                         Part I: n, a_n, p_n, p_n - 4a_n, j_n for 0 <= n <= 2000 (CRLF)
data/verification.json                        Part I: verify.py summary (37 OEIS terms, b-file anchors 50, 100, 200, 500, eight checks)
data/exact_checks.txt                         Part I: recorded verify.py stdout
data/numerical_table.csv                      Part I: ratio and deficit diagnostics at n = 50 ... 2000 (CRLF)
data/expanded_table.csv                       Part I: truncation and inverse diagnostics at n = 50 ... 2000 (CRLF)
data/symbolic_checks.txt                      Part I: Q_3, h_3, the radial series through t^8, the correction coefficients
data/symbolic_run.txt                         Part I: recorded verify_symbolic.py stdout
data/requirements.txt                         Part I: sympy==1.14.0, mpmath==1.3.0 (only for verify_symbolic.py)
data/02-all-orders-coefficients-2000.txt      Part II: the replay's reference fixture, "n a_n" for 0 <= n <= 2000 (no final newline)
data/02-all-orders-forward-series.json        Part II: recorded D, D^2 and h_r coefficients through degree 12
data/02-all-orders-exact-identities.json      Part II: recorded q-series identity checks through q^96
data/02-all-orders-inverse-series.json        Part II: recorded inverse coefficients through order 4
data/02-all-orders-numerical-diagnostics.json Part II: recorded 90-digit diagnostics (not certified bounds)
data/02-all-orders-receipt.json               Part II: parameters, versions, reference and output SHA-256 of the recorded run
data/02-all-orders-safety-checks.json         Part II: operational tests of the delivery tooling
data/02-all-orders-final-pdf-visual-approval.json  Part II: approval record of the unshipped 11-page PDF
data/02-all-orders-requirements-optional.txt  Part II: mpmath==1.3.0, sympy==1.14.0 (only for --extras)
data/03-transfer-symbolic_results.json        Part III: b_r, lambda_r and inverse polynomials (check_inverse.py output)
data/03-transfer-exact-exact_coefficients_8000.json   Part III: a_0 ... a_8000 as decimal strings (generated beyond n = 2000)
data/03-transfer-exact-verification_results_8000.json   Part III: verify_exact.py record (2001 b-file terms, literal to 400)
data/03-transfer-exact-verification_results_8000_optimized.json   the same under python -O
data/03-transfer-exact-diagnostics_8000.json  Part III: check_diagnostics.py record through n = 8000
data/03-transfer-exact-diagnostics_8000_optimized.json   the same under python -O
data/03-transfer-exact-lambert_rounding_scan.json   Part III: rounding scan, correct for 556 <= n <= 8000
data/03-transfer-exact-lambert_rounding_scan_optimized.json   the same under python -O
data/03-transfer-PROVENANCE.json              Part III: the delivery's provenance record and SHA-256 manifest
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery.

**Part I.** Placement renamed `lconvex_asymptotics.tex` to `article.tex`,
moved the delivered `checks/` directory to `data/` and the scripts to
`code/`, and moved `requirements.txt` from the package root to `data/`. The
delivered PDF and `manifest.json` (a SHA-256 ledger with a page count,
verified 13/13 at placement) are not shipped. The three CSVs have CRLF line
endings as delivered (Python's `csv` writer) and keep them through `-text`
lines in `SetTheory/Cardinals/.gitattributes`. The scripts call the
article's constant `K` by the name `A`. Delivered text that names the
delivery layout: the article's Appendix A (`lconvex_asymptotics.tex`,
`--out checks`, the compiled PDF; dated note added) and
`code/verify_symbolic.py` itself, whose paths `checks/coefficients.csv`,
`checks/symbolic_checks.txt` and `checks/expanded_table.csv` are fixed
relative to the script.

**Part II.** Placement prefixed every shipped name with `02-all-orders-`.
It moved `audit/*.md` to the report root, `receipts/*.json` and the
fixture to `data/`, and `requirements-optional.txt` to `data/`. Not
shipped: the manuscript (printed in `article.tex`), its 11-page PDF, its
build script `article/build.sh`, its delivery README, its checksum manifest
`MANIFEST.json` (verified 20/20 at placement) with its verifier
`code/verify_package.py`, `receipts/coefficients.txt` (the fixture plus a final
newline), and `receipts/portable-tex-build.json` (the record of the PDF
build). Delivered text that still uses delivery names:

- The three reviews name `article/lconvex-asymptotics.tex`,
  `receipts/receipt.json`, `receipts/safety-checks.json` and
  `receipts/portable-tex-build.json`, and they refer to the PDF, the
  manifest and the extraction helper.
- `02-all-orders-final-pdf-visual-approval.json` and
  `02-all-orders-final-source-review.md` record SHA-256 hashes of the
  unshipped manuscript and PDF.
- `02-all-orders-receipt.json` records output hashes of LF-terminated
  outputs, among them the unshipped `coefficients.txt`.
- `code/02-all-orders-replay.py` reads its fixture from
  `../data/coefficients-2000.txt`, relative to itself, and writes unprefixed
  output names.

The mathematical audit reviewed a proof note (`proof-note.md`, SHA-256
`17b92af4…`) that was not delivered; the final source review compares the
manuscript with it.

**Part III.** Placement prefixed every shipped name with `03-transfer-` and
the delivered subdirectory (`multiplier-`, `symbolic-`, `exact-`), moved the
scripts and `run_checks.sh` to `code/`, the JSON records and
`PROVENANCE.json` to `data/`, and `checks/exact/README.md` to the report
root. Delivered names: `checks/multiplier/derive_multiplier.py`,
`checks/symbolic/check_inverse.py`, `checks/symbolic/symbolic_results.json`,
`checks/exact/{verify_exact,check_diagnostics,scan_lambert_rounding}.py`,
`checks/exact/*.json`, `run_checks.sh`, `PROVENANCE.json`. Not shipped: the
manuscript's six sources and its expanded `article_standalone.tex` (printed
in `article.tex`), its 16-page PDF, its delivery README, `verify_package.py`
(a SHA-256 check against `PROVENANCE.json`; 28/28 at intake),
`build_local.sh` (a PDF build of the sources), `checks/exact/b126764_web.txt`
(the OEIS b-file snapshot: `data/02-all-orders-coefficients-2000.txt` plus a
final newline, SHA-256 `d036795c…`), and `checks/exact/symbolic_results.json`
(a byte copy of the shipped symbolic results). Delivered text that still
uses delivery names, or names unshipped files:

- The scripts read and write files beside themselves under fixed delivered
  names: `verify_exact.py` reads `b126764_web.txt` and writes its `--output`
  and **overwrites** `exact_coefficients_<max-n>.json`;
  `check_diagnostics.py` reads `exact_coefficients_<max-n>.json` and
  `symbolic_results.json`; `scan_lambert_rounding.py` reads
  `exact_coefficients_<max-n>.json` and writes `lambert_rounding_scan.json`
  by default; `check_inverse.py` rewrites `symbolic_results.json` beside
  itself.
- `code/03-transfer-run_checks.sh` uses the delivered paths, calls bare
  `python` (which does not resolve on every system) and ends with the
  unshipped `verify_package.py`.
- `03-transfer-exact-checks-README.md` names `b126764_web.txt`,
  `symbolic_results.json`, `../symbolic/check_inverse.py` and commands with
  the delivered names.
- `data/03-transfer-PROVENANCE.json` hashes the unshipped files, records the
  PDF's page count, and its key `known_related_unpublished_manuscript`
  carries the stale novelty sentence corrected in Remark 31.1.
- The `_optimized` records differ from the ordinary ones only in the flag
  `python_optimization` and in timing fields.

The OEIS data in the b-file (and in Part II's fixture and the coefficient
files that agree with it) are licensed CC BY-SA 4.0.

## Rerun the checks (on a scratch copy in the delivered layout)

The scripts of all three parts expect their delivered layouts, and running
them in place would either fail or overwrite shipped files. Use scratch
copies (Git Bash, from this directory).

**Part I.** `verify.py` writes into `--out` (default `checks`, relative to
the working directory). `verify_symbolic.py` reads `checks/coefficients.csv`
and writes `checks/symbolic_checks.txt` and `checks/expanded_table.csv`
**next to itself**:

```sh
R=$(mktemp -d) && mkdir "$R/checks" && cp code/verify.py code/verify_symbolic.py "$R" && cd "$R"
uv run --no-project python verify.py --nmax 2000 --out checks > checks/exact_checks.txt
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify_symbolic.py > checks/symbolic_run.txt
```

Run `verify.py` first, because it produces the CSV that the symbolic checker
reads. Do not use `python -O`, because the checks are assertions. Then
compare `checks/` with `data/`. On 2 October 2026 (batch 75) the two
commands took 3 s and 7 s. All assertions passed. `coefficients.csv`,
`numerical_table.csv` and `expanded_table.csv` came out byte-identical, and
`verification.json`, `exact_checks.txt`, `symbolic_checks.txt` and
`symbolic_run.txt` were identical apart from line endings (Windows writes
CRLF). With `--nmax 8000` (about 8 minutes at intake, 5 October 2026) all
assertions still pass, and its `a_n` equal Part III's
`data/03-transfer-exact-exact_coefficients_8000.json`.

**Part II.** The replay needs Python 3.10 or later. It refuses an existing
output directory and rejects `-O`:

```sh
R=$(mktemp -d) && mkdir "$R/code" "$R/data"
cp code/02-all-orders-replay.py "$R/code/replay.py"
cp data/02-all-orders-coefficients-2000.txt "$R/data/coefficients-2000.txt"
cd "$R"
uv run --no-project python code/replay.py --output-dir core
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/replay.py --output-dir full --extras
```

Compare `full/*.json` with `data/02-all-orders-*.json`, and
`full/coefficients.txt` with the fixture plus a final newline, using
`diff --strip-trailing-cr`. On Windows the replay writes CRLF line endings,
so the hashes in its new `receipt.json` differ from the recorded ones
although the content is equal. On 2 October 2026 the core run took 6 s and
the full run 78 s here. Both passed, and all five outputs equalled the
recorded ones apart from line endings. The new receipt's reference SHA-256
equals the recorded `19d49450…`.

**Part III.** Recreate the delivered `checks/` tree, rebuild the b-file
snapshot from Part II's fixture, and pass explicit output names so that no
recorded file is overwritten:

```sh
R=$(mktemp -d) && mkdir -p "$R/checks/exact" "$R/checks/symbolic" "$R/checks/multiplier"
cp code/03-transfer-multiplier-derive_multiplier.py "$R/checks/multiplier/derive_multiplier.py"
cp code/03-transfer-symbolic-check_inverse.py "$R/checks/symbolic/check_inverse.py"
for f in verify_exact check_diagnostics scan_lambert_rounding; do cp "code/03-transfer-exact-$f.py" "$R/checks/exact/$f.py"; done
cp data/03-transfer-symbolic_results.json "$R/checks/exact/symbolic_results.json"
{ cat data/02-all-orders-coefficients-2000.txt; echo; } > "$R/checks/exact/b126764_web.txt"   # SHA-256 d036795c...
cd "$R"
uv run --no-project --with sympy==1.14.0 python checks/multiplier/derive_multiplier.py
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python checks/symbolic/check_inverse.py
cd checks/exact
uv run --no-project --with mpmath==1.3.0 python verify_exact.py --max-n 8000 --literal-n 400 --output verification_replay.json
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python check_diagnostics.py --max-n 8000 --output diagnostics_replay.json
uv run --no-project --with mpmath==1.3.0 python scan_lambert_rounding.py --max-n 8000 --output scan_replay.json
```

`verify_exact.py` writes `exact_coefficients_8000.json`, which the last two
commands read (to skip it, copy
`data/03-transfer-exact-exact_coefficients_8000.json` there instead). Compare
`exact_coefficients_8000.json`, `diagnostics_replay.json`, `scan_replay.json`
and `../symbolic/symbolic_results.json` with the corresponding
`data/03-transfer-*` files using `diff --strip-trailing-cr`;
`verification_replay.json` equals
`data/03-transfer-exact-verification_results_8000.json` apart from its timing
fields. These checks use explicit exceptions, so `python -O` also works. At
intake (5 October 2026, Python 3.14.4) the suite passed on a copy in about
6.5 minutes (the exact coefficients through 8000 took 122 s; the delivery
records 15 s), and every output equalled its record apart from line endings
and timings. In writing, the recipe above was checked with the shipped
coefficients and a short `verify_exact.py --max-n 2000` run: the snapshot's
SHA-256 matched, all 2001 terms matched, and the diagnostics, scan and
symbolic results equalled their records.

## Build the PDF

pdfLaTeX with newpxtext/newpxmath, amsmath, amsthm, mathtools, microtype,
xcolor, booktabs, array, longtable, enumitem, fancyhdr, tcolorbox and
hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory. It has 71 pages, with
no errors, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, and no overfull or underfull boxes. Part I
alone built to 20 pages in batch 75, and Parts I–II to 39 pages in batch 77.

## Provenance

- Part I: OEIS A126764 and its b-file (accessed 1 October 2026);
  Castiglione, Frosini, Munarini, Restivo, Rinaldi, Eur. J. Combin. 28
  (2007); Guttmann–Kotěšovec, Sém. Lothar. Combin. 87B (2023),
  arXiv:2109.09928 v3; DLMF §27.14; Guttmann–Massazza (Z-convex, cited only
  as a research target). Repository input: an overview and a targeted
  A126764 search, no commit recorded. Batch 75 of `docs/incoming`,
  manuscript 05: arrival `4b874cea0`, placement `6ea60e367`, written in
  `936896776`.
- Part II: the same OEIS entry, Castiglione et al., Guttmann–Kotěšovec and
  Guttmann–Massazza (its p. 19 for the conjectural status), and DLMF
  version 1.2.8, §§17.6, 23.18 and 10.40 (inspected 1 October 2026). No
  repository input. Batch 77 of `docs/incoming`, manuscript 31: arrival
  `096ee7b87`, placement `4f11bc9c0`, written in the batch-77 write phase
  (2 October 2026). The archive can be retrieved with
  `git show 096ee7b87:docs/incoming/lconvex-asymptotics-reproducibility.zip`.
- Part III: the same OEIS entry and b-file (accessed 2 October 2026),
  Castiglione et al. (equations (24)–(25)), Guttmann–Kotěšovec,
  Bringmann–Jennings-Shaffer–Mahlburg on Tauberian pitfalls, DLMF §§23.18,
  27.14, 10.40, 10.17 and 17.6, Conway–Conway–Elvey Price–Guttmann and
  Borinsky (further directions), Tony Guttmann's publication list, and
  Part I's manuscript. No repository input. Batch 101 of `docs/incoming`,
  bundle Report 95: arrival `60f54ea06`, placement `f7c612c72`. The archive
  can be retrieved with
  `git show 60f54ea06:docs/incoming/L_Convex_Polyomino_Area_Asymptotics_Source.zip`.
  The write added Koekoek–Lesky–Swarttouw §14.8 for the Al-Salam–Chihara
  remark.
- Where the merges had to choose (Sections 23 and 34):
  - Parts II and III go after Part I's closing Section 12 and before its
    appendices, in arrival order, so no number of an earlier part moves;
    Part III's manuscript appendix is its Section 32.
  - Letters are kept, with clash tables, rather than renamed.
  - Duplicated results keep every proof.
  - Four of Part II's five references were merged into Part I's entries;
    its DLMF entry stays separate. Part III's references to
    Castiglione et al., Guttmann–Kotěšovec and OEIS were merged; its three
    DLMF entries became one; its other references are new entries.
