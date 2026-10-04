# Unitary Divisor Sum Colored Partitions and Their Asymptotics

**The recorded OEIS equivalents of A301981 and A301982 are false; an
unconditional `o(n^(1/3))` logarithmic law that cannot be `O(n^(1/4-ε))`, a
sequence-specific criterion equivalent to the Riemann hypothesis, a corrected
equivalent at an explicit point, all-fixed-order exact-saddle and off-center
expansions, and integer-threshold brackets (Part I); two-sided oscillation,
`liminf a_n/m_n = 0` and `limsup a_n/m_n = ∞`, with logarithmic swings of
order at least `n^(1/4)` (Part II)**

A research report in two Parts, built from two manuscripts. Part I is dated
2 October 2026; its author line reads only "Research article and
reproducibility companion", and the delivery names no author and no tool.
Part II is the partition subject of a three-subject manuscript dated
4 October 2026 (UTC), whose author line reads "Prepared with ChatGPT" and
"Building on Vladimir Reshetnikov's ProveIt research repository".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 70 (cluster P4) | `unitary-partition-report.zip` (wrapper directory `unitary-partition-report/`), arrival commit `096ee7b87`; main file `unitary-partitions.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | Part I (Sections 1-11) |
| 02 | batch 86, manuscript 01 (cluster R1, placement 86A) | `oeis_advances.zip` (wrapper directory `oeis_advances/`, main file `oeis_advances.tex`), arrival commit `ae9baa422` | `eaf08931cbfd0132dd36ab82a7743ccb02506dc7`, continuing this report's `article.tex`, which did not change between the pin and the placement | `0f084afa9` | Part II (Sections 12-13): the manuscript's Section 7 in full, with the partition passages of its abstract and Sections 1, 8 and 9 |

Manuscript 01 of batch 86 treats three subjects and was split by subject at
placement. Its Section 2 (A343093, bridgeless toroidal maps) is the new
report
[`enumerative-combinatorics/a343093-bridgeless-toroidal-maps`](../../../enumerative-combinatorics/a343093-bridgeless-toroidal-maps/),
whose starting `article.tex` and `README.md` are that manuscript's source and
README; its Sections 3-6 (A088714 and A088713) are Part IV of
[`a088714-bell-scale-growth`](../a088714-bell-scale-growth/) (Sections 35-41
there; Theorems 37.1, 38.1 and 39.1 are its density, golden-ratio and
fixed-shift theorems). The A343093 report also keeps the manuscript's
introduction and its manuscript-wide non-claims: the internal reviews are
not refereeing, the bounded literature search is not a priority claim, and
no OEIS update or submission was made.

**Status:** both Parts are AI-assisted (Part I presumed so: its delivery
names neither an author nor a tool; Part II says "Prepared with ChatGPT"),
unrefereed, and not formalized. Part II records internal mathematical
reviews, which are not refereeing. The proofs are analytic; the shipped
programs check finite exact arithmetic and floating-point diagnostics only.

## What it proves

`b_m = σ*(m)` is the sum of the unitary divisors of `m` (OEIS A034448).
A301981 is `∏(1-z^m)^(-b_m)` and A301982 is `∏(1+z^m)^(b_m)`; write `a_n^±`
for their coefficients, `A_- = π²/6`, `A_+ = π²/8`,
`c_± = 3(A_±/4)^(1/3)`, `t_0 = (2A_±/n)^(1/3)`.

### Part I

- **Theorem 3.3 (refutation).** Kotěšovec's conjectured equivalents
  `a_n^± ~ m_n^±` recorded in the two OEIS entries (2018, inspected
  2 October 2026) are false; more strongly, `a_n^±/m_n^±` does not
  eventually stay in any compact subinterval of `(0, ∞)`. The proof is a
  least-height zeta-zero noncancellation (Lemma 3.1: the Mellin kernel,
  with denominator `ζ(2s-1)`, has a genuine pole with `3/4 ≤ ℜ s_0 < 1`)
  combined with an Abelian transfer (Lemma 3.2).
- **Theorems 6.1, 7.2 (unconditional logarithmic law).**
  `log a_n^± = c_± n^(2/3) + o(n^(1/3))`, and for no `0 < ε < 1/4` is the
  error `O(n^(1/4-ε))`.
- **Theorem 7.4 (RH criterion).** For each sign separately, RH holds if and
  only if `log a_n^± = c_± n^(2/3) + O_ε(n^(1/4+ε))` for every `ε > 0`.
  This is an equivalence: it neither proves nor disproves RH.
- **Theorem 6.1 (corrected equivalent at an explicit point).**
  `a_n ~ t_0^2 (12πA)^(-1/2) exp(f(t_0) + n t_0) = m_n exp(R(t_0))`, with
  relative error `o(1)` and no rate.
- **Theorem 5.2 (all fixed orders at the exact saddle)** with explicit
  cumulant corrections `C_j(t_n)` and error `O_M(t_n^(2M+2))`;
  **Theorem 9.1 (all fixed orders at the explicit point)** with Hermite
  grades that keep the mean mismatch and all odd grades.
- **Theorems 8.2, 9.2 (inverses).** Eventual increase of `a_n^±`; the integer
  threshold `N(y) = min{n : a_n ≥ y}` lies between two ceilings
  `⌈x_M(y) ∓ ε_M(y)⌉` with `ε_M = O(x_M^(-(2M+1)/3))`; `N(y) ~ (log y / c)^(3/2)`.

### Part II

Let `ρ = β + iγ` be a nontrivial zeta zero of least positive height,
reflected so that `β ≥ 1/2`, `m` its multiplicity, and
`s_* = (1+ρ)/2 = σ_* + iτ_*` (Part I's `s_0`; `3/4 ≤ σ_* < 1`).

- **Lemma 12.4 (the surviving pole and its constant).** `M_±` has a pole of
  order `m` at `s_*` with the explicit nonzero leading Laurent coefficient
  `C_± = m! Γ(s_*) χ_±(s_*) ζ(s_*+1) ζ(s_*) ζ(s_*-1) / (2^m ζ^(m)(ρ))`.
  This re-proves Part I's Lemma 3.1 and adds the order and the constant.
- **Lemma 12.3 (a quantitative two-sided consequence).** Landau's
  positivity principle (Lemma 12.2) in quantitative form: a nonreal pole of
  order `m` with leading coefficient `C_*` of the Mellin transform of `h`
  forces `h(x)/(x^σ_* (log x)^(m-1))` to have upper limit at least
  `|C_*|/(m-1)!` and lower limit at most its negative. A written-out form
  of a classical method; no novelty is claimed for the principle.
- **Theorem 12.5 (quantified two-sided oscillation).** With
  `W(n) = n^(σ_*/3) (log n)^(m-1)` and
  `K_± = |C_±| (2A_±)^(-σ_*/3) 3^(1-m) / (m-1)!`,
  `limsup log(a_n^±/m_n^±)/W(n) ≥ K_±` and
  `liminf log(a_n^±/m_n^±)/W(n) ≤ -K_±`, and the same for
  `log a_n^± - c_± n^(2/3)`. Hence `liminf a_n^±/m_n^± = 0`,
  `limsup a_n^±/m_n^± = ∞`, and both centered logarithms are
  `Ω_±(n^(1/4))`. No RH, no simplicity of zeros, no sum over zeros. This
  answers question 3 of Part I's Section 11. `W(n)` here is **not** the
  Lambert W function used in the neighbouring A088714 report.
- **Corollary 12.6 (oscillating error of the pure inverse).** If `X_±(y)`
  inverts the pure model `m^±(x)` and `N_±(y) = min{n : a_n^± ≥ y}`, then
  `(N_± - X_±)(y) / ((log y)^((σ_*+1)/2) (log log y)^(m-1))` has upper
  limit at least `L_±` and lower limit at most `-L_±`, with
  `L_± = 2^(1-m) |C_±| / ((m-1)! (3A_±)^((σ_*+1)/2))`; in particular the
  error is `Ω_±((log y)^(7/8))`.
- Proposition 12.1 restates Part I's Lemma 4.1 and Theorem 6.1 and re-derives
  them in outline (credited by the manuscript).

A dated note after Theorem 12.5 records what follows by combining it with
Part I: under RH the centered logarithm is both `Ω_±(n^(1/4))` and
`O_ε(n^(1/4+ε))`, so the exponent `1/4` is exact under RH.

## What is not claimed

- RH is not proved or disproved; RH is assumed only in Lemma 7.3 and the
  direction "RH ⇒ bound" of Theorem 7.4. Every other result, Part II
  included, is unconditional. No simplicity of zeta zeros, no numerical zero
  location and no zero-residue expansion is used.
- Part I's refutation alone does not say which one-sided divergence occurs
  (Remark after Theorem 3.3). Part II proves that both occur; a dated note
  after the remark says so.
- Part II's constants `K_±`, `L_±` are rigorous lower bounds, not exact
  amplitudes, and not estimates of the first index where a sign occurs; the
  proof does not assert that a single zero dominates the remainder. It gives
  no density of either sign, no gap bound between sign changes, no effective
  index, no certified value of `K_±`, no sharp scale or limiting
  distribution, and no joint sign pattern of the two sequences (its
  questions in Section 12.6 and Section 13.1). The finite ratios recorded in
  Part I's `data/unitary_diagnostics.json` stay between about 0.69 and 1.10
  for `20 ≤ n ≤ 1000` and move monotonically; this does not contradict
  Theorem 12.5, an infinite-subsequence statement (a dated note in Section 13
  says so).
- The explicit-point equivalent has no rate (Remark 6.2).
- The inverse constants `C_M`, `Y_M` are existence constants, not certified
  cutoffs; there is no exact single-ceiling identity `N(y) = ⌈x_M(y)⌉`
  (Remark 8.3).
- Priority: the Dirichlet series of `σ*` is classical (Tóth, unnumbered in
  §4.9 on p. 28, not his eq. (50)); Bureaux–Enriquez, Bodini et al., Dong et
  al., Bridges et al. and others receive explicit methodological credit; "a
  targeted literature search … not an exhaustive priority claim or a claim of
  a new general Mellin/RH method". Part II credits the positivity method to
  Landau (1905) and a related Mellin application to Diamond–Pintz (2009),
  claims "no new general oscillation principle or an exhaustive historical
  priority determination", does not claim Part I's refutation as new, and
  says its bounded search "does not establish exhaustive historical
  priority".
- Numerical checks: exact integer arithmetic for coefficients and exact
  rational tail majorants, but floating evaluations, root-finder results and
  ratios are **not** interval enclosures; a larger-cutoff, higher-precision
  match checks stability only. Finite numerics cannot establish a pure
  equivalent, decide RH, or certify either infinitely occurring sign. Part II
  deliberately presents no plot as evidence.
- Of Part I's five closing questions (Section 11), question 3 (oscillation)
  is answered by Part II; questions 1, 2, 4 and 5 (an explicit rate,
  effective constants, zero-residue corrections, other weights) remain open,
  as do the finer oscillation questions Part II lists. Dated notes at the
  end of Section 11 say so.
- **Inversion: no novelty for the integer step.** The model inverted is the
  exact-saddle model `G_M` (or the explicit-point `L_M`), which keeps the
  arithmetic fluctuations; the Lambert-core theorems `p0:thm:lambert-core` /
  `p0:thm:lambert-centered` do **not** apply to it as stated. They apply
  only to the refuted pure models (`X = x^(2/3)`, `a = c_±`, `b_+ = -1`,
  `b_- = -5/4`, branch `W_{-1}`), whose inverse cannot locate `N(y)` within
  bounded distance; Part II's Corollary 12.6 quantifies that error from both
  sides. The width `ε_M` is the residual-to-root conversion
  `p0:thm:backward-error`, and the two-ceiling bracket is
  `p0:thm:staircase` (1)–(2) with `x_* = x_M(y)`, `η = ε_M(y)`; all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note after Remark 8.3 says so.
- Part II's delivery: "No OEIS update, repository change, or external
  submission was made as part of this work"; the manuscript "has not been
  externally refereed or formalized in a proof assistant".

## Relation to the repository

**Claims about OEIS text, not about ProveIt.** Theorem 3.3 is the
manuscript's theorem about formulas printed in OEIS A301981 and A301982. At
intake, untruncated searches of the research-report collection, the
transseries volumes, `Oeis/` and `docs/reports/` for A301981 and A301982
returned no file, so no repository claim is refuted and nothing was
retracted. Part II strengthens Part I and contradicts none of its
statements. Neither delivery says that a correction was submitted to the
OEIS, and this report implies none.

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; neither
manuscript used a formalized ProveIt theorem. The generic order-theoretic
steps named in the inverse note are formalized for an arbitrary monotone
function, not for `a_n`: `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, and
`Fabius.abs_sub_right_inverse_le_div` in
`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`.

**Neighbouring reports.** The collection's other partition-product reports
(`a033552-catalan-partitions`, `a022629-distinct-partition-norms`,
`a097356-sqrt-restricted-partitions`,
`a238016-restricted-partitions-cubic-boundary`) and the batch-77 reports
`a174065-radix-layer-partitions` (where a pure OEIS equivalent likewise
omits an oscillating factor, there a log-periodic one) and
`a372395-acyclic-orientation-partitions` treat other products; none treats
unitary-divisor weights, a zeta-zero denominator or an RH criterion, and no
result is shared. Part II's sibling subjects went to
`enumerative-combinatorics/a343093-bridgeless-toroidal-maps` and to Part IV
of `a088714-bell-scale-growth`; they share no result with this report.
The batch-86 reciprocal notes added pointers back here: in
`a343093-bridgeless-toroidal-maps` (its Section 3 and README, naming
Sections 12–13 and Theorem 12.5, `udp:tw:thm:main`), in
`a088714-bell-scale-growth` (Part IV's provenance in its Section 35), in
`a174065-radix-layer-partitions` (a dated sentence in its batch-77 note in
Section 1, contrasting its bounded log-periodic factor with the two-sided
oscillation here), and in `a301746-divisor-weighted-asymptotics`, whose
batch-77 note in Part I, Section 7, uses this report's zero-pole as a sharp
instance of a warning, and now gains a dated note on Part II.

## Notation

Part I reuses letters: `c` (growth constant) vs the contour abscissa
`c_*`; the correction terms `C_j(t)` vs the constants `C_1, C_2`, `C_r`,
`C_M`; `K` four ways; `δ` three ways; `ε = ±1` in the cumulant recursion
(where `ε = 1` is the *minus* product) vs the small exponent `ε`; `H`
(holomorphic remainder) vs Hermite `H_d`; `σ(m)` vs a contour abscissa `σ`;
`N(y)` vs `N = ⌊1/t⌋`; `t_0` is the explicit point `(2A/n)^(1/3)`, not `t_x`
at `x = 0`; `R_±` is an exact (unbounded) remainder. A table in the first
`[write]` note (end of §1.1) fixes every such symbol.

Part II keeps its manuscript's symbols. Shared objects agree with Part I
(`t_{0,±}` is Part I's `t_0^±`, `χ_±` its `\ch_±`, `𝒢` its Glaisher
constant), but `j` is the part size, `m` the order of the pole, `W(n)` the
oscillation scale (not Lambert W, and not Part I's `W(t)` in the proof of
Theorem 9.2), `σ_*` (subscript) is not `σ*` (superscript, the unitary divisor
sum), and `C_*`, `C_±`, `K_±`, `L_±`, `h`, `H`, `T_±`, `E_n`, `x_n`, `X_±`
have their own meanings. A table at the start of Part II fixes them. No
symbol of either manuscript was renamed.

## Labels

Every label carries the prefix `udp:`; Part II's carry `udp:tw:`. Part I:
the manuscript's 79 labels were prefixed before anything cited them (79
`\ref`/`\eqref` updated), and three section labels were added
(`udp:sec:results`, `udp:sec:prior`, `udp:sec:questions`): 82 labels. Part
II (3 October 2026) added 27: `udp:part:one`, `udp:tw:part`, the
manuscript's 23 `part:` labels renamed `udp:tw:`, `udp:tw:sec:scope` and
`udp:tw:sec:verify`: **109 labels in all**. Wrapping Part I in `\part`
renumbers nothing in the article class: the `.aux` files of the one-Part and
two-Part builds give all 82 Part I labels the same numbers.

The batch-77 write added four dated `[write]` notes (end of §1.1: provenance,
OEIS-facing claims, the RH equivalence, neighbours, notation table; after
Remark 8.3: the inverse note; end of §10.3: the shipped files; end of §11:
the open questions), one bibliography entry (`udp-tai`), and restored the
diacritic in "Kotěšovec" (three places, printed "Kotesovec" in the
delivery). The batch-86 write added a paragraph to the abstract, a second
title-page date line, four dated notes in Part I (after the first note: the
two Parts; after the remark following Theorem 3.3; after Theorem 7.2; after
the Section 11 note: question 3 answered), the Part II heading with its
summary and five dated notes (provenance and editorial changes, notation,
after Theorem 12.5, shipped files, Section 13 sources), the `array` package
for Part II's table, and two bibliography entries (Landau 1905,
Diamond–Pintz 2009). No statement, proof or number of either manuscript was
changed. Part II's editorial changes (cross-references for its citations of
the pinned report, Part I's bibliography keys for shared references, and
lightly adapted sentences from the manuscript's abstract and Sections 1, 8
and 9) are listed in its provenance note.

## Files

```text
README.md                                     this guide (replaces both delivery READMEs)
article.tex                                   the report (Part I delivered as unitary-partitions.tex)
article.pdf                                   compiled report, 32 pages
code/numerics_core.py                         shared numerical core (mpmath); keep it beside the check scripts
code/check_oeis_prefixes.py                   unitary-divisor enumeration and binomial products vs the OEIS prefixes (reads data/oeis-prefixes.json)
code/check_unitary.py                         integer recurrence through 1000, trial-divisor checks, principal residue, old-model diagnostics
code/check_saddle.py                          exact-cumulant centered formulas, M = 0, 1, 2
code/check_fixed_saddle.py                    explicit-point equivalent and stationary-exponent comparisons
code/check_cutoff_precision.py                cutoff 1000/60 digits vs 2000/80 digits; WRITES two files into ../data
code/check_inverse.py                         centered model inverse tests
code/check_offcenter.py                       binomial products vs recurrence through 500, Hermite grades, odd-grade deletion
code/check_offcenter_replay.py                cutoff 1200/70 digits vs 1800/90 digits; WRITES two files into ../data
code/check_offcenter_inverse.py               explicit-point inverse checks
code/compare_replay.py                        JSON comparison of a replay directory with a reference directory
code/verify_manifest.py                       checks a delivered SHA-256 manifest (the manifests are not shipped)
code/safe_extract.py                          standalone safe ZIP extractor
code/package_release.py                       the delivery's release packer (do not run; see below)
code/reproduce.sh                             the delivered replay driver (expects the delivery layout; see below)
code/build.sh                                 the delivered PDF build (expects unitary-partitions.tex; see below)
code/02-two-sided-verify_partitions.py        Part II: two weight algorithms and two coefficient algorithms through n = 160, 21 OEIS terms per sequence (standard library only)
data/oeis-prefixes.json                       inspected OEIS prefixes (36 terms of A301981, 37 of A301982)
data/unitary_diagnostics.json                 recorded check_unitary.py output
data/saddle_diagnostics.json                  recorded check_saddle.py output
data/fixed_saddle_diagnostics.json            recorded check_fixed_saddle.py output
data/fixed_saddle_replay_2000_80.json         high-precision replay written by check_cutoff_precision.py
data/cutoff_precision_report.json             comparison report written by check_cutoff_precision.py
data/cutoff-precision-summary.json            recorded check_cutoff_precision.py output (rational tail bounds)
data/inverse_diagnostics.json                 recorded check_inverse.py output
data/offcenter_diagnostics.json               recorded check_offcenter.py output
data/offcenter_replay_1800_90.json            high-precision replay written by check_offcenter_replay.py
data/offcenter_replay_report.json             comparison report written by check_offcenter_replay.py
data/offcenter-replay-summary.json            recorded check_offcenter_replay.py output
data/offcenter_inverse_diagnostics.json       recorded check_offcenter_inverse.py output
data/runtime-versions.json                    reference environment (Python 3.12.14, mpmath 1.3.0)
data/requirements.txt                         mpmath==1.3.0
data/receipts-build-environment.txt           delivered receipt: pdfTeX, Python and mpmath versions
data/receipts-numerical-verification.json     delivered receipt: entry points, case counts, source hashes
data/receipts-safe-extraction-tests.json      delivered receipt: safe_extract.py tests
data/receipts-visual-qa.json                  delivered receipt: rendering checks of the delivered PDF
data/02-two-sided-partition_verification.json Part II: recorded output of 02-two-sided-verify_partitions.py
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery.

**Part I.** Placement renamed `unitary-partitions.tex` to `article.tex`;
moved `build.sh` and `reproduce.sh` from the package root to `code/`,
`requirements.txt` to `data/`, and `receipts/<name>` to
`data/receipts-<name>`. Not shipped: the delivered 18-page PDF
`unitary-partitions.pdf` and the checksum ledgers `MANIFEST.sha256` (39/39)
and `SOURCE-MANIFEST.sha256` (33/33), both verified at placement. All survive
in the archive:
`git show 096ee7b87:docs/incoming/unitary-partition-report.zip > <scratch>/unitary-partition-report.zip`.

**Part II.** Placement (`0f084afa9`) shipped `code/verify_partitions.py` as
`code/02-two-sided-verify_partitions.py` and `data/partition_verification.json`
as `data/02-two-sided-partition_verification.json`. The manuscript's other
programs and outputs belong to its other subjects and are shipped with the
A343093 report and with Part IV of the A088714 report; its source and README
were placed as the A343093 report's starting `article.tex` and `README.md`.
Its 40-page PDF is not shipped, and the delivery has no checksum manifest.
Everything survives in the archive:
`git show ae9baa422:docs/incoming/oeis_advances.zip > <scratch>/oeis_advances.zip`.

Delivered text that names the delivery layout or unshipped files:
`code/reproduce.sh` (runs from its own directory; needs
`SOURCE-MANIFEST.sha256`, `unitary-partitions.pdf` and `build.sh` beside it,
and `pdftotext`); `code/build.sh` (compiles `unitary-partitions.tex` in its
own directory, writing `.build/`); `code/package_release.py` (writes
`SOURCE-MANIFEST.sha256` and `MANIFEST.sha256` into the directory above
`code/` and a ZIP beside that directory: run in place it would write into
this report and into `oeis-sequence-asymptotics/`); the receipts (delivery
paths `receipts/…` and hashes of the delivered files); the article's
Section 10 (the "companion archive" with its manifests; a dated note there
says what is shipped); `code/02-two-sided-verify_partitions.py` (its
docstring says `python3 code/verify_partitions.py`); and the article's
Section 12.6 and Section 13, printed from the manuscript (they name
`code/verify_partitions.py`, `data/partition_verification.json` and "the
accompanying archive"; a dated note in Section 13 gives the shipped names).

**OEIS data.** `data/oeis-prefixes.json` (36 and 37 terms) and the two
21-term lists inside `code/02-two-sided-verify_partitions.py` are short
excerpts of OEIS A301981 and A301982, content of The OEIS Foundation
licensed under CC BY-SA 4.0 and cited in the article's bibliography; they
are reference data for the checks, not results of this report. The 21 terms
of each list equal the first 21 of `data/oeis-prefixes.json`.

## Rerun the checks (on a scratch copy)

### Part I

Never run the scripts in this directory: `check_cutoff_precision.py` and
`check_offcenter_replay.py` overwrite four shipped files in `data/`. Also,
`compare_replay.py` compares every `*.json` of its reference directory, and
the shipped `data/` holds three `receipts-*.json` that no script produces
and Part II's `02-two-sided-partition_verification.json`, so compare against
a reference copy without them. Git Bash, from this directory:

```sh
R=$(mktemp -d) && cp -R code data "$R" && cd "$R"
mkdir ref && cp data/*.json ref/ && rm ref/receipts-*.json ref/02-two-sided-*.json
export PYTHONUTF8=1
PY="uv run --no-project --with mpmath==1.3.0 python"
run() { echo "$1"; $PY code/$1.py > data/$2.json; }
run check_oeis_prefixes oeis-prefix-check
run check_unitary unitary_diagnostics
run check_saddle saddle_diagnostics
run check_fixed_saddle fixed_saddle_diagnostics
run check_cutoff_precision cutoff-precision-summary
run check_inverse inverse_diagnostics
run check_offcenter offcenter_diagnostics
run check_offcenter_replay offcenter-replay-summary
run check_offcenter_inverse offcenter_inverse_diagnostics
$PY code/compare_replay.py ref data
```

This is the sequence of `code/reproduce.sh` without its manifest check and
its PDF rebuild. The comparison is of parsed JSON, so Windows line endings do
not matter. Alternatively use the delivered layout: extract the archive
above and run `bash reproduce.sh` there (it also rebuilds and compares the
PDF text, which depends on the TeX installation).

At intake (2 October 2026, Python 3.13.5, mpmath 1.3.0, a heavily loaded
machine, a three-minute limit per step) the manifest check passed (33
files), and twelve recomputed JSON files equalled the recorded ones;
`check_inverse.py` and `check_offcenter_inverse.py` did not finish within
the limit, so `inverse_diagnostics.json` and
`offcenter_inverse_diagnostics.json` were not regenerated, and the PDF
rebuild was not run. Expect the whole sequence to take more than ten
minutes.

### Part II

The program uses only the standard library and writes a file only when
given `--output` (it always prints its JSON report). Run it on a copy with
an explicit output path, never into this report's `data/`. Git Bash, from
this directory:

```sh
R=$(mktemp -d) && cp code/02-two-sided-verify_partitions.py "$R/" && cd "$R"
uv run --no-project python 02-two-sided-verify_partitions.py --output out.json > /dev/null
tr -d '\r' < out.json | cmp - "$OLDPWD/data/02-two-sided-partition_verification.json" && echo identical
```

Run it without `python -O`: its checks are assertions. On Windows the
written file has CRLF line endings, hence the `tr`. At placement and again
at this write (3 October 2026, Python 3.13.5, about 3 seconds) the output
equalled the recorded file up to line endings. The delivery's own command,
`python3 code/verify_partitions.py --output data/partition_verification.json`,
needs the delivered layout (extract the archive above).

## Build the PDF

pdfLaTeX with lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, microtype, hyperref and enumitem. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 32 pages, no
errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The one-Part report built to 20 pages; Part I's delivered source
builds to 18 pages, and manuscript 01 of batch 86 to 40 pages, all without
warnings.) `code/build.sh` is kept as delivered; to use it, copy it to a
scratch directory together with `article.tex` renamed to
`unitary-partitions.tex`.

## Provenance

- OEIS A301981, A301982 (entries by V. Kotěšovec, 30 March 2018; inspected
  2 October 2026 for Part I and 4 October 2026 UTC for Part II), A034448;
  Tóth, J. Integer Seq. 20 (2017), Art. 17.2.1; Bureaux–Enriquez, Discrete
  Analysis 2016:19; Bodini–Duchon–Jacquot–Mutafchiev (DGCI 2013); Dong–
  Robles–Zaharescu–Zeindler, arXiv:2412.20101; Bridges–Brindle–Bringmann–
  Franke, Math. Ann. 390 (2024); Trudgian, Funct. Approx. 52 (2015); Landau,
  Math. Ann. 61 (1905); Diamond–Pintz, J. Théor. Nombres Bordeaux 21 (2009);
  see the article's bibliography.
- Part I: batch 77 of `docs/incoming`, manuscript 70 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Repository input: none recorded; no pin.
- Part II: batch 86 of `docs/incoming`, manuscript 01 (`oeis_advances.zip`,
  cluster R1); arrival `ae9baa422`, placement `0f084afa9` (batch 86A, split
  by subject), written in the batch-86 write phase (3 October 2026). Pin
  `eaf08931cbfd0132dd36ab82a7743ccb02506dc7`; repository input: Part I
  (Lemma 3.1, Lemma 4.1, Theorems 6.1 and 8.2, the definitions of
  Section 1).
- Merge choices: Part I is printed unchanged and wrapped as Part I; Part II
  takes the manuscript's Section 7 in full and, from its shared Sections 1,
  8 and 9, only the partition passages (the other passages are printed with
  the A343093 and A088714 reports). Part II's citations of the pinned report
  became cross-references to Part I, and its OEIS, Tóth, Trudgian and DLMF
  citations use Part I's bibliography entries. Its re-proofs of Part I's
  results (Proposition 12.1, the pole of Lemma 12.4) are printed as
  delivered, credited by the manuscript and by the provenance note, not
  merged into Part I.
