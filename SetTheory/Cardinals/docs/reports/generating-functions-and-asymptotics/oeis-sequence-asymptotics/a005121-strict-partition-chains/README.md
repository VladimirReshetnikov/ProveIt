# Strict Partition Chains (OEIS A005121, Lengyel's Numbers)

**A fixed-order asymptotic expansion of the number of strict chains in the
partition lattice, proved by a recurrence and a first-difference
contraction; cumulants of the chain length; inverse thresholds; and a sign
error in the OEIS generating-function formula**

A research article ("Report 223" of a session bundle), built from one
manuscript. The manuscript is undated; its author line reads "Report 223"
and its PDF author field is empty: it names no person, tool or addressee.
The package carries no "prepared for private review" line, no e-mail address
and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 223 (batch 106) | `Report223.zip` (15 files at the archive root, no wrapper directory, 509,137 bytes, SHA-256 `c1781918…cf2b8f25`), arrival commit `60f54ea06`; main file `Report223.tex` (787 lines, 19 pp.) | ProveIt `9f19e58de` (the inspected `a139383-iterated-bell-diagonals` article, blob `ab5014ec`, unchanged at the write, and the transseries catalogue) | `47fc7a069` (batch 106) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. Every theorem has a
conventional proof from the recurrence; no proof uses a computation or a
numerical value of the constant.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 (the expansion to every fixed
  order), Theorem 8.1 (the complex marking disk), Corollaries 9.1–9.2
  (cumulants, mean and variance with corrections, central limit theorem) and
  Section 10 (logarithmic expansion, inverse, sampled recovery, two-ceiling
  threshold enclosure), from the recurrence
  `Z_n(q) = q Σ_{j<n} S(n,j) Z_j(q)` alone.
- **What is prior work, re-proved.** The leading equivalent and `C > 0`
  (Babai–Lengyel 1992, Theorem 2), the leading mean and the central limit
  theorem (Van Cutsem–Ycart 1994). Formal higher corrections were announced
  by Prellberg (2002); the 1990 Flajolet–Salvy manuscript was not recovered,
  so no first occurrence of `c_2, c_3, …` is claimed.
- **What is numerical only.** `C ≈ 1.098685805525187`,
  `K_1 ≈ −0.565529523`, `K_2 ≈ −0.220333135` (Section 11) are uncertified
  diagnostics. No constant `A_M`, `Y_M` or onset is evaluated.
- **The programs** check exact values, the full partition poset for
  `n ≤ 6`, the factorial domination for `n ≤ 100`, the symbolic coefficient
  algebra through order 4 and the inverse; they prove nothing asymptotic.

## What it proves

`z_n` is the number of strict chains from the least to the greatest element
of the partition lattice `Π_n` (A005121); `Z_n(q)` marks the length `H`
(number of strict transitions, `H_1 = 0`). Put `L = log 2` and
`f_n = (n!)² (2L)^{−n} n^{−1−L/3}`. Statement numbers are the delivered ones.

- **Theorem 1.1 (`spc:thm:main`)**: `z_n = C f_n (Σ_{j≤M} c_j(L) n^{−j} +
  O(n^{−M−1}))` for every fixed `M`, with `C = lim z_n/f_n > 0` (Lengyel's
  constant) and `c_j ∈ ℚ[L]`: `c_1 = L/6`, `c_2 = −L(16L² + 45L − 90)/3240`,
  `c_3 = L²(10L² − 81L − 270)/6480`, `c_4` displayed.
- **Sections 3–7**: the factorial domination `2^k k! S(n, n−k) ≤ (n)_k²`
  (Lemma 3.1), a uniform kernel expansion by block defects (Lemma 4.1),
  `c_m ∈ ℚ[L]` (Proposition 5.1), a first-difference transfer lemma with
  limiting norm `2 log 2 − 1 < 1` (Lemma 6.1), and the anchoring of `C`.
- **Theorem 8.1 (`spc:thm:marked`)**: the same expansion for `Z_n(q)` with
  `L(q) = Log(q+1) − Log q`, uniformly on one disk about `q = 1` (contraction
  on `|q − 1| ≤ 1/16`, then one shrink to avoid zeros of `C(q)`).
- **Section 9**: every fixed cumulant of `H_n`;
  `E H_n = n/(2L) + (log n)/6 + K_1 − 1/(12n) + O(n^{−2})`,
  `Var H_n = (1−L)n/(4L²) − (log n)/12 + K_2 + 1/(24n) + O(n^{−2})`;
  the central limit theorem (a re-proof).
- **Section 10**: `log z_n` to every fixed order (Proposition 10.1); a
  Lambert-`W_0` inverse with a triangular recursion (Theorem 10.2); eventual
  recovery of `n` from `log z_n` (Corollary 10.3); for
  `N(y) = min{n ≥ 2 : log z_n ≥ y}`,
  `⌈ξ − ε⌉ ≤ N(y) ≤ ⌈ξ + ε⌉` with `ε = A_M ξ^{−M−1}/log ξ` (Theorem 10.4).
- **Section 2.1**: the formal e.g.f. obeys `2Z(z) = z + Z(e^z − 1)`
  (radius of convergence zero).

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 2.1 (`spc:rem:oeis`)**: the OEIS sign error (next section).
- **Remark 10.5 (`spc:rem:transseries`)**: Section 10 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  (a) The core `H(X) = 2X log(X/e^κ) = y`, `X = e^{κ+W_0(y/(2e^κ))}`, is an
  instance of `p0:prop:factorial-core` (slope `2`, `d = −2κ`), **not** of
  `p0:thm:lambert-core` (whose phase `aX + b log X` is linear-logarithmic).
  (b) The coefficient recursion is an instance of `p0:thm:core-reversion`
  after the change of variable `E = δ/X`, with
  `h(u) = 2((1+u)log(1+u) − u)`. (c) The analytic step is the argument of
  `p0:thm:backward-error`. (d) The rounding of Corollary 10.3 is
  `p0:thm:staircase`(3). (e) Theorem 10.4 is proved directly and is not an
  instance as proved; a second route derives it from `p0:thm:staircase`(1)
  with the interpolation `F_M + (piecewise-linear residuals)` (proof
  included; the plain piecewise-linear interpolation of `log z_n` would give
  only `O(1/(x log x))`). No novelty is claimed for the inversion.
- Section 1.2 (provenance, the sources as the write read them, relation to
  the repository, collected non-claims, reading conventions), the note at
  the end of Section 11 (shipped layout, reruns), a note in the bibliography
  entry for `a139383`, and Section 12.1.

## The OEIS formula with the wrong sign

The live OEIS entry A005121 (revision #79 of 30 May 2026, read 5 October
2026, the revision the source inspected) has the formula line

    E.g.f. satisfies Z(z) = 1/2 * (Z(exp(z)-1) - z). [Lengyel]

It carries no contributor's signature or date. In the entry's history it
first appears in revision #8 of 13 September 2003 (an edit by N. J. A.
Sloane, with the asymptotic line), attributed "(Lengyel)"; revision #30
(18 April 2014) changed that to "[Lengyel]"; the sign has not changed since
2003. **The correct equation is `Z(z) = ½(Z(e^z − 1) + z)`.** One-line
proof: `n![zⁿ] Z(e^z − 1) = Σ_{k≤n} S(n,k) z_k`, which is `2z_n` for
`n ≥ 2` (by the recurrence and `S(n,n) = 1`) and `z_1 = 1` for `n = 1`;
so `Z(e^z − 1) = 2Z(z) − z`. With the printed minus sign the coefficient of
`z` reads `1 = ½(1 − 1) = 0`; Remark 2.1 proves that the printed equation
has exactly one formal solution, `−Z`, the e.g.f. of `(−1, −1, −4, −32,
−436, …)`. The same entry's PARI program (Somos, 2007) and
`a139383-iterated-bell-diagonals` (Part II, Section 17.2) use the correct
sign. Whether Lengyel's 1984 paper prints the minus sign was not checked.
This is recorded only; nothing was submitted to the OEIS.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.2):

- All orders are fixed: no convergence, Gevrey bound, optimal truncation or
  exponentially small remainder; no local limit theorem, Edgeworth expansion,
  large deviations or distributional error estimate.
- No interval-certified `C`, `K_1`, `K_2` or marked derivatives; no
  numerically efficient `A_M`; `A_M`, `Y_M` of Theorem 10.4 not evaluated;
  the exact inverse in the code is resource-bounded.
- No priority for the leading results (prior), for the correction
  coefficients or for the inversion machinery; Van Cutsem–Ycart's general
  variance conjecture is not resolved; the disk `|q − 1| ≤ 1/16` gives no
  global marked statement; the e.g.f. is formal.
- The literature check is "an inspected source boundary, not a
  worldwide-priority certificate"; the source does not claim that the
  ProveIt iterated-Bell results cannot imply aggregate statements.
- Cross-version byte identity of the rebuild is not promised.

The write adds: the numerical observation of Question 6 is a floating-point
extrapolation and certifies nothing.

## Further questions

Section 12.1 of the article ("Further questions and research",
`spc:sec:further`) states every unproved claim as an open question with its
source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). **Nothing in the source was found to be wrong**; the one error
recorded is in the OEIS entry.

1. **Certified constants** (`spc:q:certified`): the "effective in
   principle" sentences of Section 7 are a sketch; no explicit `A_M`.
   Theorem 1.1 gives `z_n/f_n = C(1 + L/(6n) + O(n⁻²))`, an asymptotic answer
   to Babai–Lengyel's convergence-speed question (as the source reports it).
2. **Dependence on the order** (`spc:q:order`).
3. **A larger marking region** (`spc:q:disk`).
4. **Distributional refinements** (`spc:q:distribution`).
5. **Comparison with analytic iteration, and priority** (`spc:q:analytic`):
   Prellberg's contour constant, the Flajolet–Salvy manuscript.
6. **Aggregate versus depth asymptotics** (`spc:q:depth`), the source's own
   question 6. Through the exact identity `z_n = Σ_m 2^{−m−1} H(n,m)`
   (`a139383`, Part II, Section 17.2) and that report's
   `ibd:pd:eq:factorial`, Laplace's method at `m = n/L` gives formally the
   scale `f_n` exactly and `C =? L^{L/3−1} I(L)/2 = D(1/L)/(2√(2π) L)`, with
   `a139383`'s amplitude `I`. *Observation at the write:* estimating `I(L)`
   from exact `H(n,m)` at the two `m` nearest `n/L` gives
   `L^{L/3−1}I(L)/2 ≈ 1.102044, 1.100861, 1.100269` at `n = 200, 300, 400`
   (excess over `C` about `0.65/n`); two-point extrapolation in `1/n` gives
   1.098494 and 1.098492, about `1.9·10⁻⁴` below `C`. Missing: tail bounds
   outside compact slopes, the logarithmic corrections of `a139383`, a
   certified `I(L)`.
7. **An evaluated inverse** (`spc:q:inverse`).
8. **Van Cutsem–Ycart's variance conjecture** (`spc:q:variance`), not
   resolved here.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4):

- At placement (batch-106 dossier): `test_lengyel_exact.py` (all PASS),
  `symbolic.py` and `diagnostics.py` regenerate `generated/*.txt` byte for
  byte up to Windows CRLF (2.3 min); `SHA256SUMS` 14/14. An independent
  program computed `z_n` to `n = 500`: `z_1, …, z_10` equal the OEIS terms,
  and `z_n/(f_n(1 + c_1/n + c_2/n² + c_3/n³))` = 1.0986858052222,
  1.0986858055062, 1.0986858055214, 1.0986858055240, 1.0986858055247 at
  `n = 100, …, 500`, within about `5·10⁻¹³` of the source's decimal of `C`.
  The OEIS sign error was confirmed in the live entry.
- At the write, route B below (copies of the shipped `code/`, SymPy 1.14.0,
  mpmath 1.3.0): the test program (8 PASS lines, 6 s), `symbolic.py` (106 s)
  and `diagnostics.py` (3 s) print outputs equal, after CRLF → LF, to the
  shipped `data/generated-*.txt` byte for byte. Route A on a fresh
  extraction of the archive: `build.py --verify-only` PASS and the test
  program PASS. The 11 staged files other than `README.md` and
  `article.tex` are byte-identical to the archive, and so were the staged
  `Report223.tex` and README in the placement commit.
- The dossier read the manuscript in full and checked Lemma 3.1's induction;
  the write rechecked identity (11), the six chain polynomials listed in
  Section 11.1 against `z_1, …, z_6`, and the OEIS history.
- Sources read by the write: OEIS A005121 (live entry and edit history);
  `a139383-iterated-bell-diagonals` (`article.tex` Part II, Section 17.2;
  `28-proportional-sources-literature.md`); the transseries volume
  (`p0:def:core`, `p0:prop:factorial-core`, `p0:thm:lambert-core`,
  `p0:thm:core-reversion`, `p0:thm:backward-error`,
  `p0:def:three-inverses`, `p0:thm:staircase`,
  `p0:prop:certified-rounding`). Not read by the write: Lengyel 1984,
  Babai–Lengyel, Prellberg, Mishna, Van Cutsem–Ycart, Finch, Dickey–Rosenberg
  (what the source read is fingerprinted in `data/SOURCES.json`).

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq; no formal file treats partition-lattice chains. Placement in the
collection confers no formal status.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a139383-iterated-bell-diagonals`:
  mentions A005121 only as background (its `article.tex` lines 909–910,
  Part II, Section 17.2: the depth-sum identity with the correct sign, and
  "a depth-summed equivalent alone does not give a pointwise
  proportional-depth equivalent"; its source note
  `28-proportional-sources-literature.md`, lines 139–141, records the known
  Lengyel asymptotic). Not a host: neither report answers a question of the
  other, and the methods differ (Stirling-kernel recurrence and contraction
  here; parabolic iteration and a Fatou-coordinate contour there).
  Question 6 here is the bridge. The source's bibliography credits that
  report to "V. Reshetnikov", but it has no author line ("A merged research
  report built from two manuscripts"); it is cited here by path. Its article
  blob is still `ab5014ec`, the one the source inspected.
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`:
  Remark 10.5 says exactly which statements of Section 10 are instances
  (`p0:prop:factorial-core`, `p0:thm:core-reversion` after `E = δ/X`,
  `p0:thm:backward-error`, `p0:thm:staircase`(3)) and which is proved
  directly (Theorem 10.4; a second route via `p0:thm:staircase`(1)).

**Stale claims.** Before batch 106 the repository mentioned A005121 only in
`a139383` (as above) and never A086053 or A008826. The source says nothing
false about the repository; its attribution of `a139383` is corrected by a
dated note.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `z_n`, `Z_n(q)` (versus `a139383`'s depth
sum `Z_n`, same numbers); `𝒵(z)` versus the OEIS's `Z(z)`; `H` (chain
length) versus `a139383`'s `H(n,m)`, the function `H(x)` of Section 10 and
`H_{e,k}(t)`; `L`, `L(q)`; `b` versus the `b` of `p0:thm:lambert-core`;
`C`, `C(q)`, `C_M`, `C_e(k)`; `K(n,k)`, `K = 2πC`, `K_1`, `K_2`; `T_r(L)`
(Touchard) versus `T_r(n)` (a weighted norm); `d`, `d_n`, `d_j`; `e`;
`κ = 1 + ½log(2L)` versus the cumulants `κ_r` and the slope `2` of
`p0:prop:factorial-core`; `β = L/3` versus `a139383`'s `β = n/m`; the
constants `A, B, R` versus `A(t), B(t), D(t)` and the disks `D_0`, `D`;
`Λ, w, X, U, v_m`; `N(y)` (a threshold on `log z_n`). No symbol was renamed.

## Labels

Every label carries the prefix `spc:` (none existed in the repository). The
manuscript's 78 labels (`eq:` 55, `sec:` 11, `thm:` 4, `lem:` 3, `cor:` 3,
`prop:` 2) were prefixed before anything cited them, and the 59 references to
them were updated. The write added 13: `spc:sec:meaning` (the delivered
Section 1.1, unlabelled before), `spc:sec:provenance`, `spc:rem:oeis`,
`spc:rem:transseries`, `spc:sec:further`, and the questions
`spc:q:certified`, `spc:q:order`, `spc:q:disk`, `spc:q:distribution`,
`spc:q:analytic`, `spc:q:depth`, `spc:q:inverse`, `spc:q:variance`. The
report has 91 labels; a build of the delivered text and of this one give all
78 delivered labels the same numbers (aux files compared). The added remarks
are the last statements of their sections and the added displays are
unnumbered, so no theorem or equation number moved.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered Report223.tex; labels prefixed, [write] additions)
article.pdf                        compiled report, 26 pages
code/lengyel_exact.py              standard-library exact core and CLI (delivered code/)
code/test_lengyel_exact.py         exact tests, full poset enumeration n <= 6, real CLI tests (delivered code/)
code/symbolic.py                   SymPy coefficient, cumulant and inverse algebra (delivered code/)
code/diagnostics.py                mpmath diagnostics, not certified (delivered code/)
code/build.py                      offline rebuild and inventory check (delivered at the package root)
data/SOURCES.json                  source URLs, inspected scope, SHA-256 fingerprints (delivered at the root)
data/requirements-optional.txt     sympy==1.14.0, mpmath==1.3.0 (delivered at the root)
data/generated-exact_checks.txt    recorded output of the test program (delivered generated/exact_checks.txt)
data/generated-symbolic.txt        recorded output of symbolic.py (delivered generated/symbolic.txt)
data/generated-diagnostics.txt     recorded output of diagnostics.py (delivered generated/diagnostics.txt)
data/generated-toolchain.json      recorded toolchain versions (delivered generated/toolchain.json)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report223.pdf` (the delivered 19-page PDF, 382,549 bytes); `SHA256SUMS`
(1,197 bytes, a SHA-256 inventory of the other 14 files; repository policy
ships no checksum manifests; verified at placement and again by
`build.py --verify-only` at the write); and the delivery `README.md`
(10,306 bytes), staged at placement and replaced by this guide (summarized
under "From the delivery README").

**Delivered text that names the delivery layout or files not shipped.**
`code/build.py` hard-codes the package root and a closed inventory
(`Report223.tex`, `README.md`, `SOURCES.json`, `requirements-optional.txt`,
`build.py`, `code/*.py`, `Report223.pdf`, `generated/*`, `SHA256SUMS`): **it
does not run in this directory**, and its `README.md` entry refers to the
delivered README. `data/SOURCES.json` and Section 11 of the article speak of
"the README" (the delivered one) and "the archive". The four programs in
`code/` need no layout.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report223.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # c178191805f950bdf5f73d7d41cb0f1932811debf579d6c6df15b6e9cf2b8f25, 509,137 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 15 files are at the archive root
```

## Rerun the checks (on a scratch copy)

Python 3.11 or later. The exact core and tests need only the standard
library; `symbolic.py` needs SymPy, `diagnostics.py` mpmath (versions in
`data/requirements-optional.txt`). Always use `-B` (bytecode files count as
unexpected package members for `build.py`). Never run anything in the
repository.

**Route A, delivered layout** (tested at the write: `--verify-only` and the
test program):

```sh
cd "$T/pkg"
python3 -B build.py --verify-only                  # PASS complete package inventory and SHA256SUMS
python3 -B code/test_lengyel_exact.py              # about 6 s
python3 -B -O code/test_lengyel_exact.py
python3 -B code/symbolic.py                         # about 2 minutes
python3 -B code/diagnostics.py
```

The full rebuild (`python3 -B build.py --output ../rebuilt-normal`, a new
sibling directory) needs pdfTeX and the recorded TeX Live toolchain to
reproduce the archive byte for byte; it was not run by the intake.

**Route B, from the shipped programs** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a005121-strict-partition-chains
T=$(mktemp -d); cp "$R"/code/*.py "$T/"; cd "$T"
python3 -B test_lengyel_exact.py > exact.txt && cmp exact.txt "$R/data/generated-exact_checks.txt"
python3 -B symbolic.py > symbolic.txt && cmp symbolic.txt "$R/data/generated-symbolic.txt"
python3 -B diagnostics.py > diagnostics.txt && cmp diagnostics.txt "$R/data/generated-diagnostics.txt"
```

On Windows standard output has CRLF line ends; strip them
(`tr -d '\r'`) before comparing. Use `py` where `python3` is not on the path.
The exact CLI examples of the delivery README (`value`, `sequence`,
`polynomial`, `moments`, `inverse`) run the same way, for example
`python3 -B lengyel_exact.py inverse 9013 --max-n 20` prints 7.

## Build the PDF

pdfLaTeX (fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, microtype, hyperref, enumitem); the bibliography
is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026: 26
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 19 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report223.tex` under the delivering toolchain, not to this
build.

## From the delivery README

The delivery README (replaced by this guide) described "a self-contained
mathematical article on OEIS A005121, with exact code and a reproducible PDF
and source archive". It summarized the scope (every fixed order; `c_1`–`c_4`;
the disk `|q − 1| ≤ 1/16`; cumulants; inverse with "an error interval of
width less than one before claiming adjacent candidates"), the prior results
and non-claims above, and the OEIS sign ("the exact recurrence gives
`2 Z(z) = z + Z(exp(z)-1)`. No external source was modified"). It listed the
15 archive members; the resource limits of the exact core (values and
inverses `n ≤ 1000`, chain polynomial `n ≤ 150`, moments `n ≤ 600` and order
`≤ 12`, inverse targets of at most 6000 digits, symbolic orders 1–4), which
are "implementation bounds, not mathematical limitations"; the test
commands, including `PYTHONINTMAXSTRDIGITS=640 python -B -O`, and what they
check (every partition, comparable pair and chain for `n ≤ 6`, factorial
domination for all 5050 pairs through `n = 100`, `z_200` with 719 digits
through the real CLI); that `generated/diagnostics.txt` "is explicitly
non-certified" and tests the inverse with a free `K = 7`; the deterministic
rebuild (`--verify-only`, `--output`, byte comparison of whole archives,
`ARTIFACT_SHA256SUMS` beside the archive, which is not part of the package);
and that `SOURCES.json` keeps both raw-file and "connector-returned" text
hashes for the two ProveIt files, which differ by one terminal LF byte.
"Source fingerprints do not license redistribution."

## Rights

Repository contents are MIT-0. The article and the recorded outputs quote
OEIS terms of A005121 and its formula line; OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
those terms remain under that licence. No third-party PDF is shipped.
Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A005121; Lengyel, Europ. J. Combin.
  5 (1984) 313–321; Babai and Lengyel, Analysis 12 (1992) 109–119;
  Prellberg, FPSAC 2002 presentation; Mishna's summary in Algorithms Seminar
  2002–2004; Van Cutsem and Ycart, Adv. Appl. Probab. 26 (1994) 988–1005;
  Finch, Mathematical Constants (2003), Section 5.7; Dickey and Rosenberg,
  arXiv:2511.16799 / Discrete Appl. Math. (2026); this repository's
  `a139383-iterated-bell-diagonals` and transseries collection, pinned at
  `9f19e58de`.
- Batch 106 of `docs/incoming`, bundle Report 223; arrival `60f54ea06`,
  placement `47fc7a069`, written 5 October 2026. Single source, so no merge
  choices. The delivered `Report223.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
