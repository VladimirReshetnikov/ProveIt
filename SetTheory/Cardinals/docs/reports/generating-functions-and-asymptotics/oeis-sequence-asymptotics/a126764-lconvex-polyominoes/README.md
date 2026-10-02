# L-convex Polyominoes and a Colored-Partition Comparison

**A proof of the A126764 asymptotic, three correction terms, an all-orders
radial expansion, and inverse asymptotics (OEIS A126764). Part II: the
all-orders coefficient theorem**

A research report dated 1 October 2026, built from two manuscripts, each
printed in full. Part I's author line is "Research manuscript prepared for
Vladimir Reshetnikov"; its PDF metadata and delivery README say "prepared
with ChatGPT". Part II's author line is empty and it names no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 05 | `A126764_Lconvex_Research.zip`, arrival commit `4b874cea0` (main file `lconvex_asymptotics.tex`; its PDF and `manifest.json` not shipped) | none: no ProveIt commit is named; the repository input was an overview and a targeted A126764 search on 1 October 2026 | `6ea60e367` (written in `936896776`) | Part I: Sections 1–12, Appendices A–B |
| 02 | batch 77, manuscript 31 | `lconvex-asymptotics-reproducibility.zip`, arrival commit `096ee7b87` (*All order asymptotics and inversion for L convex polyominoes*, main file `article/lconvex-asymptotics.tex`, 11-page PDF; manuscript, PDF, README and manifest not shipped) | none: no ProveIt commit is named and the repository is not mentioned | `4f11bc9c0` | Part II: Sections 13–23 (13 and 23 editorial) |

**Status:** AI-assisted, unrefereed, not formalized. Part I is backed by exact
integer checks through `n = 2000` and symbolic checks, Part II by an exact
replay through `n = 2000` and `q^96`. These checks corroborate the
identities and constants; no numerical fit enters either proof. Part II's
three shipped reviews are the delivery's own internal checks, not external
peer review.

The two manuscripts were written independently. Part II is not a version of
Part I: only 40 of its 380 distinct non-blank source lines occur in Part I's
source, and it uses another proof architecture. Results proved in both are
printed in both parts, each with its own proof, and cross-referenced
(Section 13.2).

## What it proves

`a_n` counts fixed L-convex polyominoes of area `n` (OEIS A126764,
`a_0 = 1`). In Part I's letters, `K = 13π²/24`, `B = 2√K = π√(13/6)` and
`c = 13√2/768`. Part II calls these constants `κ`, `2√κ` and `C`; see
"Notation" below.

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

## What is not claimed

- The area generating function (Castiglione–Frosini–Munarini–Restivo–Rinaldi
  2007, in the recurrence form of Guttmann–Kotěšovec) is a cited input of
  both parts.
- Neither part made an exhaustive priority search; targeted searches found
  no earlier proof. Part II says that the final display of Section 2 of
  Guttmann–Kotěšovec prints the reciprocal of `C`. This was **not checked at
  intake**; its shipped audit says the same, but that audit is the
  delivery's own review.
- **No exponentially small sectors and no complete transseries** for `a_n`.
  Part II's bound on the exact remainder is deliberately coarse. Part I
  disclaimed an all-orders coefficient expansion; Part II now proves it.
  Part I's Section 8.2, research question 1 and claim ledger carry dated
  notes saying so.
- No numerical universal error constants, so neither part certifies an
  integer inversion near a threshold. Part II's bracket constants and its
  log-concavity threshold are existential, and no finite starting index is
  given.
- No convergence, optimal truncation or resummation of the formal series
  (Part II, open problem 3). No modularity claim for `B`.
- No four-to-one combinatorial map behind `p_n >= 4a_n`; perimeter
  enumeration and 201-avoiding ascent sequences are not addressed.
- Numerical tables are diagnostics, not proof. Of the 2001 computed
  coefficients, only the first 37 OEIS terms and four b-file anchors were
  compared with an external source. The two parts compute the same 2001
  integers by different recurrences.
- **Both inversions are instances of repository results, and no novelty is
  claimed for the method.** Part I's core `s - 3 log s = ℓ` and Part II's
  core `y_0 - 3 log y_0 = L` are `p0:thm:lambert-core` (`a = 1`, `b = -3`,
  branch `W_{-1}`). Their corrections are `p0:thm:lambert-centered` and
  `p0:thm:perturbed-inversion`. Part I's rounding rule and Part II's integer
  brackets are `p0:thm:staircase` (1)–(2). The shape of the argument is that
  of the partition chapter `p3:sec:lambert` / `p3:thm:core-correction`. All
  of these are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  Dated `[write]` notes in Sections 9.2 and 20 say so.
- The research directions of Section 11 (eight) and Section 22 (five) are
  questions, not results.
- Some proofs in Part II are sketched to the level of standard estimates:
  the whole-circle bounds of Lemma 17.1 and the minor arcs of Lemma 17.3.
  Its shipped mathematical audit, items 6–8, spells them out.
- No OEIS edit was made.

## Notation

Part II keeps its manuscript's letters, because its shipped data and reviews
use them. Many of them clash with Part I. Table 1 (Section 13.3) lists every
clash, with the tempting false reading. The dangerous ones are these:

- Part II's `P` is Part I's `R`, the Euler product.
- Part II's `R` is the exact remainder, which has no counterpart in Part I.
- Part II's `κ` is Part I's `K`, and Part II's `K = C(2√κ)³` is Part I's
  `cB³`.
- Part II's `B(q) = D(q)` is a partial theta function. Part I's `B` is the
  constant `2√K`, and Part I's `D(q) = L/R` is the same function as Part
  II's `B(q)`.
- Part II's `p_n = [q^n]PB² ~ a_n`; Part I's `p_n = [q^n]R ~ 4a_n`.
- Part II's `N = n - 1/6`; Part I's `N(y)` is the threshold index.

No symbol was renamed and no normalization changed. Write notes in Part II
mark a clashing Part I object with a superscript `I`.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq. Its place in the collection gives it no formal status, and neither
manuscript used a ProveIt theorem. The generic staircase lemmas named in
Sections 9.2 and 20 are formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
They concern an arbitrary monotone interpolation, not `a_n`.

**Stale sentence.** Section 1.1 says that a targeted repository search for
A126764 returned no matching file. That was true at the inspection; the only
match now is this report (dated note added).

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
`a097356-sqrt-restricted-partitions`, which treat different products. These
pointers are made here only; those reports are not edited.

**Ascent sequences (batch 77, dated 2 October 2026).** Section 1.1 leaves
the asymptotics of 201-avoiding ascent sequences, which Guttmann and
Kotěšovec discuss beside L-convex polyominoes, to other work. The sibling
report `a202062-ascent-201-enumeration` (batch 77P1) proves their cubic
generating function for A202062 and its all-orders asymptotics; the two
problems share only the Guttmann–Kotěšovec paper (dated note in
Section 1.1).

## Labels

Part I's labels carry the prefix `lcp:`. The manuscript's 59 labels were
prefixed in batch 75 before anything cited them. Part II's labels carry the
prefix `lcp:ao:`: the manuscript's 50 labels, plus 15 added in writing (12
section and subsection labels, the notation table and two remarks). The report now has
124 labels, and no earlier label was renamed or removed.

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

## Files

```text
README.md                                     this guide (replaces both delivery READMEs)
article.tex                                   the report (Part I delivered as lconvex_asymptotics.tex; Part II's
                                              manuscript lconvex-asymptotics.tex is printed inside it)
article.pdf                                   compiled report, 39 pages
02-all-orders-mathematical-audit.md           Part II's internal analytic audit of its proof note (as delivered)
02-all-orders-final-source-review.md          Part II's internal review of its final source (as delivered)
02-all-orders-computational-review.md         Part II's code and reproducibility review (as delivered)
code/verify.py                                Part I: exact integer checks (standard library); writes into --out
code/verify_symbolic.py                       Part I: SymPy/mpmath checks; reads and writes checks/ beside itself
code/02-all-orders-replay.py                  Part II: exact replay (standard library), optional SymPy/mpmath extras
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

## Rerun the checks (on a scratch copy in the delivered layout)

The scripts of both parts expect their delivered layouts, and running them in
place would either fail or overwrite shipped files. Use scratch copies (Git
Bash, from this directory).

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
CRLF).

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

## Build the PDF

pdfLaTeX with newpxtext/newpxmath, amsmath, amsthm, mathtools, microtype,
xcolor, booktabs, array, longtable, enumitem, fancyhdr, tcolorbox and
hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory. It has 39 pages, with
no errors, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, and no overfull or underfull boxes. Part I
alone built to 20 pages in batch 75.

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
- Where the merge had to choose (Section 23):
  - Part II goes after Part I's closing Section 12 and before its
    appendices, so no Part I number moves.
  - Letters are kept, with a clash table, rather than renamed.
  - Duplicated results keep both proofs.
  - Four of Part II's five references were merged into Part I's entries;
    its DLMF entry stays separate.
