# L-convex Polyominoes and a Colored-Partition Comparison

**A proof of the A126764 asymptotic, three correction terms, an all-orders
radial expansion, and inverse asymptotics (OEIS A126764)**

A research report dated 1 October 2026, built from one manuscript (author
line: "Research manuscript prepared for Vladimir Reshetnikov"; its PDF
metadata and delivery README say "prepared with ChatGPT").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 05 | `A126764_Lconvex_Research.zip`, arrival commit `4b874cea0` (main file `lconvex_asymptotics.tex`, now `article.tex`; its PDF and `manifest.json` not shipped) | none: no ProveIt commit is named; the repository input was an overview and a targeted A126764 search on 1 October 2026 | `6ea60e367` | the whole report |

**Status:** AI-assisted (prepared with ChatGPT), unrefereed, not
formalized. Exact integer checks through `n = 2000` and symbolic checks
corroborate the identities and constants; no numerical fit enters the
proofs.

## What it proves

`a_n` counts fixed L-convex polyominoes of area `n` (OEIS A126764,
`a_0 = 1`). Put `K = 13π²/24`, `B = 2√K = π√(13/6)`, `c = 13√2/768`.

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

## What is not claimed

- The area generating function (Castiglione–Frosini–Munarini–Restivo–Rinaldi
  2007, in the recurrence form of Guttmann–Kotěšovec) is a cited input.
- No exhaustive priority search; a targeted search found no earlier proof.
- **No all-orders coefficient expansion and no exponentially small sectors**
  for `a_n`: the radial expansion is not a coefficient expansion (Section 8.2
  of the article says why). No numerical universal error constants, hence
  no certified integer inversion near a threshold.
- No four-to-one combinatorial map behind `p_n >= 4a_n`; perimeter
  enumeration and 201-avoiding ascent sequences are not addressed.
- Numerical tables are diagnostics, not proof. Not all 2001 computed
  coefficients were compared with an external source: the first 37 OEIS
  terms and four b-file anchors were.
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** Its core `s - 3 log s = ℓ` is
  `p0:thm:lambert-core` (`a = 1`, `b = -3`, branch `W_{-1}`), its correction
  is `p0:thm:lambert-centered`, and the shape is that of the partition
  chapter `p3:sec:lambert` / `p3:thm:core-correction` (there `b = -2`); the
  rounding remark is `p0:thm:staircase` (1)–(2), as in `p3:thm:staircase`.
  All are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note in Section 9 says so.
- The eight research directions of Section 11 are questions, not results.
- No OEIS edit was made.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase lemmas named in
Section 9 are formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; they
concern an arbitrary monotone interpolation, not `a_n`.

**Stale sentence.** Section 1.1 says a targeted repository search for
A126764 returned no matching file. That was true at the inspection; the only
match now is this report (dated note added).

**Neighbouring reports.**
`enumerative-combinatorics/polyomino-growth-finite-prefix-corrections`
bounds **Klarner's constant** for all polyominoes (`λ <= 2249/500`; its Lean
project `Combinatorics/Polyominoes/KlarnerConstant` proves
`λ <= 9047/2000`). That is an exponential growth rate of a different
class; L-convex polyominoes grow like `e^(B√n)`, so the constants are
unrelated and no theorem is shared. `enumerative-combinatorics/skew-partition-continued-fractions`
touches parallelogram polyominoes (A006958) only. Among the OEIS-sequence
asymptotics reports, the closest in method are the partition-type
`e^(C√n)` reports such as `a022629-distinct-partition-norms` and
`a097356-sqrt-restricted-partitions`; they treat different products. (These
pointers are made here only; those reports are not edited by this write.)

## Labels

Every label carries the prefix `lcp:`. The manuscript's 59 labels were
prefixed before anything cited them (9 `\ref` and 60 `\eqref` updated); no
label was added, so the count is 59. Three dated `[write]` notes were added
(Section 1.1: provenance, pin, formal status, neighbours; Section 9.2: the
instance note; Appendix A: layout and rerun), with two bibliography entries
(`lcp-tai`, `lcp-klarner`), and the bibliography was set ragged-right to
avoid underfull lines from the long repository paths. No statement, proof
or number of the manuscript was changed.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered as lconvex_asymptotics.tex)
article.pdf                  compiled report, 20 pages
code/verify.py               exact integer checks (standard library); writes into --out
code/verify_symbolic.py      SymPy/mpmath checks; reads and writes checks/ beside itself
data/coefficients.csv        n, a_n, p_n, p_n - 4a_n, j_n for 0 <= n <= 2000 (CRLF)
data/verification.json       verify.py summary (37 OEIS terms, b-file anchors 50, 100, 200, 500, eight checks)
data/exact_checks.txt        recorded verify.py stdout
data/numerical_table.csv     ratio and deficit diagnostics at n = 50 ... 2000 (CRLF)
data/expanded_table.csv      truncation and inverse diagnostics at n = 50 ... 2000 (CRLF)
data/symbolic_checks.txt     Q_3, h_3, the radial series through t^8, the correction coefficients
data/symbolic_run.txt        recorded verify_symbolic.py stdout
data/requirements.txt        sympy==1.14.0, mpmath==1.3.0 (only for verify_symbolic.py)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed
`lconvex_asymptotics.tex` to `article.tex`, moved the delivered `checks/`
directory to `data/` and the scripts to `code/`, and moved
`requirements.txt` from the package root to `data/`. Not shipped: the
delivered PDF and `manifest.json` (a SHA-256 ledger with a page count;
verified 13/13 at placement). The three CSVs have CRLF line endings as
delivered (Python's `csv` writer) and keep them through `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The scripts call the constant `K` of
the article `A`. Delivered text that names the delivery layout: the
article's Appendix A (`lconvex_asymptotics.tex`, `--out checks`, the
compiled PDF; dated note added) and `code/verify_symbolic.py` itself, whose
paths `checks/coefficients.csv`, `checks/symbolic_checks.txt` and
`checks/expanded_table.csv` are fixed relative to the script.

## Rerun the checks (on a scratch copy in the delivered layout)

`verify.py` writes into `--out` (default `checks`, relative to the working
directory). `verify_symbolic.py` reads `checks/coefficients.csv` and writes
`checks/symbolic_checks.txt` and `checks/expanded_table.csv` **next to
itself**, so it cannot run from `code/` as shipped, and running `verify.py`
with `--out data` here would overwrite shipped files. Recreate the delivered
layout in a scratch directory (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir "$R/checks" && cp code/*.py "$R" && cd "$R"
uv run --no-project python verify.py --nmax 2000 --out checks > checks/exact_checks.txt
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify_symbolic.py > checks/symbolic_run.txt
```

Run `verify.py` first (it produces the CSV the symbolic checker reads). Do
not use `python -O` (the checks are assertions). Then compare `checks/`
with `data/`. On 2 October 2026 the two commands took 3 s and 7 s here, all
assertions passed, `coefficients.csv`, `numerical_table.csv` and
`expanded_table.csv` came out byte-identical, and `verification.json`,
`exact_checks.txt`, `symbolic_checks.txt` and `symbolic_run.txt` identical
modulo line endings (Windows writes CRLF).

## Build the PDF

pdfLaTeX with newpxtext/newpxmath, amsmath, amsthm, mathtools, microtype,
booktabs, longtable, enumitem, fancyhdr, tcolorbox and hyperref. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 20 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. (The delivered source
built to 19 pages with the same clean log.)

## Provenance

- OEIS A126764 and its b-file (accessed 1 October 2026); Castiglione,
  Frosini, Munarini, Restivo, Rinaldi, Eur. J. Combin. 28 (2007);
  Guttmann–Kotěšovec, Sém. Lothar. Combin. 87B (2023), arXiv:2109.09928 v3;
  DLMF §27.14; Guttmann–Massazza (Z-convex, cited only as a research target).
- Repository input: an overview and a targeted A126764 search, no commit
  recorded.
- Batch 75 of `docs/incoming`, manuscript 05; arrival `4b874cea0`, placement
  `6ea60e367`, written in the batch-75 write phase (2 October 2026).
