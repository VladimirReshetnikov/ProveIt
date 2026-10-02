# Ordered Long Jump Rook Paths

**Exact coefficient identities and fixed dimension asymptotics (OEIS
A227578 and its fixed-`k` columns A059231, A227580, A227583, A227596)**

A research report dated 2 October 2026, built from one manuscript. Its
author line is empty; the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 58 | `ordered-rook-reproducibility.zip` (wrapper directory `ordered-rook-report/`), arrival commit `096ee7b87`; main file `ordered_rook_paths.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. The delivered `VALIDATION.md` records
"an independent integrated review", which it calls "ordinary mathematical
review, not a proof-assistant certificate"; exact-arithmetic and numerical
checks corroborate the finite algebra only.

## What it proves

`A(n,k)` counts paths from `(n,…,n)` to the origin in `k` dimensions that
decrease one coordinate by an arbitrary positive integer at each step (a
"rook step") and stay weakly ordered, `p_1 ≤ … ≤ p_k` (OEIS A227578;
`A(0,k) = A(1,k) = 1`, so the counts are nondecreasing, not strictly
increasing).

- **Proposition 2.2 (exact identities).** A boundary-tail equation, a
  weighted orbit sum and a diagonal-support exclusion lemma give, for all
  `n ≥ 0`, `k ≥ 2`,
  `A(n,k) = ((-1)^p/k!) [x_1^N … x_k^N] Δ(x)^2 / (H(x) Π(1-x_i)^(k-1))`,
  `N = n+k-1`, `p = k(k-1)/2`, `H = 1 - Σ x_i/(1-x_i)`. Consequence: each
  fixed-`k` generating function is D-finite (Lipshitz), so some polynomial
  recurrence exists; no posted OEIS recurrence is certified.
- **Theorem 1.1 (all fixed orders).** For each fixed `k ≥ 2` and `M`,
  `A(n,k) = C_k Λ^n n^(-α) (Σ_{j<M} d_j(k) n^(-j) + O(n^(-M)))`,
  `Λ = (k+1)^k`, `α = (k²-1)/2`, with `C_k` in closed form (a
  superfactorial times powers of `k`, `k+1`, `k+2`, `2π`) and
  `d_1(k) = -(k-1)(k+1)(2k^4+8k^3+9k^2+6k+12)/(12k(k+2)^2)`
  (`d_1(2) = -39/32`, `d_1(3) = -326/75`). Method: the Raichev–Wilson
  smooth-point theorem at the strictly minimal point `x_i = 1/(k+1)`, a
  trace-zero Gaussian Vandermonde (Mehta-type) integral.
- **Theorem 5.1 (finite generator).** `d_j(k)` is an explicit finite
  Gaussian–Vandermonde expectation of a coefficient of a normalized
  amplitude; rational for every fixed `k, j`.
- **Proposition 7.1, Corollary 7.2.** `d_2(k)` in closed form (a degree-12
  polynomial over `288k^3(k+2)^5`), via a trace-moment integration-by-parts
  recursion; every `d_j(k)` is one rational function of `k` with possible
  poles only at `0, -1, -2`.
- **Section 8 (inverse).** A Lambert-`W_{-1}` inverse of the named model
  `C e^{Lx} x^{-α}`, `L = k log(k+1)`, with recursive corrections
  (Proposition 8.1, a specified-model inverse), and a two-ceiling enclosure
  of the integer threshold `N_k(M) = min{n : A(n,k) ≥ M}` with non-effective
  constants (Corollary 8.2).

## What is not claimed

Kept from the manuscript and its package:

- The general fixed-`k` scale is an OEIS conjecture and the `k = 2, 3, 4, 5`
  leading constants are prior OEIS statements (Kotěšovec, 2013–2016); orbit
  sums, smooth-point asymptotics, Gaussian Vandermonde integration, Wick
  expansion and Lambert inversion are credited as classical.
- The stated contribution is the boundary-tail derivation of the symmetric
  identity for this infinite-step model and the explicit fixed-order and
  inverse calculations; "a bounded literature observation, not a claim of
  worldwide novelty". The Bostan–Bousquet-Mélou–Melczer finite-step
  framework is not invoked as a theorem for infinite rook steps; the
  Denisov–FitzGerald harmonic determinant is prior machinery, and their
  simultaneous-update process is not identified with this model.
- No uniformity in growing `k`, no convergence of the full expansion, no
  exponentially small terms, no effective remainder constants, no certified
  posted recurrence, no algebraicity for `k ≥ 3`, no canonical real
  interpolation of the sequence, and no certified integer threshold (the
  continuous inverse is "not a certified integer threshold").
- Numerical tables are illustrations; a truncated correction can be poor or
  negative at moderate `n`.
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** Its leading term solves
  `Lx - α log x = log(M/C)`: `p0:thm:lambert-core` with `a = L = k log(k+1)`,
  `b = -α`, branch `W_{-1}`. Its recursion is `p0:thm:lambert-centered`
  with `Q(t) = Σ ℓ_j t^j`, and its first three coefficients coincide with
  `t2:eq:balanced-first` of `t2:thm:balanced-inverse` (`a = L`,
  `β = -α`). The two-equal-ceilings remark is the separation condition,
  part (2) of `p0:thm:staircase`; part (1) (exact rounding) does not apply,
  because the model is not an interpolation of `A(n,k)`. The two volumes are
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  and
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`.
  A dated `[write]` note at the end of Section 8 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase arithmetic named
in the Section 8 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern an arbitrary monotone function, not `A(n,k)`.

**Neighbouring reports.** None shares a result. The intake searched the
collection, the transseries volumes, `Oeis/` and `docs/reports/` for the
five OEIS numbers and for the objects, without truncation, and found
nothing beyond this report. "Rook" elsewhere in the collection means rook
polynomials (non-attacking rook placements on a board), in
`oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson` and
`a000382-winding-correction`; the batch-77 report
`a201513-sparse-chess-placements` counts non-attacking king and knight
placements. Those are different objects; a note in Section 1 says so.

## Notation

The manuscript reuses letters with section-local meanings (`M` a
truncation order in Theorem 1.1 but a target count in Section 8; `N` the
extraction index `n+k-1` and the threshold `N_k(M)`; `μ = (k+1)/k^2` a
derivative, not a growth rate (the growth rate is `Λ = (k+1)^k`); `d = k-1`
vs `d_j(k)`; `a`, `b`, `B`, `D`, `G`, `H`, `J`, `K`, `P`, `R`, `T`, `σ`, `λ`
two or more ways each). A table in the Section 1 `[write]` note fixes each
by section, with the tempting false readings. No symbol was renamed.

## Labels

Every label carries the prefix `orp:`. The manuscript's 51 labels were
prefixed before anything cited them (56 `\ref`/`\eqref` targets updated),
and seven section labels `orp:sec:…` were added for the notes: 58 labels in
all. The writing step also added three dated `[write]` notes (Section 1:
provenance, the other meanings of "rook", notation table; Section 8: the
instance note; Section 9: the files in the collection), two bibliography
entries (`orp-tai`, `orp-cti`), and set the bibliography ragged-right. No
statement, proof, number or table of the manuscript was changed.

## Files

```text
README.md                              this guide (replaces the delivery README)
SOURCES.md                             delivered source and version notes (as delivered)
VALIDATION.md                          delivered verification scope and limitations (as delivered)
article.tex                            the report (delivered as ordered_rook_paths.tex)
article.pdf                            compiled report, 18 pages
code/generate_coefficients.py          exact finite generator for d_0..d_J (integer or symbolic k); --output FILE
code/evaluate_model.py                 forward and specified-inverse models through two corrections (stdout)
code/check_models.py                   direct rook DP vs weighted unit words, k=1..5, n=0..8 (stdout)
code/check_unsymmetric.py              direct counts vs the unsymmetric identity (stdout)
code/check_symmetric.py                direct counts vs the symmetric identity; writes symmetric-checks.json
code/check_first_correction.py         symbolic d_1(k); writes first-correction-check.json
code/check_wick.py                     Wick contractions; writes root-gue-check.json
code/check_radial_and_wick.py          radial root and Wick checks; writes radial-wick-checks.json
code/check_second_pairings.py          d_2(k) from Wick pairings; writes second-correction-pairings.json
code/check_second_independent.py       d_2(k) by integration by parts; writes second-independent-check.json
code/check_saddle_k3.py                k=3 eliminated-coordinate chart, first correction; writes saddle-k3-check.json
code/check_saddle_k3_order2.py         the same chart, second correction; writes saddle-k3-order2-check.json
code/check_inverse.py                  formal inverse cancellation through degree 4; writes inverse-checks.json
code/check_numerics.py                 recurrence-free counts and errors; writes direct-numerics.json
code/verify_manifest.py                checks MANIFEST.sha256 (not shipped; see below)
code/safe_extract.py                   delivered ZIP extraction helper
code/replay.sh                         the delivered full replay (delivered layout only; see below)
code/build.sh                          the delivered PDF build (expects ordered_rook_paths.tex beside it)
data/model-checks.json                 recorded check_models.py output
data/unsymmetric-checks.txt            recorded check_unsymmetric.py output
data/symmetric-checks.json             recorded check_symmetric.py result file
data/symmetric-checks.txt              recorded check_symmetric.py stdout
data/first-correction-check.json       recorded check_first_correction.py result
data/root-gue-check.json               recorded check_wick.py result
data/radial-wick-checks.json           recorded check_radial_and_wick.py result
data/second-correction-pairings.json   recorded check_second_pairings.py result
data/second-independent-check.json     recorded check_second_independent.py result
data/saddle-k3-check.json              recorded check_saddle_k3.py result
data/saddle-k3-order2-check.json       recorded check_saddle_k3_order2.py result
data/inverse-checks.json               recorded check_inverse.py result
data/direct-numerics.json              recorded check_numerics.py result (12 exact counts, n up to 100)
data/generator-k2-order2.json          generate_coefficients.py --k 2 --order 2
data/generator-k3-order2.json          generate_coefficients.py --k 3 --order 2
data/generator-symbolic-order2.json    generate_coefficients.py --k symbolic --order 2
data/inverse-example.json              evaluate_model.py inverse --k 3 --target 1e100 --order 2
data/forward-example.json              evaluate_model.py forward --k 3 --n 80 --order 2
data/numerical_table.tex               the article's table (\input by article.tex from this path)
data/requirements.txt                  sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `ordered_rook_paths.tex`
to `article.tex`, moved `replay.sh`, `build.sh` and `safe_extract.py` from
the package root to `code/` (the other scripts were already there), and
`requirements.txt` from the root to `data/`; `data/` kept its delivered
name, so the article's `\input{data/numerical_table.tex}` still resolves.
Not shipped: the delivered 16-page PDF `ordered_rook_paths.pdf` and
`MANIFEST.sha256` (a checksum ledger, verified 43/43 at placement). Both
survive in the archive:
`git show 096ee7b87:docs/incoming/ordered-rook-reproducibility.zip > <scratch>/ordered-rook-reproducibility.zip`.
No delivered file was excluded for size (the largest support file is
6.2 KB).

`data/numerical_table.tex` is produced by no shipped script; its eight rows
are eight of the twelve rows of `data/direct-numerics.json` (all but
`(k, n) = (2, 25), (3, 20), (4, 20), (5, 5)`), rounded to six decimals
(checked at intake: all eight agree).

Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` (changes to its own directory, then calls
`code/verify_manifest.py`, `build.sh` and `ordered_rook_paths.pdf` relative
to it, so it cannot run from `code/`); `code/build.sh` (compiles
`ordered_rook_paths.tex` in its own directory); `code/verify_manifest.py`
(reads `MANIFEST.sha256` from the parent of `code/`, i.e. this directory,
where it is not shipped); `code/safe_extract.py` and the delivery README
(the archive name); `VALIDATION.md` (the full `bash replay.sh` run and a
byte-identical PDF rebuild); `SOURCES.md` (records the SHA-256 of a
third-party PDF read for the Raichev–Wilson citation; that PDF is not
distributed); and the article's Section 9 (`bash replay.sh`,
`requirements.txt`; a dated note there gives the collection layout).

## Rerun the checks

Every script writes its result into the **current directory**, so never
run them from this directory or from `code/`. On Windows, Python also writes
text with CRLF; compare JSON by value and text modulo line endings.

**Option A, the delivered layout (full replay including the manifest):**

```sh
git show 096ee7b87:docs/incoming/ordered-rook-reproducibility.zip > "$TMP/orp.zip"
cd "$TMP" && unzip -q orp.zip && cd ordered-rook-report
uv venv "$TMP/v" && uv pip install -p "$TMP/v" sympy==1.14.0 mpmath==1.3.0
PYTHON="$TMP/v/Scripts/python" bash replay.sh    # $TMP/v/bin/python outside Windows
```

(`replay.sh` quotes `$PYTHON`, so it must name a single executable.)

`replay.sh` ends with a PDF rebuild that must be byte-identical to the
delivered PDF, which depends on the TeX installation; the comparison step
before it is the one that checks the data.

**Option B, the shipped files (Git Bash, from this directory):**

```sh
R=$(mktemp -d) && cp -r code data "$R" && mkdir "$R/out" && cd "$R/out"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY ../code/check_models.py > model-checks.json
$PY ../code/check_unsymmetric.py > unsymmetric-checks.txt
$PY ../code/check_symmetric.py > symmetric-checks.txt
for s in check_first_correction check_wick check_inverse check_radial_and_wick \
         check_saddle_k3 check_saddle_k3_order2 check_second_pairings \
         check_second_independent check_numerics; do $PY ../code/$s.py > $s.log; done
for d in 2 3 symbolic; do $PY ../code/generate_coefficients.py --k $d --order 2 --output generator-k$d-order2.json; done
mv generator-ksymbolic-order2.json generator-symbolic-order2.json
$PY ../code/evaluate_model.py inverse --k 3 --target 1e100 --order 2 > inverse-example.json
$PY ../code/evaluate_model.py forward --k 3 --n 80 --order 2 > forward-example.json
for f in ../data/*.json; do $PY -c "import json,sys;assert json.load(open(sys.argv[1]))==json.load(open(sys.argv[2])),sys.argv[1]" "$(basename $f)" "$f"; done
diff -q --strip-trailing-cr unsymmetric-checks.txt ../data/unsymmetric-checks.txt
diff -q --strip-trailing-cr symmetric-checks.txt ../data/symmetric-checks.txt
```

At intake (2 October 2026, pinned SymPy 1.14.0 and mpmath 1.3.0, on a
heavily loaded machine) all eighteen recorded outputs were regenerated this
way, partly by the cluster's suite run and partly by the write step, and all
were equal to the shipped files (JSON by value, text up to line endings).
Step times: `check_saddle_k3.py` 104 s, `check_second_pairings.py` 34 s,
`check_second_independent.py` 16 s, `check_numerics.py` 13 s,
`check_saddle_k3_order2.py` 8 s; the generator 55 s (`k = 2`), 83 s
(`k = 3`) and 133 s (symbolic `k`); `evaluate_model.py` under 10 s; the
seven steps before `check_saddle_k3.py` together under three minutes. The delivered PDF rebuild
and the manifest checks were not run.

## Build the PDF

pdfLaTeX (the preamble uses `\pdfmapfile`) with lmodern, geometry, amsmath,
amssymb, amsthm, mathtools, booktabs, array, microtype, hyperref and
enumitem. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 18 pages,
no errors, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. The
log carries 684 "fontmap entry … already exists, duplicates ignored"
notices from the delivered `\pdfmapfile{+lm.map}` lines (MiKTeX already
maps those fonts); the delivered source gives the same 684 notices, at 16
pages. `code/build.sh` is kept as delivered; to use it, copy it to a
scratch directory together with `article.tex` renamed to
`ordered_rook_paths.tex` and `data/numerical_table.tex`.

## Provenance

- OEIS A227578, A059231, A227580, A227583, A227596 (accessed 2 October
  2026); Raichev–Wilson, Electron. J. Combin. 15 (2008) R89; Lipshitz,
  J. Algebra 113 (1988); Chen–Li, arXiv:1110.5577; Corless et al.,
  Adv. Comput. Math. 5 (1996); Bostan–Bousquet-Mélou–Melczer, JEMS 23
  (2021); Kung–de Mier, JCTA 120 (2013); Kauers–Zeilberger, Adv. Appl.
  Math. 47 (2011); Denisov–FitzGerald, ALEA 20 (2023). Details in
  `SOURCES.md`.
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 58 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
