# Tournament Score Sequences and Weighted Component Asymptotics

**Explicit corrections and uniform inverse models: every fixed order for all
and strong score sequences (OEIS A000571, A351822), a uniform half-power
expansion of the component-weighted count on a logarithmic window, and the
coexistence profile at `τ = ½ log n + 2 log log n + log(μ√π/2) + s`**

A research report dated 2 October 2026, built from one manuscript. It names no
author and no tool (its title block reads "Research report"), and the PDF
metadata has an empty Author field.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 68 | `tournament-score-sequences-source.zip` (wrapper directory `tournament-score-sequences/`), arrival commit `096ee7b87`; main file `report.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized: no Lean or Rocq declaration exists for any
statement of this report. **Its inputs are prior work, credited:** the exact
generating function `S(z) = exp A(z)` and the strong-block decomposition are
Claesson–Dukes–Franklín–Stefánsson's (Proc. AMS 151, 2023; divisor evaluation
attributed there to Alekseyev), and the leading asymptotics of `S_n`, `I_n`
and each fixed component count are Kolesnik's (Combinatorica 43, 2023; shorter
proof by Bassan–Donderwinkel–Kolesnik, ECP 31, 2026). The renewal and
logarithmic heavy-traffic/heavy-tail mechanisms are credited to Blanchet–Glynn
(2007) and Olvera-Cravioto–Blanchet–Glynn (2011). The contribution is the
explicit local refinement; no exhaustive novelty search is claimed.

## What it proves

`S_n` counts score sequences of tournaments on `n` vertices (A000571), `I_n`
the strong (irreducible) ones (A351822 without its empty object; A054946, which
counts strongly connected labeled tournaments, is a different problem), and
`W_n(u) = Σ_m S_{n,m} u^m` weights by the number of strong blocks. With the
CDFS split `A = F + R` (`R` analytic in `|z| < 1/2`), `ρ = 1/4`,
`λ = A(ρ) = 0.33023754398…`, `μ = ρA'(ρ) = 0.67395260185…`,
`p = 1 − e^(−λ)`:

- **Theorem 3.1.** For every fixed `K`, `T_n^σ = (e^(σλ)/(2√π)) 4^n n^(-5/2)
  (Σ_{m≤K} c_m^σ n^(-m) + O(n^(-K-1)))` for all (`σ = +`) and strong
  (`σ = −`) sequences, with `c_1^σ = −1/8 + σ(5/2)μ`, explicit `c_2^σ`
  (`c_2^+ ≈ −0.59217`, `c_2^− ≈ 4.58215`).
- **Proposition 3.2.** Fixed subcritical weights `0 < u < u_c = 1/p`, and
  the critical weight, where `4^(-n) W_n(u_c) = 1/a_c + (2/(3μ a_c √π)) n^(-1/2)
  + O(n^(-3/2))` with no `n^(-1)` term.
- **Theorems 4.1 and 5.1.** Uniformly on `0 ≤ τ ≤ C log n`,
  `4^(-n) W_n(u_n(τ)) = a_n(τ)^(-1) Σ_{m≤M} n^(-m/2) C_m(τ) + O(n^(-(M+1)/2))`,
  with `C_0 = e^(−τ)`, `C_1 = k H(τ)`, `H = ₁F₁(2; 1/2; −τ)/√π`, explicit
  `C_2`, and a finite generator in entire (regularized Kummer) kernels.
- **Corollary 6.1 (coexistence).** At `τ = b_n + s`,
  `a_c √n (log n)² 4^(-n) W_n → (2/(μ√π))(1 + e^(−s))`.
- **Section 7.** Inverses of specified models: fixed family size from `S_n`
  or `I_n` (explicit `W_{-1}` at order 0), size along a coexistence path, and
  the component weight when `n` is known.

## What is not claimed

- No result for `τ < 0` (supercritical moving pole), for truncation orders or
  component counts growing with `n`, or convergence of the full series.
- The coexistence statement is a coefficient asymptotic, not a conditional
  mixture law; the factors `1` and `e^(−s)` are not asserted to be mixture
  probabilities.
- Inverses locate real model inverses; they do not certify integer rounding
  or finite-`n` confidence intervals; weight calibration assumes known `n`.
- All decimals (including high-precision ones) are non-interval checks; the
  remainders are proved analytically.
- The further questions of Section 9 (conditional component laws,
  supercritical crossover, explicit constants, growing orders, comparison
  with general renewal theorems) are open.
- **The inversion is an instance of repository results; no novelty is claimed
  for the method.** The explicit order-0 inverse is `p0:thm:lambert-core`
  (`a = log 4`, `b = −5/2`, branch `W_{-1}`), the three localization bounds are
  the residual-to-root conversion `p0:thm:backward-error`, and the bracketing
  remark is the separation condition, part (2) of `p0:thm:staircase`, all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note at the end of Section 7 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; the manuscript used
no ProveIt theorem. The generic staircase arithmetic named in the Section 7
note is formalized as `Fabius.staircase_ceil` and `Fabius.staircase_separation`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `S_n` or `W_n`.

**Neighbouring reports.** None: no other repository report treats tournament
score sequences or A000571, A351822, A145855, A054946 (searched at
placement). Batch-77 manuscripts 13 and 14 (cluster P5, beta renewals) use
the word "renewal" for an unrelated object. The batch-77 report
`a116379-bounded-identity-trees` shares only the delivered PDF build script
(byte-identical `build_pdf.sh`).

## Notation

The manuscript reuses letters: `s` is both the Hankel variable `nw` and the
coexistence shift; `b_j` are Puiseux coefficients and `b_n` the coexistence
centre; `W` is the weighted generating function and `W_{-1}` Lambert's
function; `t` is `√(1−4z)` and the free parameter of the weight model;
`c`, `C`, `D`, `d`, `E`, `H`, `h`, `k`, `K`, `M` have two or three meanings
each. A table in the first `[write]` note (after "Results and scope at a
glance") fixes each symbol by section, with the tempting false readings. No
symbol was renamed.

## Labels

Every label carries the prefix `tss:`. The manuscript's 73 labels were
prefixed before anything cited them (every `\ref`/`\eqref` updated); no label
was added. The writing step also added three dated `[write]` notes (after
"Results and scope at a glance": provenance, credit, notation table; Section 7:
the transseries-instance note; Section 8.1: the shipped layout and the
intake's independent check), typeset the six binomial coefficients with
`\binom` instead of `\choose` (identical output; removes the delivered
source's amsmath "Foreign command \atopwithdelims" warning), and set the
bibliography ragged-right (removes its one underfull box). No statement,
proof or number of the manuscript was changed.

## Files

```text
README.md                                this guide (replaces the delivery README)
article.tex                              the report (delivered as report.tex)
article.pdf                              compiled report, 17 pages
code/run_checks.py                       one command for all checks; writes results/ beside scripts/ (see below)
code/check_exact_counting.py             independent Landau enumeration through n = 10
code/check_scores.py                     exact integer recurrences through n = 1000 and constants
code/check_crossover.py                  normalized weighted recurrence and two-term models
code/check_higher_crossover.py           corrected third term and fixed second corrections
code/uniform_generator.py                finite half-power generator through M = 4
code/check_weight_inverse.py             known-size component-weight inverse checks
code/verify_manifest.py                  delivered SHA256SUMS check (the manifest is not shipped)
code/replay.sh                           delivered replay: run_checks.py, then build_pdf.sh
code/build_pdf.sh                        delivered PDF build (compiles report.tex beside it)
data/exact-counting-checks.json          Landau enumeration S_n, I_n, S_{n,m} for n <= 10
data/score-checks.json                   recurrence checks and scaled residuals
data/crossover-checks.json               two-term crossover checks
data/higher-crossover-checks.json        third-term and fixed second-correction checks
data/allorders-crossover-checks.json     21 crossover points through M = 4
data/weight-inverse-checks.json          24 weight-inverse cases
data/verification.json                   status PASS, symbolic c_1, c_2, d_4, C_2, and source hashes
data/requirements.txt                    mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `report.tex` to
`article.tex`, `scripts/` to `code/` and `results/` to `data/`, and moved
`replay.sh`, `build_pdf.sh` (to `code/`) and `requirements.txt` (to `data/`).
Not shipped: the delivered 15-page PDF `report.pdf` and `SHA256SUMS` (a
checksum ledger, verified 21/21 at placement and retired). Both survive in the
archive:
`git show 096ee7b87:docs/incoming/tournament-score-sequences-source.zip > <scratch>/tournament-score-sequences-source.zip`.
Nothing heavy was excluded (every data file is under 15 KB).

Delivered text that names the delivery layout or unshipped files:
`code/run_checks.py` (reads `scripts/`, writes `results/` under the package
root, and says the requirements are in `../requirements.txt`),
`code/check_*.py` and `code/uniform_generator.py` (write `../results/`),
`code/verify_manifest.py` (reads `SHA256SUMS`), `code/replay.sh` and
`code/build_pdf.sh` (`scripts/run_checks.py`, `report.tex`, `report.pdf` in
their own directory), and Section 8.1 of the article (dated note). The
delivery README, which this guide replaces, began its replay with
`python3 scripts/verify_manifest.py`.

## Rerun the checks (on a scratch copy)

Every script writes into `results/` beside its own directory: run from
`code/` it would create `results/` in this report directory, and in the
delivered layout it overwrites the recorded outputs; `run_checks.py` also
looks for its siblings in `scripts/`. Rebuild the delivered layout on a copy
(Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir -p "$R/scripts" "$R/results" && cp code/*.py "$R/scripts/" && cd "$R"
export PYTHONUTF8=1
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python scripts/run_checks.py
for f in "$OLDPWD"/data/*.json; do diff -q --strip-trailing-cr "results/$(basename "$f")" "$f"; done
```

It enumerates Landau sequences through `n = 10`, runs the integer recurrences
to `n = 1000`, asserts the symbolic `c_1`, `c_2`, `d_4`, `C_2` identities, and
checks the 21 crossover and 24 inverse cases against non-interval envelopes;
it also writes one `.log` per script into `results/`. At intake (2 October
2026, heavily loaded machine) it took about 165 s, reported status PASS, and
all seven JSON files equalled the recorded ones up to line endings (Windows
writes CRLF, hence `--strip-trailing-cr`); the recipe above, run in the write
phase, passed in 79 s with the same result. `verification.json` records source
hashes of the scripts at their `scripts/` paths.

## Build the PDF

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, enumitem, xcolor, hyperref, fancyhdr; the preamble uses
`\pdfmapfile`); no BibTeX. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 17 pages, no
errors or warnings, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. (The
delivered source built to 15 pages with one amsmath warning and one underfull
box in the bibliography, both removed as described under Labels.)
`code/build_pdf.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to `report.tex`.

## Provenance

- Claesson–Dukes–Franklín–Stefánsson, Proc. Amer. Math. Soc. 151 (2023)
  3691–3704, Corollaries 12–13; Kolesnik, Combinatorica 43 (2023) 827–844;
  Bassan–Donderwinkel–Kolesnik, Electron. Commun. Probab. 31 (2026) 3;
  Blanchet–Glynn, Adv. Appl. Probab. 39 (2007); Olvera-Cravioto–Blanchet–Glynn,
  Ann. Appl. Probab. 21 (2011); OEIS A000571, A351822, A145855, A054946
  (checked 2 October 2026 by the manuscript).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 68 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
