# First Pattern Failure in Catalan Permutations

**A proof of OEIS A273821, exact formulas, all-orders expansions, and a
critical phase transition; and its extension to the patterns 1(r+1)r…2**

A research report in two Parts, built from two manuscripts (both
AI-assisted). Part I (dated 1 October 2026; author line "Research report
prepared for Vladimir Reshetnikov") treats the pattern 132. Part II (added
5 October 2026; title page "An AI-assisted research manuscript", PDF author
"ChatGPT") answers Part I's first research question for the patterns
τ_r = 1(r+1)r…2, r ≥ 2.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 74, manuscript 04 | `A273821_First_Pattern_Failure.zip`, arrival commit `c664fc2f0` (29-page PDF, not shipped) | `291fbe6bb` (its `sources.md` also records the default-branch blob `3d9ce016` of `Analysis/Transseries/README.md`) | `b669cff87` | Part I (Sections 1–13, Appendices A–B) |
| 02 | batch 98, manuscript 07 | `First_Pattern_Failure_Beyond_132.zip` (24 files, 1,044,533 bytes), arrival commit `2172df76a` (23-page PDF, not shipped) | `0f93381e8` (this report's directory is unchanged from the pin to the placement) | `0fba5167f` | Part II (Sections 14–28), printed in full |

**Status:** AI-assisted, unrefereed, not formalized. The proofs are
conventional; the computations support them and are not kernel
certificates. Manuscript 07's delivery README speaks of "two independent AI
proof audits"; no audit file was delivered.

## What it proves

**Part I (the pattern 132).** For a 123-avoiding permutation of `[n]`, let
`K` be the largest `k` such that its `k` largest entries, in order, avoid
132, and let `T(n,k)` count the permutations with `K = k` (OEIS A273821,
David Callan). Part I proves, from the permutation definition, by inserting
successive minima and then telescoping a Catalan convolution:

    T(n,k) = 2^(k-1) binomial(2n-2k, n-k-1) - binomial(2n-k-1, n-k-1)   (n > k >= 1),
    T(n,n) = 2^(n-1).

This proves the bivariate generating function that A273821 marked
conjectural on the retrieval date, and the suggested growth constant 4 for
every fixed column `k >= 2`, with `T(n,k) ~ ((k-1)(k+4)/2^(k+3)) 4^n /
(sqrt(pi) n^(3/2))`. Further results: hypergeometric columns and a
first-order column recurrence; an all-orders fixed-column coefficient engine
(`c_1`, `c_2`, `c_3` explicit); the discrete limit law
`p_k = (k-1)(k+4)/2^(k+3)` with an exponentially weighted `O(1/n)`
total-variation error; a crossover at `k ≍ sqrt(n)`; two separately expanded
exponential sectors on linear rays; under weight `y^K` a transition at
`y = 2` (bounded `K` below, bounded `n - K` above, `K/n → Beta(1, 1/2)` at
criticality) with `Z_n(2) = (n+2) binomial(2n,n) - 4^n`, the exact critical
mean and second moment, and a critical window; Lambert-`W_{-1}` inverse
expansions with a rounding bracket.

**Part II (the patterns τ_r = 1(r+1)r…2).** With `K_r` the largest `k`
whose `k` largest entries avoid τ_r, and `Δ_r(u) = Σ_j (-u)^j
binomial(r+1-j, j)` (a Chebyshev polynomial; manuscript `D_r`), for every
`r >= 2`:

    F_r(x,y) = u Δ_{r-2}(u)/Δ_r(u) + x u^r C(x)^(r+1) / (Δ_r(u)(1 - u C(x))),   u = xy,
    T_r(n,k) = Σ_{j=r..k} e_{k-j} B(n-k-1, j+1)   (n > k >= r),   e_h = [u^h] 1/Δ_r(u),

with `B(m,p) = [x^m] C(x)^p`; growth constant 4 in every fixed column; the
critical weight `y_c = sec^2(pi/(r+2))`; the subcritical law, also as an
independent sum of geometric variables; and an iterated long-pattern limit
`K_r^∞/r^2 ⇒ W = Σ E_j/(pi^2 j^2)` (Laplace transform `sqrt(s)/sinh
sqrt(s)`) with an explicit Wasserstein bound. For every fixed `r >= 3`: a
uniform two-index estimate (Theorem 19.2), a tight critical deficit with
masses `~ a_r m^(-3/2)`, sharp total-variation rate `2a_r/(P_r sqrt n)` and
moment threshold 1/2, the supercritical law as an exponential tilt, a
coexistence window displaced by `(½ log n + log log n)/n` with a two-point
limit, and local complex zeros; the worked example `r = 3` (golden-ratio
constants, `P(M_3 = 0) = 1/5`). At `r = 2` Part II re-proves Part I's
convolution, safe-state lemmas, subcritical law and `Z_n(2)` (printed as
second routes, Table 4). Written in this write and proved there: the
coefficient computation Theorem 17.2 omits; `T_3(n,n) = Fib(2n-1)`; the
geometric decomposition at `r = 2`; that the uniform estimate is false at
`r = 2` (its residue series is Part I's `b_m/2`, of infinite mass), so the
restriction `r >= 3` is necessary; that Theorem 21.1's formulas hold at
`r = 2` by Part I; and that the median weight of the window is
`y_c exp(-(b_n + s_r* + o(1))/n)`.

## What is not claimed

Part I:

- No exhaustive priority search: a targeted search of the identifier and
  statistic found no other proof; "proved here" is meant literally and does
  not assert that every extension is unprecedented.
- A000245 and A071718 are known companion columns; their leading
  asymptotics are prior and acknowledged.
- Catalan generating trees, Stirling expansions and singularity analysis are
  established methods, not claimed as new.
- The Lambert-W and rounding material (Section 11) instantiates results
  already in the repository and claims no novelty: the inverse theorem is
  `t2:thm:balanced-inverse` of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`
  with `a = log 4`, `β = -3/2`, `C = A_k^*`, `q_j = ℓ_j(k)`; the threshold
  identity and bracket are parts (1)–(2) of `p0:thm:staircase` of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note after Theorem 11.1 says so.
- The numerical tables are high-precision evaluations, not interval
  certificates; no explicit remainder constants or effective monotonicity
  cutoffs are claimed.
- The research questions of Section 13 are proposals, not results.
  [Added 5 October 2026, batch 98: question 1 is answered by Part II (dated
  note there); questions 2, 4, 7 and 8 stay open and carry dated notes
  pointing to Part II's questions 7, 5, 8 and 10.]
- `OEIS_update.txt` is a draft proposal and was **not submitted** to the
  OEIS.

Part II (manuscript 07's non-claims, kept in Section 14):

- The safe counts and their Chebyshev quotient are classical (Chow–West,
  Theorem 3.1; Krattenthaler, Theorem 9 for Dyck paths, Theorem 8 marks
  occurrences, not first failure); first-ascent stopping statistics predate
  it (Connolly–Gabor–Godbole). The `r = 2` formula, beta law and `Z_n(2)` are
  Part I's.
- Its scope ledger "does not assert that no equivalent refinement exists
  elsewhere"; no worldwide priority. This write did not recheck the cited
  theorem numbers of Chow–West and Krattenthaler.
- Sections 19–23 fix `r >= 3`; the constants are not uniform in `r`;
  Theorem 18.1 is an iterated limit (`n → ∞`, then `r → ∞`); no joint
  `r = r(n)` theorem.
- The zero theorem is local, for each fixed zero index: no global ordering,
  not all zeros, and Part I's `r = 2` zero question is not settled.
- Numerical values and root residuals (55 digits) are not interval
  certificates; the coexistence curves converge slowly (`n = 4000`: late
  weight 0.343 against the limit 0.234; zero at `Im s = 4.24` against `pi`);
  the proofs do not use the computations.
- Not peer reviewed, not formalized; its research questions are proposals.
- The unproved items are listed in Section 26, "Further questions and
  research": manuscript 07's ten questions and two added by this write (the
  conditional "prediction" for other pattern families, and priority with
  the unrechecked theorem numbers). No claim of manuscript 07 was found to
  be false.

## Relation to the repository

The ProveIt transseries project is methodological context only, as Part I
itself says (Sections 1.3 and 13.1, and the claim ledger in Appendix B): it
calls that project a "possible formalization destination", not a
dependency, and nothing in this report has been formalized. Placement in the
research-report collection, beside the repository's Lean and Rocq
developments, confers no formal status. The staircase theorem cited above
is recorded by its volume as partly formalized in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; that
is a property of the volume, not of this report. No Lean or Rocq file
mentions A273821 (rechecked 5 October 2026).

No other report treats A273821 or its statistic (still true on 5 October
2026: Part II is in this report). The nearest relatives share the genre
only: `enumerative-combinatorics/mesh-avoidance-catalan-inflation` proves a
Catalan-type generating function marked conjectural in A289587, and
`enumerative-combinatorics/adjacency-bounded-132-avoiders` studies
132-avoiders under another constraint. No other report cites Chow–West.

## Labels

Every label carries the prefix `fpf:`. Part I: the manuscript's 118 labels
were prefixed before anything cited them, and six were added in writing
(`fpf:sec:question`, `fpf:sec:insertion`, `fpf:sec:first-failure`,
`fpf:sec:inversion`, `fpf:sec:formal`, `fpf:sec:provenance`): 124. Part II:
labels carry `fpf:lp:` (with `fpf:` alone eleven would have collided with
Part I's): manuscript 07's 98 labels and nine added in writing
(`fpf:lp:part`, `fpf:lp:sec:front`, `fpf:lp:sec:provenance`,
`fpf:lp:sec:claims`, `fpf:lp:sec:notation`, `fpf:lp:tab:claims`,
`fpf:lp:tab:routes`, `fpf:lp:tab:dictionary`, `fpf:lp:rem:pointwise`): 231 in
all. No Part I label was renamed, removed or renumbered (checked against a
build of the committed text). In Part I, three hard-coded section numbers
became references and Section 1.4 and three `[write]` notes were added in
batch 74; batch 98 added an editorial note before the contents, the
heading "Part I", and dated notes in Section 1.4, after Theorem 3.1's
example, after Theorem 10.1 and at questions 1, 2, 4, 7 and 8 of Section
13.2. No statement, proof or number of either manuscript was changed.
Manuscript 07's section n is Section n+14 (its item n.m is (n+14).m); its
Appendices A and B are Sections 27 and 28. Its `\cref` references are now
`\ref`, and fifteen symbols are renamed (Table 5; for example `D_r → Δ_r`,
`W → 𝒲`, the Wasserstein `W_1 → d_W`); Part I's macros print falling
factorials as `(M)_h` (underlined) instead of `(M)^h`.

## Files

```text
README.md                        this guide (replaces both delivery READMEs)
article.tex                      the report, standalone LaTeX with an internal bibliography
article.pdf                      compiled report, 58 pages (unnumbered title page, then pages 1-57)
sources.md                       Part I: the manuscript's source and search record, as delivered
OEIS_update.txt                  Part I: draft OEIS amendments, NOT submitted, as delivered
code/verify.py                   Part I: exact enumeration, insertion DP, symbolic and 100-digit checks
code/make_figures.py             Part I: regenerates figures/ (needs numpy, matplotlib)
code/Makefile                    Part I: the delivered Makefile (written for the archive root; see below)
code/02-longer-patterns-verify_first_failure.py  Part II: permutation checks r = 2..6, insertion DP, safe states, GF specializations (stdlib)
code/02-longer-patterns-audit_limit_laws.py      Part II: exact moment and limit-law audit (stdlib; imported by the verifier)
code/02-longer-patterns-make_figures.py          Part II: exact r = 3 rows to n = 4000, figures, 55-digit zeros
data/verification_summary.json   Part I: the verifier's JSON summary
data/verification_log.txt        Part I: the verifier's captured stdout
data/fixed_column_errors.csv     Part I: Table 1 source (12 rows)
data/critical_limit.csv          Part I: Table 2 source (6 rows)
data/crossover.csv               Part I: crossover comparison (12 rows)
data/inverse_errors.csv          Part I: inverse-expansion errors (9 rows)
data/supercritical.csv           Part I: supercritical comparison (12 rows)
data/environment.json            Part I: the delivered run's environment (Python 3.13.5, sympy 1.14.0, mpmath 1.3.0, numpy 2.3.5, matplotlib 3.10.8)
data/requirements.txt            Part I: mpmath>=1.3, sympy>=1.12, numpy>=1.24, matplotlib>=3.7
data/02-longer-patterns-verification_summary.json  Part II: verifier summary (PASS)
data/02-longer-patterns-verification_run.txt       Part II: verifier stdout
data/02-longer-patterns-limit_law_audit.json       Part II: limit-law audit (59 exact rational moment checks)
data/02-longer-patterns-exact_small_tables.csv     Part II: T_r(n,k), r = 2..6, n <= 12 (390 rows; Table 8)
data/02-longer-patterns-numerical_summary.json     Part II: figure program summary
data/02-longer-patterns-numerical_run.txt          Part II: figure program stdout
data/02-longer-patterns-critical_moments.csv       Part II: r = 3 critical finite-size moments (Table 9)
data/02-longer-patterns-critical_deficit_pmf.csv   Part II: r = 3 finite and limiting deficit masses (Figure 4)
data/02-longer-patterns-coexistence_probabilities.csv  Part II: r = 3 window probabilities (Table 9, Figure 5)
data/02-longer-patterns-complex_zero_diagnostics.csv   Part II: 55-digit zeros and residuals (Table 10)
data/02-longer-patterns-latex_build.txt            Part II: the delivered LaTeX build log
data/02-longer-patterns-delivery_checks.json       Part II: the delivery's packaging checks
data/02-longer-patterns-provenance.json            Part II: pin, scope, references, environment
data/02-longer-patterns-requirements.txt           Part II: numpy, scipy, matplotlib, mpmath pins (figures only)
figures/crossover.pdf, .png      Part I: Figure 1 (the PDF is included by article.tex)
figures/critical_cdf.pdf, .png   Part I: Figure 2
figures/phase_transition.pdf, .png  Part I: Figure 3
figures/02-longer-patterns-critical_deficit.pdf, .png    Part II: Figure 4
figures/02-longer-patterns-coexistence_window.pdf, .png  Part II: Figure 5
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. The CSVs of both Parts (five each) have CRLF
line endings as delivered and are kept so by `-text` lines in
`SetTheory/Cardinals/.gitattributes`.

Part I disclosures: the delivered `MANIFEST.sha256` was verified (23/23) and
not shipped, and the delivered PDF is not shipped. Placement moved two files
out of the archive root: `requirements.txt` is `data/requirements.txt` and
`Makefile` is `code/Makefile`; the other paths are as delivered.

- `data/verification_log.txt` and `data/verification_summary.json` are
  byte-identical: the log is the verifier's captured stdout, which is the
  JSON summary.
- `requirements.txt` lists numpy and matplotlib, which only
  `make_figures.py` needs; `verify.py` needs only mpmath and sympy.
- The three Part I figure PDFs embed a Type 3 font (DejaVuSans, from
  matplotlib); they are kept as delivered. (Part II's two embed TrueType
  fonts only.)
- Delivered text that names unshipped or moved files: the article's
  "Rebuilding the archive" (Section 12.4) and `code/Makefile` give commands
  for the archive root, with `requirements.txt` there; `sources.md` and
  `OEIS_update.txt` refer to "the accompanying article.tex / article.pdf"
  (the PDF is now this report's build).
- `sources.md` says repository searches for A273821 returned nothing. That
  remains true: no other repository file treats A273821.

Part II disclosures: placement prefixed every staged file with
`02-longer-patterns-` and moved `requirements.txt` and `provenance.json`
into `data/`; the delivery's `article.tex`, `article.pdf` and `README.txt`
are not shipped (they survive in the arrival commit), and the package had no
checksum manifest.

- The two verification programs import each other by their delivered names
  (`from audit_limit_laws import run`, `from verify_first_failure import
  ...`), so the prefixed files cannot run as shipped.
- Their default output directory is `<script>/../data`: run in place,
  `verify_first_failure.py` would **overwrite Part I's
  `data/verification_summary.json`** (and write unprefixed
  `exact_small_tables.csv` and `limit_law_audit.json`), and
  `make_figures.py` writes unprefixed files into `data/` and `figures/`.
  Never run them in this directory (see below).
- Delivered text naming delivery paths or unshipped files: Section 25.1
  ("Reproduction", the manuscript's commands for the archive root) and its
  delivery README; `data/02-longer-patterns-delivery_checks.json` and
  `data/02-longer-patterns-latex_build.txt` describe the delivered 23-page
  `article.pdf` and `figures/critical_deficit.pdf`, `figures/coexistence_window.pdf`;
  `data/02-longer-patterns-verification_summary.json` names
  `detail_file: limit_law_audit.json`; `provenance.json` names the
  delivered layout.
- `requirements.txt` pins numpy, scipy, matplotlib and mpmath, which only
  `make_figures.py` needs; the two verification programs use the standard
  library only. The delivered run used Python 3.12.14.
- The figure PNGs are previews; the PDFs are what `article.tex` includes.

## Rerun the checks (on a copy)

**Part I.** `code/verify.py` rewrites `data/verification_summary.json` and
the five CSVs (paths fixed relative to its own location), and
`make_figures.py` rewrites `figures/`. Run them on a copy of this directory
(Git Bash, from this directory):

```sh
R=$(mktemp -d)/a273821 && cp -r . "$R" && cd "$R"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py > run_log.txt
```

The default run (`--brute-max 9 --dp-max 120`) examines every permutation
of sizes 1–9 (409,113 in total), checks every triangle entry through row 120 (7,260 cells) with an
independent insertion-state dynamic program, and runs the symbolic and
100-digit checks. On 1 October 2026 it passed here in about 17 s; the five
CSVs came out byte-identical, and `run_log.txt` and
`data/verification_summary.json` identical to the shipped ones modulo line
endings (Windows writes CRLF). `--brute-max` (1–10) and `--dp-max` (2–400)
raise the ranges at a cost in time. Figures: `uv run --no-project --with
numpy --with matplotlib python code/make_figures.py` in the same copy (not
rerun in batch 74 or batch 98).

**Part II.** Restore the delivered layout in a scratch directory, outside
this report (Git Bash, from this directory):

```sh
R=$(mktemp -d)/fpf-lp && mkdir -p "$R/code" && for f in verify_first_failure audit_limit_laws make_figures; do cp "code/02-longer-patterns-$f.py" "$R/code/$f.py"; done
cd "$R" && py code/verify_first_failure.py > verification_run.txt
uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 --with matplotlib==3.10.8 --with mpmath==1.3.0 python code/make_figures.py > numerical_run.txt
```

Both write into `$R/data` (and `$R/figures`), never into this report.
`verify_first_failure.py` accepts `--brute`, `--dp`, `--safe`, `--outdir`
and `--skip-limits`; `make_figures.py` accepts `--outdir` (a package root),
`--maximum` (default 4000) and `--skip-zeros`. Run so on 5 October 2026
with Python 3.14.4: the verifier passed in 39 s (409,113 permutations, 6,917
avoiders, `r = 2..6`; DP to `n = 40`, safe states to `n = 120`); its
`exact_small_tables.csv` is byte-identical to the shipped one, its summary
and stdout identical up to `elapsed_seconds` and line endings, and
`limit_law_audit.json` differs only in last-place floating-point digits (11
values). The figure program passed in 3 min 16 s of wall time:
`complex_zero_diagnostics.csv` byte-identical, the other
three CSVs equal to relative 9e-16, the JSON summary and stdout equal up to
floats and timings; the figure PDFs and PNGs differ in bytes (metadata and
rasterization), as the delivery README warns. The symbolic checks of this
write's `[write]` notes were run with SymPy 1.14.0 on a scratch file, not
shipped.

## Build the PDF

pdfLaTeX with newtx, amsmath, amsthm, mathtools, geometry, microtype,
hyperref, bookmark, titlesec, fancyhdr, enumitem and the standard graphics
and table packages. The figures are read from `figures/`. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(or `pdflatex` three times; `code/Makefile` does that only when copied to
this directory). The committed PDF was built in a scratch directory on
5 October 2026: 58 pages, no errors, no undefined references or citations,
no multiply defined labels, no duplicate PDF destinations (the title page is
built with `pageanchor=false`), no overfull or underfull boxes; the
committed text before this write built the same way to 30 pages.
Manuscript 07 was written for lmodern and `cleveref`; it is set here in the
report's newtx fonts with plain references.

## Provenance

- Definition and conjecture: OEIS A273821, David Callan (introduced
  31 May 2016), retrieved 1 October 2026 (Part I) and 4 October 2026
  (Part II). Companion columns A000245 and A071718. Standard methods:
  Flajolet–Sedgewick, Flajolet–Odlyzko, DLMF §§4.13, 4.36 and 5.11. Safe
  counts: Chow–West (1999), Krattenthaler (2001).
- Part I's manuscript inspected ProveIt at `291fbe6bb` through a GitHub tool
  and read `Analysis/Transseries/README.md` from the default branch (blob
  `3d9ce016`). It was written without knowledge of the collection's other
  reports.
- Part II's manuscript read this report at `0f93381e8` (4 October 2026,
  19:54 PDT), together with its README, the collection catalogue and the
  enumerative and generating-function report directories; it answers
  Part I's Section 13, question 1. It made no repository change and no OEIS
  submission.
- Neither manuscript embeds OEIS data files; terms quoted from OEIS entries
  are CC BY-SA 4.0. Part II's exact rows are computed by its own programs.
