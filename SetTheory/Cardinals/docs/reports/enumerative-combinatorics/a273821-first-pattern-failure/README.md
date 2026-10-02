# First Pattern Failure in Catalan Permutations

**A proof of OEIS A273821, exact formulas, all-orders expansions, and a
critical phase transition**

A research report dated 1 October 2026, built from one manuscript (author
line: "Research report prepared for Vladimir Reshetnikov"; AI-assisted).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 74, manuscript 04 | `A273821_First_Pattern_Failure.zip`, arrival commit `c664fc2f0` (29-page PDF, not shipped) | `291fbe6bb` (its `sources.md` also records the default-branch blob `3d9ce016` of `Analysis/Transseries/README.md`) | `b669cff87` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized. The proofs are
conventional; the computations support them and are not kernel certificates.

## What it proves

For a 123-avoiding permutation of `[n]`, let `K` be the largest `k` such that
its `k` largest entries, in order, avoid 132, and let `T(n,k)` count the
permutations with `K = k` (OEIS A273821, David Callan). The report proves,
from the permutation definition, by inserting successive minima and then
telescoping a Catalan convolution:

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

## What is not claimed

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
- `OEIS_update.txt` is a draft proposal and was **not submitted** to the
  OEIS.

## Relation to the repository

The ProveIt transseries project is methodological context only, as the
manuscript itself says (Sections 1.3 and 13.1, and the claim ledger in
Appendix B): it calls that project a "possible formalization destination",
not a dependency, and nothing in this report has been formalized. Placement
in the research-report collection, beside the repository's Lean and Rocq
developments, confers no formal status. The staircase theorem cited above
is recorded by its volume as partly formalized in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; that
is a property of the volume, not of this report.

No other report treats A273821 or its statistic. The nearest relatives share
the genre only: `enumerative-combinatorics/mesh-avoidance-catalan-inflation`
proves a Catalan-type generating function marked conjectural in A289587,
and `enumerative-combinatorics/adjacency-bounded-132-avoiders` studies
132-avoiders under another constraint.

## Labels

Every label carries the prefix `fpf:`. The manuscript's 118 labels were
prefixed before anything cited them, and six were added in writing
(`fpf:sec:question`, `fpf:sec:insertion`, `fpf:sec:first-failure`,
`fpf:sec:inversion`, `fpf:sec:formal`, `fpf:sec:provenance`): 124 in all.
The three hard-coded section numbers of the manuscript ("Section 1",
"Sections 2–3", "Section 13") are now references. Section 1.4 (provenance)
and three `[write]` notes were added; no statement, proof or number of the
manuscript was changed.

## Files

```text
README.md                        this guide (replaces the delivery README)
article.tex                      the report, standalone LaTeX with an internal bibliography
article.pdf                      compiled report, 30 pages (unnumbered title page, then pages 1-29)
sources.md                       the manuscript's source and search record, as delivered
OEIS_update.txt                  draft OEIS amendments, NOT submitted, as delivered
code/verify.py                   exact enumeration, insertion DP, symbolic and 100-digit checks
code/make_figures.py             regenerates figures/ (needs numpy, matplotlib)
code/Makefile                    the delivered Makefile (written for the archive root; see below)
data/verification_summary.json   the verifier's JSON summary
data/verification_log.txt        the verifier's captured stdout
data/fixed_column_errors.csv     Table 1 source (12 rows)
data/critical_limit.csv          Table 2 source (6 rows)
data/crossover.csv               crossover comparison (12 rows)
data/inverse_errors.csv          inverse-expansion errors (9 rows)
data/supercritical.csv           supercritical comparison (12 rows)
data/environment.json            the delivered run's environment (Python 3.13.5, sympy 1.14.0, mpmath 1.3.0, numpy 2.3.5, matplotlib 3.10.8)
data/requirements.txt            mpmath>=1.3, sympy>=1.12, numpy>=1.24, matplotlib>=3.7
figures/crossover.pdf, .png      Figure 1 (the PDF is included by article.tex)
figures/critical_cdf.pdf, .png   Figure 2
figures/phase_transition.pdf, .png  Figure 3
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. The five CSVs have CRLF line endings as
delivered and are kept so by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The delivered `MANIFEST.sha256` was
verified (23/23) and not shipped, and the delivered PDF is not shipped.
Placement moved two files out of the archive root: `requirements.txt` is
`data/requirements.txt` and `Makefile` is `code/Makefile`; the other paths
are as delivered. Disclosures:

- `data/verification_log.txt` and `data/verification_summary.json` are
  byte-identical: the log is the verifier's captured stdout, which is the
  JSON summary.
- `requirements.txt` lists numpy and matplotlib, which only
  `make_figures.py` needs; `verify.py` needs only mpmath and sympy.
- The three figure PDFs embed a Type 3 font (DejaVuSans, from matplotlib);
  they are kept as delivered.
- Delivered text that names unshipped or moved files: the article's
  "Rebuilding the archive" (Section 12.4) and `code/Makefile` give commands
  for the archive root, with `requirements.txt` there; `sources.md` and
  `OEIS_update.txt` refer to "the accompanying article.tex / article.pdf"
  (the PDF is now this report's build).
- `sources.md` says repository searches for A273821 returned nothing. That
  remains true: no other repository file treats A273821.

## Rerun the checks (on a copy)

`code/verify.py` rewrites `data/verification_summary.json` and the five CSVs
(paths fixed relative to its own location), and `make_figures.py` rewrites
`figures/`. Run them on a copy of this directory (Git Bash, from this
directory):

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
rerun for this write).

## Build the PDF

pdfLaTeX with newtx, amsmath, amsthm, mathtools, geometry, microtype,
hyperref, bookmark, titlesec, fancyhdr, enumitem and the standard graphics
and table packages. The figures are read from `figures/`. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(or `pdflatex` three times; `code/Makefile` does that only when copied to
this directory). The committed PDF was built in a scratch directory: 30
pages, no errors, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations (the title page is now built with
`pageanchor=false`; the delivered source produced a duplicate `page.1`
destination), no overfull boxes.

## Provenance

- Definition and conjecture: OEIS A273821, David Callan (introduced
  31 May 2016), retrieved 1 October 2026. Companion columns A000245 and
  A071718. Standard methods: Flajolet–Sedgewick, DLMF §5.11 and §4.13.
- The manuscript inspected ProveIt at `291fbe6bb` through a GitHub tool and
  read `Analysis/Transseries/README.md` from the default branch (blob
  `3d9ce016`). It was written without knowledge of the collection's other
  reports.
