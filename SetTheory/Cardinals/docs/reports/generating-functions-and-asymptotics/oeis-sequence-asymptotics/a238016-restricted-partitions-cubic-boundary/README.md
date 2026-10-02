# The Cubic Boundary for Restricted Partitions

**Sharp volume laws, uniform all-order expansions, exponentially small
corrections, inverse asymptotics, and a Poisson law for repeated parts
(OEIS A238016, A238608 and relatives)**

A research report dated 1 October 2026, built from one manuscript (author
line: "Research report prepared for Vladimir Reshetnikov"; AI-assisted).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 74, manuscript 05 | `OEIS_Restricted_Partitions_Cubic_Boundary.zip`, arrival commit `c664fc2f0` (main file `restricted_partitions_cubic_boundary.tex`; its PDF not shipped) | none: no ProveIt commit is named; the repository input was a direct reading of the main-branch file `Analysis/FabiusFunction/Lean/FabiusFunction/PartitionBoundedParts.lean` | `b669cff87` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized. Exact finite checks and
high-precision diagnostics corroborate the formulas; they do not replace the
uniform estimates proved in the text.

## What it proves

`p_m(N)` counts partitions of `N` into parts at most `m` (equivalently, into
at most `m` parts). The report proves:

- **The cubic boundary.** `p_m(N) ~ N^(m-1)/(m!(m-1)!)` as `m → ∞` if and
  only if `N/m^3 → ∞`, by elementary lattice-volume and Burnside-type
  bounds. This settles, in a sharp form, the condition still marked
  conjectural in OEIS A238016 and A258670. **Sufficiency is classical**
  (the Erdős–Lehner estimate, recorded in Step 5 of Canfield's 1997 account
  of Szekeres' formula) and is credited as such; necessity, by an
  elementary fixed-point bound, is the new direction. At `N ~ c m^3` the
  ratio to the volume tends to `e^(1/(4c))`.
- A centered expansion to every fixed order, uniform for `N >= c_0 m^3`,
  with a minor-arc estimate covering very large `N`.
- An all-order logarithmic expansion at `N = c m^3` and five explicit
  rational corrections for A238608 (`1 - 61/(288m) - 37463/(165888m^2) +
  …`); the same formulas give A258302–A258305 at `c = 2,…,5`. The leading
  constant `e^(2m+1/4) m^(m-3)/(2π)` is posted in A238608 and is not claimed.
- Higher power columns (A238609–A238615), with a caveat on rounding
  `c m^3` to an integer.
- Dilute expansions resolving genuine `q^(-m)` sectors for `p_m(q^m)`
  (A238010, A237998), the diagonal A238000, and A258670.
- Cubic and exponential inverse charts.
- In the at-most-`m`-parts model, the number of equal adjacent parts
  converges to `Poisson(1/(2c))`, with an explicit first finite-size
  correction to its generating function. (The statistic is not preserved by
  conjugation to the bounded-part-size model.)

## What is not claimed

- No exhaustive priority search. The leading partition asymptotics and the
  first Sylvester wave are classical (Erdős–Lehner via Canfield;
  Dilcher–Vignat; Sills–Zeilberger; O'Sullivan in another joint regime).
  The retrieved sources were not found to list the higher coefficients or
  the probability correction; that is a limited observation.
- Numerical tests corroborate but do not prove the uniform remainders.
  Inverse charts hold with the stated error at exact sample values;
  arbitrary real thresholds still need discrete rounding control.
- No analysis of individual root-of-unity waves or of optimal truncation.
- The inversion material (Section 6) instantiates the inversion apparatus of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  and claims no novelty for the method: the integer-threshold discussion is
  `p0:thm:staircase`; the cubic chart's core `x log x + b_c x = L` is the
  Lambert core of the inverse gamma function in `p6:thm:gamma`, shifted by
  `b_c`; its corrections and the exponential-sector inverse corrections are
  `p0:thm:perturbed-inversion`. Two dated `[write]` notes in Section 6 say so.
- The Section 9 formalization route and the Section 10 questions are
  proposals, not results.
- `OEIS_update_draft.md` is a draft and was **not submitted** to the OEIS.

## Relation to the repository

**Formal status.** The manuscript cites the Lean file
`Analysis/FabiusFunction/Lean/FabiusFunction/PartitionBoundedParts.lean` as
a starting point. At the placement commit that file has namespace `Fabius`
(line 22) and the declarations `card_restricted_le_eq` (line 57),
`boundedCount` (line 85) and `hasSum_boundedCount_mul_pow` (line 90): the
identification of restricted partitions with multiplicity vectors and the
finite-product generating function. Those are formalized; **no statement of
this report is**, and its place in the collection gives it no formal status.
The manuscript read that source and did not build it.

**Neighbouring reports.** `oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions`
treats the same counts `p_m(N)` at the quadratic scale `N ≍ m^2` (its
parameter `α = N/m^2` held in a compact set). This report works at
`N ≍ m^3` and beyond, which is the `α → ∞` end of that report's research
question "Uniform limits as the saddle moves to zero or infinity". It does
**not** answer that question: nothing here is matched uniformly to the
quadratic regime, and the two reports share no proposition. (The pointer is
made here only; that report is not edited by this write.)
`a033552-catalan-partitions` (parts restricted to Catalan numbers) and
`a022629-distinct-partition-norms` (products `∏(1+k^a q^k)`) concern
different products.

## Labels

Every label carries the prefix `rpc:`. The manuscript's 72 labels were
prefixed before anything cited them, and three were added in writing
(`rpc:sec:intro`, `rpc:sec:proveit`, `rpc:sec:provenance`): 75 in all.
Section 1.4 (provenance) and four dated `[write]` notes were added (1.4;
two in Section 6; one in Section 8.4), with two bibliography entries; no
statement, proof or number of the manuscript was changed.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered as restricted_partitions_cubic_boundary.tex)
article.pdf                  compiled report, 23 pages
source_audit.md              the manuscript's source and repository audit, as delivered
OEIS_update_draft.md         draft OEIS comments, NOT submitted, as delivered
code/derive_coefficients.py  exact symbolic derivation of L_r(c), b_r(c) (default order 5)
code/asymptotics.py          forward profiles and inverse charts (reads coefficients.json)
code/verify.py               exact DP and divisor-recurrence checks, diagnostics
code/build.sh                the delivered build script (names the old .tex file; see below)
data/coefficients.json       symbolic output through order 5
data/coefficients_tex.txt    the same coefficients as TeX
data/exact_values.json       258 exact count samples (decimal strings)
data/critical_errors.csv     relative errors at truncation orders 0, 1, 2, 3, 5
data/poisson_checks.csv      zero probabilities, means, factorial moments, variance, pgf at u = 1/2
data/inverse_checks.csv      cubic and exponential inverse sample-point errors
data/verification_summary.json  the recorded verifier summary (PASS, 9,230 exact assertions)
data/verification_run.txt    the recorded verifier stdout
data/symbolic_run.txt        the recorded derivation stdout (L_1 … L_5)
data/requirements.txt        sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` was delivered as
`restricted_partitions_cubic_boundary.tex`; the delivered PDF and
`SHA256SUMS.txt` (verified 19/19) are not shipped. The three CSVs have CRLF
line endings as delivered and are kept so by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The delivered package was flat;
placement split it into `code/` and `data/`. Delivered text that names old
or unshipped paths: `code/build.sh` runs `pdflatex` on
`restricted_partitions_cubic_boundary.tex`; the article's Section 8.4 and
`source_audit.md` describe the flat package and its PDF; and the
`\bibitem{proveit}` points to "Section 1.3" for the Lean path (still
correct).

## Rerun the checks (on a flat copy)

Every program reads and writes next to itself (`verify.py` and
`asymptotics.py` read `coefficients.json` from their own directory;
`verify.py` rewrites the three CSVs, `exact_values.json` and
`verification_summary.json`; `derive_coefficients.py` rewrites
`coefficients.json` and `coefficients_tex.txt`). Run from `code/`, they fail
or write into `code/`. Copy `code/` and `data/` into one scratch directory
and run there (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp code/*.py data/* "$R" && cd "$R"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify.py > run.txt
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify.py --quick   # m <= 24
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python derive_coefficients.py --order 5
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python asymptotics.py
```

On 1 October 2026 the full `verify.py` run passed here in about 11 s (9,230
exact assertions, `m <= 60`, `N <= 320000`, 258 samples, 90 digits): the
three CSVs came out byte-identical, `exact_values.json` and `run.txt`
identical modulo line endings (Windows writes CRLF), and
`verification_summary.json` identical apart from its `seconds` field. At
placement, `derive_coefficients.py --order 5` (about 97 s here) reproduced
`coefficients.json` and `coefficients_tex.txt` modulo line endings.
`verify.py` requires at least five orders in `coefficients.json`.

## Build the PDF

pdfLaTeX with Latin Modern, amsmath, amsthm, mathtools, booktabs, longtable,
enumitem, fancyhdr and hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(`code/build.sh` would look for the delivery file name.) The committed PDF
was built in a scratch directory: 23 pages, no errors, no undefined
references or citations, no multiply defined labels, no duplicate PDF
destinations, no overfull boxes.

## Provenance

- OEIS entries A238016, A238608, A238010, A258670 (retrieved 1 October
  2026); Canfield, *From Recursions to Asymptotics* (EJC 4(2), 1997, R6);
  Dilcher–Vignat (2017); Sills–Zeilberger (arXiv:1108.4391); O'Sullivan
  (arXiv:1702.03611); DLMF §5.11. `source_audit.md` records what was read.
- Repository input: a source reading of `PartitionBoundedParts.lean` on the
  main branch, not a Lean build and not an audit of the rest of the
  repository.
