# The Cubic Boundary for Restricted Partitions

**Sharp volume laws, uniform all-order expansions, exponentially small
corrections, inverse asymptotics, and a Poisson law for repeated parts
(OEIS A238016, A238608 and relatives) — with Part II: uniform asymptotics
for N ≥ a m², a crossover hierarchy and analytic inversion**

A research report dated 1 October 2026, extended on 5 October 2026. It is
built from two manuscripts of ProveIt's incoming-reports intake, both
AI-assisted: Part I (author line "Research report prepared for Vladimir
Reshetnikov") and Part II (title page "Prepared for Vladimir Reshetnikov";
PDF metadata "OpenAI; research report prepared for Vladimir Reshetnikov").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 74, manuscript 05 | `OEIS_Restricted_Partitions_Cubic_Boundary.zip`, arrival commit `c664fc2f0` (main file `restricted_partitions_cubic_boundary.tex`; its PDF not shipped) | none: no ProveIt commit is named; the repository input was a direct reading of the main-branch file `Analysis/FabiusFunction/Lean/FabiusFunction/PartitionBoundedParts.lean` | `b669cff87` | Part I (Sections 1–11 and Appendix A) |
| 02 | batch 98, manuscript 09 | `OEIS_Restricted_Partitions_Crossover.zip` (*Beyond the Cubic Boundary*, 20-page PDF dated 4 October 2026, 21 files), arrival commit `2172df76a` | none: no ProveIt commit is named; its source audit read this report's README as blob `ffeb1d4c…` (the batch-74 README, unchanged until this write) and the README of `a097356-sqrt-restricted-partitions`, not the articles | `0fba5167f` | Part II (Sections 12–26), files prefixed `02-crossover-` |

Both placement commits deleted their archives from `docs/incoming`; the
archives survive in the arrival commits (`git show 2172df76a:docs/incoming/OEIS_Restricted_Partitions_Crossover.zip`).

**Status:** AI-assisted, unrefereed, not formalized. Exact finite checks and
high-precision diagnostics corroborate the formulas; they do not replace the
uniform estimates proved in the text. The 55-digit `mpmath` diagnostics of
Part II are not interval certificates.

## What it proves

`p_m(N)` counts partitions of `N` into parts at most `m` (equivalently, into
at most `m` parts).

### Part I (batch 74)

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

### Part II (batch 98)

With `X = N + m(m+1)/4` (Part I's `M`), `ε = m^2/X` and
`V_m(X) = X^(m-1)/(m!(m-1)!)`:

- **Theorem 14.1**: for every fixed `a > 0` and every fixed `J`,
  `log(p_m(N)/V_m(X)) = m 𝒟(ε) + E_0(ε) + Σ_{j≤J} E_j(ε) m^(-j) + O(m^(-J-1))`
  uniformly for **all** `N ≥ a m^2`, with no upper bound on `N`; `𝒟`, `E_j`
  are real-analytic on `[0,4)` with even germs, computed by an explicit
  Gaussian coefficient operator. The key new estimate (Lemma 16.2) bounds the
  far arcs by `C t (1 + log m) e^(-cm)`, reserving the factor `j = 1`, which
  stays a relative bound however small the saddle `t` is.
- **Theorem 14.2**: the *centered* volume law `p_m(N) ~ V_m(X)` holds iff
  `X/m^(5/2) → ∞`; at `X ~ λ m^(5/2)` the ratio tends to `exp(-1/(72λ^2))`.
  (This does not change Part I's *uncentered* cubic boundary.)
- **Theorem 14.3**: transition scales `X ~ λ m^(2+1/(2r))` with limits
  `exp(d_r/λ^(2r))`, `d_r = -[z^(2r)]B(z)^(2r+1)/(2r(2r+1))` rational;
  infinitely many `d_r` are nonzero; `d_1, …, d_6 < 0` are tabulated.
- **Theorem 14.4** and Proposition 22.2: an analytic inverse chart
  `η = ε e^(-𝒟(ε))` on `[0, e^2)` with corrections to every fixed order,
  and an integer-threshold error transfer; a Lambert-W inverse on power-law
  slices.
- An exact-saddle Edgeworth expansion uniform for `N ≥ a m^2`
  (Theorem 15.2), series of `𝒟`, `E_0`, `E_1`, and the inverse coefficients.

Part II **answers Part I's research question 2** ("A uniform bridge below
the cubic scale") and the end `α = N/m^2 → ∞` of the question "Uniform
limits as the saddle moves to zero or infinity" (Section 14.6) of
`a097356-sqrt-restricted-partitions`. It proves again, as second routes
recorded in its Table 2: Part I's Theorem 3.1 (in logarithmic form), the
near-arc bound (3.9) of Lemma 3.2, Corollary 4.1 (`e^(1/(4c))`), the first
A238608 correction `-61/288`, and the `a_1` term; and the Szekeres leading
constants `u`, `C` of `a097356-sqrt-restricted-partitions`. Dated notes in
Part I and in Part II point to each.

The write added two `[write]` remarks: **Remark 18.1** completes the
condensed proof of Theorem 14.1 (the circle at the continuum saddle, the
complex domain on which Euler–Maclaurin is uniform, the uncancelled linear
term, the relative tail bounds, analyticity and parity), and **Remark 22.1**
writes out the all-orders inverse of Theorem 14.4. Neither has been
independently refereed.

## What is not claimed

- No exhaustive priority search, in either Part. The leading partition
  asymptotics and the first Sylvester wave are classical (Erdős–Lehner via
  Canfield; Dilcher–Vignat; Sills–Zeilberger; O'Sullivan in another joint
  regime). Part I's retrieved sources were not found to list its higher
  coefficients or the probability correction; Part II's source audit was
  bounded and says "There may be older equivalent results or
  coefficients". Szekeres' leading formula, the uncentered cubic law, the
  A238608 leading law and `-61/288` are not claimed by Part II.
- Numerical tests corroborate but do not prove the uniform remainders.
  Inverse charts hold with the stated error at exact sample values;
  arbitrary real thresholds still need discrete rounding control.
- Fixed-order expansions only: no convergence, Gevrey bounds, Borel
  summability, optimal truncation or uniformity in a growing order; no
  analysis of individual root-of-unity waves, their actions or Stokes data.
  Part II calls a "complete resurgent transseries" too strong.
- Part II is **not uniform as `N/m^2 → 0`**; its endpoint statement at
  `ε → 4` concerns the entropy function only. Negativity or nonvanishing of
  **every** `d_r` is not claimed.
- The inversion material of both Parts instantiates the inversion apparatus
  of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  and claims no novelty for the method: the integer-threshold discussion of
  Part I and Proposition 22.2 of Part II are `p0:thm:staircase`; the
  Lambert cores (Part I's `x log x + b_c x = L`, Part II's
  `β m log m + b_λ m = L`) are the Lambert core of the inverse gamma
  function in `p6:thm:gamma`; their corrections are
  `p0:thm:perturbed-inversion`. Dated `[write]` notes in Sections 6 and 22
  say so.
- Part I's Section 9 formalization route, Part I's Section 10 questions and
  Part II's Section 25 questions are proposals, not results.
- `OEIS_update_draft.md` is a draft and was **not submitted** to the OEIS.
  Part II submitted nothing either.

### Part II's further questions (standing rule)

Section 25 holds manuscript 09's seven questions (25.1–25.7) and two moved
there in the write: 25.8 (convergence, Gevrey bounds, Borel summability,
optimal truncation and uniformity in a growing order of the `1/m` series)
and 25.9 (when the second-transition sign appears; the truncated expansion
puts it between `m = 1373` and `m = 1374` on the slice `X = (3/4) m^(9/4)`,
an estimate only). Evidence recorded in the write: `d_1, …, d_16` are all
negative by two exact routes (25.1), and match the law
`d_r ~ -sqrt(π/6) (2r)^(-3/2) 16^(-r)` suggested by the endpoint
singularities at `ε = ±4` to ratios 0.869, 0.955, 0.987, 0.996 at
`r = 1, 7, 12, 16` (25.2); this is evidence for the negativity question
only, and what is missing is stated there. No claim of manuscript 09 was
found to be false.

## Relation to the repository

**Formal status.** Part I cites the Lean file
`Analysis/FabiusFunction/Lean/FabiusFunction/PartitionBoundedParts.lean` as
a starting point. At Part I's placement commit that file has namespace
`Fabius` (line 22) and the declarations `card_restricted_le_eq` (line 57),
`boundedCount` (line 85) and `hasSum_boundedCount_mul_pow` (line 90): the
identification of restricted partitions with multiplicity vectors and the
finite-product generating function. Those are formalized; **no statement of
this report, in either Part, is**, and its place in the collection gives it
no formal status. Neither manuscript built that file.

**Neighbouring reports.** `oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions`
treats the same counts `p_m(N)` at the quadratic scale `N ≍ m^2` (its
parameter `α = N/m^2` held in a compact set). Part I works at `N ≍ m^3` and
beyond, the `α → ∞` end of that report's research question "Uniform limits
as the saddle moves to zero or infinity", and does not answer it: nothing in
Part I is matched uniformly to the quadratic regime.
*[Write note, batch 98, 5 October 2026.]* Part II does answer that end:
its Theorem 14.1 is one expansion uniform for every `N ≥ a m^2`, covers that
report's `srp:thm:allorders` on compact α-ranges in other coordinates, and
re-derives its leading constants as the Szekeres formula; the end `α → 0`
stays open (Part II, Section 25.3). Part II does not reprove that report's
floor-phase, three-exception or plateau results. A reciprocal note for that
report (re-scoping its Section 14.6 to `α → 0`) is proposed separately; the
pointer is made here only.
`a033552-catalan-partitions` (parts restricted to Catalan numbers) and
`a022629-distinct-partition-norms` (products `∏(1+k^a q^k)`) concern
different products. The transseries tree has sibling uses of the same
toolkit (splitting off `h` before Euler–Maclaurin of a finite q-product) for
Gaussian binomials, a different object; no theorem is shared.

## Labels

Every label carries the prefix `rpc:`. Part I: the manuscript's 72 labels
were prefixed before anything cited them, and three were added in writing
(`rpc:sec:intro`, `rpc:sec:proveit`, `rpc:sec:provenance`): 75. Part II
(batch 98) adds 113 labels with the sub-prefix `rpc:cx:`: manuscript 09's 93
labels, prefixed, and 20 added in writing (`rpc:cx:part`, the front-matter
sections and tables `sec:front`, `sec:provenance`, `sec:claims`,
`sec:notation`, `tab:claims`, `tab:routes`, `tab:dictionary`, the remarks
`rem:completion` and `rem:inverse-completion`, `sec:conclusion`, and the nine
question subsections `sec:q-…`): **188 in all**. No Part I label was renamed,
removed or renumbered (checked against a build of the committed text).

Numbering. Part I is unchanged: Sections 1–11 and Appendix A (which now
stands after Part II and belongs to Part I). Part II is Sections 12–26:
Section 12 is the write's front matter; manuscript 09's Sections 1–14 are
Sections 13–26 (manuscript Section k is Section k + 12, and its Theorem 2.1
is Theorem 14.1, Lemma 4.2 is Lemma 16.2, and so on), with one exception:
its Proposition 10.1 is **Proposition 22.2**, because the write's Remark 22.1
precedes it. Manuscript 09's Table 1 (the `d_r`) and Table 2 (errors) are
Tables 4 and 5; Tables 1–3 are the write's. Manuscript 09's
"Further research questions" section is renamed "Further questions and
research" and its "Conclusion" "Conclusion of Part II".

Notation. Part II renames the manuscript symbols that clash with Part I or
are used twice in the manuscript (Table 3 of the article): `D, d_r → 𝒟, 𝖽_r`;
`M_{r-1} → 𝒱_{r-1}`; `Q, Q_3, Q_4 → 𝒬, 𝒬_3, 𝒬_4`; `η → η_⋆`; `R(η), v, v_k →
ℛ, ω, ω_k`; `R_j(θ) → ϱ_j(θ)`; `L_m(t) → Λ_m(t)`; `C_j, R → 𝒞_j, 𝖱` (Edgeworth);
`A_k → 𝖠_k`; `Z_j → ξ_j`; `S → s̄`; `K → K_*` (one proof); `w → ζ`;
`u → ħ`; `G → 𝒢`; standard normal `Y → g`; slice `b → b_λ`. No
normalization is changed; `X` is kept and equals Part I's `M`.

Text added in the writes: Section 1.4 and four dated `[write]` notes in
batch 74 (1.4; two in Section 6; one in Section 8.4), with two bibliography
entries; in batch 98, an editorial note after the status paragraph, the
`\part` headings, dated notes in Part I (Section 1.4, after the remark
following Theorem 3.1, after Lemma 3.2, after Corollary 4.1, and at research
questions 1, 2, 7, 8 and 9), a note at the head of Appendix A, all of
Section 12, dated notes throughout Part II, Remarks 18.1 and 22.1, Section
25's introduction, notes and questions 25.8–25.9, and one bibliography entry
(A097356). No statement, proof or number of either manuscript was changed,
apart from the symbol renames listed above and the restored cross-references.

## Files

```text
README.md                    this guide (replaces both delivery READMEs)
article.tex                  the report (Part I delivered as restricted_partitions_cubic_boundary.tex)
article.pdf                  compiled report, 52 pages
source_audit.md              Part I's source and repository audit, as delivered
OEIS_update_draft.md         Part I's draft OEIS comments, NOT submitted, as delivered
02-crossover-SOURCE_AUDIT.md Part II's source and novelty audit, as delivered (SOURCE_AUDIT.md)
02-crossover-QA.md           Part II's production and review checklist, as delivered (QA.md)
code/derive_coefficients.py  Part I: exact symbolic derivation of L_r(c), b_r(c) (default order 5)
code/asymptotics.py          Part I: forward profiles and inverse charts (reads coefficients.json)
code/verify.py               Part I: exact DP and divisor-recurrence checks, diagnostics
code/build.sh                Part I: the delivered build script (names the old .tex file; see below)
code/02-crossover-asymptotics.py           Part II: continuum profiles, exact finite-saddle evaluator, inverse chart
code/02-crossover-derive_coefficients.py   Part II: exact rational coefficients, 4 symbolic assertions
code/02-crossover-verify.py                Part II: exact recurrences, OEIS check, 55-digit diagnostics
code/02-crossover-build.sh                 Part II: the delivered build.sh (two pdflatex passes on article.tex)
data/coefficients.json       Part I: symbolic output through order 5
data/coefficients_tex.txt    Part I: the same coefficients as TeX
data/exact_values.json       Part I: 258 exact count samples (decimal strings)
data/critical_errors.csv     Part I: relative errors at truncation orders 0, 1, 2, 3, 5
data/poisson_checks.csv      Part I: zero probabilities, means, factorial moments, variance, pgf at u = 1/2
data/inverse_checks.csv      Part I: cubic and exponential inverse sample-point errors
data/verification_summary.json  Part I: the recorded verifier summary (PASS, 9,230 exact assertions)
data/verification_run.txt    Part I: the recorded verifier stdout
data/symbolic_run.txt        Part I: the recorded derivation stdout (L_1 … L_5)
data/requirements.txt        Part I: sympy==1.14.0, mpmath==1.3.0
data/02-crossover-coefficients.json         Part II: s, d_r (r ≤ 6), E_0, E_1, inverse series, the -61/288 check
data/02-crossover-exact_samples.json        Part II: 46 exact counts (m ≤ 96, N ≤ 268566)
data/02-crossover-uniform_errors.csv        Part II: forward errors of the continuum expansion
data/02-crossover-finite_saddle_checks.csv  Part II: exact-saddle (Edgeworth) errors
data/02-crossover-crossover_checks.csv      Part II: m^(5/2) and m^(9/4) transition ratios
data/02-crossover-inverse_checks.csv        Part II: inverse-chart errors at Y = p_m(m^2)
data/02-crossover-profiles.csv              Part II: numerical s, 𝒟, E_0, E_1 profiles
data/02-crossover-verification_summary.json Part II: recorded verifier summary (PASS, 4,017 exact assertions)
data/02-crossover-verification_run.txt      Part II: recorded verifier stdout
data/02-crossover-requirements.txt          Part II: mpmath==1.3.0, sympy==1.14.0 (a generic copy, not Part I's file)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped: both delivered PDFs, both
delivery READMEs and both `SHA256SUMS.txt` (verified 19/19 and 20/20),
manuscript 09's `article.tex` (Part II is its text) and its
`data/symbolic_run.txt` (a byte copy of its `coefficients.json`). Eight
CSVs have CRLF line endings as delivered (Part I's three, Part II's five)
and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`.

Delivered text that names delivery paths or unshipped files:
- Part I: `code/build.sh` runs `pdflatex` on
  `restricted_partitions_cubic_boundary.tex`; the article's Section 8.4 and
  `source_audit.md` describe the flat package and its PDF; the
  `\bibitem{proveit}` points to "Section 1.3" for the Lean path (still
  correct).
- Part II: `02-crossover-SOURCE_AUDIT.md`, `02-crossover-QA.md` and the
  article's Section 24.4 name the delivery layout (`code/`, `data/` without
  prefixes, `article.pdf`, `README.md`, `SHA256SUMS.txt`,
  `data/symbolic_run.txt`); `code/02-crossover-build.sh` changes to its own
  directory (`code/`) and compiles `article.tex` there, so it does not build
  this report as shipped; `02-crossover-verify.py` imports `asymptotics` and
  reads `data/coefficients.json` by their delivered names. The delivery
  README's claim that the scripts "overwrite only their own result files"
  holds in the delivered layout only: run in place they would write
  unprefixed files into `data/`.

## Rerun the checks (on copies, never in place)

Part I's programs read and write next to themselves (`verify.py` and
`asymptotics.py` read `coefficients.json` from their own directory;
`verify.py` rewrites the three CSVs, `exact_values.json` and
`verification_summary.json`; `derive_coefficients.py` rewrites
`coefficients.json` and `coefficients_tex.txt`). Copy Part I's unprefixed
files into one scratch directory and run there (Git Bash, from this
directory):

```sh
R=$(mktemp -d) && cp code/asymptotics.py code/derive_coefficients.py code/verify.py data/[!0]* "$R" && cd "$R"
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

Part II's programs locate `data/` as the sibling of their own `code/`
directory, under the delivered names. Restore the delivered layout in a
scratch directory (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir "$R/code" "$R/data"
for f in code/02-crossover-*.py; do cp "$f" "$R/code/${f#code/02-crossover-}"; done
for f in data/02-crossover-*; do cp "$f" "$R/data/${f#data/02-crossover-}"; done
cd "$R"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/derive_coefficients.py > derive.txt
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py > verify.txt
```

On 5 October 2026 this passed here: `derive_coefficients.py` in 14 s
(rewriting `data/coefficients.json`, identical modulo line endings; its
stdout is the same JSON), `verify.py` in 80 s against a recorded 12.8 s
(PASS: 4,017 exact assertions, 4 symbolic and 10 numerical; 46 samples,
`m <= 96`, `N <= 268566`, 55 digits). The five CSVs came out byte-identical,
`exact_samples.json` identical modulo line endings, and
`verification_summary.json` and `verify.txt` (against
`data/verification_run.txt`) identical apart from `elapsed_seconds` and line
endings. `verify.py` embeds the 17 displayed A238608 terms (`m = 0..16`) of
the OEIS entry (Alois P. Heinz), which are OEIS data under CC BY-SA 4.0; all
other counts come from the shipped dynamic program.

## Build the PDF

pdfLaTeX with Latin Modern, amsmath, amsthm, mathtools, booktabs, longtable,
enumitem, fancyhdr and hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(Neither `code/build.sh` nor `code/02-crossover-build.sh` builds the
shipped layout.) The committed PDF was built in a scratch directory: 52
pages, no errors, no warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull boxes;
its four underfull-box notices, in the two bibliography entries with long
repository paths (the transseries volume and `a097356`), are those of the
batch-74 build of the same entries.

## Provenance

- Part I: OEIS entries A238016, A238608, A238010, A258670 (retrieved
  1 October 2026); Canfield, *From Recursions to Asymptotics* (EJC 4(2),
  1997, R6); Dilcher–Vignat (2017); Sills–Zeilberger (arXiv:1108.4391);
  O'Sullivan (arXiv:1702.03611); DLMF §5.11. `source_audit.md` records what
  was read. Repository input: a source reading of
  `PartitionBoundedParts.lean` on the main branch, not a Lean build and not
  an audit of the rest of the repository.
- Part II: OEIS entries A238016, A238608, A097356 (inspected 4 October
  2026); Canfield (full PDF inspected); O'Sullivan (version 2, 2018) and
  Sills–Zeilberger (abstract-level). Repository input: the READMEs of this
  report and of `a097356-sqrt-restricted-partitions`, the collection README
  and selected search results, read through a GitHub connector on the
  default branch; no Lean build. `02-crossover-SOURCE_AUDIT.md` records
  what was read.
- Write of Part II (batch 98): dossier checks and the write's own exact
  recomputation of `d_1 … d_16` by two routes; both delivered programs rerun
  on copies as above.
