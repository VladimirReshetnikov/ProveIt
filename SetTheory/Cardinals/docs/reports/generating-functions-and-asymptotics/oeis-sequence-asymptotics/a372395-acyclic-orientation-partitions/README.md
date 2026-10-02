# Full Asymptotic Expansions for Partition Sums of Acyclic Orientations

**Prefactors and every fixed order for OEIS A372395 and A370613, a uniform
quadratic majorant for the signed Gamma representation, explicit first and
second corrections, a finite coefficient algorithm, Lambert-W inverses with
integer-threshold envelopes, and a fixed positive chromatic parameter**

A research report dated 1 October 2026, built from one manuscript. Its
author line is empty; the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 59 (cluster P4) | `orientation-partition-asymptotics.zip` (wrapper directory `orientation-partition-asymptotics/`), arrival commit `096ee7b87`; main file `orientation-partition-asymptotics.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized. The delivered audits are source-level
reviews, "not a machine-verification certificate".

## What it proves

`B_+(n)` (A372395) and `B_-(n)` (A370613) sum the number of acyclic
orientations `AO(K_λ)` of the complete multipartite graph `K_λ` over the
partitions `λ` of `n`, unrestricted (`η = +1`, Bose) or into distinct parts
(`η = -1`, Fermi).

- **Theorem 1.1 (every fixed order).**
  `B_η(n) = A_η n! n^(-p_η) e^(C_η √n) (Σ_{j≤L} a_{η,j} n^(-j/2) + O(n^(-(L+1)/2)))`
  with `p_+ = 1`, `p_- = 3/4`, explicit amplitudes `A_η` (including a tilted
  Gamma-integral factor `E_0`), and `a_{η,1}`, `a_{η,2}` evaluated
  (`a_{+,1} = -0.30756533…`, `a_{-,1} = 0.23095021…`).
- **Theorem 3.2 (uniform quadratic majorant).** `AO(K_λ)/n! ≤ C_0
  exp(-(Σλ_i² - n)/(2n))` uniformly for largest part `≤ n^β`,
  `3/4 < β < 4/5`, controlling the signed Gamma representation; Section 4
  removes the cutoffs at relative precision.
- **Section 7 (finite coefficient algorithm)**: every `a_{η,j}` as the
  `ε^j` coefficient of a Gaussian expectation (eq. (37)); the scale is
  `n^(-1/2)` with no logarithms. **Section 8**: an independent short route to
  `a_1`.
- **Theorem 9.1 (inverse).** For a smooth increasing interpolant, `F^{-1}(Y)
  = N - C√N/ℓ - α_0 - d_0/ℓ + …` with `N = L/W(L/e)`, `L = log Y`,
  `ℓ = log N`, to every finite order (polynomials in `1/ℓ`), plus a next term
  (45); the integer threshold `τ(Y)` is `⌈F^{-1}(Y)⌉` for an exact increasing
  interpolant (42), and a finite approximation gives the two-ceiling envelope
  (46).
- **Corollary 11.1 (chromatic parameter).** For fixed `v > 0`, uniformly on
  compact subsets of `(0, ∞)`, the sums of `(-1)^|V| χ_{K_λ}(-v)` satisfy the
  same expansion with `Γ(n+v)/Γ(v)` in place of `n!`, the same `A_η, C_η,
  p_η`, and `a_{η,1}(v) = a_{η,1}(1) + (v-1)M_2/2`.

## What is not claimed

- **Priority.** The exact Gamma representation and the constants `C_±`
  (`log(B_±(n)/n!) ~ C_± √n`) are Zhiyang Sun's (arXiv:2605.04006v1); the
  manuscript answers the question of Sun's Section 11 (prefactors and
  complete expansion). The audits make no "exhaustive historical-priority
  search".
- The expansion holds to every fixed order in the Poincaré sense; no
  exponentially complete transseries, exponentially small sector or
  summation prescription is claimed. No convergence of the full series.
- The coefficient executable is tested through second order, not offered as
  an optimized arbitrary-order implementation.
- The inverse uses a constructed smooth interpolant; "no canonical analytic
  continuation is asserted". Exact rounding needs separation from an
  integer; the inverse checks are residual checks, not certified threshold
  bounds.
- The chromatic corollary claims no uniformity for `v` growing with `n` and
  no `v = 0` limit.
- Numerical decimals are not interval-certified; exact checks through
  `n = 300` support but do not replace the proof.
- Section 12's four questions (late coefficients and exponentially small
  sectors, limit laws, growing `v`, effective constants) remain open.
- **Inversion: no novelty claimed for the method.** The core `N = L/W(L/e)`
  is the unbalanced core `t2:eq:unbalanced-core` (`κ = 1`, `λ = -1`) of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`,
  equivalently `p0:prop:factorial-core` (`κ = 1`, `d = -1`, branch `W_0`)
  of `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`;
  the correction recursion is the local reversion `t2:prop:scaled`; the
  mean-value step is `p0:thm:backward-error`; `τ = ⌈F^{-1}⌉` and the
  envelope are `p0:thm:staircase` (1) and (2) for the admissible
  interpolation (42) (`p0:def:three-inverses`). A dated `[write]` note at
  the end of Section 9 says so. (The batch-77 dossier proposed citing CTI's
  `t2:thm:balanced-inverse`; that theorem is the balanced case `κ = 0` and
  does not cover this factorial phase, so the unbalanced core is cited
  instead.)

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic order-theoretic steps named
in the inverse note are formalized for an arbitrary monotone function, not
for `B_η`: `Fabius.staircase_ceil` and `Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, and
`Fabius.abs_sub_right_inverse_le_div` in
`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`.

**Neighbouring reports.** No report of the collection treats acyclic
orientations, chromatic polynomials of complete multipartite graphs, A372395
or A370613 (intake search); Touchard and Stirling polynomials appear
elsewhere only as classical tools. `a301981-unitary-divisor-partitions` and
`a174065-radix-layer-partitions` (same batch) and earlier reports such as
`a022629-distinct-partition-norms` apply saddle-point analysis to other
weighted partition products; no result is shared. (Pointers made here only;
those reports are not edited.) The manuscript, its audits and its delivery
README do not mention ProveIt.

## Notation

`η = ±1` is a sign, not a small parameter (that is `ε = n^(-1/2)`). Letters
with several meanings: `L` (a fixed order, the largest part, and `log Y`);
`d_0` (a *function* `f_0 - f_std` in Section 5 and a *constant*
`log(A√(2π))` in Section 9); `H` (the product coefficients `H_j`, the
chromatic evaluation `H_v`, the Touchard polynomials `H_{±,n}`); `A`, `B`,
`C_0`, `K`, `M`, `P/p`, `Q`, `R`, `F`, `α`, `β` two or three ways each;
`N = L/W(L/e)` is not the index `n`. Table 1 (a `[write]` float in Section
1) fixes every such symbol. No symbol was renamed.

## Labels

Every label carries the prefix `aop:`. The manuscript's 50 labels were
prefixed before anything cited them (39 `\ref`/`\eqref` updated), and six
section labels (`aop:sec:results`, `aop:sec:exact`, `aop:sec:first`,
`aop:sec:checks`, `aop:sec:chromatic`, `aop:sec:questions`) and the
notation table's `aop:tab:notation` were added: 57 labels in all. The
writing step also added four dated `[write]` notes (end of Section 1:
provenance, credit and scope, neighbours, notation table; end of Section 9:
the inverse note; end of Section 10: the shipped files; end of Section 12:
the open questions), two bibliography entries (`aop-tai`, `aop-cti`), and
set the bibliography ragged-right. No statement, proof or number of the
manuscript was changed.

## Files

```text
README.md                                    this guide (replaces the delivery README)
article.tex                                  the report (delivered as orientation-partition-asymptotics.tex)
article.pdf                                  compiled report, 15 pages
proof.md                                     delivered plain-text core proof (Sections 1-9 of the theorem), from which the article was translated
tutte_axis_extension.md                      delivered plain-text form of the chromatic corollary (Section 11)
independent_audit-audit.md                   delivered mathematical audit of the core proof
independent_audit-fixed_parameter_audit.md   delivered audit of the chromatic corollary
independent_audit-integrated_source_audit.md delivered audit of the integrated TeX manuscript (names the delivered .tex/.pdf hashes)
code/first_correction.py                     a_1 by one-dimensional integrals; writes first_correction.json beside itself
code/generic_second_correction.py            the finite generator through a_2; writes generic_second_correction.json beside itself
code/exact_check.py                          exact B_η(n) by Touchard/Kronecker arithmetic; `exact_check.py N` writes exact_values_N.json beside itself
code/validate_results.py                     exact overlap 150/300, the OEIS initial terms, residuals, inverse; reads three JSON beside itself, writes validation_300.json
code/independent_audit-checks.py             the audit's independent checks (n ≤ 40 arrays, direct orientations n ≤ 6, AD quadrature); expects to sit in independent_audit/ below the package root
code/replay.sh                               the delivered short replay (bare `python`, files beside it)
code/build.sh                                the delivered PDF build (expects orientation-partition-asymptotics.tex)
data/exact_values_150.json                   exact values, n ≤ 150
data/exact_values_300.json                   exact values, n ≤ 300
data/first_correction.json                   recorded first_correction.py output
data/generic_second_correction.json          recorded generic_second_correction.py output
data/validation_300.json                     recorded validate_results.py output
data/short_replay.log                        recorded replay.sh output
data/quality_checks.json                     delivered PDF/TeX quality record (13 pages; hash of the delivered .tex)
data/independent_audit-checks.json           recorded audit-check output (records input hashes)
data/independent_audit-checks.log            recorded audit-check stdout
data/independent_audit-convergence_300.json  the audit's n ≤ 300 residual table (no shipped script writes it)
data/requirements.txt                        mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed
`orientation-partition-asymptotics.tex` to `article.tex`; moved the scripts,
`build.sh` and `replay.sh` to `code/`, the JSON, logs and requirements to
`data/`, and `independent_audit/<name>` to `independent_audit-<name>` (the
`.py` to `code/`, the `.json`/`.log` to `data/`, the `.md` to this
directory). The two logs are matched by the root `.gitignore` rule `*.log`
and were added with `git add -f`. Not shipped: the delivered 13-page PDF
`orientation-partition-asymptotics.pdf` and the hash ledgers
`manifest.json` (27/27) and `independent_audit/reviewed_hashes.json`
(19/19), both verified at placement. All survive in the archive:
`git show 096ee7b87:docs/incoming/orientation-partition-asymptotics.zip > <scratch>/orientation-partition-asymptotics.zip`.

Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` and the scripts (inputs and outputs beside the script);
`code/independent_audit-checks.py` (reads `proof.md`, `first_correction.json`
and `exact_values_150.json` from the directory above its own);
`code/build.sh` (compiles `orientation-partition-asymptotics.tex`; a
fallback branch copies TeX formats from a `/tmp/hamiltonian-rank-build/`
directory of the authoring machine);
`independent_audit-audit.md` (names `checks.py`, `checks.json`,
`checks.log`, `convergence_300.json` and `reviewed_hashes.json` "in this
directory", and says that the test run in `checks.json` records the
preceding manuscript revision, whose mathematics is identical);
`independent_audit-integrated_source_audit.md`,
`independent_audit-fixed_parameter_audit.md` and `data/quality_checks.json`
(hashes of the delivered `.tex`, `.pdf` and `tutte_axis_extension.md`);
`tutte_axis_extension.md` (refers to "the formal exponent Q of proof.md");
and the article's Section 10 (a dated note there says what is shipped).

## Rerun the checks (on a scratch copy)

Every script writes its JSON beside itself and reads its inputs from there,
so never run them in `code/`. Rebuild the delivered flat layout in a scratch
directory. Git Bash, from this directory:

```sh
D=$PWD; R=$(mktemp -d); cd "$R"
cp "$D"/code/*.py "$D"/data/exact_values_*.json "$D"/proof.md .
mkdir independent_audit && mv independent_audit-checks.py independent_audit/checks.py
export PYTHONUTF8=1
PY="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
$PY first_correction.py
$PY generic_second_correction.py
$PY validate_results.py          # ends with "PASS: exact OEIS initials and independent overlap"
for f in first_correction generic_second_correction validation_300; do
  $PY -c "import json,sys; print(sys.argv[1], json.load(open(sys.argv[1]))==json.load(open(sys.argv[2])))" $f.json "$D/data/$f.json"
done
$PY independent_audit/checks.py  # ends with "All independent checks passed"
```

Optional full exact replay (several minutes for 300): `$PY exact_check.py
150`, `$PY exact_check.py 300`, then `$PY validate_results.py` again, and
compare the two `exact_values_*.json` with `data/` the same way. The audit
output `independent_audit/checks.json` records SHA-256 hashes of its inputs;
on Windows the regenerated `first_correction.json` is written with CRLF, so
those hashes will differ from the recorded ones even when every value
agrees. `replay.sh` calls bare `python`, which may not resolve on this
machine; the commands above replace it.

At intake (2 October 2026, Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0) the
short replay on a copy took 77 s: the three JSON outputs equalled the
recorded ones up to line endings, and "PASS: independently organized first
corrections agree within 1e-45". The exact `n ≤ 300` recomputation, the
audit program and the PDF rebuild were not rerun then. At this write the
commands above were run on a scratch copy: the three comparisons printed
`True` (41 s for the first three commands), and the audit program printed
"All independent checks passed" (2 min 42 s). The exact `n ≤ 300`
recomputation and the PDF rebuild remain unrerun.

## Build the PDF

pdfLaTeX with geometry, amsmath, amssymb, amsthm, mathtools, booktabs and
hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 15 pages, no
errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source builds to 13 pages, also without warnings.)
`code/build.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to
`orientation-partition-asymptotics.tex`.

## Provenance

- OEIS A372395 and A370613 (accessed 1 October 2026); Z. Sun,
  arXiv:2605.04006v1 (2026), Sections 2, 7–9 and 11; R. P. Stanley, Discrete
  Math. 5 (1973); see the article's bibliography.
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 59 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
