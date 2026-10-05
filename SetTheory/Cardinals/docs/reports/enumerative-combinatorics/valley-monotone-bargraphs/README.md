# A Pole Hierarchy for Valley-Monotone Compositions

**Resolving a bargraph asymptotic conjecture linked to OEIS A001523, with
exponential expansions, limit laws, and Lambert-W inversion (Part I);
critical windows and extreme heights (Part II)**

A research report in two Parts, built from two manuscripts (author lines:
"Research draft prepared for Vladimir Reshetnikov" and "Research manuscript
prepared for Vladimir Reshetnikov"; AI-assisted, although neither manuscript
says so). Part I is dated 1 October 2026, Part II 4 October 2026.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 04 | `OEIS_Valley_Monotone_Bargraphs.zip`, arrival commit `4b874cea0` (main file `article.tex`; its PDF, `build.sh` and `SHA256SUMS.txt` not shipped) | `29aca108e` (1 October 2026; called a "tree SHA" in Section 1.3 and `SOURCE_NOTES.md`, but it is a commit, an ancestor of the placement commit) | `6ea60e367` | Part I (Sections 1–10, Appendices A–B) |
| 02 | batch 98, manuscript 04 | `OEIS_Bargraph_Critical_Windows_and_Extremes.zip`, arrival commit `2172df76a` (inner directory `oeis_bargraph_phase_extremes/`; its `article.tex`, PDF, delivery README, `build.sh` and `SHA256SUMS.txt` not shipped) | `70ab31a1e` (4 October 2026); it read the article blob `f37593705a`, which is Part I as written in `9891e1f5e`, unchanged up to this write | `9353a7171` | Part II (Sections 11–22, Appendices C–D) |

**Status:** AI-assisted (not stated in either manuscript), unrefereed, not
formalized. Rational interval certificates (Part I) and exact enumeration
(both Parts) corroborate the constants and the decompositions; they do not
replace the analytic proofs. Part II's decimals are diagnostics only; none
of its constants is interval-certified.

**The target sequence has no OEIS number.** `d(n)` counts nonempty
compositions of `n` whose interior valley heights are weakly increasing
(the non-decreasing bargraphs of Flórez, Ramírez and Villamizar, by area):
1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1023, 2042, 4071, … . Neither
manuscript verified an OEIS identifier for it, and neither they nor this
report invent one. **A001523** (weakly unimodal compositions, or stacks) is
the *input*: its generating function determines the growth constant and
supplies the unimodal blocks. The known leading asymptotic of A001523
(credited to Auluck in the OEIS) is not claimed, nor posed as open.

## What it proves

**Part I** (source 01):

- **Conjecture 2.3 of Flórez–Ramírez–Villamizar (JCTA 208, 2024)** in its
  proposed form: `d(n) = C λ^n (1 + O(θ^n))` for some `0 < θ < 1`, with
  `λ = 1.97642067794583573531…` and `C = 0.60390151906189910496…`, where
  `ρ = 1/λ` is the unique root in `(0,1)` of `ρ(1-ρ)A(ρ) = 1 + ρ` and `A`
  is the A001523 generating function. The constants are certified by
  standard-library rational interval arithmetic with rigorous tails. The
  digits printed in the 2024 paper (`λ_100 = 1.97642067807…`,
  `C_100 = 0.60390151489…`) are the finite-area ratio at `n = 100`, which
  the report reproduces exactly; they are not the limiting constants.
- A decomposition by minimum part (the generating function is the 2024
  paper's, rederived), meromorphic continuation to the unit disk, and
  **infinitely many simple positive real poles** increasing to 1 with
  alternating amplitudes; hence the generating function is not D-finite and
  `d(n)` is not P-recursive.
- A finite-pole expansion to every radius below 1.
- A central limit theorem for the number of bottom-level valleys and a
  Boltzmann limit for the terminal component.
- **Pole accumulation** (Theorem 7.3, delivered as "Pole accumulation
  transseries"; renamed, see below): `x_j = j·(-log ρ_j)` satisfies
  `x_j = w_j + Σ α_k(c)/w_j^k + …` with `w_j = 2W(√(j/2))`, `c = log 2`,
  `α_1 … α_4` displayed (and `α_5`, `α_6` in `data/expansion_coefficients.json`);
  an inverse of the positive-pole counting function.
- Inversion of finite-sector interpolants of the area count, and two-ceiling
  bounds for the integer threshold `N(Y) = min{n : d(n) >= Y}`.

**Part II** (source 02):

- **The lattice-Gumbel law of the maximum part** (Theorem 17.1), answering
  the extreme-height half of Part I's question 10.4: for the tallest column
  `H_n` of a uniform object of area `n`,
  `P(H_n <= h) = exp(-α n ρ^h) (1 + O(log n / n))` uniformly in the window
  `τ_- <= n ρ^h <= τ_+`, with `α = ρ² P_1(ρ)/M = 0.45020217246…`
  (`P_1 = ∏(1-q^r)^{-2}`, `M` Part I's mean); lattice limits
  `exp(-ρ^{k-θ})` along phase subsequences (no single continuous Gumbel
  limit); `H_n = log n / log λ + O_P(1)`; and asymptotic independence of
  `H_n` and the Gaussian bottom-valley count (Theorem 17.2).
- **A weighted phase transition** (Theorem 13.1): weighting each
  bottom-level valley by `u`, the count is geometric for `u < u_c`, Gaussian
  for `u > u_c` (the ordinary model `u = 1` is this case, Part I's
  Theorem 6.1), and uniform on `[0, 1/M_c]` after scaling at the exact
  critical weight `u_c = ρ_2(1-ρ_2)(1-ρ_2²)/(1+ρ_2⁴) = 0.12218100900…`,
  where `f_n(u_c) = ρ_2^{-n}(κ n + κ_0) + O(R^{-n})`; a first-order
  transition of the growth rate (Corollary 13.2).
- A uniform `1/n` critical window with its first correction (Theorem 14.1)
  and an all-orders window expansion (Proposition 14.2).
- At simultaneous critical weights on `m` levels: a counting polynomial of
  degree `m`, Dirichlet(1,…,1) area fractions, macroscopic covariances
  (Theorem 15.2, Corollary 15.3).
- An exact `q`-product identity for the height tail (Lemma 16.1) and the
  expansion of the height-cutoff pole in `h^k ρ^{rh}` to every order, with
  a Lambert-W top-degree structure (Theorem 16.2).
- The maximum part at criticality: a Dirichlet mixture of Gumbel-type laws
  (Theorem 18.1); with `α_1* = 0.30530…`, `α_0* = 0.37656…` at the first
  critical point, height scale `2.1534 log n` against `1.4678 log n`.
- Inverses: of the cutoff expansion (Theorem 19.2), exact Lambert-W inverses
  of the critical interpolants, and two-ceiling rounding bounds for the
  critical counts and the height quantiles.
- **Proved in writing** (marked `[write]`, not independently reviewed): five
  statements that the manuscript supports only by a sketch, an analogy or
  one line — the tilted multicritical window (Proposition 15.4), the
  phase-chamber classification (Proposition 15.5), the conditional
  intensity of the critical maximum, which is independent of the area
  fractions exactly when all intensities `α_i*` coincide (Proposition 18.2),
  the multicritical rounding and critical quantile bounds
  (Proposition 19.4), and the monotonicity of the interpolated cutoff shift
  (Lemma 19.1). Section 21.8 lists them.

## What is not claimed

- No exhaustive priority search in either source; targeted searches found
  no earlier proof (a limited observation). The generating-function
  decomposition is the 2024 paper's. Source 02 could not access the full
  publisher text of that paper (bibliographic record and OEIS link only)
  and makes no assertion about uninspected passages of it.
- The limitations listed in `SOURCE_NOTES.md` and Appendix B: that the
  positive real poles exhaust the pole spectrum; that `ρ_2` is
  second-smallest in modulus; simplicity at every nonreal zero; convergence
  of a sum over all poles; a natural boundary on the unit circle; uniform
  asymptotics when the minimum part grows; the leading beyond-all-orders
  pole correction; a canonical interpolation or an unconditional ceiling
  formula for the inverse. None of these is proved.
- Part II's limitations (its ledger, Section 22, and
  `02-critical-windows-SOURCE_NOTES.md`): all results are for fixed weights
  and a fixed number `m` of critical levels, with no uniformity when `m`
  grows; no natural-boundary theorem and no classification of nonreal
  poles; the cutoff-pole expansion is finite-order, with no convergence,
  Borel or Stokes claim (the manuscript's ledger called it a "transseries";
  the write does not); its decimals are diagnostics, its symbolic checks
  verify finite identities only, and JSON keys such as `exact_cdf`,
  `exact_ratio` denote a finite recurrence at approximate weights, not
  enclosures. The weighted and multicritical problems are new formulations,
  not previously posed OEIS conjectures, and the ordinary model is
  supercritical, not critical.
- **Open from Part I's question 10.4:** a joint normal law for the additive
  statistics (columns, ones, peak heights) with a nondegenerate covariance
  matrix. Part II does not address it. Part I's questions 10.1–10.3, 10.5
  and 10.6 remain open; Part II restates 10.2 and 10.5 without answering
  them (Section 21.6).
- `numerics.py` values other than `ρ`, `λ`, `C` are exploratory, not
  certified (the file says so).
- **The Lambert-W and rounding material is an instance of repository
  results, with no novelty claimed for the method.** Source 01 placed
  itself in the `Analysis/Transseries` programme and called Theorem 7.3 a
  "transseries"; it is a single-scale Lambert-W expansion of pole positions.
  Its core `X + 2 log X = log(2j)` is `p0:thm:lambert-core`, its correction
  series is `p0:thm:core-reversion` (with `Λ = 1`, `h = 0`, `t = 1/w_j`),
  Proposition 8.2 is `p0:thm:staircase` (parts 1 and 2), and the series of
  Theorem 8.1 is Lagrange reversion (formally `p0:thm:LB`), all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  In Part II, the critical inverse (19.4) is the same core with `a = L_c`,
  `b = 1`, the multicritical inverse (19.7) the core with `a = L_m`,
  `b = m`, (19.8) and Theorem 19.2 are reversion, and Propositions 19.3 and
  19.4(i) and the quantile ceilings are the staircase theorem. Dated
  `[write]` notes (Sections 7.2, 8.2 and 19) say so.
- Sections 10 and 21 are questions, not results.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; neither
manuscript used a ProveIt theorem. The generic staircase lemmas cited in
Sections 8.2 and 19 are formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
they concern an arbitrary monotone interpolation, not `d(n)` or the critical
counts.

**Part II and Part I.** Part II re-proves Part I's decomposition lemmas,
continuation, root ladder and dominant pole (Lemmas 12.1, 12.2), and its
supercritical case `u = 1` is Part I's bottom-valley CLT; Table 1
(Section 11.2) lists every overlap, and these are printed as second routes.
Part II's notation differs from Part I's and from its manuscript in places:
Table 2 (Section 11.3) lists every renaming (for example the manuscript's
`R = ρ_2` and critical `M, V` are printed `ρ_2`, `M_c`, `V_c`, so that
`R` stays a radius and `M, V` stay Part I's moments).

**Placement.** The report is in the research-report collection, not in
`Analysis/Transseries` (no transseries in that project's sense is built),
and not among the OEIS-sequence asymptotics reports (the target has no OEIS
number). No other collection report treats bargraphs, valley-monotone
compositions or A001523; `log-concavity-and-unimodality/q-integer-product-unimodality`
shares only the word "unimodal". Lattice-Gumbel laws in other reports
(for example `oeis-sequence-asymptotics/a022629-distinct-partition-norms`) concern other objects;
the kinship is one of method only.

## Labels

Every label carries the prefix `vmb:`. Part I's 73 labels (source 01's,
prefixed in the batch-75 write) are unchanged in name and number. Part II's
labels carry `vmb:cw:` (critical windows): source 02's 104 labels, prefixed
before anything cited them, and 18 added in writing (provenance, notation
and claims sections, the five `[write]` propositions and lemmas, one
equation, the further-questions subsections, the ledger section, the Part
and Appendix D), so the count is 195 (`vmb:cw:` 122). Changes besides the
prefix in Part II are listed in Section 11: renamed symbols (Table 2), the
macros `\Pp`, `\coef` printed as Part I's `\Prob`, `\coeff`, the package
`bm` and the operators `\Cov`, `\Dir`, `\Unif` added to the preamble, the
manuscript's unused `\cO`, `\tr` dropped, citations of Part I printed as
cross-references, the ledger row "Cutoff-pole transseries and inverse"
renamed "Cutoff-pole expansion and inverse" and the ledger set
ragged-right, and dated `[write]` notes and inline `[write: …]`
identifications. No statement, proof or number of source 02 was otherwise
changed. In Part I the batch-98 write added only dated notes (after the
abstract, in Section 1.3 and at question 10.4), the Part and appendix
entries of the table of contents, and the preamble lines; Part I's
statements, labels and numbering are unchanged.

## Files

```text
README.md                                         this guide (replaces both delivery READMEs)
SOURCE_NOTES.md                                   source 01: sources consulted, repository review, unproved items, as delivered
02-critical-windows-SOURCE_NOTES.md               source 02: source audit, provenance, novelty boundary, as delivered
article.tex                                       the report, Parts I and II
article.pdf                                       compiled report, 53 pages
code/verify.py                                    source 01: exact coefficients to area 200, brute force to 17, interval certificate; writes verification.json
code/numerics.py                                  source 01: exploratory high-precision poles, amplitudes, limit-law constants (imports verify)
code/expansion.py                                 source 01: symbolic alpha_1..alpha_6 of Theorem 7.3; writes expansion_coefficients.json
code/02-critical-windows-verify.py                source 02: 84 enumeration-vs-recurrence checks to area 14, A001523 to 20, coefficients to 240; writes exact_checks.json
code/02-critical-windows-symbolic_checks.py       source 02: five finite symbolic identity groups (SymPy); writes symbolic_checks.json
code/02-critical-windows-numerics.py              source 02: critical constants, window, height and pole-shift diagnostics (mpmath; imports verify); writes numerical_checks.json
code/02-critical-windows-critical_extremes.py     source 02: critical mixed extremes and a two-level window (mpmath; imports verify, numerics; reads numerical_checks.json); writes critical_extreme_checks.json
data/verification.json                            source 01: recorded verify.py output (d(n) and A001523 through 200, certificate)
data/numerical_results.json                       source 01: recorded numerics.py output (8 real poles, error table; not certified)
data/expansion_coefficients.json                  source 01: recorded expansion.py output (order 6)
data/requirements-optional.txt                    source 01: mpmath, sympy (unpinned; not needed by verify.py)
data/BUILD_INFO.json                              source 01: delivery build record (Python 3.13.5, mpmath 1.3.0, sympy 1.14.0)
data/02-critical-windows-exact_checks.json        source 02: recorded verify.py output (check list, D_1, U_2, D_2 to 240)
data/02-critical-windows-symbolic_checks.json     source 02: recorded symbolic_checks.py output
data/02-critical-windows-numerical_checks.json    source 02: recorded numerics.py output (diagnostics, not enclosures)
data/02-critical-windows-critical_extreme_checks.json  source 02: recorded critical_extremes.py output
data/02-critical-windows-requirements.txt         source 02: mpmath==1.3.0, sympy==1.14.0 (versions of the recorded run)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped from source 01: the delivered
PDF, `build.sh` (three `pdflatex` runs) and `SHA256SUMS.txt` (verified
13/13 at placement). Not shipped from source 02: its `article.tex` (printed
as Part II), PDF, delivery README, `build.sh` (two `pdflatex` runs) and
`SHA256SUMS.txt` (verified 14/14 at placement); all survive in the arrival
commit `2172df76a` (`git show 2172df76a:docs/incoming/OEIS_Bargraph_Critical_Windows_and_Extremes.zip`).
Source 01's package was flat and source 02's had `code/` and `data/`;
placement put both into `code/` and `data/`, source 02's files with the
prefix `02-critical-windows-`.

Delivered text that names the delivered layout or unshipped files: the
delivery READMEs (not shipped); Section 9.3 of the article (`python
verify.py`, `pdflatex article.tex`; a dated note added); Section 20.4 (`python
code/verify.py` … and `pdflatex article.tex` for the delivered package; a
dated note added); `data/BUILD_INFO.json`, whose `pdf` field ("18 pages")
describes source 01's delivered PDF; and source 02's programs, which write
unprefixed names (`exact_checks.json`, …) into a sibling `data/` and import
`verify` and `numerics` by their delivered names. Inside this directory
those imports would resolve to source 01's `code/verify.py` and
`code/numerics.py`, which lack the imported functions (`coefficients`,
`root`, `moment`), so they fail with an ImportError rather than silently.

**Data key names in source 02's JSON** differ from the article's symbols:
`R` is `ρ_2`, `R3` is `ρ_3`, `P` is `P_1(ρ)`, `A` is `α`, `physical_M`,
`physical_V` are Part I's `M`, `V`, `critical_M`, `critical_V`, `Jc`,
`critical_D`, `critical_d` are `M_c`, `V_c`, `J_c`, `D_c`, `d_c`,
`critical_height_alpha1`, `critical_height_alpha2` are `α_1*`, `α_0*`,
`critical_level2_M` is `M_2(ρ_2)`, `shift` is `a_c = κ_0/κ`, and `u1`, `u2`,
`M1`, `M2` of the two-level record are `u_1*`, `u_2*`, `M_1*`, `M_2*` at
`m = 2` (Section 20.4 note).

**OEIS data.** `code/verify.py` (source 01) and
`code/02-critical-windows-verify.py` (source 02) hard-code initial terms of
A001523 (through `n = 20`), and `data/verification.json` records A001523
through 200 as computed by source 01; OEIS sequence data are licensed
CC BY-SA 4.0. The arrays `D1`, `U2`, `D2` of
`data/02-critical-windows-exact_checks.json` are computed, not OEIS data.
Nothing was submitted to the OEIS.

## Rerun the checks (on a scratch copy)

Every program writes its output into a fixed location relative to itself,
so never run them inside this directory. Source 01's programs write next to
themselves (`Path(__file__).with_name`), and `numerics.py` imports
`verify`. Copy `code/` to a scratch directory and run there (Git Bash, from
this directory):

```sh
R=$(mktemp -d) && cp code/verify.py code/numerics.py code/expansion.py "$R" && cd "$R"
uv run --no-project python verify.py                                          # standard library only
uv run --no-project --with mpmath==1.3.0 python numerics.py
uv run --no-project --with sympy==1.14.0 python expansion.py                  # order 6: slow
uv run --no-project --with sympy==1.14.0 python -c "from expansion import coefficients; print(coefficients(5)[2])"   # order 5: quick
```

Source 02's programs need their delivered names and a sibling `data/`
directory, and must run in this order (`critical_extremes.py` reads the
`numerical_checks.json` that `numerics.py` writes):

```sh
R=$(mktemp -d) && mkdir -p "$R/code" "$R/data"
for f in verify symbolic_checks numerics critical_extremes; do
  cp "code/02-critical-windows-$f.py" "$R/code/$f.py"
done
cd "$R"
uv run --no-project python code/verify.py                                     # standard library only
uv run --no-project --with sympy==1.14.0 python code/symbolic_checks.py
uv run --no-project --with mpmath==1.3.0 python code/numerics.py
uv run --no-project --with mpmath==1.3.0 python code/critical_extremes.py
```

Do not use `python -O` (the checks are assertions). Then compare each
`data/<name>.json` of the scratch copy with `data/<name>.json` (source 01)
or `data/02-critical-windows-<name>.json` (source 02) here, modulo line
endings (on Windows the programs write CRLF).

**Runtimes and what has been rerun.** Source 01: at intake (placement, 1–2
October 2026, under load) `verify.py` (11 s) and `numerics.py` (105 s)
passed with JSON-equal output, but **the order-6 `expansion.py` run timed
out at 175 s and was not rerun**; only order 5 was checked (16 s), and it
reproduced `α_1 … α_5` of `data/expansion_coefficients.json` exactly. At
the batch-75 write (2 October 2026, lighter load) all three programs ran on a
scratch copy: `verify.py` 2 s, `numerics.py` 31 s, **`expansion.py` (order
6) 94 s**, and all three outputs equal the shipped files modulo line
endings. Expect the order-6 run to take one to three minutes or more on a
loaded machine. Source 02: at placement (5 October 2026) the four programs
passed in 2 s, 25 s, 96 s and 141 s; at the batch-98 write (5 October 2026,
Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0), with the recipe above, in 1 s,
5 s, 25 s and 34 s. Both times `verify.py` reported 84 passing enumeration
checks, A001523 terms 0..20 and coefficients through 240, `symbolic_checks.py`
PASS on five identity groups, and all four JSON outputs were equal to the
shipped files as JSON (bytes differ only by CRLF).

## Build the PDF

pdfLaTeX with Latin Modern, microtype, amsmath, amsthm, mathtools, bm,
booktabs, longtable, enumitem, TikZ, fancyhdr and hyperref. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 53 pages (Part I on
pages 5–20, Part II on pages 21–50, appendices and references after), no
errors, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. (Source 01
built to 18 pages and source 02 to 24 pages as delivered; Part I alone built
to 19 pages after the batch-75 write.)

## Provenance

- Flórez, Ramírez, Villamizar, *Restricted bargraphs and unimodal
  compositions*, JCTA 208 (2024) 105934 (publisher HTML consulted 1 October
  2026 by source 01; source 02 had the bibliographic record only); OEIS
  A001523 (consulted 1 and 4 October 2026); Flajolet–Sedgewick, *Analytic
  Combinatorics* (2009). `SOURCE_NOTES.md` and
  `02-critical-windows-SOURCE_NOTES.md` record what was read and searched.
- Repository input: source 01 read `Analysis/Transseries/README.md` at
  `29aca108e` for context (searches for "bargraphs" and "A001523" found
  nothing); source 02 read Part I's `article.tex` at `70ab31a1e`.
- Batch 75 of `docs/incoming`, manuscript 04: arrival `4b874cea0`,
  placement `6ea60e367`, written in the batch-75 write (2 October 2026,
  `9891e1f5e`).
- Batch 98 of `docs/incoming`, manuscript 04: arrival `2172df76a`,
  placement `9353a7171` (batch 98A), written in the batch-98 write
  (5 October 2026) as Part II. The write chose to print the manuscript in
  full with Part I's notation for shared objects, to keep its re-proofs of
  Part I as second routes, and to prove five sketched statements rather
  than list them as open.
