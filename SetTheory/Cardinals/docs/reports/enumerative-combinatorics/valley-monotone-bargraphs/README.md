# A Pole Hierarchy for Valley-Monotone Compositions

**Resolving a bargraph asymptotic conjecture linked to OEIS A001523, with
exponential expansions, limit laws, and Lambert-W inversion**

A research report dated 1 October 2026, built from one manuscript (author
line: "Research draft prepared for Vladimir Reshetnikov"; AI-assisted,
although the manuscript does not say so).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 04 | `OEIS_Valley_Monotone_Bargraphs.zip`, arrival commit `4b874cea0` (main file `article.tex`; its PDF, `build.sh` and `SHA256SUMS.txt` not shipped) | `29aca108e` (1 October 2026; called a "tree SHA" in Section 1.3 and `SOURCE_NOTES.md`, but it is a commit, an ancestor of the placement commit) | `6ea60e367` | the whole report |

**Status:** AI-assisted (not stated in the manuscript), unrefereed, not
formalized. Rational interval certificates and exact enumeration corroborate
the constants and the decomposition; they do not replace the analytic proofs.

**The target sequence has no OEIS number.** `d(n)` counts nonempty
compositions of `n` whose interior valley heights are weakly increasing
(the non-decreasing bargraphs of Flórez, Ramírez and Villamizar, by area):
1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1023, 2042, 4071, … . The manuscript
verified no OEIS identifier for it and invents none; neither does this
report. **A001523** (weakly unimodal compositions, or stacks) is the
*input*: its generating function determines the growth constant. The
known leading asymptotic of A001523 (credited to Auluck in the OEIS) is
not claimed.

## What it proves

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

## What is not claimed

- No exhaustive priority search; targeted searches found no earlier proof
  (a limited observation). The generating-function decomposition is the
  2024 paper's.
- The limitations listed in `SOURCE_NOTES.md` and Appendix B: that the
  positive real poles exhaust the pole spectrum; that `ρ_2` is
  second-smallest in modulus; simplicity at every nonreal zero; convergence
  of a sum over all poles; a natural boundary on the unit circle; uniform
  asymptotics when the minimum part grows; the leading beyond-all-orders
  pole correction; a canonical interpolation or an unconditional ceiling
  formula for the inverse. None of these is proved.
- `numerics.py` values other than `ρ`, `λ`, `C` are exploratory, not
  certified (the file says so).
- **The Lambert-W and rounding material is an instance of repository
  results, with no novelty claimed for the method.** The manuscript placed
  itself in the `Analysis/Transseries` programme and called Theorem 7.3 a
  "transseries"; it is a single-scale Lambert-W expansion of pole positions.
  Its core `X + 2 log X = log(2j)` is `p0:thm:lambert-core`, its correction
  series is `p0:thm:core-reversion` (with `Λ = 1`, `h = 0`, `t = 1/w_j`),
  Proposition 8.2 is `p0:thm:staircase` (parts 1 and 2), and the series of
  Theorem 8.1 is Lagrange reversion (formally `p0:thm:LB`), all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  Two dated `[write]` notes (Sections 7.2 and 8.2) say so.
- Section 10's research directions are questions, not results.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase lemmas cited in
Section 8.2 are formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
they concern an arbitrary monotone interpolation, not `d(n)`.

**Placement.** The report is in the research-report collection, not in
`Analysis/Transseries` (no transseries in that project's sense is built),
and not among the OEIS-sequence asymptotics reports (the target has no OEIS
number). No collection report treats bargraphs, valley-monotone
compositions or A001523; `log-concavity-and-unimodality/q-integer-product-unimodality`
shares only the word "unimodal" (unimodality of products of q-integers).

## Labels

Every label carries the prefix `vmb:`. The manuscript's 73 labels were
prefixed before anything cited them (20 `\ref` and 35 `\eqref` updated); no
label was added, so the count is 73. Changes besides the prefix: Theorem
7.3's name (from "Pole accumulation transseries" to "Pole accumulation: a
Lambert–W expansion"), a ragged-right bibliography (removing four underfull
boxes present in the delivered build), four dated `[write]` notes (Section
1.3: provenance, pin, placement, formal status; Section 7.2 and Section 8.2:
instance notes; Section 9.3: files) and one bibliography entry (`vmb-tai`).
No other statement, proof or number was changed.

## Files

```text
README.md                          this guide (replaces the delivery README)
SOURCE_NOTES.md                    sources consulted, repository review, unproved items, as delivered
article.tex                        the report (delivered under the same name)
article.pdf                        compiled report, 19 pages
code/verify.py                     exact coefficients to area 200, brute force to 17, interval certificate; writes verification.json
code/numerics.py                   exploratory high-precision poles, amplitudes, limit-law constants (imports verify)
code/expansion.py                  symbolic alpha_1..alpha_6 of Theorem 7.3; writes expansion_coefficients.json
data/verification.json             recorded verify.py output (d(n) and A001523 through 200, certificate)
data/numerical_results.json        recorded numerics.py output (8 real poles, error table; not certified)
data/expansion_coefficients.json   recorded expansion.py output (order 6)
data/requirements-optional.txt     mpmath, sympy (unpinned; not needed by verify.py)
data/BUILD_INFO.json               delivery build record (Python 3.13.5, mpmath 1.3.0, sympy 1.14.0)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Not shipped: the delivered PDF, `build.sh`
(three `pdflatex` runs; replaced by the build command below) and
`SHA256SUMS.txt` (verified 13/13 at placement). The delivered package was
flat; placement split it into `code/` and `data/`. Delivered text that names
the flat layout or unshipped files: the delivery README (not shipped),
Section 9.3 of the article (`python verify.py`, `pdflatex article.tex`; a
dated note added), and `data/BUILD_INFO.json`, whose `pdf` field ("18
pages") describes the delivered PDF, not this one.

## Rerun the checks (on a scratch copy)

Every program writes its output next to itself (`Path(__file__).with_name`),
so running it in `code/` would add files there, and `numerics.py` imports
`verify`. Copy `code/` to a scratch directory and run there (Git Bash, from
this directory):

```sh
R=$(mktemp -d) && cp code/*.py "$R" && cd "$R"
uv run --no-project python verify.py                                          # standard library only
uv run --no-project --with mpmath==1.3.0 python numerics.py
uv run --no-project --with sympy==1.14.0 python expansion.py                  # order 6: slow
uv run --no-project --with sympy==1.14.0 python -c "from expansion import coefficients; print(coefficients(5)[2])"   # order 5: quick
```

Do not use `python -O` (the checks are assertions). Then compare the three
JSON files with `data/` modulo line endings (on Windows the programs write
CRLF).

**Runtimes and what has been rerun.** At intake (placement, 1–2 October
2026, under load) `verify.py` (11 s) and `numerics.py` (105 s) passed with
JSON-equal output, but **the order-6 `expansion.py` run timed out at 175 s
and was not rerun**; only order 5 was checked (16 s), and it reproduced
`α_1 … α_5` of `data/expansion_coefficients.json` exactly. At this write
(2 October 2026, lighter load) all three programs ran on a scratch copy:
`verify.py` 2 s, `numerics.py` 31 s, **`expansion.py` (order 6) 94 s**, and
all three outputs equal the shipped files modulo line endings. Expect the
order-6 run to take one to three minutes or more on a loaded machine.

## Build the PDF

pdfLaTeX with Latin Modern, microtype, amsmath, amsthm, mathtools, booktabs,
longtable, enumitem, TikZ, fancyhdr and hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 19 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. (The delivered source
built to 18 pages, with four underfull boxes in the bibliography.)

## Provenance

- Flórez, Ramírez, Villamizar, *Restricted bargraphs and unimodal
  compositions*, JCTA 208 (2024) 105934 (publisher HTML consulted 1 October
  2026); OEIS A001523; Flajolet–Sedgewick, *Analytic Combinatorics* (2009).
  `SOURCE_NOTES.md` records what was read and searched.
- Repository input: `Analysis/Transseries/README.md` at `29aca108e`, read
  for context; searches for "bargraphs" and "A001523" found nothing.
- Batch 75 of `docs/incoming`, manuscript 04; arrival `4b874cea0`, placement
  `6ea60e367`, written in the batch-75 write phase (2 October 2026).
