# Rooted Identity Trees with Fixed Maximum Outdegree

**Boundary closure and computable asymptotic inverses: the square-root law
`a_{d,n} = C ρ^(-n) n^(-3/2) (1 + Σ D_j n^(-j))` to every fixed order for each
cap `d ≥ 2`, with the worked cases OEIS A116379 (`d = 3`) and A116380
(`d = 4`)**

A research article dated 2 October 2026, built from one manuscript. It names
no author and no tool (its title block reads "Research article"), and the PDF
metadata has an empty Author field.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 63 | `rooted-identity-trees-source.zip` (wrapper directory `rooted-identity-trees/`), arrival commit `096ee7b87`; main file `report.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized: no Lean or Rocq declaration exists for any
statement of this report. **No priority is claimed:** two especially relevant
older works — Meir–Moon–Mycielski, *Hereditarily finite sets and identity
trees* (JCTB 1983), and Haigh–Kennedy–Quintas, *Counting and coding identity
trees with fixed diameter and bounded degree* (Discrete Appl. Math. 7, 1984) —
were not inspected at full-text level, and the derivative cancellation is
credited to Bell–Burris–Yeats (EJC 13, 2006). Numerical digits are stability
checks, not interval certificates.

## What it proves

`a_{d,n}` counts rooted unlabeled trees with **at most** `d` children at every
vertex and trivial root-preserving automorphism group (siblings pairwise
nonisomorphic); `I_d(z) = Σ a_{d,n} z^n` satisfies the signed root equation
`I = z E_d(I(z), I(z²), …, I(z^d))`.

- **Lemma 2.1.** `1/4 ≤ ρ ≤ 9/20` and `τ = I(ρ) < ∞` for every `d ≥ 2`
  (plane-tree majorant, binary-root discriminant).
- **Proposition 2.2 (explicit transversality).** `F_z(z, I(z)) ≥ (I(z)/z) η`
  with `η = 1 − 810/(319√19) > 0`, independent of `d`.
- **Theorem 3.1.** `(ρ, τ)` is a characteristic point with `F_z, F_yy > 0`,
  the unique singularity on `|z| = ρ`; convergent Puiseux expansion with
  `b_1 < 0` and a Δ-domain.
- **Theorem 4.1.** For every fixed `d ≥ 2` and `R ≥ 0`,
  `a_{d,n} = C ρ^(-n) n^(-3/2) (Σ_{j≤R} D_j n^(-j) + O_{d,R}(n^(-R-1)))`,
  `C = b_1/Γ(−1/2) > 0`, with finite Puiseux and Gamma-ratio generators and
  explicit `D_1`, `D_2`.
- **Table 1.** `ρ, τ, C, D_1, D_2` for `d = 3, 4` to 30 decimals
  (non-certified); for example `ρ_3 = 0.40077450047…`, `C_3 = 0.41431687066…`,
  `D_{3,1} = −0.70839613959…`.
- **Proposition 6.1 and (42)–(44).** Inverses of the specified finite smooth
  model `M_R` by `W_{-1}` with recursive Lambert corrections, and a pure
  logarithmic expansion with polynomials `P_k(h)`, `deg P_k ≤ k`.
- **Proposition 7.1.** The two-ceiling enclosure of `N(y) = min{n : a_n ≥ y}`.

## What is not claimed

- No priority (above); the OEIS pages' "unknown leading asymptotic" comment
  (inspected 2 October 2026 by the manuscript, not re-checked at placement)
  motivates the calculation but "is not evidence of exhaustive priority".
- The classical machinery (the `n^(-3/2)` mechanism, analytic implicit
  functions, Puiseux, Gamma-ratio transfer) is prior work; Genitrini (2016)
  and Gittenberger–Jin–Wallner (2018) are discussed as not covering the
  bounded signed PSET case. The emphasis is the explicit finite-cap closure.
- No uniformity as `d → ∞` (the `d`-independent `η` alone does not give it),
  no convergence of the full asymptotic series, no growing `R`.
- The inverses are of an explicitly specified finite model, with `D_j = 0`
  for `j > R`; no unconditional exact rounding at a jump, no effective
  `K_{d,R}` or certified starting threshold.
- The 1e-60 agreement of three nested-jet runs is a numerical stability
  observation; the two nested routes share the exact counts and later algebra.
- **The inversion is an instance of repository results; no novelty is claimed
  for the method.** The Lambert carrier is `p0:thm:lambert-core`
  (`a = λ`, `b = −3/2`, branch `W_{-1}`; equation (37)), the recursion (39) is
  `p0:thm:lambert-centered` (`Q(t) = log(1 + Σ D_j t^j)`), the pure-log
  expansion is of the kind treated by `p0:thm:flattening` (normalizations not
  matched term by term), and the enclosure has the form of the separation
  condition, part (2) of `p0:thm:staircase`, all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note at the end of Section 7 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; the manuscript used
no ProveIt theorem. The generic staircase arithmetic named in the Section 7
note is formalized as `Fabius.staircase_ceil` and `Fabius.staircase_separation`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `a_{d,n}`.

**Neighbouring reports.** None: no other repository report treats identity
trees, A116379, A116380 or A004111 (searched at placement). The batch-77
report `a000571-tournament-score-sequences` shares only the delivered PDF
build script (byte-identical `build_pdf.sh`).

## Notation

The manuscript reuses letters: `p` is both a power sum `p_r = I(z^r)` and the
exponent `3/2` of the inverse model; `E_j` are cumulative elementary symmetric
functions in Sections 1–4 and inverse coefficients `E_k` in Section 6; `P` is
the plane-tree majorant and the pure-log polynomials `P_k`; `B`, `h`, `N`,
`R`, `K`, `L` have two or three meanings each. A table in the first `[write]`
note (after "Results and conventions") fixes each symbol by section, with the
tempting false readings. No symbol was renamed.

## Labels

Every label carries the prefix `bit:`. The manuscript's 68 labels were
prefixed before anything cited them (every `\ref`/`\eqref` updated); no label
was added. The writing step added four dated `[write]` notes (after "Results
and conventions": provenance, priority caveat, notation table; Section 5: the
table digits and the intake's independent check; Section 7: the
transseries-instance note; Section 9: the shipped layout). No statement,
proof or number of the manuscript was changed.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered as report.tex)
article.pdf                               compiled report, 14 pages
code/README.md                            delivered guide to the generators (delivery commands; see below)
code/check_identity.py                    exact counts by the positive product and an independent Newton recurrence
code/identity_allorders.py                Puiseux/Gamma jets (sum and Taylor-differentiation routes)
code/identity_inverse.py                  Lambert and pure-log inverse generators
code/formal.py                            shared formal-series helpers
code/replay.py                            numerical replay (counts, jets, inverses)
code/reproduce.sh                         runs replay.py
code/replay.sh                            delivered full replay: SHA256SUMS check, reproduce.sh, PDF rebuild
code/build_pdf.sh                         delivered PDF build (compiles report.tex beside it)
code/safe_extract.py                      delivered ZIP-extraction helper (not needed in the repository)
data/README.md                            delivered data conventions
data/identity-checks.json                 exact counts a_0..a_400 for d = 2, 3, 4; 48-decimal characteristic data
data/identity-allorders-checks.json       d = 3, 4 jets: (N, digits, route) = (200,70,sum), (400,110,sum), (250,80,differentiate)
data/identity-inverse-checks.json         original R = K = 4 inverse reference
data/identity-inverse-replay-checks.json  regenerated R = K = 4 inverse results
data/identity-inverse-extended-checks.json R = 2/K = 6 and R = 0/K = 4 model checks
data/replay-validation-summary.json       delivered replay status (Python 3.12.14, mpmath 1.3.0)
data/requirements.txt                     mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `report.tex` to
`article.tex` and moved `replay.sh` and `build_pdf.sh` from the package root,
and `code/requirements.txt`, into `code/` and `data/` respectively; `code/` and
`data/` otherwise keep their delivered names. Not shipped: the delivered
12-page PDF `report.pdf` and `SHA256SUMS` (a checksum ledger, verified 21/21 at
placement and retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/rooted-identity-trees-source.zip > <scratch>/rooted-identity-trees-source.zip`.
Nothing heavy was excluded (the largest data file is the 101 KB count table).

Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` (checks `SHA256SUMS`, then runs `bash build_pdf.sh` and
compares `report.pdf` hashes, all in its own directory), `code/build_pdf.sh`
(compiles `report.tex`), `code/README.md` (`code/requirements.txt`, commands
"from the bundle root"), `data/README.md`, and Section 9 of the article
(`bash replay.sh`, the manifest; dated note). The delivery README, which this
guide replaces, began its replay with `bash replay.sh` and the manifest check.

## Rerun the checks (on a scratch copy)

`code/replay.py` reads `data/` relative to itself and writes only to
`--output-dir` (default: `replay-output/` beside `code/`, which in the
repository would be this directory). Run it on a copy (Git Bash, from this
directory):

```sh
R=$(mktemp -d) && cp -r code data "$R/" && cd "$R"
export PYTHONUTF8=1 PYTHONDONTWRITEBYTECODE=1
uv run --no-project --with mpmath==1.3.0 python code/replay.py --output-dir "$R/out"
diff -q --strip-trailing-cr out/inverse-checks.json data/identity-inverse-replay-checks.json
diff -q --strip-trailing-cr out/inverse-extended-checks.json data/identity-inverse-extended-checks.json
```

(`bash code/reproduce.sh --output-dir "$R/out"` does the same with
`python3`.) It recomputes the counts to `n = 400` for `d = 2, 3, 4` by both
recurrences and compares them with `data/identity-checks.json`, repeats the
three jet runs for `d = 3, 4` (agreement within 1e-60), and checks the
inverse generators. At intake (2 October 2026, heavily loaded machine) it
passed in 41 s; in the write phase it passed in 8 s and both inverse outputs
were identical to the shipped files. `code/replay.sh` cannot run as shipped
(it needs `SHA256SUMS` and `report.tex`/`build_pdf.sh` beside it); recover the
archive above for the byte-identical delivered replay.

## Build the PDF

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, enumitem, xcolor, hyperref, fancyhdr; the preamble uses
`\pdfmapfile`); no BibTeX. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 14 pages, no
errors or warnings, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. (The
delivered source built to 12 pages, also clean.) `code/build_pdf.sh` is kept as
delivered; to use it, copy it to a scratch directory together with
`article.tex` renamed to `report.tex`.

## Provenance

- Bell–Burris–Yeats, Electron. J. Combin. 13 (2006) R63, §§6.1–6.2 and p. 57;
  Flajolet–Sedgewick, *Analytic Combinatorics* (2009), Chapters VI–VII;
  Genitrini, arXiv:1605.00837v2 (2016); Gittenberger–Jin–Wallner, Discrete
  Math. 341 (2018); Meir–Moon–Mycielski (1983) and Haigh–Kennedy–Quintas
  (1984), full texts not inspected; OEIS A116379, A116380 (inspected
  2 October 2026 by the manuscript).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 63 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
