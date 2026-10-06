# Rooted Identity Trees with Fixed Maximum Outdegree

**Boundary closure and computable asymptotic inverses: the square-root law
`a_{d,n} = C ρ^(-n) n^(-3/2) (1 + Σ D_j n^(-j))` to every fixed order for each
cap `d ≥ 2`, with the worked cases OEIS A116379 (`d = 3`) and A116380
(`d = 4`). Part II: rational-interval certificates of the constants for
`d = 3, 4`, and a second route to the theorem**

A research article in two Parts, built from two manuscripts, both dated
2 October 2026. Neither names an author or a tool: Part I's title block reads
"Research article" and its PDF metadata has an empty Author field; Part II's
source reads "Research report" in both places.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 63 | `rooted-identity-trees-source.zip` (wrapper directory `rooted-identity-trees/`), arrival commit `096ee7b87`; main file `report.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | Part I, Sections 1–10 |
| 02 | batch 103, bundle Report 130 | `A116379_A116380_All_Orders_Identity_Trees_and_Inversion_Source.zip` (wrapper directory `Report130/`), arrival commit `60f54ea06`; main file `Report130.tex` with `\input{certified_constants.tex}`, merged into `article.tex` | none: "standalone", names no ProveIt commit, does not know source 01 | `9c995cefe` (prefix `02-certified-`) | Part II, Sections 11–19 |

**Status:** presumed AI-assisted (neither delivery names an author or a tool),
unrefereed, not formalized: no Lean or Rocq declaration exists for any
statement of this report. **No priority is claimed** by either source. Four
relevant older works were not inspected at full-text level:
Meir–Moon–Mycielski, *Hereditarily finite sets and identity trees* (JCTB
1983), and Haigh–Kennedy–Quintas, *Counting and coding identity trees with
fixed diameter and bounded degree* (Discrete Appl. Math. 7, 1984), both cited
by Part I; Labelle, *Counting asymmetric enriched trees* (J. Symbolic Comput.
14, 1992), and Kennedy–McKeon–Palmer–Robinson, *Asymptotic number of
symmetries in locally restricted trees* (Discrete Appl. Math. 26, 1990), cited
by Part II after abstract-level checks. The derivative cancellation is
credited to Bell–Burris–Yeats (EJC 13, 2006). Part I's 30-digit constants were
stability checks as delivered; since Part II they are certified for `d = 3, 4`
by a computer-assisted interval computation (below).

## What it proves

`a_{d,n}` counts rooted unlabeled trees with **at most** `d` children at every
vertex and trivial root-preserving automorphism group (siblings pairwise
nonisomorphic); `I_d(z) = Σ a_{d,n} z^n` satisfies the signed root equation
`I = z E_d(I(z), I(z²), …, I(z^d))`.

### Part I (source 01)

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
- **Table 1.** `ρ, τ, C, D_1, D_2` for `d = 3, 4` to 30 decimals (delivered as
  non-certified; every entry is now certified to be correctly rounded, see
  Part II); for example `ρ_3 = 0.40077450047…`, `C_3 = 0.41431687066…`,
  `D_{3,1} = −0.70839613959…`.
- **Proposition 6.1 and (42)–(44).** Inverses of the specified finite smooth
  model `M_R` by `W_{-1}` with recursive Lambert corrections, and a pure
  logarithmic expansion with polynomials `P_k(h)`, `deg P_k ≤ k`.
- **Proposition 7.1.** The two-ceiling enclosure of `N(y) = min{n : a_n ≥ y}`.

### Part II (source 02)

- **Section 16, Tables 4–6 (new).** A rational-interval certificate
  (fixed denominator `10^90`, outward rounding, Machin `π`, `artanh`
  logarithm with remainder, Catalan tail bounds for the nested jets) encloses
  `ρ, τ, C, c_1 = D_1, c_2 = D_2, λ = log(1/ρ), b = −(3/2) log λ − log C` and
  the Puiseux coefficients `β_1, …, β_5` (`= b_1, …, b_5`) for `d = 3, 4`; the
  radius brackets have width `10^(-45)`, every other enclosure width at most
  `1.4·10^(-41)`. A global monotonicity argument (`M(z) = F(z, y_*(z))`,
  `M' = G_z > 0`) identifies the critical root uniquely on `0 < z ≤ 9/20`.
  Table 6 (written at the write) prints every enclosure of
  `data/02-certified-certificate.json` in full, including `β_1, …, β_5`.
  Remark 16.2: every entry of Part I's Table 1 and of its `E_1, E_2` table is
  the correctly rounded value of the certified quantity.
- **Section 13 (second route to Lemma 2.1, strict).** An explicit infinite
  injective family of binary identity trees,
  `H(z) = z^21/(1 − z(1 + S(z)))`, `S` the binary counts through size 20,
  gives `ρ_d ≤ ρ_2 ≤ r < 9/20`; the exact rational `9/20 (1 + S(9/20)) − 1 > 0`
  is printed, and the write's Remark 13.1 brackets
  `0.4464104 < r < 0.4464105`.
- **Theorem 12.1** is Lemma 2.1 with Theorems 3.1 and 4.1 (a second proof;
  its transversality bound (71) is weaker than Proposition 2.2 and holds at
  the critical point only). **(82)** is Part I's (31).
- **(80) (new formula).** A purely rational recurrence for the Gamma-ratio
  coefficients; the write's Proposition 15.1 proves it equals Part I's
  Bernoulli route (28)–(29).
- **Theorem 17.1** (integer inverse brackets with the pure-log approximant
  `f_M(log T)`) is Proposition 7.1 with (42) in another normalization (the
  write's Remark 17.2 derives it from them).
- **Section 18.** An exact threshold algorithm (doubling plus binary search on
  exact counts) that certifies `N_d(T)` for a given `T` by integer comparisons
  alone.

The proofs written at the write (not in either source) are Proposition 15.1,
Remarks 13.1, 16.1, 16.2 and 17.2, and the citation correction Remark 11.1.

## What is not claimed

- No priority (above); the OEIS pages' "unknown leading asymptotic" comment
  (inspected 2 October 2026 by both manuscripts, not re-checked at intake)
  motivates the calculation but "is not evidence of exhaustive priority".
- The classical machinery (the `n^(-3/2)` mechanism, analytic implicit
  functions, Puiseux, Gamma-ratio transfer) is prior work; Genitrini (2016)
  and Gittenberger–Jin–Wallner (2018) are discussed as not covering the
  bounded signed PSET case. The emphasis is the explicit finite-cap closure.
- No uniformity as `d → ∞` (the `d`-independent `η` alone does not give it),
  no convergence of the full asymptotic series, no growing `R`.
- The inverses are of an explicitly specified finite model, with `D_j = 0`
  for `j > R`; no unconditional exact rounding at a jump, no effective
  `K_{d,R}` (Part II: `K`, `T_0`) or certified starting threshold; in general
  `N_d(T) ≠ f_M(log T) + o(1)`.
- Part I's 1e-60 agreement of three nested-jet runs is a numerical stability
  observation; the two nested routes share the exact counts and later algebra.
- **Part II's certificate** is computer-assisted (exact integer interval
  arithmetic in Python), not a proof-assistant development. It uses the
  qualitative theorem to identify the radius and does not independently prove
  analytic continuation. The executable is specialized to `d = 3, 4`,
  `N = 400` and local jet degree 6 (`c_1, c_2`, `β_1, …, β_5`); `c_j` for
  `j ≥ 3` and other caps are specified, not implemented. The 90-place JSON
  strings record the arithmetic grid, not 90 certified digits. The constant
  enclosures give no coefficient-remainder bound or finite-threshold
  guarantee. Hashes give file identity, not authenticity; nothing was
  uploaded, submitted or published.
- **The inversion is an instance of repository results; no novelty is claimed
  for the method.** The Lambert carrier is `p0:thm:lambert-core`
  (`a = λ`, `b = −3/2`, branch `W_{-1}`; equation (37)), the recursion (39) is
  `p0:thm:lambert-centered` (`Q(t) = log(1 + Σ D_j t^j)`), the pure-log
  expansion is of the kind treated by `p0:thm:flattening` (normalizations not
  matched term by term), and the enclosure has the form of the separation
  condition, part (2) of `p0:thm:staircase`, all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note at the end of Section 7 says so; Part II's
  Theorem 17.1 is the same instance.

## Corrections and open questions

- **Wrong citation (source 02), corrected.** Report 130's bibliography
  attributes *Counting and coding identity trees with fixed diameter and
  bounded degree* (Discrete Appl. Math. 7 (1984) 141–160,
  doi:10.1016/0166-218X(84)90063-5) to "G. W. Furnas". Its authors are
  C. W. Haigh, J. W. Kennedy and L. V. Quintas (Crossref, checked
  5 October 2026); Part I already cites it correctly. Part II cites it as
  Part I's entry, with Remark 11.1 recording the error. No mathematical claim
  of either source was found to be wrong.
- **Part I's further question 1** ("Certify ρ, C, D_j by interval root and tail
  bounds, then make (49) effective") is half answered: certified for
  `d = 3, 4` and `j ≤ 2`; `j ≥ 3`, other caps and the effective ceiling stay
  open (dated note there).
- Section 19 (Part II's further questions): effective `K`, `T_0`; certified
  `c_j`, `j ≥ 3`, and other caps; uniformity in `d`; **unrooted identity trees
  with a total-degree bound (new)**; the four unchecked older papers; the
  OEIS status statements.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; neither manuscript
used a ProveIt theorem. The generic staircase arithmetic named in the
Section 7 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `a_{d,n}`.

**Neighbouring reports.** No other repository report treats identity trees,
A116379, A116380 or A004111. Related material, none of it a shared theorem:

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a182220-source-boundary`
  counts extensional acyclic digraphs, the other classical coding of
  hereditarily finite sets, and points to this report (Part II's manuscript
  describes bounded identity trees as hereditarily finite sets of bounded
  cardinality).
- `a333497-historic-trees` and the other batch-77 tree reports share only
  generic singularity analysis; `a000571-tournament-score-sequences` shares
  only the delivered PDF build script (byte-identical `code/build_pdf.sh`).

*Dated note (5 October 2026, batch 103).* Until this write this paragraph read
"None: no other repository report treats identity trees, A116379, A116380 or
A004111 (searched at placement)". That was true at placement (2 October 2026)
but stale since 3 October 2026, when the batch-85 write of
`a182220-source-boundary` (`eab47e330`) began citing this report.

## Notation

Part I reuses letters: `p` is both a power sum `p_r = I(z^r)` and the
exponent `3/2` of the inverse model; `E_j` are cumulative elementary symmetric
functions in Sections 1–4 and inverse coefficients `E_k` in Section 6; `P` is
the plane-tree majorant and the pure-log polynomials `P_k`; `B`, `h`, `N`,
`R`, `K`, `L` have two or three meanings each. A table in the first `[write]`
note (after "Results and conventions") fixes each symbol by section, with the
tempting false readings.

Part II prints source 02's symbols unchanged; Section 11.3 has a dictionary.
The dangerous clash is the **swap of `F` and `G`**: Part II's
`G = z Σ_{j≤d} P_j` is Part I's `F`, and Part II's `F = G − y` is **minus**
Part I's `G`. Also: Part II's `E_j` are Part I's evaluated `e_j` and its
`Φ_j` Part I's cumulative `E_j`; `β_m, c_j` are `b_m, D_j`; `T(z)` is Part I's
`P(z)`, `T_{k,j} = (−1)^j N_{k,j}`, and `T` is also the threshold target;
`B(x) = x Φ_{d−1}` is Part I's `H`; `η` is a Δ-domain radius, not Part I's
margin; `L = log T` (Part I: `log(y/C)`); `u` and `M` have two and three
meanings. No symbol was renamed. Bibliography keys were merged into Part I's
(`bby`, `genitrini`, `fs`, `oeis3`, `oeis4`, `hkq`); `labelle` and `kmpr` were
added.

## Labels

Every label carries the prefix `bit:`. Part I's 68 labels were prefixed at its
write and keep their numbers. Part II's labels carry `bit:cert:`: the 65
labels of source 02 (prefixed before anything cited them) and 20 added by the
write (sections, tables, remarks, Proposition 15.1, `bit:cert:part`); the
write also added `bit:part:one`. Total 154 (`\label` count, with the
`\label[type]{…}` form included). The `.aux` files of the committed and new
builds give all 68 Part I labels the same numbers.

## Files

```text
README.md                                 this guide (replaces both delivery READMEs)
article.tex                               the report (Part I delivered as report.tex; Part II merged from Report130.tex and certified_constants.tex)
article.pdf                               compiled report, 34 pages
code/README.md                            Part I: delivered guide to the generators (delivery commands; see below)
code/check_identity.py                    Part I: exact counts by the positive product and an independent Newton recurrence
code/identity_allorders.py                Part I: Puiseux/Gamma jets (sum and Taylor-differentiation routes)
code/identity_inverse.py                  Part I: Lambert and pure-log inverse generators
code/formal.py                            Part I: shared formal-series helpers
code/replay.py                            Part I: numerical replay (counts, jets, inverses)
code/reproduce.sh                         Part I: runs replay.py
code/replay.sh                            Part I: delivered full replay: SHA256SUMS check, reproduce.sh, PDF rebuild
code/build_pdf.sh                         Part I: delivered PDF build (compiles report.tex beside it)
code/safe_extract.py                      Part I: delivered ZIP-extraction helper (not needed in the repository)
code/02-certified-certify.py              Part II: the integer-interval certifier (delivered certificate/certify.py)
code/02-certified-test_certifier.py       Part II: supplementary arithmetic and algebra tests (delivered certificate/test_certifier.py; imports certify)
code/02-certified-verify_package.py       Part II: delivered closed-inventory check and isolated replay (needs SHA256SUMS and the delivered tree)
code/02-certified-test_package.py         Part II: delivered negative regression suite (imports verify_package)
code/02-certified-build.sh                Part II: delivered isolated PDF build (compiles Report130.tex)
data/README.md                            Part I: delivered data conventions
data/identity-checks.json                 Part I: exact counts a_0..a_400 for d = 2, 3, 4; 48-decimal characteristic data
data/identity-allorders-checks.json       Part I: d = 3, 4 jets: (N, digits, route) = (200,70,sum), (400,110,sum), (250,80,differentiate)
data/identity-inverse-checks.json         Part I: original R = K = 4 inverse reference
data/identity-inverse-replay-checks.json  Part I: regenerated R = K = 4 inverse results
data/identity-inverse-extended-checks.json Part I: R = 2/K = 6 and R = 0/K = 4 model checks
data/replay-validation-summary.json       Part I: delivered replay status (Python 3.12.14, mpmath 1.3.0)
data/requirements.txt                     Part I: mpmath==1.3.0
data/02-certified-certificate.json        Part II: the reference certificate (delivered certificate/certificate.json)
data/02-certified-tests.json              Part II: expected output of test_certifier.py (delivered certificate/tests.json)
data/02-certified-release_checks.json     Part II: the producer's release checks (2 October 2026, Python 3.12.14)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery.

*Source 01.* Placement renamed `report.tex` to `article.tex` and moved
`replay.sh` and `build_pdf.sh` from the package root, and
`code/requirements.txt`, into `code/` and `data/` respectively; `code/` and
`data/` otherwise keep their delivered names. Not shipped: the delivered
12-page PDF `report.pdf` and `SHA256SUMS` (verified 21/21 at placement). Both
survive in the archive:
`git show 096ee7b87:docs/incoming/rooted-identity-trees-source.zip > <scratch>/rooted-identity-trees-source.zip`.
Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` (checks `SHA256SUMS`, then runs `bash build_pdf.sh` and
compares `report.pdf` hashes, all in its own directory), `code/build_pdf.sh`
(compiles `report.tex`), `code/README.md` (`code/requirements.txt`, commands
"from the bundle root"), `data/README.md`, and Section 9 of the article
(`bash replay.sh`, the manifest; dated note).

*Source 02.* Delivery path → shipped path: `certificate/certify.py`,
`certificate/test_certifier.py`, `verify_package.py`, `test_package.py`,
`build.sh` → `code/02-certified-*`; `certificate/certificate.json`,
`certificate/tests.json`, `release_checks.json` → `data/02-certified-*`. Not
shipped (all in the archive): `Report130.tex` and `certified_constants.tex`
(merged into `article.tex`), the delivered `README.md` (replaced by this
guide), the 17-page `Report130.pdf`, `SHA256SUMS` (14 entries, verified at
intake), and the two coefficient exports `certificate/a_d3_through_400.json`
and `a_d4_through_400.json` (31 395 and 31 654 bytes; the same integers as
`data/identity-checks.json`; regenerated in seconds by
`certify.py --coefficients-out DIR`, their SHA-256 recorded in the
certificate). Retrieve the archive with
`git show 60f54ea06:docs/incoming/A116379_A116380_All_Orders_Identity_Trees_and_Inversion_Source.zip > <scratch>/r130.zip`.
Delivered files whose text names the delivery layout: the **prefixed names
break the delivered imports** — `02-certified-test_certifier.py` does
`import certify` and `02-certified-test_package.py` does
`import verify_package`; `02-certified-verify_package.py` checks the delivered
tree against `SHA256SUMS` and replays `certificate/` from its own directory
(with `--build` it also compiles `Report130.tex` by `build.sh`); `02-certified-build.sh` compiles `Report130.tex`;
`release_checks.json` hashes the delivered `Report130.tex`, table and PDF. The
delivered README says the commands "may be run from any working directory";
on Windows the replay of `verify_package.py --replay` fails as shipped,
because `certify.py` and `test_certifier.py` print in text mode and Windows
writes CRLF where the reference files have LF (all outputs agree modulo
carriage returns; checked at intake on Python 3.14.4).

## Rerun the checks (on a scratch copy)

**Part I.** `code/replay.py` reads `data/` relative to itself and writes only to
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

**Part II.** Copy the programs to a scratch directory **with the prefix
removed** (so that `import certify` resolves), run them there, and compare
modulo carriage returns (Git Bash, from this directory; standard library
only, use `python3` on POSIX):

```sh
D=$PWD; R=$(mktemp -d)
for f in code/02-certified-*.py; do b=${f#code/02-certified-}; cp "$f" "$R/$b"; done
cd "$R"
py -B certify.py > certificate.json
diff -q --strip-trailing-cr certificate.json "$D/data/02-certified-certificate.json"
py -B -O certify.py > certificate-O.json
diff -q --strip-trailing-cr certificate-O.json "$D/data/02-certified-certificate.json"
py -B test_certifier.py > tests.json
diff -q --strip-trailing-cr tests.json "$D/data/02-certified-tests.json"
mkdir exp && py -B certify.py --coefficients-out exp > /dev/null
tr -d '\r' < exp/a_d3_through_400.json | sha256sum   # = cases[0].coefficient_sha256
tr -d '\r' < exp/a_d4_through_400.json | sha256sum   # = cases[1].coefficient_sha256
```

In the write phase (5 October 2026, Python 3.14.4) `certify.py` ran in about
1 s and `test_certifier.py` in about 2 s; both outputs equal the shipped
references modulo carriage returns, and both exports have the recorded
SHA-256 after LF normalization and equal the `d = 3, 4` counts of
`data/identity-checks.json`. `verify_package.py` and `test_package.py` need
the delivered tree and its `SHA256SUMS`: extract the archive above into a
scratch directory and run, inside `Report130/`,
`python3 -B verify_package.py`, `python3 -B verify_package.py --replay` and
`python3 -B test_package.py` on a POSIX host (on Windows `--replay` fails on
line endings only, as disclosed above; `test_package.py` passed at intake in
ordinary and `-O` mode). `verify_package.py --build` needs the Debian TeX Live
layout of `build.sh` and was not run.

## Build the PDF

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, enumitem, xcolor, hyperref, fancyhdr; the preamble uses
`\pdfmapfile`); no BibTeX. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 34 pages, no
errors or LaTeX warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the font-map "already exists" messages caused by the preamble's
`\pdfmapfile` lines are pre-existing). Part I alone built to 14 pages, the
delivered source 01 to 12 and source 02 to 17. `code/build_pdf.sh` and
`code/02-certified-build.sh` are kept as delivered; to use either, copy it to a
scratch directory with the source it expects (`report.tex`, or the archive's
`Report130.tex` and `certified_constants.tex`).

## Provenance

- Bell–Burris–Yeats, Electron. J. Combin. 13 (2006) R63, §§6.1–6.2 and p. 57;
  Flajolet–Sedgewick, *Analytic Combinatorics* (2009), Chapters VI–VII;
  Genitrini, arXiv:1605.00837v2 (2016); Gittenberger–Jin–Wallner, Discrete
  Math. 341 (2018); Meir–Moon–Mycielski (1983), Haigh–Kennedy–Quintas (1984),
  Labelle (1992) and Kennedy–McKeon–Palmer–Robinson (1990), full texts not
  inspected; OEIS A116379, A116380 (inspected 2 October 2026 by both
  manuscripts). The counts in the data and tables are computed by the
  delivered programs and agree with the OEIS records; OEIS terms as such are
  CC BY-SA 4.0 material of The OEIS Foundation.
- Repository input: none recorded for either source; no pin.
- Source 01: batch 77 of `docs/incoming`, manuscript 63 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write phase
  (2 October 2026, `b3ffc8d30`). Single source, no merge choices.
- Source 02: batch 103, bundle Report 130 (INDEX row 142, created
  2026-10-02T17:37Z, 472 637 bytes); arrival `60f54ea06`, placement
  `9c995cefe`, written in the batch-103 write phase (5 October 2026) as
  Part II, the existing text becoming Part I with no number changed (the
  precedent is `a301981-unitary-divisor-partitions`). Merge choices: Part II
  prints every statement, proof, table and number of Report 130, and shortens
  the wording only where it repeats Part I in substance (the boundary
  dominance and Δ-domain argument, Section 14.4); duplicated results are
  printed once as second routes with the Part I label named (Table 3 of the
  article maps them); the certificate (Section 16) is printed in full; the
  bibliography was merged into Part I's keys, with the "Furnas" attribution
  corrected.
