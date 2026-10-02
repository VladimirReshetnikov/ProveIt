# Apéry Hankel growth: a proof, sharp Szegő asymptotics, and reproducible computations

**Part I: a proof of the A228143 growth conjecture (18 September 2026). Part II: the ratio constant K, monotone Hankel envelopes, polynomial modifications and inverse growth (1 October 2026).**

This is a research report in two Parts, built from two manuscripts. Both are
AI-assisted research notes (Part I's author line: "Research report prepared
with ChatGPT"; Part II's: "Research report prepared for the ProveIt project",
with PDF metadata "prepared with ChatGPT"). Neither is peer reviewed or
formalized in a proof assistant.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | the original report, one of the 64 research reports catalogued on 19 September 2026 | `apery_hankel_research.zip` (main file `apery_hankel_growth.tex`, 12-page PDF) | none | `a3fe9660e` (former Cardinals repository, merged here in `dc54c3cb3`) | Part I: Sections 1–8, Appendix A |
| Part II | batch 73O1, manuscript 41 | `apery_hankel_research.zip` of arrival commit `bdf1a1a73` (main file `apery_hankel_refinement.tex`, 18-page PDF) — **same archive name as Part I's, different content** | commit `bc4d1fa2b` | `9df4ba51a` | Part II: Sections 9–20, Appendices B–C |

Every theorem, proposition, lemma, corollary, remark, proof, table, figure
and research question of manuscript 41 is printed. Part I is unchanged except
for dated notes (`[Added 1 October 2026, batch 73O1: …]`) after the remark
following the proof of its Theorem 1.1 and twice in its Section 8, a front
matter (title, abstract, contents) that announces both Parts, and the place
of its Appendix A, which now follows Part II.

## Main results

**Part I.** For

\[
A_k=\sum_{j=0}^k\binom{k}{j}^2\binom{k+j}{j}^2,
\qquad D_n=\det(A_{i+j})_{0\le i,j\le n},
\]

Part I proves

\[
\log D_n=n(n+1)\log\!\left(\frac{17+12\sqrt2}{4}\right)+O(n).
\]

In particular, it proves the limit conjectured in the September 13, 2026
revision of OEIS A228143. The proof uses Edgar's known moment-density theorem;
it does not reprove that theorem. All subsequent determinant arguments are
included in the article. The accessed OEIS entry still labelled the precise
limit as a conjecture. This is not a claim of worldwide priority.

Part I also proves an explicit law for
`det(A_(m*(i+j)+r_n))` with fixed positive integer m and r_n/n -> rho >= 0,
and proves that the formal ordinary generating series of D_n is not D-finite.

**Part II.** With C = 17+12√2, Λ = C/4 and Edgar's density φ on [0, C], put
K = (πC/2)·exp⟨log φ⟩_C, where ⟨·⟩_C is the arcsine average
(1/π)∫₀^C f(x) dx/√(x(C−x)). Part II proves 0 < K ≤ 2 and

\[
\frac{D_n}{D_{n-1}}\sim K\Lambda^{2n},\qquad
\log D_n=n(n+1)\log\Lambda+(n+1)\log K+o(n),
\]

so the normalized norms h_n/Λ^{2n} = D_n/(D_(n−1)Λ^{2n}) converge to K,
the question Part I left open. Numerically K ≈ 0.633427435172 and, in the
normalization of the OEIS ratio plot, ΛK ≈ 5.379471608281 (quadrature,
not interval-certified). Part II also proves: D_{n+1}D_{n−1}/D_n² → Λ²;
fixed-window ratios and the radius 1/K of Σ D_n z^n/Λ^{n(n+1)}; a proved
Szegő minimum principle; four exact norm identities; interleaved monotone
envelopes E_m ↓ K that are finite expressions in Q(√2) (E_1 = 81120√2 −
114720); the product K = 2∏(1−α_j²) over reflection coefficients; sharp
constants for every fixed nonnegative polynomial modification (with a root
formula), for fixed strides and shifts, and a two-term inverse-index law.

Part II recovers Part I's Theorem 1.1 (except its explicit sandwich) as a
corollary (Remark 10.4) and does not claim it as new; its fixed-stride
theorem refines Part I's Theorem 4.1 at ρ = 0 by the linear coefficient
(Remark 16.2).

## What is not claimed

- Neither Part claims a full multiplicative asymptotic equivalent for D_n.
  Part II's (n+1) log K + o(n) still allows powers of n, powers of log n and
  a further constant; D_n ~ K^{n+1}Λ^{n(n+1)} is **not** asserted. The
  prefactor appears only in Part II's **conditional** Theorem 18.1 and
  Proposition 18.2, whose hypothesis on the reflection coefficients is
  **not proved** for the Apéry density.
- The oscillation period π/(2 arcsin(1/C)) ≈ 53.3531 (Section 20.2) is a
  candidate suggested by the geometry, not a theorem.
- The exact linear term for shifts proportional to n (Part I's Theorem 4.1
  regime) remains open; Part II's Theorem 16.1 is for fixed m and r only.
- No decimal of either Part is interval-certified; Part I's constant η and
  κ are not evaluated (every admissible κ satisfies κ ≤ K, Remark 10.4).
- Part II's literature check (1 October 2026) is bounded and not a priority
  claim; the general Szegő theory is classical, and no new general Szegő
  theorem is claimed. None of the other arithmetic assertions on A228143 is
  claimed.
- No Lean or Rocq declaration in this repository formalizes any statement of
  either Part. (A search for Apéry, A228143 and Szegő in `*.lean`/`*.v` finds
  only the Fabius project's Rogers–Szegő polynomial modules, which are
  unrelated.) Placement in the Cardinals research-report collection confers
  no formal status.

## Files

```
apery_hankel_growth.tex                  the report (Parts I and II), standalone LaTeX with an internal bibliography
apery_hankel_growth.pdf                  the compiled report, 33 pages (title and abstract, contents pp. 2-3,
                                         Part I pp. 4-13, Part II pp. 14-30, Appendices A-C pp. 30-31,
                                         references pp. 32-33)
README.md                                this guide
Makefile                                 Part I's build file (make pdf)
sources.md                               Part I's source audit (18 September 2026)
review_checklist.md                      Part I's mathematical review points
oeis_submission_draft.txt                Part I's unsubmitted OEIS suggestion
requirements-plots.txt                   Part I's optional plotting dependencies
02-szego-sources.md                      Part II's source audit (1 October 2026), as delivered
02-szego-oeis_update_draft.txt           Part II's unsubmitted OEIS suggestion, as delivered
code/apery_exact.py                      Part I: exact determinants, standard-library Python
code/apery_gmp.cpp                       Part I: exact determinants, C++17/GMP
code/verify.py                           Part I: independent exact checks
code/shift_experiments.py                Part I: shifted/dilated families
code/make_figures.py                     Part I: tables and figure
code/02-szego-verify_exact.py            Part II: exact Q(sqrt 2) checks (standard library)
code/02-szego-density_constant.py        Part II: density quadrature for K (mpmath)
code/02-szego-moment_norms.cpp           Part II: high-precision norms U_n, V_n, X_n, Y_n (C++17/GMP)
code/02-szego-make_figures.py            Part II: figures (matplotlib)
code/02-szego-Makefile                   Part II: delivered Makefile (see "Rerun hazards")
data/convergence.csv                     Part I: diagnostics from exact determinants, n <= 200
data/convergence_table.tex, data/shift_table.tex, data/verification_table.tex   Part I: tables input by the article
data/gmp_run.log, data/shift_run.log     Part I: run logs
data/numerical_evaluation.json, data/shift_diagnostics.json, data/shift_experiments.json, data/verification.json   Part I: recorded outputs
data/02-szego-exact_checks.json          Part II: recorded exact checks
data/02-szego-constant.json              Part II: recorded quadrature (dps 40)
data/02-szego-norms.csv                  Part II: norms and envelopes, n <= 200, 4096-bit run
data/02-szego-norms_3072.csv             Part II: the same, 3072-bit run (byte-identical to the 4096-bit file)
data/02-szego-precision_check.json       Part II: two-precision comparison (largest difference 0.0)
figures/convergence.pdf, figures/convergence.png                         Part I figure
figures/02-szego-ratio_limit.pdf, figures/02-szego-ratio_limit.png       Part II figure 2
figures/02-szego-monotone_envelope.pdf, figures/02-szego-monotone_envelope.png   Part II figure 3
```

`data/determinants_0_200.txt` (2.4 MB, exact D_0 … D_200, D_200 having
37,308 digits) is **not distributed**; rebuild it with
`build/apery_gmp 200 > data/determinants_0_200.txt` (see below).

Delivery-name map of Part II (manuscript 41; every file is byte-identical to
the delivery): `code/{verify_exact.py, density_constant.py, moment_norms.cpp,
make_figures.py}` → `code/02-szego-*`; `Makefile` → `code/02-szego-Makefile`;
`data/{constant.json, exact_checks.json, norms.csv, norms_3072.csv,
precision_check.json}` → `data/02-szego-*`; `figures/{ratio_limit,
monotone_envelope}.{pdf,png}` → `figures/02-szego-*`; `sources.md`,
`oeis_update_draft.txt` → `02-szego-sources.md`,
`02-szego-oeis_update_draft.txt`. Not shipped: the manuscript
`apery_hankel_refinement.tex` (its text is Part II), its PDF and its delivery
README (replaced by this README).

## Labels

Part I's 50 labels are bare (`thm:main`, `eq:apery`, `sec:density`, …) and
are unchanged; no Part I theorem, equation or section number changed (the
`.aux` numbers of all Part I labels were compared with a build of the
committed text). Every label of Part II carries the prefix `szego:`: the 84
delivered labels of manuscript 41 that are printed (its other five labelled
displays, `eq:A`, `eq:D`, `eq:old`, `eq:left`, `eq:right`, restated Part I's
`eq:apery`, `eq:det`, `eq:logmain`, `eq:left`, `eq:right` and are replaced by
references to them) and four new ones (`szego:sec:provenance`,
`szego:tab:notation`, `szego:rem:partI`, `szego:rem:strides`): 138 labels in
all. Seven delivered names collided with Part I (`thm:main`, `eq:left`,
`eq:right`, `eq:product`, `eq:constants`, `sec:density`, `sec:computations`).
Manuscript 41's section *n* is Section *n* + 8 here (its Theorem 2.1 is
Theorem 10.1), and its Appendices A, B are Appendices B, C.

## Notation (Part II)

Table 4 of the article lists every symbol shared by the two Parts. Two
symbols of manuscript 41 are renamed because Part I uses the letters for
other objects: its fixed-stride constant `K_m` is printed as 𝒦_m (Part I's
`K_m` is the upper constant in its equation (4.11)), and its log-log exponent
`η` in the conditional transfer theorem is printed as ξ (Part I's η is the
minorant constant of its Lemma 2.1). No normalization changed. Part II's
`L = log Λ`, `B = L + log K`, `Ψ_C`, `α_j` and `F` differ from Part I's `L`,
placeholder `B`, `Ψ`, `α_±` and `F`, as the table says.

## Relation to other material

- The other Hankel-determinant reports of the collection
  (`../rueppel-binary-run-determinants`, `../../catalan-and-ballot`,
  `../../somos-and-elliptic`, `../../a122251-numerators-and-denominators`)
  treat other sequences.
- The Apéry reports `generating-functions-and-asymptotics/apery-array-zeta-accelerations`
  and `congruences-and-valuations/supercongruences/a267220-apery-transform-supercongruences`
  treat arithmetic and ζ(3) accelerations of A005259, not Hankel
  determinants; neither Part re-proves anything there.

## Rerun the checks

### Part I (standard-library Python only)

Python 3.10 or later is sufficient. The recorded run used Python 3.13.5.
From this directory:

```sh
python3 code/verify.py
```

The verifier checks 401 moments against their defining binomial sums, the
10-term displayed OEIS prefix, 41 Python/GMP determinants, 13 independent
rational-Gaussian determinants, 33 modular-Gaussian determinants, 64 shifted
condensation identities, 32 rational power-weight determinants, and 501
central-binomial inequalities. A failed check raises an error. These are finite
arithmetic tests, not the proof of the limit.

Small and medium cases require only Python:

```sh
python3 code/apery_exact.py --n 40 --output data/recomputed.txt
python3 code/apery_exact.py --n 20 --stride 2 --shift 5 --output data/example.txt
```

For the complete 200-index run, use C++17 with GMP development libraries:

```sh
mkdir -p build
g++ -O3 -std=c++17 code/apery_gmp.cpp -lgmpxx -lgmp -o build/apery_gmp
build/apery_gmp 200 > data/determinants_0_200.txt 2> data/gmp_run.log
python3 code/verify.py
```

(The third line rewrites the shipped `data/gmp_run.log`; redirect it
elsewhere to keep the recorded log.) The program writes
`index exact_integer` records. The determinant indexed n has matrix order
n+1. Its optional arguments are stride (default 1) and shift (default 0).
Every integer division is checked; a nonexact division or a nonpositive
leading pivot causes failure. The delivered run checked 1,353,400 symmetric
Bareiss divisions and took about 124 seconds for the determinant phase in
that runtime; that timing is not a guarantee on other machines. The
elimination uses O(n^3) integer arithmetic operations and O(n^2) integer
storage locations. These are not bit-complexity bounds.

```sh
python3 code/shift_experiments.py --gmp build/apery_gmp --indices 10,20,40,80
```

Without `--gmp`, the script uses Python and defaults to indices 10 and 20.
It checks the cases `(m,r_n)=(1,n),(2,0),(2,n)`. The shift is fixed across
each matrix. Samples with n <= 20 are cross-checked with the Python
implementation even when GMP generates them.

The existing tables and figure are sufficient to compile the report. To
regenerate them: `python3 -m pip install -r requirements-plots.txt` and
`python3 code/make_figures.py`. This uses logarithms of exact integer
determinants, never a floating-point determinant. The delivered run compared
evaluations at 90 and 180 decimal digits; their maximum absolute difference
across the main diagnostics was less than 8e-87 (a precision-stability check,
not interval certification). `code/verify.py`, `code/shift_experiments.py` and
`code/make_figures.py` rewrite Part I's recorded outputs in `data/` and
`figures/`; run them on a copy if the shipped evidence should stay as
delivered.

### Part II

The delivered Part II programs are byte-identical and still use their
**delivery names**: `code/02-szego-verify_exact.py` writes
`data/exact_checks.json`; `code/02-szego-make_figures.py` reads
`data/norms.csv` and `data/constant.json` and writes
`figures/ratio_limit.{pdf,png}` and `figures/monotone_envelope.{pdf,png}`;
`code/02-szego-Makefile` refers to `apery_hankel_refinement.tex` (not shipped)
and `code/*.py` without the prefix, and its `moments` target writes
`data/norms.csv` and `data/norms_3072.csv`. Run in place, they would create
unprefixed files next to the shipped ones. Run them **on a copy of the
delivered layout** (re-extracted from arrival commit `bdf1a1a73`, or rebuilt
by copying each `02-szego-` file back to its delivery name in a scratch
directory), or pass explicit output paths:

```sh
python3 code/02-szego-verify_exact.py            # on a copy: writes data/exact_checks.json there
python3 code/02-szego-density_constant.py --dps 40 --output /tmp/constant.json   # needs mpmath
g++ -O3 -std=c++17 code/02-szego-moment_norms.cpp -lgmpxx -lgmp -o /tmp/moment_norms
/tmp/moment_norms 200 4096 > /tmp/norms.csv      # GMP floating point, not interval arithmetic
```

At intake (batch 73O1, on a copy), `verify_exact.py` (under 5 s) and
`density_constant.py --dps 40` (104 s, mpmath 1.3.0) reproduced the shipped
`data/02-szego-exact_checks.json` and `data/02-szego-constant.json` (JSON-equal;
on Windows, `verify_exact.py` writes CRLF line ends, so compare as JSON, not
bytes). `moment_norms.cpp` (GMP, n = 200) was
**not** rerun; its output was spot-checked independently by 900-digit Hankel
elimination at n = 10, 20, 30, and its U_200 agrees in all 33 printed digits
with Part I's `data/convergence.csv`, computed from exact determinants. The
figure script was not rerun.

## Compile the report

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error apery_hankel_growth.tex
```

or `make pdf` (Part I's `Makefile`, which builds into `build/` and copies out
the PDF). A TeX installation with pdfLaTeX, Libertinus text and math fonts,
AMS packages, tcolorbox, enumitem, xurl, graphics and hyperref is sufficient.
The batch-73O1 build (MiKTeX, pdfLaTeX) has no errors, undefined references
or citations, multiply defined labels, duplicate destinations, or overfull
boxes. The four figure PDFs (Part I's and Part II's, as delivered) embed
matplotlib Type 3 fonts; they were not regenerated.

## Discrepancies and disclosures

- **Archive name.** Part II arrived as `apery_hankel_research.zip` (arrival
  commit `bdf1a1a73`), the same file name as the archive that delivered
  Part I; the contents differ.
- **Pin.** Manuscript 41 and `02-szego-sources.md` call `bc4d1fa2b…` an
  "inspected tree"; it is a commit. At that commit Part I's source was the
  18 September text.
- **Twin CSVs.** `data/02-szego-norms.csv` and `data/02-szego-norms_3072.csv`
  are byte-identical: both GMP runs emitted the same 70 digits
  (`data/02-szego-precision_check.json`, largest difference 0.0). Both are
  shipped as the delivered evidence of the two-precision run.
- **Delivered texts naming delivery files.** `02-szego-oeis_update_draft.txt`
  says the report is "included here" (it is Part II of this report);
  `code/02-szego-Makefile` names `apery_hankel_refinement.tex` and unprefixed
  paths; `02-szego-sources.md` says the repository was read "using the
  connected GitHub tools".
- **External claims, dated.** "The accessed OEIS entry still labels the
  n²-root limit as a conjecture" (Part I: 18 September 2026; Part II:
  1 October 2026) and the link to Kotesovec's ratio plot are as inspected on
  those dates, not re-verified at intake.
- Part I's `sources.md` is dated September 18, 2026. Neither OEIS draft has
  been submitted, and no external repository or OEIS entry has been modified.

## Source and novelty scope

The critical source is G. A. Edgar, *The Apéry Numbers as a Stieltjes Moment
Sequence*, arXiv:2005.10733v2 (2020). Part I exploits the positive density on
the full interval [0,17+12*sqrt(2)], including the small part to the left of
the interior singularity; classical orthogonal-polynomial and
Cauchy-determinant methods are proved where needed. Part II uses the same
input with the classical unit-circle (Szegő) theory, whose minimum principle
it proves; context: B. Simon, *OPUC on one foot* (2005); Deift–Its–Krasovsky
(2011) is cited only as a framework for the open prefactor question. The
contribution of each Part is the explicit application to the Apéry
determinants, not the invention of the general methods.
