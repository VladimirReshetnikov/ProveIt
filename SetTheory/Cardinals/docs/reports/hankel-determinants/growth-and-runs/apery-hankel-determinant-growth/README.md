# Apéry Hankel growth: a proof, sharp Szegő asymptotics, and reproducible computations

**Part I: a proof of the A228143 growth conjecture (18 September 2026). Part II: the ratio constant K, monotone Hankel envelopes, polynomial modifications and inverse growth (1 October 2026). Part III: full equivalents for proportionally shifted determinants (2 October 2026).**

This is a research report in three Parts, built from three manuscripts. All
are AI-assisted research notes (Part I's author line: "Research report
prepared with ChatGPT"; Part II's: "Research report prepared for the ProveIt
project", with PDF metadata "prepared with ChatGPT"; Part III's: "Research
report prepared with ChatGPT"). None is peer reviewed or formalized in a
proof assistant.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | the original report, one of the 64 research reports catalogued on 19 September 2026 | `apery_hankel_research.zip` (main file `apery_hankel_growth.tex`, 12-page PDF) | none | `a3fe9660e` (former Cardinals repository, merged here in `dc54c3cb3`) | Part I: Sections 1–8, Appendix A |
| Part II | batch 73O1, manuscript 41 | `apery_hankel_research.zip` of arrival commit `bdf1a1a73` (main file `apery_hankel_refinement.tex`, 18-page PDF) — **same archive name as Part I's, different content** | commit `bc4d1fa2b` | `9df4ba51a` | Part II: Sections 9–20, Appendices B–C |
| Part III | batch 77 (cluster P5), manuscript 10 | `apery-shifted-release.zip` of arrival commit `096ee7b87` (main file `article.tex`, 17-page PDF) | commit `946b6c762` | `4f11bc9c0` | Part III: Sections 21–30 |

Every theorem, proposition, lemma, corollary, remark, proof, table, figure
and research question of manuscripts 41 and 10 is printed. Part I is
unchanged except for dated notes (`[Added 1 October 2026, batch 73O1: …]`)
after the remark following the proof of its Theorem 1.1 and twice in its
Section 8, one further dated note (`[Added 2 October 2026, batch 77P5: …]`)
after the examples of its Theorem 4.1, a front matter (title, abstract,
contents) that announces all three Parts, and the place of its Appendix A,
which now follows Part III. Part II is unchanged except for three dated
batch-77P5 notes: in the paragraph after the proof of Theorem 16.1 ("An
exact linear correction in that varying regime remains a further problem"),
in the opening paragraph of Section 20, and at the end of Subsection 20.5
("Growing shifts and moving polynomial zeros").

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

**Part III.** Let H_N(r) = det(A_(r+i+j)), 0 ≤ i, j < N — matrix order
**N**, so H_N(r) is Part I's H_(N−1)^(1,r) and D_n = H_(n+1)(0). Put
s* = 3√2/4 − 1 = 0.0606601717798212866… (the shift proportion at which the
moving soft edge of the equilibrium measure meets the density's interior
singularity). Uniformly for s = r/N in every fixed compact subset of
(s*, ∞), Part III proves (Theorem 22.1, Corollary 22.2, Theorem 28.1)

\[
H_N(r)=C^{Nr+N(N-1)}S_N(r,\tfrac12)e^{NF(s)}E(s)\Bigl(1+\frac{c_{\rm rel}(s)}N+O(N^{-2})\Bigr)
=M(s)N^{-1/24}e^{N^2A(s)+NB(s)}\Bigl(1+\frac{c_{\rm full}(s)}N+O(N^{-2})\Bigr),
\]

with S_N an exact Selberg product, F and E built from Edgar's density on the
moving support, and A, B, M, c_rel, c_full explicit (c_rel is a cubic in the
first two endpoint derivatives of one arcsine integral, Lemma 28.3). The
proof adapts Charlier–Gharakhloo's determinant-ratio analysis to a
logarithmically (not superlogarithmically) confining potential with
explicit remote-jump and differential-identity tail estimates. It also keeps
the bounded floor phases, proves that the floor-shifted sequence is
eventually strictly increasing, and gives rational-residue inverse
thresholds with an O(log y / y) error inside the ceiling (Corollary 27.1),
sharpened by one further inverse term (Section 28.5). The quadratic
coefficient A(s) = (1+s) log C − Ψ(s) is exactly Part I's Theorem 4.1 at
m = 1, ρ = s (Remark 21.1) and is not claimed as new; B, N^(−1/24), M and
the corrections are. Numerically (s = 1, binary64 quadrature, not
interval-certified): F(1) ≈ −0.9052804694622163, E(1) ≈ 1.3511218257963278,
c_rel(1) ≈ 0.0206331502, c_full(1) ≈ −0.0036724054.

## What is not claimed

- No Part claims a full multiplicative asymptotic equivalent for D_n.
  Part II's (n+1) log K + o(n) still allows powers of n, powers of log n and
  a further constant; D_n ~ K^{n+1}Λ^{n(n+1)} is **not** asserted. The
  prefactor appears only in Part II's **conditional** Theorem 18.1 and
  Proposition 18.2, whose hypothesis on the reflection coefficients is
  **not proved** for the Apéry density. Part III gives a full multiplicative
  equivalent for proportional shifts s = r/N > s* = 3√2/4 − 1 only; it does
  not apply to D_n (s = 0), whose prefactor remains open. Its estimates are
  uniform only on compact subsets of (s*, ∞), and substituting s = 0 (or
  letting s ↓ 0) in M(s)N^(−1/24) is invalid; no relation between B(0+),
  M(0+) and Part II's K is asserted.
- The oscillation period π/(2 arcsin(1/C)) ≈ 53.3531 (Section 20.2) is a
  candidate suggested by the geometry, not a theorem.
- The exact linear term for shifts proportional to n (Part I's Theorem 4.1
  regime) is now proved by Part III **only** for stride m = 1 and
  proportions s > s* (in Part III's normalization: matrix order N, s = r/N
  exactly; Section 27 converts to r = ⌊ρN⌋ and to the older N = n + 1
  convention). Strides m ≥ 2, proportions s ≤ s*, and the cusp collision as
  s ↓ s* (whose double scaling Part III does not give) remain open; Part
  II's Theorem 16.1 is for fixed m and r only.
- Part III's further non-claims: only the first inverse-N correction is
  evaluated (a continuation method to any fixed order is described, but no
  all-orders recursion or implementation is supplied); the sign and constant
  of the inside-ceiling error ε_j in Corollary 27.1 are not determined, and
  for irrational ρ no phase-free smooth inverse is claimed; the replay's
  residual tables neither identify nor prove a second correction; the
  application of Charlier–Gharakhloo is an adaptation with its own tail
  estimates, not a literal use of their printed theorem; the general methods
  and the moment density are established mathematics, and the comparison
  with Parts I and II (dated 2 October 2026) is not a universal priority
  claim.
- No decimal of any Part is interval-certified; Part I's constant η and
  κ are not evaluated (every admissible κ satisfies κ ≤ K, Remark 10.4).
- Part II's literature check (1 October 2026) is bounded and not a priority
  claim; the general Szegő theory is classical, and no new general Szegő
  theorem is claimed. None of the other arithmetic assertions on A228143 is
  claimed.
- No Lean or Rocq declaration in this repository formalizes any statement of
  any of the three Parts. (A search for Apéry, A228143 and Szegő in
  `*.lean`/`*.v` finds only the Fabius project's Rogers–Szegő polynomial
  modules, which are unrelated; a repeat search on 2 October 2026 for Apéry,
  A228143 and A005259 found nothing.) The generic rounding steps that
  Part III's threshold corollary shares with the transseries volume's
  staircase theorem are formalized in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`
  (`Fabius.staircase_ceil`, `Fabius.staircase_separation`,
  `Fabius.isLeast_residue_class`), but those are order-theoretic facts about
  ceilings, not Part III's asymptotics. Placement in the Cardinals
  research-report collection confers no formal status.

## Files

```
apery_hankel_growth.tex                  the report (Parts I-III), standalone LaTeX with an internal bibliography
apery_hankel_growth.pdf                  the compiled report, 52 pages (title and abstract, contents pp. 2-3,
                                         Part I pp. 4-13, Part II pp. 14-30, Part III pp. 31-49,
                                         Appendices A-C pp. 49-50, references pp. 51-52)
README.md                                this guide
Makefile                                 Part I's build file (make pdf)
sources.md                               Part I's source audit (18 September 2026)
review_checklist.md                      Part I's mathematical review points
oeis_submission_draft.txt                Part I's unsubmitted OEIS suggestion
requirements-plots.txt                   Part I's optional plotting dependencies
02-szego-sources.md                      Part II's source audit (1 October 2026), as delivered
02-szego-oeis_update_draft.txt           Part II's unsubmitted OEIS suggestion, as delivered
03-shifted-replay-README.md              Part III's replay guide (conventions, expected values, precision), as delivered
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
code/03-shifted-density.py               Part III: Edgar's upper-band density and its continuation sheet (mpmath)
code/03-shifted-check_shift.py           Part III: exact moments, high-precision Hankel elimination, Selberg reference, F, E
code/03-shifted-verify_symbolic.py       Part III: exact algebra (s*, Barnes cancellation) and equilibrium-mass quadrature
code/03-shifted-evaluate_c1.py           Part III: derivative quadrature for c_rel, c_full and corrected residuals
code/03-shifted-verify_c1_log_shift.py   Part III: exact c_rel check for f = gamma log t (sympy)
code/03-shifted-check_first_correction_trace.py   Part III: exact c_rel check for f = lambda t via Schur/Selberg cumulants
code/03-shifted-run_replay.py            Part III: replay runner and comparison with the expected outputs
code/03-shifted-tests-test_replay.py     Part III: the eleven unit tests
data/convergence.csv                     Part I: diagnostics from exact determinants, n <= 200
data/convergence_table.tex, data/shift_table.tex, data/verification_table.tex   Part I: tables input by the article
data/gmp_run.log, data/shift_run.log     Part I: run logs
data/numerical_evaluation.json, data/shift_diagnostics.json, data/shift_experiments.json, data/verification.json   Part I: recorded outputs
data/02-szego-exact_checks.json          Part II: recorded exact checks
data/02-szego-constant.json              Part II: recorded quadrature (dps 40)
data/02-szego-norms.csv                  Part II: norms and envelopes, n <= 200, 4096-bit run
data/02-szego-norms_3072.csv             Part II: the same, 3072-bit run (byte-identical to the 4096-bit file)
data/02-szego-precision_check.json       Part II: two-precision comparison (largest difference 0.0)
data/03-shifted-expected-{numerics_s01,numerics_s02,numerics_s1,symbolic_results}.json   Part III: reference outputs
                                         (s = 0.1, 0.2, 1 and the symbolic checks)
data/03-shifted-expected-{c1_direct_s1_256,c1_direct_s1_512,first_correction_residuals_s1}.json   Part III: reference
                                         first-correction outputs (256/512 nodes) and corrected residuals
data/03-shifted-recorded-*.json (10 files), data/03-shifted-recorded-tests.txt   Part III: the delivered fresh run
                                         of 2 October 2026 (the seven files above, first_correction_log_shift,
                                         first_correction_trace, validation_report; test log)
data/03-shifted-requirements.txt         Part III: pinned replay dependencies (mpmath, numpy, scipy, sympy)
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

Delivery-name map of Part III (manuscript 10, archive wrapper directory
`apery-shifted-release/`; every shipped file is byte-identical to the
delivery): `replay/{density.py, check_shift.py, verify_symbolic.py,
evaluate_c1.py, verify_c1_log_shift.py, check_first_correction_trace.py,
run_replay.py}` → `code/03-shifted-*`; `replay/tests/test_replay.py` →
`code/03-shifted-tests-test_replay.py`; `replay/expected/X` →
`data/03-shifted-expected-X`; `replay/recorded/X` →
`data/03-shifted-recorded-X`; `replay/requirements.txt` →
`data/03-shifted-requirements.txt`; `replay/README.md` →
`03-shifted-replay-README.md`. Not shipped: the manuscript `article.tex`
(its text is Part III), its 17-page PDF, its delivery README (replaced by
this README), its `build.sh` and `Makefile` (they build the unshipped
manuscript), `replay/.gitignore`, and the release manifest `SHA256SUMS`
with its checker `verify_manifest.py` (35/35 entries verified at intake,
then retired; a manifest establishes file integrity, not correctness).

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

Every label of Part III carries the prefix `psh:`: the 95 delivered labels
of manuscript 10 that are printed (its 96th, `eq:apery`, labelled a restated
definition of the Apéry numbers and is replaced by a reference to Part I's
`eq:apery`) and five new ones (`psh:sec:scope`, `psh:sec:relation`,
`psh:rem:partI`, `psh:sec:provenance`, `psh:tab:notation`): **238 labels in
all** (138 before, none renamed or removed; the `.aux` numbers of all 138
earlier labels were compared with a build of the committed text and are
unchanged). Manuscript 10's section *n* is Section *n* + 20 here (its
Theorem 2.1 is Theorem 22.1, its Corollary 7.1 is Corollary 27.1, its
Theorem 8.1 is Theorem 28.1); its equation (1.2) is (21.1), other equation
numbers shift with the section; its Tables 1 and 2 are Tables 6 and 7. Its
bibliography keys `cg`, `charlier`, `arw` are `psh-cg`, `psh-charlier`,
`psh-arw`; `edgar` is merged with the existing entry; `prior` and
`priorcode` (this report and Part II's density program, pinned at
`946b6c762`) are replaced by internal references.

## Notation (Part II)

Table 4 of the article lists every symbol shared by Parts I and II. Two
symbols of manuscript 41 are renamed because Part I uses the letters for
other objects: its fixed-stride constant `K_m` is printed as 𝒦_m (Part I's
`K_m` is the upper constant in its equation (4.11)), and its log-log exponent
`η` in the conditional transfer theorem is printed as ξ (Part I's η is the
minorant constant of its Lemma 2.1). No normalization changed. Part II's
`L = log Λ`, `B = L + log K`, `Ψ_C`, `α_j` and `F` differ from Part I's `L`,
placeholder `B`, `Ψ`, `α_±` and `F`, as the table says.

## Notation (Part III)

Table 5 of the article lists every Part III symbol that Parts I and II also
use, with the earlier meaning beside the new one. **The matrix order is N,
not n + 1**: H_N(r) = det(A_(r+i+j))_(0≤i,j<N) is Part I's H_(N−1)^(1,r),
and D_n = H_(n+1)(0). The Apéry numbers are printed in sans-serif (𝖠_k, the
manuscript's `\mcA`, which is Part I's `\A` macro) because italic A(s) is
the quadratic coefficient. Six letters of manuscript 10 are renamed (the
table's equation and section numbers are those printed here), with no change
of normalization:

| manuscript 10 | printed | why |
|---|---|---|
| `K` (generic constant in (25.7), (25.8), Lemma 28.2) | K_I | Part II's K is the ratio constant |
| `E_0, E_1, E_2` (coefficient functionals, Lemma 28.2) | Θ_0, Θ_1, Θ_2 | Part II's envelopes E_0 = 2, E_1 = 81120√2 − 114720 |
| `η`, `η_1` (tail slopes) | η_I, η_(I,1) | Part I's η is the minorant constant |
| `m` (lower bound of h in (25.3); exponent in (25.9)) | h_min; ℓ | Part I's m is the stride |
| `φ` (angle in Section 25.5) | ϑ | φ is Edgar's density |
| `c` in O(e^(−cN)) | c_I | c = 1/C |

Part III's E(s), B(s), F(s), D (= a_ε'(0)), G (Barnes), Q_s, R, U(u), J(a,V),
L_s, a, b and q differ from the Part I/II objects with the same letters;
the table says how. The replay README and JSON files use the delivery
notation: their `B` or `bias` is (f̂_0 − f(1))/4, not B(s); their J_N(r) is
the article's S_N(r, 1/2); their `f0`, `f1` are f̂_0 and f(1); their
determinant is normalized as C^(−N(r+N−1)) H_N(r).

## Relation to other material

- The other Hankel-determinant reports of the collection
  (`../rueppel-binary-run-determinants`, `../../catalan-and-ballot`,
  `../../somos-and-elliptic`, `../../a122251-numerators-and-denominators`)
  treat other sequences.
- The Apéry reports `generating-functions-and-asymptotics/apery-array-zeta-accelerations`
  and `congruences-and-valuations/supercongruences/a267220-apery-transform-supercongruences`
  treat arithmetic and ζ(3) accelerations of A005259, not Hankel
  determinants; no Part re-proves anything there.
- Part III's inverse thresholds (Section 27) follow the pattern of the
  staircase theorem `p0:thm:staircase` and the perturbed inversion
  `p0:thm:perturbed-inversion` of the transseries volume
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (cited in an editorial paragraph after Corollary 27.1); no novelty is
  claimed for the inversion technique, and no Lambert-W block
  (`p0:thm:lambert-core`) occurs.

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

### Part III

The delivered Part III replay is byte-identical and still uses its
**delivery layout**: the modules import one another by their unprefixed
names (`from check_shift import …`, `from density import …`),
`run_replay.py` and the unit tests read `expected/*.json` next to the
scripts, and `run_replay.py` writes to `generated/` by default (`--output`
changes that). Run in this directory, the prefixed scripts cannot even
import each other. Run it **on a copy of the delivered layout**: either
re-extract `apery-shifted-release.zip` from the arrival commit
(`git show 096ee7b87:docs/incoming/apery-shifted-release.zip > /tmp/a.zip`
and unzip it, then `cd apery-shifted-release/replay`), or recreate the
layout in a scratch directory:

```sh
mkdir -p /tmp/replay/expected /tmp/replay/recorded /tmp/replay/tests
for f in code/03-shifted-*.py; do b=${f#code/03-shifted-}; case $b in tests-*) cp "$f" /tmp/replay/tests/${b#tests-};; *) cp "$f" /tmp/replay/$b;; esac; done
for f in data/03-shifted-expected-*; do cp "$f" /tmp/replay/expected/${f#data/03-shifted-expected-}; done
for f in data/03-shifted-recorded-*; do cp "$f" /tmp/replay/recorded/${f#data/03-shifted-recorded-}; done
cp data/03-shifted-requirements.txt /tmp/replay/requirements.txt
cd /tmp/replay
python3 -m pip install -r requirements.txt    # mpmath 1.3.0, numpy 2.3.5, scipy 1.17.0, sympy 1.14.0
python3 -m unittest discover -s tests -v
python3 run_replay.py --output /tmp/replay-out          # add --stability for grid doubling and 320/400-digit repeats
```

`03-shifted-replay-README.md` gives the individual commands and their
precision controls. The delivered fresh run (Python 3.12.14, 2 October 2026,
with `--stability`) passed all eleven tests and reproduced every reference
value exactly, in 28.86 s (`data/03-shifted-recorded-validation_report.json`).
At intake (batch 77P5, on a copy of the re-extracted layout, Windows,
Python 3.13.5 with the pinned packages) the eleven unit tests passed in
10.5 s, and `run_replay.py` without `--stability` printed `PASS` in 94.8 s:
s = 0.1, s = 1 and both first-correction grids agreed with the references
exactly, s = 0.2 within 6.4e-13 (one binary64 unit in F, multiplied by N in
the `N_times_error` column; the runner's tolerance is 1e-10). The
`--stability` option was not rerun. These are floating-point
reproducibility checks, not interval certificates, and they do not replace
the analytic proof.

## Compile the report

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error apery_hankel_growth.tex
```

or `make pdf` (Part I's `Makefile`, which builds into `build/` and copies out
the PDF). A TeX installation with pdfLaTeX, Libertinus text and math fonts,
AMS packages, tcolorbox, enumitem, xurl, graphics and hyperref is sufficient.
The batch-77P5 build (MiKTeX, pdfLaTeX, 52 pages) has no errors, no LaTeX
or package warnings at all (so no undefined references or citations,
multiply defined labels or duplicate destinations), and no overfull or
underfull boxes; the same holds for a build of the batch-73O1 text. The four
figure PDFs (Part I's and Part II's, as delivered) embed matplotlib Type 3
fonts; they were not regenerated. Part III has no figures.

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
- **Part III's citation of this report.** Manuscript 10 cites Parts I and II
  as an external report at commit `946b6c762` ("Section 20 explicitly leaves
  its linear coefficient and support/cusp collision open"). The citation is
  correct: Section 20's opening paragraph says "the prefactor, the
  oscillation and the varying-shift linear term are not" determined, and
  Subsection 20.5 asks for the next linear term "including regimes where a
  moving equilibrium-support endpoint approaches the density's interior
  singularity". The merged text cites these by section reference.
- **Delivered texts naming delivery files.** `03-shifted-replay-README.md`
  describes `density.py`, `check_shift.py`, `tests/test_replay.py`,
  `expected/`, `recorded/`, `requirements.txt` and `generated/` by their
  delivery names, calls Part III "the article", and links Part II's density
  script by its GitHub URL at `946b6c762` (the same file is shipped here as
  `code/02-szego-density_constant.py`). `data/03-shifted-recorded-tests.txt`
  and `data/03-shifted-recorded-validation_report.json` record a run in the
  delivery layout. The delivered README also mentioned a 17-page
  `article.pdf`, `build.sh`, `Makefile`, `verify_manifest.py` and
  `SHA256SUMS`; none is shipped (see the delivery-name map).
- **Expected versus recorded outputs.** Four pairs are byte-identical
  (`numerics_s01`, `numerics_s02`, `numerics_s1`, `symbolic_results`). The
  recorded `c1_direct_s1_{256,512}.json` add four fields
  (`c_rel_simplified`, `S_prime_identity_residual`,
  `S_prime_endpoint_identity`, `c_rel_formula_difference`) to otherwise
  equal values, and the recorded `first_correction_residuals_s1.json` differs
  from the expected one only by a final newline. Both members of each pair
  are shipped, as delivered.
- **Rerun hazard.** `run_replay.py` writes only below its `--output`
  directory (default `generated/` beside the scripts) and preserves
  `expected/` and `recorded/`; on a copy it is safe. In this directory it
  cannot run at all (prefixed module names), so no shipped file is at risk.

## Source and novelty scope

The critical source is G. A. Edgar, *The Apéry Numbers as a Stieltjes Moment
Sequence*, arXiv:2005.10733v2 (2020). Part I exploits the positive density on
the full interval [0,17+12*sqrt(2)], including the small part to the left of
the interior singularity; classical orthogonal-polynomial and
Cauchy-determinant methods are proved where needed. Part II uses the same
input with the classical unit-circle (Szegő) theory, whose minimum principle
it proves; context: B. Simon, *OPUC on one foot* (2005); Deift–Its–Krasovsky
(2011) is cited only as a framework for the open prefactor question. Part III
uses Edgar's Propositions 4, 23, 25 and 26 and adapts the Riemann–Hilbert
determinant-ratio analysis of C. Charlier and R. Gharakhloo (Adv. Math. 383
(2021), Section 5 and Proposition 9.1) and the differential identities of
C. Charlier (arXiv:1706.03579v4, (6.3)–(6.6)); its trace check uses the
Schur/Selberg average of Albion–Rains–Warnaar (Constr. Approx. 62 (2025),
equation (4.1)). The contribution of each Part is the explicit application
to the Apéry determinants, not the invention of the general methods.

## Provenance of Part III

Part III was merged from one manuscript (batch 77, cluster P5, manuscript
10; arrival commit `096ee7b87`, placement commit `4f11bc9c0`, pin
`946b6c762`, at which this report's text was exactly Parts I and II as now
printed). It contributed Sections 21–30, the three new bibliography entries
and the 28 `03-shifted-` files. The merge had to choose in these places:
the manuscript's restated definition of the Apéry numbers is replaced by a
reference to Part I's (1.1); its citations of this report and of Part II's
density program become internal references; six letters are renamed
(Notation, above); Section 21 gains Remark 21.1 (the quadratic term is Part
I's Theorem 4.1), a paragraph on the false reading s ↓ 0, a provenance
subsection and the notation table (Table 5); an editorial paragraph after
Corollary 27.1 relates the thresholds to the transseries volume; and the
title page, abstract, running head and Appendix note now announce Part III.
Nothing else of the manuscript was changed, shortened or dropped. The
intake checked the identity A(s) = (1+s) log C − Ψ(s) by hand and reran the
replay as described above; the analytic proof (the confinement adaptation,
Lemma 28.2 and the coefficient algebra beyond the replay's symbolic
checks) was not independently re-derived.
