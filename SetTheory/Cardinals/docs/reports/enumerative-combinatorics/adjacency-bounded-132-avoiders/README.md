# Strict growth and the Catalan limit for adjacency-bounded 132-avoiding permutations

**Strict monotonicity of the growth constants, and the exact constant 2 log π in their approach to 4**

This is a research report in two parts. Part I is the original report of
19 September 2026. Part II was added on 28 September 2026 in batch 38 of
ProveIt's incoming-report intake, from a later manuscript that answers the
question Part I left open: whether the centered remainder `E_m` converges.
Both were prepared for Vladimir Reshetnikov and are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Strict growth and the Catalan limit for adjacency-bounded 132-avoiding permutations*) | `strict_growth_132.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–9 (pp. 5–19) and Appendices A–C (pp. 41–42) |
| 02 | batch 38, manuscript 04 (*Closing the Catalan growth-constant gap: Endpoint renewal comparison for adjacency-bounded 132-avoiding permutations*, 28 Sep 2026, 23-page PDF as delivered) | `Closing_Catalan_Growth_Gap` (inner `Adjacency_Growth_Constant/`, main file `article.tex`) | `6c9175a54` | `938b2f74e` (prefix `02-centered-remainder-`) | Part II: Sections 10–20 (pp. 20–40) |

The pin `6c9175a54` is ProveIt commit
`6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0`; the manuscript quotes the blob
`5ec75ee4…` of the `article.tex` it read, and that blob was unchanged at the
placement commit, so Part II's statements about Part I refer to the text
printed here. The archive arrived in `fbba58593`. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. Part II
prints every result, proof, example, remark, limitation and question of the
manuscript. What it re-derives from Part I (endpoint recurrence, component
structure and spectral interface, first-entry lemma, injective skew blocks) is
printed once, in Part I, and credited; the manuscript's different proof of
`lambda_U(m) > 1` is kept as a second proof (Section 11). Section 20.5 of the
article lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and neither source claims otherwise. The
exact certificates verify finite algebraic statements; they are not a proof of
the all-`m` or asymptotic theorems.

## Results

Let `a_n^(m)` count the 132-avoiding permutations of `{1,…,n}` with every
adjacent absolute difference at most `m`, and let `alpha_m` be their exponential
growth constant (`n → ∞` with `m` fixed). Logarithms are natural.

**Part I** (unchanged apart from dated pointers) proves:

1. `alpha_(m+1) > alpha_m` for every integer `m ≥ 1`. More strongly, both
   irreducible component growth rates increase strictly for `m ≥ 2`
   (Theorem 1.1). This completes the remaining strict-inequality part of
   Nadler's Conjecture 2, using the endpoint system introduced by Mayama and
   Akita; the report includes proofs of its finite-state prerequisites.
2. `4 - alpha_m = (2 log m + 4 log log m + O(1))/m` (Theorem 1.2), by a separate
   counting and analytic proof.
3. For `E_m = m(4 - alpha_m) - 2 log m - 4 log log m`,
   `2 log π - 4 log 2 ≤ liminf E_m ≤ limsup E_m ≤ 2 log π` (Theorem 1.3).

**Part II** (manuscript 04). Let `r_m` be the positive root of
`sum_{k=1}^m C_(k-1) r^k = 1` and `beta_m = 1/r_m`. It proves:

1. `alpha_m < beta_m < 4` for every `m ≥ 2` (Theorem 10.1), by a
   Catalan-weighted positive vector on the last endpoint threshold
   (Lemma 12.2) that absorbs the append transition through the Catalan
   renewal identity. This is strictly sharper than Part I's scalar majorant.
2. `0 ≤ beta_m - alpha_m ≤ beta_m - lambda_U(m) = O((log m)^2/m^2)`
   (Theorem 10.2), from a uniform first-deficiency tail bound (Lemma 13.2)
   and a cutoff `d = ⌈log_2 m⌉` growing with `m` (Theorem 15.2).
3. **`E_m → 2 log π`** (Corollary 15.3): the window of Part I's Theorem 1.3
   closes at its upper endpoint. Part II sharpens Part I; it refutes nothing.
4. An expansion of `m(4 - alpha_m)` to every inverse-logarithmic order, with
   an explicit triangular recursion for the correction polynomials and the
   first four printed and symbolically checked (Theorem 10.3,
   Proposition 16.1, equations (77) and (79)).
5. `(lambda_V(m) - lambda_U(m))_+ = O((log m)^2/m^2)` (Corollary 15.4): a
   one-sided constraint on the component competition.

## Not claimed

- The all-`m` component ordering (`V` dominates `U` for every `m ≥ 5`,
  Problem P3 of Mayama–Akita) is not proved, in either part. Part I certifies
  it only for `m = 2..20`; Part II bounds only a dominant `V`'s lead, and does
  not bound `|lambda_V - lambda_U|` when `V` is below `U`.
- No asymptotic equivalent, or optimal order, of the scalar defect
  `beta_m - alpha_m`; no joint limit in `n` and `m`; no minimal recurrence order,
  uniform denominator factorization, simple-pole statement or state
  minimization of `A_m(x)`.
- Part II's scalar polynomial is not a denominator of `A_m`,
  `det(I - W_V) ≠ 1 - K_m` in general, and the coefficientwise majorant
  `A_m ⪯ 1/(1 - K_m)` is **false** (at `m = 2`, `n = 3`: 5 against 3). The
  upper bound is spectral only (Remark 12.4, Section 18).
- The Perron test vector is a supersolution, not an approximation of the true
  eigenvector. A fixed truncation of the asymptotic expansion does not promise
  better numerical accuracy at any particular `m`.
- **The numerics are not evidence for the value `2 log π`.** At `m = 10^6`
  the computed corridor for `E_m` is about `[3.1495, 3.1503]`, 0.86 above the
  limit `2 log π ≈ 2.2895`, and its lower endpoint is not monotone (it peaks
  near 3.168 at `m = 73,920`). This agrees with the slow inverse-logarithmic
  corrections (the first, `(8z - 12)/log m`, is about 0.98 at `m = 10^6`), but no
  computation in the range distinguishes `2 log π` from nearby constants; the
  value rests on the proofs alone (Remark 17.1).
- Floating-point tables and all four figures are illustrations, not interval
  certificates; only Part I's Perron certificates and Part II's Table 7 are
  rigorous (outward-rounded from exact fractions).
- No priority. Both literature checks were targeted (Part I on
  19 September 2026, Part II on 28 September 2026: the arXiv v1 records of
  Nadler and of Mayama–Akita); neither is an exhaustive novelty certification
  or external peer review.

## Labels

Part I's 65 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `tab:`,
`fig:`, `app:`) and are unchanged, with unchanged numbers (compared in the
`.aux` files of the committed and the new build). Part II added **93** labels,
all with the prefix `crem:` ("centered remainder"). Total: 158. No label was
renamed or removed. Part II starts at Section 10 and its tables and figures
continue Part I's numbering (Tables 4–10, Figures 3–4); Part I's appendices
come after Part II and contain no numbered equations, tables or figures.

## Notation

Part I's symbols keep their meanings, and the manuscript uses them the same
way (`alpha_m`, `E_m`, `C_k`, `c_(k,p)`, `U_m`, `V_m`, `lambda_U`, `K_(m,d)`,
`s_(m,d)`). Table 4 (Section 10.2) lists Part II's symbols. Watch in
particular for:

- `K_m` (one index) `= sum_{k≤m} C_(k-1) x^k` is **not** the block polynomial
  `K_(m,d)` (two indices); `K_(m-d)` is the Catalan polynomial truncated at
  `m - d`, and `K_(m,d) ⪯ K_(m-d)`. Part I's majorant is `R_m = x + K_m`.
- `r_m`, `beta_m`, `t_m = m log(4 r_m)` belong to `K_m`; they are not the
  component roots `r_U(m)`, `r_V(m)`, nor Part I's `t_m* = m log(4/alpha_m)`.
- `b_1 = 1/4` in Part II, `b_1 = 1/2` in Part I's Section 7 (the extra `x`).
- Renamed from the manuscript: `L → Λ = (1/2) log m` (Part I's `L_m` includes
  `log log m`), `P_j → 𝒫_j` (Part I's `P_3`, `P_4` are numerators),
  `B_N → ℬ_N`, `T_m → Δ_m`, the absolute constants `C, c → C_*, c_*`,
  `W_U, W_V → W_(U_m), W_(V_m)`, and the manuscript's `H = log m` is written out.
  No normalization changed.

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 42 pages (title page, contents pp. 2–4,
                                                     Part I pp. 5–19, Part II pp. 20–40, Part I's appendices pp. 41–42)
README.md                                            this guide
build.sh, build.ps1                                  Part I's three-pass pdfLaTeX scripts (build in place; see below)
requirements.txt                                     Part I's pins: numpy 2.3.5, scipy 1.17.0, sympy 1.14.0, matplotlib 3.10.8
code/model.py                                        Part I: exact endpoint model and combinatorics
code/compute.py                                      Part I: numerical proposals and exact symbolic solver
code/verify.py                                       Part I: standard-library independent exact verifier
code/plot_results.py                                 Part I: Figures 1–2
data/sequences.csv                                   Part I: exact a_n^(m), n = 0..200, m = 1..12
data/growth_constants.csv                            Part I: component roots, m = 2..20
data/perron_certificates.json                        Part I: 38 rational Perron-radius certificates
data/symbolic_certificate_m1..m4.json                Part I: polynomial state certificates (four files)
data/generating_functions.json                       Part I: reduced rational functions, m = 1..4
data/large_m_scalar_bounds.csv                       Part I: scalar root evaluations through m = 1,000,000
data/computation_log.txt, data/verification_log.txt  Part I: recorded runs
data/environment.json                                Part I: the numerical/symbolic environment
figures/component_growth.{pdf,png}                   Part I: Figure 1
figures/scalar_remainder_bounds.{pdf,png}            Part I: Figure 2
code/02-centered-remainder-model.py                  Part II: exact Catalan, endpoint and block objects
code/02-centered-remainder-verify.py                 Part II: exact finite checks (standard library)
code/02-centered-remainder-verify_expansion.py       Part II: exact symbolic check of the expansion (SymPy)
code/02-centered-remainder-compute.py                Part II: floating-point illustrations (NumPy, SciPy)
code/02-centered-remainder-plot_results.py           Part II: its two figures from the CSVs (Matplotlib)
data/02-centered-remainder-verification_report.json  Part II: recorded exact-check run (PASS)
data/02-centered-remainder-verification_console.txt  Part II: its console output (identical to the report)
data/02-centered-remainder-rational_certificates.json  Part II: five exact scalar corridors (Table 7)
data/02-centered-remainder-expansion_verification.json  Part II: recorded symbolic run (P_1..P_4, residual 0)
data/02-centered-remainder-expansion_console.txt     Part II: its console output (identical to the JSON)
data/02-centered-remainder-scalar_numerics.csv       Part II: scalar corridor, 63 values of m from 10 to 10^6 (CRLF)
data/02-centered-remainder-component_numerics.csv    Part II: component rates and beta_m, m = 2, 3, 4, 5, 10, 20, 30, 50 (CRLF)
data/02-centered-remainder-environment.json          Part II: environment (byte-identical to data/environment.json)
data/02-centered-remainder-requirements.txt          Part II: lower-bound pins, as delivered at the package root
data/02-centered-remainder-pdf_fonts.txt             Part II: font list of the delivered (unshipped) PDF
data/02-centered-remainder-pdf_validation.json       Part II: inspection record of the delivered 23-page PDF
figures/02-centered-remainder-remainder_corridor.pdf Part II: Figure 3
figures/02-centered-remainder-corridor_width.pdf     Part II: Figure 4
```

The sixteen `02-centered-remainder-` code and data files were staged in the
placement commit `938b2f74e`, byte-identical to the delivery; the two CSVs
are all-CRLF as delivered and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`. The two Part II figure PDFs were added
in the write phase, copied byte-identically from the delivered `figures/`; the
delivered PNG versions of those figures are not shipped (the plot script
regenerates both formats).

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex` three times. Build in a scratch copy of `article.tex` and
`figures/`, so that no auxiliary files land here; `build.sh` and `build.ps1`
run three pdfLaTeX passes in this directory and leave `.aux`, `.log`, `.toc`
and `.out` files beside the source. The figures are retained, so Python is not
needed to rebuild. The shipped PDF was built with MiKTeX (pdfTeX 1.40.26) with
no errors, no undefined or multiply defined references, no duplicate
destinations and no overfull or underfull boxes; the two font-substitution
warnings (`T1/cmss` at 5.5 pt) are present in a build of the committed Part I
text as well. No font files are included.

## Rerun the checks

**Part I.** Its exact verifier only reads its data and runs in place:

```sh
py code/verify.py        # or: python code/verify.py; do not use -O
```

It needs no third-party packages and checks, among others, 2,840 cumulative
endpoint counts, 53,534 weighted-edge comparisons for the shift, the 38
rational Perron certificates (3,458 strict integer row inequalities) and the
four polynomial-matrix certificates; `data/verification_log.txt` is its
recorded run (Python 3.13.5). Part I's generator and plot script
**overwrite** the shipped tables, certificates and figures, so run them only
on a copy:

```sh
W=/path/to/scratch
mkdir -p "$W/01" && cp -r code data figures requirements.txt "$W/01/"
(cd "$W/01" && python -m pip install -r requirements.txt \
   && python code/compute.py --max-m 20 --symbolic-max 4 --large-scalars \
   && python code/verify.py && python code/plot_results.py)
```

A positive numerical eigenvector is only a proposal: the generator refuses to
issue a certificate unless the integer inequalities pass, and the verifier
checks them again without the numerical solver. Part I's large-`m` scalar
bounds are floating-point evaluations of roots for which the article proves
exact comparison theorems, not outward-rounded interval endpoints.
`OPENBLAS_NUM_THREADS=1` is optional.

**Part II.** Its scripts still use the delivered names. Run in place,
`02-centered-remainder-verify.py` and `02-centered-remainder-compute.py` fail
with `ImportError`, because their `from model import …` loads Part I's
different `code/model.py`; `02-centered-remainder-verify_expansion.py` would
write a new `data/expansion_verification.json` here; and
`02-centered-remainder-plot_results.py` reads `data/scalar_numerics.csv`,
which does not exist here. Restore the delivered layout in a scratch copy
(Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code" "$W/02/data" "$W/02/figures"
for f in code/02-centered-remainder-*.py; do cp "$f" "$W/02/code/${f#code/02-centered-remainder-}"; done
for f in data/02-centered-remainder-*; do cp "$f" "$W/02/data/${f#data/02-centered-remainder-}"; done
mv "$W/02/data/requirements.txt" "$W/02/requirements.txt"
cd "$W/02"
py code/verify.py                 # standard library; writes data/verification_report.json
                                  #   and data/rational_certificates.json
py code/verify_expansion.py       # SymPy; writes data/expansion_verification.json
uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 python code/compute.py
                                  # writes data/scalar_numerics.csv, data/component_numerics.csv
uv run --no-project --with matplotlib==3.10.8 python code/plot_results.py
                                  # writes figures/remainder_corridor.* and corridor_width.*
```

The first three were run this way on 28 September 2026 (Python 3.14.4,
SymPy 1.14.0, NumPy 2.3.5, SciPy 1.17.0): `verify.py` passed with the recorded
counts (55 first-entry counts, 4,930 `V`-row comparisons, 9,000 tail
inequalities, 67,425 restricted-`U` comparisons, five corridors), and its two
outputs and the symbolic output equal the shipped files apart from Windows
line endings; the regenerated CSVs differ from the shipped ones by at most
6 × 10⁻¹⁶ relative (last-ulp floating-point differences). The plot script was
not rerun. On Windows, Python writes the JSON files with CRLF line endings.

## Discrepancies and delivery names

- **Delivery names.** The Part II scripts and records use the delivered paths
  `code/verify.py`, `code/model.py`, `data/*.json`, `data/*.csv` and
  `figures/remainder_corridor.*`, `figures/corridor_width.*`; the recipe above
  recreates them in a copy. The article quotes the shipped names.
- **Unshipped PDF.** `data/02-centered-remainder-pdf_validation.json` and
  `data/02-centered-remainder-pdf_fonts.txt` describe the manuscript's
  delivered 23-page PDF, which is not shipped; `article.pdf` here is a new
  build of the merged text (42 pages).
- **Duplicates.** Each Part II console capture is byte-identical to the JSON
  it prints, and `data/02-centered-remainder-environment.json` is
  byte-identical to Part I's `data/environment.json` (the same environment).
- **Requirements.** Part II's delivered `requirements.txt` (shipped as
  `data/02-centered-remainder-requirements.txt`) gives lower bounds
  (`numpy>=1.24`, `scipy>=1.10`, `sympy>=1.12`, `matplotlib>=3.7`); the
  versions actually used are those in its environment file, the same as
  Part I's exact pins in `requirements.txt`.
- **Table rows.** Table 8 of the article omits the `m = 30` row of
  `data/02-centered-remainder-component_numerics.csv`, as the manuscript did.
- **Part I's delivered files.** Part I's text and its data files predate the
  addition; the sentences of Part I that called the convergence of `E_m`
  open (Theorem 1.3, Section 9) now carry dated pointers to Part II, and its
  other files are unchanged.

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats these permutations,
and Part II names no neighbouring report, so no reciprocal note was written.
The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration anywhere in ProveIt formalizes any statement of Parts I–II (a
search of the repository's `.lean` files for 132-avoidance or adjacency bounds
finds none). Section 19.9 records the formalization targets the manuscript
proposes (the renewal polynomial identity, the supersolution argument, the
skew-cut injection, the uniform tail inequality); none has been started.

## Sources and attribution

Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*,
arXiv:2604.22135v1, Conjecture 2 in Section 5.2.
https://arxiv.org/abs/2604.22135

Teruki Mayama and Dai Akita, *Finite-state enumeration of adjacency-constrained
132-avoiding permutations*, arXiv:2605.23519v1, especially Theorem 2.4,
Proposition 2.7, Theorems 4.12 and 4.14, and Problems P1–P4.
https://arxiv.org/abs/2605.23519

The finite-state system, rationality, existence of the growth constants,
non-strict monotonicity, and the earlier O(log(m)/m) bound are established
work and are credited in the article. Part I's new arguments are the shift
embedding, its strict-growth consequence and the refined asymptotic
comparison; Part II's are the Catalan-weighted spectral upper bound, the
uniform tail and growing-cutoff corridor, the exact constant and the
all-orders expansion. No third-party paper PDFs or font files are included.
