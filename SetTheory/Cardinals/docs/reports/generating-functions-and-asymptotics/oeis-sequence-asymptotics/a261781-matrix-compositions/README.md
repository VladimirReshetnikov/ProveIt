# Matrix Compositions: Exact Spectra, Hankel Products, and Uniform Asymptotics

**OEIS A261781, its empty-row transition, and refined asymptotics for A261784 — Part II: finite spectra, uniform asymptotics, and two Poisson limits**

This research report is dated 3 October 2026. It was built from two manuscripts of ProveIt's incoming-reports intake, both of batch 85, written independently of each other on the same subject: manuscript 06 (Part I, the base) and manuscript 01 (Part II). Manuscript 06's author line and PDF metadata read "OpenAI ChatGPT", with "Research prepared for Vladimir Reshetnikov"; manuscript 01's title page and PDF metadata read "Research report prepared for Vladimir Reshetnikov" and name no author or tool.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | batch 85, no. 06 | `Matrix_Compositions_Uniform_Asymptotics.zip` (21 files; main file `matrix_compositions.tex`, 2,078 lines, 100 labels; 31-page PDF *Matrix Compositions: Exact Spectra, Hankel Products, and Uniform Asymptotics*) | `ce37e13f4` (the repository search index it saw) | `345284ac8` | `fa2f3e419` | Part I (Sections 1–10); files prefixed `06-hankel-` |
| addition | batch 85, no. 01 | `OEIS_Matrix_Compositions_Research.zip` (26 files in `matrix_compositions_research/`; main file `matrix_compositions.tex`, 1,561 lines, 98 labels; 22-page PDF *Matrix compositions: finite spectra, uniform asymptotics, and two Poisson limits*) | `d68b65ea0` (tree revision; its search index exposed `ce37e13f4`) | `317c1ce2e` | `fa2f3e419` | Part II (Sections 11–22) and notes in Part I; files prefixed `01-two-poisson-` |

Manuscript 01 arrived with the rest of batch 85 in `317c1ce2e` (2026-10-03 17:53 −0700); the batch-85A placement `713149ded` held it back, because manuscript 06 had arrived thirteen minutes later in `345284ac8` on the same theorems. Both pins are ancestors of the placement. The two texts share 0.7 % (01 in 06) and 0.5 % (06 in 01) of their word 8-grams, almost all bibliography entries, and permute their Greek letters; neither is an edition of the other. The placement commit `fa2f3e419` deleted both archives from `docs/incoming`; they survive in their arrival commits (`git show 345284ac8:docs/incoming/Matrix_Compositions_Uniform_Asymptotics.zip`, `git show 317c1ce2e:docs/incoming/OEIS_Matrix_Compositions_Research.zip`).

**Status: AI-assisted, unrefereed, not formalized.** The intake reran both packages on copies and spot-checked the mathematics (see "Checks by the intake"). It did not re-derive every proof.

## Files

```
README.md                                   this guide (replaces both delivered READMEs)
article.tex                                 the merged report (LaTeX, internal bibliography)
article.pdf                                 the compiled report, 55 pages
06-hankel-SOURCE_AUDIT.txt                  (06) its bounded source and contribution audit, as delivered
01-two-poisson-provenance-SOURCES.md        (01) its sources and bounded priority audit, as delivered
code/06-hankel-verify.py                    (06) exact enumeration, recurrence, Hankel and impulse checks; coupon and diagonal diagnostics (SymPy, mpmath)
code/06-hankel-make_figures.py              (06) the coupon-window figure and its curve data (matplotlib; imports verify)
code/01-two-poisson-verify.py               (01) exact identities, kernel polynomials, constants, a(0..200) and the CSV/table outputs (SymPy, mpmath)
code/01-two-poisson-make_tables.py          (01) LaTeX table bodies from the CSV files (standard library)
code/01-two-poisson-make_figures.py         (01) the A261784 error figure (matplotlib)
code/01-two-poisson-ray_spotchecks.py       (01) optional saddle-formula checks at n/k = 3/2, 3, 5 (imports verify, so needs SymPy too)
data/06-hankel-oeis_rows.json               (06) the nine OEIS rows n = 0..8 of A261781 it matches (third-party, CC BY-SA 4.0)
data/06-hankel-recurrence_checks.json       (06) numerators, denominators, gcd and impulse checks, k = 1..10
data/06-hankel-hankel_determinants.csv      (06) full-rank tail Hankel determinants, k = 1..5, shifts 1..3
data/06-hankel-initial_hankel_determinants.csv (06) initial size-(D+1) determinants, k = 1..4
data/06-hankel-weighted_hankel_checks.json  (06) five symbolic determinant identities in u
data/06-hankel-pole_bound_checks.csv        (06) thirty comparisons with the uniform pole bound
data/06-hankel-coupon_window.csv            (06) fifteen coverage-window cases with Bonferroni/pole budgets
data/06-hankel-coupon_curve.csv             (06) the 393 finite-k points of Figure 1
data/06-hankel-diagonal_constants.json      (06) seventy-digit r, v, b, kappa_3, kappa_4, d_*, c_*, beta_1, beta_2
data/06-hankel-diagonal_asymptotics.csv     (06) exact a_N and diagnostics, N = 5..100 (Table 4)
data/06-hankel-verification_summary.json    (06) its run receipt (PASS)
data/06-hankel-figure_generation_summary.json (06) its figure receipt
data/06-hankel-requirements.txt             (06) mpmath==1.3.0, sympy==1.14.0, matplotlib==3.10.8
data/01-two-poisson-verification.json       (01) its run receipt (ALL CHECKS PASSED), ninety-digit constants, denominators k = 1..8
data/01-two-poisson-verification_stdout.txt (01) the same receipt as printed (records the delivery path /mnt/data/…)
data/01-two-poisson-a261784_exact.txt       (01) a(0..200) of A261784, computed exactly
data/01-two-poisson-a261784_asymptotics.csv (01) relative errors of orders 0..3, N = 5..200
data/01-two-poisson-coupon_transition.csv   (01) exact coverage probabilities and both approximations
data/01-two-poisson-stirling_defect.csv     (01) Stirling-defect probabilities and their Poisson limit
data/01-two-poisson-ray_spot_checks.csv     (01) output of ray_spotchecks.py
data/01-two-poisson-ray_spotchecks_stdout.txt (01) its printed output (records /mnt/data/…)
data/01-two-poisson-error_table.tex         (01) body of Table 7
data/01-two-poisson-coupon_table.tex        (01) body of Table 8
data/01-two-poisson-defect_table.tex        (01) body of Table 6
data/01-two-poisson-diagonal_table.tex      (01) a longer diagonal table body, unused by either article
data/01-two-poisson-document_qa.json        (01) its QA record of its own delivered 22-page PDF (not of this build)
data/01-two-poisson-OEIS_updates_draft.txt  (01) draft OEIS additions — NOT submitted; see below
data/01-two-poisson-requirements.txt        (01) sympy==1.14.0, mpmath==1.3.0, matplotlib==3.10.8
figures/06-hankel-coupon_window.pdf         (06) Figure 1 (used by the article)
figures/06-hankel-coupon_window.png         (06) the same at 220 dpi
figures/01-two-poisson-a261784_errors.pdf   (01) Figure 2 (used by the article)
figures/01-two-poisson-a261784_errors.png   (01) the same as PNG
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. `article.tex` is manuscript 06's `matrix_compositions.tex` with the edits listed under "Edited text"; `article.pdf` is a build of it, not either delivered PDF. Ten CSV files (all six of 06's and all four of 01's) are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`.

## Delivery names and shipped names

| Delivered (06) | Shipped |
|---|---|
| `matrix_compositions.tex` | `article.tex` (edited) |
| `README.txt` | replaced by this `README.md` |
| `SOURCE_AUDIT.txt` | `06-hankel-SOURCE_AUDIT.txt` |
| `code/verify.py`, `code/make_figures.py` | `code/06-hankel-verify.py`, `code/06-hankel-make_figures.py` |
| `code/requirements.txt` | `data/06-hankel-requirements.txt` |
| `data/X` (12 files) | `data/06-hankel-X` |
| `figures/coupon_window.{pdf,png}` | `figures/06-hankel-coupon_window.{pdf,png}` |

| Delivered (01, inside `matrix_compositions_research/`) | Shipped |
|---|---|
| `provenance/SOURCES.md` | `01-two-poisson-provenance-SOURCES.md` |
| `scripts/X.py` (4 files) | `code/01-two-poisson-X.py` |
| `results/X` (13 files) | `data/01-two-poisson-X` |
| `OEIS_updates_draft.txt`, `requirements.txt` | `data/01-two-poisson-OEIS_updates_draft.txt`, `data/01-two-poisson-requirements.txt` |
| `figures/a261784_errors.{pdf,png}` | `figures/01-two-poisson-a261784_errors.{pdf,png}` |

**Not shipped** (they survive in the arrival commits): both delivered PDFs (replaced by a build of the merged text); manuscript 01's `matrix_compositions.tex` (merged as Part II) and `README.md` (replaced by this README); manuscript 06's `README.txt` (staged by the placement as `README.md`, now replaced); manuscript 01's checksum ledger `SHA256SUMS.txt` (25/25 verified at the intake, then retired). Manuscript 06 has no checksum ledger.

## Labels and numbering

The report's labels carry the prefix `mxc:`. Manuscript 06's 100 labels were given the prefix before anything cited them, and every reference was updated; the write added nine more `mxc:` labels (the Part I heading, the notation dictionary section and table, Remarks 2.3, 4.2 and 7.3, equations (2.8) and (4.4), and Appendix A). Part II's 64 labels carry the sub-prefix `mxc:tp:`. In all **173** labels; there are no duplicates. Part II follows manuscript 06's last section as Sections 11–22, Tables 5–8 and Figure 2. The three inserted remarks shift some numbers of Sections 2, 4 and 7 relative to manuscript 06's delivered PDF (for example its Remark 2.3 on the initial impulse is now Remark 2.4, and its Corollary 7.3 for A261784 is now Corollary 7.4).

## Notation

The two manuscripts permute three Greek letters: manuscript 06's η (the Poisson mean k e^{−n/k}), λ (the ratio n/k on compact rays) and ρ (the pole-bound ratio L/√(L²+8)) are manuscript 01's λ, ρ and η. Its saddle r is 01's τ, its v = Lr/2 is 01's μ, and 01's "β₁" is β₁ + 1/6, not manuscript 06's β₁. **The whole report is printed in manuscript 06's letters**; Table 2 (Section 1.5) lists every renamed symbol of manuscript 01 with the false reading the old letter would have. No normalization was changed. Manuscript 06's own overloaded letters (D, d, c, b, P_j, E, r, v, m) are kept and listed in Appendix A.

## What is claimed

**Part I** (manuscript 06; every statement for column weight u > 0 unless restricted):

- **Minimal recurrence and spectrum** (Theorem 2.2): the reduced denominator of column k is ∏_{j≤k}((1+u)(1−z)^j − u), so the minimal eventual constant-coefficient recurrence has order exactly k(k+1)/2, over ℂ; all roots simple and nonzero. The exact initial impulse (Remark 2.4): the recurrence starts at n = D + 1, with Σ q_i T(D−i, k) = (−1)^{k+D} 2^{k−1}.
- the growth-constant limit d_{k+1} − d_k → 1/log 2 with expansions of d_k, c_k and of the increment (Corollary 2.5).
- **Maximal Hankel determinant** (Theorem 3.1): H_{k,s}(u) as an explicit product in ℤ[u] (root products, discriminants, resultants), rank exactly k(k+1)/2, the initial exceptional determinant, coefficientwise positivity, and all other zeros on Re u = −1/2.
- **Uniform pole bound** (Theorem 4.1): A(n,k) = c_k d_k^n (1 + ε), |ε| ≤ (π²L²/24) ρ^{n−1}, ρ < 0.239, for all n, k ≥ 1; weighted version.
- **Coverage window** n = k(log k + s): the generating function E(1+w)^M to first correction uniformly in complex w (Theorem 5.1); the probability-mass expansion and the sharp total-variation rate Θ((log k)/k) with its leading constant; the Poisson limit and the critical count (Corollary 5.3).
- **Joint Gaussian–Poisson law** of column count and zero-row count, with independence and the conditional law given M = m (Theorem 6.2).
- **Compact rays** n/k ∈ K ⋐ (1,∞): the uniform saddle expansion to every fixed order (Theorem 7.1, (7.16)–(7.17)); for A261784 the closed amplitude c_* and the corrections β₁, β₂ (Corollary 7.4, (9.1)); the Gaussian column law with mean and variance to O(1/k) (Corollary 7.5).
- **Prescribed column count** m = o(k): the threshold m log(1 + n/(km)) − log k → s and the shifted window at m ~ γ(log k)² (Theorem 8.1, Corollary 8.2).

**Part II** (manuscript 01; **all at u = 1**). Its re-proofs of Part I's theorems are listed in Table 5 and not reprinted. New relative to manuscript 06:

- strict monotonicity of d_{k+1} − d_k, always below 1/log 2 (Theorem 12.1);
- **every fixed order of the coverage probability** P(M = 0) in the window, by a finite algorithm with a uniform remainder (Theorem 13.1);
- **the entire Stirling kernel** W_n(w): the representation without truncation (Proposition 14.1), |W_n| ≤ e^{|w|} and an exact differential recurrence in n (Lemma 14.2), and the all-orders expansion uniform on compact subsets of ℂ with no hypothesis on k, with P₃ (Theorem 14.3) — the general form of Part I's Lemma 7.2; a second exact algorithm for the P_r;
- a recursion for the cumulants κ_j (Section 15);
- **the Poisson law of the Stirling defect** Δ_{n,k} = n − Q_{n,k}, with its analytic generating function to every order (Theorem 16.2), which implies Part I's two moments of D;
- the third diagonal correction β₃ = −0.0024435384228485950037…, the recipe for every further one, and fifty-digit constants (Corollary 17.1);
- an asymptotic Lambert-W inversion of A261784 and integer threshold brackets (Propositions 18.1, 18.2) — an instance of the transseries volume's apparatus, no novelty claimed for the method;
- exact-ratio coverage, defect and error tables (Tables 6–8), its research questions (Section 20) and its proof audit (Section 21).

**Not new** (both Parts credit them): the generating functions, inclusion–exclusion, the root-of-unity formula, the fixed-row asymptotic, the positive Stirling–Fubini transform and the stars-and-bars identities (Munarini–Poneti–Rinaldi, JIS 12 (2009), Article 09.4.8, Props. 1, 12, 13, 22–24, 28, 29); **the existence of a recurrence of order k(k+1)/2 with the product denominator** (their Proposition 25, printed page 16, with Remark 26 giving two and three rows); the leading A261784 law, d_* and the decimal c_* (Kotěšovec, in the OEIS entry); Louchard's fixed-row Gaussian theorem, an antecedent of Theorem 6.2.

## Correction of manuscript 01's novelty claim

Manuscript 01's abstract, its delivered README and its OEIS draft say that it proves "its two explicitly posted conjectures" of A261781. A constant-coefficient recurrence of order binom(k+1, 2) with the denominator ∏(2(1−x)^j − 1) is Proposition 25 of Munarini, Poneti and Rinaldi (2009), eight years before the conjecture; their Remark 26 prints manuscript 01's two-row example (f^{(2)} = (3x² − 2x³)/(1 − 6x + 10x² − 4x³) and f_{n+3} = 6f_{n+2} − 10f_{n+1} + 4f_n). The intake checked both in the published paper. Only the **minimality** (no shorter eventual recurrence, even over ℂ) is new; the limit of the increments is immediate from their Proposition 13, and only the strict monotonicity is new. The report states this in Remark 2.3 and Section 11.2. Manuscript 01's `01-two-poisson-provenance-SOURCES.md` lists only Propositions 1, 12, 13 and 29 and says printed pages 3 and 18 were inspected; Proposition 25 is on page 16. That file, the OEIS draft and the stdout receipts are delivered text and are kept byte-identical; the correction lives in the article and here.

## What is not claimed

These are both manuscripts' own limits, kept in full (manuscript 06's abstract, Section 1.3, Remark 4.3, the moving-mean remark of Section 5, the end of Section 7.6, Sections 8 and 9 and the preamble of Section 10, `06-hankel-SOURCE_AUDIT.txt`; manuscript 01's status paragraph, Section 11, the remarks after Theorems 13.1 and 16.2, Remark 15.1, Sections 18, 19 and 21, `01-two-poisson-provenance-SOURCES.md`).

- Unrefereed proofs; no proof-assistant verification; no historical-priority guarantee. Both literature audits are bounded; "established here" means proved here, not first.
- Theorem 4.1 controls A(n,k) uniformly; it does not say T(n,k) ~ c_k d_k^n uniformly. Manuscript 01's variant bound (k−1)ρ^{n+1} (Remark 4.2) is not claimed small for large k and fixed n.
- The compact-ray results need n/k in a fixed compact subset of (1,∞); neither n/k → 1 nor the coverage window is covered, and the actual n/k must be used when n is rounded. "All orders" means each fixed finite order: no convergent series, no exponentially small sectors, no optimal truncation.
- No rate is asserted for an arbitrary o(1) perturbation of the Poisson mean. The prescribed-column theorem is not a theorem about a column weight u_k → 0. Hankel positivity is for the maximal minors only (a negative 2 × 2 minor is shown).
- The Stirling defect is an auxiliary variable; neither manuscript claims a canonical matrix statistic for it.
- Minimality concerns homogeneous constant-coefficient recurrences only, not polynomial-coefficient, nonlinear or multi-column ones.
- The numerics are diagnostics: manuscript 06's coupon brackets carry analytic Bonferroni and pole budgets but their decimal endpoints are not directed-rounded; manuscript 01's 90-digit values are not interval enclosures; β₂ and β₃ are evaluations of finite exact prescriptions, not fits; the N = 100 and N = 200 errors are finite comparisons; C_J in the threshold bracket is existential, and no unconditional formula N(Y) = ⌈x_J(Y)⌉ is claimed.
- Manuscript 01 compared 8 rows of A261781 and 15 terms of A261784, not the 201-term b-file; manuscript 06 compared 9 rows. The coverage correction is not claimed monotone in accuracy for small inputs.
- The research questions of both manuscripts are proposals, "not assertions that every formulation is open throughout the literature". Two are re-scoped in the text: manuscript 06's Research question 2 is answered for the single event M = 0 by Theorem 13.1, and manuscript 01's question on joint column laws is answered in the coverage window by Theorem 6.2 (open on compact rays jointly with the defect).

## Relation to neighbouring material and formal status

- **Method neighbour** [`a260700-parabolic-double-cosets`](../a260700-parabolic-double-cosets/) (prefix `pdc:`): the same two devices, a uniform extraction of the Fubini pole at log 2 (its section `pdc:sec:poles`) followed by an outer Stirling transform (`pdc:sec:outer`), for a different sequence; it cites Munarini–Poneti–Rinaldi as related work. No theorem is shared. Manuscript 06 found it in its repository search and assumes nothing from it.
- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`: its Theorem `q2:thm:fubini` (exact pole-lattice transseries of the Fubini numbers) has the estimate (7.5) of both manuscripts as its one-pole truncation; its `p0:thm:perturbed-inversion` and `p0:thm:staircase` are the apparatus of which Section 18 is an instance. Manuscript 01 read the volume's overview README at its pin as motivation but cited neither theorem.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report. The only ingredient formalized anywhere in the repository is the Fubini exponential generating function used in Section 7: `Fabius.fubini` (the definition F_n = Σ k! S(n,k)), `Fabius.egfA_fubini` and `Fabius.two_sub_exp_mul_egfA_fubini` ((2 − e^t) Σ F_n t^n/n! = 1), in `Analysis/FabiusFunction/Lean/FabiusFunction/OrderedBell.lean`. Nothing else stated in either Part is formalized. Both manuscripts propose the reduced denominator and its no-cancellation proof as a first formalization target (Section 10.1, Section 20); that is a proposal only.
- No report of the collection treats A261780, A261781 or A261784.

## Third-party material and the OEIS draft

- **OEIS fixtures.** `data/06-hankel-oeis_rows.json` and the `OEIS_ROWS` list in `code/06-hankel-verify.py` hold the nine rows n = 0..8 of A261781; the `TRIANGLE_FIXTURE` (8 rows of A261781) and `DIAGONAL_FIXTURE` (15 terms of A261784) lists in `code/01-two-poisson-verify.py` are transcriptions from the OEIS entries. OEIS content is licensed **CC BY-SA 4.0, not MIT-0**; these fixtures are third-party data used only as validation targets. `data/01-two-poisson-a261784_exact.txt` is computed by the program, not copied from the b-file. No full-text paper is included (the Munarini–Poneti–Rinaldi PDF that the intake read is not in the repository).
- **The OEIS update draft is NOT submitted.** `data/01-two-poisson-OEIS_updates_draft.txt` is manuscript 01's draft, marked "DRAFT ONLY -- NOT SUBMITTED" by its author; nothing was submitted by the manuscript or by this report. Its A261781 text says the statements "prove the two claims labeled conjectures"; before any use it must cite Munarini–Poneti–Rinaldi Proposition 25 and Remark 26 and be narrowed to minimality and strict monotonicity (Section 22 of the article). The file is kept byte-identical.

## Building

From a scratch directory holding a copy of `article.tex` and of the report's `data/` and `figures/` directories (the article reads three table bodies from `data/` and two figures from `figures/`), run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 55 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations and no overfull or underfull boxes. Copy back only `article.pdf`. Manuscript 06's delivered PDF built cleanly in the same way (31 pages).

## Rerunning the programs

**Never run the programs in the report directory.** Both packages import their siblings by the delivered names (`06-hankel-make_figures.py` does `from verify import …`; `01-two-poisson-ray_spotchecks.py` does `import verify`), so under the shipped names they fail; and both write **unprefixed** outputs relative to the directory above their own (`data/` and `figures/` for 06, `results/` and `figures/` for 01), which in place would create unprefixed duplicates inside the report. Restore the delivered names in a scratch directory:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions

# manuscript 06
W=$(mktemp -d); mkdir -p "$W/code"
cp "$R/code/06-hankel-verify.py" "$W/code/verify.py"
cp "$R/code/06-hankel-make_figures.py" "$W/code/make_figures.py"
cd "$W"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py --output-root out
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 --with matplotlib==3.10.8 python code/make_figures.py --output-root out
# compare out/data/X with $R/data/06-hankel-X and out/figures/coupon_window.* with $R/figures/06-hankel-coupon_window.*

# manuscript 01
W=$(mktemp -d); mkdir -p "$W/scripts" "$W/results" "$W/figures"
for f in verify make_tables make_figures ray_spotchecks; do cp "$R/code/01-two-poisson-$f.py" "$W/scripts/$f.py"; done
cd "$W"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python scripts/verify.py --max-m 200
py scripts/make_tables.py                     # needs verify.py --max-m 200 or larger first
uv run --no-project --with matplotlib==3.10.8 python scripts/make_figures.py
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python scripts/ray_spotchecks.py
# compare results/X with $R/data/01-two-poisson-X and figures/* with $R/figures/01-two-poisson-*
```

Run times at the intake (Windows, loaded machine; Python 3.13.5 for 06): 06's `verify.py` about 5 s of Python time (22 s with `uv` start-up) and `make_figures.py` about 74 s, against the 0.3 s and 2.3 s of its delivered README; 01's `verify.py --max-m 200` 162 s and `ray_spotchecks.py` 207 s, against "approximately 16 seconds". On Windows the regenerated text files are CRLF where the shipped JSON, TXT and TEX files are LF, so compare ignoring line endings (the CSV files are CRLF on both sides). Receipts differ in `elapsed_seconds` and, for 06, in the recorded Python version.

## Checks by the intake

- Both suites were rerun on copies. 06: status PASS; all six CSV files byte-identical; five JSON files equal apart from CRLF; `verification_summary.json` different only in Python version and elapsed time; the PNG figure pixel-identical (0 of 1,361,976 pixels), the PDF figure identical apart from `/CreationDate`. 01: ALL CHECKS PASSED; outputs byte-identical or equal apart from CRLF and elapsed time; stdout equal apart from elapsed time and the delivery path; `ray_spotchecks.py` CSV byte-identical; the PNG figure pixel-identical; `SHA256SUMS.txt` 25/25.
- Cross-package: 06's `diagonal_constants.json` and 01's `verification.json` agree in every printed digit (about seventy) for r, b, v, d_*, c_*, β₁ and β₂; the coverage probabilities at k = 20, n = 60 agree.
- By hand or by a short computation: Proposition 25 and Remark 26 in the published paper (printed page 16); the impulse of Remark 2.4 at k = 1, 2; H_{3,s}(u) = 27u^{14}(1+u)^{3s+5}(1+2u)², H_{2,1}(1) = 8, H_{3,1}(1) = 62208; the constants of Theorem 4.1 and the comparison in Remark 4.2 (manuscript 01's bound is sharper exactly for k ≤ 4); the moments in Corollary 7.5; the increment expansion (2.11); the cumulant recursion at j = 3; P₃ numerically (n³ times the remainder at w = 1.3 is −0.22070, −0.22010, −0.21981 for n = 400, 800, 1600, against P₃(1.3) = −0.21951).

These checks do not replace an independent review of the proofs. No mathematical error was found.

## Disclosures and discrepancies

- **Delivery wording in shipped files.** `06-hankel-SOURCE_AUDIT.txt`, `code/06-hankel-*.py` (docstrings: `python3 code/verify.py`), `data/06-hankel-figure_generation_summary.json` (`code/make_figures.py`, `figures/coupon_window.*`), `01-two-poisson-provenance-SOURCES.md` (`results/a261784_exact.txt`), `code/01-two-poisson-*.py` (`scripts/`, `results/`) and `data/01-two-poisson-OEIS_updates_draft.txt` ("the accompanying manuscript") use the delivery names. `data/01-two-poisson-verification_stdout.txt` and `data/01-two-poisson-ray_spotchecks_stdout.txt` record the delivery path `/mnt/data/matrix_compositions_research/…`. `data/01-two-poisson-document_qa.json` is manuscript 01's quality record of its own 22-page PDF, not of this build. Manuscript 06's numerics section uses its delivery names; a bracketed note there gives the shipped ones.
- **Stale repository sentences.** Manuscript 06's "Searches for A261780, A261781, and A261784 found no indexed matching report" and manuscript 01's "Indexed searches for A261781 and A261784 returned no matches" describe the search index at `ce37e13f4`, before either manuscript arrived; this report is now that match. Bracketed notes in Sections 1.3 and 11.1 say so and add the neighbours both missed (a260700, `q2:thm:fubini`, the Lean Fubini declarations, and for 01 the inversion apparatus).
- **Louchard.** Manuscript 01 says Louchard's 2008 paper "could not be retrieved"; manuscript 06 retrieved the author's long version (publication list item 99) and inspected it. The intake confirmed the listing but did not read the paper.
- **Dates.** Manuscript 06's figure PDF records `/CreationDate` with a −04:00 offset although its article is dated "Pacific time"; cosmetic.
- **Run times and requirements.** Both delivered READMEs promise run times far below those measured (above). Manuscript 01's README omits that `ray_spotchecks.py` needs SymPy (it imports `verify`). Manuscript 01's README says it was tested with Python 3.13; manuscript 06's receipts record Python 3.12.14.
- **Edited text.** `article.tex` is manuscript 06's text with: the label prefix; a second author and date line, a subtitle line and the PDF metadata; the editorial note after the abstract; the Part I and Part II headings; Section 1.5 (the notation dictionary); Remarks 2.3, 4.2 and 7.3; bracketed notes marked "[Added 3 October 2026, batch 85B]" in Sections 1.3, 2, 5, 7, 9 and 10; the figure path; `\usepackage[hyphens]{url}` (for long repository paths) and a `\tableinput` macro; Part II; Appendix A (provenance and editorial notes); and five bibliography entries. No delivered sentence of manuscript 06 was changed or removed. Manuscript 01's text is restated in manuscript 06's letters, with some proofs condensed; none of its statements was strengthened.

## Provenance

Appendix A of the article records both sources, their pins, why manuscript 06 is the base, where the merge had to choose and what the write changed. The placement commit `fa2f3e419` records the placement decisions: both manuscripts prove the same core theorems in independent texts, so they were merged into one new report; manuscript 06 is the base because on every shared theorem it has the weaker hypotheses or the more general statement (every column weight u > 0; a pole bound uniform in k; the whole coverage generating function), and manuscript 01 contributes Part II.
