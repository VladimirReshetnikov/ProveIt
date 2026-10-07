# Matrix Compositions: Exact Spectra, Hankel Products, and Uniform Asymptotics

**OEIS A261781, its empty-row transition, and refined asymptotics for A261784 — Part II: finite spectra, uniform asymptotics, and two Poisson limits — Part III: Cauchy limits, arithmetic atoms, and edge laws for the Hankel zeros — Part IV: packed matrices on the total-weight 2N diagonal: fixed-order asymptotics, controlled inversion, and joint marked limits**

This research report is dated 3 October 2026, with Part III added on 5 October 2026 and Part IV on 6 October 2026. It was built from four sources of ProveIt's incoming-reports intake. Two of batch 85 were written independently of each other on the same subject: manuscript 06 (Part I, the base) and manuscript 01 (Part II). Manuscript 08 of batch 98 (Part III) was written against Parts I and II and answers Part I's Research question 7 on the zeros of the Hankel determinant. Report 169 of a session bundle of research reports (Part IV, batch 108), written without sight of this report, proves some of its A261784 results again by a different route and adds an expansion with two complex markers and a Poisson law of repeated cells; its author line and PDF author field are empty. Manuscripts 06 and 08 have the author line and PDF metadata "OpenAI ChatGPT" (06 adds "Research prepared for Vladimir Reshetnikov"); manuscript 01's title page and PDF metadata read "Research report prepared for Vladimir Reshetnikov" and name no author or tool.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | batch 85, no. 06 | `Matrix_Compositions_Uniform_Asymptotics.zip` (21 files; main file `matrix_compositions.tex`, 2,078 lines, 100 labels; 31-page PDF *Matrix Compositions: Exact Spectra, Hankel Products, and Uniform Asymptotics*) | `ce37e13f4` (the repository search index it saw) | `345284ac8` | `fa2f3e419` | Part I (Sections 1–10); files prefixed `06-hankel-` |
| addition | batch 85, no. 01 | `OEIS_Matrix_Compositions_Research.zip` (26 files in `matrix_compositions_research/`; main file `matrix_compositions.tex`, 1,561 lines, 98 labels; 22-page PDF *Matrix compositions: finite spectra, uniform asymptotics, and two Poisson limits*) | `d68b65ea0` (tree revision; its search index exposed `ce37e13f4`) | `317c1ce2e` | `fa2f3e419` | Part II (Sections 11–22) and notes in Part I; files prefixed `01-two-poisson-` |
| addition | batch 98, no. 08 | `a261781_hankel_zero_laws.zip` (30 files in `a261781_hankel_zero_laws/`; main file `a261781_hankel_zero_laws.tex`, 2,041 lines, 110 labels; 29-page PDF *Cauchy Limits, Arithmetic Atoms, and Edge Laws for Matrix-Composition Hankel Zeros*) | `d18416ec7` (this report as it stood, Parts I–II) | `2172df76a` | `0fba5167f` | Part III (Sections 23–33) and dated notes in Part I; files prefixed `07-zero-laws-` |
| addition | bundle Report 169 (batch 108) | `Packed_Matrices_Asymptotics_Inverses_and_Joint_Limits_Source.zip` (571,859 bytes; 27 files in `report169/`; main file `source/report169.tex`, 686 lines, 60 labels; 16-page PDF *Report 169: Packed matrices on the total-weight 2n diagonal*) | none (it names no ProveIt commit and cites nothing in the repository) | `60f54ea06` | `602e5bd0f` | Part IV (Sections 34–44) and dated notes in Parts I and II; files prefixed `08-packed-` |

Manuscript 08 arrived on 5 October 2026 in `2172df76a` and was placed by `0fba5167f` (batch 98B), which deleted its archive from `docs/incoming`; it survives in its arrival commit (`git show 2172df76a:docs/incoming/a261781_hankel_zero_laws.zip`). The report's text did not change between its pin and the batch-98 write. It is a continuation, not an edition: 1.25 % of its word 8-grams occur in this report and 0.50 % of the report's in it.

Report 169 arrived on 5 October 2026 in `60f54ea06` with the rest of its bundle and was placed by `602e5bd0f` (batch 108), which deleted its archive from `docs/incoming`; it survives in its arrival commit (`git show 60f54ea06:docs/incoming/Packed_Matrices_Asymptotics_Inverses_and_Joint_Limits_Source.zip`). It is dated 3 October 2026, the day Parts I and II were written, and cites neither: 0.66 % of its word 8-grams occur in this report and 0.13 % of the report's in it. Its checksum ledger matched 26 of 26 files at the intake.

Manuscript 01 arrived with the rest of batch 85 in `317c1ce2e` (2026-10-03 17:53 −0700); the batch-85A placement `713149ded` held it back, because manuscript 06 had arrived thirteen minutes later in `345284ac8` on the same theorems. Both pins are ancestors of the placement. The two texts share 0.7 % (01 in 06) and 0.5 % (06 in 01) of their word 8-grams, almost all bibliography entries, and permute their Greek letters; neither is an edition of the other. The placement commit `fa2f3e419` deleted both archives from `docs/incoming`; they survive in their arrival commits (`git show 345284ac8:docs/incoming/Matrix_Compositions_Uniform_Asymptotics.zip`, `git show 317c1ce2e:docs/incoming/OEIS_Matrix_Compositions_Research.zip`).

**Status: AI-assisted, unrefereed, not formalized.** The intake reran all three packages on copies and spot-checked the mathematics (see "Checks by the intake"). It did not re-derive every proof.

## Files

```
README.md                                   this guide (replaces the three delivered READMEs)
article.tex                                 the merged report (LaTeX, internal bibliography)
article.pdf                                 the compiled report, 116 pages
06-hankel-SOURCE_AUDIT.txt                  (06) its bounded source and contribution audit, as delivered
01-two-poisson-provenance-SOURCES.md        (01) its sources and bounded priority audit, as delivered
07-zero-laws-PROVENANCE.md                  (08) its sources and contribution boundary, as delivered
08-packed-companion-README.md               (169) its companion's delivered guide (commands assume the delivered layout)
code/06-hankel-verify.py                    (06) exact enumeration, recurrence, Hankel and impulse checks; coupon and diagonal diagnostics (SymPy, mpmath)
code/06-hankel-make_figures.py              (06) the coupon-window figure and its curve data (matplotlib; imports verify)
code/01-two-poisson-verify.py               (01) exact identities, kernel polynomials, constants, a(0..200) and the CSV/table outputs (SymPy, mpmath)
code/01-two-poisson-make_tables.py          (01) LaTeX table bodies from the CSV files (standard library)
code/01-two-poisson-make_figures.py         (01) the A261784 error figure (matplotlib)
code/01-two-poisson-ray_spotchecks.py       (01) optional saddle-formula checks at n/k = 3/2, 3, 5 (imports verify, so needs SymPy too)
code/07-zero-laws-reproduce.py              (08) determinant, multiplicity, CDF, tail and moment checks; all its data and figures (SymPy, mpmath, NumPy, matplotlib)
code/07-zero-laws-README.txt                (08) its delivered guide to the program, data and figures
code/07-zero-laws-build.sh                  (08) its LaTeX build script, for the delivered .tex (not shipped)
code/08-packed-companion-packed_matrix.py   (169) exact counts by two routes, marked polynomials, β₀..β₃ by the Morse/Lagrange formula, uncertified diagnostics (standard library)
code/08-packed-companion-run_companion.py   (169) its command-line interface (imports packed_matrix)
code/08-packed-companion-test_companion.py  (169) 19 unit tests (imports packed_matrix)
code/08-packed-companion-verify_symbolic.py (169) optional check of the four frozen rational functions over ℚ(q, R) (SymPy)
code/08-packed-build_pdf.py                 (169) its POSIX PDF build of the delivered source/report169.tex (not shipped)
code/08-packed-build_archive.py             (169) its POSIX ZIP build of the delivered package (needs unshipped files)
code/08-packed-release_tools.py             (169) descriptor-pinned POSIX file helpers of the two build scripts
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
data/07-zero-laws-determinant_checks.csv    (08) symbolic, rational and algebraic determinant checks
data/07-zero-laws-degree_checks.csv         (08) three exact expressions for the reduced degree
data/07-zero-laws-cotangent_identity_checks.csv (08) 70-digit finite cotangent identity checks
data/07-zero-laws-tail_count_checks.csv     (08) independent root-tail counts
data/07-zero-laws-exact_CDF_discrepancies.csv (08) full-support exact Kolmogorov discrepancies (Table 14)
data/07-zero-laws-scaled_moments.csv        (08) exact normalized p = 2, 4 moments
data/07-zero-laws-first_absolute_moment.csv (08) first absolute moments (Table 15; long-double sums, see below)
data/07-zero-laws-fixed_order_multiplicities.csv (08) fixed-order multiplicity ratios (Figure 4)
data/07-zero-laws-primitive_multiplicities.csv (08) all primitive multiplicities E_m(k) (field M_k_m) at table values of k
data/07-zero-laws-full_zero_measure_weights.csv (08) masses at 0, -1 and of the reduced zeros for several shifts
data/07-zero-laws-edge_tail_grid.csv        (08) integer masses and edge curves of Figure 5
data/07-zero-laws-verification_summary.json (08) its run receipt: check counts, constants, versions, scope, limitations
data/07-zero-laws-verification_summary.txt  (08) the same as text
data/07-zero-laws-pdf_validation.json       (08) an external PyMuPDF rendering record of its four figure PDFs (not produced by the program)
data/07-zero-laws-requirements.txt          (08) sympy==1.14.0, mpmath==1.3.0, numpy==2.3.5, matplotlib==3.10.8
data/08-packed-companion-coefficient_formulas.txt (169) β₀..β₃ (its C0–C3) as exact rational functions of q = r/2 and R = log 2
data/08-packed-companion-frozen-coefficients_C0_C3.json (169) the same in a sparse encoding (read by the programs)
data/08-packed-companion-frozen-oeis_A261784.json (169) the 15 OEIS terms a_0..a_14 with source and retrieval date (third-party, CC BY-SA 4.0)
data/08-packed-companion-examples-counts_exact.json (169) the prefix and both counting routes at N = 20, 50, 100
data/08-packed-companion-examples-marked_exact.json (169) the marked polynomials T_N(ω,u), N ≤ 4, by transform and by enumeration
data/08-packed-companion-examples-coefficients_exact_checks.json (169) the coefficient formula against the frozen expressions at 12 rational points
data/08-packed-companion-examples-diagnostics_uncertified.json (169) UNCERTIFIED residuals and inverse errors, N = 10, 20, 50, 100
data/08-packed-companion-examples-manifest.json (169) SHA-256 of the four example files under their delivered names
data/08-packed-companion-symbolic_checks-symbolic_checks.json (169) result of verify_symbolic.py (SymPy 1.14.0)
data/08-packed-companion-symbolic_checks-manifest.json (169) its SHA-256 manifest (delivered name)
data/08-packed-companion-optional_large_run-diagnostics_uncertified.json (169) UNCERTIFIED N = 800 diagnostics with the 4,838-digit count
data/08-packed-companion-optional_large_run-manifest.json (169) its SHA-256 manifest (delivered name)
data/08-packed-companion-provenance.json    (169) source locations and attribution
data/08-packed-companion-requirements-optional.txt (169) sympy==1.14.0, mpmath==1.3.0 (the optional verifier only)
data/08-packed-sources.json                 (169) its 15 inspected public sources with hashes and review scope (none shipped)
figures/06-hankel-coupon_window.pdf         (06) Figure 1 (used by the article)
figures/06-hankel-coupon_window.png         (06) the same at 220 dpi
figures/01-two-poisson-a261784_errors.pdf   (01) Figure 2 (used by the article)
figures/01-two-poisson-a261784_errors.png   (01) the same as PNG
figures/07-zero-laws-central_cdf.pdf        (08) Figure 3 (used by the article)
figures/07-zero-laws-fixed_order_multiplicities.pdf (08) Figure 4 (used by the article)
figures/07-zero-laws-edge_tail.pdf          (08) Figure 5 (used by the article)
figures/07-zero-laws-discrepancy_moments.pdf (08) Figure 6 (used by the article)
figures/07-zero-laws-central_cdf.png        (08) Figure 3 at 300 dpi
figures/07-zero-laws-fixed_order_multiplicities.png (08) Figure 4 at 300 dpi
figures/07-zero-laws-edge_tail.png          (08) Figure 5 at 300 dpi
figures/07-zero-laws-discrepancy_moments.png (08) Figure 6 at 300 dpi
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. `article.tex` is manuscript 06's `matrix_compositions.tex` with the edits listed under "Edited text"; `article.pdf` is a build of it, not any delivered PDF. Twenty-one CSV files (all six of 06's, all four of 01's and all eleven of 08's) are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`.

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

| Delivered (08, inside `a261781_hankel_zero_laws/`) | Shipped |
|---|---|
| `a261781_hankel_zero_laws.tex` | merged as Part III of `article.tex` |
| `PROVENANCE.md` | `07-zero-laws-PROVENANCE.md` |
| `code/reproduce.py`, `code/README.txt`, `build.sh` | `code/07-zero-laws-reproduce.py`, `code/07-zero-laws-README.txt`, `code/07-zero-laws-build.sh` |
| `requirements.txt` | `data/07-zero-laws-requirements.txt` |
| `data/X` (14 files) | `data/07-zero-laws-X` |
| `figures/X.{pdf,png}` (4 pairs) | `figures/07-zero-laws-X.{pdf,png}` |

| Delivered (169, inside `report169/`) | Shipped |
|---|---|
| `source/report169.tex` | merged as Part IV of `article.tex` |
| `companion/README.md` | `08-packed-companion-README.md` |
| `companion/X.py` (4 files: `packed_matrix`, `run_companion`, `test_companion`, `verify_symbolic`) | `code/08-packed-companion-X.py` |
| `build_pdf.py`, `build_archive.py`, `release_tools.py` | `code/08-packed-X.py` |
| `companion/coefficient_formulas.txt`, `companion/provenance.json`, `companion/requirements-optional.txt` | `data/08-packed-companion-X` |
| `companion/D/X.json` (D one of `examples`, `frozen`, `optional_large_run`, `symbolic_checks`; 10 files) | `data/08-packed-companion-D-X.json` |
| `sources.json` | `data/08-packed-sources.json` |

**Not shipped** (they survive in the arrival commits): the three delivered PDFs (replaced by a build of the merged text); manuscript 01's `matrix_compositions.tex` (merged as Part II) and `README.md` (replaced by this README); manuscript 06's `README.txt` (staged by the placement as `README.md`, now replaced); manuscript 08's `a261781_hankel_zero_laws.tex` (merged as Part III) and `README.md` (replaced by this README); manuscript 01's checksum ledger `SHA256SUMS.txt` (25/25 verified at the intake, then retired). Manuscripts 06 and 08 have no checksum ledger. Report 169's `report169.pdf` (replaced by the build), `source/report169.tex` (merged as Part IV), `README.md` (replaced by this README) and `SHA256SUMS` (26/26 verified at the intake, then retired) are not shipped. Manuscript 08's `requirements.txt` is byte for byte a generic file of an unrelated report in the Fabius tree (`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Fabius_Stein_Koopman_Frontier_Report/requirements.txt`); it is shipped with the prefix all the same.

## Labels and numbering

The report's labels carry the prefix `mxc:`. Manuscript 06's 100 labels were given the prefix before anything cited them, and every reference was updated; the write added nine more `mxc:` labels (the Part I heading, the notation dictionary section and table, Remarks 2.3, 4.2 and 7.3, equations (2.8) and (4.4), and Appendix A). Part II's 64 labels carry the sub-prefix `mxc:tp:`. Part III's 115 labels carry the sub-prefix `mxc:hz:` (added 5 October 2026, batch 98): manuscript 08's labels are printed as `mxc:hz:` followed by the delivered name (its Section 6 labels keep their own `ar:`, as in `mxc:hz:ar:cor:sharp`), except those of its Section 2, which is not reprinted; the write added labels for the Part, its front sections, tables and research questions. Part IV's 79 labels carry the sub-prefix `mxc:pm:` (added 6 October 2026, batch 108): Report 169's 60 labels are printed as `mxc:pm:` followed by the delivered name, and the write added 19 (the Part, five sections, two tables, five research questions and six remarks of the write). In all **367** labels; there are no duplicates, and the batch-98 and batch-108 writes renamed, removed or renumbered none of the earlier ones (173 before batch 98, 288 before batch 108; compared in the `.aux` files). Part III follows Part II as Sections 23–33, Tables 9–15, Figures 3–6 and Research questions 9–16, and Part IV follows as Sections 34–44, Tables 16–17 and Research questions 17–21, so no earlier number changed. Part II follows manuscript 06's last section as Sections 11–22, Tables 5–8 and Figure 2. The three inserted remarks shift some numbers of Sections 2, 4 and 7 relative to manuscript 06's delivered PDF (for example its Remark 2.3 on the initial impulse is now Remark 2.4, and its Corollary 7.3 for A261784 is now Corollary 7.4).

## Notation

The two manuscripts permute three Greek letters: manuscript 06's η (the Poisson mean k e^{−n/k}), λ (the ratio n/k on compact rays) and ρ (the pole-bound ratio L/√(L²+8)) are manuscript 01's λ, ρ and η. Its saddle r is 01's τ, its v = Lr/2 is 01's μ, and 01's "β₁" is β₁ + 1/6, not manuscript 06's β₁. **The whole report is printed in manuscript 06's letters**; Table 2 (Section 1.5) lists every renamed symbol of manuscript 01 with the false reading the old letter would have. No normalization was changed. Manuscript 06's own overloaded letters (D, d, c, b, P_j, E, r, v, m) are kept and listed in Appendix A.

Manuscript 08 (Part III) collides with Parts I and II in about thirty letters, among them ν_k (its zero measure; Part I's ν_k = E M), M (Part I's zero-row count) and M_p, D_k, d_k and c_k (the growth constants), Δ_k (the Stirling defect), γ, Λ, L = log 2, ρ, τ and σ. Part III renames every one of them (Table 10, Section 23.3): its colliding Latin objects are written in sans-serif (R_k, D_k, E_m(k), A_k, B_{k,s}, C_k, U_q, M_p, …), its zero measures carry a superscript z (ρ^z_k, ν^z_k, μ^z_{k,s}), its binomial c_k is Section 3's unindexed c, and its Euler and von Mangoldt symbols become γ_E and Λ_vM. Renames are changes of letter only. Its four figures are delivered files and keep its letters; their captions translate them (the edge figure's "E(x)" is the two-sided limit 2Ξ(x)).

Report 169 (Part IV) writes n for the number of rows, ρ for log 2, t for the saddle, C_j for the corrections, h_j for the logarithmic coefficients, and u, v for its markers of cells with entry ≥ 2 and of columns. **Part IV is printed in the letters of Parts I and II** (Table 17, Section 34.3): N rows and total 2N, L = log 2, the saddle r, β_j and β̃_j (β̃₁ is Part II's), the column weight u, a new marker ω for the cells ≥ 2, and Part II's inverse core Λ, ϖ, x₀; its λ = ρt is written Lr (= 2v), its σ² is 2σ_∞², its b is b_Q = 2(r − 1)/(2 − r) (Part I's b at λ = 2 is 2(r − 1)), its ordered Bell numbers are 𝖥_j, its poles L^{(ℓ)}, and objects colliding with Parts I–III are in sans-serif or fraktur type (𝖧_N, 𝖳_N(ω,u), 𝔎_N, 𝔄, 𝔥_j, 𝔭_j, 𝔉_j). About forty renames, changes of letter only.

## What is claimed

**Part I** (manuscript 06; every statement for column weight u > 0 unless restricted):

- **Minimal recurrence and spectrum** (Theorem 2.2): the reduced denominator of column k is ∏_{j≤k}((1+u)(1−z)^j − u), so the minimal eventual constant-coefficient recurrence has order exactly k(k+1)/2, over ℂ; all roots simple and nonzero. The exact initial impulse (Remark 2.4): the recurrence starts at n = D + 1, with Σ q_i T(D−i, k) = (−1)^{k+D} 2^{k−1}.
- the growth-constant limit d_{k+1} − d_k → 1/log 2 with expansions of d_k, c_k and of the increment (Corollary 2.5).
- **Maximal Hankel determinant** (Theorem 3.1): H_{k,s}(u) as an explicit product in ℤ[u] (root products, discriminants, resultants), rank exactly k(k+1)/2, the initial exceptional determinant, coefficientwise positivity, and all other zeros on Re u = −1/2. (5 October 2026, batch 98: Part III gives their multiplicities and their limiting law; see below.)
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

**Part III** (manuscript 08 of batch 98, added 5 October 2026; column weight u, the zeros of H_{k,s}(u) of Theorem 3.1). It **answers Part I's Research question 7**, "The limiting distribution of determinant zeros". Its Section 2 re-derives Theorem 3.1 by the same argument and is printed only as a pointer (Remark 24.4), with its new small cases H_{1,s} = u(1+u)^{s−1} and H_{2,s} = 2u^5(1+u)^{2s}. New:

- **cyclotomic multiplicities** (Section 25): R_k(u) = ∏_{m=2}^{k−1} Φ_m(1+u, u)^{E_m(k)} with E_m(k) = 2Σ_{i<j, m | q_ij} gcd(i,j), q_ij = (j−i)/gcd(i,j); every order 2 ≤ m ≤ k−1 occurs; the reduced degree is D_k = 2(C(k+1,3) − G_k) = k³/3 − k² log k/ζ(2) + O(k²), with G_k = Σ_{i<j} gcd(i,j); and **E_m(k) = k² log k/(ζ(2)ψ(m)) + O(k²)** with an absolute constant, uniformly in m (Proposition 25.2; ψ is Dedekind's function);
- **the bulk law** (Theorem 24.1, Section 26): the reduced zeros, normalized by D_k, converge to −1/2 + iY with Y Cauchy of scale 1/2 (density 2/(π(1+4y²))), with the elementary bound 2G_k/D_k on the Kolmogorov distance, and the **sharp constant**: the distance is ∼ (9/π²)(log k)/k (Corollary 28.3), via pointwise arithmetic corrections at irrational, rational and moving angles (Theorems 28.1, 28.2) and a harmonic sawtooth lemma (Lemma 28.5);
- the first correction for smooth statistics, a factor 1 + (3/ζ(2))(log k)/k (Theorem 27.1);
- **the edge law** (Theorem 29.2): k·ν_k((kx, ∞)) → Ξ(x) = (3/ζ(2)) Σ_n σ_{−1}(n)(1 − 2πnx)²₊ uniformly for x ≥ ε with error O(log k/k); the edge density, the jumps of Ξ'' that recover the divisor sums, and the exact extreme zeros −1/2 ± (i/2)cot(π/(k−1)), each double (Proposition 29.3);
- the expansion of Ξ at 0 with its constant, a uniform transition formula for every height, and Cauchy tails 1/(2πy_k) for every y_k → ∞ with y_k = o(k) (Theorems 30.1, 30.2, Corollary 30.3);
- **the moment transition** (Theorem 24.2, Section 31): convergence of the p-th absolute moment for 0 < p < 1; M_1(k) = (log k + γ − log π − 5/6 + ζ'(2)/ζ(2))/π + O(log²k/k); M_p(k) ∼ 12ζ(p)ζ(p+1)k^{p−1}/((2π)^p(p+1)(p+2)ζ(2)) for p > 1; an exact formula for M_2;
- **the full-degree limit** (Theorem 24.3): with the factors at 0 and −1 kept and s/k² → ϰ, the zero measure tends to the mixture (1/(3(1+ϰ)))δ_0 + ((1+3ϰ)/(3(1+ϰ)))δ_{−1} + (1/(3(1+ϰ))) Cauchy, and to δ_{−1} if s/k² → ∞;
- exact checks and finite data (Section 32: Tables 13–15, Figures 3–6) and eight research questions (Section 33, Research questions 9–16).

**Part IV** (Report 169 of batch 108, added 6 October 2026; the diagonal a_N = T(2N, N), A261784). It answers no question of this report. **Second routes** (printed in full, because its marked theorem reuses the proofs, with remarks identifying them): the expansion of a_N to every fixed order (Theorem 35.1 = Corollaries 7.4 and 17.1; its closed form of β₁ is Corollary 7.4's β as the same rational function of independent L and r; its β₂, β₃ equal Part II's to 10⁻⁵⁰), the transform (= (2.4), Munarini–Poneti–Rinaldi), the column mean and variance at n/k = 2 (Theorem 41.1 = Corollary 7.5, identical formulas), the first inverse correction and the integer brackets (Proposition 39.1, Theorem 39.2 = Propositions 18.1, 18.2). New:

- an explicit pole-tail bound Σ_{ℓ≠0}(L/|L + 2πiℓ|)^{N+1} (Lemma 36.1) and a Morse/Lagrange finite formula for every β_m, with exact rational expressions for β₂, β₃ in ℚ(L, r) (Section 38);
- the inversion two terms further: with β̃₂ = β₂ − β₁²/2 and β̃₃ = β₃ − β₁β₂ + β₁³/3 − 1/180, the x₀^{−2} and x₀^{−3} terms with error O(x₀^{−4}/(1+ϖ)) (Proposition 39.1; the write shows it holds for Part II's root x_J(Y), J ≥ 3, Remark 39.3);
- **a complex-uniform two-marker expansion** (Theorem 40.1): T_N(ω,u)/(c_*(ω,u) d_*(u)^N (N!)²/N) has an expansion to every fixed order uniformly on |ω − 1| ≤ 2.1, |u − 1| ≤ 0.02, ω marking cells with entry ≥ 2 and u columns, with c_*(ω,u) = e^{L_u r(ω−1/2)}/(2π(1+u)L_u√(r−1)) and an explicit pole-tail base < 0.83;
- **the repeated cells are Poisson(Lr), Lr = 1.1046161627…, jointly with and independent of the Gaussian column count** (Theorem 41.1); the same joint limit for the total excess, and E(cells ≥ 3) = (Lr)²/(2N) + O(N^{−2}) (Section 41.1);
- dated notes: it **bears on** Part II's question "A combinatorial realization of the latent defect" (the repeated-cell count is a statistic of the matrices whose generating function carries e^{Lr(ω−1/2)}, so weighting each such cell by 1/2 removes the factor e^{Lr/2} from the amplitude; its mean Lr is twice the defect's; no relation to the defect and no decorated construction is claimed, so the question stays open), and it **answers an analogue** of Part II's "Joint laws with the number of columns" (on the single ray n/k = 2, with the repeated-cell count in place of the defect; that count, Poisson(2v), is not a realization of the defect, Poisson(v), so the write's first wording "settles one instance" was corrected after the independent check below); five research questions (Section 44, Research questions 17–21).

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
- The research questions of both manuscripts are proposals, "not assertions that every formulation is open throughout the literature". Two are re-scoped in the text: manuscript 06's Research question 2 is answered for the single event M = 0 by Theorem 13.1, and manuscript 01's question on joint column laws is answered in the coverage window by Theorem 6.2 (open on compact rays jointly with the defect). Since 5 October 2026 (batch 98), manuscript 06's Research question 7 is answered by Part III, with dated notes in the article.

Manuscript 08's own limits (Part III; Section 23 and the places cited there, `07-zero-laws-PROVENANCE.md`, `data/07-zero-laws-verification_summary.*`), kept in full:

- Unrefereed proofs; the computations are independent checks, not proofs of limits and not proof-assistant certificates; no Lean or Rocq formalization and no OEIS submission. No exhaustive priority search; the tools (spectral algebra, Möbius inversion, Fourier approximation, real-variable estimates) are standard and the contribution is the family-specific theorem set. The determinant product is this report's (Theorem 3.1), re-derived and credited; recurrence existence is Munarini–Poneti–Rinaldi's Proposition 25 and is not presented as an OEIS conjecture newly solved.
- The multiplicity estimate has an absolute error, not a uniform relative equivalent for growing m (relative only for ψ(m) = o(log k)). Total-variation distance to the Cauchy law is 1; weak convergence gives no moment convergence. Normalizing the reduced zeros by the full degree gives a subprobability. The smooth correction does not extend to indicators. The sharp constant 9/π² comes with no quantitative error, and the finite data (0.618 at k = 2048) lie far below it. The edge law describes order-k² zeros with multiplicity, not the finitely many largest ones.
- Its unproved items stand in Section 33 ("Further questions and research"): Research questions 9–16 (its questions 1–7 and 9), its question 8 merged into Part I's Research question 5, its explicit unproved candidate for the correction of the fractional moments (the analytic continuation of the constant M_p, Research question 13), its speculation that the last zeros depend on arithmetic features of k (Research question 12), and three numerical observations (the maximizing angle moving from 1/7 to 1/11; the first-moment residual 0.473 at k = 4096; "moment convergence … substantially faster"). None of its claims was found wrong.

Report 169's own limits (Part IV; Sections 34, 35, 39, 41–43 and its delivered README), kept in full:

- Fixed-order asymptotics only: no convergence, optimal truncation or effective thresholds; O-constants and onsets are existential; the threshold constant C_J is existential and no exact ceiling rule is claimed. No local limit theorem for the column count. The coupling of the total excess with the repeated cells says nothing about unbounded moments. Decimal values and the N = 800 diagnostics are UNCERTIFIED.
- The leading equivalent is credited to Kotěšovec (OEIS, 18 February 2017, updated 20 April 2024), the transform to Munarini–Poneti–Rinaldi; Cerbai–Claesson, Cameron–Prellberg–Stark, Louchard and Greenhill–McKay are precedents; "no claim of historical priority or global novelty"; Kotěšovec's mathematics page and the A261784 history were not available to it; exact computation and independent checking are not formal verification or interval arithmetic.
- Its statement that no reviewed source has the combination of all-order diagonal corrections, controlled inversion and marked consequences is true of what it reviewed; this report's Parts I and II, written the same day, have the first two (note in Section 43).
- Its unproved items stand in Section 44: its questions 1, 3, 4, 5 as Research questions 17, 19, 20, 21; its question 2 as Research question 18, re-scoped because Theorem 7.1 answers its unmarked form (dated note at Research question 1); its question 6 printed once, in Part II's paragraph "Beyond all algebraic orders". The fourth coefficient near 0.0043 suggested by the N = 800 diagnostic is an observation, not a claim. None of its claims was found wrong.

## Relation to neighbouring material and formal status

- **Method neighbour** [`a260700-parabolic-double-cosets`](../a260700-parabolic-double-cosets/) (prefix `pdc:`): the same two devices, a uniform extraction of the Fubini pole at log 2 (its section `pdc:sec:poles`) followed by an outer Stirling transform (`pdc:sec:outer`), for a different sequence; it cites Munarini–Poneti–Rinaldi as related work. No theorem is shared. Manuscript 06 found it in its repository search and assumes nothing from it.
- **Sibling Poisson defect** [`a122399-surjection-diagonal`](../a122399-surjection-diagonal/) (prefix `a122:`), Part II (batch 98): for ordered partitions of an m-set with a map of an n-set to the blocks, the defect m − K tends to Poisson(e^{−c}/2) at n = m(log m + c), with an all-orders Touchard-summed expansion (its Theorems 13.1 and 15.1); its factor 1/2 comes from defects that are pairs (its Proposition 16.1), as a dated note of its batch-98 write, on its source audit, says of the parameter Lr/2 of Theorem 16.2 here (`mxc:tp:thm:defect`). No theorem is shared. [Independent check, 7 October 2026: this bullet and the article's note first said "as its source note says"; the delivered source audit of a122399 does not mention this report. The article's note also first called the defect "the number of missing blocks"; it is m − K. Both corrected with the first wordings kept in the article.] A dated reciprocal note after Theorem 16.2 (added 5 October 2026, batch 98) records the pointer; it adds no label.
- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`: its Theorem `q2:thm:fubini` (exact pole-lattice transseries of the Fubini numbers) has the estimate (7.5) of both manuscripts as its one-pole truncation; its `p0:thm:perturbed-inversion` and `p0:thm:staircase` are the apparatus of which Section 18 is an instance. Manuscript 01 read the volume's overview README at its pin as motivation but cited neither theorem.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report. The only ingredient formalized anywhere in the repository is the Fubini exponential generating function used in Section 7: `Fabius.fubini` (the definition F_n = Σ k! S(n,k)), `Fabius.egfA_fubini` and `Fabius.two_sub_exp_mul_egfA_fubini` ((2 − e^t) Σ F_n t^n/n! = 1), in `Analysis/FabiusFunction/Lean/FabiusFunction/OrderedBell.lean`. Nothing else stated in any Part is formalized; in particular nothing of Parts III and IV. Both batch-85 manuscripts propose the reduced denominator and its no-cancellation proof as a first formalization target (Section 10.1, Section 20), and manuscript 08 extends that stage by the cyclotomic multiplicities, degree identities and full-support CDF comparisons (Research question 16); these are proposals only.
- **Symmetric sibling** [`a138178-symmetric-packed-matrices`](../a138178-symmetric-packed-matrices/) (bundle Report 238, batch 108): symmetric packed matrices (A138178), with the same devices as Part IV (a geometric weighting that erases zero lines, the Fubini pole at log(1 + 1/u), complex-uniform marked expansions, Poisson laws of repeated cells) for a different model (involution saddle, expansion in n^{−1/2}). No theorem is shared; its source notes say the models differ. A reciprocal note there is written separately.
- Apart from that sibling, no other report of the collection treats A261780, A261781 or A261784, and none treats the zeros of Hankel determinants of this family (checked at the batch-98 placement). Part III cites OEIS A001615 (Dedekind ψ) and Tóth's survey of gcd-sum functions for context only.

## Third-party material and the OEIS draft

- **OEIS fixtures.** `data/06-hankel-oeis_rows.json` and the `OEIS_ROWS` list in `code/06-hankel-verify.py` hold the nine rows n = 0..8 of A261781; the `TRIANGLE_FIXTURE` (8 rows of A261781) and `DIAGONAL_FIXTURE` (15 terms of A261784) lists in `code/01-two-poisson-verify.py` are transcriptions from the OEIS entries. OEIS content is licensed **CC BY-SA 4.0, not MIT-0**; these fixtures are third-party data used only as validation targets. `data/01-two-poisson-a261784_exact.txt` is computed by the program, not copied from the b-file. No full-text paper is included (the Munarini–Poneti–Rinaldi PDF that the intake read is not in the repository). `data/08-packed-companion-frozen-oeis_A261784.json` holds the 15 OEIS terms a_0..a_14 of A261784 (third-party, CC BY-SA 4.0; validation targets only); Report 169's `data/08-packed-sources.json` lists hashes of 15 public sources, none of which is shipped. Manuscript 08's package ships no OEIS data: its program builds every row from the counting recurrence, and its data are its own computations.
- **The OEIS update draft is NOT submitted.** `data/01-two-poisson-OEIS_updates_draft.txt` is manuscript 01's draft, marked "DRAFT ONLY -- NOT SUBMITTED" by its author; nothing was submitted by the manuscript or by this report. Its A261781 text says the statements "prove the two claims labeled conjectures"; before any use it must cite Munarini–Poneti–Rinaldi Proposition 25 and Remark 26 and be narrowed to minimality and strict monotonicity (Section 22 of the article). The file is kept byte-identical.

## Building

From a scratch directory holding a copy of `article.tex` and of the report's `data/` and `figures/` directories (the article reads three table bodies from `data/` and six figures from `figures/`), run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 116 pages (115 before the independent check of the batch-98 write on 7 October 2026; also 115 at the Part IV write, before the independent check of 6 October 2026; 89 before Part IV was added on 6 October 2026; 55 before Part III was added; 90 before the batch-98 reciprocal note of 5 October 2026 after Theorem 16.2, which changed the later page breaks), with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations and no overfull or underfull boxes. Copy back only `article.pdf`. Manuscript 06's delivered PDF built cleanly in the same way (31 pages). Manuscript 08's `code/07-zero-laws-build.sh` builds its delivered `.tex`, which is not shipped; it does not build this article. Likewise Report 169's `code/08-packed-build_pdf.py` (POSIX only) builds the unshipped `source/report169.tex`, and `code/08-packed-build_archive.py` rebuilds its delivered ZIP from files that are not all shipped.

## Rerunning the programs

**Never run the programs in the report directory.** The two batch-85 packages import their siblings by the delivered names (`06-hankel-make_figures.py` does `from verify import …`; `01-two-poisson-ray_spotchecks.py` does `import verify`), so under the shipped names they fail; and both write **unprefixed** outputs relative to the directory above their own (`data/` and `figures/` for 06, `results/` and `figures/` for 01), which in place would create unprefixed duplicates inside the report. Restore the delivered names in a scratch directory:

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

# manuscript 08 (writes data/ and figures/ under the directory above code/)
W=$(mktemp -d); mkdir -p "$W/code"
cp "$R/code/07-zero-laws-reproduce.py" "$W/code/reproduce.py"
cd "$W"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 --with numpy==2.3.5 --with matplotlib==3.10.8 python code/reproduce.py
# compare data/X with $R/data/07-zero-laws-X and figures/X with $R/figures/07-zero-laws-X

# Report 169 (the companion reads frozen/ next to packed_matrix.py)
W=$(mktemp -d)/companion; mkdir -p "$W"/{frozen,examples,symbolic_checks,optional_large_run}
for f in packed_matrix run_companion test_companion verify_symbolic; do cp "$R/code/08-packed-companion-$f.py" "$W/$f.py"; done
for d in frozen examples symbolic_checks optional_large_run; do for p in "$R"/data/08-packed-companion-$d-*.json; do cp "$p" "$W/$d/${p##*/08-packed-companion-$d-}"; done; done
cd "$W"
python -m unittest -v; python -O -m unittest -v      # 19 tests; on Windows 2 POSIX output-safety tests error
python run_companion.py generate --output reproduced  # POSIX only; compare reproduced/* with examples/*
uv run --no-project --with sympy==1.14.0 python verify_symbolic.py   # prints the JSON of symbolic_checks/symbolic_checks.json
```

Report 169's companion (added 6 October 2026, batch 108) imports `packed_matrix` by its delivered name and reads `frozen/` beside it, so it runs only on a copy with the delivered layout as above. Its `generate` command writes only a new directory and refuses on Windows (it requires POSIX `O_NOFOLLOW`); on Windows the intake reproduced the four example files byte for byte by calling `packed_matrix.generated_payloads(60)` directly in such a copy. The unit tests take about 2 s; on Windows 17 of 19 pass and the 2 errors are the POSIX output-safety tests. `verify_symbolic.py` reproduces `symbolic_checks.json` apart from line endings. The optional N = 800 run (`python run_companion.py diagnostics 800 --digits 60 --output large_reproduced`, about half a minute in its author's run) and the two POSIX build scripts were not rerun.

Manuscript 08's program (added 5 October 2026, batch 98) writes **unprefixed** files into `data/` and `figures/` under `Path(__file__).parents[1]`; under its shipped name in `code/` it would write them into the report directory, so run it only on a copy as above. It reads no network resource and no OEIS data. It does not write `pdf_validation.json`, which is an external PyMuPDF record (PyMuPDF is neither a dependency nor shipped), so that file cannot be regenerated from the package. Its delivered `code/README.txt` says `python code/reproduce.py` "from the extracted article directory", and the article's own text says `python3 code/reproduce.py`; both mean the delivered layout.

Run times at the intake (Windows, loaded machine; Python 3.13.5 for 06): 06's `verify.py` about 5 s of Python time (22 s with `uv` start-up) and `make_figures.py` about 74 s, against the 0.3 s and 2.3 s of its delivered README; 01's `verify.py --max-m 200` 162 s and `ray_spotchecks.py` 207 s, against "approximately 16 seconds". On Windows the regenerated text files are CRLF where the shipped JSON, TXT and TEX files are LF, so compare ignoring line endings (the CSV files are CRLF on both sides). Receipts differ in `elapsed_seconds` and, for 06, in the recorded Python version. Manuscript 08's program ran in 287 s at the placement and in 45 s at the write (Python 3.13.5, Windows; its delivery records no run time); its JSON receipt differs only in the recorded Python version (3.12.14 delivered) and its text receipt only in line endings. **Long double on Windows:** it sums cotangents in NumPy `longdouble`, which is an extended format on typical x86 Linux builds but plain double on Windows, so on Windows 16 of the 20 data rows of `first_absolute_moment.csv` and 20 of the 4,804 data rows of `edge_tail_grid.csv` differ from the shipped files in the last one or two of seventeen printed digits. The nine-digit values of Table 15 and the figures are unaffected (Remark 32.1). Its Table 15 caption's "extended-precision cotangent summation" and its summary's "exact CSV values are reproducible" are therefore platform-dependent for those two files.

## Checks by the intake

- Both suites were rerun on copies. 06: status PASS; all six CSV files byte-identical; five JSON files equal apart from CRLF; `verification_summary.json` different only in Python version and elapsed time; the PNG figure pixel-identical (0 of 1,361,976 pixels), the PDF figure identical apart from `/CreationDate`. 01: ALL CHECKS PASSED; outputs byte-identical or equal apart from CRLF and elapsed time; stdout equal apart from elapsed time and the delivery path; `ray_spotchecks.py` CSV byte-identical; the PNG figure pixel-identical; `SHA256SUMS.txt` 25/25.
- Cross-package: 06's `diagonal_constants.json` and 01's `verification.json` agree in every printed digit (about seventy) for r, b, v, d_*, c_*, β₁ and β₂; the coverage probabilities at k = 20, n = 60 agree.
- By hand or by a short computation: Proposition 25 and Remark 26 in the published paper (printed page 16); the impulse of Remark 2.4 at k = 1, 2; H_{3,s}(u) = 27u^{14}(1+u)^{3s+5}(1+2u)², H_{2,1}(1) = 8, H_{3,1}(1) = 62208; the constants of Theorem 4.1 and the comparison in Remark 4.2 (manuscript 01's bound is sharper exactly for k ≤ 4); the moments in Corollary 7.5; the increment expansion (2.11); the cumulant recursion at j = 3; P₃ numerically (n³ times the remainder at w = 1.3 is −0.22070, −0.22010, −0.21981 for n = 400, 800, 1600, against P₃(1.3) = −0.21951).

- Part III (batch 98). Manuscript 08's program was rerun on copies at the placement and at the write: exit 0; all counted checks passed (12 symbolic, 96 rational and 3 algebraic determinant checks, 91 degree and multiplicity, 18 root-merging and CDF, 20 tail, 78 cotangent, 18 exact CDF, 2 first-moment, 4 PDF-structure); nine CSV files byte-identical, the other two differing only in last digits (long double, above); the four PNG figures pixel-identical and the four PDF figures identical apart from `/CreationDate`. The placement read every proof of manuscript 08's Sections 3–9 and re-derived by hand, among others, the Euler product for ψ, the smooth-statistic grid bounds, the exact low-range identity and the case analysis of the sharp constant, the tail count and the jump formula, the Bernoulli identity of Theorem 30.1, the full-degree weights, M_2 = ζ(3)/(4π²), M_4 = ζ(5)/(600π²) and the exact M_2 formula. Its own mpmath computation (not shipped) confirmed ∫₁^∞ B₃({v})/v³ dv = (3/2)log 2π − 11/4 to 10⁻¹⁵, and at k = 500 and 1500 gave D_k = 2(C(k+1,3) − G_k) exactly, M_1(k) − (log k)/π = −0.5923 and −0.6107 (limit −0.62733), (k/log k)(F_k(t) − t) = −0.127 and −0.130 at t = √2 − 1 (limit −0.156), and k·ν_k((kx,∞)) = 0.2570 and 0.2545 at x = 0.1 (limit Ξ(0.1) = 0.2520): slow approaches consistent with the proved error terms. The write checked H_{1,s} and H_{2,s}, the uniformity of Proposition 25.2 for m ≥ k (Remark 25.3), the table and figure values against the data files, and every renamed formula against the delivered source.

- Part IV (batch 108). The placement verified Report 169's checksum ledger (26/26), compared its β₁ with Corollary 7.4's β (25 digits) and its column moments with Corollary 7.5 (differences 0 and 2·10⁻⁴⁰), computed E(cells ≥ 2) = 1.0312, 1.0743, 1.0893 at N = 20, 50, 100 from the finite transform (N(Lr − E) = 1.47, 1.52, 1.53, consistent with Lr + O(1/N)), and checked the pole ratio 0.10965, the marked pole-tail base (0.8221; its rational bound 105861/128110 is the value at L = 0.69, π = 3.14) and the inverse series for cells ≥ 3; the companion reran on copies as described above. The write checked, by SymPy, that (35.4) and Corollary 7.4's β are the same rational function of independent L and r; Report 169's exact β₁, β₂, β₃ against Part II's fifty-digit values (< 10⁻⁵⁰); the x₀^{−3} coefficient of (39.4) by hand and the whole expansion numerically; T_1, T_2 (and T_3) by brute-force enumeration; the binary specialization T_N(0,1)/a_N → e^{−Lr} by exact counts at N = 10..40 (0.33486 at N = 40 against 0.33134, with N-scaled deviation 0.425 to 0.433); and every renamed formula against the delivered source.

- **Independent check of the batch-98 write (7 October 2026).** An adversarial check made by the intake after the Part III write (`324818ddb`) and its reciprocal note (`639b038ab`) re-derived every added statement with its own code: provenance facts, the generic requirements blob, the 8-gram shares (1.25 %, 0.50 %, word tokens) and the decimals of the printed text (unchanged from the manuscript) confirmed; H_{1,s}, H_{2,s}, H_{3,s} recomputed as determinants; the Part I note on E_m(k), the atom masses and Remark 25.3 checked by hand; the check's own atom computation (D_k = Σ φ(m) E_m(k) = 2(c − G_k)) reproduces Table 14 (maximizing angle 1/7, then 1/11 or its mirror 10/11), the k = 1024, 2048, 4096 rows of Table 15, the limit −0.6273278444052115 and the placement's values at k = 500 and 1500; I_3 and Ξ(0.05), Ξ(0.1) confirmed; a rerun of manuscript 08's program on a copy confirms Remark 32.1 exactly (16 of 20 and 20 of 4,804 rows; Windows `longdouble` is float64). No mathematical error. Corrected with the first wording kept: the reciprocal note after Theorem 16.2 (the sibling's defect m − K is not "the number of missing blocks"; the pair mechanism is named in a note of that report's write, not in its source note). Added: numerical evidence at p = 1/2 for manuscript 08's fractional-moment candidate (Research question 13: the residual is 2.05 (log k)/√k for k = 500 … 4096). Recorded in Appendix A.

- **Independent check of the Part IV write (6 October 2026).** An adversarial check made by the intake after the write (`ab4e30d32`) re-derived every identification and number: (35.4) minus Corollary 7.4's β simplifies to 0 with L, r independent (SymPy); Report 169's exact β₁, β₂, β₃ at 80 digits differ from Part II's printed fifty-decimal truncations by 6.5·10⁻⁵¹, 9.7·10⁻⁵¹, 1.4·10⁻⁵¹; independently of every route, exact a_N for N ≤ 150 (its own row/column inclusion–exclusion, equal to the transform for N ≤ 8) give N⁴(a_N/(c_* d_*^N (N!)²/N) − 1 − β₁/N − β₂/N² − β₃/N³) = 0.004376, 0.004322, 0.004304 at N = 50, 100, 150 (bounded); the column mean and variance agree with Corollary 7.5 term for term, with exact errors O(1/N); the x₀^{−3} coefficient of (39.4) and Remark 39.3 (ii) were re-derived (at log Y = 10³, 10⁵, 10⁷ the scaled error is −0.00383, −0.00366, −0.00360 with the root of log A^[3] as comparator; the write's figures used another comparator); Lr = 1.10461616271868… = 2v, and the exact binary-packed ratios, E J_N and the second factorial moment for N ≤ 40 are consistent with Poisson(Lr) at rate O(1/N); all 288 earlier labels and every earlier number are unchanged. No mathematical error. Corrected, with the first wordings quoted in the dated note of Section 20, Remark 41.2 and the note of Section 43: "settles one instance" of Part II's "Joint laws with the number of columns" (abstract, front matter, dated note, Remark 41.2) is now "answers an analogue" (the repeated-cell count, Poisson(2v), is not a realization of the defect, Poisson(v)); and Section 43's note credited Part II with "integer brackets at first order", whereas Proposition 18.2 gives them at every fixed order J (only Proposition 18.1's explicit inverse is first order). The check is recorded at the end of the article's appendix.

These checks do not replace an independent review of the proofs. No mathematical error was found.

## Disclosures and discrepancies

- **Delivery wording in shipped files.** `06-hankel-SOURCE_AUDIT.txt`, `code/06-hankel-*.py` (docstrings: `python3 code/verify.py`), `data/06-hankel-figure_generation_summary.json` (`code/make_figures.py`, `figures/coupon_window.*`), `01-two-poisson-provenance-SOURCES.md` (`results/a261784_exact.txt`), `code/01-two-poisson-*.py` (`scripts/`, `results/`) and `data/01-two-poisson-OEIS_updates_draft.txt` ("the accompanying manuscript") use the delivery names. `data/01-two-poisson-verification_stdout.txt` and `data/01-two-poisson-ray_spotchecks_stdout.txt` record the delivery path `/mnt/data/matrix_compositions_research/…`. `data/01-two-poisson-document_qa.json` is manuscript 01's quality record of its own 22-page PDF, not of this build. Manuscript 06's numerics section uses its delivery names; a bracketed note there gives the shipped ones.
- **Stale repository sentences.** Manuscript 06's "Searches for A261780, A261781, and A261784 found no indexed matching report" and manuscript 01's "Indexed searches for A261781 and A261784 returned no matches" describe the search index at `ce37e13f4`, before either manuscript arrived; this report is now that match. Bracketed notes in Sections 1.3 and 11.1 say so and add the neighbours both missed (a260700, `q2:thm:fubini`, the Lean Fubini declarations, and for 01 the inversion apparatus).
- **Louchard.** Manuscript 01 says Louchard's 2008 paper "could not be retrieved"; manuscript 06 retrieved the author's long version (publication list item 99) and inspected it. The intake confirmed the listing but did not read the paper.
- **Dates.** Manuscript 06's figure PDF records `/CreationDate` with a −04:00 offset although its article is dated "Pacific time"; cosmetic.
- **Run times and requirements.** Both delivered READMEs promise run times far below those measured (above). Manuscript 01's README omits that `ray_spotchecks.py` needs SymPy (it imports `verify`). Manuscript 01's README says it was tested with Python 3.13; manuscript 06's receipts record Python 3.12.14.
- **Edited text.** `article.tex` is manuscript 06's text with: the label prefix; a second author and date line, a subtitle line and the PDF metadata; the editorial note after the abstract; the Part I and Part II headings; Section 1.5 (the notation dictionary); Remarks 2.3, 4.2 and 7.3; bracketed notes marked "[Added 3 October 2026, batch 85B]" in Sections 1.3, 2, 5, 7, 9 and 10; the figure path; `\usepackage[hyphens]{url}` (for long repository paths) and a `\tableinput` macro; Part II; Appendix A (provenance and editorial notes); and five bibliography entries. No delivered sentence of manuscript 06 was changed or removed. Manuscript 01's text is restated in manuscript 06's letters, with some proofs condensed; none of its statements was strengthened. The batch-98 write (5 October 2026) added eight preamble macros for Part III's notation, a third title, author and date line and the PDF metadata, a batch-98 editorial note, bracketed notes marked "[Added 5 October 2026, batch 98]" in Sections 1.3, 1.5 and 3 and in Research questions 5 and 7 and "A practical order of attack" of Section 10, Part III (Sections 23–33), four paragraphs of Appendix A and three bibliography entries. Manuscript 08 is printed in full except its Section 2 (a re-proof of Theorem 3.1, printed as the pointer Remark 24.4) and its Section 12 (source audit and package contents, folded into Section 23, Section 32 and Appendix A), with renamed letters and notes of the write; none of its statements was strengthened.
- **Manuscript 08's delivered files.** `code/07-zero-laws-README.txt`, the docstrings and output names of `code/07-zero-laws-reproduce.py`, and `data/07-zero-laws-verification_summary.*` use the delivery names (`code/reproduce.py`, unprefixed `data/` and `figures/`), and use manuscript 08's own letters (the code stores the reduced degree as `N`; the README calls the edge profile `E(x)`, which is the two-sided limit 2Ξ(x)). `code/07-zero-laws-build.sh` builds the unshipped `a261781_hankel_zero_laws.tex`. `07-zero-laws-PROVENANCE.md` speaks of "the article", meaning manuscript 08's own text, in which the product was re-derived; here that re-derivation is a pointer. It also says the statements were cross-checked by "independent mathematical reviews in this session"; those reviews are not part of the package. `data/07-zero-laws-pdf_validation.json` records a PyMuPDF rendering of the figures that the package cannot reproduce (above). Manuscript 08's PDF records `/CreationDate` 4 October 2026 20:00 PDT although the article is dated 5 October; cosmetic. Its delivered text calls the tables "extended precision" and the CSV values "reproducible"; see the long-double note above.
- **Report 169's delivered files.** `08-packed-companion-README.md` gives its commands for the delivered `companion/` directory (`python run_companion.py …`, `frozen/`, `examples/`); `code/08-packed-companion-*.py` import `packed_matrix` and read `frozen/` beside themselves; `data/08-packed-companion-examples-manifest.json`, `…-symbolic_checks-manifest.json` and `…-optional_large_run-manifest.json` hash the files under their delivered names; `code/08-packed-build_pdf.py` and `code/08-packed-build_archive.py` import `release_tools` by its delivered name and need the unshipped `source/report169.tex`, `report169.pdf` and `README.md`, with TeX trees under `/usr/share/…` and `/proc/self/fd` (POSIX only). Its delivered README promises `report169.pdf`, `source/report169.tex` and `SHA256SUMS`, which are not shipped (above). Its text names its markers u, v and its count A_n(u, v); Part IV renames them (Table 17).

## Provenance

Appendix A of the article records both sources, their pins, why manuscript 06 is the base, where the merge had to choose and what the write changed. The placement commit `fa2f3e419` records the placement decisions: both manuscripts prove the same core theorems in independent texts, so they were merged into one new report; manuscript 06 is the base because on every shared theorem it has the weaker hypotheses or the more general statement (every column weight u > 0; a pole bound uniform in k; the whole coverage generating function), and manuscript 01 contributes Part II. The batch-98 placement commit `0fba5167f` placed manuscript 08 as Part III, an addition, because it answers a question this report names (Research question 7); Appendix A's paragraphs "Part III (batch 98)", "Where the batch-98 write had to choose", "What the batch-98 write changed" and "Checks by the intake for Part III" record its source, its pin and the write's choices. The batch-108 placement commit `602e5bd0f` placed Report 169 as Part IV, an addition, because it re-proves this report's A261784 theorems and adds a statistic of the same matrices (it answers no question here); Appendix A's paragraphs "Part IV (batch 108)", "Where the batch-108 write had to choose", "What the batch-108 write changed" and "Checks by the intake for Part IV" record its source and the write's choices.
