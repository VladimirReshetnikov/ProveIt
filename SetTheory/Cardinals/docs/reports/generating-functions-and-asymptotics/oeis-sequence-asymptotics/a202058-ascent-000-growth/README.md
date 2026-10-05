# Ascent Sequences Avoiding 000 (OEIS A202058)

**Factorial growth constant, finer bounds, logarithmic-square growth, the ratio limit and the endpoint laws**

This research report was merged on 2 October 2026 from four manuscripts of
batch 77. All four arrived in commit `096ee7b87` and were placed in
`f76fcb566`. They form one chain, and each cites or bundles the one before it.
On 5 October 2026 a fifth source, bundle Report 97 of batch 102, was written
in as Part V (arrival `60f54ea06`, placement `6ab1f1979`). It cites none of
the four.

| Part | Source | Batch-77 manuscript | Archive (delivered main file, PDF pages) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| I | 1 October report | 37 | `oeis-a202058-report.zip` (`a202058-report.tex`, 9 pp.) | `0870c19bb` | `f76fcb566` | Sections 1–8, equations (1)–(23) |
| II | fine addendum | 36 | `oeis-a202058-fine-report.zip` (`a202058-fine-addendum.tex`, 18 pp.) | `13ef7d939` | `f76fcb566` | Sections 9–20, equations (24)–(69) |
| III | log-square report | 07 | `a202058-lognormal-report.zip` (`a202058-lognormal.tex`, 23 pp.) | `4b874cea0` | `f76fcb566` | Sections 21–32, equations (70)–(150) |
| IV | ratio sequel | 08 | `a202058-ratio-report.zip` (`a202058-ratio.tex`, 14 pp.) | none | `f76fcb566` | Sections 33–41, equations (151)–(209) |
| V | growth-constant report | bundle Report 97 (batch 102) | `A202058_Ascent_Sequence_Growth_Source.zip` (`article.tex` + 9 section files; no PDF delivered, 23 pp. when rebuilt) | none | `6ab1f1979` | Sections 42–49, equations (210)–(285); Section 50 added |

The pins are the ProveIt commits named by each delivery's repository
search. Part I's pin `0870c19bb` is in its literature note
(`37-foundation-literature.md`, line 23), which arrived only inside
manuscript 36. Part II's pin is in `36-fine-literature.md`, line 44. Part
III's pin is printed in its Section 31 and recorded in
`data/07-lognormal-source-audit-public-sources.json`. Manuscript 08 names
no pin and reports no repository search. Report 97 names no pin, does not
mention this repository and did not know Parts I–IV.

Delivered author lines: "A proof and reproducible research report" (37),
"A mathematical addendum with reproducible computations" (36), "A self
contained mathematical and reproducibility report" (07), "A sequel with
complete proofs and reproducibility materials" (08). None names a person
or a tool. Report 97's author line (TeX and PDF metadata) is "Research
report prepared with OpenAI".

**Status.** The report is AI-assisted and unrefereed, and nothing in it is
formalized. Its proofs have been checked only by the reviews and audits
delivered with the manuscripts (shipped below), not by a referee or a
proof assistant.

## What is claimed

Write `T = 3π²/8`, `μ = 1/T = 8/(3π²) = 0.27018982304623405718…`, and
`c_n = a_n T^n / n!`, so that Part II's `h_n = log c_n`.

- **Part I** (Theorem 1.1): the exponential generating function has radius
  `T`, `(a_n/n!)^{1/n} → μ`, and `log c_n = O(n^{9/13}(log n)^3)`.
  Corollary 7.1 gives a threshold inverse with error
  `O(N^{9/13}(log N)^2)`. The constant was conjectured by Conway, Conway,
  Elvey Price and Guttmann (EJC 29(4) P4.25, 2022), whose compacted
  recurrence is the starting point.
- **Part II** (Theorem 9.1, Corollary 9.2):
  `−O(n^{2/3}(log n)^{5/3}) ≤ log c_n ≤ O((log n)^2)`. Hence no equivalent
  `C₀ n! μ^n exp(c n^σ) n^g (log n)^h` with `c, σ > 0` exists. The inverse
  is `x − O(log x) ≤ N(y) ≤ x + O(x^{2/3}(log x)^{2/3})`, where
  `x = y/W(y/(eT))` and `y` is the logarithm of a count. Part II also gives
  exact counts through 400 and long-double values through 1000, the exact
  identity (66), and finite log-concavity checks. It proves that `a_n/n!`
  is not PF₃, that a natural refinement polynomial is not real-rooted, and
  that the raw-word class is not meet-closed. It states Conjecture 16.1,
  `log c_n ~ (2/3)(log n)^2`, and gives a formal (non-proof) route to the
  constant 2/3.
- **Part III** (Theorems 21.1, 28.1): `log A′(t(q)) = q²/6 +
  O(q^{3/2}√(log q))`, `log A(t) ~ (2/3) log²(1/(T−t))`, and
  `log Σ_{j≤N} c_j = (2/3)(log N)^2 + O((log N)^{3/2}√(log log N))`.
  Moreover `limsup log c_n/(log n)^2 = 2/3`. It also proves an abstract
  one-sided regularity criterion (Proposition 29.2) and inverses for the
  cumulative and real-axis laws (Section 30.2).
- **Part IV** (Theorem 33.1): `a_{n+1}/((n+1)a_n) = μ +
  O(n^{−1/4}(log n)^{3/4})`, `log c_n ≥ −O(√n (log n)^{3/2})`, and
  `x − O(log x) ≤ N_a(y) ≤ x + O(√(x log x))`. It uses the exact
  inequality `R_{n+1} ≥ R_n − 1` for `R_n = a_{n+1}/a_n`. It also gives an
  exact counterexample to a "childwise" strengthening of log-concavity
  (Section 40.1), and two scans of 48,510,450 inequalities each in which no
  log-concavity violation was found.
- **Part V** (bundle Report 97; its `c_n` is the raw count `a_n`):
  Theorem 42.1 is a third proof of the root limit (error `o(n)` only),
  by a finite Perron bound with a calibrated weight and buffered
  Eulerian blocks; Theorem 46.1 is a second proof of the ratio limit,
  without a rate. New in the repository: the two-catalytic functional
  equation `H(x; s+x(t−1), t) = t H(x; s, t−xs(t−1)) − xst(t−1)` and its
  coefficient recurrence (Proposition 43.1); the weighted upper bound
  `limsup n^{-1} log(H_n(s,t)/n!) ≤ −log χ(s,t)` (Proposition 46.3); the
  endpoint laws (Corollary 46.4, equation (276)): the proportions of values
  used once, unused available values, distinct values and ascents tend to
  `1 − 8/(3π)`, `8(π+1)/(3π²) − 1`, `1 − 4/(3π)` and `4/(3π) + 8/(3π²)`,
  with exponentially small deviations; strict monotonicity
  `a_{n+1} > a_n` (Lemma 47.1); exact counts `a_0, …, a_395`, equal to
  Part II's independent table. Its inverse (Corollary 47.2) is weaker
  than those of Parts II and IV. Section 48 is a second formal route to
  the constant 2/3. Part V is the cap-two case of Part III of
  `../a294220-ascent-multiplicity-caps/` (bundle Report 99, same method),
  which proves the root and ratio limits, the endpoint laws (as
  integrals) and a full large-deviation principle for every cap.

**What no Part claims.** No Part proves the pointwise law
`log c_n ~ (2/3)(log n)^2`, which is open in Part II (Conjecture 16.1),
Part III (equation (76)) and Part IV (equation (160)). No Part proves
eventual normalized monotonicity or log-concavity, a multiplicative
equivalent `a_n ~ C n! μ^n …`, a power prefactor, a limiting amplitude, an
all-orders expansion, optimal remainders or effective constants. Part
III's one-sided ratio bound (143) is unproved. Part II's §18 is explicitly
a formal route, not a proof. Exact counts, residual grids and log-concavity
scans are diagnostics or evidence and prove no uniform or asymptotic
statement. Long-double terms 401–1000 are not interval-certified. The
literature and repository searches are scoped negative evidence, not
novelty or priority certificates; no Part claims publication. Part IV's
counterexample refutes an inequality that Part IV itself proposes, which
no other Part and no report of this collection states. It refutes no
delivered or repository claim and does not refute statewise
log-concavity. Part V keeps Report 97's non-claims: no convergence rate of
the ratios, no amplitude or equivalent, the factor
`exp((2/3)(log n)^2)` and an all-orders expansion "not proved"; its
floating data are not interval certified; no exact rounding rule for its
inverse; a bounded literature search, no priority claim, no publication
or OEIS submission. Its unproved claims are listed in its Section 50
(standing rule of 4 October 2026): the pointwise law; the formal
eikonal, transport and Borel-singularity reading of Section 48; the
numerical `d_n → 4/3`; the `O(n^4)`-operation, `O(n^3)`-storage count
(settled at the write by Corollary 18.3 of the A294220 report at cap two);
and the warning that a cutoff `10^-30` corrupts later ratios (supported at
the write by a rerun to n = 400, see Rerunning). No claim of Report 97 was
found to be wrong.

**Statements that a later Part supersedes** are printed as delivered, each
followed by a dated `[write]` note:

- "the ratio limit is unresolved" (Part I, abstract and §§1, 8; Part II,
  abstract; Part III, abstract and §21). Part IV proves the limit.
- "the coefficient 2/3 is unproved" (Part II). Part III proves it in
  limsup and cumulative form.
- Part II's Theorem 9.1 and Corollary 9.2. Part IV improves both.
- Report 97 (Part V, §§42 and 49) calls the stretched factor
  `μ₁^{n^σ} n^g` of Conway–Conway–Elvey Price–Guttmann "unresolved";
  Parts II and III exclude it for either sign. Its literature paragraph
  (§42) found no proof of the root limit; Part I is one, dated 1 October.

Part III's `limsup` theorem also rules out an equivalent of Part II's form
with `c < 0`. The merge added this one-line deduction in a `[write]` note
after Part II's §9; the manuscripts do not state it.

## Files

The numerals I–V name the Part that a delivered file belongs to.

```
article.tex                                                   the merged report (standalone LaTeX, internal bibliography)
article.pdf                                                   the compiled report, 101 pages
README.md                                                     this guide
figures/36-fine-correction-diagnostics.pdf                    II: Figure 1, included by article.tex
figures/36-fine-correction-diagnostics.png                    II: the same figure as PNG (not used by the build)
37-foundation-radius-proof.md                                 I: radius / limsup proof draft (1 Oct)
37-foundation-root-limit-proof.md                             I: root-limit upgrade draft (1 Oct)
37-foundation-audits-radius-audit.md                          I: independent audit of the radius proof
37-foundation-audits-root-limit-audit.md                      I: independent audit of the root-limit proof
37-foundation-audits-integrated-audit.md                      I: integrated article and Lambert-inverse audit
37-foundation-literature.md                                   I: scoped literature and duplication note (pin 0870c19bb)
code/37-foundation-build.sh                                   I: delivered PDF build script
code/37-foundation-verify_radius.py                           I: recurrence, enumeration, residual and integral checks
code/37-foundation-verify_root_limit.py                       I: bounded-shift calculus checks
data/37-foundation-verify_radius.json                         I: recorded output of verify_radius.py
data/37-foundation-verify_root_limit.json                     I: recorded output of verify_root_limit.py
data/37-foundation-verification-summary.json                  I: build, review and layout record
data/37-foundation-requirements.txt                           I: mpmath>=1.3,<2
data/37-foundation-audits-radius-manifest.json                I: hash manifest of the radius audit
data/37-foundation-audits-root-limit-manifest.json            I: hash manifest of the root-limit audit
data/37-foundation-audits-integrated-manifest.json            I: hash manifest of the integrated audit
36-fine-padded-barrier-proof.md                               II: quadratic-logarithm upper bound (proof note)
36-fine-improved-coarse-lower.md                              II: the n^{2/3}(log n)^{5/3} lower bound (proof note)
36-fine-coefficient-obstruction.md                            II: coefficient-regularity obstruction note
36-fine-lognormal-route.md                                    II: formal (non-proof) route to 2/3
36-fine-kernel-audit-padded-barrier.md                        II: audit of the padded barriers
36-fine-kernel-formal-kernel-audit.md                         II: frozen-kernel calculation; audit of the formal route
36-fine-audits-independent-mathematical-audit.md              II: integrated independent audit
36-fine-literature.md                                         II: scoped literature and repository audit (pin 13ef7d939)
36-fine-literature-regularity-supplement.md                   II: regularity literature search, small counterexamples
36-fine-research-README.md                                    II: delivered README of support/fine-research/
36-fine-numerics-README.md                                    II: delivered numerical reproduction guide
36-fine-qa-visual-review.md                                   II: all-page visual review of the delivered PDF
code/36-fine-verify.py                                        II: replay driver (needs g++ and GMP even in quick mode)
code/36-fine-verify.sh                                        II: wrapper that runs verify.py with python3
code/36-fine-build.sh                                         II: delivered PDF build script
code/36-fine-create_bundle.py                                 II: recreates the delivered ZIP and SHA256SUMS
code/36-fine-qa-check_pdf.py                                  II: renders the delivered PDF, checks its structure
code/36-fine-kernel-verify_padded_barrier.py                  II: residual and padding checks
code/36-fine-kernel-verify_continuum_average.py               II: continuum-average check of (69)
code/36-fine-audits-verify_fine_independently.py              II: the auditor's independent checks
code/36-fine-literature-checks-check_small_polynomials.py     II: PF3, discriminant and meet counterexamples
code/36-fine-numerics-exact_counts.cpp                        II: exact counts (C++17, GMP)
code/36-fine-numerics-floating_counts.cpp                     II: long-double normalized counts
code/36-fine-numerics-analyze.py                              II: diagnostics g_n, c_n and fits
code/36-fine-numerics-fit_log_polynomials.py                  II: logarithmic-polynomial fits
code/36-fine-numerics-plot_diagnostics.py                     II: draws the figure
code/36-fine-numerics-check_generic_logconcavity.py           II: all-state log-concavity (3,060 tests)
data/36-fine-numerics-exact-counts-400.txt                    II: exact a_n, n = 0..400 (reference data of verify.py)
data/36-fine-numerics-exact-counts-400.log                    II: run log of the exact counts
data/36-fine-numerics-floating-counts-1000.txt                II: long-double a_n/(n! mu^n), n = 0..1000
data/36-fine-numerics-floating-counts-1000.log                II: run log of the floating counts
data/36-fine-numerics-oeis-b202058.txt                        II: OEIS b-file, terms 0..176, fetched 2 Oct 2026
data/36-fine-numerics-diagnostics.tsv                         II: diagnostics table (output of analyze.py)
data/36-fine-numerics-analysis.json                           II: analysis output
data/36-fine-numerics-analysis-summary.json                   II: analysis summary
data/36-fine-numerics-log-polynomial-fits.json                II: fit results
data/36-fine-numerics-log-polynomial-fits.txt                 II: fit results, text
data/36-fine-numerics-generic-logconcavity.json               II: all-state log-concavity output
data/36-fine-kernel-verification.json                         II: residual-check output
data/36-fine-kernel-verification-output.txt                   II: residual-check output (same bytes)
data/36-fine-kernel-continuum-average-verification.json       II: continuum-average output
data/36-fine-kernel-continuum-average-output.txt              II: continuum-average output (same bytes)
data/36-fine-literature-checks-small_polynomials.json         II: obstruction-check output
data/36-fine-audits-independent-check-results.json            II: auditor's check results
data/36-fine-audits-independent-check-output.txt              II: auditor's check output (same bytes)
data/36-fine-audits-independent-audit-manifest.json           II: audit hash manifest
data/36-fine-checks-continuum-average.log                     II: recorded replay log
data/36-fine-checks-exact-replay.log                          II: recorded replay log
data/36-fine-checks-floating-replay.log                       II: recorded replay log
data/36-fine-checks-independent-audit-replay.log              II: recorded replay log
data/36-fine-checks-residual.log                              II: recorded replay log
data/36-fine-checks-small-polynomials.log                     II: recorded replay log
data/36-fine-checks-suffix-logconcavity.log                   II: recorded replay log
data/36-fine-checks-verify_radius.log                         II: replay of Part I's radius check
data/36-fine-checks-verify_root_limit.log                     II: replay of Part I's root-limit check
data/36-fine-checks-archive-replay.json                       II: archive replay record
data/36-fine-checks-clean-replay-summary.json                 II: clean replay summary
data/36-fine-checks-full-replay-summary.json                  II: full replay summary
data/36-fine-checks-foundation-integrity.json                 II: hashes of the bundled foundation
data/36-fine-full-replay-output.txt                           II: full replay output (same bytes as the summary)
data/36-fine-build-output.txt                                 II: recorded build output
data/36-fine-verification-summary.json                        II: verification summary (delivery root)
data/36-fine-research-verification-summary.json               II: verification summary (support/fine-research/)
data/36-fine-source-provenance.json                           II: hashes of the bundled foundation and sources
data/36-fine-qa-final-reviewed-render-hashes.txt              II: SHA-256 of the 18 excluded page renders
data/36-fine-qa-structural-check.json                         II: PDF structural check
data/36-fine-qa-structural-check-output.txt                   II: PDF structural check (same bytes)
data/36-fine-qa-comparison-with-earlier-review.json           II: comparison with the earlier visual review
data/36-fine-requirements.txt                                 II: Python requirements
07-lognormal-source-audit-verification-summary.md             III: verification and audit summary
code/07-lognormal-replay.sh                                   III: delivered replay entry point (core/full/all)
code/07-lognormal-build.sh                                    III: delivered PDF build script
code/07-lognormal-scripts-check_exact_identities.py           III: 73,984 exact rational transition cases
code/07-lognormal-scripts-check_enumeration.py                III: literal words through length 10
code/07-lognormal-scripts-check_corrector.py                  III: 40 corrected-residual cases (NumPy)
code/07-lognormal-scripts-check_manifest.py                   III: checks the delivered SHA256SUMS (not shipped)
data/07-lognormal-results-exact-identity-check.json           III: frozen result
data/07-lognormal-results-enumeration-check.json              III: frozen result
data/07-lognormal-results-corrector-check.json                III: frozen result
data/07-lognormal-source-audit-environment.json               III: recorded environment
data/07-lognormal-source-audit-proof-input-fingerprints.json  III: SHA-256 of the proof inputs
data/07-lognormal-source-audit-public-sources.json            III: public sources (pin 4b874cea0)
data/07-lognormal-source-audit-release-checks.json            III: release QA record
08-ratio-PROVENANCE.md                                        IV: attribution, predecessor fingerprints
code/08-ratio-replay.sh                                       IV: delivered replay entry point (core/full)
code/08-ratio-build.sh                                        IV: delivered PDF build script
code/08-ratio-scripts-check_core.py                           IV: transitions, moments, root counts
code/08-ratio-scripts-check_tilted_identity.py                IV: coefficients of the tilted square identity
code/08-ratio-scripts-verify_counterexample.py                IV: the childwise counterexample
code/08-ratio-scripts-check_concavity.py                      IV: factorial-normalized scan
code/08-ratio-scripts-check_m_concavity.py                    IV: rising-factorial scan
code/08-ratio-scripts-compare_replay.py                       IV: compares replayed scans with frozen ones
code/08-ratio-scripts-check_manifest.py                       IV: checks the delivered SHA256SUMS (not shipped)
data/08-ratio-results-core.json                               IV: frozen core result
data/08-ratio-results-tilted-identity.json                    IV: frozen identity result
data/08-ratio-results-counterexample.json                     IV: frozen counterexample
data/08-ratio-results-a_seq.json                              IV: a_n, n = 0..180 (first scan)
data/08-ratio-results-a_seq_m.json                            IV: a_n, n = 0..180 (second scan; same bytes)
data/08-ratio-results-concavity_violations.json               IV: violations of the first scan: []
data/08-ratio-results-m_concavity_violations.json             IV: violations of the second scan: []
data/08-ratio-results-finite-scope.json                       IV: domain of the two scans
code/38-growth-run_checks.sh                                  V: delivered check driver (delivery layout, g++ with GMP, python3)
code/38-growth-build_local.sh                                 V: delivered PDF build (builds article.tex; also Report 99's, byte-identical)
code/38-growth-compute_exact.cpp                              V: exact GMP transfer (C++17, gmpxx)
code/38-growth-compute_distribution.cpp                       V: normalized long-double transfer with a mass cutoff
code/38-growth-verify.py                                      V: exact-data, small-word and numerical-table verifier
code/38-growth-test_verify.py                                 V: fail-closed regression tests of verify.py
data/38-growth-exact_coefficients_395.txt                     V: exact a_n, n = 0..395
data/38-growth-normalized_transfer_cut120.txt                 V: floating run, cutoff 1e-120, n = 1..1200
data/38-growth-normalized_transfer_cut200.txt                 V: floating run, cutoff 1e-200 (same bytes as cut120)
data/38-growth-verification.txt                               V: recorded output of run_checks.sh
data/38-growth-PROVENANCE.json                                V: sources, proved / not-proved lists, checks, SHA-256 of the delivery
```

The directory holds 133 files: 23 at the root (`article.tex`,
`article.pdf`, this README and 20 delivered Markdown notes), 39 in `code/`,
69 in `data/` and 2 in `figures/`. Every file except `article.tex`,
`article.pdf` and `README.md` is byte-identical to the delivery.

**Delivery names.** Files were renamed when placed: delivered
`X/Y/z.ext` became `NN-slug-X-Y-z.ext`, with code in `code/` and outputs in
`data/`. Manuscript 36's `support/fine-research/` was dropped from the
flattened names. Its `README.md` and `verification-summary.json` became
`36-fine-research-README.md` and
`data/36-fine-research-verification-summary.json`, to avoid collisions
with the files of 36's root. The nine files that only manuscript 36's
`dependencies/frozen-foundation/` carried are shipped as
`37-foundation-*`, because they belong to Part I. The placement plan
(`b77P1_plan.tsv`, one row per delivered file) maps every name.
Delivered files whose text still uses delivery names or names unshipped
files:

- Every shipped script. The build scripts build the delivered TeX
  (`a202058-report.tex`, `a202058-fine-addendum.tex`,
  `a202058-lognormal.tex`, `a202058-ratio.tex`), which is not shipped
  under that name. `36-fine-verify.py` expects `support/fine-research/`,
  `audits/` and `dependencies/frozen-foundation/` (with the frozen
  `a202058-report.tex`). The two `check_manifest.py` scripts read a
  `SHA256SUMS` that is not shipped. `36-fine-create_bundle.py` rebuilds the
  delivered ZIP. `36-fine-qa-check_pdf.py` reads the unshipped delivered
  PDF and writes into `qa/`.
- The Markdown notes cite each other and their scripts by delivery path,
  for example `../padded-barrier-proof.md` and `radius-proof.md`.
  `08-ratio-PROVENANCE.md` describes the `prior/` copy of manuscript 07,
  which is not shipped. `36-fine-qa-visual-review.md` reviews the
  excluded page renders.
- Several records hash files that are not shipped: the delivered PDFs, the
  nested `frozen-foundation.zip` and the `SHA256SUMS` ledgers. These are
  `data/36-fine-source-provenance.json`,
  `data/36-fine-checks-foundation-integrity.json`, the three
  `data/37-foundation-audits-*-manifest.json`,
  `data/07-lognormal-source-audit-proof-input-fingerprints.json` and
  `data/36-fine-audits-independent-audit-manifest.json`.
- `data/36-fine-qa-final-reviewed-render-hashes.txt` lists the excluded
  renders by the absolute delivery path
  `/workspace/shared/oeis-a202058-fine-report/qa/page-NN.png`.
- Part V (placement plan `plan99_102-ASC_01.tsv`): Report 97's
  `checks/` level was dropped from the names, so delivered
  `checks/verify.py` is `code/38-growth-verify.py` and
  `checks/exact_coefficients_395.txt` is
  `data/38-growth-exact_coefficients_395.txt`; the root files
  `run_checks.sh`, `build_local.sh` and `PROVENANCE.json` became
  `code/38-growth-*.sh` and `data/38-growth-PROVENANCE.json`.
  `run_checks.sh` compiles `checks/compute_exact.cpp` into `checks/build/`
  and runs `checks/verify.py`; `verify.py` reads its data from its own
  directory under the delivered names, including `oeis_b202058.txt`, which
  is not shipped (it is byte-identical to
  `data/36-fine-numerics-oeis-b202058.txt`). `build_local.sh` builds the
  unshipped `article.tex` with a TeX Live layout. `PROVENANCE.json` hashes
  the unshipped manuscript files and README and gives `pdf_sha256` of a
  PDF that was never delivered (no file of the archive has that hash).
  `data/38-growth-verification.txt` prints the replay output twice.

**Not shipped** (all survive in `096ee7b87`): the four delivered PDFs and
the four delivery READMEs. This README replaces them. The `README.md`
placed here in `f76fcb566` was manuscript 37's delivery README; it is now
this file. Also not shipped: the three member manuscripts (printed as
Parts II–IV) and the `SHA256SUMS` ledgers and audit hash lists, all
verified at placement. The embedded duplicates are not shipped either:
36's nested `frozen-foundation.zip`, which is byte-identical to archive 37,
the nine files of 36's unpacked frozen foundation that are byte-identical
to Part I's, and 08's `prior/` copy of manuscript 07. Nor are the
superseded render-hash list, 36's PDF text extraction
`qa/extracted-text.txt`, 36's two empty compile logs, or the 18 page
renders described next.

Not shipped from Report 97 (all in `60f54ea06`, archive
`A202058_Ascent_Sequence_Growth_Source.zip`): its manuscript (`article.tex`,
the nine section files and `article_standalone.tex`, printed as Part V),
its delivery README, and `checks/oeis_b202058.txt` (byte copy of Part II's
b-file, above). Its README lists an `article.pdf` that the archive does not
contain; a rebuild of the delivered source at intake had 23 pages, the
count `PROVENANCE.json` records. Nothing was excluded as heavy.

**Kept duplicates.** These shipped files are byte-identical in pairs or
triples, because the delivered scripts read each by its own name:

- `data/08-ratio-results-a_seq.json` and `-a_seq_m.json`;
  `-concavity_violations.json` and `-m_concavity_violations.json` (both
  `[]`).
- `data/36-fine-checks-verify_radius.log` and
  `data/37-foundation-verify_radius.json`.
- `data/36-fine-checks-residual.log`, `data/36-fine-kernel-verification.json`
  and `-verification-output.txt`.
- `data/36-fine-checks-continuum-average.log` and the two
  `data/36-fine-kernel-continuum-average-*` files.
- `data/36-fine-checks-suffix-logconcavity.log` and
  `data/36-fine-numerics-generic-logconcavity.json`.
- `data/36-fine-checks-small-polynomials.log` and
  `data/36-fine-literature-checks-small_polynomials.json`.
- `data/36-fine-checks-independent-audit-replay.log` and the two
  `data/36-fine-audits-independent-check-*` files.
- `data/36-fine-checks-full-replay-summary.json` and
  `data/36-fine-full-replay-output.txt`.
- `data/36-fine-qa-structural-check.json` and `-structural-check-output.txt`.
- `data/38-growth-normalized_transfer_cut120.txt` and `-cut200.txt` (the
  two cutoffs give the same printed digits; `verify.py` reads both names).

**Figure fonts.** The delivered figure
`figures/36-fine-correction-diagnostics.pdf` embeds two Type 3 DejaVu Sans
fonts (matplotlib's default). It is included unchanged, so `article.pdf`
carries those two Type 3 fonts; every other font is Type 1.

## Reconstructing the excluded data

Not committed (heavy and regenerable, per the repository rule "Exclude
heavy regenerable artifacts"): the 18 page renders qa/page-01.png …
qa/page-18.png of the Part II delivery (4,400,431 bytes, 69 % of that
archive). They are poppler renders of the delivered PDF
a202058-fine-addendum.pdf at 130 dpi (1105 × 1430 px), the command of
qa/check_pdf.py, line 21.

    git show 096ee7b87:docs/incoming/oeis-a202058-fine-report.zip > fine.zip
    unzip fine.zip && cd oeis-a202058-fine-report
    pdftoppm -r 130 -png a202058-fine-addendum.pdf qa/page

About 1.5 minutes. At intake (2 October 2026) poppler pdftoppm 24.04.0
(MiKTeX) reproduced all 18 files byte for byte against
data/36-fine-qa-final-reviewed-render-hashes.txt; another poppler version
may differ in bytes but not in content. The delivered copies themselves
are in the archive above (arrival commit 096ee7b87).

Notes on this procedure, checked at the write:

- Run the commands in Git Bash. PowerShell redirection of `git show`
  may not preserve the bytes of the ZIP.
- The archive is 5,521,731 bytes. Its 117 entries hold 6,348,483 bytes
  uncompressed, and the renders are 69.3 % of that total.
- A rerun at the write took 42 seconds on a less loaded machine. All 18
  SHA-256 values again matched the hash list.
- The hash list records the delivery's absolute paths
  (`/workspace/shared/...`), so `sha256sum -c` does not apply as it
  stands. Compare the first column instead:
  `sha256sum qa/page-*.png | cut -c1-64 | diff - <(cut -c1-64 <hash list>)`.
- The delivered `SHA256SUMS` inside the archive lists the PNGs too, so it
  checks the extracted archive as it stands.
- The extraction already contains the delivered PNGs, and the command
  overwrites them. To test regeneration itself, delete
  `qa/page-*.png` first, or render into another directory.

Two other Part II files are regenerable but small enough to keep. Both
scripts use delivery-relative paths, so run them on a copy with the
delivered layout, for example the extraction above:

- `data/36-fine-numerics-exact-counts-400.txt` (118,112 bytes) needs a
  C++17 compiler and GMP:
  `code/36-fine-numerics-exact_counts.cpp`, delivered as
  `support/fine-research/numerics/exact_counts.cpp`. The delivery records
  about 1 minute (62 s).
- `data/36-fine-numerics-diagnostics.tsv` (143,800 bytes) regenerates in
  seconds:
  `py support/fine-research/numerics/analyze.py`, the shipped
  `code/36-fine-numerics-analyze.py`. At intake it took 6 s and matched
  except for line endings: on Windows Python writes CRLF.

## Rerunning the checks

Never run the shipped scripts in this directory. They write next to
themselves or into delivery-relative directories, and on Windows they
write CRLF. Rerun each suite in a fresh extraction of its delivered
archive, outside the repository:

    git show 096ee7b87:docs/incoming/<archive>.zip > x.zip && unzip x.zip

The delivered entry points call `python3`, which on this Windows machine
is the Microsoft Store alias. In Git Bash, define a shim first:
`python3() { py "$@"; }; export -f python3`.

- **Part I** (`oeis-a202058-report/`): `py -m pip install -r
  requirements.txt` (mpmath), then `py verify_root_limit.py` and
  `py verify_radius.py`. The second visits 287,820 cases and was recorded
  at 12 s. Both rewrite their JSON in place inside the extraction. At
  intake `verify_root_limit.py` reproduced its JSON up to line endings,
  but `verify_radius.py` twice failed to finish within 170 s on the
  loaded machine. At the write (2 October 2026), on a fresh copy of
  archive 37 with mpmath 1.3, `verify_radius.py` passed in under a
  minute. Its JSON was identical to the delivered
  `verify_radius.json` except for CRLF line endings.
- **Part II** (`oeis-a202058-fine-report/`): `bash verify.sh` (quick) or
  `bash verify.sh --full`. Both modes compile the C++ counters and need
  `g++` with GMP (`verify.py`, line 55). Without them, run the Python
  steps one by one with `py`:
  `support/fine-research/kernel/verify_padded_barrier.py`,
  `kernel/verify_continuum_average.py`,
  `numerics/check_generic_logconcavity.py`,
  `literature-checks/check_small_polynomials.py` and
  `audits/verify_fine_independently.py`. At intake all five passed.
  Floating-point output differed from the recorded output by at most
  3.7e-9 relative, and the C++ steps were not run. `verify.py --full`
  takes several minutes and much memory.
- **Part III** (`a202058-lognormal-report/`): `bash replay.sh core` (exact
  rational and enumeration checks, standard library only) or
  `bash replay.sh full` (adds the NumPy residual check). It writes to
  `build/replay/`. At intake the manifest, exact-identity, enumeration and
  full corrector checks passed, equal to the frozen results.
- **Part IV** (`a202058-ratio-report/`): `bash replay.sh core`, or
  `bash replay.sh full` for the two 48,510,450-inequality scans (about one
  minute each recorded). It writes to `build/replay/` (or
  `$A202058_REPLAY_OUT`). At intake the core checks passed and equalled
  the frozen results; the full scans were not run.
- **Part V** (Report 97, arrival `60f54ea06`):
  `git show 60f54ea06:docs/incoming/A202058_Ascent_Sequence_Growth_Source.zip > r97.zip`,
  unzip, then in `A202058_Ascent_Sequence_Growth/` run `py checks/verify.py`
  (exact data, small words, catalytic recurrence and the numerical tables;
  about 2 s; the GMP rebuild line needs `--rebuilt`), `py
  checks/test_verify.py` and `py -O checks/test_verify.py` (4 tests each,
  15–20 s). The full `bash run_checks.sh 176` (or `395`) needs `g++` with
  the GMP C++ library (`-lgmpxx`), which this machine lacks, and
  `python3`. At intake (5 October 2026, on copies) `verify.py` reproduced
  every line of `verification.txt` except the GMP-rebuild line, both test
  runs passed, a fresh Python transfer matched the archived table for
  n ≤ 60, and the 396 archived counts equalled Part II's table. At the write
  `compute_distribution.cpp` (no GMP needed) was compiled with WinLibs
  `g++ -O3 -std=c++17` and run on a copy: `./cd 400 1e-120` reproduced rows
  1–400 of `data/38-growth-normalized_transfer_cut120.txt` byte for byte
  (9 s), and `./cd 400 1e-30` (3 s) gave ratio errors of −4.7e-12, −3.3e-8
  and −7.3e-6 at n = 200, 300, 395 against the exact table, which supports
  the delivered warning about that cutoff. The 1200-row long-double runs
  were not repeated.

## Labels

Every label in `article.tex` carries the prefix `a58:`. The sub-prefixes
are `a58:fd:` for Part I (manuscript 37), `a58:fn:` for Part II (36),
`a58:ln:` for Part III (07) and `a58:rt:` for Part IV (08). After the
sub-prefix, every delivered label keeps its delivered name: 28, 67, 102
and 69 delivered labels. The merge added 14 labels: five section labels
in Part I (`a58:fd:sec:recurrence`, `…:radius`, `…:fulllimit`,
`…:coarse`, `…:verification`) and one in Part III
(`a58:ln:sec:allindex`), four Part labels (`a58:part:fd`, `…:fn`,
`…:ln`, `…:rt`), and four front-matter labels (`a58:sec:guide`,
`…:status`, `…:notation`, `…:provenance`). That makes 280 labels; the
placed `article.tex` (manuscript 37 alone) had 28. The batch-102 write
added Part V under `a58:eg:` ("exponential growth"): Report 97's 103
delivered labels keep their names after the sub-prefix (for example
`a58:eg:thm:main`, `a58:eg:low:theorem`, `a58:eg:rat:joint`), plus
`a58:part:eg` and `a58:eg:sec:further`; 385 labels in all, none of the
280 renamed or renumbered (checked against a build of the committed text).

The sub-prefixes were needed: the four manuscripts share 27 label names.
`thm:main` occurs in all four. `eq:FK` (36, 37) and `eq:fk` (07, 08)
differ only in case, and `lem:slow` names two different lemmas (07: slow
profile; 08: slow decrease of ratios). Manuscript 08 cited manuscript 07's
labels by literal name (`eq:quantcum`, `eq:coarseenclosure`,
`eq:coarseuniform`, `eq:growing`, `eq:chernoff`) and its sections by
number. These are now `\eqref`s and `\ref`s to the `a58:ln:` labels.

## Numbering

Sections, statements and equations are numbered continuously.

| Part | delivered Section k is | delivered equation (k) is |
|---|---|---|
| I | Section k | (k) |
| II | Section k + 8 (its Appendix A is Section 20) | (k + 23) |
| III | Section k + 20 | (k + 69) |
| IV | Section k + 32 | (k + 150) |
| V | Section k + 41 (Section 50 added at the write) | (k + 209) |

Statement numbers follow their sections. For example, Part II's
Theorem 1.1 is Theorem 9.1 here, and Part IV's Theorem 1.1 is
Theorem 33.1. Part II's Table 1 and Figure 1 keep their numbers.

## How the merge was done

Each Part prints its manuscript from `\maketitle` to the bibliography,
with every result, proof, remark, question and limitation. Statements keep
their delivered wording. The changes:

- the label prefixes above;
- one shared preamble, the union of the four, in which every shared macro
  has the same definition in every source;
- the per-Part title blocks, printed as Part headings with a source line;
  the abstracts are printed as "Abstract of this Part (as delivered)";
- the tables of contents of 07 and 08 replaced by one;
- 36's `\appendix` turned into an ordinary last section of Part II, so
  that later Parts keep arabic section numbers;
- the four bibliographies merged into one, keeping every detail of every
  entry. The keys of 07 and 08 were renamed to those of 36 (`cceg` →
  `CCEG`, `oeis` → `OEIS`, `triangle` → `OEIStriangle`, `callan` →
  `CallanMansour`, `liu` → `LiuKitaevZhang`, `hwang` → `HwangJin`,
  `proveit` → `ProveIt`). 36's `Foundation` and 08's `prior` entries
  became references to Parts I and III; 08's entry text about the
  superseded ratio statement is quoted in a `[write]` note;
- 36's figure path changed to `figures/36-fine-correction-diagnostics.pdf`;
- the `\pdfmapfile{+lm.map}`, `{+cm.map}` and `{+symbols.map}` lines of
  the four preambles removed. On MiKTeX they only produced 684 "fontmap
  entry already exists" warnings;
- 23 dated `[write]` notes (a 24th, in the guide, was added with the
  batch-77P2 reciprocal notes: the pointer to `a294220-ascent-multiplicity-caps`
  below), plus front matter: a guide, a table of what is
  proved where, a notation table and a provenance section.

No symbol was renamed. Symbols that change meaning between Parts are
tabulated in the front matter. Among them are `c_n` (Part II's table
column is a second difference, not `a_n T^n/n!`), `N(·)` and `y` (Part
I's `y` is a count, while Parts II–IV use its logarithm), `x_0` versus
Part IV's `x_*`, and `E`, `H`, `M`, `R`, `d`, `D`, `A_0`, `B_0`, `L`,
`K`. One more: the neighbouring A202061 and A202062 reports use `μ ≈
7.2959`, not `8/(3π²)`.

**Where the merge had to choose.** The order is the chain 37 → 36 → 07 →
08, and manuscript 37, the foundation, is the base. The re-derived
foundations in Parts II–IV stay where they stand, because each Part's
later proofs cite their equations: the compacted model, the endpoint
`t(∞) = 3π²/8`, the coarse comparison and the Chernoff window. `[write]`
notes mark them. Part III's §30.1 re-proves Part II's Theorem 9.1 and
Corollary 9.2 and Part I's root limit; it is marked as a second route and
kept in full, because Part IV cites its equations. Part IV restates Part
II's identity (66) and target (67) as (166) and (205) without credit. The
`[write]` note after (167) gives the credit, and keeps as new only
`R_{n+1} ≥ R_n − 1` and its use. Manuscript 07 cites neither 37 nor 36. A
note after its §21 supplies the attribution, confirmed by its proof-input
fingerprint: the SHA-256 `0c5fdcd5…` of `36-fine-padded-barrier-proof.md`.

**Changes at the batch-102 write (5 October 2026).** Report 97 is printed
in full as Part V, after Part IV, from its first section to its
bibliography (`article_standalone.tex` equals the expansion of its
`article.tex`). Changes: the labels above; its title block became the Part
heading and its abstract is printed as delivered; its table of contents and
`\clearpage` were dropped; its macros were added to the preamble, except
that its `\dd` (an upright d) is printed by `\egdd`, because this report's
`\dd` sets an italic d; its citation keys `Conway2022` → `CCEG` and `OEIS`
→ `OEIS` (both entries gained its details), and `DS2011` and `ConwayData`
are new entries. Seventeen dated `[write]` notes (5 October 2026): the
Part-head reading note; three in §42 (stretched factor excluded; third
route to the root limit; literature status); two in §43 (the state is Part
I's `(s,u,k)`; the catalytic equation is new, its recurrence checked with
SymPy through n = 9); §44 (second evaluation of 3π²/8); three in §46
(second route to the ratio limit; weighted bound superseded; endpoint
laws); §47 (inverse weaker); §48 (2/3 proved in limsup and cumulative
form); §49 (shipped files, the cutoff rerun, the operation count); the
list of Section 50, "Further questions and research", a section added at
the write; one after Part II's Conjecture 16.1 (neighbouring reports); and
two in the front matter (Part V added; a294220 now shares theorems).

**OEIS data.** The b-file and the exact OEIS terms compared by the checks
(`data/36-fine-numerics-oeis-b202058.txt`, the counts quoted in the
Parts) come from the OEIS and are licensed CC BY-SA 4.0. The title, author line, abstract and front-matter
tables were extended to five Parts; the earlier wording is recorded in a
dated note in the guide. Where the write had to choose: Report 97 is not
merged with its generalization Report 99, which went to
`a294220-ascent-multiplicity-caps` as Part III; the batch-77P2 split (cap
two here, every cap there) is kept and the two Parts cite each other.

## Relation to other reports and to formal work

- `../a202061-ascent-120-deficit/` and
  `../a202062-ascent-201-enumeration/` treat the 120- and 201-avoiding
  ascent sequences of the same Conway–Conway–Elvey Price–Guttmann paper.
  Those sequences grow exponentially and are studied by different methods,
  so the reports share no theorem with this one.
- `../a294220-ascent-multiplicity-caps/` (batch 77, manuscripts 47 and 52)
  treats every multiplicity cap `b` (the array A294220; A202058 is `b = 2`):
  the factorial growth constants `T_b` for every fixed `b ≥ 3`, their
  large-cap expansion and exact Taylor sectors of `T_b − π²/6`. For `b = 2`
  it cites this report's Part I (`T_2 = 3π²/8` and the root limit) and uses
  nothing else from here. Dated `[write]` note in the guide. Since 5 October
  2026 the two reports share theorems: that report's Part III (bundle
  Report 99) proves the root and ratio limits, the endpoint laws, a full
  large-deviation principle and an `O(N^{r+2})` algorithm for every cap
  `r ≥ 2`, and this report's Part V (Report 97) is its case `r = 2`, by the
  same method (second dated note in the guide).
- `../a202059-ascent-100-110-growth/` (batch 102, Reports 243 and 241)
  treats the 100- and 110-avoiding ascent sequences of the same
  Conway–Conway–Elvey Price–Guttmann paper (A202059, A202060). Its class
  avoiding 000 and 100 is a subclass of A202058; there the factorial-
  normalized root is `Θ((log n)^{-2})` (tending to 0, with
  `(log n)²(e_n/n!)^{1/n} → 2`), against `8/(3π²)` here. No theorem is
  shared. Note that report's `aₙ` avoids 100 and its `cₙ` avoids 000, 100,
  110 simultaneously.
- `../a336070-weak-ascents/` (batch 102, Reports 105, 107, 108) treats weak
  and difference ascent sequences, with factorial constant 6/π² and the
  pointwise correction `(d/2)(log n)²` with `O(log n)` remainder for every
  fixed difference `d ≥ 1` (`wasc:sh:thm:main`), by a path change of
  measure. It is the proved analogue of this report's open pointwise law
  with coefficient 2/3, not a proof of it; no theorem is shared. A dated
  note after Conjecture 16.1 points to both batch-102 neighbours.
- `../a098569-self-modified-ascents/`: self-modified ascent sequences
  (positive-diagonal tables, A098569/A121690), a different model on an
  `N log N` scale; no shared theorem.
- `../a126764-lconvex-polyominoes/` cites the Guttmann–Kotěšovec paper on
  201-avoiding ascent sequences; it does not treat A202058.
- Every inverse in this report uses the Lambert-W approximation
  `x = y/W(y/(eT))`, the solution of `x log(x/(eT)) = y`. After taking
  logarithms this is the case `a = b = 1` of the exact Lambert-core theorem
  `p0:thm:lambert-core` of the transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  No novelty is claimed for the inversion method.
- **No formal status.** No Lean or Rocq declaration in the repository
  states or proves any result of this report. No declaration was delivered
  with it either. Its place in the `SetTheory/Cardinals` report collection
  confers no formal status.

## Building

From a copy of this directory with `figures/` alongside:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

This uses pdfLaTeX with amsmath, amssymb, amsthm, mathtools, graphicx,
booktabs, array, enumitem, hyperref, xurl, lmodern and microtype. The
build at the batch-102 write (MiKTeX, 5 October 2026) gave 101 pages
(front matter 1–11, Part I 12–20, Part II 21–39, Part III 40–61, Part IV
62–75, Part V 76–101, references 101), with 0 errors, 0 undefined
references or citations, 0 multiply defined labels, 0 duplicate PDF
destinations and 0 overfull boxes. Three underfull boxes remain, in the
bibliography's URL lines, as in the build of the committed text. Build in a scratch directory and
copy back only `article.pdf`.
