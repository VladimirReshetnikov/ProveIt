# Five OEIS Asymptotic Conjectures for Distinct-Partition Norms

**Proofs, all-orders logarithmic expansions, exact-saddle corrections, inverse and extreme-value laws, eventual log-concavity and Jensen hyperbolicity, convolution powers for ∏(1 + k^α q^k)^μ, slot multiplicities ∏(1 + k^α q^k)^(k^β), the smooth lattice-minus-integral sector with exact-range inversion, and a critical theta window for growing powers: A022629, A092484, A265840, A265841, A265842, A022630, A022631, A266891**

This research report is dated 1 October 2026. It was built from five
manuscripts of ProveIt's incoming-reports intake, all written independently
on that day: two of batch 73O1 (cluster O1 of batch 73), merged on
1 October, two of batch 75 and one of batch 77 (cluster P2), merged on
2 October 2026. All five prove the same core theorems for the same real
family (source 48's A022629 is source 40's α = 1; sources 48 and 75-01 call
the power `s`, source 75-06 calls it `r`; source 77-51 proves all orders for
α = 1 and the first two orders for every α), with identical coefficients.
Each shared theorem is printed once and credited; the batch-75 and batch-77
duplicates are recorded in two tables (Tables 2 and 6) with pointers rather
than reprinted, and only genuinely different proofs and forms are kept as
marked second routes. No manuscript is superseded: each has results the
others lack.

**Batch 100 (5 October 2026).** Three more manuscripts, Research Reports 82,
89 and 93 of the session bundle of Reports 1–243 (arrival `60f54ea06`,
placement `36571ae0e`), were added as Sections 21 and 22. They are one author
series written on 1–2 October 2026, each building on the one before, and are
called by their bundle report numbers (sources 100-82, 100-89, 100-93),
because the cluster-local numbers 01–03 of batch 100 are used by other
clusters. Sources 100-82 (A022629) and 100-89 (every real α > 0) are this
report's sixth and seventh proofs of the core theorems, recorded once in
Table 8; their new material is Section 21, merged with source 100-89 as the
base. Source 100-93 treats powers growing with n and is Section 22. None of
the three saw this report, and none is superseded.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| base | batch 73O1, no. 40 | `OEIS_Distinct_Partition_Norms.zip` (`f8c3a392a`); `article.tex`, *Five OEIS Asymptotic Conjectures for Distinct-Partition Norms*, 22-page PDF | `1f1981f68` | `9df4ba51a` | the whole text, in its order (Sections 1–14, Appendix A) |
| member | batch 73O1, no. 48 | `A022629_Research_Package.zip` (`3a9518c52`); `article.tex`, *The A022629 Conjecture: All-Orders Logarithmic Asymptotics, Saddle-Point Expansions, Inverse Growth, and the Largest Part of a Weighted Partition*, 20-page PDF | `dc1a7242d` | `9df4ba51a` | second proofs and credits throughout; Section 3.1, Sections 6.1, 7.3, 8.1–8.2, 9.1, 10.3, 12.5, 13.1, part of Appendix B, Appendix C |
| addition | batch 75, no. 01 (source 75-01) | `A022629_research_package.zip` (`4b874cea0`); `article.tex`, *Norm-weighted distinct partitions: A proof of the A022629 growth conjecture, all-order asymptotics, Lambert inversion, and eventual Jensen hyperbolicity*, 20-page PDF | `29aca108e` | `6ea60e367` | Table 2 and Section 15.2; Sections 16–17; Section 19 (75-01.1–10); files prefixed `75-01-jensen-` |
| addition | batch 75, no. 06 (source 75-06) | `OEIS_Norm_Weighted_Partitions.zip` (`4b874cea0`); `article.tex`, *Norm-weighted distinct partitions: A022629, all-order expansions, and inversion*, 26-page PDF | `29aca108e` | `6ea60e367` | Table 2 and Section 15.2; the second proof of Lemma 16.1; Section 18; Section 19 (75-06.1–12); files prefixed `75-06-powers-` |
| addition | batch 77, no. 51 (source 77-51) | `oeis-fixed-power-asymptotics-result.zip` (`096ee7b87`; no wrapper directory); `article/fixed-power-partition-asymptotics.tex`, *Asymptotic expansions and inversion for fixed power weighted partitions*, 11-page PDF | none | `aa7345800` | Section 20: Table 6, Proposition 20.1 and the routes of Section 20.2, Theorem 20.2, Corollary 20.3 (A266891), Table 7, questions 77-51.1–4; files prefixed `77-51-fp-` |
| addition (base of Section 21) | batch 100, Report 89 (source 100-89) | `ProveIt_Power_Weighted_Distinct_Partitions_Relative_Expansions.zip` (`60f54ea06`); `power_weight_relative/article.tex`, *Relative Expansions and Exact Range Inversion for Power Weighted Distinct Partitions*, 9-page PDF | none | `36571ae0e` | Table 8; Theorem 21.2 with Lemma 21.3 (holomorphy, completed at the write), the closed forms (21.12)–(21.16), Theorem 21.4, Corollary 21.6, Proposition 21.7 (completed at the write), Theorem 21.8, routes of Section 21.5, Table 9 (right), questions 100.1–100.7; files prefixed `100-89-boundary-` |
| addition | batch 100, Report 82 (source 100-82) | `ProveIt_OEIS_A022629_Asymptotics_and_Inversion.zip` (`60f54ea06`); `a022629_asymptotics/article.tex`, *Asymptotics and Inverse Growth for Weighted Distinct Partitions*, 7-page PDF | none | `36571ae0e` | Table 8; Proposition 21.1 (P_9, P_10, Δ_9, Δ_10, from its JSON record); (21.20), the case α = 1 of Corollary 21.6, with its proofs in Section 21.5; Remark 21.9; Table 9 (left); files prefixed `100-82-integral-` |
| addition | batch 100, Report 93 (source 100-93) | `ProveIt_Critical_Theta_Power_Weighted_Distinct_Partitions.zip` (`60f54ea06`); `critical_power_theta/article.tex` with `diagnostics.tex`, `context.tex` and `references_extra.tex`, *Critical Theta Asymptotics and Inversion for Power Weighted Distinct Partitions*, 13-page PDF | `6591a56b3` | `36571ae0e` | Section 22: Theorem 22.1, Corollary 22.2, Lemmas 22.3–22.6, Corollary 22.7, Proposition 22.8, Theorem 22.9, Proposition 22.11, Table 10, questions 100-93.1–6; files prefixed `100-93-theta-` |

Author lines as delivered: source 40, "Research report prepared for Vladimir
Reshetnikov" (no AI wording); source 48, the same, with "Developed with AI
assistance; proofs and computations supplied for review"; source 75-01,
"Research report prepared for Vladimir Reshetnikov" (empty PDF author field,
no AI wording); source 75-06, "Prepared for Vladimir Reshetnikov" (PDF
author "Research report prepared for Vladimir Reshetnikov", no AI wording);
source 77-51, "Research report" (PDF author the same, no AI wording).
The pins are ProveIt commits of 1 October 2026
(`1f1981f682b2878bde51a6ad40c22777f362fc05`,
`dc1a7242d2ab4a4496b7dfee63256ee767b21fc9`, and
`29aca108ed25d714f31b1316512777fbbdc8e006` for both batch-75 sources);
source 77-51 names no ProveIt commit (its approval records name only the
producer's working directory) and records no repository search;
source 48 calls its identifier a "tree response" and says it does not pin
every later read. The batch-75 pin already held the archives of sources 40
and 48, unopened, and predates their placement, so source 75-01's "A
repository code search for A022629 returned no match" is stale; the article
says so (Sections 1.3 and 15.1). No source cites another, and their texts
share 0.4–1.4 % of their word 8-grams pairwise (source 40/48: 0.4 %; the
batch-75 pairs: 0.55–1.41 %): they are independent. Source 75-01 is not a
version of source 48, although the archive names differ only in letter case.
Source 77-51 shares 0.69 % / 0.11 % of its word 8-grams with this report.
Each placement commit deleted its archives, which survive in the arrival
commits.

Sources 100-82, 100-89 and 100-93 carry the author line "Research note
prepared for Vladimir Reshetnikov with OpenAI" (also their PDF author).
Sources 100-82 and 100-89 name no ProveIt commit and record no repository
search; source 100-93 pins `6591a56b3551e08700aef333cb98849c8cdfe69e`
(1 October 2026, 18:55 PDT), eighteen minutes before this report's first
placement (`9df4ba51a`), and pins source 100-89 by the SHA-256 of its archive
(`225b2070…`, which matches). They share 1.12 %, 0.63 % and 0.15 % of their
word 8-grams with this report as it stood before batch 100, and 0.6–2.8 % with
each other (status lines, preambles, standard displays). No "prepared for
private review" line, personal path or third-party data file occurs in them.

**Status: AI-assisted (source 48 says so, and sources 100-82, 100-89 and
100-93 say "with OpenAI"; sources 40, 75-01, 75-06 and 77-51 do not say),
unrefereed, not formalized.** For batch 73O1 the intake recomputed the
A022629 table to n = 6400, re-derived P_1–P_8 and the inverse coefficients by
a third route (a Sommerfeld expansion), recomputed source 48's operator
series and coordinate change in exact arithmetic, and compared the two Gumbel
centrings numerically. For batch 75 it checked in exact rational arithmetic
that source 75-06's b_j(6c) = P_j(c) for j ≤ 8 and source 75-01's
c_j(6c) = P_j(c) for j ≤ 5, recomputed the inverse coefficients Δ_2–Δ_8 from
the report's own inverse equation (they equal source 75-06's d_j(6c), and
source 75-01's through order 5), compared source 75-01's exact tables with
the earlier ones, confirmed the OEIS names and first fifteen terms of A022630
and A022631 and the definition of A297321, and reran every batch-75 program
on copies (below). For batch 77 it checked in exact arithmetic that source
77-51's d_3, d_4, b_4, b_5 are P_3, P_4, Δ_4, Δ_5 at α = 1 and that its
family theorem at β = 0 reproduces P_1 = P_2 = c and Δ_2 = Δ_3 = −2c;
computed ∏(1 + kq^k)^k through q^12 (its first ten coefficients are the
A266891 prefix recorded in the delivery; the OEIS entry was not re-fetched);
converted source 77-51's relative errors to the convention of Table 3 and
found them equal to source 75-01's and 75-06's at n = 200, 1000, 2000
to within one unit in the last printed digit; and reran its producer check and three independent checkers on
copies (below). It did not referee every proof.
For batch 100 the intake checked in exact rational arithmetic that source
100-82's recorded s_1–s_8 and v_2–v_8 are P_1–P_8 and Δ_2–Δ_8 at P = π² = 6c;
reran source 75-06's `formal.py` at order 10, whose orders 9 and 10 agree
exactly with source 100-82's s_9, s_10, v_9, v_10 (Proposition 21.1);
confirmed source 100-89's six printed boundary constants by fitting the
directly computed lattice-minus-integral difference (and its ξ_0, ξ_1 at
α = 1.5, 2.5, 3); checked source 100-93's main proof chain at placement;
evaluated source 100-93's theta formula at the fixed-α saddles of Section 12
and decomposed those finite-size residuals into Fourier cells (Section 16.3;
numerical evidence only); and reran the batch-100 programs on copies (below).
It did not referee every proof.

## Files

```
README.md                                          this guide
article.tex                                        the merged report (pdfLaTeX, internal bibliography)
article.pdf                                        the compiled report, 100 pages (title page, then pages 1-99)
48-a022629-PROVENANCE.md                           source 48's sources and verification record, as delivered
75-01-jensen-BUILD_AND_VALIDATION.txt              source 75-01's build and computation record, as delivered
75-01-jensen-OEIS_PROPOSED_NOTES.md                source 75-01's draft OEIS notes (not submitted), as delivered
75-06-powers-proposed_oeis_updates.txt             source 75-06's draft OEIS notes (not submitted), as delivered
77-51-fp-QA.md                                     source 77-51's visual review of its delivered 11-page PDF
77-51-fp-INTEGRATED_REVIEW.md                      source 77-51's integrated transcription review (audits/INTEGRATED_REVIEW.md)
77-51-fp-ind-AUDIT.md                              source 77-51's independent audit of the A022629 core (audits/independent/)
77-51-fp-ind-FAMILY_AUDIT.md                       its independent audit of the slot family
77-51-fp-ind-LOG_HIERARCHY_AUDIT.md                its independent audit of the logarithmic hierarchy
77-51-fp-ind-SOURCE_CHECK.md                       its supplementary OEIS and literature source check
77-51-fp-proofs-ALL_LOG_ORDERS.md                  source 77-51's proof snapshots (proofs/): all logarithmic orders
77-51-fp-proofs-EXACT_SADDLE_EXPANSION.md          exact-saddle expansion
77-51-fp-proofs-FIXED_POWER_FAMILY.md              slot family
77-51-fp-proofs-LEADING_AND_INVERSE.md             leading term and inverse
77-51-fp-proofs-THERMAL_CORRECTION.md              thermal correction
100-93-theta-diagnostics-README.md                 source 100-93's computational README for its diagnostics (checks/diagnostics/README.md)
code/40-norm-moments-verify.py                     exact sequences (alpha = 1..5, n <= 5000), recurrence check, saddle/Edgeworth diagnostics
code/40-norm-moments-derive_series.py              symbolic boundary derivatives and P_j (SymPy)
code/40-norm-moments-derive_inverse.py             symbolic reversion through six inverse orders (SymPy)
code/40-norm-moments-check_continuum.py            continuum quadrature check of the P_8 limit (mpmath)
code/40-norm-moments-check_resonances.py           product moduli at the first resonance (reads diagnostics.csv)
code/48-a022629-coefficients.py                    source 48's operator construction of six forward and six inverse coefficients
code/48-a022629-verify.py                          source 48's exact table to n = 6400 and saddle diagnostics
code/48-a022629-Makefile                           source 48's pdf/verify/clean targets (delivery layout; see below)
code/75-01-jensen-verify.py                        source 75-01's exact tables, log-concavity audits, saddle and Edgeworth comparisons (mpmath)
code/75-01-jensen-derive_series.py                 source 75-01's exact check of five forward and five inverse coefficients (SymPy)
code/75-01-jensen-extra_checks.py                  source 75-01's divisor recurrence, exact Jensen root counts, 40/60-digit comparison, Gaussian inverse
code/75-06-powers-formal.py                        source 75-06's exact formal algebra over Q[u]: eight forward, seven inverse coefficients
code/75-06-powers-numerics.py                      source 75-06's exact A022629 coefficients to 10000 and floating-point saddle estimates (NumPy, SciPy)
code/75-06-powers-checks.py                        source 75-06's recurrence and convolution checks (imports numerics)
code/77-51-fp-producer-check.py                    source 77-51's exact A022629 coefficients (2,001), monotonicity, factorial bounds, saddle numerics
code/77-51-fp-producer-generate_log_series.py      source 77-51's symbolic d_1..d_6, b_2..b_7 (SymPy)
code/77-51-fp-ind-check.py                         source 77-51's independent core checker (standard library)
code/77-51-fp-ind-check_family.py                  its independent family checker (standard library)
code/77-51-fp-ind-check_log_hierarchy.py           its independent hierarchy checker (standard library)
code/77-51-fp-verify.py                            source 77-51's root driver (delivery layout only; see below)
code/77-51-fp-build.sh                             source 77-51's PDF build (builds the unshipped manuscript)
code/100-82-integral-check_formal_series.py        source 100-82's exact formal series: s_1..s_10, v_2..v_10 in P = pi^2, residuals to order 12 (SymPy)
code/100-82-integral-check_coefficients_independent.py  its independent check of the printed coefficients (SymPy)
code/100-82-integral-check_finite_coefficients.py  exact A022629 to n = 10000 and integral-saddle comparisons at n = 100, 1000, 10000 (mpmath)
code/100-82-integral-check_integral_constant.py    numerical illustration of the constant (1/2) log(2 pi) - 1 (mpmath)
code/100-82-integral-run_checks.sh                 source 100-82's exact-check driver (delivery layout)
code/100-89-boundary-check_corrections.py          source 100-89's exact boundary coefficients at power 1 and Gaussian blocks (SymPy)
code/100-89-boundary-check_reconstruction.py       independent cumulant and weighted-profile reconstruction (SymPy)
code/100-89-boundary-check_integer_roots.py        rational reconstructions at the square-weight roots and the Gamma constant (SymPy)
code/100-89-boundary-check_boundary.py             numerical boundary illustration (mpmath)
code/100-89-boundary-check_relative_numeric.py     exact DP to n = 3000 and integral comparisons, alpha = 1, 2, 3 (mpmath)
code/100-89-boundary-verify_numeric_examples.py    independent recurrence and 65-digit log-coordinate quadrature for its table (mpmath)
code/100-89-boundary-run_checks.sh                 source 100-89's exact-check driver (delivery layout)
code/100-93-theta-check_identities.py              source 100-93's eight exact identities (SymPy)
code/100-93-theta-run_checks.sh                    source 100-93's check driver (delivery layout)
code/100-93-theta-diag-diagnostics.py              its Fourier diagnostics (NumPy, SciPy, mpmath)
code/100-93-theta-diag-error_diagnostics.py        its omitted-arc envelope checks (rewrites its input file)
code/100-93-theta-diag-assemble_summary.py         merges the result files into the summary JSON and TSV
code/100-93-theta-diag-prepare_quad113.py          writes the binary128 inputs and quadrature nodes
code/100-93-theta-diag-quad113.cpp                 independent binary128 full-product audit (g++, libquadmath)
code/100-93-theta-diag-verify_summary.py           consistency checks of the 18 saved rows (standard library)
data/40-norm-moments-A022629_computed.txt          a(n), n = 0..5000, alpha = 1 (and A092484, A265840, A265841, A265842 below)
data/40-norm-moments-A092484_computed.txt
data/40-norm-moments-A265840_computed.txt
data/40-norm-moments-A265841_computed.txt
data/40-norm-moments-A265842_computed.txt
data/40-norm-moments-diagnostics.csv               exact versus saddle comparisons, all five alphas
data/40-norm-moments-diagnostics_alpha1.csv        the same, per alpha (alpha1 ... alpha5)
data/40-norm-moments-diagnostics_alpha2.csv
data/40-norm-moments-diagnostics_alpha3.csv
data/40-norm-moments-diagnostics_alpha4.csv
data/40-norm-moments-diagnostics_alpha5.csv
data/40-norm-moments-continuum_diagnostics.csv     continuum checks of the P_8 limit
data/40-norm-moments-continuum_run.txt             its console transcript
data/40-norm-moments-resonance_diagnostics.csv     product moduli at theta = 2 pi / M
data/40-norm-moments-formal_coefficients.txt       symbolic P_j
data/40-norm-moments-series_run.txt                its console transcript
data/40-norm-moments-inverse_coefficients.txt      symbolic E and E^2
data/40-norm-moments-inverse_run.txt               its console transcript
data/40-norm-moments-run_alpha1.txt                verify transcripts (alpha 1; 2-3; 4-5)
data/40-norm-moments-run_alpha23.txt
data/40-norm-moments-run_alpha45.txt
data/40-norm-moments-requirements.txt              mpmath>=1.3.0, sympy>=1.12
data/48-a022629-exact_coefficients.csv             a(n), n = 0..6400, alpha = 1
data/48-a022629-formal_coefficients.json           six forward and six inverse polynomials
data/48-a022629-numerical_checks.json              saddle, variance, cumulants, residuals, cutoffs, errors (n = 100, 400, 1600, 6400)
data/48-a022629-saddle_table.tex                   generated table fragment (not \input by the article)
data/48-a022629-requirements.txt                   mpmath==1.3.0, sympy==1.14.0
data/75-01-jensen-exact_s1.json                    a(n), n = 0..10000, alpha = 1, as decimal strings
data/75-01-jensen-exact_audit_s1.json              strict-log-concavity failures and monotonicity, alpha = 1 (n <= 10000)
data/75-01-jensen-exact_audit_s2.json              the same, alpha = 2 (n <= 2500)
data/75-01-jensen-exact_audit_s3.json              the same, alpha = 3 (n <= 2500)
data/75-01-jensen-saddle_s1_dps40.csv              relative errors for J = 0..3, inverse displacements, log-expansion errors (alpha = 1)
data/75-01-jensen-saddle_s1_dps60.csv              the n = 10000 row at 60 digits
data/75-01-jensen-saddle_s2_dps40.csv              the same, alpha = 2 (n = 1000, 2500)
data/75-01-jensen-saddle_s3_dps40.csv              the same, alpha = 3 (n = 1000, 2500)
data/75-01-jensen-extra_checks.json                recurrence result, Jensen root counts, 40/60-digit difference, Gaussian inverse
data/75-01-jensen-symbolic.txt                     symbolic coefficient output
data/75-01-jensen-symbolic_run.txt                 derive_series console transcript
data/75-01-jensen-requirements.txt                 mpmath==1.3.0, sympy==1.14.0
data/75-06-powers-formal_coefficients.json         eight forward and seven inverse polynomials in u
data/75-06-powers-a022629_exact.json               selected exact A022629 coefficients up to n = 10000
data/75-06-powers-numerical_results.json           saddle results; exact comparisons to n = 10000, saddle-only estimates at 10^6, 10^8, 10^10
data/75-06-powers-verification_results.json        checks.py summary and software versions
data/75-06-powers-source_audit.json                source 75-06's inspected OEIS entries, conjecture dates and repository tree
data/75-06-powers-requirements.txt                 numpy==2.3.5, scipy==1.17.0, sympy==1.14.0
data/77-51-fp-producer-verification.json           source 77-51's producer receipt
data/77-51-fp-producer-log_series_verification.json  its symbolic receipt
data/77-51-fp-ind-verification.json                its independent core receipt
data/77-51-fp-ind-family_verification.json         its independent family receipt
data/77-51-fp-ind-log_hierarchy_verification.json  its independent hierarchy receipt
data/77-51-fp-ind-approval.json                    approval of the core proof (pins delivered files)
data/77-51-fp-ind-family_approval.json             approval of the family proof
data/77-51-fp-ind-log_hierarchy_approval.json      approval of the hierarchy proof
data/77-51-fp-ind-source_check.json                source-check receipt
data/77-51-fp-ind-negative-control.txt             expected stderr under python -O (delivered as optimization-negative-control.txt)
data/77-51-fp-ind-family-negative-control.txt      the same, family checker (delivered as family-optimization-negative-control.txt)
data/77-51-fp-ind-log-hierarchy-negative-control.txt  the same, hierarchy checker (delivered as log-hierarchy-optimization-negative-control.txt)
data/77-51-fp-integrated-approval.json             integrated approval (pins the delivered tex and PDF)
data/77-51-fp-root-integrated-approval.json        root integrated approval
data/77-51-fp-requirements.txt                     mpmath>=1.3, sympy>=1.13
data/100-82-integral-check_formal_series.json      source 100-82's exact forward and inverse coefficients (P_9, P_10, Delta_9, Delta_10 at P = 6c)
data/100-82-integral-check_coefficients_independent.json  its independent check record
data/100-82-integral-check_finite_coefficients.json  its exact values and integral-saddle comparisons
data/100-82-integral-PROVENANCE.json               source 100-82's provenance record (hashes its delivered files)
data/100-89-boundary-check_corrections.json        source 100-89's boundary coefficients and Gaussian blocks
data/100-89-boundary-reconstruction.json           its reconstruction record
data/100-89-boundary-check_integer_roots.json      its integer-root record
data/100-89-boundary-check_relative_numeric.json   its table values (35 digits)
data/100-89-boundary-verify_numeric_examples.json  its independent 65-digit check of the table
data/100-89-boundary-PROVENANCE.json               source 100-89's provenance record (hashes its delivered files)
data/100-93-theta-check_identities.json            source 100-93's identity record
data/100-93-theta-PROVENANCE.json                  source 100-93's provenance record (hashes its delivered files)
data/100-93-theta-diag-results.json                main diagnostics run (powers 12-48, lambda = 4, 5)
data/100-93-theta-diag-initial.json                the a = 8 run
data/100-93-theta-diag-lambda4_checked.json        checked snapshots of the concurrent runs (lambda4_checked, lambda5_checked,
data/100-93-theta-diag-lambda5_checked.json          lambda5_early, lambda5_a48, lambda5_a48_checked)
data/100-93-theta-diag-lambda5_early.json
data/100-93-theta-diag-lambda5_a48.json
data/100-93-theta-diag-lambda5_a48_checked.json
data/100-93-theta-diag-diagnostics_complete.json   all 18 rows with satellites, errors and omitted-arc estimates
data/100-93-theta-diag-diagnostics_table.tsv       the summary table (CRLF as delivered)
data/100-93-theta-diag-sensitivity_a8.json         sensitivity checks (a = 8; a = 12; extra satellites)
data/100-93-theta-diag-sensitivity_a12.json
data/100-93-theta-diag-satellite_sensitivity.json
data/100-93-theta-diag-a8_l4_phase0.txt            binary128 inputs (two cases)
data/100-93-theta-diag-a12_l5_phasehalf.txt
data/100-93-theta-diag-nodes96.txt                 60-digit Gauss-Legendre nodes (96, 128)
data/100-93-theta-diag-nodes128.txt
data/100-93-theta-diag-quad113_a8_96.txt           binary128 outputs (two cases, two node counts)
data/100-93-theta-diag-quad113_a8_128.txt
data/100-93-theta-diag-quad113_a12_l5_half_96.txt
data/100-93-theta-diag-quad113_a12_l5_half_128.txt
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. The eight `40-norm-moments-*.csv` files,
`data/48-a022629-exact_coefficients.csv` and the four
`data/75-01-jensen-saddle_*.csv` files are CRLF as delivered and are kept
byte for byte by `-text` lines in `SetTheory/Cardinals/.gitattributes`. So is
`data/100-93-theta-diag-diagnostics_table.tsv` (19 CRLF lines).
Delivered name → shipped path: source 40's `oeis_norm_partitions/X.py` →
`code/40-norm-moments-X.py`, `data/Y` → `data/40-norm-moments-Y`,
`requirements.txt` → `data/40-norm-moments-requirements.txt`, `article.tex` →
`article.tex` (rewritten in the merge), `README.md` → this README; source 48's
`A022629_Research/code/X.py` → `code/48-a022629-X.py`, `Makefile` →
`code/48-a022629-Makefile`, `data/Y` → `data/48-a022629-Y`,
`requirements.txt` → `data/48-a022629-requirements.txt`, `PROVENANCE.md` →
`48-a022629-PROVENANCE.md`; source 75-01's `A022629_research/code/X.py` →
`code/75-01-jensen-X.py`, `data/Y` → `data/75-01-jensen-Y`,
`requirements.txt` → `data/75-01-jensen-requirements.txt`,
`BUILD_AND_VALIDATION.txt` and `OEIS_PROPOSED_NOTES.md` →
`75-01-jensen-<name>`; source 75-06's `oeis_norm_weighted_partitions/X.py` →
`code/75-06-powers-X.py`, its JSON files and `requirements.txt` →
`data/75-06-powers-<name>`, `proposed_oeis_updates.txt` →
`75-06-powers-proposed_oeis_updates.txt`. Not shipped: the four PDFs, the
manuscripts and READMEs of sources 48, 75-01 and 75-06, source 40's
`SHA256SUMS.txt` (30/30 verified, retired), source 75-06's `SHA256SUMS.txt`
(14/14 verified, retired) and `build.sh` (it builds the unshipped
manuscript), and source 75-01's `data/exact_s2.json` and `data/exact_s3.json`
(α = 2, 3 to n = 2500; value-identical to source 40's A092484 and A265840
tables on that range, and regenerated in seconds; see the rerun recipe).
Source 77-51 (archive without a wrapper directory): `QA.md`, `build.sh`,
`verify.py`, `requirements.txt` → `77-51-fp-<name>`, `code/77-51-fp-<name>`
or `data/77-51-fp-<name>`; `audits/X` → `77-51-fp-X` (`.md`) or
`data/77-51-fp-X`; `audits/independent/X` → `77-51-fp-ind-X` (`.md`),
`code/77-51-fp-ind-X` (`.py`) or `data/77-51-fp-ind-X`, with the three
`*-optimization-negative-control.txt` shortened to `*-negative-control.txt`;
`checks/producer/X` → `code/77-51-fp-producer-X` or
`data/77-51-fp-producer-X`; `proofs/X` → `77-51-fp-proofs-X`. Not shipped:
its manuscript (printed in Section 20), PDF, README and `SHA256SUMS` (36/36
verified, retired). All survive in the arrival commits.

Batch 100: source 100-82's `a022629_asymptotics/checks/X` →
`code/100-82-integral-X` (`.py`) or `data/100-82-integral-X` (`.json`), its
`run_checks.sh` → `code/100-82-integral-run_checks.sh`, `PROVENANCE.json` →
`data/100-82-integral-PROVENANCE.json`; source 100-89's
`power_weight_relative/…` likewise with the prefix `100-89-boundary-` (its
`checks/reconstruction.json` → `data/100-89-boundary-reconstruction.json`);
source 100-93's `critical_power_theta/checks/check_identities.*`,
`run_checks.sh` and `PROVENANCE.json` likewise with `100-93-theta-`, its
`checks/diagnostics/X` → `code/100-93-theta-diag-X` (`.py`, `.cpp`) or
`data/100-93-theta-diag-X`, and `checks/diagnostics/README.md` →
`100-93-theta-diagnostics-README.md`. Not shipped: the three manuscripts
(printed in Sections 21–22) and source 100-93's `diagnostics.tex`,
`context.tex` and `references_extra.tex` (printed in Section 22), the PDFs and
READMEs, `verify_package.py` (identical in sources 100-82 and 100-89) and
`build_local.sh` (identical in sources 100-82 and 100-89, and equal to a
generic TeX helper already in the repository), source 100-89's
`checks/check_logarithmic_reversion.py` and `.json` (byte copies of source
100-82's `check_formal_series.py` and `.json`), and source 100-93's
`checks/diagnostics/SHA256SUMS.txt` (5/5 verified, retired); the three
provenance manifests verified 13/13, 19/19 and 39/39 at placement. All
survive in `60f54ea06`.

## Labels, structure and notation

Every label carries the prefix `dpn:`. The staged base had **84** labels; the
batch-73O1 merge added **44** (37 of source 48's labels under the sub-prefix
`dpn:48:`, 4 new `dpn:48:` names and 3 new `dpn:` labels): **128**. The
batch-75 merge renamed or deleted none of them and left every existing
section, theorem, equation and table number unchanged (checked against a
build of the previous text), and added **46**: 28 under `dpn:jh:` (source
75-01's sharp scales, threshold, log-concavity and Jensen material), 13 under
`dpn:cp:` (source 75-06's convolution powers) and 5 `dpn:` labels for the
merge sections and the duplicates table (`sec:b75`, `sec:b75dup`,
`sec:b75routes`, `sec:b75questions`, `tab:b75dup`): **174**. The batch-77
merge again renamed or deleted none and left every existing section,
theorem, equation and table number unchanged (checked against a build of the
previous text), and added **21**, all under `dpn:fp:` (source 77-51's
Section 20: 7 sections, 2 tables, 1 proposition, 1 theorem, 1 corollary,
9 equations): **195** in all. The batch-100 merge again renamed or
deleted none and left every existing section, theorem, equation and table
number unchanged (checked against a build of the previous text), and added
**116**: 46 under `dpn:rb:` (Section 21: 9 section and subsection labels,
2 tables, 3 theorems, 2 propositions, 1 lemma, 1 corollary, 2 remarks,
26 equations) and 70 under `dpn:ct:` (Section 22: 12 section labels, 1 table,
2 theorems, 2 propositions, 4 lemmas, 2 corollaries, 1 remark,
46 equations): **311** in all. The batch-75, batch-77 and batch-100 sources'
own labels were not carried over: their shared results are pointers, and their new
results were rewritten in this report's notation.

Section 1.4 says what came from where; Section 1.5 has the notation tables.
This report's notation (source 40's) is used throughout, and the other four
sources are translated into it. The collisions that matter: the power is α
here, `s` in sources 48 and 75-01 and `r` in source 75-06; source 75-06's `s`
is the number of layers, here μ; this report's `s` is the log transition
coordinate −W₋₁(−t/α) (source 48's and 75-01's `L`, source 75-06's `v`);
source 48's `r` and source 75-06's `K` are the transition site (here M),
while `r` here is log √(2n); sources 48's and 75-01's `K` are truncation
orders; source 75-01's ε = 1/(αMs) is written ε♯ here, beside ε = s/M;
source 75-01's cumulant polynomials `P_j(p)` are not the coefficients
`P_j(c)`, and source 75-06's `b_j(u)` are the coefficients, not the cumulant
polynomials `b_j(p)`; source 75-06's `d(v)`, `d_j(u)` and source 48's `d_s(λ)`
are not `d_α(s)`; source 75-01's `x_0(A)` (Gaussian inverse, here n_*) is not
source 48's `x_0` (= K_0); source 75-01's Hermite `H_d` is written 𝖧_d, since
`H` is the transition width. Source 77-51's `s = log y` is the log threshold
Y here, not the transition coordinate s (its ℓ); its `μ(t)` is the mean, not
the layer count μ; its `m`, `L` are K, r; its `d_j`, `b_j` are P_j(π²/6),
Δ_j(π²/6), not source 75-06's `d_j(u)`, `b_j(u)` nor the cumulant polynomials
b_j(p); its `E_R` includes the leading 1; its slot family is written
A^[β]_α with scale K^[β] = ((β+2)n)^(1/(β+2)), so as not to collide with
a_{α,μ} or with the Lambert datum K_0. Text added in the merges is marked
"[Merge note, batch 73O1.]", "[Merge note, batch 75.]" or "[Merge note,
batch 77.]"; dated notes on earlier text read "[Batch 75, 2 October 2026.]"
or "[Batch 77, 2 October 2026.]"; material from a single source is marked
"(source 48)", "(source 75-01)", "(source 75-06)" or "(source 77-51)". The
batch-75 material follows the conclusion as Sections 15–19 and the batch-77
material as Section 20, so that the earlier numbering is unchanged; merge
notes in the earlier sections point forward to it.

The batch-100 sources are translated by a fourth table in Section 1.5. The
collisions that matter: in all three, `K` is the transition site M (not
√(2n)), `b` is s, and `B` is log √(2n) (sources 100-82, 100-89) or a block of
sizes (source 100-93), never the variance; source 100-89's `c_r(a)` (here
ξ_r(α)) and source 100-82's `c_j` (= 2η(2j)) are not c = π²/(6α²); source
100-82's `t_n`, `N(t)`, `V(t)` belong to the saddle of the integral (here
t^int, B^int); source 100-89's `E_a(t)` is written Ξ_α(t), its `J_D` F_D,
and its Edgeworth order `M` is J − 1 here; source 100-93's `λ`, `μ`, `Q`,
`R`, `U`, `C`, `V`, `T_r`, `W`, `z` are Λ, μ_R, Q_⊥, R_{≥2}, B_RR, B_RS, B,
𝖳_r, H and K; its Θ(μ, Q) = (2πQ)^{−1/2} ϑ(1/Q, μ) in terms of the
lattice-peak report's ϑ. Text added in that merge is marked "[Merge note,
batch 100.]", dated notes "[Batch 100, 5 October 2026.]", and statements and
proofs supplied by the write rather than by a source "[write]". The
batch-100 material is Sections 21 and 22, after Section 20 and before the
appendices.

## What is claimed

For every fixed real α > 0, with K = √(2n), r = log K, c = π²/(6α²), and M,
s the exact-saddle transition site and its logarithm:

- The Kotesovec conjectures log a_α(n) ~ α√(n/2)(log 2n − 2) for A022629,
  A092484, A265840, A265841, A265842 hold, with the sharper additive form
  log a_α(n) = αK(r − 1) + O(K/r) (all four sources; sources 48, 75-01 and
  75-06 give further elementary routes).
- All fixed orders of log a_α(n) = αK(r − 1 + Σ P_j(c) r^{−j}), with
  P_1–P_7 printed and P_8 computed (source 40), and two generating
  algorithms: source 40's Lagrange-inversion route and source 48's
  differential operator. Sources 48, 75-01 and 75-06 print P_1–P_6, P_1–P_5
  and P_1–P_8; source 75-06's exact rational P_8 confirms source 40's, which
  was checked only numerically before.
- The exact-saddle multiplicative expansion with all fixed Edgeworth orders,
  including control of noncentral arcs (all four), and, from source 75-01
  (with source 75-06 for the scales), its sharp form: signed cumulants
  κ_j ~ (j!/2)M^{j+1}/(αs)^{j−1}, relative error O((αMs)^{−J−1}) after J
  corrections, and first correction 𝓔_1 ~ −3/(8αMs).
- Lambert-W_0 inversion of the first index with log a_α(n) ≥ Y, through
  R_0^{−6} (sources 40, 48), R_0^{−5} (75-01) and R_0^{−8} (75-06; the
  coefficients of R_0^{−7} and R_0^{−8} are new), and (source 75-01)
  localization of that index to within 1 + o(1) of an exact-saddle Gaussian
  inverse, with displacement −3/(8α²s²)(1 + o(1)) at sequence values.
- Logistic occupation at the boundary, a Gumbel law for the largest part
  with exact-root centring (sources 40, 75-06) and explicit centring in
  log √(2n) (source 48), and L_n/√(2n) → 1 + 1/α.
- The fixed-resonance modulus −log|φ_t(2πℓ/M)| ~ 2π⁴ℓ²M/(3α³s³)
  (source 40).
- Source 48 only: the Taylor series of log ∏(1 + k^α q^k) at 0 has radius
  3^{−α/3}; log max weight = αK(r − 1) + O(r); and
  log(a_α(n)/max weight) ~ π²K/(6αr).
- Source 75-01 only: eventual strict log-concavity of a_α(n), with gap
  log(a(n)²/(a(n−1)a(n+1))) ~ α log √(2n)/(2n)^{3/2}; eventual hyperbolicity
  of the Jensen polynomials of each fixed degree, by verifying the hypotheses
  of the Griffin–Ono–Rolen–Zagier Hermite-limit criterion; exact data to
  n = 10000 (α = 1) with the strict-log-concavity failures (the last tested
  failure for α = 1 is n = 76) and exact Jensen root counts.
- Source 75-06 only: the convolution powers ∏(1 + k^α q^k)^μ for fixed
  integer μ ≥ 1 (A022630, A022631 and the positive columns of A297321 at
  α = 1): growth, all logarithmic orders with the same P_j in
  √(2n/μ), the relative expansion with first correction −3/(8μαMs), the
  threshold inversion, and the logistic and Gumbel laws with centring
  (μ/t)b^α e^{−tb} = 1.
- Source 77-51 only: the slot family ∏(1 + k^α q^k)^(k^β), α > 0 real,
  β ≥ 0 integer (Theorem 20.2): two logarithmic orders
  log a = αK^(β+1)(r/(β+1) − 1/(β+1)²) + π²K^(β+1)/(6α(r − 1)) + O(K^(β+1)/r³)
  with K = ((β+2)n)^(1/(β+2)), r = log K; the exact-saddle expansion to every
  fixed order with remainder O((s/M^(β+1))^(R+1)); the threshold inverse with
  its first correction; strict monotonicity. For (α, β) = (1, 1) this proves
  Kotěšovec's conjectured leading term n^(2/3)(2 log(3n) − 3)/(4·3^(1/3)) for
  **A266891** (Corollary 20.3). Also the resummed forms
  log a_α(n) = αK(r − 1) + π²K/(6α(r − 1)) + O(K/r³) and
  N_α(Y) = (K_0²/2)(1 − 2c/(R_0(R_0 − 1)) + O(R_0^{−4})) (Proposition 20.1:
  the same accuracy as the two-term truncations, not sharper), and a further
  citation (Naranjo–Ramírez 2026).
- Sources 100-82 and 100-89 (batch 100): the sixth and seventh proofs of the
  core theorems (Table 8), and new: **P_9, P_10, Δ_9, Δ_10** (Proposition
  21.1; source 100-82's exact record, confirmed by source 75-06's program at
  order 10); the lattice-minus-integral difference Ξ_α(t) extends smoothly
  to t = 0, uniformly on compact α-sets, with coefficients ξ_r(α) real
  analytic and holomorphic on Re α > 0 (Theorem 21.2; the holomorphy proof is
  completed in Lemma 21.3), closed forms such as ξ_0(1) = ½ log 2π − 1,
  ξ_0(2) = log(1 − e^{−2π}), ξ_1(1) = 7/12 − γ, ξ_1(2) = 1/12 − Re ψ(1 + i),
  and a finite digamma–Hurwitz rule for integer α; an all-orders relative
  expansion keeping the exact integral and finitely many ξ_r (Theorem 21.4,
  remainder at the conservative scale t^J; Remark 21.5 transfers the sharp
  scale of Section 16) and its first-order form at the saddle of the integral
  (Corollary 21.6; at α = 1 source 100-82's
  a(n) ~ exp(I(t) + nt − 1)/√(I''(t))); an all-orders exact-range inverse
  (Theorem 21.8: index recovery by rounding at sequence values, and the
  threshold off an O(t^{J−1})-neighbourhood of the integers; its slope bound
  is completed in Proposition 21.7).
- Source 100-93 (batch 100): for α growing so that Λ = α(s − 1)/M^{1/3}
  stays in a compact subset of (0, ∞) (equivalently
  α log √(2n)/(2n)^{1/6} → Λ_∞ ∈ (0, ∞)), the uniform relative equivalent
  a_α(n) = e^{F(t)+nt}(2πB)^{−1/2}{Θ(μ_R, Q_⊥) + o(1)}, with
  Θ(μ, Q) = Σ_j exp(−2π²Qj² − 2πijμ), μ_R the mean number of parts at least
  two and Q_⊥ → π²/(3Λ³) their variance after regression on the size
  (Theorem 22.1); so the single-Gaussian ratio has the two limits
  Θ(0, ·) > 1 and Θ(½, ·) < 1 along integer powers (Corollary 22.7); a
  theta-adjusted inverse with error o(M^{2/3}) and threshold brackets
  (Theorem 22.9); the leading logarithm αK(r − 1) and the Lambert inverse in
  the joint limit (Proposition 22.11). The satellites' damping is the action
  of Theorem 11.1, so in this window Section 22 supplies the secondary
  saddles, phases and cell contributions that Section 11 leaves open. The
  write adds the phase average ∫_0^1 Θ dμ = 1 and the theta shift
  −log Θ/t of the threshold (Remark 22.10: of order at most 1/t ≍ M^{2/3},
  and of exact order 1/t away from the two phases per period where
  log Θ(μ_R, Q_⊥) = 0, in particular near integer and half-integer μ_R).
- *[Independent check, 5 October 2026.]* An adversarial check made by the
  intake after the write found the five results the write supplied
  (Lemma 21.3, Proposition 21.7, Remark 21.5, the phase average (22.46) and
  Remark 22.10) valid, with no counterexample and no gap in any proof chain.
  Two wordings were corrected where they stand, with dated notes: Remark
  22.10 first said the threshold shift is "of exact order 1/t", false at the
  two zeros of log Θ per period (and the forward pointer in Section 16.4 said
  "of order M^{2/3}"); Remark 21.5 understated the saddle-displacement terms
  (relative variance change O(t^D s/M²), not O(t^D/B)), with the conclusion
  unchanged. The tests: exact coefficients of ∏(1 + k^α q^k) by a big-integer
  recursion to n = 4000 for α = 1, 2, 3 (A022629, A092484) and tilted binary64
  recursions for α = 1.5, 6, 8, 10; the boundary functional at complex α
  (Cauchy–Riemann to 10⁻¹¹, the printed ξ_r to 19–25 digits); the slope
  formula (21.23) to 5·10⁻¹¹; the residuals of Remark 21.5 on the sharp scale
  (J = 1 tends to −3/8 at α = 1); and the theta shift at exact lattice
  saddles (α = 8–32) and exact thresholds (α = 6, 8, 10). A careful reading
  with numerical tests, not a formal verification; recorded in a dated note
  at the end of Section 22.

## What is not claimed

- No complete multi-saddle coefficient transseries; the resonance theorem
  gives the modulus at a point, not the secondary saddles' contributions
  (source 40). *[5 October 2026, batch 100: in the critical window of growing
  powers source 100-93 computes them, with relative error o(1) and no
  effective constant (Section 22); for fixed α they remain open.]* No resolution of the smaller blocks or exponentially small
  contributions; no convergence of the inverse-logarithmic series
  (sources 48, 75-01, 75-06).
- No uniformity as α ↓ 0 (all); α = 0 is a different regime. No theorem for
  growing α, growing μ, or growing Jensen degree (75-01, 75-06); the
  diagonal A292190 is not covered. *[Corrected 5 October 2026, batch 100:
  growing α is now covered in the critical window α ≍ (2n)^{1/6}/log n,
  that is Λ = α(s − 1)/M^{1/3} in a compact subset of (0, ∞), by source
  100-93 (Section 22). No theorem is uniform as Λ → 0 or Λ → ∞; the diagonal
  A292190 (Λ → ∞) is still not covered; growing μ and growing Jensen degree
  remain uncovered.]*
- The sharp remainder O((αMs)^{−J−1}) is proved for one layer only; source
  75-06's μ-layer remainder uses the safe parameter s/M. The complete
  expansion of 𝓔_1 in 1/s, asked for by source 48's project 48.6, is not
  given; that question is only partly answered.
- The near-integer threshold localization is asymptotic: no universal
  rounding rule, no explicit constants, no certified finite-input algorithm
  (75-01). 77 is not proved to be the log-concavity threshold of A022629.
- The finite-size diagnostics are not interval-certified. At n = 5000 the
  central approximation is excellent for α = 1 but fails for α = 3, 4, 5
  (ratio about 1.58 at α = 5); fixed truncations of the logarithmic
  expansion do not improve monotonically at fixed n (source 40). The
  four-term logarithmic approximation is still off by about 3.55 in the
  logarithm at n = 6400 (source 48). At α = 3, n = 2500 the relative error
  stays near 5 % for J = 1, 2, 3 (source 75-01); the article identifies this
  as the noncentral contribution of the resonance section, not slow
  Edgeworth convergence, but neither source computes it. *[5 October 2026,
  batch 100: an uncertified cell-by-cell integration at n = 5000 puts those
  residuals in the Fourier cells around ±2π/M (and, for α = 4, 5, ±4π/M and
  beyond), Section 16.3; this is numerical evidence only. Source 100-93's
  theta formula does not explain them: it assumes a frozen lower bulk, which
  fails at fixed α, and evaluated with the exact moments it gives 1.0000,
  0.981 and 1.194 at α = 3, 4, 5 against 0.962, 1.231 and 1.581.]* Source 75-06's
  values at n = 10^6, 10^8, 10^10 are saddle estimates, not exact
  comparisons.
- Gikunda's 2026 dissertation treats a shrinking tilt and is not claimed to
  be superseded; Granovsky–Stark's theorem is not claimed to be
  inapplicable in every form; Kumar–Rana 2026 is flagged by source 75-01 for
  any priority review; the Hermite-limit mechanism is not new.
- Source 77-51: its saddle remainder O(w^{−R−1}), w = M/s, is the
  conservative scale, not source 75-01's sharp one; its exact-saddle inverse
  brackets are weaker than Theorem 16.4 and prescribe no rounding near an
  integer; its constants are not effective and "not asserted to be uniform
  as α ↓ 0 or β → ∞"; fractional slot multiplicities are outside its
  theorem; for β ≥ 1 only two logarithmic orders are proved (all orders only
  for A022629); "neither an exponentially complete transseries nor a
  literature-wide priority claim is asserted". Its four questions (77-51.1–4)
  remain open. Its proofs of the A022629 and A092484 conjectures are, here,
  the fifth.
- Sources 100-82 and 100-89: unrefereed, not Lean; no convergence of the
  boundary Taylor series or of the logarithmic series, no optimal truncation,
  no exponentially small lattice correction, no effective onset, no remainder
  uniform in the truncation order; uniform only on compact α-sets, not for
  growing α (that is Section 22); no unconditional rounding rule for
  arbitrary thresholds and no claim on how often thresholds fall near an
  integer; quadratures are orientation, not certificates ("Verified" in
  source 100-89's table caption means reproduced, not interval-certified);
  bounded literature comparisons, no priority claim. Source 100-89's
  remainder O(t^J) is the conservative scale, not the sharp one of
  Section 16; the sharp form in Remark 21.5 is the write's bookkeeping.
  Their "proves and strengthens the conjecture currently listed" (100-82)
  and "settles the current conjectures" (100-89) are, here, further proofs.
  Their open items are questions 100.1–100.7.
- Source 100-93: no effective onset; no nearest-integer recovery in its
  window (the inverse error o(M^{2/3}) may diverge); nothing uniform as
  Λ → 0 or Λ → ∞; no full series and no exponentially small remainders; its
  diagnostics are Fourier computations, not exact coefficients or interval
  enclosures, and its omitted-arc integrations are not certified. Its
  theorem is not a corollary of the lattice-peak transfer theorem of
  `a357825-theta-ballot-power-sums` Part II (the hypotheses (H1), (H2e) are
  unproved for its row; question 100-93.7). Its questions 100-93.1–6 remain
  open.
- No priority, no Lean or Rocq verification, and no OEIS submission (the
  three shipped OEIS-note files are drafts).

## Relation to neighbouring material

- **Sibling reports of batch 73O1** in this collection treat other partition
  products with the same saddle, Edgeworth and Lambert-W toolkit and prove no
  common proposition: [`a033552-catalan-partitions`](../a033552-catalan-partitions/)
  (parts in the Catalan numbers) and
  [`a097356-sqrt-restricted-partitions`](../a097356-sqrt-restricted-partitions/)
  (parts at most √N). [`a039831-two-fourier-peaks`](../a039831-two-fourier-peaks/)
  (batch 73O2) is a further sibling: a Fourier-peak and Lambert-W inverse
  study of another product.
- **Neighbours of batch 77.**
  [`a301746-divisor-weighted-asymptotics`](../a301746-divisor-weighted-asymptotics/)
  applies the same exact-saddle sum and consecutive-block lemma to
  ∏(1 + q^k)^(d(k)²) (source 77-51's sibling of the same day; its Part I's
  independent audit cites "the independently reviewed A022629 proof", which
  is `77-51-fp-ind-AUDIT.md` here).
  [`a291698-moving-fugacity-partitions`](../a291698-moving-fugacity-partitions/)
  treats distinct partitions with one global fugacity n^α, a different
  weighting with no result in common. Both pointers are dated notes in
  Section 20.
- **Lattice-peak transfer (batch 100).** Section 22 (source 100-93) is the
  Fourier-dual form of the lattice-peak transfer theorem of
  [`a357825-theta-ballot-power-sums`](../a357825-theta-ballot-power-sums/)
  Part II (written in `2b257ba94`): read with the row
  l ↦ P(S = n, R_{≥2} = l), r_n = 1, q_n = 1/Q_⊥, phase μ_R, its conclusion
  is Theorem 22.1, but it is not a corollary — (H1) is a fibre local limit
  theorem for (S, R_{≥2}) and (H2e) would need log-concavity in l, both
  unproved (question 100-93.7); Section 22.8 gives the dictionary. A
  reciprocal note in that report is proposed with this batch.
- **Neighbour of batch 100.**
  [`a271619-strict-twice-partitions`](../a271619-strict-twice-partitions/)
  records that its Part I Section 6 (near-modulus-one Fourier peaks) is the
  same phenomenon class as Section 22 here, for a different product, and that
  its two competing charges do not answer project 7; no theorem is shared.
  [Reciprocal notes, 5 October 2026, batch 100.] Its Part I's weight p(k)
  (A271619) is not regularly varying and gives two competing charges
  instead of one crossing, and its Part II's question 3 (A358836, Section
  27 there) is the counterpart of project 5; dated notes after projects 5
  and 7 here record both, and project 7 stays open.
- **Sibling of the same screen (5 October 2026, batch 100).** The source
  audit of [`a126348-stable-hilbert-series`](../a126348-stable-hilbert-series/)
  (bundle Report 84) screened A022629 and A266891 together with A126348;
  that report treats `∏(1 + qᵏ/(1 − q))`, a distinct-part product whose
  fugacity depends on `q` rather than on the part `k`, and cites the same
  Naranjo–Ramírez paper (*Integers* 26 (2026), A20). No shared theorem.
- **Transseries.** The partition-number chapter of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion`
  (`transseries_and_inversion.tex`, label `p3:sec:top`, A000041) is a
  methodological relative. Nothing is imported from it, and no manuscript
  builds a transseries in that volume's sense. The Lambert-W inversions and
  the threshold localization are instances of that volume's theorems
  `p0:thm:lambert-core`, `p0:thm:perturbed-inversion`,
  `p0:thm:backward-error` and `p0:thm:staircase`, which the batch-75 sections
  cite.
- **Lean.** No manuscript ships or cites Lean or Rocq proofs (batch 100's
  included), and no statement of this report is formalized; placement in the collection
  confers no formal status. The only formal statement the article cites is
  the separation step of the staircase theorem,
  `Fabius.staircase_separation` (with `Fabius.staircase_ceil`) in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, a
  general fact about ceilings that this report's threshold theorem uses but
  that does not formalize any of its analytic content.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf` (rebuilt for the
independent check of the batch-100 write, 5 October 2026, and again after the
batch-100 reciprocal notes the same day, with no label renumbered): 100 pages (an
unnumbered title page, then pages 1–99), with no errors, no warnings, no
undefined references or citations, no multiply defined labels, no duplicate
destinations and no overfull or underfull boxes. The title page is wrapped in
`\hypersetup{pageanchor=false}` … `pageanchor=true`. Copy back only
`article.pdf`.

## Rerunning the programs

Every program writes its outputs under the **delivered** names, relative to
its own location: source 40's scripts write to `data/` beside themselves (run
from `code/` they would create `code/data/`); source 48's and source 75-01's
write to `../data/` (run from `code/` they would add unprefixed files to the
shipped `data/`); source 75-06's write beside themselves (into `code/`).
Three programs import a sibling by its delivered name:
`75-01-jensen-extra_checks.py` imports `verify`, `75-06-powers-checks.py`
imports `numerics`, and `check_resonances.py` reads `data/diagnostics.csv`.
So rerun on a copy laid out as delivered:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a022629-distinct-partition-norms
W=$(mktemp -d); mkdir -p "$W/40" "$W/48/code" "$W/01/code" "$W/01/data" "$W/06"
for f in "$R"/code/40-norm-moments-*.py; do cp "$f" "$W/40/${f##*/40-norm-moments-}"; done
for f in "$R"/code/48-a022629-*.py;      do cp "$f" "$W/48/code/${f##*/48-a022629-}"; done
for f in "$R"/code/75-01-jensen-*.py;    do cp "$f" "$W/01/code/${f##*/75-01-jensen-}"; done
for f in "$R"/data/75-01-jensen-*;       do cp "$f" "$W/01/data/${f##*/75-01-jensen-}"; done
for f in "$R"/code/75-06-powers-*.py;    do cp "$f" "$W/06/${f##*/75-06-powers-}"; done
U="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
V="uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 --with sympy==1.14.0 python"
(cd "$W/40" && $U verify.py --max-n 5000 --dps 50 && $U derive_series.py && $U derive_inverse.py \
             && $U check_continuum.py && $U check_resonances.py)    # about 85, 79, 66, 51, 13 s
(cd "$W/48" && $U code/coefficients.py --order 6 && $U code/verify.py --max-n 6400 --dps 45)   # about 83, 46 s
(cd "$W/01" && for s in 1 2 3; do n=2500; [ $s = 1 ] && n=10000; $U code/verify.py --exact --s $s --nmax $n; done \
            && $U code/verify.py --s 1 --dps 40 \
            && $U code/verify.py --s 2 --samples 1000,2500 --dps 40 \
            && $U code/verify.py --s 3 --samples 1000,2500 --dps 40 \
            && $U code/derive_series.py && $U code/extra_checks.py)  # about 41 s (exact tables), 48 s (three saddle runs), 89 s, 14-70 s
(cd "$W/06" && $V formal.py --order 8 && $V checks.py && $V numerics.py)   # about 7, 13, 32 s
```

Compare `$W/40/data/<name>` with `data/40-norm-moments-<name>`,
`$W/48/data/<name>` with `data/48-a022629-<name>`, `$W/01/data/<name>` with
`data/75-01-jensen-<name>`, and `$W/06/<name>` with
`data/75-06-powers-<name>`. The intake's runs matched every shipped file:
the CSVs byte for byte, source 75-01's `exact_s1.json` byte for byte, and the
other text and JSON outputs up to line endings (on Windows, Python text mode
writes CRLF where the delivered files are LF) or, for
`numerical_results.json`, last-place floating-point differences. The console
transcripts `*_run.txt` are the scripts' standard output. Notes:

- Source 75-01's `extra_checks.py` reads `exact_s1.json`, `exact_s2.json`,
  `exact_s3.json`, `saddle_s1_dps40.csv` and `saddle_s1_dps60.csv` from
  `data/`. The α = 2, 3 tables are not shipped, so the `--exact --s 2/3`
  runs above must come first. `verify.py --exact` **replaces** that α's
  table and audit, and the saddle runs **merge** their sample rows into the
  existing CSV, which is why the recipe copies the shipped data first.
  `saddle_s1_dps60.csv` comes from `verify.py --s 1 --samples 10000 --dps 60`,
  which the intake did not rerun; `extra_checks.py` uses the shipped one.
- `verify.py --alpha 1 --max-n 300` (source 40) is a quick partial run, but a
  subset run rewrites `data/diagnostics.csv` with that subset only.
- `make verify` and `make pdf` in `code/48-a022629-Makefile` assume source
  48's delivered layout (`code/coefficients.py`, `code/verify.py`,
  `article.tex` beside the Makefile); `make pdf` would build source 48's
  unshipped manuscript, so use it only in a re-extraction of the archive
  from `3a9518c52`.

**Source 77-51.** Its five checkers take `--output-dir`, and **default to
writing beside themselves** (into `code/`), so always pass a fresh directory.
The three independent checkers need only the standard library (`R` and `U`
as in the recipe above):

```sh
W=$(mktemp -d)
for c in check check_family check_log_hierarchy; do
  cp "$R/code/77-51-fp-ind-$c.py" "$W/$c.py" && py "$W/$c.py" --output-dir "$W/out"
done                                                   # about 4 s each
diff <(tr -d '\r' < "$W/out/verification.json") "$R/data/77-51-fp-ind-verification.json"
diff <(tr -d '\r' < "$W/out/family_verification.json") "$R/data/77-51-fp-ind-family_verification.json"
diff <(tr -d '\r' < "$W/out/log_hierarchy_verification.json") "$R/data/77-51-fp-ind-log_hierarchy_verification.json"
cp "$R/code/77-51-fp-producer-check.py" "$W/check.py"
$U "$W/check.py" --output-dir "$W/prod"                 # about 30-45 s
cp "$R/code/77-51-fp-producer-generate_log_series.py" "$W/gen.py"
$U "$W/gen.py" --output-dir "$W/prod"                   # about 100 s
```

The independent receipts are reproduced byte for byte (modulo CR); the two
producer receipts differ only in their `seconds` fields (the intake reran
the producer check and all three independent checkers on 2 October 2026; the
symbolic generator was rerun at placement). The root driver
`code/77-51-fp-verify.py` checks the delivered file manifest
(`SHA256SUMS`), the approval pins of the delivered manuscript and PDF and
the `-O` negative controls; it cannot run in this layout. Run it on an
extraction of the arrival archive (which has no wrapper directory):
`git show 096ee7b87:docs/incoming/oeis-fixed-power-asymptotics-result.zip >
"$W/51.zip" && unzip -q "$W/51.zip" -d "$W/51" && (cd "$W/51" && py verify.py)`.
It did not finish within three minutes at placement on a loaded machine.

**Batch 100 (sources 100-82, 100-89, 100-93).** The checkers write their
JSON outputs **beside themselves** (`Path(__file__).with_suffix('.json')`, or
`reconstruction.json`), so run from `code/` they would add unprefixed files
there; `verify_numeric_examples.py` reads `check_relative_numeric.json` by its
delivered name; the three `run_checks.sh` call `checks/<delivered name>.py`
with `python` or `python3`, and source 100-89's calls
`checks/check_logarithmic_reversion.py`, which is not shipped (it is a byte
copy of source 100-82's `check_formal_series.py`); source 100-93's diagnostics
scripts import `diagnostics` by its delivered name, `diagnostics.py` defaults
to writing `results.json` beside itself, and `error_diagnostics.py` rewrites
the result file it is given. So rerun on a copy laid out as delivered (`R` as
in the recipe above):

```sh
W=$(mktemp -d); mkdir -p "$W/82/checks" "$W/89/checks" "$W/93/checks/diagnostics"
for f in "$R"/code/100-82-integral-*.py;  do cp "$f" "$W/82/checks/${f##*/100-82-integral-}"; done
for f in "$R"/code/100-89-boundary-*.py;  do cp "$f" "$W/89/checks/${f##*/100-89-boundary-}"; done
cp "$R/code/100-82-integral-check_formal_series.py" "$W/89/checks/check_logarithmic_reversion.py"
cp "$R/code/100-93-theta-check_identities.py" "$W/93/checks/check_identities.py"
for f in "$R"/code/100-93-theta-diag-*;   do cp "$f" "$W/93/checks/diagnostics/${f##*/100-93-theta-diag-}"; done
for f in "$R"/data/100-93-theta-diag-*;   do cp "$f" "$W/93/checks/diagnostics/${f##*/100-93-theta-diag-}"; done
cp "$R/data/100-89-boundary-check_relative_numeric.json" "$W/89/checks/check_relative_numeric.json"
U="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
(cd "$W/82" && $U -O checks/check_formal_series.py && $U -O checks/check_coefficients_independent.py \
            && $U checks/check_finite_coefficients.py && $U checks/check_integral_constant.py)   # about 100, 22, 57, 9 s
(cd "$W/89" && $U -O checks/check_corrections.py && $U -O checks/check_integer_roots.py \
            && $U -O checks/check_reconstruction.py && $U checks/check_relative_numeric.py \
            && $U checks/verify_numeric_examples.py && $U checks/check_boundary.py)            # about 14, 9, 10, 46, 24, 16 s
(cd "$W/93" && $U checks/check_identities.py && $U checks/diagnostics/verify_summary.py)       # a few seconds
```

Compare `$W/82/checks/<name>.json` with `data/100-82-integral-<name>.json`,
`$W/89/checks/<name>.json` (and `reconstruction.json`) with
`data/100-89-boundary-<name>.json`, and `$W/93/checks/check_identities.json`
with `data/100-93-theta-check_identities.json`. The intake's run on
5 October 2026 reproduced every one of these files up to line endings
(Python on Windows writes CRLF; the shipped files are LF), and
`verify_summary.py` passed on the 18 saved rows. Source 100-89's
`check_logarithmic_reversion.py` reproduces source 100-82's record exactly
and was not run twice. Source 100-93's main diagnostics
(`diagnostics.py --powers 12 20 32 48 --lambdas 4 5`, `--powers 8 --lambdas 4`,
then `error_diagnostics.py` on each result file) need NumPy, SciPy and mpmath
and are much more expensive; they were not rerun. Its binary128 audit
(`python prepare_quad113.py`, `g++ -std=c++17 -O3 quad113.cpp -lquadmath -o
quad113`, `./quad113 a8_l4_phase0.txt nodes96.txt` and the three other
combinations) was compiled and run at placement, reproducing all four shipped
outputs. The commands are in `100-93-theta-diagnostics-README.md`, under the
delivered names. The delivered `verify_package.py` (not shipped) checks the
delivered file hashes and runs only on an extraction of the arrival archive,
e.g. `git show 60f54ea06:docs/incoming/ProveIt_Critical_Theta_Power_Weighted_Distinct_Partitions.zip > "$W/93.zip"`.

## Disclosures and discrepancies

- `code/40-norm-moments-verify.py` says in its docstring "Run: python
  verify.py --max-n 5000 --dps 60", and 60 is its default, while the
  recorded transcripts and source 40's text use `--dps 50`; both are well
  above the 30 the script requires, and the intake's `--dps 50` run
  reproduced the shipped data.
- The A022629 tables `data/40-norm-moments-A022629_computed.txt`
  (n ≤ 5000), `data/48-a022629-exact_coefficients.csv` (n ≤ 6400),
  `data/75-01-jensen-exact_s1.json` (n ≤ 10000) and the selected values in
  `data/75-06-powers-a022629_exact.json` agree on their common indices; each
  is shipped beside its own verifier.
- **Delivery names in shipped text.** `48-a022629-PROVENANCE.md` points to
  "requirements.txt and the executable programs" (shipped as
  `data/48-a022629-requirements.txt` and `code/48-a022629-*.py`), and its
  "compiled to a 20-page A4 PDF" describes source 48's delivered PDF, which is
  not shipped. `code/48-a022629-Makefile` names `article.tex`,
  `code/coefficients.py` and `code/verify.py` in source 48's delivered layout.
  `code/40-norm-moments-verify.py` names itself `verify.py` (also in the
  header line it writes into the `*_computed.txt` files), and
  `code/40-norm-moments-derive_series.py` cites "Sections 7 and 8 of
  article.pdf": the section numbers of source 40's text are unchanged in the
  merged article, so that pointer still holds.
  `75-01-jensen-BUILD_AND_VALIDATION.txt` describes source 75-01's unshipped
  20-page PDF and its own build; `75-01-jensen-OEIS_PROPOSED_NOTES.md` cites
  "`article.pdf` in this package", meaning source 75-01's manuscript, not
  this report; the docstring of `code/75-01-jensen-verify.py` says "Output is
  written to ../data". `75-06-powers-proposed_oeis_updates.txt` cites
  "Section 5" and "Section 6" of source 75-06's manuscript (its relative and
  logarithmic theorems; here Theorems 2.2 and 2.1 with Sections 6 and 8, and
  Section 18 for μ layers), and `data/75-06-powers-source_audit.json` records its
  repository tree and that "No repository changes were made". The scripts'
  output names are the delivered ones (above). The article uses the shipped
  names; its Appendix A records all four sources' delivered command lists.
- **Stale statements.** Source 75-01's "A repository code search for A022629
  returned no match" and both batch-75 sources' presentation of the proof of
  the five conjectures as their contribution predate the placement of
  sources 40 and 48; the article records them as the third and fourth
  proofs (Sections 1.3 and 15.1). Source 75-01's README line "Higher powers
  can converge slowly" (its α = 3, n = 2500 test) is kept in the article with
  its own words and a merge note identifying the residual as noncentral.
- **Source 77-51's delivered text.** `77-51-fp-QA.md` and
  `77-51-fp-INTEGRATED_REVIEW.md` describe its delivered eleven-page PDF and
  manuscript, which are not shipped; its approval JSONs pin those delivered
  files and `article/…` paths; `code/77-51-fp-build.sh` runs `pdflatex` on
  `article/fixed-power-partition-asymptotics.tex`; the proof snapshots'
  status lines ("proposed", "pending") are superseded, by its own README, by
  the independent approvals. Its abstract and README say it "proves the
  logarithmic OEIS conjectures for A022629, A092484 and A266891"; here those
  are the fifth proofs, and only A266891 is new (Section 20, "Stale
  statements"). It cites Gikunda's thesis at two different ResearchGate
  addresses (publication 402798449 in the manuscript, 402798310 in
  `77-51-fp-ind-SOURCE_CHECK.md`); the article keeps the DOI of the existing
  bibliography item. `77-51-fp-ind-SOURCE_CHECK.md` cites a screening note
  under the producer's `/workspace/shared/` directory, which was not
  delivered.
- **Batch 100 delivered text.** The three `PROVENANCE.json` files hash
  their delivered files, including the unshipped manuscripts, PDFs, READMEs,
  `verify_package.py` and `build_local.sh`, under delivered paths.
  `100-93-theta-diagnostics-README.md` describes the delivered
  `checks/diagnostics/` layout, its commands use the delivered names, and it
  says that "the existing delivered fixed-a package" had an exact DP only
  through n = 3000 (source 100-89's `check_relative_numeric.py`). The
  `run_checks.sh` drivers name `checks/…` paths and `python`/`python3`; source
  100-89's names a file that is shipped only as source 100-82's (above).
  Source 100-89 cites Gikunda's thesis at the ResearchGate address
  402798310, as source 77-51's source check did; the article keeps the DOI.
  Source 100-93's bibliography item for source 100-89 is "previously
  delivered companion report and source package"; here that is Section 21.
- **Batch 100 stale statements.** Source 100-82's "proves and strengthens
  the conjecture currently listed in OEIS A022629", source 100-89's "settles
  the current conjectures in OEIS A092484 and A265840–A265842" and its "The
  closest located source is Gikunda's 2026 thesis" were written blind to this
  report; here they are the sixth and seventh proofs (Section 21, "Stale
  statements"). Source 100-89's table caption "Verified numerical
  diagnostics" means reproduced by independent recurrences and quadratures,
  not interval-certified (Section 21.6).
- **OEIS data (CC BY-SA 4.0).** `code/100-82-integral-check_finite_coefficients.py`
  embeds the first 21 terms of A022629 as an acceptance test. OEIS sequence
  data are licensed CC BY-SA 4.0 (attribution: The OEIS Foundation,
  https://oeis.org/A022629); no other batch-100 file embeds OEIS terms. The
  intake did not re-fetch A022629, A092484, A265840–A265842 or A292189 for
  batch 100.
- **External claims.** The A022629 entry's conjecture text (Kotesovec,
  8 May 2018) was confirmed live on 1 October 2026; on 2 October 2026 the
  intake confirmed the names and first fifteen terms of A022630 and A022631
  and the definition of A297321. Source 75-06's statement that A297321
  cross-references its first 32 columns to A022629–A022660, the other four
  entries, A292189, A292190, A022661, the Gikunda dissertation,
  Bridges–Craig, Schneider–Sills, Rana–Kaur–Kumar, Kumar–Rana,
  Granovsky–Stark, Griffin–Ono–Rolen–Zagier, Fristedt and Lagarias–Sun were
  not re-checked by the intake.
- **Abstracts and title pages.** The batch-73O1 abstracts were merged into
  source 40's with an added paragraph, a second paragraph summarizes the
  batch-75 additions and a third the batch-77 addition (source 77-51's title,
  abstract and package description are replaced by Section 20 and this
  README); source 48's title page and package-contents paragraph,
  and both batch-75 sources' title pages, abstracts, novelty paragraphs and
  package-contents appendices, are replaced by the article's Sections 1.4 and
  15, its provenance appendix and this README.
