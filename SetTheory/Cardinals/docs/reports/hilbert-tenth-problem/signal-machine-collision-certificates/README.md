# Collision Geometry Is Linear

**Diophantine Certificates for Rational Signal Machines and Conservative Particle Dynamics: event-sparse chambers, canonical quadratic and quartic certificates, two routes to complete chronology, a conservative universal frontend, and sparse lattice certificates**

This is a research report dated 2 October 2026, built from four AI-assisted
research manuscripts of ProveIt's incoming reports: manuscripts 07 and 11 of
batch 78 (Parts I and II) and manuscripts 16 and 19 of batch 79 (Parts III and
IV). The report calls them *source 07*, *source 11*, *source 12* and *source
13* after the file prefixes of their shipped programs and data. For the first
two the prefix is also the batch-78 manuscript number; for the last two it is
not: **source 12 is batch-79 manuscript 16, and source 13 is batch-79
manuscript 19** (the prefixes continue this report's own sequence). Source 07
is "prepared with ChatGPT for Vladimir Reshetnikov's ProveIt research
program", source 11's document metadata name "Research report prepared with
OpenAI", source 12 is an AI-assisted research note, and source 13 is a
"Research report prepared with AI assistance for Vladimir".

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 07 (base) | batch 78, manuscript 07 | `Collision_Geometry_Diophantine_Signal_Machines.zip` (`808b53ed8`); *Collision Geometry Is Linear: Event-Sparse Quadratic Diophantine Certificates for Rational Signal Machines*, main file `collision_geometry/article.tex`, 29-page PDF | `f1edb38f9` (audit blob `cb31d0a10`) | `798b0c5d4` | Part I (Sections 2–16) and Appendices A–B |
| 11 | batch 78, manuscript 11 | `Signal_Machine_Diophantine_Certificates.zip` (`808b53ed8`); *Direct Diophantine Certificates for Rational Signal Machines: Finite collision schemas with unique quadratic witnesses*, main file `signal-diophantine-release/article.tex`, 15-page PDF | none named | `798b0c5d4` | Part II (Sections 17–28) and Appendices C–D |
| 12 | batch 79, manuscript 16 | `Conservative_Signal_Frontend_Corrected.zip` (`aebfa386e`); *Conservative signal machines as Diophantine frontends*, main file `paper/conservative-signal-diophantine.tex` with `paper/morita-table.tex`, 21-page PDF; the corrected edition of batch-79 manuscript 07 (`Conservative_Signal_Diophantine_Frontend.zip`, `2a8a39599`), which is superseded and not shipped | none named (its `CORRECTION.md` cites the review commit `9f033fa6e`) | `a7ae02511` | Part III (Sections 29–37) and Appendices F–H |
| 13 | batch 79, manuscript 19 | `Sparse_Lattice_Diophantine_Certificates.zip` (`aebfa386e`); *Sparse Diophantine certificates for finite mass lattice dynamics*, main file `paper/sparse-lattice.tex` reading five further files, 27-page PDF; corrected code edition `Sparse_Lattice_Diophantine_Certificates_corrected.zip` (batch 80, manuscript 07, `4e270aa46`) | none named | `a7ae02511`; corrected code `8a4e64732` | Part IV (Sections 38–48) |

**Parts I and II prove one theorem by two routes.** Once a complete finite
collision history of a rational signal machine is fixed, its realizations are
exactly the natural zeros of a sum of squares of integer affine residuals, of
degree two, with exactly one witness tuple per realization. Both use typed
endpoint conditions on maximal adjacency intervals and causal-depth
denominators. Source 07 eliminates every event coordinate (a linear chamber in
the initial gaps, slack witnesses only, signed rational speeds); source 11
keeps batch times and event positions as natural witnesses on a fixed grid
and adds halting semantics. The texts are independent (neither cites the
other). Both are printed in full; Section 1.2 compares the routes (Table 1).

**Parts III and IV certify conservative dynamics at a fixed horizon.**
Part III writes out a fixed reversible, number-conserving universal signal
machine with 114 meta-signals, 445 two-to-two rules and exactly 18 live
signals on every encoded input, compiled from Morita's 15-state, 6-symbol
reversible universal Turing machine through Durand-Lose's 2012 conservative
stacks; its event dynamics is an 18-dimensional partial piecewise homogeneous
integer-linear map, and every step (hence every fixed horizon) has an explicit
canonical quadratic certificate, 4,196,998 auxiliary variables per step for
the literal machine. Part IV compiles a fixed horizon of one-dimensional
partitioned number-conserving lattice dynamics into one quartic sum of squares
with a unique natural witness, corrects a sign in Morita and Imai's
construction, and proves decidability and effective semilinearity at total
mass at most two. Sections 1.7–1.11 introduce them.

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs and
finite exact-arithmetic checks. Nothing in the report is formalized in Lean or
Rocq, and no priority is certified.

**Already reviewed.** All four manuscripts were reviewed in the
Hilbert-tenth-problem research tree
(`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`)
before or while this report was written: sources 07 and 11 in
`incoming_substrate_review_808b53ed8.md` and `incoming_signal_review_808b.md`
(commit `126028588`); source 12's earlier edition in
`review_conservative_signal_2a8a39599.md` and
`review_conservative_signal_independent.md` (commit `9f033fa6e`, with the
repair `conservative_signal_packet_domains.patch` that source 12 applies) and
source 12 itself in `review_conservative_signal_corrected_aebfa386e.md`
(commit `9df1f72ca`); source 13 in `review_sparse_lattice_aebfa386e.md`
(commit `9975af7e1`, with the repair
`sparse_mass_exact_polynomials.patch`, never applied here; since batch 80 the
shipped program is source 13's corrected code edition, whose own repair is
equivalent). Section "Reviews and patches" below
gives the details. This intake is not a first review.

**Batch 80 (corrected code edition of source 13).** A corrected edition of
source 13's archive, `Sparse_Lattice_Diophantine_Certificates_corrected.zip`
(3,895,754 bytes, SHA-256 `cf9b546b…dec1e2`; arrival `4e270aa46`, batch 80,
manuscript 07; the archive dates its correction 3 October 2026), repairs the
review's finding P2. It was placed by `8a4e64732` (batch 80, cluster K1):
five placed files were replaced by their corrected bytes under the same
names (`code/13-sparse-lattice-sparse_mass.py`,
`code/13-sparse-lattice-run_release.py`,
`13-sparse-lattice-SOURCE-PROVENANCE.md`,
`data/13-sparse-lattice-coefficient-crosscheck.json`,
`data/13-sparse-lattice-release-verification.json`; the originals remain in
`a7ae02511` and `aebfa386e`) and three were added
(`13-sparse-lattice-CORRECTION.md`,
`code/13-sparse-lattice-test_poly_exactness.py`,
`data/13-sparse-lattice-poly-exactness.json`). Its six manuscript files,
PDF, fixtures and tables are byte-identical to the batch-79 delivery, so no
printed statement, proof, count or label changes; Part IV records it in a
dated paragraph of Section 47 (`smc:sl:sec:reproduction`). The research
tree's correction audit `review_batch80_corrected.md` (commit `abfc0cb25`)
confirms the repair.

```
article.tex                                                     the report, standalone LaTeX with an internal bibliography
article.pdf                                                     the compiled report, 120 pages (unnumbered title page, then pages 1–119)
README.md                                                       this guide
07-collision-geometry-PROVENANCE.md                             source 07's repository and literature provenance, as delivered
11-signal-certificates-REPRODUCIBILITY.md                       source 11's reproducibility record, as delivered
12-conservative-signal-CORRECTION.md                            source 12's account of the generic-evaluator correction, as delivered
12-conservative-signal-PROOF_AND_LEDGER.md                      source 12's mode-closure proof and numeric packet ledger, as delivered
12-conservative-signal-SOURCE-PROVENANCE.md                     source 12's primary sources (Durand-Lose, Morita) and the Table 5 discrepancy, as delivered
13-sparse-lattice-CORRECTION.md                                 source 13's corrected edition: the exact Poly constructor, scope and evidence, as delivered (batch 80)
13-sparse-lattice-SOURCE-PROVENANCE.md                          source 13's provenance, primary sources and packaging changes, as delivered (batch-80 corrected edition, with a dated preface)
code/07-collision-geometry-Makefile                             source 07's make targets: test (run_checks.py) and pdf (latexmk)
code/07-collision-geometry-run_checks.py                        source 07's 34,560-assertion regression suite (imports signal_certificates; rewrites data/)
code/07-collision-geometry-signal_certificates.py               source 07's exact simulator, chamber compiler, quartic union (standard library)
code/11-signal-certificates-build.sh                            source 11's three-pass pdflatex build of its own article (delivered layout)
code/11-signal-certificates-run_replay.py                       source 11's isolated replay runner and receipt comparison
code/11-signal-certificates-signal_geometry.py                  source 11's exact simulator, full-layer compiler, rank calculation and checks
code/11-signal-certificates-signal_sparse.py                    source 11's sparse event-coordinate compiler and checks
code/11-signal-certificates-verify_additional.py                source 11's separately seeded edge cases and sharp height checks
code/11-signal-certificates-verify_examples.py                  source 11's worked-example and convention checks
code/12-conservative-signal-MORITA_15_6_audit.py                source 12's independent transcription of Morita's table and cyclic-tag/TM comparisons
code/12-conservative-signal-build.sh                            source 12's TeX Live build of its own article (delivered layout)
code/12-conservative-signal-check_original_replays.py           source 12's audit of the five literal runs against the numeric branch guards
code/12-conservative-signal-compile_packet.py                   source 12's closure compiler and exact coefficient exporter (verify/build/residuals/coefficient)
code/12-conservative-signal-conservative_signal.py              source 12's stack gadget, reversible-TM compiler, simultaneous-event engine, integer lifts
code/12-conservative-signal-independent_checks.py               source 12's all-pairs event engine, tie/germ checks, loaders, uniform QD^k lift
code/12-conservative-signal-initial_side_checks.py              source 12's left/right-entry loader regression suite
code/12-conservative-signal-instantiate_morita.py               source 12's literal universal table, loader, differential replay, mode codes
code/12-conservative-signal-pivot_scale_checks.py               source 12's pivot-scaled integer replay and fixed-span decoding
code/12-conservative-signal-quadratic_packet.py                 source 12's generic packet constructor and evaluator (the corrected, patched edition)
code/12-conservative-signal-run-replay.sh                       source 12's ten-command replay (python3; rewrites receipts in place)
code/12-conservative-signal-test_exporter.py                    source 12's small-packet exact exporter audit
code/12-conservative-signal-verify_packet_correction.py         source 12's regression test of the evaluator correction
code/13-sparse-lattice-build.sh                                 source 13's TeX Live build of its own article (delivered layout)
code/13-sparse-lattice-crosscheck_row_producer.py               source 13's producer/independent coefficient cross-check
code/13-sparse-lattice-independent_dynamics.py                  source 13's independent dense/sparse dynamics tests
code/13-sparse-lattice-independent_polynomial_audit.py          source 13's independent factorized-baseline compiler audit
code/13-sparse-lattice-independent_row_polynomial_audit.py      source 13's independent preferred row-selector compiler audit
code/13-sparse-lattice-morita_audit.py                          source 13's corrected Morita–Imai rule compiler and source tests
code/13-sparse-lattice-run-replay.sh                            source 13's wrapper: python3 replay/run_release.py
code/13-sparse-lattice-run_checks.py                            source 13's core checks and generic fixture generation
code/13-sparse-lattice-run_morita_fixture.py                    source 13's generator of the two Morita first-pulse certificates (the excluded .json.gz files)
code/13-sparse-lattice-run_release.py                           source 13's release runner (works in a temporary copy, compares with receipts; batch-80 edition, runs the exactness suite first)
code/13-sparse-lattice-semilinearity-audit.py                   source 13's independent actual-CA/Presburger arithmetic audit (delivered replay/semilinearity/audit.py)
code/13-sparse-lattice-semilinearity-check.py                   source 13's semilinearity proof-component regression (delivered replay/semilinearity/check.py)
code/13-sparse-lattice-sparse_mass.py                           source 13's coefficient-explicit sparse compiler and verifier (batch-80 corrected edition: exact Poly constructor)
code/13-sparse-lattice-test_poly_exactness.py                   source 13's exactness suite for direct Poly construction (batch 80; --baseline-module compares the original)
code/13-sparse-lattice-two-mass-audit.py                        source 13's mass-two encounter/query arithmetic audit (delivered replay/two-mass/audit.py)
code/13-sparse-lattice-two-mass-regression.py                   source 13's separate mass-two encounter regression
data/07-collision-geometry-checks.json                          source 07's recorded run: PASS, 34,560 assertions, test counts and ledgers
data/07-collision-geometry-first_hit_quartic_union.json         the two-chamber first-hit quartic (all matrices and the selector formula)
data/07-collision-geometry-simultaneous_two_sites.json          the simultaneous two-site certificate (Section 11.3)
data/07-collision-geometry-tournament_left.json                 the tournament chamber AB (Section 11.1)
data/07-collision-geometry-tournament_right.json                the tournament chamber BC
data/07-collision-geometry-tournament_triple.json               the tournament chamber ABC
data/07-collision-geometry-zeno_clock_24_batches.json           the 24-batch prefix of the four-speed clock (Section 12)
data/11-signal-certificates-expected-additional_verification_receipt.json  expected receipt: 506 fixtures, 878 certificates, 2,152 growth checks
data/11-signal-certificates-expected-signal_geometry_receipt.json          expected receipt: 122 full-layer certificates, 4,229 mutations, 625 tuples
data/11-signal-certificates-expected-signal_sparse_receipt.json            expected receipt: 444 sparse certificates, 3,982 lifetimes, 10,102 mutations
data/11-signal-certificates-expected-worked_examples_receipt.json          expected receipt: the worked examples and 64 shuttle batches
data/11-signal-certificates-manifest.json                       source 11's build/replay manifest with payload hashes, as delivered
data/11-signal-certificates-signal_geometry_examples.json       full-layer coefficient dictionaries and witnesses
data/11-signal-certificates-signal_sparse_examples.json         sparse coefficient dictionaries and witnesses
data/12-conservative-signal-COMPACT_VERIFICATION.json           source 12's compact-closure verification record (49,700 modes, 80,501 branches)
data/12-conservative-signal-EXPORTER_TEST_RECEIPT.json          source 12's exporter test receipt
data/12-conservative-signal-FULL_REPLAY_PRESERVATION.json       source 12's record that the ten original replay commands still pass after the correction
data/12-conservative-signal-INDEPENDENT_RESULTS.json            receipt of independent_checks.py
data/12-conservative-signal-INITIAL_SIDE_RESULTS.json           receipt of initial_side_checks.py
data/12-conservative-signal-LEDGER.json                         the numeric one-step packet ledger (Appendix H)
data/12-conservative-signal-MORITA_15_6_AUDIT_RESULTS.json      receipt of the Morita table audit
data/12-conservative-signal-MORITA_15_6_FIGURE28_REPLAY.json    all 185 configurations of Morita's 184-step example
data/12-conservative-signal-MORITA_15_6_TABLE.json              Morita's 62-quintuple table as data (printed as Appendix F)
data/12-conservative-signal-MORITA_18_REPLAY_RECEIPT.json       receipt of the literal 18-signal replays
data/12-conservative-signal-MORITA_18_SIGNAL_MACHINE.json       the complete literal machine: labels, speeds, 445 rules, mode codes, loader
data/12-conservative-signal-ORIGINAL_REPLAY_AUDIT.json          receipt of check_original_replays.py (13,798 events)
data/12-conservative-signal-PACKET_CORRECTION_OPTIMIZED_VERIFICATION.json  correction test receipt under python -O
data/12-conservative-signal-PACKET_CORRECTION_STANDALONE_VERIFICATION.json correction test receipt, standalone
data/12-conservative-signal-PACKET_CORRECTION_VERIFICATION.json            correction test receipt, compared with the original evaluator
data/12-conservative-signal-PIVOT_SCALE_RESULTS.json            receipt of pivot_scale_checks.py
data/12-conservative-signal-POLYNOMIAL_CIRCUIT.json             variable order and factored form of the step polynomial
data/12-conservative-signal-QUADRATIC_PACKET_RESULTS.json       receipt of quadratic_packet.py
data/12-conservative-signal-REPLAY_RECEIPT.json                 receipt of conservative_signal.py
data/12-conservative-signal-SOURCE_MANIFEST.json                digests and access dates of the (unshipped) primary-source PDFs
data/13-sparse-lattice-binary_three_way_collision.json          coefficient-explicit fixture (Section 47.2)
data/13-sparse-lattice-binary_three_way_collision_orthant.json  the same, orthant-exact
data/13-sparse-lattice-coefficient-crosscheck.json              receipt of the producer/independent cross-check (batch 80: producer hash refreshed)
data/13-sparse-lattice-core-checks.json                         receipt of the core checks
data/13-sparse-lattice-doubling-complete.csv                    the 17,576-row completed doubling table (CRLF, kept byte for byte)
data/13-sparse-lattice-false-signal-complete.csv                the 9,261-row unsafe-source counterexample table (CRLF, kept byte for byte)
data/13-sparse-lattice-huge_empty_span.json                     coefficient-explicit fixture with a gap of 10^100
data/13-sparse-lattice-independent-dynamics.json                receipt of the dense/sparse dynamics tests
data/13-sparse-lattice-independent-rows.json                    receipt of the independent row-selector audit
data/13-sparse-lattice-legacy-factorized.json                   receipt of the factorized-baseline audit
data/13-sparse-lattice-morita-n0.json                           receipt of the n=0, T=7 first-pulse certificate (file excluded, see below)
data/13-sparse-lattice-morita-n2.json                           receipt of the n=2, T=41 first-pulse certificate (file excluded, see below)
data/13-sparse-lattice-morita-source.json                       receipt of the source-interface audit (no final newline, as delivered)
data/13-sparse-lattice-poly-exactness.json                      receipt of the exactness suite (PASS: 24 malformed categories, 2,700 exact comparisons; batch 80)
data/13-sparse-lattice-release-verification.json                receipt of the release runner (batch 80: new first stage, producer hash refreshed)
data/13-sparse-lattice-semilinearity-components.json            receipt of the semilinearity component regression
data/13-sparse-lattice-semilinearity-independent.json           receipt of the independent semilinearity audit
data/13-sparse-lattice-ternary_mixed_mass.json                  coefficient-explicit mixed-mass fixture
data/13-sparse-lattice-two-mass-arithmetic.json                 receipt of the mass-two arithmetic audit
data/13-sparse-lattice-visual-qa.json                           source 13's record of its PDF visual check
```

Placed by `345a9e44e`, to be printed as Parts V–VI (batch 80K2); listed
here only so that this listing matches the directory (116 files):

```
14-three-mass-SOURCE_PROVENANCE.md
15-clean-targets-CLEAN-TARGET-THEOREM.md
15-clean-targets-INDEPENDENT-AUDIT.md
15-clean-targets-SOURCE_PROVENANCE.md
16-single-unit-AUDIT.md
16-single-unit-REVISION.md
16-single-unit-SOURCE-PROVENANCE.md
17-four-mass-BINARY-EXPANDING-SHUTTLE.md
17-four-mass-BINARY-INDEPENDENT-AUDIT.md
17-four-mass-EXPANDING-SHUTTLE.md
17-four-mass-FINAL-REVIEW.md
17-four-mass-INDEPENDENT-AUDIT.md
17-four-mass-SOURCE-PROVENANCE.md
17-four-mass-finite-seed-section-lemma.md
code/14-three-mass-build.sh
code/14-three-mass-certificate.py
code/14-three-mass-checker.py
code/14-three-mass-export_examples.py
code/14-three-mass-legacy-certificate.py
code/14-three-mass-legacy-checker.py
code/14-three-mass-radius_one.py
code/14-three-mass-replay.sh
code/14-three-mass-spatial_radius_one.py
code/14-three-mass-test_certificate_hardening.py
code/14-three-mass-test_certificates.py
code/14-three-mass-test_certificates_independent.py
code/14-three-mass-test_checker_mutations.py
code/14-three-mass-test_clock_scale_independent.py
code/14-three-mass-test_literal_exports.py
code/14-three-mass-test_radius_one.py
code/14-three-mass-test_radius_one_boundaries.py
code/14-three-mass-test_size_ledger.py
code/14-three-mass-test_spatial_radius_one.py
code/14-three-mass-test_three_mass_independent.py
code/14-three-mass-test_two_mass_arithmetic.py
code/14-three-mass-three_mass_collision_generator.py
code/15-clean-targets-audit_actual_ca.py
code/15-clean-targets-audit_certificates.py
code/15-clean-targets-audit_lift_name_collisions.py
code/15-clean-targets-audit_witness_lift.py
code/15-clean-targets-build.sh
code/15-clean-targets-check_clean_targets.py
code/15-clean-targets-clean_targets.py
code/15-clean-targets-replay.py
code/15-clean-targets-test_affine_lift.py
code/15-clean-targets-test_clean_targets.py
code/16-single-unit-audit_accelerator.py
code/16-single-unit-build.sh
code/16-single-unit-run-tests.sh
code/16-single-unit-test_single_unit_acceleration.py
code/17-four-mass-audit_arithmetic.py
code/17-four-mass-audit_binary_shuttle.py
code/17-four-mass-binary_exact.py
code/17-four-mass-build.sh
code/17-four-mass-check_binary_rule.py
code/17-four-mass-draw_binary_shuttle_trace.py
code/17-four-mass-run-tests.sh
code/17-four-mass-test_binary_expanding_shuttle.py
code/17-four-mass-test_exact_boundaries.py
code/17-four-mass-test_expanding_shuttle.py
data/14-three-mass-certificate-hardening.json
data/14-three-mass-certificate-tests.json
data/14-three-mass-chain_certificate.json
data/14-three-mass-chain_check.json
data/14-three-mass-chain_request.json
data/14-three-mass-chain_witness.json
data/14-three-mass-checker-mutations.json
data/14-three-mass-clock-scale-optimized-tests.json
data/14-three-mass-clock-scale-tests.json
data/14-three-mass-generator-tests.json
data/14-three-mass-independent-ca-tests.json
data/14-three-mass-independent-certificate-tests.json
data/14-three-mass-literal-export-check.json
data/14-three-mass-literal-export.json
data/14-three-mass-mixed_check.json
data/14-three-mass-mixed_radius_one_check.json
data/14-three-mass-mixed_radius_one_request.json
data/14-three-mass-mixed_radius_one_witness.json
data/14-three-mass-mixed_request.json
data/14-three-mass-mixed_witness.json
data/14-three-mass-pdf-qa.json
data/14-three-mass-radius-one-boundaries.json
data/14-three-mass-radius-one-tests.json
data/14-three-mass-replay-summary.json
data/14-three-mass-rule_index.json
data/14-three-mass-size-ledger-tests.json
data/14-three-mass-spatial-radius-one-optimized-tests.json
data/14-three-mass-spatial-radius-one-tests.json
data/15-clean-targets-actual-ca-receipt.json
data/15-clean-targets-affine_lift.json
data/15-clean-targets-certificate-receipt.json
data/15-clean-targets-chain_certificate.json
data/15-clean-targets-chain_receipt.json
data/15-clean-targets-chain_request.json
data/15-clean-targets-chain_witness.json
data/15-clean-targets-final-prose-review.json
data/15-clean-targets-lift-name-collision-receipt.json
data/15-clean-targets-portable-replay.json
data/15-clean-targets-report-qa.json
data/15-clean-targets-source-provenance.json
data/15-clean-targets-test_clean_targets.json
data/15-clean-targets-upstream-extension-manifest.json
data/15-clean-targets-witness-lift-receipt.json
data/16-single-unit-audit-results.json
data/16-single-unit-test-results.json
data/17-four-mass-audit-arithmetic-results.json
data/17-four-mass-binary-four-particle-shuttle.csv
data/17-four-mass-binary-four-particle-shuttle.json
data/17-four-mass-binary-independent-audit-results.json
data/17-four-mass-binary-radius6-conservation-certificate.json
data/17-four-mass-binary-rule-receipt.json
data/17-four-mass-binary-shuttle-test-results.json
data/17-four-mass-exact-boundary-results.json
data/17-four-mass-portable-replay-results.json
data/17-four-mass-shuttle-test-results.json
figures/17-four-mass-binary-four-particle-shuttle.pdf
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery; for source 13 the delivery is, since
batch 80, the corrected code edition (its other 30 shipped files are
byte-identical in both editions). The files of the batch-80K2 block above
are described by the write of Parts V–VI. Delivered name → shipped name:

- Source 07 (`collision_geometry/`): `Makefile`, `code/run_checks.py`,
  `code/signal_certificates.py` → `code/07-collision-geometry-*`;
  `data/*.json` (seven files) → `data/07-collision-geometry-*.json`;
  `PROVENANCE.md` → `07-collision-geometry-PROVENANCE.md`; `article.tex` →
  the base of `article.tex` (Part I); `README.md` → replaced by this README.
- Source 11 (`signal-diophantine-release/`): `build.sh` and `scripts/*.py`
  → `code/11-signal-certificates-*`; `examples/*.json` and `manifest.json`
  → `data/11-signal-certificates-*.json`; `expected_receipts/*_receipt.json`
  → `data/11-signal-certificates-expected-*_receipt.json`;
  `REPRODUCIBILITY.md` → `11-signal-certificates-REPRODUCIBILITY.md`.
- Source 12 (`conservative-signal-release/`): `build.sh`, `run-replay.sh`,
  `code/*.py`, `numeric/*.py` and `correction/verify_packet_correction.py`
  → `code/12-conservative-signal-<file name>`; `data/*.json`,
  `receipts/*.json`, `correction/*.json` and `numeric/*.json` →
  `data/12-conservative-signal-<file name>`; `CORRECTION.md`,
  `SOURCE-PROVENANCE.md` and `numeric/PROOF_AND_LEDGER.md` →
  `12-conservative-signal-<file name>` at the report root. The delivered
  `numeric/MORITA_18_SIGNAL_MACHINE.json` is a byte copy of
  `data/MORITA_18_SIGNAL_MACHINE.json` and is shipped once.
- Source 13 (`sparse-lattice-release/`): `build.sh`, `run-replay.sh`,
  `replay/run_release.py`, `replay/core/*.py` and `replay/independent/*.py`
  → `code/13-sparse-lattice-<file name>`; `replay/semilinearity/{audit,check}.py`
  → `code/13-sparse-lattice-semilinearity-{audit,check}.py`;
  `replay/two-mass/{audit,regression}.py` →
  `code/13-sparse-lattice-two-mass-{audit,regression}.py`; `receipts/*.json`
  → `data/13-sparse-lattice-<file name>`; the four
  `replay/core/fixtures/*.json` → `data/13-sparse-lattice-<file name>`;
  `tables/*.csv` → `data/13-sparse-lattice-*-complete.csv`;
  `SOURCE-PROVENANCE.md` → `13-sparse-lattice-SOURCE-PROVENANCE.md`; the
  corrected edition's `CORRECTION.md`, `replay/core/test_poly_exactness.py`
  and `receipts/poly-exactness.json` → `13-sparse-lattice-CORRECTION.md`,
  `code/13-sparse-lattice-test_poly_exactness.py` and
  `data/13-sparse-lattice-poly-exactness.json`. The
  delivered `replay/morita/audit.py` is a byte copy of
  `replay/core/morita_audit.py` and is shipped once.

Not shipped (all survive in the archives of the arrival commits):

- source 11's manuscript (printed as Part II), source 12's two manuscript
  files (Part III; its Morita table is Appendix F) and source 13's six
  (Part IV); all four PDFs; the four delivered READMEs (this text and
  `article.tex` replace them);
- the checksum ledgers, all verified at placement: source 07's `SHA256SUMS`
  (14 of 14), source 11's `CHECKSUMS.sha256` (17 of 17), source 12's
  `SHA256SUMS` (44 of 44; batch-79 manuscript 07's had 37 of 37), source
  13's `SHA256SUMS` (48 of 48) with its checker `replay/verify_manifest.py`,
  and the corrected edition's refreshed `SHA256SUMS` (51 of 51) at the
  batch-80 placement; the corrected edition's delivery `README.md` (with a
  correction notice);
- source 12's `correction/conservative_signal_packet_domains.patch`, which is
  byte-identical to the research tree's
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/conservative_signal_packet_domains.patch`
  and already applied in `code/12-conservative-signal-quadratic_packet.py`;
- source 13's packager `replay/package_release.py`, which only rewrites
  `SHA256SUMS` and builds the delivery ZIP;
- the two byte copies named above;
- four heavy regenerable files (next section);
- all 38 files of batch-79 manuscript 07, the superseded edition of source 12
  (36 of them are byte-identical to source 12's; its `code/quadratic_packet.py`
  is the unpatched evaluator).

```sh
git show 808b53ed8:docs/incoming/Collision_Geometry_Diophantine_Signal_Machines.zip > cg.zip
git show 808b53ed8:docs/incoming/Signal_Machine_Diophantine_Certificates.zip > sd.zip
git show aebfa386e:docs/incoming/Conservative_Signal_Frontend_Corrected.zip > cs.zip
git show aebfa386e:docs/incoming/Sparse_Lattice_Diophantine_Certificates.zip > sl-original.zip   # source 13, original edition
git show 4e270aa46:docs/incoming/Sparse_Lattice_Diophantine_Certificates_corrected.zip > sl.zip   # source 13, corrected edition (preferred)
git show 2a8a39599:docs/incoming/Conservative_Signal_Diophantine_Frontend.zip > cs-original.zip
```

Both editions of source 13 contain every file, including the excluded
fixtures (byte-identical in the two); the corrected one matches the shipped
programs.

### Reconstructing the excluded data

Four regenerable files of sources 12 and 13 (6,842,592 bytes together) are
not shipped. Each is rebuilt by a shipped program, in the delivered layout
(get it by extracting the archive, `cs.zip` or `sl.zip` above, into a scratch
directory, or with the research tree's stager described under "Rerunning the
programs"). The simplest way to obtain the exact delivered bytes is the
archive itself.

| Excluded file (delivered path) | Bytes | Rebuild, from the extracted archive root | Time here | Result |
|---|---:|---|---|---|
| `numeric/MODES.jsonl.gz` (source 12; 49,700 lines) | 1,054,196 | `py numeric/compile_packet.py build` (one run writes both) | 43–58 s | decompressed content identical (8,747,944 bytes) after removing the CR bytes that Windows text mode adds |
| `numeric/EVENTS.jsonl.gz` (source 12; 80,501 lines) | 580,458 | the same run | — | decompressed content identical (2,089,381 bytes), likewise |
| `replay/core/fixtures/morita_doubling_n0_pulse_T7.json.gz` (source 13) | 839,734 | `py replay/core/run_morita_fixture.py --input 0` | 10–14 s | decompressed payload identical (5,138,262 bytes) |
| `replay/core/fixtures/morita_doubling_n2_pulse_T41.json.gz` (source 13) | 4,368,204 | `py replay/core/run_morita_fixture.py --input 2` | 94 s | decompressed payload identical (28,739,575 bytes) |

The compressed bytes differ (gzip header time and the local zlib build;
under Python 3.14.4 on Windows the n=0 file is 840,087 bytes), so compare
after decompression. At this write the source-12 build (43 s) and the n=0
fixture (10 s) were rerun on fresh extractions of the archives and matched;
the placement dossier ran all four (`a7ae02511`). Side effects to expect:
`compile_packet.py build` also rewrites `numeric/LEDGER.json` (only its
`elapsed_export_seconds` field changes) and `numeric/POLYNOMIAL_CIRCUIT.json`
(value-equal), and writes the unshipped `BRANCHES.jsonl.gz` (about 23 MB),
`MODES.bin`, `EVENTS.bin` and `MANIFEST.json`; `run_morita_fixture.py`
rewrites `replay/core/morita_fixture_n{0,2}_results.json`, which differ from
the shipped receipts `data/13-sparse-lattice-morita-n{0,2}.json` only in
`compressed_bytes`. Under Windows Python, `gzip` text mode writes CRLF line
ends, so source 13's n=0 payload gains one CR byte unless Python runs on a
POSIX system (or WSL) or with a newline shim; compare modulo CRLF in that
case. Shipped programs that read the excluded files: source 12's
`compile_packet.py verify` and `run-replay.sh` need both `.gz` files; source
13's `run_release.py` silently skips missing fixtures in its default mode
(losing coverage) and fails with `--regenerate-source`, which also compares
the zlib-dependent `compressed_bytes` field, so it can fail under another
zlib even when the payloads agree. Regenerate first, or run in the
extracted archive.

## Labels and numbering

Every label carries the prefix `smc:`. Source 07's 66 labels are `smc:cg:`
plus their delivered names, and source 11's 26 are `smc:sd:` plus theirs.
The batch-78 merge added 51 labels (143 in all): thirteen `smc:` labels of
the front section, the two Parts and the provenance appendix
(`smc:sec:front`, `smc:sec:parts`, `smc:sec:routes`, `smc:tab:routes`,
`smc:sec:notation`, `smc:tab:notation`, `smc:sec:relation`,
`smc:sec:status`, `smc:sec:questions`, `smc:tab:questions`, `smc:part:cg`,
`smc:part:sd`, `smc:app:provenance`); fifteen `smc:cg:` labels
(`lem:endpoint` on source 07's unlabelled endpoint lemma, `sec:simultaneous`,
nine `q:*` on its research directions, `sec:conclusion`, `app:dependency`,
and the two new remarks `rem:singlefold` and `rem:credit`); and twenty-three
`smc:sd:` labels (sixteen `sec:*` on source 11's sections and subsections,
`cor:hessian`, five `q:*` on its questions, `app:sources`).

Batch 79 added 109 labels, 252 in all, and removed or renamed none (the
`.aux` files before and after give the same number to every one of the 143
earlier labels): source 12's 49 labels as `smc:cs:` plus their delivered
names, source 13's 53 as `smc:sl:` plus theirs, and seven new labels, which
use `smc:cs:` although some cover both Parts: `smc:cs:part`, `smc:sl:part`
and the five front subsections `smc:cs:sec:batch79`, `smc:cs:sec:notation`,
`smc:cs:sec:relation`, `smc:cs:sec:status`, `smc:cs:sec:questions`.
The batch-79 reciprocal notes (cluster J2: the note after
`smc:cs:thm:packet` and a parenthesis in `smc:cs:sec:relation`) added no
label; the report still has 252, and no label's number changed (compared in
the `.aux`).

Each Part keeps its source's numbering of statements, by section: source
07's Section *n* is Section *n* + 1 here (Sections 2–16), so its Theorem
*n.m* is Theorem (*n* + 1).*m*; source 11's Section *n* is Section *n* + 16
(Sections 17–28); source 12's is *n* + 28 (Sections 29–37); source 13's is
*n* + 37 (Sections 38–48). Source 07's two appendices are Appendices A–B,
source 11's are C–D, Appendix E is the provenance, and source 12's three
appendices are F–H (placed after E so that no earlier letter changed).
Equations are numbered by section in all Parts (sources 07, 12 and 13
numbered them consecutively). The notation table of Parts III–IV is
uncaptioned, so Tables 1–6 keep their numbers. Text written in the merges is
marked `[write]`; text without a marker is the source's own.

## Setting and notation

A rational signal machine has finitely many labels, each moving at a fixed
rational speed on a line; a collision consumes its incoming signals and emits
a rule-determined set. A *skeleton* (Part I) or *schema* (Part II) fixes the
ordered batches of simultaneous collisions; a *site* of Part I is an *event*
of Part II. Part III certifies the steps of one fixed universal machine,
Part IV the steps of a partitioned number-conserving cellular automaton.
Each Part keeps its source's letters; Table 2 (Section 1.3) lists every
letter used in both Parts I and II, and the table of Section 1.8 every letter
of Parts III and IV with another meaning elsewhere. The ones most likely to
be misread:

- `B` — Part I: number of batches; Part II: the grid modulus `B = D^K`;
  Part III: number of branches of the step map; Part IV: the control
  baseline `m + 16`. **Never** a number of batches outside Part I.
- `K` — Part I: `2 + 4V`, and the number of first-hit chambers; Part II: the
  number of batches; Part III: the horizon (number of steps); Part IV: the
  alphabet cap (`q = K + 1`).
- `T` — Part I: site budget; Part II: batch times; Part III: the number of
  strict guards, **not** a time; Part IV: the horizon.
- `D` — the same lcm of nonzero speed differences in Parts I–III (Part I
  after scaling time by `L`, Part II after a Galilean shift and a scaling by
  `m`; with `m = L` they coincide); Part IV: the diameter of the initial
  support.
- `R` — residual counts in Parts II–IV (raw rows in Part I), but also Part
  III's layout half-width `ℓ + 2` and Part IV's right lane.
- `L`, `m`, `p`, `q`, `r`, `s`, `W` — Part I: speed-clearing integer, number
  of distinct speeds, in/out counts at a site, retained equality/strict rows,
  `3u + 2v`; Part II: number of lifetimes, speed multiplier, initial
  positions, position scale, largest arity/fanout, number of witnesses; Parts
  III–IV: see Section 1.8.
- **Sparse** — Part I counts conditions (rows may be dense in the gaps);
  Part II's residuals also have bounded width; Part III's gap matrices have
  at most `2(n−2)` nonzero entries; Part IV keeps `M` records however large
  the gaps. None is an arithmetic-operation count or a fixed-arity statement.
- **Convex** — Part I's certificate is convex jointly; Part II's is
  *strictly* convex in the witnesses with the input fixed; Part III's step
  polynomial is not asserted convex (it is nonnegative on the real orthant).

No symbol was renamed in the printed text and no normalization changed.
The TeX macro `\N` of sources 11, 12 and 13 is `\NN` in this file because
source 07's `\N` prints `ℕ₀`; all print `{0, 1, 2, …}` as their sources did.
Source 11's bibliography keys `DL09` and `GS66` are cited as source 07's
`durandlose` and `ginsburgspanier` (merged entries); source 12's `dl2007`
and `dl2006` are cited as the existing `DL07` and `DL06`, and source 13's
`ginsburgspanier` is the existing entry.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **The common theorem of Parts I and II** (Part I, Theorems 5.3 and 6.1;
  Part II, Theorem 18.3): for a fixed machine, initial label word and finite
  skeleton or schema, an effective sum of squares of integer affine residuals
  of degree at most two whose natural zeros are exactly the realizations,
  with a unique witness tuple; typed adjacency-interval endpoints exclude
  unrecorded earlier collisions, omitted simultaneous inputs and omitted
  simultaneous sites.
- **Part I (source 07).** The realizing gap vectors form a relatively open
  rational polyhedral cone with at most `3(n−1) + (3m+1)E` raw conditions;
  the certificate `‖Eg‖² + ‖Gg − 1 − z‖²` with unique slacks; causal-depth
  denominators `D^h` and row heights `2d(1+V)(DK)^h`; a positive integer
  realization of size at most `d^{d/2} A^d`, and real = rational = integer
  realizability; an NP upper bound for bounded synthesis; a certified
  perturbation radius and codimension `rank E`; finite-horizon semilinearity;
  a canonical first-hit quartic with unique selector and slacks; exact
  Ehrhart quasi-polynomial seed counts with rational density; the
  first-collision tournament (`C(H) = ⌊(3H² + 1)/4⌋`, its generating function
  and inverse); a four-speed accumulating clock with denominators exactly
  `2·3^k`; and a convex-quadratic rigidity theorem and compression barrier.
- **Part II (source 11).** The same theorem with batch times and event
  positions as natural witnesses on the grid `D^K`, in prefix and halting
  versions; full column rank of the witness matrix (strict convexity in the
  witnesses); `W ≤ (2s+5)E + 3n₋` and `R ≤ (r+2s+3)E + 3n₋`; a full-layer
  reference construction with exact counts; the canonical-witness height
  bound `60^K max(1, M₀)` for the four-speed interface `{0, 2, 3, 4}` of
  Durand-Lose's universal machine; a bounded shuttle with denominators
  exactly `3^{k−1}`; semilinearity of fixed-schema inputs; positive-witness
  translation.
- **Part III (source 12).** A fixed partial signal machine `U₁₈` (114
  meta-signals, 445 injective two-to-two rules, speeds
  `{−12, −9, −4, 0, 4, 9, 12}`, `D = 65520`) that simulates Morita's
  explicitly halting cyclic-tag interpreter with exactly 18 live signals,
  stays in `[−8, 8]` before halt, separates accepting from null termination,
  and has no accumulation on encoded runs (Theorem 29.1); a ten-signal
  binary machine by an existence compiler (Theorem 29.2); exact rational
  stack arithmetic and its collision gadget; an exact two-half input loader
  with its arithmetic cost; complete simultaneous-event selection (Lemma
  34.1) and the equal-cardinality branch map; the pivot-scaled integer lift
  `N_j = c_j I − c e_jᵀ`, `N_j² = c_j N_j`, rank `n − 2` (Proposition 35.1),
  with one mode coordinate; a selector/copy quadratic polynomial with a
  unique natural witness for every legal step of a finite homogeneous branch
  system, its exact ledger `A = B(d+1) + T + W`, `R = 1 + 2d + E + T + W`,
  and its fixed-horizon sums (Theorem 36.1); for `U₁₈`, a closed family of
  49,700 modes and 80,501 branches, 4,196,998 auxiliary variables,
  2,762,961 squared residuals and 80,501 products per step,
  `4,197,016K − 18` witnesses for horizon `K`, and an expanded monomial
  count of 1,059,563,096,023 (Appendix H).
- **Part IV (source 13).** For any supplied total conservative table, mass
  `M` and horizon `T`, one sum of squares of degree at most four with
  exactly one natural zero decoding to the physical history, with
  `V = T[M(q³+14) + 5M(M−1)]` witnesses, `R = T[17M + 5M(M−1)]` residuals
  and the height bound `3(D+2T) + M + 3K + 3` (Theorem 38.1); restricted row
  lists; an orthant-exact option with `2MT` extra residuals; the sign
  correction of Morita–Imai's rule (8.2), the completion lemma within mass
  fibres, the false observer, the existence of safe universal sources, the
  paid loader `4 + 3M(M−1)` and first-pulse observer `4MT + 3M` /
  `4MT + 2M + T`, the doubling example with pulse time `5n² + 7n + 7`;
  decidability under a bounded orbit diameter and no computable complete
  diameter cutoff (Propositions 43.1–43.2); decidability at total mass at
  most two (Theorem 44.1) and effective semilinearity there (Theorem 45.1),
  with horizon-free canonical quartics of `2I + 6C + G` witnesses
  (Corollary 46.1).

**Credit and re-derived results.** Part I's convex-quadratic rigidity
theorem and compression barrier (Theorem 13.1, Corollary 13.2) are a special
case of Part XI of `canonical-diophantine-certificates`
(`cdc:of:lem:affinezero`, `cdc:of:thm:cubicsemilinear`,
`cdc:of:thm:classification`: degree ≤ 3, nonnegative only on the orthant,
`D⁺₂ = D⁺₃ = SL`), which source 07 does not cite; Remark 10.3 relates the
first-hit quartic to that Part's `cdc:of:thm:singlefoldsl`. Part III's
Lemma 34.1 is the one-batch case of Part I's chamber theorem (Theorem 5.3)
and of Part II's Lemmas on interior and boundary meetings; its uniform `QD^k`
lift is the denominator device of Part I's Theorem 7.1 and Part II's grid;
its step polynomial has the form `Σ A² + Σ BC` of the spine of
`quadratic-orthant-certificates` (`qoc:eq:spine`), and the existence of such
a single-fold quadratic also follows from `cdc:of:thm:singlefoldsl`; its
selector/copy construction is Balas's disjunctive formulation (Balas 1979,
1985; Jeroslow–Lowe 1984), which source 12 does not cite. Part IV's
comparison gadget is `cdc:mem:lem:compare` and its sorting comparator the
record comparator `cdc:mem:prop:comparator-cost` of CDC Part V; its
horizon-free quartic is a degree-four second route to
`cdc:of:thm:singlefoldsl`; its cutoff proof reuses `cdc:bd:prop:nobound`.
All are printed as delivered with `[write]` notes and no novelty claim.

The report does **not** claim:

- historical priority or exhaustive novelty (all four sources say so); a
  general linearizability of signal-machine evolution, which sources 11 and
  12 attribute to Durand-Lose's linear real-register simulation; a new
  universal computational mechanism or new classical universality;
- one fixed-arity polynomial for unbounded halting or for an unknown
  horizon, a single-fold or finite-fold Diophantine representation of c.e.
  sets, or any improvement of the repository's 75- and 87-operation bounds;
  the skeleton, schema or horizon is compiler data, and row, residual or
  variable counts are not operation counts;
- that the published 13-meta-signal, 21-rule universal machine of
  Durand-Lose 2009 or its input loader has been transcribed (Part III
  transcribes a different universal machine); that any Part converts an
  ordinary binary integer input (Part III's loader starts from a prepared
  tape and states, without paying, the cost of a conversion);
- for Part III: a printed ten-signal interpreter, optimality of 18 or ten
  signals, of the loader or of the dimension, injectivity of the integer
  event map, realizability of every path of the mode graph, a bound on
  universal runtime from that graph, a flat monomial expansion or a minimal
  gate count, convexity of the step polynomial, semantics for malformed
  rational configurations; universality is imported from Morita's theorem;
- for Part IV: a printed universal source table or its state count,
  faithful interpretation of arbitrary counter pairs, intrinsic universality,
  an efficient simulation, exact-target undecidability, global halting, a
  minimum universal mass or that three particles suffice, statements over
  unrestricted reals, lower bounds from the displayed counts, an
  arbitrary-rule quantifier eliminator, or anything about arbitrary c.e.
  sets from the mass-two subclass;
- any semantics at or after an accumulation point; that the clock discovers
  accumulation;
- NP-hardness, an efficient first-hit enumerator, or that the denominator
  examples bound arbitrary Diophantine representations (Part II's is a lower
  bound for common-grid encodings);
- that integer scaling of a rational seed keeps a prescribed physical length
  or deadline;
- that the finite checks are exhaustive, or that Part II's two compilers are
  independent (they share a simulator); the code is not a verified compiler
  and the low-level compilers are not hardened parsers;
- novelty for any reduction of the programme's reviews, which are the
  reviews';
- any Lean or Rocq verification.

## Research questions

Part I's nine research directions, Part II's five questions and Part IV's
five questions are printed in their Parts (Part III states none); Table 3
pairs Parts I and II. Batch 79 answers two of them, in dated `[write]` notes:

- Part I's direction 15.2 (`smc:cg:q:universal`, an audited universal
  signal-machine frontend) is answered by Part III **except for the
  ordinary-integer loader**, and with Morita's UTM(15,6) through Durand-Lose's
  2012 stacks instead of the 13-type construction named there.
- Part II's question `smc:sd:q:conservative` (exploit conservative bounded
  populations) is answered in part, at a fixed horizon, by Parts III and IV;
  neither encodes unbounded histories in fixed arity.
- Part II's `smc:sd:q:universal` (transcribe the 13-label table) stays open.

## Relation to neighbouring reports and to the formal project

This report is in the collection's `hilbert-tenth-problem` category, as a
substrate with low-degree Diophantine certificates; nothing in the repository
treated signal machines before batch 78 apart from the programme's review.

- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  Part XI, the credit above and the single-fold quadratic that Parts III and
  IV re-derive in special forms; Part V, the comparison and sorting gadgets
  that Part IV re-derives; Part IX's `cdc:bd:prop:nobound`, the
  bounded-search argument that Parts I and IV use for different statements;
  Part VIII, the dense finite cellular-automaton tableau of which Part IV is
  a sparse infinite-line counterpart; Part XVI's question "Local
  certificates on adaptive support geometry", on which Part IV bears without
  answering it.
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**, Part V: the
  question of its source 11 "Optimal degree under stronger geometric
  restrictions" mentions the "rigid affine geometry" of globally nonnegative
  quadratics; Part I's Theorem 13.1 states that geometry. The question is
  not settled here.
- **[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)**
  (dated note of 2 October 2026, batch 78H3; that report was opened by
  cluster H3 of batch 78 and written in `c51b9880d`): the same format
  family. Its three Parts compile fixed finite systems (maximal-parallel
  multiset rewriting, timed irreversible races, a fixed universal Waterfall
  program) into one integer polynomial of degree two of the form
  `Σ A_i² + Σ B_j C_j`, with affine `A_i` and with factors `B_j`, `C_j` that
  have nonnegative coefficients, so that it is nonnegative on the whole real
  orthant (its section `qoc:sec:spine`). The common theorem of Parts I–II is
  the case without product terms, a sum of squares of integer affine
  residuals; Part III's step polynomial (added in batch 79) has exactly that
  report's form, with selector-times-copy products. All these sit at the
  level `D⁺₂ = SL` of `cdc:of:thm:classification`, which is why a fixed
  skeleton, schema or horizon gives semilinear projections; Part I's
  first-hit quartic, Part IV's quartics and that report's degree-four
  variants lie outside the format. The products are where Parts I–II and
  that report differ: that report uses them for negative conditions
  (maximality, earliest completion, inactive directions), and its Theorem
  `qoc:mp:thm:convexno` shows that already the deadlock of `A + B → C` has
  no convex quadratic certificate, whereas the sums of squares of Parts I–II
  are convex. That report names this one in its relation section
  (`qoc:sec:relation`); neither report re-proves a theorem of the other.
  Reciprocal note (batch 79, cluster J2, 2 October 2026): that report's
  Parts V and VI (its sources 16 and 17, batch-79 manuscripts 09 and 18,
  written in `11abe5008`) use Part III's selector/copy device with the
  selector added to the right factor of each product,
  `(Σ_{k≠r} e_k)(e_r + Σ x_r)` (`qoc:um:eq:polynomial`,
  `qoc:rn:lem:gates`), which makes their nonnegative real fibres natural.
  A dated note after Part III's packet theorem compares the two gates and
  adds an elementary observation that neither source makes: two positive
  selectors force every local copy, hence the input `X`, to vanish, so the
  nonnegative real fibre of Part III's packet is natural at every natural
  input `X ≠ 0`; adding the selector term would remove the exception at
  `X = 0` without changing the ledger. That report's relation section and
  a note after its Theorem `qoc:um:thm:poly` point back here.
- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**:
  its trace theorem `pqc:pm:thm:trace` is the same kind of fixed-horizon,
  one-natural-zero statement as Part III's horizon sums, for different
  dynamics. **[`group-theoretic-substrates`](../group-theoretic-substrates)**:
  no overlap.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/`:
  - the reviews listed in the next section;
  - `1980/REVERSIBLE_FINITE_HISTORY_MODELS.md`: cited by source 07 (blob
    `cb31d0a10`, unchanged at the write);
  - `1980/EXPLORATION_BINARY_BLOCK_CA_AUDIT.md`: notes that finite particles
    "can in principle store unbounded values in their separation" and that a
    new construction would have to establish that interface. Parts I–II do
    not; **Part III establishes it for signal machines** (18 live signals,
    finite support, stack values in two distances, observable halt), with a
    prepared rational loader rather than an ordinary integer, and not for
    billiard-ball or block automata.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. The sources use MRDP only as an
  imported classical theorem (source 07 cites Matiyasevich and the Isabelle
  AFP entry); the project's formal endpoint is `Diophantine.mrdp`,
  `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26). The project has formalized none of this report's statements: its
  Lean development has no signal-machine, collision-chronology,
  polyhedral-chamber, cellular-automaton or Presburger-compiler module. One
  imported ingredient of Part IV is formalized elsewhere in the repository:
  Cooper's quantifier elimination for Presburger arithmetic,
  `Logic/PresburgerArithmetic/Lean` (for instance
  `PresburgerArithmetic.Formula.holds_iff_quantifierEliminate` and the
  decision procedure `PresburgerArithmetic.Formula.presburgerArithmetic_decidable`);
  that formalizes the imported step only, not Part IV's statements. The
  project README (`Computability/HilbertTenthProblem/README.md`, line 16)
  still states the 75- and 87-operation bounds; no Part bears on them.

## Reviews and patches

All in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.
None changes a theorem of this report; the reductions are the programme's and
are not printed as results here. Delivered programs are shipped unpatched
except where a source itself shipped the patched program (source 12).

- Sources 07 and 11: `incoming_substrate_review_808b53ed8.md` and
  `incoming_signal_review_808b.md` (commit `126028588`). PASS, no mandatory
  correction; its Transfer A deletes source 11's identically zero same-birth
  rows and redundant same-death rows and erases the initial-order slacks
  when `K > 0` or halting (the worked annihilation goes from 6 residuals and
  5 witnesses to 4 and 4; a natural-integer, not nonnegative-rational,
  zero-set bijection); its Transfer B deletes redundant strict rows from
  source 07's five exported packets.
- Source 12, earlier edition (batch-79 manuscript 07):
  `review_conservative_signal_2a8a39599.md`,
  `review_conservative_signal_independent.md` (commit `9f033fa6e`). PASS for
  the construction; independent enumeration of all 49,700 modes and 80,501
  branches; noncancellation of the trillion-term count; three input
  validation defects of the generic evaluator (padded output `(1,999)`,
  floating endpoint, surplus `None` slack) and mutable nested records,
  repaired by `conservative_signal_packet_domains.patch`. Source 12 is the
  corrected archive with exactly this patch applied.
- Source 12 itself: `review_conservative_signal_corrected_aebfa386e.md`
  (commit `9df1f72ca`). All ten author entrypoints and the three correction
  runs pass; no new valid-domain defect. It adds a natural-domain guard
  projection (natural zero sets only, not nonnegative reals) reducing the
  literal step packet to 2,747,980 witnesses and 1,313,943 squared residuals,
  with an explicit schedule 7,489,424 operations shorter.
- Source 13: `review_sparse_lattice_aebfa386e.md` (commit `9975af7e1`). Sound
  within its stated domains; checked the rule (8.2) sign against the primary
  paper; regenerated both Morita fixtures; one low-level finding (P2): the
  public `Poly` constructor of `sparse_mass.py` accepts float coefficients and
  mutable terms, repaired by `sparse_mass_exact_polynomials.patch`, which
  was **not** applied: at the batch-79 write the shipped
  `code/13-sparse-lattice-sparse_mass.py` was the delivered original.
  **Batch 80:** it is now source 13's corrected code edition (arrival
  `4e270aa46`, placement `8a4e64732`), written after reading (not running)
  this review: `Poly.__post_init__` requires a tuple of
  `(monomial, coefficient)` tuples, exact `int` indices and coefficients
  (not `bool`, float or subclasses), nonzero coefficients, sorted indices
  and distinct sorted monomials; `Poly.make` stays the canonicalizer, and
  negative (parameter) and repeated (power) indices remain valid. Its new
  suite `code/13-sparse-lattice-test_poly_exactness.py` passes on the
  shipped file and on the original with the review's patch; with
  `--baseline-module` on the original it reproduces the floating false
  zero (residual `0.0` at `2**60+1`, witness accepted) and the mutable
  alias (3, then 6). **Do not apply the patch to the shipped file**: the
  repair is already present, and the patch would apply with fuzz 2 and
  insert a second `__post_init__` (the later definition wins). The
  correction audit `review_batch80_corrected.md` (commit `abfc0cb25`)
  confirms the repair and that removing the new guard leaves the module's
  syntax tree identical to the original's. One disclosure on the suite
  (delivered file unchanged): in baseline mode its receipt field
  `"noncanonical_examples_accepted": 3` is a literal, and the loop feeds
  the original only three of the four noncanonical forms listed in
  `13-sparse-lattice-CORRECTION.md` (not the explicit zero coefficient,
  which the original also accepts, as checked at this write).
  Later: `sparse_lattice_projection.md` (commit `352ec5c1c`) reduces the
  preferred ledger to `V = T[M(S+7) + 4M(M−1)]`, `R = T[10M + 4M(M−1)]`, and
  `presburger_congruence_five.md` (commit `d175245d7`) lowers the
  post-elimination witness count from `2I + 6C + G` to `2I + 5C + G`.
- Placement: `review_placement_a7ae02511.md` (commit `653349f6a`)
  authenticates every file of sources 12 and 13 shipped here against the
  delivered archives, with a stager that restores the delivered layouts.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
mathtools, microtype, booktabs, longtable, ragged2e, xcolor, TikZ, enumitem,
fancyhdr, listings, xurl, hyperref). The committed build has 120 pages: no
errors, no undefined references or citations, no multiply defined labels,
no duplicate destinations, no overfull boxes. The log's only box messages
are four underfull lines in bibliography entries: three in `reversible`,
which the delivered source 07 already produces, and one in `moritaimai`,
source 13's entry as delivered.

The rebuild for the batch-79 reciprocal notes (cluster J2) found that the
batch-79 build had in fact two "destination with the same identifier
(name{table.4})" warnings: the uncaptioned notation longtable of Parts
III–IV steps the table counter, which `\addtocounter{table}{-1}` then
rewinds, so its hyperlink anchor collided with that of Table 4. The
longtable now gets its own anchor name (`\theHtable` redefined inside its
`center` group); no printed number or text changed, and the new build has
119 pages and the clean log described above, with no duplicate destination
(label numbers compared in the `.aux`).

The batch-80 notes of cluster K1 (the corrected code edition of source 13:
one dated paragraph, updated sentences and one bibliography entry appended
last; no label, macro or package) add one page, 120 pages, whose last page
holds the end of the new entry. The log is as described above (no errors,
warnings, undefined references or citations, multiply defined labels,
duplicate destinations or overfull boxes; the same four underfull
bibliography lines). The `.aux` of a build of the previous text has the
same 252 labels with the same numbers and the same 35 earlier bibliography
numbers (`reviewbeighty` is 36). The pages with the new paragraph, the
provenance table of Parts III–IV and the bibliography were rendered and
inspected.

## Rerunning the programs

All suites import their companion modules by their delivered names and
expect the delivered layout; several rewrite their own records. **Never run
them in place.** `py` is the Python launcher on this machine; the delivered
texts say `python` or `python3`. Python 3.10 or newer, standard library only,
assertions enabled (never `-O`, except where source 12's correction test asks
for it).

Sources 07 and 11 — copy the files to a scratch directory with the delivered
layout:

```sh
R=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates
# source 07
mkdir -p r07/code r07/data
cp $R/code/07-collision-geometry-run_checks.py r07/code/run_checks.py
cp $R/code/07-collision-geometry-signal_certificates.py r07/code/signal_certificates.py
(cd r07 && py code/run_checks.py)        # rewrites r07/data/*.json (7 files)
# source 11
mkdir -p r11/scripts r11/examples r11/expected_receipts
for s in run_replay signal_geometry signal_sparse verify_additional verify_examples; do
  cp $R/code/11-signal-certificates-$s.py r11/scripts/$s.py; done
for e in signal_geometry signal_sparse; do
  cp $R/data/11-signal-certificates-${e}_examples.json r11/examples/${e}_examples.json; done
for r in additional_verification signal_geometry signal_sparse worked_examples; do
  cp $R/data/11-signal-certificates-expected-${r}_receipt.json r11/expected_receipts/${r}_receipt.json; done
(cd r11 && py scripts/run_replay.py --output out)   # writes r11/out/
```

At the batch-78 write (Windows, Python 3.14.4, `PYTHONUTF8=1`) both passed.
Source 07's suite reported PASS with 34,560 assertions in about 4 s, and its
seven regenerated JSON files equal the shipped ones apart from line endings:
the Windows run writes CRLF, the shipped files are LF. Source 11's replay
(about 18 s) matched all four expected receipts and both coefficient-example
files; it runs the scripts in a temporary directory and writes only its
output directory. The placement-time runs (12.7 s and 39.2 s) and the
programme's review (Python 3.13.14) agree. Running source 11's individual
scripts directly writes their receipts into the current directory.

Sources 12 and 13 have deeper layouts (45 and 49 files, with the excluded
data; source 13's corrected edition has 52). Restore the delivered layout in one of two ways, never in the report
directory:

```sh
# (a) from the arrival archive (contains the excluded files too)
mkdir r12 r13
git show aebfa386e:docs/incoming/Conservative_Signal_Frontend_Corrected.zip > r12/cs.zip
git show 4e270aa46:docs/incoming/Sparse_Lattice_Diophantine_Certificates_corrected.zip > r13/sl.zip   # corrected edition
(cd r12 && unzip -q cs.zip)    # r12/conservative-signal-release/
(cd r13 && unzip -q sl.zip)    # r13/sparse-lattice-release/
# (b) from the shipped files, with the research tree's placement stager
#     (authenticates the shipped bytes, restores the omitted members from Git;
#      the destination must not exist)
py Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py \
   --repo . --destination ../placed-a7ae02511
```

Way (a) is the tested one. Way (b) was tried at this write on this Windows
checkout (7 s): it restored `conservative-signal-release/` and
`sparse-lattice-release/` byte-identical to the archives, including the
excluded files, which it takes from Git, but then stopped with "Restored
complete package manifest differs" while checking the six package roots it
restores (the other four belong to `quadratic-orthant-certificates` and
`canonical-diophantine-certificates`). The stager is the research tree's
program, not part of this report. Since batch 80 it authenticates only a
checkout of `a7ae02511` (`git worktree add <dir> a7ae02511`), where it
restores source 13's original edition; on a current checkout it stops
earlier, with "Placed source differs" at the five replaced files. For the
corrected layout use way (a).

Then, in `conservative-signal-release/` (source 12): `sh run-replay.sh` runs
the ten original commands; it hard-codes `python3` and rewrites its receipts
(`receipts/*.json`), recorded data and `numeric/COMPACT_VERIFICATION.json` in place, so on
this machine run its commands one by one with `py` (they are listed in
`code/12-conservative-signal-run-replay.sh`), or put a `python3` that
resolves to Python 3.10+ first on `PATH`. Three of them
(`instantiate_morita.py`, `independent_checks.py`, `pivot_scale_checks.py`)
took more than three minutes each here and were not completed at placement;
the programme's reviews ran all ten. The correction test is
`py correction/verify_packet_correction.py code/quadratic_packet.py`
(add `--original <path>` with the unpatched evaluator from `cs-original.zip`
to compare). At placement on a copy: `compile_packet.py verify` PASS (15 s),
`test_exporter.py`, `check_original_replays.py` (13,798 events), the
correction test (1,200 cases, 72 sections, 66 rejections), and the other
four commands passed, with all receipts equal to the delivery apart from
line endings.

In `sparse-lattice-release/` (source 13): `sh run-replay.sh` (that is,
`py replay/run_release.py`) copies the code to `.replay/` and compares with
the shipped receipts; it leaves the release files unchanged. Its receipts
record byte sizes, so it fails at its first stage on Windows, where Python
writes CRLF: run it on POSIX or WSL, or with a newline shim. The default run
takes more than three minutes here (the n=2 bound replay alone takes 75 s);
both ways (a) and (b) supply the two Morita fixtures; a layout assembled by
hand from the shipped files lacks them, so regenerate them first (see
"Reconstructing the excluded data"). At placement every stage passed under
an LF shim (the last two bound replays, which the three-minute cap
interrupted, were run separately and were valid), and the programme's review
ran both complete eighteen-stage replays. Since batch 80 the runner has the
exactness stage first (nineteen stages with `--regenerate-source`,
seventeen without). At this write the suite was run on a copy of the
shipped `sparse_mass.py` and suite (with the fixture
`binary_three_way_collision.json` beside them as `fixtures/`; about 1 s):
PASS, and its `--output` receipt equals
`data/13-sparse-lattice-poly-exactness.json` after removing carriage
returns; with `--baseline-module` pointing at the original
(`git show a7ae02511:<path of code/13-sparse-lattice-sparse_mass.py>`) it
passes and reports the false zero. The batch-80 placement check also reran,
in the extracted corrected archive under an LF shim,
`replay/verify_manifest.py` (51 files), `core/run_checks.py` and
`crosscheck_row_producer.py` (receipts equal, including the new producer
hash `3a8b4747…`), the bound replays of the four generic fixtures and the
n=0 fixture, `two-mass/regression.py` and `semilinearity/check.py`; it did
not repeat the full `--regenerate-source` run (over three minutes), whose
other stages run unchanged code on unchanged data.

## Discrepancies and disclosures

- The shipped build scripts keep the delivered layout:
  `code/07-collision-geometry-Makefile` runs `python3 code/run_checks.py` and
  `latexmk` on `article.tex` from the package root;
  `code/11-signal-certificates-build.sh` runs pdflatex three times on an
  `article.tex` that is not there; `code/12-conservative-signal-build.sh` and
  `code/13-sparse-lattice-build.sh` build `paper/conservative-signal-diophantine.tex`
  and `paper/sparse-lattice.tex`, which are not shipped, and copy a PDF to the
  package root. None builds this report; use the build command above.
- Delivered names in shipped and printed text: Part I's Sections 14.1–14.2
  and Appendix A, Part II's Appendix C and source 11's `REPRODUCIBILITY.md`
  name delivered paths (`code/…`, `data/checks.json`, `tournament_left.json`,
  `scripts/…`, `examples/…`, `expected_receipts/…`, `build.sh`); `[write]`
  notes in Section 14.2 and Appendices A and C give the shipped names.
  Source 11's `REPRODUCIBILITY.md` describes `CHECKSUMS.sha256` and the
  delivered `article.tex` and `article.pdf`, and its `manifest.json` lists
  the delivered `README.md`, `article.tex` and `article.pdf` among its
  payload files; none of these is shipped under that name. Source 07's
  `PROVENANCE.md` names no package file.
- Source 12's shipped texts use delivered names: `12-conservative-signal-CORRECTION.md`
  names `code/quadratic_packet.py`, `run-replay.sh`,
  `correction/verify_packet_correction.py`, `SHA256SUMS` and
  `correction/conservative_signal_packet_domains.patch` (not shipped; it is
  the research tree's file of that name, already applied) and gives commands
  with `python3`; `12-conservative-signal-PROOF_AND_LEDGER.md` names
  `MODES.jsonl.gz` and `EVENTS.jsonl.gz` (excluded, regenerable),
  `RESIDUALS.jsonl.gz`, `BRANCHES`/verbose exports, `MODES.bin`,
  `EVENTS.bin` and `EXPANDED.jsonl.gz` (never shipped by the delivery
  either); `data/12-conservative-signal-POLYNOMIAL_CIRCUIT.json` and
  `FULL_REPLAY_PRESERVATION.json` name the two excluded `.gz` files;
  `data/12-conservative-signal-SOURCE_MANIFEST.json` records digests of
  primary-source PDFs that were never shipped. Parts III's `[write]` notes at
  the end of Section 37 and in Appendix H give the shipped names.
- Source 13's shipped texts use delivered names:
  `13-sparse-lattice-SOURCE-PROVENANCE.md` names `replay/morita/audit.py`
  and `replay/core/morita_audit.py` (shipped once, as
  `code/13-sparse-lattice-morita_audit.py`); the receipts
  `data/13-sparse-lattice-morita-n{0,2}.json` and
  `release-verification.json` describe the two excluded fixtures and record
  their `compressed_bytes`. Batch 80: `13-sparse-lattice-CORRECTION.md` and
  the dated preface of `13-sparse-lattice-SOURCE-PROVENANCE.md` name
  `replay/core/sparse_mass.py`, `replay/core/test_poly_exactness.py`,
  `receipts/*.json`, `run-replay.sh`, `replay/verify_manifest.py` and
  `SHA256SUMS` (the last two not shipped), and give commands with `python3`
  "from this directory"; `code/13-sparse-lattice-test_poly_exactness.py`
  imports `sparse_mass` by its delivered name and reads
  `fixtures/binary_three_way_collision.json` beside itself; the corrected
  `run_release.py` runs `core/test_poly_exactness.py` by delivered path.
  Written in the article for batch 80: the dated paragraph in Section 47,
  and updated sentences in the front section (reviews), the paragraphs on
  the release and on the review in Section 47, the provenance paragraph
  and table of Parts III–IV, and one bibliography entry,
  `reviewbeighty`, appended last. No label, statement or number changed
  (the corrected archive's `.tex` files are byte-identical), and no label
  was added.
- Source 13's two CSV tables have CRLF line ends as delivered; the lines
  `docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-doubling-complete.csv -text`
  and `…/data/13-sparse-lattice-false-signal-complete.csv -text` in
  `SetTheory/Cardinals/.gitattributes` keep them byte for byte. Its receipt
  `data/13-sparse-lattice-morita-source.json` has no final newline, as
  delivered.
- Source 12's article notes that a paragraph of Morita's survey reverses the
  letters of a production relative to Example 3.3 and Figure 28; the report
  keeps the article's convention (the figure, which the 184-step replay
  matches). The programme's reviews did not re-authenticate Morita's printed
  table visually (the 2008 PDF was unavailable to them).
- Source 11's `manifest.json` author fields read "Jérôme Durand-Lose" in
  correct UTF-8 (bytes `C3 A9`, `C3 B4`); a placement note that suspected
  double-encoded UTF-8 there was checked at the write and is unfounded.
- Source 07 records its repository snapshot `f1edb38f9` and the audit blob it
  read; the audit is unchanged at the write, and the project README has gained
  text since the pin while still stating the 75/87 bounds. Sources 11, 12 and
  13 name no repository snapshot.
- The delivered title pages are replaced by one. Each source's title and
  abstract open its Part verbatim, and each source's author line is quoted
  there, except source 12's: its title page says "Research note prepared with
  AI assistance for private review", which Part III's opening replaces by a
  neutral description in this public report (the wording is recorded in
  Appendix E). Credit notes were added to source 07's abstract and
  conclusion, marked `[write]`.
- AI wording kept as delivered: source 07 "prepared with ChatGPT", source 11
  "Research report prepared with OpenAI" (PDF metadata only), source 13
  "Research report prepared with AI assistance for Vladimir".
