# Collision Geometry Is Linear

**Diophantine Certificates for Rational Signal Machines and Conservative Particle Dynamics: event-sparse chambers, canonical quadratic and quartic certificates, two routes to complete chronology, a conservative universal frontend, sparse lattice certificates, and conserved-mass thresholds**

This is a research report dated 2 October 2026, built from eight AI-assisted
research manuscripts of ProveIt's incoming reports: manuscripts 07 and 11 of
batch 78 (Parts I and II), manuscripts 16 and 19 of batch 79 (Parts III and
IV), and manuscripts 10, 02, 05 and 03 of batch 80 (Parts V and VI). The
report calls them *source 07*, *source 11* and *source 12* to *source 17*
after the file prefixes of their shipped programs and data. For the first two
the prefix is also the batch-78 manuscript number; for the others it is not:
**source 12 is batch-79 manuscript 16, source 13 is batch-79 manuscript 19,
source 14 is batch-80 manuscript 10, source 15 is batch-80 manuscript 02,
source 16 is batch-80 manuscript 05, and source 17 is batch-80 manuscript
03** (the prefixes continue this report's own sequence). Source 07 is
"prepared with ChatGPT for Vladimir Reshetnikov's ProveIt research
program", source 11's document metadata name "Research report prepared with
OpenAI", source 12 is an AI-assisted research note, and source 13 is a
"Research report prepared with AI assistance for Vladimir". Sources 14–17
carry the author lines "Mathematical construction and reproducibility
report", "A clean return extension of the reversible weighted CA
construction", "Decidability theorem and executable checks" and "Decidability
proof and a binary timing certificate"; they name no assistant, and the
article describes them as AI-assisted research manuscripts.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 07 (base) | batch 78, manuscript 07 | `Collision_Geometry_Diophantine_Signal_Machines.zip` (`808b53ed8`); *Collision Geometry Is Linear: Event-Sparse Quadratic Diophantine Certificates for Rational Signal Machines*, main file `collision_geometry/article.tex`, 29-page PDF | `f1edb38f9` (audit blob `cb31d0a10`) | `798b0c5d4` | Part I (Sections 2–16) and Appendices A–B |
| 11 | batch 78, manuscript 11 | `Signal_Machine_Diophantine_Certificates.zip` (`808b53ed8`); *Direct Diophantine Certificates for Rational Signal Machines: Finite collision schemas with unique quadratic witnesses*, main file `signal-diophantine-release/article.tex`, 15-page PDF | none named | `798b0c5d4` | Part II (Sections 17–28) and Appendices C–D |
| 12 | batch 79, manuscript 16 | `Conservative_Signal_Frontend_Corrected.zip` (`aebfa386e`); *Conservative signal machines as Diophantine frontends*, main file `paper/conservative-signal-diophantine.tex` with `paper/morita-table.tex`, 21-page PDF; the corrected edition of batch-79 manuscript 07 (`Conservative_Signal_Diophantine_Frontend.zip`, `2a8a39599`), which is superseded and not shipped | none named (its `CORRECTION.md` cites the review commit `9f033fa6e`) | `a7ae02511` | Part III (Sections 29–37) and Appendices F–H |
| 13 | batch 79, manuscript 19 | `Sparse_Lattice_Diophantine_Certificates.zip` (`aebfa386e`); *Sparse Diophantine certificates for finite mass lattice dynamics*, main file `paper/sparse-lattice.tex` reading five further files, 27-page PDF; corrected code edition `Sparse_Lattice_Diophantine_Certificates_corrected.zip` (batch 80, manuscript 07, `4e270aa46`) | none named | `a7ae02511`; corrected code `8a4e64732` | Part IV (Sections 38–48) |
| 14 | batch 80, manuscript 10 | `Three_Mass_Reversible_Computation.zip` (`4e270aa46`); *Three mass units in a reversible weighted cellular automaton*, main file `three-mass-release/three-mass-report.tex` (also as four modular files under `tex/`), 24-page PDF | none named | `345a9e44e` | Part V (Sections 49–63) |
| 15 | batch 80, manuscript 02 | `Exact_Targets_Three_Mass_Units.zip` (`4e270aa46`); *Exact targets with three conserved mass units*, main file `clean-target-release/clean-target-report.tex`, 15-page PDF; a declared extension of source 14 | source 14 by SHA-256 ("frozen companion release 9": its TeX, PDF and ledger) | `345a9e44e` | Part V (Sections 64–73) |
| 16 | batch 80, manuscript 05 | `Single_Unit_Three_Mass_Decidability (1).zip` (`4e270aa46`; note the space before the parenthesis); *Three mass units with a single unit symbol*, main file `single-unit-three-mass/single-unit-mass-three.tex`, 10-page PDF; the attribution revision of batch-80 manuscript 06 (`Single_Unit_Three_Mass_Decidability.zip`, 9-page PDF), which is superseded and not shipped | none named (cites source 13 by title) | `345a9e44e` | Part VI (Sections 74–82) |
| 17 | batch 80, manuscript 03 | `Four_Mass_Decidability_Package.zip` (`4e270aa46`); *Four mass units and exact reachability*, main file `four-mass-bound/four-mass-decidability.tex`, 12-page PDF | none named (cites source 16 as its companion) | `345a9e44e` | Part VI (Sections 83–92) |

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

**Parts V and VI find the least conserved mass of an undecidable
observation (batch 80).** Both work in Part IV's weighted model (finite
alphabet and radius, positive integer weights, a unique zero-weight vacuum).
Part V (sources 14 and 15): when many symbols have weight one (a power-set
alphabet of Boolean channels, weight = cardinality), a fixed globally
reversible, mass-conserving cellular automaton of forward and inverse radius
at most four (radius one by four-site blocking at the same clock, or by
four-phase dilation at four times the time) simulates every separated
reversible two-counter machine at total mass exactly three, with gap
`12·2^a·3^b` and a clean halt symbol, so three is the least mass with
fixed-rule undecidable pattern occurrence there (Theorems 49.1–49.2, with
Part IV's Theorem 44.1 as the lower half); exact type and row counts, exact
microtimes and a degree-two natural certificate with a unique witness at each
fixed source horizon (Theorem 58.1). Source 15 wraps a fresh-entry source so
that it runs forward, then its logical inverse, then relabels: exact-pair
reachability `∃t A^t(x_N) = y_N` between two computable mass-three
configurations of the same support is undecidable for one fixed reversible
rule (Theorems 64.1, 67.1), with an exact first-target clock and a compact
certificate whose natural zero fibres are in affine bijection with those of
the full wrapped certificate (Theorem 70.2). Part VI (sources 16 and 17): with
at most one weight-one symbol (for example an integer-state number-conserving
automaton), the timed relation at mass at most three is effectively
Presburger, uniformly in all positions and the time (Theorem 74.1), and exact
reachability and pattern occurrence stay decidable at mass four (Theorem
83.1), where a binary radius-six shuttle with hit times `k² + (2d−11)k`
shows that the timed relation is no longer Presburger (Proposition 89.2). So
integer-state automata need at least five particles. Sections 1.12–1.16
introduce the two Parts, with a threshold table.

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs and
finite exact-arithmetic checks. Nothing in the report is formalized in Lean or
Rocq, and no priority is certified.

**Already reviewed.** All four manuscripts of Parts I–IV were reviewed in the
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

**Batch 80 (Parts V and VI) was reviewed too, before this write.** The
research tree reviewed sources 14 and 15 in `review_batch80_three_mass.md`
(commit `933600302`) and sources 16 and 17 with manuscript 06 in
`review_batch80_low_mass.md` (commit `7f1161730`): "PASS within the stated
model and interfaces" and "PASS within the stated mathematical and executable
scopes", with no repair or correction; its index
`incoming_substrate_review_4e270aa46.md` (commit `e903a3f35`, updated in
`3aa123856`) lists both, and `review_batch80_mass_placement_345a9e44e.md`
(commit `3aa123856`) authenticates the 116 files placed here. Those reviews
concern the archives and the placement; the assembled text of Parts V and VI
has not been reviewed by the research tree ("A subsequent assembled
mathematical write will need a new semantic-transfer review", in the
placement review).

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
article.pdf                                                     the compiled report, 193 pages (unnumbered title page, then pages 1–192)
README.md                                                       this guide
07-collision-geometry-PROVENANCE.md                             source 07's repository and literature provenance, as delivered
11-signal-certificates-REPRODUCIBILITY.md                       source 11's reproducibility record, as delivered
12-conservative-signal-CORRECTION.md                            source 12's account of the generic-evaluator correction, as delivered
12-conservative-signal-PROOF_AND_LEDGER.md                      source 12's mode-closure proof and numeric packet ledger, as delivered
12-conservative-signal-SOURCE-PROVENANCE.md                     source 12's primary sources (Durand-Lose, Morita) and the Table 5 discrepancy, as delivered
13-sparse-lattice-CORRECTION.md                                 source 13's corrected edition: the exact Poly constructor, scope and evidence, as delivered (batch 80)
13-sparse-lattice-SOURCE-PROVENANCE.md                          source 13's provenance, primary sources and packaging changes, as delivered (batch-80 corrected edition, with a dated preface)
14-three-mass-SOURCE_PROVENANCE.md                              source 14's frozen generator identity and source/receipt conventions, as delivered
15-clean-targets-CLEAN-TARGET-THEOREM.md                        source 15's audited statement of the exact-target theorem, as delivered
15-clean-targets-INDEPENDENT-AUDIT.md                           source 15's independent review of the wrapper, clock and lift (delivered audit/), as delivered
15-clean-targets-SOURCE_PROVENANCE.md                           source 15's hashes of source 14 and of its vendored programs, portability adaptations, as delivered
16-single-unit-AUDIT.md                                         source 16's independent mathematical and executable audit (delivered independent/AUDIT.md)
16-single-unit-REVISION.md                                      source 16's attribution-revision note: what changed from batch-80 manuscript 06
16-single-unit-SOURCE-PROVENANCE.md                             source 16's primary sources (Kong, Imai, Alhazov-Imai), scope and dependencies, as delivered
17-four-mass-BINARY-EXPANDING-SHUTTLE.md                        source 17's binary rule, complete timing proof and arithmetic ledger, as delivered
17-four-mass-BINARY-INDEPENDENT-AUDIT.md                        source 17's independent audit of the binary shuttle (delivered independent/), as delivered
17-four-mass-EXPANDING-SHUTTLE.md                               source 17's earlier typed weighted shuttle used by its arithmetic audit, as delivered
17-four-mass-FINAL-REVIEW.md                                    source 17's final review note (delivered independent/), as delivered
17-four-mass-INDEPENDENT-AUDIT.md                               source 17's independent mathematical audit (delivered independent/), as delivered
17-four-mass-SOURCE-PROVENANCE.md                               source 17's primary-source scope and page mappings, as delivered
17-four-mass-finite-seed-section-lemma.md                       source 17's detailed finite seed library and threshold construction, as delivered
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
code/14-three-mass-build.sh                                     source 14's three-pass build of its own article (needs the unshipped tex/report.tex)
code/14-three-mass-certificate.py                               source 14's certificate exporter and witness builder (export / witness)
code/14-three-mass-checker.py                                   source 14's independent certificate checker
code/14-three-mass-export_examples.py                           source 14's exporter of the three literal rules and rule_index.json (rebuilds excluded data)
code/14-three-mass-legacy-certificate.py                        source 14's pre-clock exporter snapshot, for byte-compatibility regression (delivered code/legacy/)
code/14-three-mass-legacy-checker.py                            source 14's pre-clock checker snapshot (delivered code/legacy/)
code/14-three-mass-radius_one.py                                source 14's four-phase radius-one dilation
code/14-three-mass-replay.sh                                    source 14's full replay into .replay/ (python3, delivered layout)
code/14-three-mass-spatial_radius_one.py                        source 14's time-preserving four-site spatial blocking
code/14-three-mass-test_certificate_hardening.py                source 14's strict-input and hardening tests of the certificate code
code/14-three-mass-test_certificates.py                         source 14's producer certificate tests
code/14-three-mass-test_certificates_independent.py             source 14's independent certificate audit
code/14-three-mass-test_checker_mutations.py                    source 14's checker mutation tests
code/14-three-mass-test_clock_scale_independent.py              source 14's independent clock-scale audit (normal and -O)
code/14-three-mass-test_literal_exports.py                      source 14's check of the literal rule exports (reads the excluded rule files)
code/14-three-mass-test_radius_one.py                           source 14's phase-radius-one audit
code/14-three-mass-test_radius_one_boundaries.py                source 14's phase-radius-one boundary tests
code/14-three-mass-test_size_ledger.py                          source 14's type, row and path-closure count audit
code/14-three-mass-test_spatial_radius_one.py                   source 14's spatial-blocking audit
code/14-three-mass-test_three_mass_independent.py               source 14's independent local-CA and microstep simulator
code/14-three-mass-test_two_mass_arithmetic.py                  source 14's mass-two arithmetic tests (source 13's audit minus one line)
code/14-three-mass-three_mass_collision_generator.py            source 14's channel and collision-rule generator (the compiler)
code/15-clean-targets-audit_actual_ca.py                        source 15's independent lattice harness (delivered audit/; imports vendor/)
code/15-clean-targets-audit_certificates.py                     source 15's independent certificate audit (delivered audit/)
code/15-clean-targets-audit_lift_name_collisions.py             source 15's public-name collision regressions of the lift (delivered audit/)
code/15-clean-targets-audit_witness_lift.py                     source 15's independent affine-lift audit (delivered audit/)
code/15-clean-targets-build.sh                                  source 15's build of its own article (delivered layout)
code/15-clean-targets-check_clean_targets.py                    source 15's separate wrapper and certificate checker
code/15-clean-targets-clean_targets.py                          source 15's wrapper, compact exporter, witness builder and hygienic affine lift
code/15-clean-targets-replay.py                                 source 15's isolated replay (calls verify_manifest.py when SHA256SUMS exists)
code/15-clean-targets-test_affine_lift.py                       source 15's producer lift tests
code/15-clean-targets-test_clean_targets.py                     source 15's producer lattice and certificate tests
code/16-single-unit-audit_accelerator.py                        source 16's independent executable audit (delivered independent/)
code/16-single-unit-build.sh                                    source 16's build of its own article (delivered layout)
code/16-single-unit-run-tests.sh                                source 16's replay in a temporary copy with receipt comparison
code/16-single-unit-test_single_unit_acceleration.py            source 16's orbit accelerator and its direct-simulation comparisons
code/17-four-mass-audit_arithmetic.py                           source 17's independent section-arithmetic audit (delivered independent/)
code/17-four-mass-audit_binary_shuttle.py                       source 17's independent binary-shuttle replay (delivered independent/)
code/17-four-mass-binary_exact.py                               source 17's strict public helper for the binary rule and its certificate
code/17-four-mass-build.sh                                      source 17's build of its own article (delivered layout)
code/17-four-mass-check_binary_rule.py                          source 17's guarded-pattern reconstruction of the local rule (delivered independent/)
code/17-four-mass-draw_binary_shuttle_trace.py                  source 17's matplotlib renderer of the figure (delivered figures/)
code/17-four-mass-run-tests.sh                                  source 17's test runner (python3; regenerates receipts in place)
code/17-four-mass-test_binary_expanding_shuttle.py              source 17's producer checks; rewrites the conservation certificate in place
code/17-four-mass-test_exact_boundaries.py                      source 17's 13 boundary-test groups of binary_exact.py (normal and -O)
code/17-four-mass-test_expanding_shuttle.py                     source 17's typed weighted shuttle tests
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
data/14-three-mass-certificate-hardening.json                   receipt of test_certificate_hardening.py
data/14-three-mass-certificate-tests.json                       receipt of test_certificates.py
data/14-three-mass-chain_certificate.json                       expanded certificate of source 14's chain fixture
data/14-three-mass-chain_check.json                             checker receipt of the chain fixture
data/14-three-mass-chain_request.json                           request of the chain fixture
data/14-three-mass-chain_witness.json                           unique witness of the chain fixture
data/14-three-mass-checker-mutations.json                       receipt of test_checker_mutations.py
data/14-three-mass-clock-scale-optimized-tests.json             receipt of the clock-scale audit under -O
data/14-three-mass-clock-scale-tests.json                       receipt of the clock-scale audit
data/14-three-mass-generator-tests.json                         receipt of the generator's own suites
data/14-three-mass-independent-ca-tests.json                    receipt of the independent CA simulator (555,394 microsteps)
data/14-three-mass-independent-certificate-tests.json           receipt of the independent certificate audit
data/14-three-mass-literal-export-check.json                    receipt of test_literal_exports.py
data/14-three-mass-literal-export.json                          types, rows, sizes and SHA-256 of the three literal rules (files excluded)
data/14-three-mass-mixed_check.json                             checker receipt of the nine-step mixed fixture (Section 61.1)
data/14-three-mass-mixed_radius_one_check.json                  checker receipt of the phase-dilated mixed fixture
data/14-three-mass-mixed_radius_one_request.json                request of the phase-dilated mixed fixture (clock_scale 4)
data/14-three-mass-mixed_radius_one_witness.json                witness of the phase-dilated mixed fixture
data/14-three-mass-mixed_request.json                           request of the nine-step mixed fixture
data/14-three-mass-mixed_witness.json                           witness of the nine-step mixed fixture
data/14-three-mass-pdf-qa.json                                  source 14's record of its PDF check
data/14-three-mass-radius-one-boundaries.json                   receipt of the phase-radius-one boundary tests
data/14-three-mass-radius-one-tests.json                        receipt of the phase-radius-one audit
data/14-three-mass-replay-summary.json                          summary of source 14's replay (names the five excluded exports)
data/14-three-mass-rule_index.json                              index of the three literal rules with sizes and SHA-256 (files excluded)
data/14-three-mass-size-ledger-tests.json                       receipt of test_size_ledger.py
data/14-three-mass-spatial-radius-one-optimized-tests.json      receipt of the spatial-blocking audit under -O
data/14-three-mass-spatial-radius-one-tests.json                receipt of the spatial-blocking audit
data/15-clean-targets-actual-ca-receipt.json                    receipt of audit_actual_ca.py
data/15-clean-targets-affine_lift.json                          receipt of the producer lift tests
data/15-clean-targets-certificate-receipt.json                  receipt of audit_certificates.py
data/15-clean-targets-chain_certificate.json                    compact certificate of the worked example (Section 71)
data/15-clean-targets-chain_receipt.json                        checker receipt of the worked example
data/15-clean-targets-chain_request.json                        request of the worked example (N0 = 5, h = 5)
data/15-clean-targets-chain_witness.json                        unique witness of the worked example
data/15-clean-targets-final-prose-review.json                   source 15's record of its final prose review
data/15-clean-targets-lift-name-collision-receipt.json          receipt of audit_lift_name_collisions.py
data/15-clean-targets-portable-replay.json                      source 15's portable replay record
data/15-clean-targets-report-qa.json                            source 15's record of its PDF check
data/15-clean-targets-source-provenance.json                    hashes of source 14's files and the vendored programs (delivered provenance/)
data/15-clean-targets-test_clean_targets.json                   receipt of test_clean_targets.py
data/15-clean-targets-upstream-extension-manifest.json          manifest relating source 15 to source 14 (delivered provenance/)
data/15-clean-targets-witness-lift-receipt.json                 receipt of audit_witness_lift.py
data/16-single-unit-audit-results.json                          receipt of the independent audit (delivered independent/audit-results.json)
data/16-single-unit-test-results.json                           receipt of the accelerator tests (7,127 orbit cases)
data/17-four-mass-audit-arithmetic-results.json                 receipt of audit_arithmetic.py
data/17-four-mass-binary-four-particle-shuttle.csv              trace data of the figure (CRLF, kept byte for byte)
data/17-four-mass-binary-four-particle-shuttle.json             trace data of the figure
data/17-four-mass-binary-independent-audit-results.json         receipt of audit_binary_shuttle.py
data/17-four-mass-binary-radius6-conservation-certificate.json  the 8,192 rule bits and 4,096 de Bruijn potentials of the binary rule
data/17-four-mass-binary-rule-receipt.json                      receipt of check_binary_rule.py
data/17-four-mass-binary-shuttle-test-results.json              receipt of test_binary_expanding_shuttle.py
data/17-four-mass-exact-boundary-results.json                   receipt of test_exact_boundaries.py
data/17-four-mass-portable-replay-results.json                  source 17's record of a portable ZIP replay
data/17-four-mass-shuttle-test-results.json                     receipt of test_expanding_shuttle.py
figures/17-four-mass-binary-four-particle-shuttle.pdf           source 17's article figure (vector PDF, printed as Figure 5)
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery; for source 13 the delivery is, since
batch 80, the corrected code edition (its other 30 shipped files are
byte-identical in both editions). Delivered name → shipped name:

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
- Source 14 (`three-mass-release/`): `build.sh`, `replay.sh` and
  `code/*.py` → `code/14-three-mass-<file name>`; `code/legacy/*.py` →
  `code/14-three-mass-legacy-<file name>`; `examples/*.json` (the eleven
  kept) and `receipts/*.json` → `data/14-three-mass-<file name>`;
  `SOURCE_PROVENANCE.md` → `14-three-mass-SOURCE_PROVENANCE.md`.
- Source 15 (`clean-target-release/`): the top-level `*.py` and `build.sh`
  and `audit/*.py` → `code/15-clean-targets-<file name>`; `examples/*.json`,
  `receipts/*.json` and `provenance/*.json` →
  `data/15-clean-targets-<file name>`; `CLEAN-TARGET-THEOREM.md`,
  `SOURCE_PROVENANCE.md` and `audit/INDEPENDENT-AUDIT.md` →
  `15-clean-targets-<file name>`. The five `vendor/*.py` are byte copies of
  source 14's `code/certificate.py`, `checker.py`, `radius_one.py`,
  `spatial_radius_one.py` and `three_mass_collision_generator.py` and are
  shipped once, as `code/14-three-mass-*`.
- Source 16 (`single-unit-three-mass/`): `test_single_unit_acceleration.py`,
  `independent/audit_accelerator.py`, `run-tests.sh` and `build.sh` →
  `code/16-single-unit-<file name>`; `test-results.json` and
  `independent/audit-results.json` → `data/16-single-unit-<file name>`;
  `REVISION.md`, `SOURCE-PROVENANCE.md` and `independent/AUDIT.md` →
  `16-single-unit-<file name>`.
- Source 17 (`four-mass-bound/`): the top-level `*.py`, `run-tests.sh`,
  `build.sh`, `independent/*.py` and `figures/draw_binary_shuttle_trace.py`
  → `code/17-four-mass-<file name>`; the top-level `*.json`,
  `independent/*.json` and `figures/binary-four-particle-shuttle.{json,csv}`
  → `data/17-four-mass-<file name>`; `figures/binary-four-particle-shuttle.pdf`
  → `figures/17-four-mass-binary-four-particle-shuttle.pdf` (printed as
  Figure 5); the top-level `*.md` other than `README.md` and
  `independent/*.md` → `17-four-mass-<file name>`.

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
  is the unpatched evaluator);
- for sources 14–17 (batch 80): the four manuscripts (printed as Parts V
  and VI) and source 14's four modular TeX files `tex/{report,certificate,slowdown,verification}.tex`
  (which expand to its standalone file); the four PDFs and four delivery
  READMEs; the checksum ledgers, all verified at placement (source 14's
  `SHA256SUMS`, 65 of 65; source 15's, 37 of 37; source 16's, 12 of 12;
  source 17's, 32 of 32) and the manifest checkers `verify_manifest.py` of
  sources 14 and 15; source 15's five `vendor/*.py` (byte copies of source
  14's programs, shipped once); source 14's
  `receipts/two-mass-arithmetic-tests.json` (a byte copy of
  `data/13-sparse-lattice-two-mass-arithmetic.json`); source 17's raster
  figure `figures/binary-four-particle-shuttle.png` (the vector PDF is
  shipped); five heavy regenerable exports of source 14 (next section);
- all twelve files of batch-80 manuscript 06
  (`Single_Unit_Three_Mass_Decidability.zip`), the superseded original of
  source 16 (seven of them are byte-identical to source 16's; its manuscript,
  README, provenance record, PDF and ledger differ only in the attribution,
  `16-single-unit-REVISION.md`).

```sh
git show 808b53ed8:docs/incoming/Collision_Geometry_Diophantine_Signal_Machines.zip > cg.zip
git show 808b53ed8:docs/incoming/Signal_Machine_Diophantine_Certificates.zip > sd.zip
git show aebfa386e:docs/incoming/Conservative_Signal_Frontend_Corrected.zip > cs.zip
git show aebfa386e:docs/incoming/Sparse_Lattice_Diophantine_Certificates.zip > sl-original.zip   # source 13, original edition
git show 4e270aa46:docs/incoming/Sparse_Lattice_Diophantine_Certificates_corrected.zip > sl.zip   # source 13, corrected edition (preferred)
git show 2a8a39599:docs/incoming/Conservative_Signal_Diophantine_Frontend.zip > cs-original.zip
git show 4e270aa46:docs/incoming/Three_Mass_Reversible_Computation.zip > tm.zip            # source 14
git show 4e270aa46:docs/incoming/Exact_Targets_Three_Mass_Units.zip > ct.zip               # source 15
git show "4e270aa46:docs/incoming/Single_Unit_Three_Mass_Decidability (1).zip" > su.zip  # source 16
git show 4e270aa46:docs/incoming/Four_Mass_Decidability_Package.zip > fm.zip               # source 17
git show 4e270aa46:docs/incoming/Single_Unit_Three_Mass_Decidability.zip > su-original.zip # manuscript 06 (superseded)
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

**Source 14 (batch 80).** Five literal exports of source 14 (20,752,637 bytes
together) are not shipped either. Each is rebuilt by a shipped program in the
delivered layout of `Three_Mass_Reversible_Computation.zip`
(`git show 4e270aa46:docs/incoming/Three_Mass_Reversible_Computation.zip > tm.zip`,
then extract it into a scratch directory; it unpacks to
`three-mass-release/`). The simplest way to obtain the exact delivered bytes
is the archive itself.

| Excluded file (delivered path) | Bytes | Rebuild, from the extracted archive root | Time here | Result |
|---|---:|---|---|---|
| `examples/cycle_rule.json` | 11,103,617 | `py code/export_examples.py <dir>` (one run writes all three rules and `rule_index.json`) | 4–6 s | byte-identical |
| `examples/merge_rule.json` | 4,110,941 | the same run | — | byte-identical |
| `examples/trap_rule.json` | 1,936,965 | the same run | — | byte-identical |
| `examples/mixed_certificate.json` | 1,791,538 | `py code/certificate.py export examples/mixed_request.json <out> --expanded` | 0.5 s | identical after removing the CR bytes that Windows text mode adds |
| `examples/mixed_radius_one_certificate.json` | 1,809,576 | `py code/certificate.py export examples/mixed_radius_one_request.json <out> --expanded` | 0.5 s | likewise |

`export_examples.py` writes the rules with `write_bytes` (LF on every
platform) but `rule_index.json` in text mode (CRLF on Windows). The shipped
`data/14-three-mass-rule_index.json` and `data/14-three-mass-literal-export.json`
record each rule's SHA-256 and byte count, so a rebuild can be checked against
them. `code/14-three-mass-test_literal_exports.py` reads the three rule files
and fails if they are absent: regenerate them first. `replay.sh` compares only
the examples present. All five were rebuilt at placement (Python 3.14.4,
Windows); at this write the export run (6.2 s) and the `mixed_certificate.json`
export (0.6 s) were rerun on a fresh extraction of the archive: the three
rules are byte-identical, `rule_index.json` and the certificate are identical
apart from CR bytes, and the shipped `data/14-three-mass-rule_index.json`
equals the delivered `examples/rule_index.json`.

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

Batch 80 (cluster K2, Parts V and VI) added 165 labels, 417 in all, and
removed or renamed none (the `.aux` files of the previous and the new build
give the same number to every one of the 252 earlier labels, and the 36
earlier bibliography entries keep their numbers): source 14's 47 labels as
`smc:tm:` plus their delivered names, source 15's 51 as `smc:ct:`, source
16's 20 as `smc:su:` and source 17's 40 as `smc:fm:`, including labels added
to unlabelled sections, one lemma, two theorems, two corollaries, two
propositions, one figure, the questions and one equation (source 16's
`smc:su:eq:counts`); and seven new labels, `smc:tm:part`, `smc:su:part` and
the five front subsections `smc:tm:sec:batch80`, `smc:tm:sec:notation`,
`smc:tm:sec:relation`, `smc:tm:sec:status` and `smc:tm:sec:frontquestions`.
The labels of the re-proofs replaced by pointers (source 14's `eq:affine`,
`eq:nearcount`, `eq:tail`; source 15's `eq:affinefar`) are not used. Source
14's Section *n* is Section *n* + 48 here (Sections 49–63), source 15's is
*n* + 63 (64–73), source 16's *n* + 73 (74–82) and source 17's *n* + 82
(83–92); equations are numbered by section (sources 16 and 17 tagged theirs
(1), (2), …). Source 15's four tables are Tables 7–10, and the figures of
sources 14 and 17 are Figures 4 and 5. The three new front tables (sources,
thresholds, letters) are uncaptioned, so no earlier table changed its number;
the appendices keep their letters.

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

Parts V and VI (batch 80) keep their sources' letters too; the table of
Section 1.13 lists those with another meaning in the other new Part or in
Part IV. The ones most likely to be misread:

- **Mass, unit, particle** — in Part V a symbol is a set of Boolean channels
  and its mass is the number of channels, so a canonical configuration has
  three mass units in **two** occupied cells. In an integer-state NCCA a
  "particle" is one unit of numerical mass. Reading Part V as "three
  particles suffice for an NCCA" is false: Part VI shows that with a single
  weight-one symbol three and four units are decidable.
- `R` — Part V: the stationary right-marker type (and, in source 15, a source
  program `R` with wrapped program `R_cl`); Part VI: the radius of `F`.
- `S` — Part V: static shuttle types `S_j`, the channel shift in `F = S∘Π`,
  state-code sums; Part VI: the padded comoving radius `max(1, R + |δ|)`.
- `u` — Part V: a controller velocity and quotient offsets `u_tj`; Part VI:
  *the* weight-one symbol.
- `N` — Part V: the gap integer (`N = 2^a 3^b`, gap `12N`); source 17: the
  threshold `N = 4B + 12S`. `B` — Part V: branch count; source 16: Boolean
  gate count (Part IV's `G`); source 17: the seed-prefix bound.
- **Companion** — source 15's companion is source 14, source 16's is Part IV
  (source 13), source 17's is source 16.
- **Timed / untimed** — source 16's mass-three relation includes time and is
  uniform in all positions; source 17's mass-four description forgets time
  and is for a fixed input.

The TeX macro `\N` of sources 14–17 is `\NN` here; it prints `{0, 1, 2, …}`
as in the sources.

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
- **Part V (sources 14 and 15).** For every separated reversible two-counter
  machine, an effective globally reversible CA on `2^𝒯` (weight =
  cardinality), forward and inverse radius at most four, with mass-three
  canonical configurations (gap `12·2^a·3^b`), exact macro times and a clean
  symbol `Ready(q_f)` that occurs iff the source halts (Theorem 49.1); three
  is the least mass with fixed-rule undecidable pattern occurrence in that
  model (Theorem 49.2, lower half = Theorem 44.1); finite path-closure
  completion of a partial pair injection (Lemma 51.1); the reversible residue
  query in `4n + 1` ticks (Lemma 53.1) and the rational gap primitive
  (Lemma 54.1); exact type and row counts `s = 96qm + 6qd + 2d + 6q + 2314`,
  `P = 3528qm + 6qd + d − 6m + 1152`, `C = 7008qm + 12qd + 2d + 6q − 6m + 2304`;
  exact microtimes; radius one by spatial blocking (same time) or phase
  dilation (four times the time) (Theorems 57.1–57.2); a degree-two natural
  certificate at a fixed source horizon with `2Bh` variables, `3h + 1`
  squares and `Bh` products and a unique witness (Theorem 58.1), with a paid
  bounded counter loader. Source 15: the clean return wrapper preserves the
  separated syntax (Lemma 66.1) and restores the whole raw input after
  `2h + 2` steps (Theorem 66.2); exact-pair reachability is undecidable for
  one fixed reversible rule at mass three, three being sharp (Theorems 64.1,
  67.1, Corollary 67.2); the first-target clock
  `T_cl = 2Θ + 192(N_h + N_0) + 16` (Theorem 68.1); the compact certificate
  keeps `2Bh / 3h + 1 / Bh` against the naive `8(B+1)(h+1) / 6h + 7 /
  4(B+1)(h+1)`, with an affine bijection of natural zero fibres onto the full
  wrapped certificate (Theorem 70.2).
- **Part VI (sources 16 and 17).** With at most one weight-one symbol: the
  no-split lemma (Lemma 75.1); the timed evolution relation at mass at most
  three is effectively Presburger, uniformly in all positions and time
  (Theorem 74.1), so reachability and pattern occurrence are decidable and
  occurrence times eventually periodic (Corollary 74.2); integer-state NCCAs
  cannot encode halting at numerical mass three (Corollary 79.1); horizon-free
  quartics with zero or one natural witness, `K = 2I + 6C + B` witnesses
  (Corollary 80.1). Source 17: exact reachability and pattern occurrence are
  decidable at mass four, anchored and anywhere (Theorem 83.1), hence the
  numerical lower bound five (Corollary 83.2); the additive gap counter, the
  dispatch and the expanding-shuttle normal form with quadratic section times
  (Lemmas 86.1–86.2, Proposition 87.1); a binary radius-six conservative rule
  (Proposition 89.1) with anchored hit times `t_k = k² + (2d − 11)k`, `d ≥ 7`
  (Proposition 89.2: not Presburger); the one-witness quartic
  `[k² + (2x + 3)k − t]²`.

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

**Re-derived results of Parts V and VI (batch 80).** Source 14's Section 59
proves Part IV's Theorem 44.1 again by the same argument (its two-mass test is
source 13's audit minus one line, its receipt byte-identical); it is printed
as a pointer, as are its bounded-diameter proposition (Proposition 43.1), source
15's summary of the same argument and its restated forward-certificate proof
(Theorem 58.1), and source 17's two small-packet lemmas (source 16's Lemmas
75.1–75.2, Proposition 77.1). Source 16 follows Part IV's semilinearity
architecture one mass higher (notes at each place) and uses Part IV's
post-elimination compiler by name. The certificate gate
`(E_t − e_tj)(e_tj + u_tj)` of sources 14 and 15 is the inactive-product gate
of `quadratic-orthant-certificates` Part VI (`qoc:rn:lem:gates`). New, and
credited to their sources: the reversible three-unit compiler and its
cleanup, the clean return wrapper, exact-pair undecidability, the clock and
lift, the no-split lemma, the mass-three core and uniform composition, and all
of source 17's four-mass analysis and binary shuttle.

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
  sets from the mass-two subclass (all still true of Part IV itself;
  Parts V and VI now prove exact-target undecidability and the sufficiency
  of three units for a weighted CA with many weight-one symbols);
- for Part V: an expanded universal source table, a numerical universal
  alphabet or row count (universality is imported from Morita and Imai's
  Proposition 3.4, and Lemma 3.5 for source 15); anchored halt observation,
  intrinsic universality or an efficiency bound; a three-numerical-particle
  theorem for integer-state NCCA; real or rational exactness of the
  certificates; a fixed-arity polynomial for an unknown horizon, or a
  finite-fold or single-fold representation; an exponentiation gadget (the
  loader is a bounded table); lower bounds from the slot counts; novelty of
  the radius reductions, optimal overhead, a smallest alphabet, priority or
  literature-wide novelty (Brandt–Portmann–Uitto, Dobrev et al. and the
  abstract of *Busy agents on a line* are credited); global halting or
  freezing; for source 15 also one target independent of the input, a
  stationary or once-reached target, microscopic reversal of the paths, a
  bound on the fresh-entry normalization, a map of the whole orthant or an
  identity off the zero sets for the lift, and novelty of forward-and-reverse
  computation (Bennett);
- for Part VI: one formula with the rule as a parameter; intrinsic
  universality, signed masses, infinite alphabets, nonuniform or
  time-dependent rules, active zero-weight backgrounds or several unit
  labels; a universal bound on the formula-dependent arity, efficient
  preprocessing, a general rule-to-formula, quantifier-elimination or
  rule-to-section implementation; real or rational fibre exactness; a
  finite-fold conclusion for c.e. sets; a five-particle upper bound for
  binary automata; reversibility of the binary shuttle (it is not
  injective); uniform timed Presburger definability at mass four; novelty
  with respect to Kong's 2021 thesis and Imai's 2021 KAKEN report, priority,
  or the present status of the four-particle question;
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
five questions are printed in their Parts (Part III states none), and so
are the six questions each of sources 14 and 15, source 16's two directions
and source 17's seven questions; Table 3 pairs Parts I and II. Batch 79 answers two of them, in dated `[write]` notes:

- Part I's direction 15.2 (`smc:cg:q:universal`, an audited universal
  signal-machine frontend) is answered by Part III **except for the
  ordinary-integer loader**, and with Morita's UTM(15,6) through Durand-Lose's
  2012 stacks instead of the 13-type construction named there.
- Part II's question `smc:sd:q:conservative` (exploit conservative bounded
  populations) is answered in part, at a fixed horizon, by Parts III and IV;
  neither encodes unbounded histories in fixed arity.
- Part II's `smc:sd:q:universal` (transcribe the 13-label table) stays open.

Batch 80 (Parts V and VI) answers, in dated `[write]` notes (Section 1.16):

- the remark after Part IV's Theorem 44.1 ("It does not show that three
  suffices, or identify a least universal mass"): **answered model by
  model** — three suffices with many weight-one symbols (Theorems 49.2,
  64.1); with at most one, three and four do not (Theorems 74.1, 83.1), so
  the least universal numerical mass is at least five, and exactly five if
  the Alhazov–Imai construction holds as its abstract states (full paper not
  checked, not asserted reversible);
- Part IV's fourth question (small-particle model comparisons): **answered
  in substance** (the number of weight-one symbols decides); open: the full
  Alhazov–Imai construction, a reversible numerical threshold, a binary
  upper bound, the least number of weight-one symbols for universality at
  mass three;
- Part IV's fifth question (exact targets versus halt signals): **answered
  for the three-mass weighted CA** by source 15; not for Part IV's own
  pulse interface;
- source 14's third question (exact finite targets) by source 15; sources 14
  and 15's fourth questions (integer-state convention) in part by Part VI;
  source 16's four-versus-five boundary by source 17.

Part IV's first question (print a safe universal source) stays open, and so
do the other questions of Parts V and VI. Part IV's non-claims "exact-target
undecidability, … a minimum universal mass, or that three particles suffice"
remain true of Part IV.

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
  input `X ≠ 0`. At `X = 0`, strict branches have zero selectors and
  disjointness allows at most one branch with only homogeneous weak or
  equality guards, so the complete packet's real fibre is natural there
  too. Adding the selector term forces one-hot selection by the gates
  alone, independently of this branch condition, without changing the
  witness and residual ledger. That report's relation section and
  a note after its Theorem `qoc:um:thm:poly` point back here.
- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**:
  its trace theorem `pqc:pm:thm:trace` is the same kind of fixed-horizon
  statement as Part III's horizon sums, for different dynamics: exactly one
  natural zero there, for a total clipped network, against an
  empty-or-singleton natural fibre here, for a partial event map. **[`group-theoretic-substrates`](../group-theoretic-substrates)**:
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
- **Parts V and VI (batch 80) and the neighbouring reports.**
  `quadratic-orthant-certificates` Part VI: the certificate gate of sources
  14 and 15 is its inactive-product gate (`qoc:rn:lem:gates`); source 14's
  natural-domain counterexample (`e = 1, u = 1/2`) is consistent with that
  report's real-orthant one-hot lemma (one-hot selection survives over the
  reals, divisibility does not). `canonical-diophantine-certificates`
  Part XI: `cdc:of:thm:singlefoldsl` gives source 16's semilinear relation a
  degree-two orthant-nonnegative single-fold representation (as for Part
  IV's), and `cdc:of:thm:classification` (`D⁺₂ = D⁺₃ = SL`) shows that
  source 17's non-semilinear hit set has no orthant-nonnegative
  representation of degree at most three, so its degree-four one-witness
  quartic is degree-minimal in that class. Notes in the article say so; the
  reciprocal notes in those two reports are not part of this write. The
  formal project has formalized none of Parts V–VI; Cooper's quantifier
  elimination, which source 16 imports, is `Logic/PresburgerArithmetic/Lean`
  (above). The research tree's notes that Part IV's review "does not prove
  three particles suffice" (`review_sparse_lattice_aebfa386e.md`) and that
  Morita's NCCA needs a background (`Papers/1980/REVERSIBLE_FINITE_HISTORY_MODELS.md`)
  are scope statements that Parts V–VI now bear on; they are the research
  tree's to update.

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
- Sources 14 and 15 (batch 80): `review_batch80_three_mass.md` (commit
  `933600302`). "PASS within the stated model and interfaces", no repair
  patch. Both complete author replays (source 14's `replay.sh`, source 15's
  `replay.py`) and both manifest verifiers passed; independent checks of 360
  literal core cases, 2,400 natural assignments, 45 compact/full natural
  zero-fibre bijections and 7,968 cleanup ticks. It checked Morita and
  Imai's Proposition 3.4 and Lemma 3.5 in the primary paper (pp. 245–246),
  and records the compact certificate's off-zero values (3 and 18, a bridge
  coordinate −1) and the rational false zero `e = 1, u = 1/2` as documented
  limitations, not defects.
- Sources 16 and 17 and manuscript 06 (batch 80): `review_batch80_low_mass.md`
  (commit `7f1161730`). "PASS within the stated mathematical and executable
  scopes", no correction. Manuscript 05 changes only the attribution of
  manuscript 06 (the TeX body from "Model and main result" to the quartic
  section is byte-identical); all nine author invocations reproduce their
  receipts; 8,192 local windows and potential edges of the binary rule
  reconstructed; Kong's thesis checked (binary Definition 1, Theorem 2, the
  four-particle case open in 2021); the KAKEN report's Japanese text not
  certified and the full Alhazov–Imai paper not obtained; the five-witness
  congruence atom applies to source 16's quartic (`K = 2I + 5C + B`), a
  formula-dependent saving with no total-gate claim.
- Batch-80 index and placement: `incoming_substrate_review_4e270aa46.md`
  (commit `e903a3f35`, updated in `3aa123856`) and
  `review_batch80_mass_placement_345a9e44e.md` (commit `3aa123856`), which
  authenticates the 116 placed files (116 placed, 13 aliases, 33
  archive-only members of the 162) and notes that the flattened names are
  not a runnable layout. Neither reviews this write.
- Batch-79 reciprocal notes: `review_batch79_j2_bbc67d225.md` (commit
  `37a829e0b`) reviews the batch-79 J2 notes of this report and others. Its
  finding 4 asks that the zero-input remark of the note after
  `smc:cs:thm:packet` (and the README sentence in "Relation to neighbouring
  reports") be qualified: under the packet's disjoint homogeneous branch
  hypothesis the complete packet's real fibre is natural also at `X = 0`;
  only the weak gates alone admit the fractional exception. Its
  seven-file prose patch `review_batch79_j2_bbc67d225.patch` was not
  applied at the batch-80K2 write; it **was applied** on 2 October 2026,
  after that write, to this article and README and to the other reports it
  touches (the two hunks here verbatim; the note after `smc:cs:thm:packet`
  now says that it was corrected in place, crediting the review). The same
  change extended the qualification to the item "The degree-two orthant
  format" of Section 1.9 (`smc:cs:sec:relation`) and replaced "one
  natural zero" by "empty or a singleton" where this report compares its horizon sums with
  `pqc:pm:thm:trace` (the review's finding 3, which the patch applied to
  the other report only).
- Batch-80 corrected-code publication: `review_batch80_correction_publication_86267b8a3.md`
  (commit `fbad71e8c`) audits the batch-80K1 corrected-code updates of
  this report, `quadratic-orthant-certificates` and
  `canonical-diophantine-certificates` (through `86267b8a3`) and passes
  their mathematics. It finds one reproducibility defect: the placement
  stager and its inventory do not exist at `a7ae02511`, so they must be run
  from a recent checkout with the historical checkout passed as `--repo`.
  Its README-only patch `batch80_historical_stager_launch.patch` was
  applied on 2 October 2026 to way (b) under "Rerunning the programs" and
  to the paragraph after it.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
mathtools, microtype, booktabs, longtable, ragged2e, xcolor, TikZ, enumitem,
fancyhdr, listings, xurl, hyperref, graphicx, pict2e). The committed build has 193 pages: no
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

The batch-80 write of cluster K2 (Parts V and VI: two new Parts, five front
subsections, dated notes, one provenance paragraph, twelve bibliography
entries appended last, `graphicx` and `pict2e` added to the preamble and
thirteen macros for the new Parts) takes the report to 193 pages (unnumbered
title page, then pages 1–192). The log has no errors, warnings, undefined
references or citations, multiply defined labels, duplicate destinations or
overfull boxes, and the same four underfull bibliography lines as before.
The `.aux` of a build of the previous text (`86267b8a3`, 120 pages) has the
same 252 labels with the same numbers and the same 36 bibliography numbers;
the new entries are 37–48. The title page (whose vertical spacing was
tightened by a few points so that the longer abstract still fits on one
page), the threshold table (page 24), the opening of Part V and Part IV's last dated notes (pages 116–117), the
pointer section 59 (page 131), Figure 4 (page 123), Figure 5 (page 171) and
the provenance table of Parts V–VI (page 182) were rendered and inspected.
Source 17's figure is its delivered vector PDF (embedded TrueType fonts, no
Type 3 fonts), included unchanged from `figures/`; a scratch build needs
that directory beside `article.tex`.

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
# (b) original editions: run the later helper from this recent checkout,
#     with its sibling placement_a7ae02511_inventory.json present.
#     The historical checkout and destination below must not exist yet.
git worktree add ../source-a7ae02511 a7ae02511
py Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py \
   --repo ../source-a7ae02511 --destination ../placed-a7ae02511
```

Way (a) is the tested one. Way (b) was tried at this write on this Windows
checkout (7 s): it restored `conservative-signal-release/` and
`sparse-lattice-release/` byte-identical to the archives, including the
excluded files, which it takes from Git, but then stopped with "Restored
complete package manifest differs" while checking the six package roots it
restores (the other four belong to `quadratic-orthant-certificates` and
`canonical-diophantine-certificates`). The stager is the research tree's
program, not part of this report. Since batch 80, use an unchanged
historical checkout as its `--repo` argument to restore the original edition.
Invoke the helper from a recent checkout with its required sibling inventory:
neither helper nor inventory exists at `a7ae02511`. Passing a current
corrected checkout as `--repo` stops earlier, with "Placed source differs"
at replaced files. For the corrected layout use way (a).

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

Sources 14–17 (batch 80) — the shipped files are flattened and renamed, and
their programs import one another by delivered names (source 15's import
`vendor/`), so restore the delivered layout from the arrival archives, never
in the report directory:

```sh
mkdir r14 r15 r16 r17
git show 4e270aa46:docs/incoming/Three_Mass_Reversible_Computation.zip > r14/tm.zip
git show 4e270aa46:docs/incoming/Exact_Targets_Three_Mass_Units.zip > r15/ct.zip
git show "4e270aa46:docs/incoming/Single_Unit_Three_Mass_Decidability (1).zip" > r16/su.zip
git show 4e270aa46:docs/incoming/Four_Mass_Decidability_Package.zip > r17/fm.zip
(cd r14 && unzip -q tm.zip)   # r14/three-mass-release/
(cd r15 && unzip -q ct.zip)   # r15/clean-target-release/
(cd r16 && unzip -q su.zip)   # r16/single-unit-three-mass/
(cd r17 && unzip -q fm.zip)   # r17/four-mass-bound/
```

- **Source 14** (`three-mass-release/`): `sh replay.sh` (it needs
  `python3`, or `PYTHON=py sh replay.sh`) writes everything under `.replay/`
  and leaves the release files unchanged; it takes several minutes (the
  placement run of its Python steps took about 440 s here, the radius-one
  audits 115 s and 130 s). Never run it with `-O`. The archive contains the
  five literal exports that this report does not ship; a layout assembled
  from the shipped files lacks them, and `test_literal_exports.py` then fails
  (regenerate them first, see "Reconstructing the excluded data"). At
  placement every Python step passed on a copy and the 14 fresh receipts
  equalled the shipped ones on every stable field.
- **Source 15** (`clean-target-release/`): `py replay.py --receipt <file outside the package>`.
  On Windows two hazards: `replay.py` first runs `verify_manifest.py` when
  `SHA256SUMS` exists, and that checker compares native relative paths with
  `/`-separated names, so it rejects every nested member — move
  `SHA256SUMS` out of the copy first; and the replay's byte-exact round trip
  of `examples/chain_*.json` fails because Windows writes CRLF, although the
  content is identical (compare after removing CR bytes). At placement all
  eleven commands passed on a copy in this way (163 s); the research tree's
  review ran it unmodified on POSIX.
- **Source 16** (`single-unit-three-mass/`): `sh run-tests.sh` (or
  `PYTHON=py sh run-tests.sh`) copies the two programs to `.replay/` and
  compares both receipts; about 15 s each. It passed at placement.
- **Source 17** (`four-mass-bound/`): `sh run-tests.sh` runs seven
  commands with `python3` and regenerates the receipts **in place**, so use a
  copy. On Windows, `test_binary_expanding_shuttle.py` rewrites the sealed
  `binary-radius6-conservation-certificate.json` with a CR byte (16,896
  instead of 16,895 bytes), after which `test_exact_boundaries.py` fails its
  hash group (12 of 13 pass): restore the certificate from the archive
  between the two, or run on POSIX. With that restore all seven passed at
  placement (about 30 s) and six receipts were JSON-equal; the figure
  renderer needs matplotlib and was not run.

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
- Sources 14–17 (batch 80): delivered names in shipped texts.
  `14-three-mass-SOURCE_PROVENANCE.md` names `receipts/` and `SHA256SUMS`;
  `data/14-three-mass-replay-summary.json`, `literal-export.json` and
  `rule_index.json` name the five excluded exports (with their SHA-256 and
  sizes); `code/14-three-mass-build.sh` builds the unshipped `tex/report.tex`
  and `replay.sh` runs `code/*.py` by delivered path.
  `15-clean-targets-SOURCE_PROVENANCE.md`,
  `data/15-clean-targets-source-provenance.json` and
  `upstream-extension-manifest.json` name source 14's
  `three-mass-report.tex`, `SHA256SUMS`, `vendor/`, `examples/`, `receipts/`
  and `README.md` (none shipped under those names; the vendored programs are
  `code/14-three-mass-*`); source 15's audits import `vendor/`, and
  `replay.py` calls the unshipped `verify_manifest.py`.
  `16-single-unit-AUDIT.md` names `independent/`, `16-single-unit-REVISION.md`
  the delivered README. `data/17-four-mass-portable-replay-results.json`
  names `SHA256SUMS` and `independent/`, and records a replay of the
  delivered ZIP. The `[write]` notes at the end of Sections 61, 72, 82 and 92
  give the shipped names.
- Source 17's figure data table `data/17-four-mass-binary-four-particle-shuttle.csv`
  has CRLF line ends as delivered (46 lines); the line
  `docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/17-four-mass-binary-four-particle-shuttle.csv -text`
  in `SetTheory/Cardinals/.gitattributes` keeps it byte for byte. Its figure
  is staged as a PDF (`figures/`), an announced exception to "PDFs are not
  staged", because Part VI prints it.
- Source 17's hypothesis `d ≥ 7` for the binary shuttle is safe but not
  sharp: the hit-time formula also holds for `d = 6` (checked by direct
  simulation at placement and again at this write, through `t ≤ 2500`) and
  fails for `d = 5`; a `[write]` note after Proposition 89.2 says so. Source
  17's sentence that its lower bound "matches" the Alhazov–Imai upper bound
  carries a `[write]` qualification (only the abstract was checked; its
  README says "compatible with").
- Source 14 calls its mass-two proof "self-contained" and cites neither
  source 13 nor the 2021 Kong and Imai precursors; source 16 cites source
  13 only for its compiler; source 17 never cites Part IV. `[write]` notes
  supply the credit (Part V and VI openings, Sections 49, 62, 74, 84).
- Manuscript 06, the superseded original of source 16, is not shipped; its
  text survives in the arrival commit `4e270aa46`.
