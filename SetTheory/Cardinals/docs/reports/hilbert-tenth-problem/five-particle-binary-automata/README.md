# Five-Particle Binary Automata

**Reversible universality, a literal universal source, startup and cellular clocks, and exact lazy evaluation**

This is a research report dated 3 October 2026, built from six
manuscripts: "Research Reports" 14–19 of one AI-assisted research
pipeline, delivered as batch 82 (cluster M1) of ProveIt's incoming reports.
They concern one object, the binary, number-conserving, globally reversible
cellular automaton that Report 15's compiler builds, fed with the explicit
universal source of Report 16; Report 14 is a sibling construction for
binary conservative (not necessarily reversible) automata.

| Report | batch-82 archive | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 15 (base) | 15 | `Reversible_Binary_Five_Particle_Package.zip` (`report15.tex` + 3 `\input` files, 21-page PDF) | none (no repository commit named) | `bca6383e9` | Part I, Sections 4–17 |
| 14 | 23 | `five-particle-binary-portable.zip` (`report/five-particle-binary-compiler.tex`, 24 pp.) | none | `bca6383e9` | Part I, Sections 18–32 |
| 16 | 13 | `Literal_Universal_Reversible_Source_Package.zip` (`report16.tex` + 10 section files, 26 pp.) | none | `bca6383e9` | Part II, Sections 33–41 |
| 17 | 16 | `Reversible_Startup_Optimization_Package.zip` (`report17.tex`, 14 pp.) | none | `bca6383e9` | Part III, Sections 42–52 |
| 18 | 04 | `Cellular_Clock_Domination_Package.zip` (`report18.tex`, 13 pp.) | none | `bca6383e9` | Part III, Sections 53–64 |
| 19 | 09 | `Exact_Lazy_Reversible_CA_Evaluator_Package.zip` (`report19.tex`, 14 pp.) | none | `bca6383e9` | Part IV, Sections 65–76 |

All six archives arrived unchanged in `db37d18c8` and survive there
(`git show db37d18c8:docs/incoming/<archive> > <archive>`). No manuscript
names a ProveIt commit; they pin one another by SHA-256 (Report 16 pins
Report 15's compiler `f95a6028c9d3…`, Report 17 pins Report 16's source
`38c586706fa1…`, Reports 18 and 19 pin Report 17's source `fa61d06178d7…`,
Reports 14–16 pin Report 12's LaTeX `803bf0c4194b…`). Report 14 is
unnumbered in its own header; Report 16's compiler proof identifies it.

**Status.** AI-assisted research manuscripts (Report 14's delivery README:
"prepared with AI assistance"); unrefereed; not formalized; **not yet
reviewed by the Hilbert's-tenth research programme** (see "Relation to the
formal project"). Every result, proof, example, question and limitation of
the six manuscripts is printed; re-proofs of results already in the
collection are kept as marked second presentations.

Four further Reports of the same pipeline, Reports 20, 26, 27 and 28
(batch 82, cluster M2), concern the same automaton. Their files were placed
in this directory by `7d2b1b245` and are listed below; their text is to be
printed as Parts V–VI, after Part IV (the insertion point is marked in
`article.tex`).

## Files

```
README.md                                       this guide
article.tex                                     the report: standalone LaTeX, internal bibliography
article.pdf                                     the compiled report, 121 pages
figures/accepting-orbit.pdf                     Report 15's Figure (raw five-particle trace of its accepting example)
figures/14-five-binary-five-particle-trace.pdf  Report 14's figure (its accepting example's CA trace)
```

**Report 14 (archive 23), prefix `14-five-binary-`** — 32 files (5 at the root, 13 in `code/`, 14 in `data/`). Root: its compiler README, audit, source provenance and proof notes and release provenance. `code/`: the compiler (`compiler-five_binary.py`), front-end emitter (`compiler-frontend.py`), their checkers and five independent audits, the figure generator (matplotlib), report-fixture checker, `replay.py` and `build.sh`. `data/`: audit and check receipts, the example front end and witness, the verified 473-state trace, the primary-source review, and replay and PDF-quality receipts.

```
14-five-binary-compiler-AUDIT.md
14-five-binary-compiler-README.md
14-five-binary-compiler-SOURCE_PROVENANCE.md
14-five-binary-compiler-proof.md
14-five-binary-provenance-RELEASE_PROVENANCE.md
code/14-five-binary-build.sh
code/14-five-binary-compiler-audit_api_independent.py
code/14-five-binary-compiler-audit_frontend_independent.py
code/14-five-binary-compiler-audit_independent.py
code/14-five-binary-compiler-audit_literal_boundaries.py
code/14-five-binary-compiler-audit_regression_modes.py
code/14-five-binary-compiler-check_five_binary.py
code/14-five-binary-compiler-check_frontend.py
code/14-five-binary-compiler-five_binary.py
code/14-five-binary-compiler-frontend.py
code/14-five-binary-figures-generate_figure.py
code/14-five-binary-replay.py
code/14-five-binary-verification-check_report_fixtures.py
data/14-five-binary-compiler-audit_api_normal.json
data/14-five-binary-compiler-audit_api_optimized.json
data/14-five-binary-compiler-audit_frontend_independent.json
data/14-five-binary-compiler-audit_independent.json
data/14-five-binary-compiler-audit_literal_boundaries.json
data/14-five-binary-compiler-audit_regression_modes.json
data/14-five-binary-compiler-checks.json
data/14-five-binary-compiler-example_frontend.json
data/14-five-binary-compiler-example_witness.json
data/14-five-binary-compiler-frontend_checks.json
data/14-five-binary-figures-verified_trace.json
data/14-five-binary-provenance-primary-source-review.json
data/14-five-binary-verification-fresh_payload_replay_receipt.json
data/14-five-binary-verification-pdf_quality_receipt.json
```

**Report 15 (archive 15, the base), prefix `15-rev-five-`** — 31 files (2 at the root, 17 in `code/`, 12 in `data/`). Root: the audits README and the compiler's source schema. `code/`: the reversible compiler (`compiler-reversible_binary.py`, SHA-256 `f95a6028c9d3…`, the compiler of Reports 16–19), its tests and stress, exhaustive and fixture checks, the clean-target sample, the certificate emitter and tests, two audits, the trace renderer, `replay.py` and `build.sh`. `data/`: the ordinary and clean-target certificates, real certificates and witnesses, sample sources, the 1,394-frame sample orbit and receipts.

```
15-rev-five-audits-README.md
15-rev-five-compiler-SOURCE_SCHEMA.md
code/15-rev-five-audits-audit_api.py
code/15-rev-five-audits-audit_certificate.py
code/15-rev-five-build.sh
code/15-rev-five-certificates-certificate.py
code/15-rev-five-certificates-test_certificate.py
code/15-rev-five-compiler-additional_tests.py
code/15-rev-five-compiler-checks-compiler_stress.py
code/15-rev-five-compiler-checks-exhaustive_audit.py
code/15-rev-five-compiler-checks-verify_clean_fixture.py
code/15-rev-five-compiler-checks-verify_original_fixture.py
code/15-rev-five-compiler-clean_target_sample.py
code/15-rev-five-compiler-full_cycle_test.py
code/15-rev-five-compiler-reversible_binary.py
code/15-rev-five-compiler-sample_orbit.py
code/15-rev-five-compiler-test_compiler.py
code/15-rev-five-replay.py
code/15-rev-five-tools-render_trace.py
data/15-rev-five-certificates-clean-target-certificate.json
data/15-rev-five-certificates-clean-target-real-certificate.json
data/15-rev-five-certificates-clean-target-real-witness.json
data/15-rev-five-certificates-clean-target-sample-source.json
data/15-rev-five-certificates-sample-certificate.json
data/15-rev-five-certificates-sample-real-certificate.json
data/15-rev-five-certificates-sample-real-witness.json
data/15-rev-five-certificates-sample-source.json
data/15-rev-five-compiler-clean-target-sample-receipt.json
data/15-rev-five-compiler-sample-boundary-demonstration.json
data/15-rev-five-compiler-sample-orbit.json
data/15-rev-five-compiler-sample-receipt.json
```

**Report 16 (archive 13), prefix `16-literal-source-`** — 65 files (12 at the root, 21 in `code/`, 32 in `data/`). Root: the sub-package README, proof, packaging adaptations, primitive-certificate proof and README, compiler proof and source schema (copies of Report 15's), and five audit notes. `code/`: `build_source.py` (rebuilds the literal tables), loader, validators, independent audit, primitive-certificate tools, release audit, replay, manifest tools and `build.sh`. `data/`: build statistics, the three-counter stages `primitive3.json` and `normalized3.json`, the target ledger, provenance, stabilized hashes, ledgers, certificates of the small example and receipts.

```
16-literal-source-PACKAGING-ADAPTATIONS.md
16-literal-source-PROOF.md
16-literal-source-README.md
16-literal-source-audits-primitive-AUDIT.md
16-literal-source-audits-primitive-INDEPENDENT-PROOF.md
16-literal-source-audits-release-level-audit.md
16-literal-source-compiler-reference-COMPILER_PROOF.md
16-literal-source-compiler-reference-SOURCE_SCHEMA.md
16-literal-source-independent-macro-audit.md
16-literal-source-periodicity-audit.md
16-literal-source-primitive-certificates-PROOF.md
16-literal-source-primitive-certificates-README.md
code/16-literal-source-audits-primitive-audit_certificate.py
code/16-literal-source-audits-release_audit.py
code/16-literal-source-build.sh
code/16-literal-source-build_source.py
code/16-literal-source-check_primary_table.py
code/16-literal-source-class_expansion_ledger.py
code/16-literal-source-independent_audit.py
code/16-literal-source-loader.py
code/16-literal-source-primitive-certificates-audit_source.py
code/16-literal-source-primitive-certificates-certificate.py
code/16-literal-source-primitive-certificates-replay_primitive_ca.py
code/16-literal-source-primitive-certificates-test_certificate.py
code/16-literal-source-replay.py
code/16-literal-source-run_checks.py
code/16-literal-source-test_concrete.py
code/16-literal-source-test_loader.py
code/16-literal-source-tools-make_manifest.py
code/16-literal-source-tools-make_release.py
code/16-literal-source-validate_source.py
code/16-literal-source-verify_affine.py
code/16-literal-source-verify_virtual3.py
data/16-literal-source-PROVENANCE.json
data/16-literal-source-affine-receipt.json
data/16-literal-source-all-checks-receipt.json
data/16-literal-source-audits-primitive-audit-normal-receipt.json
data/16-literal-source-audits-primitive-audit-optimized-receipt.json
data/16-literal-source-audits-primitive-literal-ledger-H0.json
data/16-literal-source-audits-primitive-literal-ledger-H1.json
data/16-literal-source-audits-primitive-literal-ledger-H2.json
data/16-literal-source-audits-primitive-source-audit.json
data/16-literal-source-audits-release-audit-optimized-receipt.json
data/16-literal-source-audits-release-audit-receipt.json
data/16-literal-source-audits-stabilized-hashes.json
data/16-literal-source-build-stats.json
data/16-literal-source-class-expansion-ledger.json
data/16-literal-source-concrete-receipt.json
data/16-literal-source-independent-audit-receipt.json
data/16-literal-source-loader-api-receipt.json
data/16-literal-source-loader-empty-tape.json
data/16-literal-source-normalized3.json
data/16-literal-source-primary-table-receipt.json
data/16-literal-source-primitive-certificates-example-materialized.json
data/16-literal-source-primitive-certificates-example-source.json
data/16-literal-source-primitive-certificates-example-witness.json
data/16-literal-source-primitive-certificates-primitive-example-ca-receipt.json
data/16-literal-source-primitive-certificates-primitive-example-orbit.json
data/16-literal-source-primitive-certificates-source-ledger-receipt.json
data/16-literal-source-primitive-certificates-test-receipt.json
data/16-literal-source-primitive-certificates-universal-h1-ledger.json
data/16-literal-source-primitive3.json
data/16-literal-source-prologue-predicted-clocks.json
data/16-literal-source-schema-injection-receipt.json
data/16-literal-source-target-ledger.json
```

**Report 17 (archive 16), prefix `17-startup-`** — 55 files (9 at the root, 23 in `code/`, 23 in `data/`). Root: README, proof, optimization and portability notes, three audits, the first-encounter optimality proof and its audit. `code/`: `build_source.py`, loader, validators and verifiers (pins, rebuild, initialization, exact delta, orientation pins, release), `run_checks.py`, `offline_stage.py`, manifest writer and `build.sh`. `data/`: provenance, rebuild and replay receipts, the literal and five-counter startup traces, ledgers and QA records.

```
17-startup-OPTIMIZATION.md
17-startup-PORTABILITY.md
17-startup-PROOF.md
17-startup-README.md
17-startup-independent-macro-audit.md
17-startup-independent-relabel-audit.md
17-startup-orientation-addendum-FIRST_ENCOUNTER_OPTIMALITY.md
17-startup-orientation-addendum-first-encounter-independent-audit.md
17-startup-periodicity-audit.md
code/17-startup-baseline_support.py
code/17-startup-build.sh
code/17-startup-build_source.py
code/17-startup-check_primary_table.py
code/17-startup-class_expansion_ledger.py
code/17-startup-independent_audit.py
code/17-startup-independent_relabel_check.py
code/17-startup-loader.py
code/17-startup-offline_stage.py
code/17-startup-run_checks.py
code/17-startup-test_concrete.py
code/17-startup-test_loader.py
code/17-startup-validate_source.py
code/17-startup-verify_affine.py
code/17-startup-verify_exact_delta.py
code/17-startup-verify_initialization.py
code/17-startup-verify_manifest.py
code/17-startup-verify_orientation_pins.py
code/17-startup-verify_pins.py
code/17-startup-verify_rebuild.py
code/17-startup-verify_release.py
code/17-startup-verify_virtual3.py
code/17-startup-write_manifest.py
data/17-startup-PROVENANCE.json
data/17-startup-baseline-expected-outputs.json
data/17-startup-baseline-rebuild-receipt.json
data/17-startup-byte-exact-rebuild-receipt.json
data/17-startup-class-expansion-ledger.json
data/17-startup-empty-first-tm-five-trace.json
data/17-startup-empty-first-tm-literal-trace.json
data/17-startup-empty-prologue-five-trace.json
data/17-startup-empty-prologue-literal-trace.json
data/17-startup-empty-through-first-tm-literal-trace.json
data/17-startup-exact-delta-receipt.json
data/17-startup-historical-portability-adaptations.json
data/17-startup-historical-predecessor-preservation-receipt.json
data/17-startup-independent-audit-receipt.json
data/17-startup-independent-relabel-receipt.json
data/17-startup-initialization-receipt.json
data/17-startup-orientation-addendum-first-encounter-manifest.json
data/17-startup-orientation-addendum-pin-verification-receipt.json
data/17-startup-primary-table-receipt.json
data/17-startup-prologue-predicted-clocks.json
data/17-startup-replay-receipt.json
data/17-startup-report17-qa.json
data/17-startup-schema-injection-receipt.json
```

**Report 18 (archive 04), prefix `18-cell-clock-`** — 31 files (5 at the root, 10 in `code/`, 16 in `data/`). Root: README, portability note, the cellular-clock proof (`CA_CLOCK_DOMINATION.md`) with its README and audit. `code/`: the six `cellular-clock` checkers, `run_checks.py` (adapted), `verify_pins.py`, manifest writer and `build.sh`. `data/`: clock, corollary and old/new startup receipts and traces, historical source manifests (inputs of `verify_manifests.py`), provenance and QA.

```
18-cell-clock-PORTABILITY.md
18-cell-clock-README.md
18-cell-clock-cellular-clock-CA_CLOCK_DOMINATION.md
18-cell-clock-cellular-clock-README.md
18-cell-clock-cellular-clock-audit-AUDIT.md
code/18-cell-clock-build.sh
code/18-cell-clock-cellular-clock-audit-check_ca_clock.py
code/18-cell-clock-cellular-clock-audit-check_old_new_startup.py
code/18-cell-clock-cellular-clock-audit-check_proof_corollaries.py
code/18-cell-clock-cellular-clock-clock_verify.py
code/18-cell-clock-cellular-clock-compare_empty_startup.py
code/18-cell-clock-cellular-clock-verify_manifests.py
code/18-cell-clock-run_checks.py
code/18-cell-clock-verify_pins.py
code/18-cell-clock-write_manifest.py
data/18-cell-clock-PROVENANCE.json
data/18-cell-clock-cellular-clock-audit-corollaries-receipt.json
data/18-cell-clock-cellular-clock-audit-old-new-five-row-traces.json
data/18-cell-clock-cellular-clock-audit-old-new-startup-receipt.json
data/18-cell-clock-cellular-clock-audit-receipt.json
data/18-cell-clock-cellular-clock-clock-receipt.json
data/18-cell-clock-cellular-clock-old-new-empty-startup-receipt.json
data/18-cell-clock-cellular-clock-portable-input-manifest-receipt.json
data/18-cell-clock-historical-report18-adaptations.json
data/18-cell-clock-historical-source-manifest-inspection.json
data/18-cell-clock-historical-source-manifests-baseline-source-manifest.json
data/18-cell-clock-historical-source-manifests-cellular-clock-audit-manifest.json
data/18-cell-clock-historical-source-manifests-cellular-clock-manifest.json
data/18-cell-clock-historical-source-manifests-optimized-source-manifest.json
data/18-cell-clock-replay-receipt.json
data/18-cell-clock-report18-qa.json
```

**Report 19 (archive 09), prefix `19-lazy-eval-`** — 32 files (5 at the root, 12 in `code/`, 15 in `data/`). Root: proof, results, audit design and addendum, the portable-replay README. `code/`: the lazy evaluator (`lazy_reversible.py`, SHA-256 `42e8aa65c05f…`), tests, audit and addendum checks, startup-geometry check, benchmark, release checks and verifier, `replay.py`, manifest writer and `build.sh`. `data/`: normal and optimized receipts, the universal startup and malformed-cascade traces, the universal count, replay and integrity receipts, provenance and QA.

```
19-lazy-eval-PROOF.md
19-lazy-eval-RESULTS.md
19-lazy-eval-audit-addendum.md
19-lazy-eval-audit-design.md
19-lazy-eval-portable-replay-README.md
code/19-lazy-eval-addendum_checks.py
code/19-lazy-eval-audit_checks.py
code/19-lazy-eval-benchmark_universal.py
code/19-lazy-eval-build.sh
code/19-lazy-eval-check_startup_geometry.py
code/19-lazy-eval-lazy_reversible.py
code/19-lazy-eval-package_checks.py
code/19-lazy-eval-release_checks.py
code/19-lazy-eval-replay.py
code/19-lazy-eval-test_lazy.py
code/19-lazy-eval-verify_release.py
code/19-lazy-eval-write_manifest.py
data/19-lazy-eval-PROVENANCE.json
data/19-lazy-eval-evidence-addendum-receipt-optimized.json
data/19-lazy-eval-evidence-addendum-receipt.json
data/19-lazy-eval-evidence-audit-receipt-optimized.json
data/19-lazy-eval-evidence-audit-receipt.json
data/19-lazy-eval-evidence-audit-universal-count.json
data/19-lazy-eval-evidence-test-optimized-receipt.json
data/19-lazy-eval-evidence-test-receipt.json
data/19-lazy-eval-evidence-universal-malformed-trace.json
data/19-lazy-eval-evidence-universal-optimized-receipt.json
data/19-lazy-eval-evidence-universal-receipt.json
data/19-lazy-eval-evidence-universal-startup-trace.json
data/19-lazy-eval-portable-replay-replay-receipt.json
data/19-lazy-eval-release-integrity-receipt.json
data/19-lazy-eval-report19-qa.json
```

**Placed by `7d2b1b245`, to be printed as Parts V–VI** (batch 82, cluster M2: Reports 20, 26, 27 and 28, which certify, replace and evaluate this report's automaton; their text is not yet in `article.tex`, and their README section will be written with those Parts). The Hilbert's-tenth review `review_parallel_particle_reports.md` (`fb7e3cb47`) covers Reports 26–28.

*Report 20, prefix `20-event-budget-`* — 40 files (4 at the root, 11 in `code/`, 25 in `data/`):

```
20-event-budget-PROOF.md
20-event-budget-README.md
20-event-budget-audit-INDEPENDENT_AUDIT.md
20-event-budget-report20-math-review.md
code/20-event-budget-artifact_checks.py
code/20-event-budget-audit-independent_audit.py
code/20-event-budget-build.sh
code/20-event-budget-check_example.py
code/20-event-budget-example_emitter.py
code/20-event-budget-independent_expansion.py
code/20-event-budget-scheduler_reference.py
code/20-event-budget-test_guards.py
code/20-event-budget-test_interface.py
code/20-event-budget-test_schema.py
code/20-event-budget-universal_slots.py
data/20-event-budget-PROVENANCE.json
data/20-event-budget-audit-independent-receipt.json
data/20-event-budget-audit-reviewed-hashes.txt
data/20-event-budget-binding-receipt.json
data/20-event-budget-example-polynomial.json
data/20-event-budget-example-receipt.json
data/20-event-budget-example-witness.json
data/20-event-budget-guard-optimized-receipt.json
data/20-event-budget-guard-receipt.json
data/20-event-budget-interface-optimized-receipt.json
data/20-event-budget-interface-receipt.json
data/20-event-budget-portable-replay-normal-artifact-checks-receipt.json
data/20-event-budget-portable-replay-normal-independent-expansion-receipt.json
data/20-event-budget-portable-replay-normal-provenance-receipt.json
data/20-event-budget-portable-replay-normal-release-checks-receipt.json
data/20-event-budget-portable-replay-normal-universal-slots-receipt.json
data/20-event-budget-portable-replay-optimized-artifact-checks-receipt.json
data/20-event-budget-portable-replay-optimized-release-checks-receipt.json
data/20-event-budget-portable-replay-summary.json
data/20-event-budget-provenance-producer-manifest.json
data/20-event-budget-report20-qa.json
data/20-event-budget-test-optimized-receipt.json
data/20-event-budget-test-optimized.log
data/20-event-budget-test-receipt.json
data/20-event-budget-test.log
```

*Report 26, prefix `26-parallel-involutions-`* — 21 files (5 at the root, 5 in `code/`, 11 in `data/`):

```
26-parallel-involutions-PROOF.md
26-parallel-involutions-README.md
26-parallel-involutions-audit-lemma.md
26-parallel-involutions-audit-preservation.md
26-parallel-involutions-references-prior-art-audit.md
code/26-parallel-involutions-build.sh
code/26-parallel-involutions-parallel_particles.py
code/26-parallel-involutions-test_parallel.py
code/26-parallel-involutions-test_periodic_lemma.py
code/26-parallel-involutions-test_public_api.py
data/26-parallel-involutions-api-receipt.json
data/26-parallel-involutions-delivery-provenance.json
data/26-parallel-involutions-periodic-receipt-optimized.json
data/26-parallel-involutions-periodic-receipt.json
data/26-parallel-involutions-references-root-scientific-QA.json
data/26-parallel-involutions-report26-qa.json
data/26-parallel-involutions-resource-ledger.json
data/26-parallel-involutions-test-optimized.log
data/26-parallel-involutions-test-receipt-optimized.json
data/26-parallel-involutions-test-receipt.json
data/26-parallel-involutions-test.log
```

*Report 27, prefix `27-sparse-parallel-`* — 22 files (4 at the root, 5 in `code/`, 13 in `data/`):

```
27-sparse-parallel-PROOF.md
27-sparse-parallel-README.md
27-sparse-parallel-RESULTS.md
27-sparse-parallel-audit-candidate-completeness.md
code/27-sparse-parallel-audit_candidate_completeness.py
code/27-sparse-parallel-benchmark_universal.py
code/27-sparse-parallel-build.sh
code/27-sparse-parallel-sparse_parallel.py
code/27-sparse-parallel-test_sparse_parallel.py
data/27-sparse-parallel-PROVENANCE.json
data/27-sparse-parallel-audit-candidate-receipt-optimized.json
data/27-sparse-parallel-audit-candidate-receipt.json
data/27-sparse-parallel-audit-timings.json
data/27-sparse-parallel-delivery-provenance.json
data/27-sparse-parallel-references-root-scientific-QA.json
data/27-sparse-parallel-report27-qa.json
data/27-sparse-parallel-test-sparse-parallel-optimized-receipt.json
data/27-sparse-parallel-test-sparse-parallel-optimized.log
data/27-sparse-parallel-test-sparse-parallel-receipt.json
data/27-sparse-parallel-test-sparse-parallel.log
data/27-sparse-parallel-universal-receipt-optimized.json
data/27-sparse-parallel-universal-receipt.json
```

*Report 28, prefix `28-parallel-quartic-`* — 66 files (13 at the root, 15 in `code/`, 38 in `data/`):

```
28-parallel-quartic-PROOF.md
28-parallel-quartic-README.md
28-parallel-quartic-REPLAY.md
28-parallel-quartic-RESULTS.md
28-parallel-quartic-audit-design.md
28-parallel-quartic-audit-emitter.md
28-parallel-quartic-bitbound-PROOF.md
28-parallel-quartic-bitbound-README.md
28-parallel-quartic-bitbound-independent-review.md
28-parallel-quartic-evidence-REPLAY_RESULTS.md
28-parallel-quartic-evidence-output-routing-audit.md
28-parallel-quartic-evidence-verifier-binding-audit.md
28-parallel-quartic-test-oracle-report.md
code/28-parallel-quartic-audit_emitter.py
code/28-parallel-quartic-bitbound-audit_bounds.py
code/28-parallel-quartic-bitbound-check_portability.py
code/28-parallel-quartic-build.sh
code/28-parallel-quartic-check_portability.py
code/28-parallel-quartic-circuit.py
code/28-parallel-quartic-compiler.py
code/28-parallel-quartic-evidence-verifier-audit-probe_binding.py
code/28-parallel-quartic-freeze_metadata.py
code/28-parallel-quartic-prepare_test_oracle.py
code/28-parallel-quartic-test_certificate.py
code/28-parallel-quartic-test_example_validation.py
code/28-parallel-quartic-test_multisource.py
code/28-parallel-quartic-test_supplement.py
code/28-parallel-quartic-verify_example.py
data/28-parallel-quartic-PROVENANCE.json
data/28-parallel-quartic-audit-emitter-receipt.json
data/28-parallel-quartic-audit-emitter-test.log
data/28-parallel-quartic-bitbound-audit-receipt-optimized.json
data/28-parallel-quartic-bitbound-audit-receipt.json
data/28-parallel-quartic-bitbound-audit.log
data/28-parallel-quartic-bitbound-plumbing-receipt.json
data/28-parallel-quartic-bitbound-portability-receipt.json
data/28-parallel-quartic-bundle-verification.json
data/28-parallel-quartic-delivery-provenance.json
data/28-parallel-quartic-evidence-independent-scientific-QA.json
data/28-parallel-quartic-evidence-verifier-audit-independent-probes-optimized.json
data/28-parallel-quartic-evidence-verifier-audit-independent-probes.json
data/28-parallel-quartic-example-pair-quartic.json
data/28-parallel-quartic-example-pair-sos.json
data/28-parallel-quartic-example-pair-witness.json
data/28-parallel-quartic-example-source.json
data/28-parallel-quartic-example-validation-receipt-optimized.json
data/28-parallel-quartic-example-validation-receipt.json
data/28-parallel-quartic-example-verification.json
data/28-parallel-quartic-expected-supplement-receipt.json
data/28-parallel-quartic-fixture-provenance-rebind.json
data/28-parallel-quartic-fixtures.json
data/28-parallel-quartic-lineage-v1-MANIFEST.json
data/28-parallel-quartic-multisource-optimized.log
data/28-parallel-quartic-multisource-receipt-optimized.json
data/28-parallel-quartic-multisource-receipt.json
data/28-parallel-quartic-multisource.log
data/28-parallel-quartic-portability-receipt.json
data/28-parallel-quartic-receipt-optimized.json
data/28-parallel-quartic-receipt.json
data/28-parallel-quartic-report28-qa.json
data/28-parallel-quartic-resource-ledger.json
data/28-parallel-quartic-supplement-optimized.log
data/28-parallel-quartic-supplement.log
data/28-parallel-quartic-test-optimized.log
data/28-parallel-quartic-test-oracle-receipt.json
data/28-parallel-quartic-test.log
```

The three files `certificate-section.tex`, `clean-target-section.tex` and
`verification-details.tex`, which `bca6383e9` placed so that the delivered
base would build, are inlined in `article.tex` and no longer exist here.
The delivered PDFs, checksum ledgers and delivery READMEs of Reports 14–19
are not shipped; this README replaces them, and `article.pdf` is a build of
`article.tex`. (The files `16-literal-source-README.md`,
`17-startup-README.md`, `18-cell-clock-README.md`,
`14-five-binary-compiler-README.md` and similar are READMEs of
sub-packages inside the archives, shipped as delivered.)

## Labels and numbering

Every label in `article.tex` carries the prefix `fpa:`. Report 15's 40
labels (36 in `report15.tex`, 4 in its `\input` files) are `fpa:`
followed by the delivered name; Report 14's 59 labels use `fpa:bc:`,
Report 16's 23 `fpa:ls:`, Report 17's 30 `fpa:st:`, Report 18's 31
`fpa:cc:`, Report 19's 11 `fpa:lz:`: 194 delivered labels, none dropped.
The write added 28: four Part labels `fpa:part:one` … `fpa:part:four`,
nine front-matter section labels `fpa:sec:*`, `fpa:app:provenance`, twelve
`fpa:rep:<r>:first`/`fpa:rep:<r>:last` on the first and last section of
each Report, and `fpa:lz:sec:pinned`, `fpa:lz:sec:bytes` on two
unlabelled sections of Report 19. Total 222 (counted in the `.aux`).
Before the write the report's text (Report 15 as placed) had 40 labels,
all unprefixed; the prefix was applied before anything cites them.

Sections and theorems are numbered continuously (Theorem *n.m* is in
Section *n*); Sections 1–3 are the front matter and Appendix A the
provenance. Reports 15 and 16 number their displays by hand, (1), (2), …,
and cite them as "(3)"; those numbers are kept and are local to the
Report. Displays of Reports 14, 17 and 18 are numbered (*n.m*) by section.
Text added in the write is marked `[write]`.

## Notation

No symbol of any Report was renamed; each Part uses its Report's symbols.
Section 2 of the article tabulates the collisions, the worst being:
Report 14's `D = m + 2p` (unsigned codes; `p` counts rows) against
Reports 15–19's `D = 2m + 4p` (signed modes; `p` counts nonzero-update
branches); `L`, `R` as travel constant and radius in Report 15 but
half-tape integers in Reports 16–18; `K` as Report 14's contact distance
but Report 16's certificate horizon; `J` as class cutoff but also the
Turing state of the halt cell `J1`; `F` as one automaton step (Report 15)
but the factor count (Report 19). Report 14's macro `\enc` (printing
"Enc") is `\Enc` internally; nothing printed changed.

## What the report claims

- **Part I (Reports 15, 14).** Report 15, Theorem 4.1: every finite
  partial-injective guarded two-counter machine with terminal halt
  compiles effectively to a globally reversible (bijective on
  `{0,1}^Z`), number-conserving binary CA of explicit finite radius, with
  five-one encodings and an anchored halt word; Corollary 4.2 (universality
  through Morita's existential universal source); exact clocks and a full
  factor ledger (`8pD + 29p + m + a` factors); fixed-horizon certificates of
  degree ≤ 4 with empty-or-singleton natural fibers and a paid
  nonnegative-real variant (Theorem 12.1); clean exact targets
  (Corollary 13.1); Corollary 16.1: with Report 12, five is the least
  particle count for globally reversible number-conserving binary CA.
  Report 14, Theorem 18.1: every deterministic ADD/SUB/NOP two-counter
  program compiles to a binary conservative CA with mass-five encodings,
  radius `30D + 37` and a persistent halt word; a literal universal
  instance from the 8,408-row source (radius 756,787, halt word 50,452,
  1,272,679,260 indexed cases); Corollary 27.1, the sharp threshold five
  for binary conservative CA; certificates with `10,750h` witnesses and
  `2,344h + 1` squares (Theorems 28.1, 29.1).
- **Part II (Report 16).** Theorem 33.1: the pinned source (122,622
  controls, 141,561 rows, `J = 0`) is a global partial injection,
  universal on the clean family `(START, C·2^L·3^R·5^T, 0)`; Corollary
  38.1: positive return and periodicity of the fixed five-particle CA are
  r.e.-complete on that family, least period exactly `2Θ + 2`; quartic and
  shared-offset certificates (Theorems 39.1, 39.2; `141,565K` witnesses, `23,435K + 1` squares).
- **Part III (Reports 17, 18).** Four history-tag swaps preserve every clean
  input and give no-later arrival at every normalized boundary and strictly
  earlier arrival at every TM cut (Theorem 42.1); empty startup
  in 138 executed steps (against a derived 79,936,151,060,302);
  first-encounter optimality among `2^233` static orientations, `2^227`
  optimal (Theorem 47.1); Report 18 proves both statements for the CA clock
  (Theorems 53.1, 53.2) through
  `Θ = λM + TV(A²) + TV(B²) + U`, `λ = 36,684,691` (empty startup
  1,394,018,396 CA microedges).
- **Part IV (Report 19).** Theorem 65.1: `compile_lazy_source(source).step(X)` equals the
  frozen ordered product of 269,291,358,255 involutions on every finite
  support, and the inverse uses the reversed order.

Section ranges are in the table above.

## What the report does not claim

Section 3 of the article collects every limitation the six Reports state;
in short: no proof-assistant formalization, novelty or priority claim; no
intrinsic universality, efficient input conversion, minimal radius or
materialized truth table (`2^1,513,575` rows for Report 14's instance);
Report 15's universal source is existential (Report 16 supplies one);
certificate horizons are compiler arguments, so no unbounded single-fold
representation follows; the threshold corollaries depend on Report 12's
separate proof; universal startup is not executed (Report 16 predicts
about `8·10^13` source steps; Report 17 executes 138 literal steps;
Report 19 executes 128 of about `1.39·10^9` CA microsteps); Report 18's
comparison is within fixed templates; Report 19 makes no cost guarantee.

## Relation to neighbouring reports

The series continues `../signal-machine-collision-certificates` (SMC):
Reports 8–12 are its sources 13–17 (Parts IV–VI), Report 13 its source 18,
Reports 29–31 its Part VII (sources 19–21) and Reports 21–22 its Part VIII
(sources 22–23). Reports 23–25, 33, 34 are `../fixed-universal-polynomials`;
Report 32 is `../group-theoretic-substrates` Part V.

- **SMC.** Report 12 (SMC source 17, `smc:fm:thm:main`) is the lower bound
  of both threshold corollaries. Reports 14–15 supply the binary
  five-particle upper bound and the reversible binary threshold that SMC's
  front matter, its Part IV question list and source 17's non-claims call
  open (the mass-5 cell of SMC's threshold table). Report 16 answers in
  substance SMC Part IV's "Print one safe universal source" (for Report
  15's guarded syntax, not source 13's pulse interface) and in part
  `smc:tm:q:source`; its history and prime invariants are the literal form
  of SMC Part IV's §`smc:sl:sec:safe`. Report 15's clean-target wrapper is
  SMC source 15's (`smc:ct:thm:restore`, Bennett's uncomputation),
  credited in a `[write]` note. SMC source 19 (Report 29) cites Report 16
  for its four-versus-five boundary. SMC's own text is not changed by
  this write.
- **`../quadratic-orthant-certificates` (QOC).** Report 14's 8,408-row
  source is QOC Part V's (source 16); its Section 26 re-derives
  `qoc:um:lem:virtual` and `qoc:um:lem:prime` (kept as a marked second
  presentation). Report 14's degree-four certificate for that source is
  weaker than QOC's degree-two `qoc:um:thm:poly` but adds the CA clock
  (dated note). Report 16's front end is QOC's 528-row program byte for
  byte. The Neary–Woods `(u10, b)` discrepancy is printed once, in QOC
  Part III.
- **`../canonical-diophantine-certificates`.** No overlap (8-gram
  containment 0.000).

## Relation to the formal project

`../../../../../../Computability/HilbertTenthProblem/` (Lean and research
notes) is maintained by another session. At the time of this write its
research programme has **not reviewed Reports 14–19**: its note
`Papers/research-wip/native-stream-queue/reviewed_report_archive_replay.md`
(commit `ceb7222e9`) lists the six archives as "Relocation only" and says
that copying them is not a scientific review; its materializer
`reviewed_report_archive_replay.py` restores all 23 batch-82 archives,
pinned by size and SHA-256, from revision `55d248dc5` into an external
cache (another way to obtain the delivered layout). Its review
`Papers/research-wip/native-stream-queue/review_parallel_particle_reports.md`
(commit `fb7e3cb47`) covers Reports 26–28 of the future Parts V–VI, finds
no defect, and records that the inherited template geometry and source
simulation of Reports 15–17 is a dependency it did not reconstruct;
`review_binary_planar_four_particle31.md` (`16f50dcc6`) concerns
Report 31 (SMC Part VII). Its note `neary_woods_explicit_universal_tm.md`
transcribes the same Neary–Woods table. Placement beside a formal
development confers no formal status: **no statement of this report is
formalized**, and no Lean or Rocq declaration is cited.

## Delivery names, renames and discrepancies

Shipped files are byte-identical to the archive members. Their names drop
the archive's top directory (and `report/`, `source/`, `reproducibility/`)
and replace `/` by `-`, after the prefix `14-five-binary-`,
`15-rev-five-`, `16-literal-source-`, `17-startup-`, `18-cell-clock-` or
`19-lazy-eval-`; programs and build scripts are in `code/`, JSON receipts,
traces and examples in `data/`, proof, audit and provenance Markdown at the
root. Report 15's figure is `figures/accepting-orbit.pdf` (delivered
name), Report 14's is `figures/14-five-binary-five-particle-trace.pdf`
(delivered `figures/five-particle-trace.pdf`). The complete map is at the
end of this README.

- **Delivery names in shipped text.** Every shipped program, audit and
  provenance file names delivery paths (for example `compiler/AUDIT.md`,
  `reproducibility/run_checks.py`, `source/source.json`, `dependency/…`,
  `companions/report15/`, `release-manifest.json`), and so does the
  article's text. The programs therefore run only in the delivered layout
  (see "Rerunning the checks").
- **Unshipped files named by shipped ones.** The delivered PDFs and their
  `.tex` sources (printed here), checksum ledgers and manifests
  (`SHA256SUMS`, `release-manifest.json`(`.sha256`), `manifest.json`), the
  companion copies of Report 12 (= SMC source 17) and of Report 15 inside
  archive 13, Report 15's compiler copies inside archives 13, 16, 04 and 09
  (shipped once, as `code/15-rev-five-compiler-reversible_binary.py`),
  archive 04's re-shipped copy of Report 17's package (70 files including
  the 56 MB table family; staged once, from archive 16 — Report 17's README
  says the old table pair is "never duplicated", which holds only within
  archive 16), QOC files re-shipped under `dependency/` and
  `source-replay/` (`virtual3.json` = `QOC/data/16-universal-membrane-virtual3.json`,
  `virtual3.txt`, `macro_certificates.json`, `tm_table.json`,
  `UniversalTM15x2.tm.txt` = `QOC/data/14-waterfall-UniversalTM15x2.tm.txt`,
  `verify_source.py` and its receipt = QOC's
  `17-reset-net-two-counter-*`), the excerpt note `dependency/PROOF.md`,
  archive 09's `portable-replay/` outputs and `.log` files, and the
  eighteen heavy generated files of the next section. All survive in
  `db37d18c8`.
- **Wrong Neary–Woods citation (dated correction, 3 October 2026).**
  Reports 14, 16, 17 and 18 cite Neary–Woods as *Fundamenta Informaticae*
  91 (2009), 105–126, DOI 10.3233/FI-2009-0008, and Reports 14 and 16 call
  123–144 incorrect. DOI 10.3233/FI-2009-0008 is Han–Salomaa–Wood (FI 90,
  93–106); Neary–Woods is FI 91(1) (2009) 123–144,
  DOI 10.3233/FI-2009-0036 (Crossref, checked 3 October 2026), as QOC
  cites it; 105–126 is the author-hosted PDF's own pagination. The
  article's bibliography follows the publisher and its text carries dated
  notes. These shipped files keep the wrong DOI or pages, byte-identical:
  `14-five-binary-compiler-AUDIT.md`,
  `14-five-binary-compiler-SOURCE_PROVENANCE.md`,
  `14-five-binary-compiler-proof.md`,
  `14-five-binary-provenance-RELEASE_PROVENANCE.md`,
  `16-literal-source-PROOF.md`, `17-startup-PROOF.md`,
  `data/14-five-binary-provenance-primary-source-review.json`,
  `data/16-literal-source-PROVENANCE.json`,
  `data/17-startup-PROVENANCE.json`, `data/18-cell-clock-PROVENANCE.json`.
- **Byte copies across the series.** Report 19's evaluator
  (`code/19-lazy-eval-lazy_reversible.py`) and Report 15's compiler are
  re-shipped inside the M2 archives of Reports 20 and 26–28; the M2
  placement did not stage them twice.

## Rerunning the checks

Delivered programs are byte-identical and unpatched, and many write their
outputs into the delivered tree, overwriting recorded receipts. **Never run
them in this directory.** The reliable route is to extract the original
archive into a scratch directory and run there (the archive also contains
the heavy files this report does not ship):

    git show db37d18c8:docs/incoming/Reversible_Binary_Five_Particle_Package.zip > r15.zip
    unzip -q r15.zip -d scratch-r15 && cd scratch-r15/reversible-five-particle
    python3 replay.py

The delivered entry points are: Report 14 `python3 replay.py`; Report 15
`python3 replay.py`; Report 16 `python3 replay.py --receipt <path outside
the tree>` (or its individual checkers, listed in
`16-literal-source-README.md`); Reports 17 and 18 `python3
verify_release.py`, then `python3 reproducibility/run_checks.py` (never
`--record`); Report 19 `python3 verify_release.py`, `python3
release_checks.py`, `python3 replay.py --out <new directory outside the
release>`. All need only the Python standard library (Report 19 targets
Python ≥ 3.12, Report 14 ≥ 3.10).

Hazards measured at placement (Windows, Python 3.14.4, on copies):

- Every producer writes text with `write_text`, so on Windows its outputs
  have CRLF line ends; they equal the recorded files after CRLF→LF, and
  manifest checks that follow a regeneration then fail. Run under POSIX,
  or compare modulo line ends.
- Report 14's `replay.py` passes all seven stages (89 s) and then stops at
  "Manifest mismatch", because the stages rewrote twelve receipts in place.
- Report 15's `replay.py` fails at once on Windows (it compares
  `str(p.relative_to(ROOT))`, which uses backslashes); under POSIX, or with
  that one line patched on a copy, it passes 20 stages in about 146 s.
  Its `tools/render_trace.py` rewrites `figures/accepting-orbit.pdf` and
  `.svg` in place (the PDF byte-identically).
- Reports 17 and 18: `offline_stage.py` calls `Path(executable)` with
  `None` on Windows, so `run_checks.py` stops at
  `independent_relabel_check.py`; on POSIX (or a patched copy) Report 17's
  14 stages pass twice in about 158 s. Report 18's six
  `cellular-clock/` checks pass unpatched (`check_ca_clock` about 75 s).
- Report 16's full replay exceeds three minutes (ten stages in 170 s, the
  remaining two separately in 13 s and 17 s).
- Report 19's `benchmark_universal.py` imports the Unix-only `resource`
  module; the other steps pass on Windows (`test_lazy` about 90 s per mode).

## Reconstructing the excluded data

Vladimir, 2026-10-02: "Exclude heavy regenerable artifacts". Eighteen
generated files, 173,983,046 bytes in all, are not shipped. Each survives in
its archive (`git show db37d18c8:docs/incoming/<archive> > <archive>`) and is
rebuilt by shipped code using only the Python standard library. The
producers expect the delivered layout: run them on a copy (a fresh
extraction of the archive, or the shipped files copied under their
delivered names), never in this directory, and pass no path inside it. On
Windows they write CRLF; the outputs equal the delivered bytes after
CRLF→LF conversion (exactly, under POSIX).

| Files (delivered path) | Bytes | Rebuild (in a copy) | Time |
|---|---:|---|---|
| Report 16 (archive 13) `source/source.json`, `source/reversible2-primitives.json`, `source/certificates.json`, `source/reversible5.json` | 32,034,272; 21,764,936; 1,200,550; 820,323 | `cp code/16-literal-source-build_source.py <copy>/build_source.py`; `cp ../quadratic-orthant-certificates/data/16-universal-membrane-virtual3.json <copy>/dependency/virtual3.json`; `cd <copy> && python3 -B build_source.py` (also rewrites `primitive3.json`, `normalized3.json`, `build-stats.json`, which are shipped as `data/16-literal-source-*.json`) | 2–5 s, about 210 MB |
| Report 17 (archive 16) `reproducibility/` same four names; Report 18 (archive 04) ships identical copies | same sizes | the same with `code/17-startup-build_source.py` | 2–5 s, about 240 MB |
| Report 19 (archive 09) `reproducibility/source.json.gz` | 1,599,790 | gzip of Report 17's `source.json` (LF): `gzip.compress(data, compresslevel=9, mtime=0)`, then set byte 9 to `0x03`, **under Python 3.11–3.13** (stock zlib 1.3.1); Python 3.14 (zlib-ng) and GNU gzip give different valid streams (1,599,993 bytes under 3.14), which the evaluator accepts but the release manifest does not | 2 s |
| Report 14 (archive 23) `compiler/source-replay/source/literal2.json`, `literal2.txt` | 878,685; 504,996 | QOC source 16's `packet/literal2.*`: copy `../quadratic-orthant-certificates/code/16-universal-membrane-packet-build_frontend.py` to `<copy>/build_frontend.py` and `../quadratic-orthant-certificates/data/14-waterfall-UniversalTM15x2.tm.txt` to `<copy>/source/UniversalTM15x2.tm.txt`; `python3 build_frontend.py` writes both beside the script; copy them to `compiler/source-replay/source/` of the Report 14 layout | 1 s |
| Report 14 `compiler/universal_h1_frontend.json` | 2,208,310 | in the Report 14 layout, with the two `literal2` files restored: `cd compiler && python3 check_frontend.py` | 3 s |
| Report 15 (archive 15) `compiler/clean-target-sample-orbit.json` | 837,481 | in the Report 15 layout: `cd compiler && python3 clean_target_sample.py` | 22 s |
| Report 15 `figures/accepting-orbit.svg` | 493,541 | in the Report 15 layout: `python3 tools/render_trace.py` (reads `compiler/sample-orbit.json` = `data/15-rev-five-compiler-sample-orbit.json`; also rewrites the figure PDF, byte-identically) | 1 s |

SHA-256 checks: Report 16's `source.json` is `38c586706fa1…` (printed in
Section 33), Report 17's `fa61d06178d7…` (printed in Section 76, with
its size). Reports 17–19's release checkers (`verify_pins.py`,
`run_checks.py`, `verify_release.py`, `replay.py`) treat the four tables
and the `.gz` as mandatory inputs: rebuild them first, or run from the
archive.

Re-verified for this write (3 October 2026, Windows, on copies under the
session scratch directory): Report 17's four tables from
`code/17-startup-build_source.py` and QOC's `virtual3.json` (1.4 s;
LF-identical, `source.json` SHA-256 `fa61d06178d7…`); Report 16's seven
outputs from `code/16-literal-source-build_source.py` (1.5 s;
LF-identical, `38c586706fa1…`); the `.gz` under Python 3.12 (identical,
1,599,790 bytes) and under 3.14 (1,599,993 bytes, different); Report 14's
`literal2` pair from QOC's builder (0.6 s; LF-identical); Report 15's SVG
and PDF from `render_trace.py` (0.1 s; SVG LF-identical, PDF identical).
The other rows were verified at placement (dossier timings).

## Build

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

pdfLaTeX (MiKTeX), standalone with an internal bibliography; needs the two
PDFs in `figures/`. The build of this text has 121 pages (Part I
from page 13, Part II from 55, Part III from 80, Part IV from 106, the
provenance appendix from 118), no undefined references or citations, no
multiply-defined labels and no duplicate destinations. One overfull line
(13 pt) is in Report 14's own text (Section 31, a long file name).

## Delivered path → shipped path

<details>
<summary>All 248 files of Reports 14–19 shipped from the archives (`article.tex`, `README.md` and the three inlined inputs of the base, rewritten or removed in the write, omitted)</summary>

`five-particle-binary-portable.zip` (path inside the archive → shipped path):

```
five-particle-binary/compiler/AUDIT.md  ->  14-five-binary-compiler-AUDIT.md
five-particle-binary/compiler/README.md  ->  14-five-binary-compiler-README.md
five-particle-binary/compiler/SOURCE_PROVENANCE.md  ->  14-five-binary-compiler-SOURCE_PROVENANCE.md
five-particle-binary/compiler/audit_api_independent.py  ->  code/14-five-binary-compiler-audit_api_independent.py
five-particle-binary/compiler/audit_api_normal.json  ->  data/14-five-binary-compiler-audit_api_normal.json
five-particle-binary/compiler/audit_api_optimized.json  ->  data/14-five-binary-compiler-audit_api_optimized.json
five-particle-binary/compiler/audit_frontend_independent.json  ->  data/14-five-binary-compiler-audit_frontend_independent.json
five-particle-binary/compiler/audit_frontend_independent.py  ->  code/14-five-binary-compiler-audit_frontend_independent.py
five-particle-binary/compiler/audit_independent.json  ->  data/14-five-binary-compiler-audit_independent.json
five-particle-binary/compiler/audit_independent.py  ->  code/14-five-binary-compiler-audit_independent.py
five-particle-binary/compiler/audit_literal_boundaries.json  ->  data/14-five-binary-compiler-audit_literal_boundaries.json
five-particle-binary/compiler/audit_literal_boundaries.py  ->  code/14-five-binary-compiler-audit_literal_boundaries.py
five-particle-binary/compiler/audit_regression_modes.json  ->  data/14-five-binary-compiler-audit_regression_modes.json
five-particle-binary/compiler/audit_regression_modes.py  ->  code/14-five-binary-compiler-audit_regression_modes.py
five-particle-binary/compiler/check_five_binary.py  ->  code/14-five-binary-compiler-check_five_binary.py
five-particle-binary/compiler/check_frontend.py  ->  code/14-five-binary-compiler-check_frontend.py
five-particle-binary/compiler/checks.json  ->  data/14-five-binary-compiler-checks.json
five-particle-binary/compiler/example_frontend.json  ->  data/14-five-binary-compiler-example_frontend.json
five-particle-binary/compiler/example_witness.json  ->  data/14-five-binary-compiler-example_witness.json
five-particle-binary/compiler/five_binary.py  ->  code/14-five-binary-compiler-five_binary.py
five-particle-binary/compiler/frontend.py  ->  code/14-five-binary-compiler-frontend.py
five-particle-binary/compiler/frontend_checks.json  ->  data/14-five-binary-compiler-frontend_checks.json
five-particle-binary/compiler/proof.md  ->  14-five-binary-compiler-proof.md
five-particle-binary/provenance/RELEASE_PROVENANCE.md  ->  14-five-binary-provenance-RELEASE_PROVENANCE.md
five-particle-binary/provenance/primary-source-review.json  ->  data/14-five-binary-provenance-primary-source-review.json
five-particle-binary/replay.py  ->  code/14-five-binary-replay.py
five-particle-binary/report/build.sh  ->  code/14-five-binary-build.sh
five-particle-binary/report/figures/five-particle-trace.pdf  ->  figures/14-five-binary-five-particle-trace.pdf
five-particle-binary/report/figures/generate_figure.py  ->  code/14-five-binary-figures-generate_figure.py
five-particle-binary/report/figures/verified_trace.json  ->  data/14-five-binary-figures-verified_trace.json
five-particle-binary/verification/check_report_fixtures.py  ->  code/14-five-binary-verification-check_report_fixtures.py
five-particle-binary/verification/fresh_payload_replay_receipt.json  ->  data/14-five-binary-verification-fresh_payload_replay_receipt.json
five-particle-binary/verification/pdf_quality_receipt.json  ->  data/14-five-binary-verification-pdf_quality_receipt.json
```

`Reversible_Binary_Five_Particle_Package.zip` (path inside the archive → shipped path):

```
reversible-five-particle/audits/README.md  ->  15-rev-five-audits-README.md
reversible-five-particle/audits/audit_api.py  ->  code/15-rev-five-audits-audit_api.py
reversible-five-particle/audits/audit_certificate.py  ->  code/15-rev-five-audits-audit_certificate.py
reversible-five-particle/build.sh  ->  code/15-rev-five-build.sh
reversible-five-particle/certificates/certificate.py  ->  code/15-rev-five-certificates-certificate.py
reversible-five-particle/certificates/clean-target-certificate.json  ->  data/15-rev-five-certificates-clean-target-certificate.json
reversible-five-particle/certificates/clean-target-real-certificate.json  ->  data/15-rev-five-certificates-clean-target-real-certificate.json
reversible-five-particle/certificates/clean-target-real-witness.json  ->  data/15-rev-five-certificates-clean-target-real-witness.json
reversible-five-particle/certificates/clean-target-sample-source.json  ->  data/15-rev-five-certificates-clean-target-sample-source.json
reversible-five-particle/certificates/sample-certificate.json  ->  data/15-rev-five-certificates-sample-certificate.json
reversible-five-particle/certificates/sample-real-certificate.json  ->  data/15-rev-five-certificates-sample-real-certificate.json
reversible-five-particle/certificates/sample-real-witness.json  ->  data/15-rev-five-certificates-sample-real-witness.json
reversible-five-particle/certificates/sample-source.json  ->  data/15-rev-five-certificates-sample-source.json
reversible-five-particle/certificates/test_certificate.py  ->  code/15-rev-five-certificates-test_certificate.py
reversible-five-particle/compiler/SOURCE_SCHEMA.md  ->  15-rev-five-compiler-SOURCE_SCHEMA.md
reversible-five-particle/compiler/additional_tests.py  ->  code/15-rev-five-compiler-additional_tests.py
reversible-five-particle/compiler/checks/compiler_stress.py  ->  code/15-rev-five-compiler-checks-compiler_stress.py
reversible-five-particle/compiler/checks/exhaustive_audit.py  ->  code/15-rev-five-compiler-checks-exhaustive_audit.py
reversible-five-particle/compiler/checks/verify_clean_fixture.py  ->  code/15-rev-five-compiler-checks-verify_clean_fixture.py
reversible-five-particle/compiler/checks/verify_original_fixture.py  ->  code/15-rev-five-compiler-checks-verify_original_fixture.py
reversible-five-particle/compiler/clean-target-sample-receipt.json  ->  data/15-rev-five-compiler-clean-target-sample-receipt.json
reversible-five-particle/compiler/clean_target_sample.py  ->  code/15-rev-five-compiler-clean_target_sample.py
reversible-five-particle/compiler/full_cycle_test.py  ->  code/15-rev-five-compiler-full_cycle_test.py
reversible-five-particle/compiler/reversible_binary.py  ->  code/15-rev-five-compiler-reversible_binary.py
reversible-five-particle/compiler/sample-boundary-demonstration.json  ->  data/15-rev-five-compiler-sample-boundary-demonstration.json
reversible-five-particle/compiler/sample-orbit.json  ->  data/15-rev-five-compiler-sample-orbit.json
reversible-five-particle/compiler/sample-receipt.json  ->  data/15-rev-five-compiler-sample-receipt.json
reversible-five-particle/compiler/sample_orbit.py  ->  code/15-rev-five-compiler-sample_orbit.py
reversible-five-particle/compiler/test_compiler.py  ->  code/15-rev-five-compiler-test_compiler.py
reversible-five-particle/figures/accepting-orbit.pdf  ->  figures/accepting-orbit.pdf
reversible-five-particle/replay.py  ->  code/15-rev-five-replay.py
reversible-five-particle/tools/render_trace.py  ->  code/15-rev-five-tools-render_trace.py
```

`Literal_Universal_Reversible_Source_Package.zip` (path inside the archive → shipped path):

```
literal-reversible-source-release-20261003/PACKAGING-ADAPTATIONS.md  ->  16-literal-source-PACKAGING-ADAPTATIONS.md
literal-reversible-source-release-20261003/audits/primitive/AUDIT.md  ->  16-literal-source-audits-primitive-AUDIT.md
literal-reversible-source-release-20261003/audits/primitive/INDEPENDENT-PROOF.md  ->  16-literal-source-audits-primitive-INDEPENDENT-PROOF.md
literal-reversible-source-release-20261003/audits/primitive/audit-normal-receipt.json  ->  data/16-literal-source-audits-primitive-audit-normal-receipt.json
literal-reversible-source-release-20261003/audits/primitive/audit-optimized-receipt.json  ->  data/16-literal-source-audits-primitive-audit-optimized-receipt.json
literal-reversible-source-release-20261003/audits/primitive/audit_certificate.py  ->  code/16-literal-source-audits-primitive-audit_certificate.py
literal-reversible-source-release-20261003/audits/primitive/literal-ledger-H0.json  ->  data/16-literal-source-audits-primitive-literal-ledger-H0.json
literal-reversible-source-release-20261003/audits/primitive/literal-ledger-H1.json  ->  data/16-literal-source-audits-primitive-literal-ledger-H1.json
literal-reversible-source-release-20261003/audits/primitive/literal-ledger-H2.json  ->  data/16-literal-source-audits-primitive-literal-ledger-H2.json
literal-reversible-source-release-20261003/audits/primitive/source-audit.json  ->  data/16-literal-source-audits-primitive-source-audit.json
literal-reversible-source-release-20261003/audits/release-audit-optimized-receipt.json  ->  data/16-literal-source-audits-release-audit-optimized-receipt.json
literal-reversible-source-release-20261003/audits/release-audit-receipt.json  ->  data/16-literal-source-audits-release-audit-receipt.json
literal-reversible-source-release-20261003/audits/release-level-audit.md  ->  16-literal-source-audits-release-level-audit.md
literal-reversible-source-release-20261003/audits/release_audit.py  ->  code/16-literal-source-audits-release_audit.py
literal-reversible-source-release-20261003/audits/stabilized-hashes.json  ->  data/16-literal-source-audits-stabilized-hashes.json
literal-reversible-source-release-20261003/build.sh  ->  code/16-literal-source-build.sh
literal-reversible-source-release-20261003/primitive-certificates/PROOF.md  ->  16-literal-source-primitive-certificates-PROOF.md
literal-reversible-source-release-20261003/primitive-certificates/README.md  ->  16-literal-source-primitive-certificates-README.md
literal-reversible-source-release-20261003/primitive-certificates/audit_source.py  ->  code/16-literal-source-primitive-certificates-audit_source.py
literal-reversible-source-release-20261003/primitive-certificates/certificate.py  ->  code/16-literal-source-primitive-certificates-certificate.py
literal-reversible-source-release-20261003/primitive-certificates/example-materialized.json  ->  data/16-literal-source-primitive-certificates-example-materialized.json
literal-reversible-source-release-20261003/primitive-certificates/example-source.json  ->  data/16-literal-source-primitive-certificates-example-source.json
literal-reversible-source-release-20261003/primitive-certificates/example-witness.json  ->  data/16-literal-source-primitive-certificates-example-witness.json
literal-reversible-source-release-20261003/primitive-certificates/primitive-example-ca-receipt.json  ->  data/16-literal-source-primitive-certificates-primitive-example-ca-receipt.json
literal-reversible-source-release-20261003/primitive-certificates/primitive-example-orbit.json  ->  data/16-literal-source-primitive-certificates-primitive-example-orbit.json
literal-reversible-source-release-20261003/primitive-certificates/replay_primitive_ca.py  ->  code/16-literal-source-primitive-certificates-replay_primitive_ca.py
literal-reversible-source-release-20261003/primitive-certificates/source-ledger-receipt.json  ->  data/16-literal-source-primitive-certificates-source-ledger-receipt.json
literal-reversible-source-release-20261003/primitive-certificates/test-receipt.json  ->  data/16-literal-source-primitive-certificates-test-receipt.json
literal-reversible-source-release-20261003/primitive-certificates/test_certificate.py  ->  code/16-literal-source-primitive-certificates-test_certificate.py
literal-reversible-source-release-20261003/primitive-certificates/universal-h1-ledger.json  ->  data/16-literal-source-primitive-certificates-universal-h1-ledger.json
literal-reversible-source-release-20261003/replay.py  ->  code/16-literal-source-replay.py
literal-reversible-source-release-20261003/source/PROOF.md  ->  16-literal-source-PROOF.md
literal-reversible-source-release-20261003/source/PROVENANCE.json  ->  data/16-literal-source-PROVENANCE.json
literal-reversible-source-release-20261003/source/README.md  ->  16-literal-source-README.md
literal-reversible-source-release-20261003/source/affine-receipt.json  ->  data/16-literal-source-affine-receipt.json
literal-reversible-source-release-20261003/source/all-checks-receipt.json  ->  data/16-literal-source-all-checks-receipt.json
literal-reversible-source-release-20261003/source/build-stats.json  ->  data/16-literal-source-build-stats.json
literal-reversible-source-release-20261003/source/build_source.py  ->  code/16-literal-source-build_source.py
literal-reversible-source-release-20261003/source/check_primary_table.py  ->  code/16-literal-source-check_primary_table.py
literal-reversible-source-release-20261003/source/class-expansion-ledger.json  ->  data/16-literal-source-class-expansion-ledger.json
literal-reversible-source-release-20261003/source/class_expansion_ledger.py  ->  code/16-literal-source-class_expansion_ledger.py
literal-reversible-source-release-20261003/source/compiler-reference/COMPILER_PROOF.md  ->  16-literal-source-compiler-reference-COMPILER_PROOF.md
literal-reversible-source-release-20261003/source/compiler-reference/SOURCE_SCHEMA.md  ->  16-literal-source-compiler-reference-SOURCE_SCHEMA.md
literal-reversible-source-release-20261003/source/concrete-receipt.json  ->  data/16-literal-source-concrete-receipt.json
literal-reversible-source-release-20261003/source/independent-audit-receipt.json  ->  data/16-literal-source-independent-audit-receipt.json
literal-reversible-source-release-20261003/source/independent-macro-audit.md  ->  16-literal-source-independent-macro-audit.md
literal-reversible-source-release-20261003/source/independent_audit.py  ->  code/16-literal-source-independent_audit.py
literal-reversible-source-release-20261003/source/loader-api-receipt.json  ->  data/16-literal-source-loader-api-receipt.json
literal-reversible-source-release-20261003/source/loader-empty-tape.json  ->  data/16-literal-source-loader-empty-tape.json
literal-reversible-source-release-20261003/source/loader.py  ->  code/16-literal-source-loader.py
literal-reversible-source-release-20261003/source/normalized3.json  ->  data/16-literal-source-normalized3.json
literal-reversible-source-release-20261003/source/periodicity-audit.md  ->  16-literal-source-periodicity-audit.md
literal-reversible-source-release-20261003/source/primary-table-receipt.json  ->  data/16-literal-source-primary-table-receipt.json
literal-reversible-source-release-20261003/source/primitive3.json  ->  data/16-literal-source-primitive3.json
literal-reversible-source-release-20261003/source/prologue-predicted-clocks.json  ->  data/16-literal-source-prologue-predicted-clocks.json
literal-reversible-source-release-20261003/source/run_checks.py  ->  code/16-literal-source-run_checks.py
literal-reversible-source-release-20261003/source/schema-injection-receipt.json  ->  data/16-literal-source-schema-injection-receipt.json
literal-reversible-source-release-20261003/source/target-ledger.json  ->  data/16-literal-source-target-ledger.json
literal-reversible-source-release-20261003/source/test_concrete.py  ->  code/16-literal-source-test_concrete.py
literal-reversible-source-release-20261003/source/test_loader.py  ->  code/16-literal-source-test_loader.py
literal-reversible-source-release-20261003/source/validate_source.py  ->  code/16-literal-source-validate_source.py
literal-reversible-source-release-20261003/source/verify_affine.py  ->  code/16-literal-source-verify_affine.py
literal-reversible-source-release-20261003/source/verify_virtual3.py  ->  code/16-literal-source-verify_virtual3.py
literal-reversible-source-release-20261003/tools/make_manifest.py  ->  code/16-literal-source-tools-make_manifest.py
literal-reversible-source-release-20261003/tools/make_release.py  ->  code/16-literal-source-tools-make_release.py
```

`Reversible_Startup_Optimization_Package.zip` (path inside the archive → shipped path):

```
reversible-startup-report17/build.sh  ->  code/17-startup-build.sh
reversible-startup-report17/report17-qa.json  ->  data/17-startup-report17-qa.json
reversible-startup-report17/reproducibility/OPTIMIZATION.md  ->  17-startup-OPTIMIZATION.md
reversible-startup-report17/reproducibility/PORTABILITY.md  ->  17-startup-PORTABILITY.md
reversible-startup-report17/reproducibility/PROOF.md  ->  17-startup-PROOF.md
reversible-startup-report17/reproducibility/PROVENANCE.json  ->  data/17-startup-PROVENANCE.json
reversible-startup-report17/reproducibility/README.md  ->  17-startup-README.md
reversible-startup-report17/reproducibility/baseline-rebuild-receipt.json  ->  data/17-startup-baseline-rebuild-receipt.json
reversible-startup-report17/reproducibility/baseline/expected-outputs.json  ->  data/17-startup-baseline-expected-outputs.json
reversible-startup-report17/reproducibility/baseline_support.py  ->  code/17-startup-baseline_support.py
reversible-startup-report17/reproducibility/build_source.py  ->  code/17-startup-build_source.py
reversible-startup-report17/reproducibility/byte-exact-rebuild-receipt.json  ->  data/17-startup-byte-exact-rebuild-receipt.json
reversible-startup-report17/reproducibility/check_primary_table.py  ->  code/17-startup-check_primary_table.py
reversible-startup-report17/reproducibility/class-expansion-ledger.json  ->  data/17-startup-class-expansion-ledger.json
reversible-startup-report17/reproducibility/class_expansion_ledger.py  ->  code/17-startup-class_expansion_ledger.py
reversible-startup-report17/reproducibility/empty-first-tm-five-trace.json  ->  data/17-startup-empty-first-tm-five-trace.json
reversible-startup-report17/reproducibility/empty-first-tm-literal-trace.json  ->  data/17-startup-empty-first-tm-literal-trace.json
reversible-startup-report17/reproducibility/empty-prologue-five-trace.json  ->  data/17-startup-empty-prologue-five-trace.json
reversible-startup-report17/reproducibility/empty-prologue-literal-trace.json  ->  data/17-startup-empty-prologue-literal-trace.json
reversible-startup-report17/reproducibility/empty-through-first-tm-literal-trace.json  ->  data/17-startup-empty-through-first-tm-literal-trace.json
reversible-startup-report17/reproducibility/exact-delta-receipt.json  ->  data/17-startup-exact-delta-receipt.json
reversible-startup-report17/reproducibility/historical/portability-adaptations.json  ->  data/17-startup-historical-portability-adaptations.json
reversible-startup-report17/reproducibility/historical/predecessor-preservation-receipt.json  ->  data/17-startup-historical-predecessor-preservation-receipt.json
reversible-startup-report17/reproducibility/independent-audit-receipt.json  ->  data/17-startup-independent-audit-receipt.json
reversible-startup-report17/reproducibility/independent-macro-audit.md  ->  17-startup-independent-macro-audit.md
reversible-startup-report17/reproducibility/independent-relabel-audit.md  ->  17-startup-independent-relabel-audit.md
reversible-startup-report17/reproducibility/independent-relabel-receipt.json  ->  data/17-startup-independent-relabel-receipt.json
reversible-startup-report17/reproducibility/independent_audit.py  ->  code/17-startup-independent_audit.py
reversible-startup-report17/reproducibility/independent_relabel_check.py  ->  code/17-startup-independent_relabel_check.py
reversible-startup-report17/reproducibility/initialization-receipt.json  ->  data/17-startup-initialization-receipt.json
reversible-startup-report17/reproducibility/loader.py  ->  code/17-startup-loader.py
reversible-startup-report17/reproducibility/offline_stage.py  ->  code/17-startup-offline_stage.py
reversible-startup-report17/reproducibility/orientation-addendum/FIRST_ENCOUNTER_OPTIMALITY.md  ->  17-startup-orientation-addendum-FIRST_ENCOUNTER_OPTIMALITY.md
reversible-startup-report17/reproducibility/orientation-addendum/first-encounter-independent-audit.md  ->  17-startup-orientation-addendum-first-encounter-independent-audit.md
reversible-startup-report17/reproducibility/orientation-addendum/first-encounter-manifest.json  ->  data/17-startup-orientation-addendum-first-encounter-manifest.json
reversible-startup-report17/reproducibility/orientation-addendum/pin-verification-receipt.json  ->  data/17-startup-orientation-addendum-pin-verification-receipt.json
reversible-startup-report17/reproducibility/periodicity-audit.md  ->  17-startup-periodicity-audit.md
reversible-startup-report17/reproducibility/primary-table-receipt.json  ->  data/17-startup-primary-table-receipt.json
reversible-startup-report17/reproducibility/prologue-predicted-clocks.json  ->  data/17-startup-prologue-predicted-clocks.json
reversible-startup-report17/reproducibility/replay-receipt.json  ->  data/17-startup-replay-receipt.json
reversible-startup-report17/reproducibility/run_checks.py  ->  code/17-startup-run_checks.py
reversible-startup-report17/reproducibility/schema-injection-receipt.json  ->  data/17-startup-schema-injection-receipt.json
reversible-startup-report17/reproducibility/test_concrete.py  ->  code/17-startup-test_concrete.py
reversible-startup-report17/reproducibility/test_loader.py  ->  code/17-startup-test_loader.py
reversible-startup-report17/reproducibility/validate_source.py  ->  code/17-startup-validate_source.py
reversible-startup-report17/reproducibility/verify_affine.py  ->  code/17-startup-verify_affine.py
reversible-startup-report17/reproducibility/verify_exact_delta.py  ->  code/17-startup-verify_exact_delta.py
reversible-startup-report17/reproducibility/verify_initialization.py  ->  code/17-startup-verify_initialization.py
reversible-startup-report17/reproducibility/verify_manifest.py  ->  code/17-startup-verify_manifest.py
reversible-startup-report17/reproducibility/verify_orientation_pins.py  ->  code/17-startup-verify_orientation_pins.py
reversible-startup-report17/reproducibility/verify_pins.py  ->  code/17-startup-verify_pins.py
reversible-startup-report17/reproducibility/verify_rebuild.py  ->  code/17-startup-verify_rebuild.py
reversible-startup-report17/reproducibility/verify_virtual3.py  ->  code/17-startup-verify_virtual3.py
reversible-startup-report17/reproducibility/write_manifest.py  ->  code/17-startup-write_manifest.py
reversible-startup-report17/verify_release.py  ->  code/17-startup-verify_release.py
```

`Cellular_Clock_Domination_Package.zip` (path inside the archive → shipped path):

```
cellular-clock-release-20261003/build.sh  ->  code/18-cell-clock-build.sh
cellular-clock-release-20261003/report18-qa.json  ->  data/18-cell-clock-report18-qa.json
cellular-clock-release-20261003/reproducibility/PORTABILITY.md  ->  18-cell-clock-PORTABILITY.md
cellular-clock-release-20261003/reproducibility/PROVENANCE.json  ->  data/18-cell-clock-PROVENANCE.json
cellular-clock-release-20261003/reproducibility/README.md  ->  18-cell-clock-README.md
cellular-clock-release-20261003/reproducibility/cellular-clock/CA_CLOCK_DOMINATION.md  ->  18-cell-clock-cellular-clock-CA_CLOCK_DOMINATION.md
cellular-clock-release-20261003/reproducibility/cellular-clock/README.md  ->  18-cell-clock-cellular-clock-README.md
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/AUDIT.md  ->  18-cell-clock-cellular-clock-audit-AUDIT.md
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/check_ca_clock.py  ->  code/18-cell-clock-cellular-clock-audit-check_ca_clock.py
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/check_old_new_startup.py  ->  code/18-cell-clock-cellular-clock-audit-check_old_new_startup.py
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/check_proof_corollaries.py  ->  code/18-cell-clock-cellular-clock-audit-check_proof_corollaries.py
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/corollaries-receipt.json  ->  data/18-cell-clock-cellular-clock-audit-corollaries-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/old-new-five-row-traces.json  ->  data/18-cell-clock-cellular-clock-audit-old-new-five-row-traces.json
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/old-new-startup-receipt.json  ->  data/18-cell-clock-cellular-clock-audit-old-new-startup-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/audit/receipt.json  ->  data/18-cell-clock-cellular-clock-audit-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/clock-receipt.json  ->  data/18-cell-clock-cellular-clock-clock-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/clock_verify.py  ->  code/18-cell-clock-cellular-clock-clock_verify.py
cellular-clock-release-20261003/reproducibility/cellular-clock/compare_empty_startup.py  ->  code/18-cell-clock-cellular-clock-compare_empty_startup.py
cellular-clock-release-20261003/reproducibility/cellular-clock/old-new-empty-startup-receipt.json  ->  data/18-cell-clock-cellular-clock-old-new-empty-startup-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/portable-input-manifest-receipt.json  ->  data/18-cell-clock-cellular-clock-portable-input-manifest-receipt.json
cellular-clock-release-20261003/reproducibility/cellular-clock/verify_manifests.py  ->  code/18-cell-clock-cellular-clock-verify_manifests.py
cellular-clock-release-20261003/reproducibility/historical/report18-adaptations.json  ->  data/18-cell-clock-historical-report18-adaptations.json
cellular-clock-release-20261003/reproducibility/historical/source-manifest-inspection.json  ->  data/18-cell-clock-historical-source-manifest-inspection.json
cellular-clock-release-20261003/reproducibility/historical/source-manifests/baseline-source-manifest.json  ->  data/18-cell-clock-historical-source-manifests-baseline-source-manifest.json
cellular-clock-release-20261003/reproducibility/historical/source-manifests/cellular-clock-audit-manifest.json  ->  data/18-cell-clock-historical-source-manifests-cellular-clock-audit-manifest.json
cellular-clock-release-20261003/reproducibility/historical/source-manifests/cellular-clock-manifest.json  ->  data/18-cell-clock-historical-source-manifests-cellular-clock-manifest.json
cellular-clock-release-20261003/reproducibility/historical/source-manifests/optimized-source-manifest.json  ->  data/18-cell-clock-historical-source-manifests-optimized-source-manifest.json
cellular-clock-release-20261003/reproducibility/replay-receipt.json  ->  data/18-cell-clock-replay-receipt.json
cellular-clock-release-20261003/reproducibility/run_checks.py  ->  code/18-cell-clock-run_checks.py
cellular-clock-release-20261003/reproducibility/verify_pins.py  ->  code/18-cell-clock-verify_pins.py
cellular-clock-release-20261003/reproducibility/write_manifest.py  ->  code/18-cell-clock-write_manifest.py
```

`Exact_Lazy_Reversible_CA_Evaluator_Package.zip` (path inside the archive → shipped path):

```
lazy-evaluator-release-20261003/build.sh  ->  code/19-lazy-eval-build.sh
lazy-evaluator-release-20261003/release-integrity-receipt.json  ->  data/19-lazy-eval-release-integrity-receipt.json
lazy-evaluator-release-20261003/release_checks.py  ->  code/19-lazy-eval-release_checks.py
lazy-evaluator-release-20261003/replay.py  ->  code/19-lazy-eval-replay.py
lazy-evaluator-release-20261003/report19-qa.json  ->  data/19-lazy-eval-report19-qa.json
lazy-evaluator-release-20261003/reproducibility/PROOF.md  ->  19-lazy-eval-PROOF.md
lazy-evaluator-release-20261003/reproducibility/PROVENANCE.json  ->  data/19-lazy-eval-PROVENANCE.json
lazy-evaluator-release-20261003/reproducibility/RESULTS.md  ->  19-lazy-eval-RESULTS.md
lazy-evaluator-release-20261003/reproducibility/addendum_checks.py  ->  code/19-lazy-eval-addendum_checks.py
lazy-evaluator-release-20261003/reproducibility/audit-addendum.md  ->  19-lazy-eval-audit-addendum.md
lazy-evaluator-release-20261003/reproducibility/audit-design.md  ->  19-lazy-eval-audit-design.md
lazy-evaluator-release-20261003/reproducibility/audit_checks.py  ->  code/19-lazy-eval-audit_checks.py
lazy-evaluator-release-20261003/reproducibility/benchmark_universal.py  ->  code/19-lazy-eval-benchmark_universal.py
lazy-evaluator-release-20261003/reproducibility/check_startup_geometry.py  ->  code/19-lazy-eval-check_startup_geometry.py
lazy-evaluator-release-20261003/reproducibility/evidence/addendum-receipt-optimized.json  ->  data/19-lazy-eval-evidence-addendum-receipt-optimized.json
lazy-evaluator-release-20261003/reproducibility/evidence/addendum-receipt.json  ->  data/19-lazy-eval-evidence-addendum-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/audit-receipt-optimized.json  ->  data/19-lazy-eval-evidence-audit-receipt-optimized.json
lazy-evaluator-release-20261003/reproducibility/evidence/audit-receipt.json  ->  data/19-lazy-eval-evidence-audit-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/audit-universal-count.json  ->  data/19-lazy-eval-evidence-audit-universal-count.json
lazy-evaluator-release-20261003/reproducibility/evidence/test-optimized-receipt.json  ->  data/19-lazy-eval-evidence-test-optimized-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/test-receipt.json  ->  data/19-lazy-eval-evidence-test-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/universal-malformed-trace.json  ->  data/19-lazy-eval-evidence-universal-malformed-trace.json
lazy-evaluator-release-20261003/reproducibility/evidence/universal-optimized-receipt.json  ->  data/19-lazy-eval-evidence-universal-optimized-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/universal-receipt.json  ->  data/19-lazy-eval-evidence-universal-receipt.json
lazy-evaluator-release-20261003/reproducibility/evidence/universal-startup-trace.json  ->  data/19-lazy-eval-evidence-universal-startup-trace.json
lazy-evaluator-release-20261003/reproducibility/lazy_reversible.py  ->  code/19-lazy-eval-lazy_reversible.py
lazy-evaluator-release-20261003/reproducibility/package_checks.py  ->  code/19-lazy-eval-package_checks.py
lazy-evaluator-release-20261003/reproducibility/portable-replay/README.md  ->  19-lazy-eval-portable-replay-README.md
lazy-evaluator-release-20261003/reproducibility/portable-replay/replay-receipt.json  ->  data/19-lazy-eval-portable-replay-replay-receipt.json
lazy-evaluator-release-20261003/reproducibility/test_lazy.py  ->  code/19-lazy-eval-test_lazy.py
lazy-evaluator-release-20261003/verify_release.py  ->  code/19-lazy-eval-verify_release.py
lazy-evaluator-release-20261003/write_manifest.py  ->  code/19-lazy-eval-write_manifest.py
```


</details>
