# Quadratic Orthant Certificates

**Maximal parallelism, timed irreversible races, a fixed Waterfall universal machine, active membranes and reset Petri nets: Diophantine certificates of degree two (four for dynamic membranes), nonnegative on the real orthant, with negative and selection conditions**

This is a research report dated 2 October 2026, built from six manuscripts
of ProveIt's incoming reports: three of batch 78 (cluster H3), printed as
Parts I–III, and three of batch 79 (cluster J2), added the same day as
Parts IV–VI. All six are treated as AI-assisted research manuscripts. The
batch-78 sources are called *source 08*, *source 12* and *source 14* after
their batch-78 manuscript numbers, which are also the file prefixes of their
shipped programs and data. The batch-79 sources are called *source 15*,
*source 16* and *source 17* after their file prefixes, which continue this
report's own sequence. **Beware:** source 15 is batch-79 manuscript 08; it is
not source 08 (batch-78 manuscript 08, Part I).

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 08 (base) | batch 78, manuscript 08 | `Maximal_Parallel_Diophantine.zip` (`808b53ed8`); *Quadratic Certificates for Maximal Parallelism: Exact witnesses, sharp growth bounds, and a convexity obstruction*, main file `article.tex`, 25-page PDF; "Research manuscript prepared for Vladimir Reshetnikov", "Developed with ChatGPT" | `db3b377f0` (its search results also showed the older `4cccfa068`) | `41e7f1189` | Part I (Sections 2–16) and Appendices A–C |
| 12 | batch 78, manuscript 12 | `Total_Quadratic_Diophantine_Semantics.zip` (`808b53ed8`); *Total Quadratic Semantics for Irreversible Computation: Exclusive sites, timed self-assembly, and Horn closure without execution histories*, main file `article.tex`, 25-page PDF; "Research prepared for Vladimir Reshetnikov", "Developed with ChatGPT" | `db3b377f0` | `41e7f1189` | Part II (Sections 17–29) and Appendices D–E |
| 14 | batch 78, manuscript 14 | `Waterfall_Diophantine_Certificates.zip` (`24a743255`); *Quadratic Diophantine certificates for a fixed Waterfall universal machine*, main file `paper/waterfall-diophantine.tex` with `paper/affine-gap-table.tex`, 16-page PDF; "Research note prepared with AI assistance for private review" | none (the manuscript names no ProveIt commit) | `41e7f1189` | Part III (Sections 30–38) and Appendices F–G |
| 15 | batch 79, manuscript 08 | `Membrane_Motif_Research_Package.zip` (`2a8a39599`); *Exact Spatially Compressed Diophantine Certificates for Active Membrane Systems*, main file `article/membrane_motifs.tex`, 20-page PDF; "Research report with an exact arithmetic replay package" | none | `a7ae02511` | Part IV (Sections 39–49) and Appendices I–J |
| 16 | batch 79, manuscript 09 | `Universal_Membrane_Research_Package.zip` (`2a8a39599`); *Literal universal active membrane frontends and quadratic outcome certificates*, main file `article/membrane_frontend.tex`, 21-page PDF; "Research manuscript" | none | `a7ae02511` | Part V (Sections 50–62) and Appendix K |
| 17 | batch 79, manuscript 18 | `Reset_Petri_Net_Certificates.zip` (`aebfa386e`; corrected code edition `Reset_Petri_Net_Certificates_corrected.zip`, batch 80, manuscript 04, `4e270aa46`); *Reset Petri Nets and Canonical Quadratic Certificates*, main file `report/reset-net-certificates.tex`, 26-page PDF; "Research report and reproducible construction" | `44983ed7e` (an ancestor of this write, at which Parts I–III already existed; it cites the README of `canonical-diophantine-certificates`, not this report) | `a7ae02511`; corrected code `8a4e64732` | Part VI (Sections 63–77) and Appendices L–M |

Every result, proof, example, remark, research question and limitation of
the three batch-78 manuscripts is printed. They are not versions of one manuscript
and share no theorem (word 8-gram overlap between 08 and 12 is about 0.5 %,
all boilerplate); none cites another. What they share is one *format*: a
fixed finite system is compiled into one integer polynomial
`P = Σ A_i² + Σ B_j C_j` (affine `A_i`; affine `B_j, C_j` with nonnegative
coefficients), of total degree two, nonnegative on the whole real
nonnegative orthant, whose natural zeros are in bijection with the
semantic objects, and whose unsquared products encode a condition that
balance equations cannot: maximality of a parallel round (Part I), earliest
completion with label priority and certified absence (Part II), and the
strict-minimum events of a fixed Waterfall program compressed into exact
macrosteps (Part III). Section 1 of the article states this spine once,
places it at the level `D⁺₂ = SL` of the degree classification proved in
Part XI of
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates),
and gives tables of notions and letters.

The batch-79 sources extend the same spine. Source 16's outcome polynomials
and source 17's certificates have the form `Σ A² + Σ B·C` and prove more:
their products are strong selector gates, so for natural parameters every
zero over the real nonnegative orthant is natural. Source 15's certificate is
the deliberate exception: the sum of squares of quadratic residual
equations, of degree four, one polynomial per finite schema. Sources 15 and
16 are complementary (source 16 discharges the universal-frontend
obligations that source 15 lists) and share no theorem; both are printed in
full, with every result, proof, example, remark, question and limitation.
**Source 17
re-derives source 16's program layer without citing it**: the 528-row
program files are byte-identical, its source compiler is source 16's up to
one docstring word, its two proof notes are excerpts of source 16's (91 % and
98 % of their word 8-grams), and its Proposition 69.1 is source 16's
Theorem 60.1 for that program. That layer is printed once, in Part V. Four
duplicated passages of source 17 are replaced by marked pointers (the
transition table, the proof of its counter-macro lemma, the proof of
Proposition 69.1, and the macro descriptions and cost table of its
two-counter companion); everything else of source 17, and everything
specific to reset nets, is printed. Sources 16 and 17 use Part III's
universal machine (Neary–Woods `U15,2`) by a different route, through counter
programs instead of Iijil's Waterfall matrix; no theorem is shared.

**Status: AI-assisted, unrefereed, not formalized.** Priority is not
certified for any Part. Nothing in the report is formalized in Lean or
Rocq.

**Batch 80 (corrected code edition of source 17).** A corrected edition of
source 17's archive, `Reset_Petri_Net_Certificates_corrected.zip`
(3,632,338 bytes, SHA-256 `8d5b9b1a…486d3`; arrival `4e270aa46`, batch 80,
manuscript 04; the archive dates its correction 3 October 2026), repairs
the two input-boundary defects found by the research programme's review
(see "Reviews and patches"). It was placed by `8a4e64732` (batch 80,
cluster K1): four placed files were replaced by their corrected bytes under
the same names (`code/17-reset-net-build_net.py`,
`code/17-reset-net-peak_quadratic.py`, `code/17-reset-net-run-checks.sh`,
`data/17-reset-net-checks-PADDING_AND_GENERIC_PEAK_RESULTS.json`; the
originals remain in `a7ae02511` and `aebfa386e`) and three were added
(`17-reset-net-CORRECTION.md`, `code/17-reset-net-checks-audit_exact_domains.py`,
`data/17-reset-net-checks-EXACT_DOMAIN_RESULTS.json`). Its manuscript
source and PDF are byte-identical to the batch-79 delivery, so no printed
statement, proof, count or label changes; nets, schemas, witnesses,
formulas and counts are unchanged. Part VI records it in a dated note in
Section 76 (`qoc:rn:sec:reproduce`).

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 170 pages (unnumbered title page, then pages 1–169)
README.md                                            this guide
08-maximal-parallel-PROOF_AUDIT.md                   source 08's proof and scope audit, as delivered
08-maximal-parallel-SOURCE_AUDIT.md                  source 08's source audit (repository pin, literature), as delivered
12-total-quadratic-SOURCE_AUDIT.md                   source 12's source audit and claim boundary, as delivered
14-waterfall-LICENSE-PROVENANCE.md                   source 14's licence and provenance statement, as delivered
14-waterfall-SOURCE-PROVENANCE.md                    source 14's provenance of the machine data and primary paper, as delivered
15-membrane-motifs-RELEASE_NOTES.md                  source 15's release notes: proved claims and finite replay coverage, as delivered
16-universal-membrane-direct-PROOF.md                source 16's proof notes for the affine (direct) frontend, as delivered
16-universal-membrane-packet-PROOF.md                source 16's proof notes for the prime (packet) frontend, as delivered
17-reset-net-CORRECTION.md                           source 17's corrected edition: exact-domain repair of two programs, scope and evidence, as delivered (batch 80)
17-reset-net-VALIDATION.md                           source 17's verification-scope statement, as delivered
code/08-maximal-parallel-parallel_certificates.py    source 08's exact-integer compiler, evaluator, canonical witnesses, rank and counting routines
code/08-maximal-parallel-verify.py                   source 08's deterministic validation (imports parallel_certificates)
code/12-total-quadratic-build.sh                     source 12's three-pass pdflatex script (delivered layout; see below)
code/12-total-quadratic-quadratic_compiler.py        source 12's event simulator, total and Horn compilers, witness constructor, exporter
code/12-total-quadratic-test_compiler.py             source 12's exhaustive small-instance and regression tests (imports quadratic_compiler)
code/12-total-quadratic-verify_exports.py            source 12's independent re-expansion of the exported polynomials
code/14-waterfall-build.sh                           source 14's PDF build script (delivered layout; see below)
code/14-waterfall-run-replay.sh                      source 14's one-command replay of the eight programs below
code/14-waterfall-verify_matrix_definition.py        rebuilds the compact matrix definition and checks all 2,116 entries
code/14-waterfall-verify_frontend.py                 the 58 macrosteps by 43,065 affine strict-minimum inequalities (64 forms)
code/14-waterfall-verify_frontend_independent.py     the same macrosteps by a second loop parameterization, plus concrete runs
code/14-waterfall-grouped_quadratic.py               builds the 35k-witness quadratic and evaluates the seven-step fixture
code/14-waterfall-verify_quadratic_independent.py    independent formula evaluation from the source machine table
code/14-waterfall-verify_halting_example.py          direct event and countdown simulation of the seven-step example
code/14-waterfall-verify_certificates.py             the common-column class, ledgers and counterexamples
code/14-waterfall-verify_release.py                  cross-checks the receipts and the exported polynomial at its fixture
code/15-membrane-motifs-export_sos.py                expands the contextual-copy example into its quartic sum of squares
code/15-membrane-motifs-focused_tests.py             old-topology, normalization, anti-sharing and ledger checks
code/15-membrane-motifs-motif_compiler.py            exact sparse residual compiler and expanded operational oracle
code/15-membrane-motifs-regression_extensions.py     cascaded dissolution, domain and duplicate-index counterexamples, population identity
code/15-membrane-motifs-replay_tests.py              the exhaustive candidate-plan suite (several minutes)
code/15-membrane-motifs-run_all.py                   ordered complete replay; rewrites the receipts and transcripts
code/15-membrane-motifs-verify_saved_examples.py     short replay of the saved schemas and witnesses, ledgers and coefficient bounds
code/16-universal-membrane-build_pdf.sh              source 16's PDF build script (delivered layout; see below)
code/16-universal-membrane-direct-build_direct.py    builds the affine frontend: 528-row program and 2,544 membrane rules
code/16-universal-membrane-direct-build_quadratic.py  compiles the affine-frontend outcome polynomial at a given horizon
code/16-universal-membrane-direct-load_input.py      structural loader for half tapes (L,R)
code/16-universal-membrane-direct-make_accepting_witness.py  builds the sparse T=328 accepting witness for (6,0)
code/16-universal-membrane-direct-quadratic_core.py  the generic d-counter outcome-polynomial compiler
code/16-universal-membrane-direct-verify_accepting_quadratic.py  evaluates every term of the T=328 accepting certificate
code/16-universal-membrane-direct-verify_direct.py   symbolic and concrete checks of the 528-row program
code/16-universal-membrane-direct-verify_membrane.py  replays the complete 1,013-step membrane run
code/16-universal-membrane-packet-build_frontend.py  builds the prime frontend (writes four of the excluded files)
code/16-universal-membrane-packet-load_input.py      structural loader for a raw input a, or half tapes via 2^L 3^R
code/16-universal-membrane-packet-quadratic_outcome.py  prime-frontend polynomial generator and evaluator (writes two excluded files)
code/16-universal-membrane-packet-replay_example.py  source-cut replay and exact macro-cost summation for a=64
code/16-universal-membrane-packet-verify_density.py  finite exact density calculations and certified lower bounds
code/16-universal-membrane-packet-verify_frontend.py  symbolic and concrete counter checks of the 8,408-row program
code/16-universal-membrane-packet-verify_membrane.py  maximal-allocation membrane checks on representative gadgets
code/16-universal-membrane-packet-verify_quadratic.py  independent checks of the prime-frontend polynomial
code/16-universal-membrane-reproduce.py              source 16's complete rerun with byte comparison (needs the arrival archive)
code/17-reset-net-budget-audit-audit_budget.py       independent reconstruction of the net specification
code/17-reset-net-build-pdf.sh                       source 17's PDF build script (delivered layout; see below)
code/17-reset-net-build_net.py                       builds the 539-place reset net and its ledger (batch-80 corrected edition: exact markings in fire)
code/17-reset-net-checks-audit.py                    JSON-only structural and arithmetic checker
code/17-reset-net-checks-audit_generated_families.py  generated-family coefficient checker
code/17-reset-net-checks-audit_exact_domains.py      exact-domain regression (batch 80): 64 rejected calls, 9 schema hashes, 388 firings; also under -O
code/17-reset-net-checks-audit_padding_and_generic_peak.py  padding and generic-peak checks
code/17-reset-net-peak_quadratic.py                  local peak recurrence and duration extensions of the certificate (batch-80 corrected edition: Boolean flags)
code/17-reset-net-replay_and_verify.py               main replay: traces, witnesses, every quadratic term (about 1-2 minutes)
code/17-reset-net-reset_quadratic.py                 generic reset-trace compiler with the checked control projection
code/17-reset-net-run-checks.sh                      the fourteen checks, then the exact-domain regression twice (normal, -O) (batch-80 corrected edition; hard-codes python3)
code/17-reset-net-shared-checks-audit_prime_macros.py  checks the 328 prime-macro summaries for a=64
code/17-reset-net-shared-checks-audit_shared.py      transition-by-transition checks of both shared-arc nets (over 3 minutes)
code/17-reset-net-shared-reset-arcs-build_shared.py  builds the shared-reset-arc nets (writes four excluded files)
code/17-reset-net-source_quadratic.py                source affine-branch compiler (source 16's quadratic_core.py up to one docstring word)
code/17-reset-net-two-counter-build_variant.py       builds the two-counter companion net (writes three excluded files)
code/17-reset-net-two-counter-verify_source.py       checks the 8,408-row prime-coded source
code/17-reset-net-two-reset-audit-audit_two_reset.py  separately generated two-counter net (writes one excluded file)
code/17-reset-net-two-reset-audit-compare_release_net.py  incidence-preserving comparison of the two-counter nets
code/17-reset-net-verify_source.py                   checks the serialization, the 528 rows and the macro bodies
data/08-maximal-parallel-example_certificate.json    structured and expanded quadratic for A+B→C, A→B, with one witness
data/08-maximal-parallel-verification.txt            source 08's recorded validation run (Python 3.13.5; all PASS)
data/08-maximal-parallel-verification_counts.json    the same counts as JSON
data/12-total-quadratic-huge_delay_chain.json        exported polynomial: four rules with delays near 10^30 (45 witnesses)
data/12-total-quadratic-literal_four_tile_example.json  exported polynomial: the literal four-tile catalogue (58 witnesses)
data/12-total-quadratic-locking_counterexample.json  exported polynomial: the reduced locking example (29 witnesses)
data/12-total-quadratic-timed_race.json              exported polynomial: timed race and blocked cycle (85 witnesses)
data/12-total-quadratic-test_receipt.json            source 12's recorded test run (PASS; seed 20261002)
data/12-total-quadratic-export_verification.json     source 12's recorded export verification (4/4 PASS)
data/14-waterfall-UniversalTM15x2.tm.txt             Iijil's source transition table (third-party data, NOT MIT-0)
data/14-waterfall-UniversalTM15x2.twm.txt            Iijil's 46-clock Waterfall matrix serialization (third-party data, NOT MIT-0)
data/14-waterfall-affine-gap-forms.json              the 64 affine gap forms with activation bounds and multiplicities
data/14-waterfall-frontend-receipt.json              receipt of verify_frontend
data/14-waterfall-grouped-quadratic7-certificate.json  all residuals and product factors of the seven-step quadratic
data/14-waterfall-grouped-quadratic7-fixture.json    its 245 natural witnesses and four parameters
data/14-waterfall-grouped-quadratic-receipt.json     receipt of grouped_quadratic
data/14-waterfall-certificate-receipt.json           receipt of verify_certificates
data/14-waterfall-unit-ledgers.json                  the literal 22/26-operation ledgers of the three-clock instance
data/14-waterfall-matrix-definition.json             receipt of verify_matrix_definition
data/14-waterfall-independent-receipt.json           receipt of verify_frontend_independent
data/14-waterfall-quadratic-independent.json         receipt of verify_quadratic_independent
data/14-waterfall-halting-example.json               the full event and timestamp trace of the seven-step example
data/14-waterfall-release-verification.json          receipt of verify_release (PASS)
data/15-membrane-motifs-contextual_copy_polynomials.json  129 named sparse residuals and the 86-coordinate witness
data/15-membrane-motifs-contextual_copy_quartic.json  their expanded quartic: 282 monomials, coefficient height 19
data/15-membrane-motifs-examples.json                saved schemas, rule arrays, natural witnesses and ledgers (708,035 bytes)
data/15-membrane-motifs-focused_receipt.json         receipt of focused_tests
data/15-membrane-motifs-quartic_receipt.json         receipt of export_sos
data/15-membrane-motifs-regression_extensions_receipt.json  receipt of regression_extensions
data/15-membrane-motifs-regression_extensions_stdout.txt  transcript of regression_extensions
data/15-membrane-motifs-replay_receipt.json          receipt of replay_tests
data/15-membrane-motifs-replay_tests_stdout.txt      transcript of replay_tests
data/15-membrane-motifs-run_receipt.json             receipt of run_all, with runtime metadata and file hashes
data/15-membrane-motifs-saved_example_receipt.json   receipt of verify_saved_examples
data/15-membrane-motifs-source-provenance.json       primary-source URLs and hashes
data/15-membrane-motifs-verify_saved_examples_stdout.txt  transcript of verify_saved_examples
data/16-universal-membrane-SOURCE_PROVENANCE.json    public source URLs and pinned digests
data/16-universal-membrane-direct-SOURCE_PROVENANCE.json  provenance of the direct packet
data/16-universal-membrane-direct-accepting_counter_trace.json  the 328-instruction accepting counter trace for (6,0)
data/16-universal-membrane-direct-accepting_example.json  the (6,0) example summary
data/16-universal-membrane-direct-accepting_membrane_trace.json  the 1,013-step membrane trace (602,183 bytes)
data/16-universal-membrane-direct-accepting_quadratic_receipt.json  receipt of verify_accepting_quadratic
data/16-universal-membrane-direct-accepting_quadratic_witness.json  the sparse T=328 accepting witness (922 nonzero of 922,008)
data/16-universal-membrane-direct-frontend_metadata.json  labels, counts and input contract of the affine frontend
data/16-universal-membrane-direct-input6_0.json      loader output for (6,0)
data/16-universal-membrane-direct-macro_certificates.json  macro-to-control-graph correspondence of the 528-row program
data/16-universal-membrane-direct-membrane_rules.jsonl  all 2,544 affine-frontend membrane rules
data/16-universal-membrane-direct-membrane_verification_receipt.json  receipt of direct verify_membrane
data/16-universal-membrane-direct-object_alphabet.txt  the 1,296-symbol alphabet
data/16-universal-membrane-direct-quadratic_schema_T1.json  the affine-frontend polynomial at T=1
data/16-universal-membrane-direct-register_verification_receipt.json  receipt of verify_direct
data/16-universal-membrane-direct-semantic_branches.json  the 761 semantic branches
data/16-universal-membrane-direct-virtual3.txt       the 528-row program as text
data/16-universal-membrane-document_checks.json      receipt of source 16's PDF layout checks
data/16-universal-membrane-packet-SOURCE_PROVENANCE.json  provenance of the prime packet
data/16-universal-membrane-packet-accepting_example.json  the a=64 example summary (no final newline, as delivered)
data/16-universal-membrane-packet-density_lower_bounds.json  exact rational lower bounds for the density
data/16-universal-membrane-packet-frontend_metadata.json  labels, counts and input contract of the prime frontend
data/16-universal-membrane-packet-input64.json       loader output for a=64
data/16-universal-membrane-packet-macro_certificates.json  macro correspondence of the 8,408-row program
data/16-universal-membrane-packet-membrane_verification_receipt.json  receipt of packet verify_membrane
data/16-universal-membrane-packet-quadratic_small_fixtures.json  small fully expanded polynomial fixtures
data/16-universal-membrane-packet-quadratic_verification_receipt.json  receipt of verify_quadratic
data/16-universal-membrane-packet-verification_receipt.json  receipt of verify_frontend
data/16-universal-membrane-packet-virtual3.txt       the 528-row program as text (packet copy, different bytes)
data/16-universal-membrane-reproduction.json         receipt of reproduce.py
data/16-universal-membrane-tm_table.json             the parsed 15-state source table (shared by both packets and by source 17)
data/16-universal-membrane-virtual3.json             the 528-row three-counter program (shared by both packets and by source 17)
data/17-reset-net-SOURCE_PROVENANCE.json             source attribution and digests
data/17-reset-net-accepting_all_duration_witness_N390.json  natural padding fixture at N=390
data/17-reset-net-accepting_peak_trace.json          per-step masses and peak coordinates of the (6,0) run
data/17-reset-net-accepting_peak_witness.json        sparse canonical witness at h=328, N=388
data/17-reset-net-accepting_reset_trace.json         all 388 labelled firings with markings
data/17-reset-net-accepting_reset_witness.json       sparse projected-trace witness at N=388
data/17-reset-net-budget-audit-audit_results.json    receipt of audit_budget
data/17-reset-net-budget-audit-shortest_accepting_word.json  the shortest accepting word
data/17-reset-net-checks-AUDIT_RESULTS.json          receipt of checks/audit
data/17-reset-net-checks-EXACT_DOMAIN_RESULTS.json   the two printed runs of audit_exact_domains, normal and -O (both PASS; batch 80)
data/17-reset-net-checks-GENERATED_FAMILIES_RESULTS.json  receipt of audit_generated_families
data/17-reset-net-checks-PADDING_AND_GENERIC_PEAK_RESULTS.json  receipt of audit_padding_and_generic_peak (batch 80: two source hashes refreshed)
data/17-reset-net-checks-PORTABILITY_RESULTS.json    receipt of relocation checks of the JSON-only checker
data/17-reset-net-net_ledger.json                    literal graph counts and degrees of the 539-place net
data/17-reset-net-reset_net.json                     every place and arc of the 539-place net
data/17-reset-net-shared-checks-audit_receipt.json   receipt of audit_shared (PASS, as delivered)
data/17-reset-net-shared-checks-independent_A64_macro_trace.json  independent a=64 macro trace
data/17-reset-net-shared-checks-prime_macro_receipt.json  receipt of audit_prime_macros
data/17-reset-net-shared-reset-arcs-three-counter-accepting_peak_witness_N446.json  canonical witness of the shared net at N=446
data/17-reset-net-shared-reset-arcs-three-counter-accepting_reset_trace_N446.json  all 446 firings of the shared run
data/17-reset-net-shared-reset-arcs-three-counter-net_ledger.json  ledger of the shared three-counter net
data/17-reset-net-shared-reset-arcs-two-counter-accepting_macro_count_A64.json  shared two-counter duration for a=64
data/17-reset-net-shared-reset-arcs-two-counter-net_ledger.json  ledger of the shared two-counter net
data/17-reset-net-shared-reset-arcs-verification_receipt.json  receipt of build_shared
data/17-reset-net-source_verification_receipt.json   receipt of verify_source
data/17-reset-net-two-counter-net_ledger.json        ledger of the two-counter companion net
data/17-reset-net-two-counter-source-accepting_example.json  the a=64 example of the companion
data/17-reset-net-two-counter-source_verification_receipt.json  receipt of two-counter verify_source
data/17-reset-net-two-reset-audit-accepting_macro_trace.json  macro trace of the separately generated net
data/17-reset-net-two-reset-audit-audit_receipt.json  receipt of audit_two_reset (hashes an unshipped proof note)
data/17-reset-net-two-reset-audit-release_comparison_receipt.json  receipt of compare_release_net
data/17-reset-net-verification_receipt.json          receipt of replay_and_verify
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery; for source 17 the delivery is, since
batch 80, the corrected code edition (the 47 files of source 17 not
replaced or added then are byte-identical in both editions). Delivered name → shipped name:

- Source 08 (inner directory `Maximal_Parallel_Diophantine/`):
  `code/*.py` → `code/08-maximal-parallel-*.py`; `data/*` →
  `data/08-maximal-parallel-*`; `PROOF_AUDIT.md`, `SOURCE_AUDIT.md` →
  `08-maximal-parallel-*.md`. Its `article.tex` was placed as this report's
  `article.tex` and is now Part I of the merged text; its `README.md` was
  placed as this README and is replaced by it.
- Source 12 (inner directory `total_quadratic_semantics/`): `code/*.py`
  and `build.sh` → `code/12-total-quadratic-*`; `results/*.json` →
  `data/12-total-quadratic-*.json`; `SOURCE_AUDIT.md` →
  `12-total-quadratic-SOURCE_AUDIT.md`.
- Source 14 (inner directory `waterfall-diophantine/`): `replay/*.py`,
  `run-replay.sh`, `build.sh` → `code/14-waterfall-*`; `replay/*.json` and
  `receipts/*.json` → `data/14-waterfall-*.json`; `source/*` →
  `data/14-waterfall-UniversalTM15x2.*`; `LICENSE-PROVENANCE.md`,
  `SOURCE-PROVENANCE.md` → `14-waterfall-*.md`.
- Source 15 (inner directory `membrane-motif-release/`): `replay/*.py` →
  `code/15-membrane-motifs-*.py`; the other files of `replay/` →
  `data/15-membrane-motifs-*`; `provenance/source-provenance.json` →
  `data/15-membrane-motifs-source-provenance.json`; `RELEASE_NOTES.md` →
  `15-membrane-motifs-RELEASE_NOTES.md`.
- Source 16 (inner directory `literal-membrane-release/`): `direct/X` →
  `…-direct-X` and `packet/X` → `…-packet-X` (programs in `code/`, everything
  else in `data/`); `direct/PROOF.md`, `packet/PROOF.md` →
  `16-universal-membrane-{direct,packet}-PROOF.md`; `reproduce.py`,
  `build_pdf.sh` → `code/16-universal-membrane-*`; `SOURCE_PROVENANCE.json`
  and `receipts/*.json` → `data/16-universal-membrane-*`. The byte-identical
  pairs `{direct,packet}/tm_table.json` and `{direct,packet}/virtual3.json`
  are shipped once, as `data/16-universal-membrane-tm_table.json` and
  `data/16-universal-membrane-virtual3.json`; the two `virtual3.txt` differ
  and are both shipped.
- Source 17 (inner directory `reset-net-release/`): root programs →
  `code/17-reset-net-*`, root data → `data/17-reset-net-*`, `VALIDATION.md`
  → `17-reset-net-VALIDATION.md`, the corrected edition's `CORRECTION.md` →
  `17-reset-net-CORRECTION.md`; files in sub-directories carry the
  sub-directory in the prefix (`two-counter/build_variant.py` →
  `code/17-reset-net-two-counter-build_variant.py`,
  `shared-reset-arcs/three-counter/net_ledger.json` →
  `data/17-reset-net-shared-reset-arcs-three-counter-net_ledger.json`,
  `two-counter/source/accepting_example.json` →
  `data/17-reset-net-two-counter-source-accepting_example.json`; the
  corrected edition's `checks/audit_exact_domains.py` and
  `checks/EXACT_DOMAIN_RESULTS.json` →
  `code/17-reset-net-checks-audit_exact_domains.py` and
  `data/17-reset-net-checks-EXACT_DOMAIN_RESULTS.json`). Source
  17's copies of source 16's files are shipped once, under source 16's names:
  `source/{tm_table.json, virtual3.json, virtual3.txt, macro_certificates.json,
  accepting_counter_trace.json}` are `data/16-universal-membrane-{tm_table.json,
  virtual3.json, direct-virtual3.txt, direct-macro_certificates.json,
  direct-accepting_counter_trace.json}`, and `two-counter/source/{tm_table.json,
  virtual3.json, virtual3.txt, macro_certificates.json}` are
  `data/16-universal-membrane-{tm_table.json, virtual3.json, packet-virtual3.txt,
  packet-macro_certificates.json}`.

Not shipped: the three PDFs; the manuscripts of sources 12 and 14 (printed
as Parts II and III; source 14's `paper/affine-gap-table.tex` is printed
as Appendix G and carries the same 64 forms as
`data/14-waterfall-affine-gap-forms.json`); the READMEs of sources 12 and
14; and the checksum ledgers of sources 08 (`SHA256SUMS.txt`, 10 of 10
verified at placement) and 14 (`SHA256SUMS`, 30 of 30). Source 12 shipped
no ledger. Nothing of sources 08, 12 and 14 was excluded as heavy (their
largest shipped file is 127,417 bytes).

Not shipped from sources 15–17: the three PDFs and manuscripts (printed as
Parts IV–VI); the delivered READMEs (source 15: one; 16: three; 17: three);
the checksum ledgers, all verified at placement (source 15 `SHA256SUMS`
26/26 and `MANIFEST.json` 26/26; 16 `MANIFEST.json` 71/71,
`direct/MANIFEST.json` 30/30, `packet/MANIFEST.json` 31/31; 17 `SHA256SUMS`
83/83, with its checker `verify-manifest.py`, and the corrected edition's
refreshed `SHA256SUMS` 86/86 at the batch-80 placement); the corrected
edition's delivery `README.md` (with a correction notice); source 15's two transcripts
`replay/export_sos_stdout.txt` and `replay/focused_tests_stdout.txt`
(byte-identical to the shipped quartic and focused receipts); source 16's two
identical copies of `WATERFALL-FRONTEND-PROOF.md`, an earlier draft of the
Waterfall frontend printed as Part III (its only content not in Part III is
a 34k-witness degree-four baseline, superseded by Part III's 35k quadratic);
source 17's two excerpt proof notes `source/SOURCE_REGISTER_PROOF.md` and
`two-counter/source/PROOF.md` and its copies of source 16's program files
(above); the four copies of Iijil's `UniversalTM15x2.tm.txt` in sources 16
and 17 (third-party, the same bytes as `data/14-waterfall-UniversalTM15x2.tm.txt`;
see "Licensing"); and seventeen heavy regenerable files of sources 16 and 17
(63,245,978 bytes; see "Reconstructing the excluded data"). The two largest
shipped files of the batch, `data/15-membrane-motifs-examples.json`
(708,035 bytes) and `data/16-universal-membrane-direct-accepting_membrane_trace.json`
(602,183 bytes), are single artifacts under 1 MB and were staged.

All of it survives in the arrival commits:

```sh
git show 808b53ed8:docs/incoming/Maximal_Parallel_Diophantine.zip > mpd.zip
git show 808b53ed8:docs/incoming/Total_Quadratic_Diophantine_Semantics.zip > tqs.zip
git show 24a743255:docs/incoming/Waterfall_Diophantine_Certificates.zip > wdc.zip
git show 2a8a39599:docs/incoming/Membrane_Motif_Research_Package.zip > mm.zip
git show 2a8a39599:docs/incoming/Universal_Membrane_Research_Package.zip > um.zip
git show aebfa386e:docs/incoming/Reset_Petri_Net_Certificates.zip > rn-original.zip   # source 17, original edition
git show 4e270aa46:docs/incoming/Reset_Petri_Net_Certificates_corrected.zip > rn.zip   # source 17, corrected edition (preferred)
```

Both editions of source 17 are complete layouts, including the heavy
files; the corrected one (batch 80) matches the shipped programs. The
commands below that name `rn.zip` work with either.

## Labels and numbering

Every label carries the prefix `qoc:`. Source 08's 73 labels are
`qoc:mp:` plus their delivered names, source 12's 40 are `qoc:ts:` plus
theirs, and source 14's 54 are `qoc:wf:` plus theirs; no source label was
dropped or renamed apart from the prefix. The batch-78 merge added 22 labels,
189 in all: fifteen of the front section, the three Parts and the provenance
appendix (`qoc:sec:front`, `qoc:sec:parts`, `qoc:sec:spine`,
`qoc:eq:spine`, `qoc:sec:conventions`, `qoc:tab:notions`,
`qoc:tab:letters`, `qoc:sec:gadgets`, `qoc:sec:reproofs`,
`qoc:sec:relation`, `qoc:sec:status`, `qoc:part:mp`, `qoc:part:ts`,
`qoc:part:wf`, `qoc:app:provenance`); six on unlabelled sections of
source 12 (`qoc:ts:sec:intro`, `qoc:ts:sec:selfassembly`,
`qoc:ts:sec:boundary`, `qoc:ts:sec:impl`, `qoc:ts:sec:future`,
`qoc:ts:app:ledger`); and `qoc:wf:sec:results` on source 14's first
section. The CDC report already uses the sub-prefix `cdc:wf:` (its
manuscript 04); it is unrelated to `qoc:wf:`. Bibliography keys carry
`mp:`, `ts:` or `wf:`; the credits added in the merge carry `w:`.

The batch-79 write added 118 labels, 307 in all: source 15's 37 delivered
labels as `qoc:mm:` plus their delivered names, source 16's 35 as `qoc:um:`,
source 17's 34 as `qoc:rn:`, and twelve new ones (`qoc:mm:part`,
`qoc:um:part`, `qoc:rn:part`, `qoc:mm:sec:intro`, `qoc:mm:sec:conclusion`,
`qoc:mm:app:ledgers`, `qoc:mm:app:provenance79`, `qoc:um:sec:intro`,
`qoc:um:sec:sources`, `qoc:um:sec:future`, `qoc:um:app:artifacts`,
`qoc:rn:app:compiler`). None of the 189 earlier labels was renamed or
removed, and every one of them still prints the same number (compared in the
`.aux` files of the committed and the new build). Bibliography keys of the
new Parts carry `mm:`, `um:` or `rn:`. The batch-79 reciprocal notes
(cluster J2) and the batch-80 reciprocal note (cluster K2) added no label;
the report still has 307, and no label's number changed (compared in the
`.aux`).

Each Part keeps its source's numbering by section: source 08's Section *n*
is Section *n* + 1 (Sections 2–16), source 12's is *n* + 16 (Sections
17–29) and source 14's is *n* + 29 (Sections 30–38); Theorem *n.m*
shifts the same way. Source 08's appendices A–C keep their letters, source
12's A–B are D–E, source 14's A–B are F–G, and Appendix H is the
provenance. Text written in the merge is marked `[write]`; text without a
marker is the source's own.

Parts IV–VI continue the section numbering: source 15's Section *n* is
Section *n* + 38 (Sections 39–49), source 16's is *n* + 49 (Sections 50–62)
and source 17's is *n* + 62 (Sections 63–77), with theorems shifted the same
way. Inside Parts IV–VI, equations, tables and figures are numbered within
sections (for example Table 60.2), and the global counters are restored
after Part VI, so that no number of Parts I–III or Appendices A–H moved.
Their appendices are Appendices I–J (source 15's A–B), K (source 16's A) and
L–M (source 17's A–B), after the provenance appendix H, which gained
Appendix H.1 for the batch-79 provenance.

## Setting and notation

No symbol is renamed and no normalization changed; each letter keeps its
source's meaning inside its Part. Table 2 of the article lists the letters
the Parts use differently, among them `H` (Part I: species–threshold
pairs, a Hessian, an undecidable set; Part III: residuals and an input),
`M` (Part I: largest coefficient; Part II: the sentinel `S+1`; Part III:
the Waterfall matrix), `D` (retention diagonal / number of prerequisite
literals / direction), `L, R` (affine form / incidences and rules / half
tapes), `B`, `C`, `Q`, `q`, `T`, `W`, `τ`. Table 1 lists the words to read
carefully:

- **maximal** (Part I) is "no feasible one-copy extension", not maximum
  cardinality, and not CDC Part II's maximal commutation or Part XII's
  maximal repetition;
- **flat** (Part I) is flat maximality, unrelated to CDC's flat schemes;
- **rank** (Part I) is the cover rank `ρ(A)`, not CDC Part XI's
  first-arrival ranks or Part XIV's rank function;
- **history-free** (Part II) is CDC Part XIV's sense (outcome instead of
  history), not the sense of *Groups as Diophantine substrates*;
- **single-fold** (Parts II, III) is relative to a fixed catalogue or a
  fixed horizon, not the single-fold problem for all c.e. sets;
- **phase** (Part II) is a timing region; **clock** (Part III) is a
  Waterfall counter, not a computable clock of `liveness-beyond-halting`.

For Parts IV–VI, an unnumbered table after Table 2 lists their letters
(among them `T`: Part V's horizon in counter instructions but Part VI's
scratch counter; `h`: Part V's halt code but Part VI's source-instruction
horizon; `K`: Part IV's number of catalogue entries, Part V's scratch
register, Part VI's minimum fuel; `M`, `N`, `B`, `H`, `Z`), and Table 1
gains rows for **reset** (a Petri-net reset arc, unrelated to the research
programme's "two-reset mortality" matrices), **motif, schema**, **budget,
fuel**, **outcome, trace**, **division**, **boundary** and **source n**.
Source macros that clashed with the report's were renamed without changing
their output (`\zero` of source 15 to `\mmzero`; `\code` and `\ind` of
source 17 to `\rncode` and `\rnind`), and source 15's `\file` is set like
source 16's (`\nolinkurl` instead of `\texttt{\detokenize}`).

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 08).** One maximal parallel multiset-rewriting round as
  a quadratic nonnegative on the real orthant with `d+2m+4H` natural
  auxiliaries (extents included), `2d+2H+m` affine squares and `2H`
  products, zeros in bijection with maximal extents; histories with
  `T(2d+2m+4H)` and exact first halting with `T(2d+2m+4H+1)+4H+m`
  witnesses; guarded, flat (`d+3m+4H`), retaining and fixed-membrane
  variants and a guarded register-machine embedding; the uniform bound
  `O((1+|x|₁)^(m−ρ(A)))` on maximal extents, attained for every `A` along
  an integral ray; eventual quasipolynomiality of fixed-horizon counts with
  degree at most `T(m−ρ(A))`, sharp across systems; a parsimonious
  graph-to-network reduction and `#P`-completeness under Turing
  reductions; no convex quadratic for the deadlock of `A+B→C`; and a
  program-uniform quartic with degree four necessary in the orthant class.
- **Part II (source 12).** A unique capped causal fixed point for
  exclusive-site systems with positive integer delays; one quadratic per
  catalogue with exactly one natural zero for every delay vector, with
  exactly `m(2q+3)+3D+3(L+R₀)+R` witnesses; height and sparsity bounds;
  the Horn compiler with `m+3(L+R₀)+R`; the `37m`/`38m` fixed-candidate tile
  allocation; the four-tile locking counterexample; compatible-box
  uniqueness; the finite polyhedral timing decomposition, the `2^m`
  explicit-outcome lower bound and unbounded nonmonotone timing; an exact
  positive Horn simulation of Turing machines; and the permanent-absence
  obstruction with no computable grounding bound.
- **Part III (source 14).** The exact macrostep word and count
  `c = 6+3Q+r+3Y` of Iijil's fixed 46-clock Waterfall program on every
  input, proved by a finite affine certificate; the halt time
  `τ = 1+2C+7k`; the quadratic `F_k` with `35k` natural witnesses, `5k+4`
  squares and `2k` products whose fibre is empty or a singleton; the
  seven-step example (`C = 189`, `τ = 428`, 245 witnesses); semilinearity
  at fixed `k`; the decidable common-column class with a horizon-free
  `4n`-witness certificate; and the endpoint-count counterexample.
- **Part IV (source 15).** For polarizationless, noncooperative active
  membranes with evolution, communication, dissolution and weak division:
  soundness of every natural zero for every well-formed finite acyclic
  schema and existential consistent-schema completeness for one maximally
  parallel step; exact inclusion maximality by one linear residual per
  parent; uniqueness of the derived coordinates; the exact ledger
  `V = dK+A+E+B+3dJ+KJ`, `R = (3d+2K)J+(d+K)L+Z`; residual degree two,
  sum-of-squares degree four and a coefficient-height bound; one 18-variable,
  30-residual schema doubling any population; the nested-division family
  (`V = 2D²+11D+5`, `R = 8D²+15D+7`); the exact next-population identity
  with the sharp bound `2^n − 1`; and a four-rule system with `2^T` distinct
  payloads defeating identical-subtree sharing.
- **Part V (source 16).** Two literal frontends for the Neary–Woods machine:
  affine (528 three-counter instructions, 2,544 rules, 1,296 symbols, five
  labels) and prime (8,408 two-counter instructions, 34,605 rules, 19,162
  symbols, four labels), accepting by existence of a globally halting run,
  both c.e.-complete; exact macro costs; the density of the prime language,
  transcendental, of Turing degree `0′`, with an explicit `O(log² N)`
  counting remainder and zero effective dimensions; and the generic outcome
  polynomial with `((d+1)B₀−S₀)T` witnesses, `(d+2)T+1` squares and `B₀T`
  products (`2,811T`, `5T+1`, `761T` and `29,904T`, `4T+1`, `10,748T`), whose
  fibres are empty or singletons over the naturals and over the nonnegative
  reals.
- **Part VI (source 17).** A unit-weight reset net with 539 places, 771
  transitions, 2,608 ordinary arcs and 233 reset arcs from three places, with
  c.e.-complete exact-target reachability; the all-run debt identity; the
  exact fuel threshold `K = M − B`; exactly one accepting word at each length
  of `N_min + 2ℕ`, `N_min = h+H+2M−B+5`; the canonical certificate with
  `2813h` witnesses, `6h+2` squares and `762h` products, natural over the
  nonnegative reals; the real-parity obstruction for padding; the generic
  reset-trace bijection with `(d+1)mN` witnesses; the one-resettable-place
  reduction to one inhibitor arc; the prime-coded companion with its
  physical-peak theorem; and shared reset arcs (three and two).

Several statements re-prove or generalize results of
`canonical-diophantine-certificates` Part XI, which sources 08 and 12 knew
only through its README and source 14 not at all. They are printed as
second routes, with `[write]` notes and the table of Section 1.5, and no
novelty is claimed for them: source 08's Lemma 12.1 (cubic semilinearity),
Corollary 12.2, Proposition 13.1, its MRDP-to-quartic paragraph and its
Euclidean penalty (`cdc:of:thm:cubicsemilinear`,
`cdc:of:cor:squares`, `cdc:of:cor:no-cubic-universal`,
`cdc:of:prop:quartic`, `cdc:of:eq:euclidean`); source 12's Theorem 19.2
generalizes `cdc:of:thm:ranks`, and its compatible-union lemma, batch
serialization and the second half of its absence theorem are
`cdc:of:prop:antimatroid`, `cdc:of:lem:closure` and
`cdc:bd:prop:nobound`; source 14's semilinearity proposition has a second
route through `cdc:of:thm:classification`. Source 17's fuel lemma
(Lemma 67.1) is `cdc:rx:thm:threshold` in another substrate, and the
ordinary-net case of its trace theorem (Theorem 71.1) is a second route to
`cdc:thm:main` and `cdc:wf:thm:petri`, generalized to reset arcs with every
nonnegative real zero natural; its canonical peak certificate is related to
`cdc:rx:thm:QL` but is not the same theorem. Source 17's program layer is
source 16's (above). These are printed with `[write]` notes and listed in
Section 1.5.

The report does **not** claim:

- historical priority for any Part (all three sources searched the
  literature in a targeted, not exhaustive, way), peer review, or
  proof-assistant verification;
- a fixed-arity universal Diophantine equation, a solution of the
  single-fold or finite-fold representation problem, or an improvement of
  the repository's universal arithmetic-operation bounds (the 75- and
  87-operation figures at the sources' pins). Part III's quadratic is for a
  universal machine, but its arity grows with the horizon `k`, which is
  compiler data; Part II's unbounded direction is "there is a grounding
  size", outside every polynomial;
- that finite tests prove the all-input theorems (all three sources say
  their executable checks are implementation and regression checks);
- minimality of any witness count, of the 23-rule maximal-parallel system
  of Alhazov and Verlan, of the Neary–Woods machine or of Iijil's matrix;
- for Part I: efficient computation of `ρ(A)` (the shipped search is
  exponential), a rank theory for guarded systems, convex certificates in
  general, or that guarded/flat histories are implemented (only
  ordinary unguarded retaining histories are);
- for Part II: correctness for zero or negative delays, negative glues,
  inhibition, detachment, consumption, stochastic kinetics or multi-tile
  attachments; an enumeration of all nondeterministic outcomes; a new
  numerical universal tile set; or an improvement over the allocation of
  CDC Part XI (the interfaces differ);
- for Part III: optimality of `35k` or of the four-operation loader, any
  cost for encoding ordinary programs as half tapes, or that the
  universal machine, the matrix or its compiler are new.
- for Part IV: a fixed-arity universal polynomial, uncharged temporal
  compression, completeness for an arbitrary preassigned catalogue, uniqueness
  of the selected schedule or of the witness across schemas, a lower bound
  for encodings other than identical-subtree quotients, priority, or a
  certified instantiated universal rule table;
- for Part V: any payment for unknown time, a fixed-arity unbounded-time
  representation, a singlefold MRDP representation, an efficiency or
  Diophantine record, priority, or a verifier of supplied membrane histories
  (its polynomial is an outcome projection); the half-tape-to-raw-input
  preprocessing is external, and the prime example (`C` about `7.4·10¹⁷`
  instructions) is computed from proved macro counts, not executed;
- for Part VI: novelty of the reset-budget method or of the decidability
  boundaries (both classical), arc-minimality, a fixed-arity unbounded-time,
  finite-fold or single-fold result, a size record, a uniform procedure
  deciding which inputs have empty length sets, marker-free trace
  certificates for the shared-arc net, or real-exactness of the padding
  variant; the prime-coded example is macro-counted, not replayed.

## Relation to neighbouring reports and to the formal project

- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  Part XI (`cdc:of:`) classifies exactly the class this report lives in
  (`D⁺₂ = D⁺₃ = SL`, `D⁺₄ = CE`, `cdc:of:thm:classification`); see above
  for the re-proofs. Its Part XIII declines a maximal-parallel reading of
  its reaction networks and cites the same Alhazov–Verlan system; Part I
  supplies certificates for that convention. Part III bears on its
  questions `cdc:q:acceleration` (a canonical factorization preserved by
  the witnesses, realized for one fixed universal Waterfall program at
  each fixed horizon), `cdc:q:restricted` (the decidable common-column
  class) and Part XII's "Canonical macro decompositions" and "A small
  explicit fixed interpreter"; Parts I and II add data points to
  `cdc:q:degree`. None of these questions is answered in general.
  Part VI re-proves Part XIII's resource threshold (`cdc:rx:thm:threshold`)
  for reset nets and generalizes Part II's trace certificates (`cdc:thm:main`,
  `cdc:wf:thm:petri`); its exact-target acceptance is the distinction behind
  `cdc:rx:thm:nopriority`. Parts V and VI bear on CDC's question
  "Substrate-transfer theorems".
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**: Part I's
  guarded register-machine embedding (one round per instruction) appears
  to satisfy the hypotheses of `lbh:thm:transfer` with block length one,
  a partial answer to that report's question "Other unconventional
  substrates with timing certificates"; source 08 does not state this and
  the hypotheses were not checked in detail (`[write]` note in Section 7).
- **[`signal-machine-collision-certificates`](../signal-machine-collision-certificates)**
  (batch 78, cluster H2) uses the same family of degree-two certificates
  for rational signal machines. No theorem is shared. Reciprocal note
  (batch 79, cluster J2, 2 October 2026): that report's Part III (its
  source 12, batch-79 manuscript 16, written in `bd8a8afd6`) is now in this
  report's own format. Its step packet `smc:cs:thm:packet`, for a
  finitely branched homogeneous-guarded piecewise-linear map instantiated
  for an 18-signal conservative universal signal machine, is literally of
  the form `qoc:eq:spine`, with selector gates
  `(Σ_{h≠r} b_h)(Σ_i X_{r,i})`: Part V's strong gates without the selector
  in the right factor. Its source claims natural exactness only; the note
  after its packet theorem shows that the real fibre is natural at every
  natural input `X ≠ 0`, and at `X = 0` too under that theorem's disjoint
  homogeneous branch hypothesis (its weak gates alone do not force one-hot
  selection at zero; corrected 2 October 2026 after
  `review_batch79_j2_bbc67d225.md`, finding 4). Its Part IV, like Part IV here, has degree four.
  Dated notes in this report's relation section and after Theorem
  `qoc:um:thm:poly` record this; neither report re-proves a theorem of the
  other. Reciprocal note (batch 80, cluster K2, 2 October 2026): the
  certificates of that report's Part V (its sources 14 and 15, batch-80
  manuscripts 10 and 02, written in `ef114b0bb`) for raw-integer
  two-counter branches use the inactive-product gate
  `(E_t − e_tj)(e_tj + u_tj)` of Lemma `qoc:rn:lem:gates`, with one base
  per branch (`smc:tm:eq:certificate`, `smc:ct:eq:poly`,
  `smc:tm:thm:certificate`). One-hot selection and inactive vanishing
  therefore hold there over the nonnegative reals too, but divisibility of
  the raw value by a prime needs natural values (that report's real
  assignment `e = 1`, `u = 1/2`), so those certificates are exact over the
  naturals only. A dated note after the lemma records this; no theorem is
  shared.
- **This report's own questions.** Part IV answers in part Part I's question
  "Add dynamic membranes without witness multiplicity" (one step, histories
  modulo renaming) and covers division and dissolution, which Part I's
  fixed-topology section excludes; Part V answers in part "Compile a
  published small universal system end to end" (a universal active-membrane
  system, not the 23-rule system); Parts V–VI are the opposite data point to
  Part III's question on longer verifiable affine blocks. Dated notes record
  each in place.
- **[`group-theoretic-substrates`](../group-theoretic-substrates)**,
  **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**,
  **[`stochastic-and-thermal-exactness`](../stochastic-and-thermal-exactness)**:
  no overlap.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`,
  reviewed all six archives on the day they arrived (source 17's review
  landed after its placement; see "Reviews and patches" below). Its note `neary_woods_explicit_universal_tm.md`
  (added 1 October 2026, commit `f2622a68c`) transcribes the same
  Neary–Woods Table 16 as Part III, entry by entry, and reports the same
  `(u10,b)`/`(u10,c)` inconsistency in the primary paper; source 14 found it
  independently, and the report credits the note. Sources 16 and 17 report
  it again; it is printed once, in Part III. The programme's
  `u15_raw_half_tape_loader.md` (commit `02419530a`) prices the
  ordinary-input loader into raw half tapes (138 = 73M+65A operations) that
  Parts III, V and VI leave external.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean
  development confers no formal status**. Sources 08 and 12 use MRDP only
  as a classical theorem; the project's formal endpoint is
  `Diophantine.mrdp`, `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines
  33, 42, 26), whose blob `74aea8c5e` is the one source 08 cites. The
  project has formalized none of this report's statements: it has no
  multiset-rewriting, timed-Horn, self-assembly, Waterfall, membrane or
  reset-net module. Source 17 cites `MRDP.lean` and
  `Common/DiophantineTrace.lean` at its pin `44983ed7e`; both are unchanged
  at this write, and the latter's declarations
  (`Diophantine.boundedForall_dioph`, `Diophantine.exactIter_dioph`,
  `Diophantine.existsExactIter_dioph`) are general Diophantine closure
  theorems, not statements of this report.

## Reviews and patches by the research programme

These reviews are in another session's tree; nothing there was changed,
and **the shipped programs are the delivered bytes, unpatched**. Applying a
patch to the prefixed copies would need its file names rewritten and is
the research programme's decision. For source 17 the delivered bytes are,
since batch 80, those of the authors' corrected code edition, which
contains its own repair of the reviewed defects (below).

- Sources 08 and 12: `incoming_substrate_review_808b53ed8.md`, with the
  detailed reviews `incoming_parallel_order_review_808b.md` (source 08)
  and `incoming_convergence_review_808b.md` (source 12), commit
  `126028588`. Both pass mathematical review. Source 08's compiler keeps
  mutable references to its input matrices and guards and accepts a guard
  `Atom(0,1,2)` whose polarity the compiler and the semantic oracle read
  differently; patch `maximal_parallel_immutable_guards.patch`. Source
  12's compiler keeps mutable references to seeds and rules, returns
  aliased export lists and accepts a fractional seed label; patch
  `total_quadratic_immutable_inputs.patch`. No valid polynomial or export
  changes. The review also proves a reduction of source 12's gates to
  `W' = m(2q+3)+2D+2G+R` witnesses (dated note after Theorem 21.2; not
  implemented) and notes the inconsistency below about duplicate literals.
- Source 14: `waterfall_intake_triage_24a743255.md`, then
  `waterfall_report_review_24a743255.md` (commit `f19aaa092`): all eight
  replay commands pass and the theorems are confirmed over natural
  coordinates; the grouped compiler accepts floating-point and Boolean
  inputs and aliases its exported name lists, repaired by
  `waterfall_grouped_exact_domains.patch`. The programme also projected the
  forced first step and the three forced steps before halt
  (`waterfall_forced_boundary_projection.md`, commit `3b8187ea9`): for
  `k ≥ 4`, `35k−138` witnesses, `5k−15` squares and `2k−8` products; at
  `k = 7`, 107 witnesses and a complete 720-operation evaluation instead of
  245 and 1558. Its `waterfall_endpoint_alias.md` shows that the
  endpoint-count shortcut also fails on the actual 46-clock matrix
  (`Mv = 194·1`; `(C,k,τ)` from `(189,7,428)` to `(251,17,622)`). These are
  dated notes in Part III (Sections 34 and 37); source 14's counts are
  printed as delivered.
- Sources 15 and 16: `review_membrane_reports_2a8a.md` (commit `85294a527`;
  index `incoming_substrate_review_2a8a39599.md`). No theorem-level defect,
  no false certificate, **no patch**; all 18 author suite commands and two
  loader checks pass in private copies (300-s limits); an independent checker
  ran 122,640 exhaustive natural tuples, 10,125 maximality cases and 502
  rejected mutations. The review documents the scope limits that Part IV
  states (well-formed schemas, natural witnesses, existential completeness)
  and a bounded direct-prefix projection of source 16's affine-frontend
  polynomial (forced first zero test: `2,811(T−1)` witnesses, `5(T−1)+1`
  squares, `761(T−1)` products), a dated note in Part V, Section 60.
- Source 17: `review_reset_petri_net_aebfa386e.md` (commit `9df1f72ca`,
  after the placement; replay index `review_reset_signal_aebfa386e.md` with
  checker `review_reset_signal_aebfa386e.py`). The mathematics on the valid
  natural domain and all fourteen author commands pass. Two malformed-input
  defects: `peak_quadratic.py` accepts non-Boolean option flags (with
  `all_durations=0.5` it emits a schema declaring 2,813 variables but using
  index 2,813), and `build_net.py`'s `fire` accepts unknown places and
  non-natural token counts. Patch `reset_net_exact_domains.patch` (SHA-256
  `bc3d28a4…`), changing only those two programs. At the batch-79 write the
  shipped `code/17-reset-net-peak_quadratic.py` and
  `code/17-reset-net-build_net.py` were the delivered originals, unpatched.
  **Batch 80:** they are now the authors' corrected code edition (arrival
  `4e270aa46`, placement `8a4e64732`), written after reading (not running)
  this review: `compile_peak` requires exact `bool` duration flags, `fire`
  requires a dictionary of known string places with exact nonnegative
  `int` counts, and `initial` raises `ValueError` instead of asserting; the
  checks hold under `python -O`. The repair is equivalent to the patch: the
  patched originals pass the authors' new regression
  `code/17-reset-net-checks-audit_exact_domains.py` (normal and `-O`, the
  same printed results), and the unpatched originals fail it ("Accepted malformed
  call"). **Do not apply the patch to the shipped files**: the repair is
  already present and the patch does not apply to them. The programme's
  correction audit `review_batch80_corrected.md` (commit `abfc0cb25`)
  confirms the repair, that removing the new guards (and restoring the old
  assertion) makes both programs' Python syntax trees identical to the
  originals, and that nets, schemas and receipts are otherwise unchanged;
  it also notes that the schema parameter and caller-supplied nets are not
  comprehensively hardened. The
  review also gives a natural-only gate simplification (`(E−e_r)X_r` instead
  of `(E−e_r)(e_r+X_r)`: same natural zero set, real exactness lost; one
  evaluation schedule from `12,770h+11` to `12,009h+11` paid operations), a
  dated note in Part VI, Section 69.
- The placement itself: `review_placement_a7ae02511.md` (commit
  `653349f6a`) authenticates all 246 files placed by `a7ae02511` against
  their archive members, and its stager `replay_placed_substrates_a7ae02511.py`
  restores the complete delivered layouts of sources 15–17 from Git. That
  statement is about the files of `a7ae02511` and remains true there; 4 of
  them (13 across three reports) were replaced by corrected bytes in the
  batch-80K1 placement. For original-edition restoration, pass an unchanged
  historical checkout (for example, a worktree at `a7ae02511`) as `--repo`,
  while invoking the later helper from a recent checkout with its required
  sibling `placement_a7ae02511_inventory.json`. Neither helper nor inventory
  exists at `a7ae02511`. A current corrected checkout passed as `--repo`
  stops with "Placed source differs". For the corrected layout of source 17
  extract the batch-80 archive.
- Later reviews of this report's own text (applied 2 October 2026):
  `review_batch79_j2_bbc67d225.md` (commit `37a829e0b`), finding 4: the
  batch-79 reciprocal note after Theorem `qoc:um:thm:poly` had presented
  fractional selectors at `X = 0` as an exception of the signal packet
  `smc:cs:thm:packet`; under that packet's disjoint homogeneous branch
  hypothesis its real fibre is natural at zero too, and only its weak
  gates in isolation admit fractional selectors. The note is corrected in
  place, crediting the review (the patch's hunk verbatim plus a
  correction sentence), and its catalogue entry no longer says that every
  Part has degree two. `review_batch80_correction_publication_86267b8a3.md`
  (commit `fbad71e8c`) passes the batch-80K1 corrected-code update of this
  README and corrects its historical-stager instructions (the preceding
  bullet and alternative 2 under "Sources 15–17") from
  `batch80_historical_stager_launch.patch`, applied verbatim.

## Licensing of the third-party machine data

`data/14-waterfall-UniversalTM15x2.tm.txt` (227 bytes) and
`data/14-waterfall-UniversalTM15x2.twm.txt` (5,414 bytes) are Iijil's
machine data from the MTGPrograms repository
(<https://github.com/Iijil1/MTGPrograms>), shipped byte for byte because
the replay needs them; their SHA-256 values are in
`14-waterfall-SOURCE-PROVENANCE.md`. **These two files are not covered by
the repository's MIT-0 licence.** Source 14 observed no upstream licence
and says it "does not claim to relicense any third-party work"
(`14-waterfall-LICENSE-PROVENANCE.md`); they are included as factual
mathematical machine specifications, and anyone redistributing them should
check the upstream terms. The source machine itself is Neary and Woods's;
their paper is cited, not bundled.

The same delivered note also says that no blanket licence is assigned to
source 14's own note and Python checks "in this private review package".
The placement treated those files as repository content; this README
records both statements and does not decide the question.

Sources 16 and 17 use the same serialization (SHA-256 `ba70ab2c…`, 227
bytes): source 16's two copies and source 17's two copies are not shipped,
and the programs read it at `source/UniversalTM15x2.tm.txt` in their
delivered layouts, where the recipes below put a copy of
`data/14-waterfall-UniversalTM15x2.tm.txt`; it stays third-party data, not
covered by MIT-0. Sources 15–17 state no licence for their own files: source
15's README says its code and article text were prepared for that release,
and sources 16 and 17 say they redistribute only the small serialization and
their own proofs and programs, citing third-party papers without bundling
them. The placement treated their files as repository content.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
bm, microtype, booktabs, longtable, enumitem, tcolorbox, fancyhdr, TikZ,
xurl, hyperref, listings, float; `hypertexnames=false`). The committed
build has 169 pages (168 before the batch-80 note), with no errors, warnings,
undefined references or citations, no multiply
defined labels, no duplicate destinations, and no overfull or underfull
boxes. The log carries eight informational "Infinite glue shrinkage found in
box being split" messages from longtable page breaks (two in the build of
Parts I–III alone, six before the batch-80 note, which moved the page
breaks of Part VI's file map and of the provenance table). The batch-80
edit added no label, macro or package; the `.aux` of a build of the
previous text has the same 307 labels with the same numbers, and the pages
of the new note (Section 76), the provenance table and the title page were
rendered and inspected. The in-place correction of 2 October 2026 to the
reciprocal note after Theorem 60.1 (`qoc:um:thm:poly`; see "Reviews and
patches by the research programme") lengthens Part V by one page: the
build now has 170 pages, still with no errors, undefined references or
citations, multiply defined labels, duplicate destinations or overfull or
underfull boxes, and with the same seven "Infinite glue shrinkage"
messages as a rebuild of the previous text in the same environment. The
307 labels keep their numbers (compared in the `.aux`); pages after
Section 60 move up by one. The batch-80 reciprocal note after Lemma 68.1
(`qoc:rn:lem:gates`; cluster K2, no label, macro, package or bibliography
entry) moves the pages from Section 69 to Appendix G up by one and leaves
the total at 170 pages, with no errors, warnings, undefined references or
citations, multiply defined labels, duplicate destinations or overfull or
underfull boxes, and five "Infinite glue shrinkage" messages (seven in a
rebuild of the previous text in the same environment). All 307 labels and
56 bibliography entries keep their numbers (compared in the `.aux`), and
the page of the note (page 136) was rendered and inspected.

The article is generated reproducibly from the delivered manuscripts by
merge scripts with anchored insertions (Parts IV–VI were appended to the
committed text of Parts I–III the same way); the scripts are not shipped,
and `article.tex` is the source of record.

## Rerunning the programs

The programs locate their companions and data by their delivered layout,
and all three suites **write into that layout**: source 08's `verify.py`
rewrites `data/verification_counts.json` (and its README redirects output
over `data/example_certificate.json` and `data/verification.txt`); source
12's `test_compiler.py` rewrites `results/test_receipt.json` and the four
example files; source 14's `run-replay.sh` rewrites all twelve JSON files
of `replay/` and `receipts/` and writes seven logs. Run in place, several
programs would also write new files beside the shipped ones (for example
`code/14-waterfall-grouped_quadratic.py` writes into `code/`). **Never run
them in place.** Recreate the delivered layout in a scratch directory
(`py` is the Python launcher on this machine; the delivered texts say
`python` or `python3`). From this directory:

```sh
# source 08 (standard library; Python 3.10+)
mkdir -p r08/code r08/data
for f in parallel_certificates.py verify.py; do cp code/08-maximal-parallel-$f r08/code/$f; done
for f in example_certificate.json verification.txt verification_counts.json; do cp data/08-maximal-parallel-$f r08/data/$f; done
(cd r08 && py code/verify.py > verification.out && py code/parallel_certificates.py > example.out)

# source 12 (standard library; Python 3.10+)
mkdir -p r12/code r12/results
for f in quadratic_compiler.py test_compiler.py verify_exports.py; do cp code/12-total-quadratic-$f r12/code/$f; done
for f in export_verification huge_delay_chain literal_four_tile_example locking_counterexample test_receipt timed_race; do
  cp data/12-total-quadratic-$f.json r12/results/$f.json; done
(cd r12 && py code/test_compiler.py > test.out && py code/verify_exports.py > export_verification.out)

# source 14 (standard library; Python 3.9+; do not use python -O)
mkdir -p r14/replay r14/receipts r14/source
for f in grouped_quadratic verify_certificates verify_frontend verify_frontend_independent \
         verify_halting_example verify_matrix_definition verify_quadratic_independent verify_release; do
  cp code/14-waterfall-$f.py r14/replay/$f.py; done
cp code/14-waterfall-run-replay.sh r14/run-replay.sh
for f in affine-gap-forms certificate-receipt frontend-receipt grouped-quadratic-receipt \
         grouped-quadratic7-certificate grouped-quadratic7-fixture unit-ledgers; do
  cp data/14-waterfall-$f.json r14/replay/$f.json; done
for f in halting-example independent-receipt matrix-definition quadratic-independent release-verification; do
  cp data/14-waterfall-$f.json r14/receipts/$f.json; done
cp data/14-waterfall-UniversalTM15x2.tm.txt r14/source/UniversalTM15x2.tm.txt
cp data/14-waterfall-UniversalTM15x2.twm.txt r14/source/UniversalTM15x2.twm.txt
(cd r14 && PYTHON=py sh run-replay.sh)
```

At the write (Windows, `PYTHONUTF8=1`, Python 3.14.4) all three passed,
in about 12 s, 23 s and 15 s. Source 08 reproduced its example and counts
files, and its transcript differed only in the Python version and elapsed
time lines; source 12 reproduced its four example polynomials and its
export verification, and its receipt differed only in `runtime_seconds`;
source 14 printed "All Waterfall replays passed." and reproduced all
twelve JSON files. All comparisons are apart from line endings: the
Windows runs write CRLF, and the shipped files are LF. Receipts with run
times or interpreter versions never regenerate byte for byte.

### Sources 15–17

Their programs too read and write their delivered layouts (they rewrite
receipts, transcripts, nets and exports in place), the delivered texts say
`python3`, and `code/17-reset-net-run-checks.sh` hard-codes `python3`. Use a
recreated layout, never the shipped files. Three ways to get one:

1. extract the arrival archives (commands under "Delivered names"); they
   contain every file, including the excluded ones;
2. create an unchanged historical checkout, for example with
   `git worktree add <historical-checkout> a7ae02511`, then run
   `py Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py --repo <historical-checkout> --destination <new-directory>`
   from a recent repository root where the helper and its required sibling
   `placement_a7ae02511_inventory.json` exist. Neither file exists in the
   `a7ae02511` checkout. This restores the original editions from the
   historical placed bytes; passing the current corrected checkout as
   `--repo` stops at the replaced files; or
3. rebuild the layouts from the shipped files with the snippet under
   "Reconstructing the excluded data", then regenerate the excluded files.

Then, with `py` and `PYTHONUTF8=1`:

```sh
# source 15, in membrane-motif-release/  (a few seconds each)
py replay/verify_saved_examples.py; py replay/focused_tests.py
py replay/regression_extensions.py; py replay/export_sos.py
py replay/replay_tests.py      # exhaustive: several minutes
# source 16, in literal-membrane-release/packet/ and .../direct/
py build_frontend.py; py verify_frontend.py; py verify_membrane.py; py replay_example.py
py verify_density.py; py quadratic_outcome.py --steps 1; py verify_quadratic.py; py load_input.py --A 64
py build_direct.py; py verify_direct.py; py build_quadratic.py --steps 1
py make_accepting_witness.py; py verify_accepting_quadratic.py; py verify_membrane.py
# source 17, in reset-net-release/  (the order of run-checks.sh)
py verify_source.py; py build_net.py; py replay_and_verify.py; py budget-audit/audit_budget.py
py checks/audit.py; py checks/audit_generated_families.py; py checks/audit_padding_and_generic_peak.py
py two-counter/verify_source.py; py two-counter/build_variant.py
py two-reset-audit/audit_two_reset.py; py two-reset-audit/compare_release_net.py
py shared-reset-arcs/build_shared.py; py shared-checks/audit_shared.py; py shared-checks/audit_prime_macros.py
py checks/audit_exact_domains.py; py -O checks/audit_exact_domains.py   # corrected edition (batch 80)
```

The exact-domain regression runs under `-O` as well; the other checkers
use assertions and must run without optimization flags.

At placement (Windows, `PYTHONUTF8=1`, 170-s limit per command) source 15's
four short suites passed and `replay_tests.py` did not finish (the research
programme ran it within 300 s); all fifteen component commands of source 16
passed, with outputs equal to the delivery apart from line endings and one
platform field (`program_sha256` in `direct/accepting_quadratic_witness.json`,
a hash of the CRLF-rewritten program); and every command of source 17 passed
except `shared-checks/audit_shared.py`, which did not finish (three of its
four phases passed; the delivered receipt records PASS). At this write, on
layouts rebuilt from the shipped files with regenerated excluded files,
`focused_tests.py` and `verify_saved_examples.py` of source 15 and
`verify_source.py`, `two-counter/verify_source.py`,
`checks/audit_padding_and_generic_peak.py` and `replay_and_verify.py` (63 s)
of source 17 passed. `reproduce.py` of source 16 reads the three manifests
and byte-compares regenerated files, so it runs only in the extracted
archive and, on Windows, fails on line endings; run it under POSIX or
compare modulo CRLF. `two-reset-audit/audit_two_reset.py` hashes the
unshipped `two-counter/source/PROOF.md` into its receipt; take that file
from the archive (`unzip -p rn.zip reset-net-release/two-counter/source/PROOF.md`).
Batch 80 (corrected edition), on a layout rebuilt by `layout.sh` from the
shipped files after the replacement (Windows, `PYTHONUTF8=1`, Python
3.14.4): `checks/audit_exact_domains.py` passed normally and with `-O` (64
rejected calls, 9 schema hashes, 388 stored firings, 72 overlap cases; about
3 s for both), and its two printed JSON lines equal the two `runs` entries
of the shipped receipt; with the three horizon-one schemas regenerated (the
compiler calls under "Reconstructing the excluded data"),
`checks/audit_padding_and_generic_peak.py`, `verify_source.py` and
`build_net.py` reproduced their receipts, `reset_net.json` and
`net_ledger.json` modulo line endings. The batch-80 placement check also
reran `checks/audit.py`, `checks/audit_generated_families.py` and
`budget-audit/audit_budget.py` in the extracted corrected archive with
identical outputs, and found that the exact-domain regression fails on the
two original programs and passes on them with the review's patch.

## Reconstructing the excluded data

Vladimir, 2 October 2026: "Exclude heavy regenerable artifacts". Seventeen
files of sources 16 and 17, 63,245,978 bytes in all, were not shipped. The
delivered programs regenerate each of them byte for byte, after the CRLF
line endings that Windows runs write are converted to LF. This write rebuilt
all seventeen from the shipped files on a recreated layout and compared them
with the archive members: all identical. Batch 80: the heavy members of
source 17's corrected code edition (`4e270aa46`) are byte-identical to those
of the original edition, and its corrections leave every generator below
unchanged (`build_net.py` changes only in `initial` and `fire`, not in the
net builder; `reset_net.json` and `net_ledger.json` regenerate byte for
byte), so the table and the commands stand; only the retrieval command
gains the corrected archive (see "Delivered names").

| Source | Excluded files (delivered paths) | Bytes | Rebuilt by | Time here |
|---|---|---:|---|---:|
| 16 | `packet/membrane_rules.jsonl`, `packet/literal2.json`, `packet/literal2.txt`, `packet/object_alphabet.txt` | 4,360,490; 878,685; 504,996; 467,766 | `py build_frontend.py` in `packet/` | 3 s |
| 16 | `packet/quadratic_schema_T1.json`, `packet/semantic_branches.json` | 3,094,551; 1,061,338 | `py quadratic_outcome.py --steps 1` in `packet/` (reads `literal2.json`) | 1 s |
| 17 | `canonical_peak_schema_h1.json`, `all_duration_schema_h1.json`, `projected_trace_schema_T1.json` | 810,169; 810,250; 1,032,589 | **no shipped script writes them** (`replay_and_verify.py` and `checks/*.py` only compare them): the three compiler calls below | 1 s |
| 17 | `two-counter/reset_net.json`, `two-counter/canonical_peak_schema_h1.json`, `two-counter/projected_trace_schema_T1.json` | 4,652,129; 10,100,914; 13,217,236 | `py two-counter/build_variant.py` (reads `two-counter/source/literal2.json`, which is source 16's `packet/literal2.json`) | 18 s |
| 17 | `shared-reset-arcs/two-counter/{reset_net,canonical_peak_schema_h1}.json`, `shared-reset-arcs/three-counter/{reset_net,canonical_peak_schema_h1}.json` | 7,676,408; 10,225,459; 504,323; 822,675 | `py shared-reset-arcs/build_shared.py` (after the two rows above) | 20 s |
| 17 | `two-reset-audit/two_reset_net.json` | 3,026,000 | `py two-reset-audit/audit_two_reset.py` (writes the net, then needs `two-counter/source/PROOF.md` for its receipt) | 5 s |

Source 17's own copies of source 16's `literal2.json` and `literal2.txt`
(`two-counter/source/`) are excluded with them. The simplest route is to
extract the arrival archives, which contain every file. To rebuild instead
from this directory, recreate the layouts: save the following as
`layout.sh` outside the repository and run `sh layout.sh . <scratch>` (POSIX
`sh`, as in Git Bash). It copies every shipped file of sources 15–17 to its
delivered path; this write checked the result byte for byte against the
archives.

```sh
#!/bin/sh
# Recreate the delivered layouts of QOC sources 15, 16, 17 from the shipped
# files.  usage: sh layout.sh <report-dir> <scratch-dir>
set -eu
Q=$(cd "$1" && pwd); O=$2
mkdir -p "$O"; O=$(cd "$O" && pwd)

# source 15 (batch-79 manuscript 08)
M=$O/membrane-motif-release; mkdir -p "$M/replay" "$M/provenance"
cp "$Q/15-membrane-motifs-RELEASE_NOTES.md" "$M/RELEASE_NOTES.md"
cp "$Q/data/15-membrane-motifs-source-provenance.json" "$M/provenance/source-provenance.json"
for f in "$Q"/code/15-membrane-motifs-* "$Q"/data/15-membrane-motifs-*; do
  b=${f##*/15-membrane-motifs-}; [ "$b" = source-provenance.json ] && continue
  cp "$f" "$M/replay/$b"; done

# source 16 (batch-79 manuscript 09)
U=$O/literal-membrane-release; mkdir -p "$U/direct/source" "$U/packet/source" "$U/receipts"
cp "$Q/16-universal-membrane-direct-PROOF.md" "$U/direct/PROOF.md"
cp "$Q/16-universal-membrane-packet-PROOF.md" "$U/packet/PROOF.md"
for f in "$Q"/code/16-universal-membrane-* "$Q"/data/16-universal-membrane-*; do
  b=${f##*/16-universal-membrane-}
  case $b in
    direct-*) cp "$f" "$U/direct/${b#direct-}" ;;
    packet-*) cp "$f" "$U/packet/${b#packet-}" ;;
    tm_table.json|virtual3.json) cp "$f" "$U/direct/$b"; cp "$f" "$U/packet/$b" ;;
    document_checks.json|reproduction.json) cp "$f" "$U/receipts/$b" ;;
    *) cp "$f" "$U/$b" ;;
  esac; done
for d in direct packet; do cp "$Q/data/14-waterfall-UniversalTM15x2.tm.txt" "$U/$d/source/UniversalTM15x2.tm.txt"; done

# source 17 (batch-79 manuscript 18)
R=$O/reset-net-release; mkdir -p "$R/source" "$R/two-counter/source"
cp "$Q/17-reset-net-VALIDATION.md" "$R/VALIDATION.md"
cp "$Q/17-reset-net-CORRECTION.md" "$R/CORRECTION.md"
for f in "$Q"/code/17-reset-net-* "$Q"/data/17-reset-net-*; do
  b=${f##*/17-reset-net-}
  case $b in
    shared-reset-arcs-three-counter-*) d=shared-reset-arcs/three-counter; b=${b#shared-reset-arcs-three-counter-} ;;
    shared-reset-arcs-two-counter-*) d=shared-reset-arcs/two-counter; b=${b#shared-reset-arcs-two-counter-} ;;
    shared-reset-arcs-*) d=shared-reset-arcs; b=${b#shared-reset-arcs-} ;;
    two-counter-source-*) d=two-counter/source; b=${b#two-counter-source-} ;;
    two-counter-*) d=two-counter; b=${b#two-counter-} ;;
    two-reset-audit-*) d=two-reset-audit; b=${b#two-reset-audit-} ;;
    shared-checks-*) d=shared-checks; b=${b#shared-checks-} ;;
    budget-audit-*) d=budget-audit; b=${b#budget-audit-} ;;
    checks-*) d=checks; b=${b#checks-} ;;
    *) d=. ;;
  esac
  mkdir -p "$R/$d"; cp "$f" "$R/$d/$b"; done
# source 17's copies of source 16's program files (shipped once, under 16-)
for d in source two-counter/source; do
  cp "$Q/data/14-waterfall-UniversalTM15x2.tm.txt" "$R/$d/UniversalTM15x2.tm.txt"
  cp "$Q/data/16-universal-membrane-tm_table.json" "$R/$d/tm_table.json"
  cp "$Q/data/16-universal-membrane-virtual3.json" "$R/$d/virtual3.json"; done
cp "$Q/data/16-universal-membrane-direct-virtual3.txt" "$R/source/virtual3.txt"
cp "$Q/data/16-universal-membrane-direct-macro_certificates.json" "$R/source/macro_certificates.json"
cp "$Q/data/16-universal-membrane-direct-accepting_counter_trace.json" "$R/source/accepting_counter_trace.json"
cp "$Q/data/16-universal-membrane-packet-virtual3.txt" "$R/two-counter/source/virtual3.txt"
cp "$Q/data/16-universal-membrane-packet-macro_certificates.json" "$R/two-counter/source/macro_certificates.json"
echo "layouts recreated under $O"
```

then regenerate in this order, converting line endings after each step on
Windows (where the programs write CRLF):

```sh
lf() { py -c "import sys,pathlib;[pathlib.Path(p).write_bytes(pathlib.Path(p).read_bytes().replace(b'\r\n',b'\n')) for p in sys.argv[1:]]" "$@"; }
export PYTHONUTF8=1
cd <scratch>/literal-membrane-release/packet
py build_frontend.py && py quadratic_outcome.py --steps 1
lf membrane_rules.jsonl literal2.json literal2.txt object_alphabet.txt quadratic_schema_T1.json semantic_branches.json
cp literal2.json literal2.txt ../../reset-net-release/two-counter/source/
cd ../../reset-net-release
py -c "
import json, sys; from pathlib import Path; sys.path.insert(0, '.')
from source_quadratic import semantic_table
from peak_quadratic import compile_peak
from reset_quadratic import compile_schema
table = semantic_table(json.loads(Path('source/virtual3.json').read_text()))
net = json.loads(Path('reset_net.json').read_text())
for name, obj in [('canonical_peak_schema_h1.json', compile_peak(table, 1)),
                  ('all_duration_schema_h1.json', compile_peak(table, 1, all_durations=True)),
                  ('projected_trace_schema_T1.json', compile_schema(net, 1, project_controls=True))]:
    Path(name).write_bytes((json.dumps(obj, indent=2) + '\n').encode('utf-8'))
"
py two-counter/build_variant.py && lf two-counter/*.json
py shared-reset-arcs/build_shared.py && lf shared-reset-arcs/*/*.json
py two-reset-audit/audit_two_reset.py; lf two-reset-audit/two_reset_net.json
```

The three compiler calls are those that `replay_and_verify.py` and the
`checks/` scripts compare against; they write LF on every platform. The
receipts that record hashes of excluded or unshipped files (source 16's
`SOURCE_PROVENANCE.json` files and receipts, source 17's
`SOURCE_PROVENANCE.json`, `checks/*RESULTS.json` and
`two-reset-audit/audit_receipt.json`) are shipped as delivered.

## Discrepancies and disclosures

- The shipped build scripts keep the delivered layout:
  `code/12-total-quadratic-build.sh` changes to its own directory and runs
  pdflatex three times on an `article.tex` that is not there, and
  `code/14-waterfall-build.sh` builds `paper/waterfall-diophantine.tex`,
  which is not shipped. Neither builds this report; use the build command
  above.
- Delivered texts name delivered paths: Part I's validation section and
  appendices (`code/parallel_certificates.py`, `data/...`), Part II's
  implementation section and Appendices D–E (`code/...`, `results/...`,
  `build.sh`, `README.md`, `SOURCE_AUDIT.md`), Part III's replay section;
  `08-maximal-parallel-PROOF_AUDIT.md`/`SOURCE_AUDIT.md`,
  `12-total-quadratic-SOURCE_AUDIT.md` and the two `14-waterfall-*.md`
  notes; `data/12-total-quadratic-export_verification.json` (file names
  without prefix); source 14's receipts. `[write]` notes give the shipped
  names in the article; the map above gives them here. Source 08's title
  page and Part II's Appendix E list the delivered PDFs and READMEs, which
  are not shipped.
- Source 12 says (Section 18.1) that duplicate identical body literals are
  removed during input validation; its compiler rejects them, as its own
  Section 26 says. Noted in a `[write]` note; no theorem is affected.
- Source 12 referred to its self-assembly section as "Section 7"; the
  merged text uses a cross-reference (Section 23) and says so in a
  footnote. Source 14's author line "for private review" is printed only
  in the provenance appendix. No other source sentence was changed.
- Sources 08 and 12 describe the repository at `db3b377f0` and know the
  `canonical-diophantine-certificates` report only through its README;
  source 12 calls its Part XI "manuscript 09" (that report's source 09,
  batch-62 manuscript 02; not batch-78 manuscript 09). The report adds the article's statements by
  label (Section 1.5). Source 14 names no repository commit.
- Credits the sources omit are added in `[write]` notes: Păun (membrane
  systems, 2000) and Burkhard (maximum firing strategy for Petri nets) for
  maximal parallelism, and Matiyasevich, Davis–Putnam–Robinson and Davis
  for MRDP (Part I); Knuth (1977), Gallo–Longo–Pallottino–Nguyen (1993),
  Dowling–Gallier (1984) and Baccelli–Cohen–Olsder–Quadrat (1992) for the
  min/max fixed-point equations, Horn closure and max-plus timing (Part II).
- The three title pages are replaced by one, each Part opening with its
  source's title, subtitle, author line, date, abstract and status
  statement. Fonts, paper size and heading and theorem styles are unified:
  source 08 used the newtx fonts on A4 paper with coloured headings, and
  source 12 printed remarks in the definition style. The appendices of the
  three sources are collected after Part III.
- The receipts of source 08 and source 12 record Python 3.13.5; the
  reruns above used Python 3.14.4.

For Parts IV–VI:

- Delivered texts name delivered paths: Part IV's Section 48, Part V's
  Section 61 and Appendix K, Part VI's Section 76 and Appendices L–M; the
  shipped notes `15-membrane-motifs-RELEASE_NOTES.md`,
  `16-universal-membrane-{direct,packet}-PROOF.md`, `17-reset-net-VALIDATION.md`;
  and the receipts. `[write]` notes give the shipped names in the article;
  the map above gives them here. The build scripts
  `code/16-universal-membrane-build_pdf.sh` and `code/17-reset-net-build-pdf.sh`
  build delivered manuscripts that are not shipped; neither builds this
  report.
- Source 17 re-derives source 16's program layer without citing it (see
  the top of this README); four passages are replaced by pointers, listed in
  Part VI's opening note and Appendix H.1. Source 16 refers to source 15 only
  as "a separate motif-based one-step arithmetization" and to an "earlier
  guard-based two-counter construction" that is in its packet proof notes
  (`16-universal-membrane-packet-PROOF.md`, line 411), not in any article;
  `[write]` notes say so.
- The placement dossier said that this report was placed but not yet
  written at source 17's pin `44983ed7e`. That is wrong: Parts I–III were
  written in `c51b9880d`, an ancestor of the pin. Source 17 still does not
  cite this report.
- Source 17's hard-coded "Appendix B" became a cross-reference with a
  footnote; no other source sentence of sources 15–17 was changed. Source 17's
  minipage in its Appendix A gained a `\noindent` (its delivered layout had
  no paragraph indent). Source 15's reference "paun" is
  Păun–Suzuki–Tanaka–Yokomori 2004; Păun's 2000 paper is credited in a
  `[write]` note.
- Source 15's maximality, source 16's frontends and source 17's net use the
  operational conventions their sources state; the conventions differ
  between Parts I, IV and V (Part I: multiset rewriting with cooperative
  rules; Parts IV–V: noncooperative active membranes, weak division in IV,
  elementary division in V). Table 1 says so.
- Batch 80 (corrected code edition of source 17). `17-reset-net-CORRECTION.md`
  uses delivered names (`peak_quadratic.compile_peak`, `build_net.fire`,
  `checks/audit_exact_domains.py`, `run-checks.sh`, `SHA256SUMS`), runs its
  reproducers "from the package root" with `python3`, and names the
  unshipped ledger and delivery README; the regression runs in a recreated
  layout (`layout.sh` above) or in the extracted archive. It writes no
  file: it prints one JSON line per run, and its receipt
  `checks/EXACT_DOMAIN_RESULTS.json` collects the two runs (normal and
  `-O`) as a `runs` list that no shipped script writes. The corrected `run-checks.sh` still
  hard-codes `python3` and now runs sixteen commands; Section 76 of the
  article prints the fourteen of the original as delivered, with a dated
  `[write]` note. Written in the article: that note, and updated sentences
  in the front section (sources and reviews), the opening note of Part VI
  and the provenance appendix (paragraph and source-17 row). No label,
  statement or number changed (the corrected archive's `.tex` is
  byte-identical), and no label was added.
