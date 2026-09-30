# Canonical Diophantine certificates

**Witness-faithful polynomial representations of bounded discrete computation: resource algebra, trace classes, accelerators, polynomial trajectories, memory logs, queues and rewriting**

This is a research report dated 30 September 2026, merged from seven
manuscripts: six of batch 60 (its manuscripts 01–06) and the only manuscript
of batch 61, which is numbered 07 here. The base is manuscript 05, *Canonical
Trace Polytopes*; its `article.tex` was staged unprefixed and has been
replaced in place by the merged text. All seven manuscripts prove the same
kind of theorem: an explicit integer polynomial whose natural zeros are in
bijection with the bounded executions (or trace classes of executions) of a
discrete substrate, with exactly one witness each. They continue the Lean
project `Computability/HilbertTenthProblem`, whose trace interfaces assert
only that such representations exist. Author lines: "Research report
prepared for the ProveIt project" (01), "Research manuscript for the ProveIt
project, Prepared with ChatGPT" (02), "Research note / article / memorandum
prepared for Vladimir Reshetnikov" (03, 04, 05) and "Prepared for Vladimir
Reshetnikov" (06, 07).

| Report no. | Batch, manuscript | Archive | Title | Pin | Arrived | Placed | Printed in |
|---|---|---|---|---|---|---|---|
| 01 | batch 60, manuscript 01 | `Diophantine_Causal_Computation` (29-page PDF) | *Canonical Diophantine Certificates for Causal Computation* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (its §1.2); Parts I (§§2–3), II (§§6–7), III (§§4–5, 8), VII (§§9.3–9.4), VIII (§§9.1–9.2), IX (§10) |
| 02 | batch 60, manuscript 02 | `canonical_diophantine_certificates` (27-page PDF) | *Canonical Diophantine Certificates for Polynomial Trajectories* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (§2); Parts IV (§§1.1–1.2, 3–9), VII (§10.2), VIII (§§10.1, 10.3), IX (§§10.4–10.6) |
| 03 | batch 60, manuscript 03 | `ProveIt_Linear_Size_Diophantine_Certificates`, inner directory `ProveIt_Diophantine_Certificates` (31-page PDF) | *Linear-Size Canonical Diophantine Certificates for Random-Access and Graph Computation* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (§1.3); Parts V (§§2–9), IX (§10) |
| 04 | batch 60, manuscript 04 | `Witness_Faithful_Diophantine_Compilation`, inner directory `diophantine_substrates` (26-page PDF) | *Witness-Faithful Diophantine Compilation* | `e8bb0931d` | `c1f56f842` | `7498484af` | Conventions (§2); Parts II (§§3–5), VII (§§6–7), VIII (§8), IX (§9) |
| 05 (base) | batch 60, manuscript 05 | `canonical_trace_polytopes` (29-page PDF) | *Canonical Trace Polytopes: Witness-Preserving Diophantine Representations of Computational Substrates* | `e8bb0931d` | `c1f56f842` | `7498484af` | Introduction; Conventions (§2); Parts I (§3), II (§§4–8), VII (§9.4), VIII (§§9.1–9.3, 9.5), IX (§10) |
| 06 | batch 60, manuscript 06 | `diophantine_counter_programs` (30-page PDF) | *Saturation and Single-Fold Diophantine Compilation of Concurrent Counter Programs* | `e8bb0931d` | `c1f56f842` | `7498484af` | Conventions (§2); Parts I (§3), II (§§4, 7), III (§§5–6, 8), VIII (§10), IX (§9) |
| 07 | batch 61, its only manuscript | `Causal_Diophantine_Queue_Compilation` (27-page PDF) | *Causality Without Tableaux: Compact Diophantine Certificates for Queue Universality* | `725d2ebb6` | `b998f70c6` | `3bf66a8bc` | Conventions (§§2.1–2.2); Parts I (§3), VI (§§2.3, 4–10), IX (§11) |

Section numbers in the last column are those of each manuscript. Every
manuscript also contributes to the Introduction and to the back matter
(Implementation and validation, Formalization targets, Research questions,
Conclusions of the manuscripts, Provenance). The Parts are: I Exact
commutation and resource algebra; II Canonical trace classes; III Compressed
repetition and accelerators; IV Polynomial trajectories; V Memory logs, RAM
and graph evaluation; VI Queues: tag systems and FIFO networks; VII
FRACTRAN, SKI and term rewriting; VIII Other substrates; IX The boundary of
fixed-arity compression.

The full pins are `e8bb0931d67f80d9fce87a8cddb0f661ff19f956` (01–06) and
`725d2ebb6909fe11a13a92354c0f47367a3cbbf5` (07). The pin of 07 is the commit
in which 01–03 arrived; 07 was written after 04 and 06, names them by title
as its companion manuscripts, and arrived after this report was placed but
before it was written. The batch-60 placement commit `7498484af` also placed
the neighbouring report of this category (batch-60 manuscripts 07–09, not to
be confused with this report's 07).

What each manuscript contributes:

- **01** exact resource envelopes for every serialization of a repeated
  multiset of box-guarded integer translations; a single-fold quartic
  accelerator; a quartic whose natural roots are in bijection with the
  executable causal trace classes of Cartier–Foata height at most `H`;
  fixed phases and powers of fixed noncommuting words; rank and progress
  criteria; and the equivalence between a fixed-arity single-fold universal
  halting polynomial and the general single-fold problem.
- **02** a single-fold quartic of `O((d+1)^3)` natural coordinates,
  independent of `T`, for `p(i) ≥ 0` on `{0,…,T}` (degree `d` fixed), with
  applications to polynomially iterable, unitriangular and unipotent affine
  updates, first-exit times and specified-input nontermination.
- **03** a quartic with `24L` witnesses and `22L+1` quadratic residuals for
  every zero-initialized memory-access log of length `L`, a sorting-network
  alternative with a size–height trade-off, parsimonious RAM composition,
  graph evaluation, counting and first-halting probabilities.
- **04** one natural zero per independent-swap class of bounded Petri
  executions; a first-applicable-fraction FRACTRAN compiler; a
  unique-witness SKI compiler for a fixed schedule; a deterministic-memory
  lower-bound family.
- **05** (base) a convex quadratic in `(2T+1)d + (7T+1)m` natural unknowns
  whose natural zeros are in bijection with the length-`T` executions of a
  Petri net modulo any sound static commutation relation, with interval
  guards and zero tests; the real zero set is a rational polytope; quartic
  and raw-run variants; counting hardness, Boolean-memory lower bounds and
  the finite-fold equivalence for a canonical universal trace verifier.
- **06** an exact resource-summary algebra, a Boolean signature for
  lexicographic trace normality with `S^2 = S^3`, a quartic compiler for
  nested repetition schedules, a root/trace-class bijection at fixed length,
  and the depth hierarchy (Presburger at depth one, universality of
  existential schedule parameterization at depth two, finite-fold and
  single-fold equivalences at depth four).
- **07** certificates for cyclic-tag and deletion-tag systems and fixed-read
  FIFO networks with one coordinate per consumed symbol and one uniquely
  determined guard slack, no intermediate queue being quantified; the
  first-failure product; a local quartic with `3T-2` coordinates; and a
  proof that faithful word memory with polynomial insertion at both ends
  needs two natural coordinates.

**Status.** The report is AI-assisted and unrefereed. None of its theorems
is formalized in Lean or Rocq, and no manuscript ships Lean or Rocq files.
The Python programs are finite exact checks of the implementations and
examples, not proofs; the proofs are the mathematical arguments of the
article.

## Files

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 196 pages
README.md                                this guide

01-causal-traces-RESEARCH_STATUS.md      manuscript 01's research and verification status, as delivered
01-causal-traces-SOURCE_AUDIT.md         manuscript 01's pin, inspected repository files and literature
02-poly-trajectories-sources.md          manuscript 02's pin and bibliographic provenance
03-linear-memory-SOURCE_PROVENANCE.md    manuscript 03's pin, consulted sources and claim status
04-witness-faithful-SOURCE_AUDIT.md      manuscript 04's source and scope audit
06-counter-schedules-repository_context.md  manuscript 06's repository snapshot and trust boundaries
07-queue-causality-lean_integration.md   manuscript 07's proposed Lean integration (not an implemented formalization)
07-queue-causality-provenance.md         manuscript 07's pin, literature and verification boundaries

code/01-causal-traces-causal_diophantine.py   exact semantics and the four compiler entry points
code/01-causal-traces-demo.py            the 11-witness large-count example (prints; writes no file)
code/01-causal-traces-verify.py          deterministic differential tests (seed 20260930); rewrites its examples and records
code/01-causal-traces-verify_exports.py  separate JSON coefficient checker (does not import the compiler)
code/02-poly-trajectories-certificates.py     sign-tower generator and endpoint checker (command line)
code/02-poly-trajectories-quartic_compiler.py positivity relation -> sum of squares of quadratic residuals
code/02-poly-trajectories-run_tests.py   regression tests (seed 20260930); writes four JSON files into the working directory
code/02-poly-trajectories-verify_export.py    separate assignment checker (prints JSON)
code/03-linear-memory-Makefile           manuscript 03's make targets (test, example, pdf, clean), delivery paths
code/03-linear-memory-canonical_memory.py     sparse polynomials and the low-height bitonic-network memory compiler
code/03-linear-memory-linear_memory.py   the linear-size large-base-product memory compiler
code/03-linear-memory-test_certificates.py    tests of the bitonic backend; rewrites its example and record
code/03-linear-memory-test_linear_memory.py   tests of the linear backend; rewrites its example and record
code/04-witness-faithful-diophantine_compiler.py  Petri, FRACTRAN and SKI compilers
code/04-witness-faithful-run_tests.py    finite checks; rewrites the four examples and its record
code/04-witness-faithful-verify_certificate.py    standalone JSON witness verifier (prints one JSON line per file)
code/05-trace-polytopes-build.py         manuscript 05's check-and-rebuild helper (do not run it here; see below)
code/05-trace-polytopes-demo.py          ordinary and zero-guarded examples; rewrites two result files
code/05-trace-polytopes-trace_polytope.py     exact compiler and witness checker
code/05-trace-polytopes-verify.py        finite checks against independent oracles; rewrites its results
code/06-counter-schedules-compiler.py    expression syntax, resource and normality summaries, quartic compiler
code/06-counter-schedules-substrates.py  polynomial/circuit-to-separated-schedule front end, 320 checks
code/06-counter-schedules-test_compiler.py    49,402 exact finite checks
code/06-counter-schedules-verify_export.py    independent evaluator of exported residuals (prints JSON)
code/07-queue-causality-Makefile         manuscript 07's make targets (pdf, test, examples, clean), delivery paths
code/07-queue-causality-compile_tag.py   general deletion-tag JSON front end
code/07-queue-causality-queue_certificates.py cyclic-tag and deletion-tag compilers (command line)
code/07-queue-causality-run_tests.py     exhaustive and seeded checks; rewrites five examples and its record
code/07-queue-causality-verify_certificate.py independent exact certificate evaluator (prints JSON)

data/01-causal-traces-build_validation.json   build and rendering record of the delivered 29-page PDF
data/01-causal-traces-canonical_history.json  32-witness, 48-residual causal-history polynomial and certificate
data/01-causal-traces-export_verification.json    recorded run of verify_exports.py
data/01-causal-traces-shared_resource_accelerator.json  11-witness, 18-residual, 76-monomial quartic and certificate
data/01-causal-traces-verification.json  recorded run of verify.py (Python 3.13.5)
data/01-causal-traces-verification.txt   the same run as text
data/02-poly-trajectories-huge_horizon_certificate.json  p(t) = (t - 10^50)^2, T = 10^100
data/02-poly-trajectories-independent_verification.json  recorded output of verify_export.py on quartic_example.json
data/02-poly-trajectories-interior_counterexample.json   p(t) = t^2 - 6t + 8, T = 6 (outer endpoints do not suffice)
data/02-poly-trajectories-quartic_example.json      template and assignment for p(t) = t^2 - 4t + 4, T = 6
data/02-poly-trajectories-test_report.json          recorded run of run_tests.py
data/03-linear-memory-build_validation.json         build record of the delivered 31-page PDF
data/03-linear-memory-example-certificate.json      four-event log, bitonic backend: certificate and assignment
data/03-linear-memory-example-events.json           the four-event log
data/03-linear-memory-example-polynomial.json       its expanded sum of squares
data/03-linear-memory-linear_example-certificate.json   the same log, linear backend (12 parameters, 96 witnesses, 89 residuals)
data/03-linear-memory-linear_example-events.json    the same log (identical to example-events.json)
data/03-linear-memory-linear_example-polynomial.json    its expanded sum of squares
data/03-linear-memory-linear_test_results.json      recorded run of test_linear_memory.py
data/03-linear-memory-linear_test_run.txt           its console output (identical bytes)
data/03-linear-memory-test_results.json             recorded run of test_certificates.py
data/03-linear-memory-test_run.txt                  its console output (identical bytes)
data/04-witness-faithful-certificate_verification.jsonl  recorded verifier output on the four examples
data/04-witness-faithful-fractran_first_halt.json   FRACTRAN first-halting certificate (103 variables, 120 residuals)
data/04-witness-faithful-petri_fork_join.json       Petri fork-join certificate (56 variables, 67 residuals)
data/04-witness-faithful-results.json               recorded run of run_tests.py
data/04-witness-faithful-ski_SKII.json              SKI certificate for SKII (13 variables, 11 residuals)
data/04-witness-faithful-ski_context.json           context-local SKI certificate (8 variables, 8 residuals)
data/05-trace-polytopes-demo_stdout.txt             recorded output of demo.py
data/05-trace-polytopes-example_guarded.json        exported zero-guarded certificate
data/05-trace-polytopes-example_quadratic.json      exported quadratic certificate
data/05-trace-polytopes-example_quartic.json        exported quartic certificate
data/05-trace-polytopes-example_raw.json            exported raw-run certificate
data/05-trace-polytopes-tiny_expanded_polynomial.txt    a small explicit expansion
data/05-trace-polytopes-verification.json           recorded run of verify.py
data/05-trace-polytopes-verification_stdout.txt     its console output (identical bytes)
data/05-trace-polytopes-witness_guarded.json        witness for example_guarded.json
data/05-trace-polytopes-witness_quadratic.json      witness for example_quadratic.json
data/05-trace-polytopes-witness_quartic.json        witness for example_quartic.json
data/05-trace-polytopes-witness_raw.json            witness for example_raw.json
data/06-counter-schedules-canonical_huge_witness.json    309-witness assignment; execution length has 221 digits
data/06-counter-schedules-canonical_multiplication_certificate.json  canonical polynomial (309 witnesses, 547 residuals)
data/06-counter-schedules-determinism_check.json    recorded comparison of two main-suite runs (hash seeds 1, 2)
data/06-counter-schedules-export_canonical_check.json   recorded verify_export.py output, canonical example
data/06-counter-schedules-export_resource_check.json    recorded verify_export.py output, resource-only example
data/06-counter-schedules-multiplication_certificate.json  resource-only polynomial (79 witnesses, 86 residuals)
data/06-counter-schedules-multiplication_witness.json      its 79-witness assignment
data/06-counter-schedules-pdf_quality.json          build and rendering record of the delivered 30-page PDF
data/06-counter-schedules-substrate_results.json    recorded run of substrates.py (320 checks)
data/06-counter-schedules-test_results.json         recorded run of test_compiler.py (49,402 checks)
data/07-queue-causality-quartic_example.json        T = 3 local quartic (7 variables, 9 residuals)
data/07-queue-causality-results.json                recorded run of run_tests.py
data/07-queue-causality-stream_example.json         T = 3 stream certificate (4 variables, 6 residuals)
data/07-queue-causality-ternary_tag_example.json    certificate for the ternary 2-tag program (5 variables)
data/07-queue-causality-ternary_tag_spec.json       that program's specification
data/07-queue-causality-uncausal_counterexample.json    word balance without a legal execution
data/07-queue-causality-zero_slack_example.json     T = 3 zero-slack certificate (3 variables)
```

The directory holds 97 files: 11 at the root (the article, its PDF, this
README and eight provenance and audit files), 29 in `code/` and 57 in
`data/`. Per manuscript: 01 has 12 files, 02 10, 03 17, 04 10, 05 16
besides the replaced `article.tex` and `README.md`, 06 15, 07 14. Every file
except `article.tex`, `article.pdf` and `README.md` is byte-identical to the
delivery.

## Labels

Every label in `article.tex` carries the prefix `cdc:`. Labels of manuscript
05 (the base) take the prefix alone (`cdc:thm:main`); those of the other
manuscripts take a sub-prefix:

| Manuscript | Sub-prefix | Example |
|---|---|---|
| 01 | `cdc:ct:` | `cdc:ct:thm:universal` |
| 02 | `cdc:pt:` | `cdc:pt:prop:height` |
| 03 | `cdc:mem:` | `cdc:mem:prop:lower` |
| 04 | `cdc:wf:` | `cdc:wf:thm:petri` |
| 05 | `cdc:` | `cdc:thm:quartic` |
| 06 | `cdc:cs:` | `cdc:cs:thm:tracebijection` |
| 07 | `cdc:qc:` | `cdc:qc:thm:stream` |

Labels written in the merge use `cdc:conv:` (the Conventions section),
`cdc:bd:` (merged statements of Part IX, such as the universal-halting
equivalence `cdc:bd:thm:universal` and the no-computable-witness-bound
proposition `cdc:bd:prop:nobound`), `cdc:part:` (the nine Parts),
`cdc:sec:` (the back-matter sections, for example `cdc:sec:validation`,
`cdc:sec:formal`, `cdc:sec:questions`, `cdc:sec:provenance`; base 05's own
thirteen section labels also begin `cdc:sec:`) and `cdc:q:` (merged
research questions). Labels written in the merge also include section labels in a manuscript's own namespace where that manuscript left a section unlabelled (`cdc:wf:sec:interfaces`, `cdc:wf:sec:monitor`, `cdc:wf:sec:ski`, `cdc:wf:sec:frontier`, `cdc:pt:sec:problem`, `cdc:pt:sec:firsthalt`, `cdc:pt:sec:limits`, `cdc:qc:sec:words`) and two remarks (`cdc:bd:rem:sfu`, `cdc:qc:rem:tagnotes`).

Label counts (pattern `\\label(\[[^]]*\])?\{`): the placed `article.tex` (manuscript 05 as delivered) had 70 labels, all bare. The written article has 523: all 475 labels of the seven manuscripts (01 74, 02 59, 03 76, 04 65, 05 70, 06 77, 07 54), each with its prefix and none dropped, and 48 labels written in the merge. None is duplicated. Where a duplicated statement is printed once, the labels of the statements it replaces sit on the merged statement (`cdc:thm:boundary`, `cdc:ct:thm:universal`, `cdc:mem:thm:compression` and `cdc:wf:thm:universal` on `cdc:bd:thm:universal`; `cdc:prop:noheight`, `cdc:ct:prop:no-bound`, `cdc:pt:prop:height`, `cdc:mem:prop:no-bound` and `cdc:wf:thm:height-obstruction` on `cdc:bd:prop:nobound`), and the section labels of the manuscripts' research-question sections sit on the merged Research questions section, so every reference resolves.

Text written during the merge is marked `[write]` in the article.

## Delivered names and shipped names

Delivered paths are relative to each manuscript's package root (the inner
directory of its archive). Base 05's `README.md` and `article.tex` were
staged unprefixed and are replaced in place by this README and the merged
article; the delivered texts survive at the placement commit `7498484af`
and in the arrival commit `c1f56f842`.

**Manuscript 01** (package root `Diophantine_Causal_Computation/`)

| Delivered | Shipped |
|---|---|
| `RESEARCH_STATUS.md` | `01-causal-traces-RESEARCH_STATUS.md` |
| `SOURCE_AUDIT.md` | `01-causal-traces-SOURCE_AUDIT.md` |
| `code/causal_diophantine.py` | `code/01-causal-traces-causal_diophantine.py` |
| `code/demo.py` | `code/01-causal-traces-demo.py` |
| `code/verify.py` | `code/01-causal-traces-verify.py` |
| `code/verify_exports.py` | `code/01-causal-traces-verify_exports.py` |
| `data/build_validation.json` | `data/01-causal-traces-build_validation.json` |
| `data/export_verification.json` | `data/01-causal-traces-export_verification.json` |
| `data/verification.json` | `data/01-causal-traces-verification.json` |
| `data/verification.txt` | `data/01-causal-traces-verification.txt` |
| `examples/canonical_history.json` | `data/01-causal-traces-canonical_history.json` |
| `examples/shared_resource_accelerator.json` | `data/01-causal-traces-shared_resource_accelerator.json` |

**Manuscript 02** (package root `canonical_diophantine_certificates/`; flat)

| Delivered | Shipped |
|---|---|
| `certificates.py` | `code/02-poly-trajectories-certificates.py` |
| `huge_horizon_certificate.json` | `data/02-poly-trajectories-huge_horizon_certificate.json` |
| `independent_verification.json` | `data/02-poly-trajectories-independent_verification.json` |
| `interior_counterexample.json` | `data/02-poly-trajectories-interior_counterexample.json` |
| `quartic_compiler.py` | `code/02-poly-trajectories-quartic_compiler.py` |
| `quartic_example.json` | `data/02-poly-trajectories-quartic_example.json` |
| `run_tests.py` | `code/02-poly-trajectories-run_tests.py` |
| `sources.md` | `02-poly-trajectories-sources.md` |
| `test_report.json` | `data/02-poly-trajectories-test_report.json` |
| `verify_export.py` | `code/02-poly-trajectories-verify_export.py` |

**Manuscript 03** (package root `ProveIt_Diophantine_Certificates/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/03-linear-memory-Makefile` |
| `SOURCE_PROVENANCE.md` | `03-linear-memory-SOURCE_PROVENANCE.md` |
| `artifacts/build_validation.json` | `data/03-linear-memory-build_validation.json` |
| `artifacts/example/certificate.json` | `data/03-linear-memory-example-certificate.json` |
| `artifacts/example/events.json` | `data/03-linear-memory-example-events.json` |
| `artifacts/example/polynomial.json` | `data/03-linear-memory-example-polynomial.json` |
| `artifacts/linear_example/certificate.json` | `data/03-linear-memory-linear_example-certificate.json` |
| `artifacts/linear_example/events.json` | `data/03-linear-memory-linear_example-events.json` |
| `artifacts/linear_example/polynomial.json` | `data/03-linear-memory-linear_example-polynomial.json` |
| `artifacts/linear_test_results.json` | `data/03-linear-memory-linear_test_results.json` |
| `artifacts/linear_test_run.txt` | `data/03-linear-memory-linear_test_run.txt` |
| `artifacts/test_results.json` | `data/03-linear-memory-test_results.json` |
| `artifacts/test_run.txt` | `data/03-linear-memory-test_run.txt` |
| `code/canonical_memory.py` | `code/03-linear-memory-canonical_memory.py` |
| `code/linear_memory.py` | `code/03-linear-memory-linear_memory.py` |
| `code/test_certificates.py` | `code/03-linear-memory-test_certificates.py` |
| `code/test_linear_memory.py` | `code/03-linear-memory-test_linear_memory.py` |

**Manuscript 04** (package root `diophantine_substrates/`)

| Delivered | Shipped |
|---|---|
| `code/diophantine_compiler.py` | `code/04-witness-faithful-diophantine_compiler.py` |
| `code/verify_certificate.py` | `code/04-witness-faithful-verify_certificate.py` |
| `examples/fractran_first_halt.json` | `data/04-witness-faithful-fractran_first_halt.json` |
| `examples/petri_fork_join.json` | `data/04-witness-faithful-petri_fork_join.json` |
| `examples/ski_SKII.json` | `data/04-witness-faithful-ski_SKII.json` |
| `examples/ski_context.json` | `data/04-witness-faithful-ski_context.json` |
| `research/SOURCE_AUDIT.md` | `04-witness-faithful-SOURCE_AUDIT.md` |
| `tests/certificate_verification.jsonl` | `data/04-witness-faithful-certificate_verification.jsonl` |
| `tests/results.json` | `data/04-witness-faithful-results.json` |
| `tests/run_tests.py` | `code/04-witness-faithful-run_tests.py` |

**Manuscript 05** (package root `canonical_trace_polytopes/`; the base)

| Delivered | Shipped |
|---|---|
| `README.md` | `README.md` (replaced by this README) |
| `article.tex` | `article.tex` (replaced by the merged article) |
| `build.py` | `code/05-trace-polytopes-build.py` |
| `code/demo.py` | `code/05-trace-polytopes-demo.py` |
| `code/trace_polytope.py` | `code/05-trace-polytopes-trace_polytope.py` |
| `code/verify.py` | `code/05-trace-polytopes-verify.py` |
| `results/demo_stdout.txt` | `data/05-trace-polytopes-demo_stdout.txt` |
| `results/example_guarded.json` | `data/05-trace-polytopes-example_guarded.json` |
| `results/example_quadratic.json` | `data/05-trace-polytopes-example_quadratic.json` |
| `results/example_quartic.json` | `data/05-trace-polytopes-example_quartic.json` |
| `results/example_raw.json` | `data/05-trace-polytopes-example_raw.json` |
| `results/tiny_expanded_polynomial.txt` | `data/05-trace-polytopes-tiny_expanded_polynomial.txt` |
| `results/verification.json` | `data/05-trace-polytopes-verification.json` |
| `results/verification_stdout.txt` | `data/05-trace-polytopes-verification_stdout.txt` |
| `results/witness_guarded.json` | `data/05-trace-polytopes-witness_guarded.json` |
| `results/witness_quadratic.json` | `data/05-trace-polytopes-witness_quadratic.json` |
| `results/witness_quartic.json` | `data/05-trace-polytopes-witness_quartic.json` |
| `results/witness_raw.json` | `data/05-trace-polytopes-witness_raw.json` |

**Manuscript 06** (package root `diophantine_counter_programs/`)

| Delivered | Shipped |
|---|---|
| `code/compiler.py` | `code/06-counter-schedules-compiler.py` |
| `code/substrates.py` | `code/06-counter-schedules-substrates.py` |
| `code/test_compiler.py` | `code/06-counter-schedules-test_compiler.py` |
| `code/verify_export.py` | `code/06-counter-schedules-verify_export.py` |
| `examples/canonical_huge_witness.json` | `data/06-counter-schedules-canonical_huge_witness.json` |
| `examples/canonical_multiplication_certificate.json` | `data/06-counter-schedules-canonical_multiplication_certificate.json` |
| `examples/multiplication_certificate.json` | `data/06-counter-schedules-multiplication_certificate.json` |
| `examples/multiplication_witness.json` | `data/06-counter-schedules-multiplication_witness.json` |
| `repository_context.md` | `06-counter-schedules-repository_context.md` |
| `verification/determinism_check.json` | `data/06-counter-schedules-determinism_check.json` |
| `verification/export_canonical_check.json` | `data/06-counter-schedules-export_canonical_check.json` |
| `verification/export_resource_check.json` | `data/06-counter-schedules-export_resource_check.json` |
| `verification/pdf_quality.json` | `data/06-counter-schedules-pdf_quality.json` |
| `verification/substrate_results.json` | `data/06-counter-schedules-substrate_results.json` |
| `verification/test_results.json` | `data/06-counter-schedules-test_results.json` |

**Manuscript 07** (package root `Causal_Diophantine_Queue_Compilation/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/07-queue-causality-Makefile` |
| `code/compile_tag.py` | `code/07-queue-causality-compile_tag.py` |
| `code/queue_certificates.py` | `code/07-queue-causality-queue_certificates.py` |
| `code/verify_certificate.py` | `code/07-queue-causality-verify_certificate.py` |
| `examples/quartic_example.json` | `data/07-queue-causality-quartic_example.json` |
| `examples/stream_example.json` | `data/07-queue-causality-stream_example.json` |
| `examples/ternary_tag_example.json` | `data/07-queue-causality-ternary_tag_example.json` |
| `examples/ternary_tag_spec.json` | `data/07-queue-causality-ternary_tag_spec.json` |
| `examples/uncausal_counterexample.json` | `data/07-queue-causality-uncausal_counterexample.json` |
| `examples/zero_slack_example.json` | `data/07-queue-causality-zero_slack_example.json` |
| `notes/lean_integration.md` | `07-queue-causality-lean_integration.md` |
| `notes/provenance.md` | `07-queue-causality-provenance.md` |
| `tests/results.json` | `data/07-queue-causality-results.json` |
| `tests/run_tests.py` | `code/07-queue-causality-run_tests.py` |

**Not shipped.** The manuscripts (`article.tex`) and delivery READMEs of
members 01, 02, 03, 04, 06 and 07: they survive in their arrival commits
(`725d2ebb6` for 01–03, `c1f56f842` for 04 and 06, `b998f70c6` for 07), as
members of the committed archives. All seven delivered PDFs, likewise
recoverable from the arrival commits. The checksum ledgers, each verified
against the fresh extraction and then retired: 04 `MANIFEST.sha256` (13/13),
05 `SHA256SUMS.txt` (19/19), 06 `SHA256SUMS.txt` (18/18) and 07 `SHA256SUMS`
(17/17). Manuscripts 01, 02 and 03 delivered no ledger.

## What is claimed and what is not

The report claims the theorems of the seven manuscripts, with the proofs
printed in the article: bijections between the natural zeros of explicit
integer polynomials and bounded executions, trace classes or logs of the
substrates listed above, with one witness per execution or class, exact
variable, residual and degree counts, and the lower bounds and equivalences
stated there. It does not claim the following. Each item is stated by at
least the manuscripts named; the article keeps every one of them.

- **No priority.** No manuscript establishes historical or literature-wide
  priority for its constructions (01's status paragraph and
  `RESEARCH_STATUS.md`; 02's relation to prior work and `sources.md`; 03's
  status table and `SOURCE_PROVENANCE.md`; 04's status and
  `SOURCE_AUDIT.md`; 05's status box; 06's title page and
  `repository_context.md`; 07's abstract, relation to earlier work and
  `provenance.md`). Their literature searches were targeted, and a search
  that finds nothing is not evidence of novelty (03, 07). The classical
  ingredients (MRDP, machine arithmetization, sums of squares, circuit
  quadratization, Cartier–Foata and forbidden-factor normal forms, sorting
  networks and sorted-memory verification, radix encodings, finite-table
  interpolation, polynomial centralizers, pairing) are not claimed.
- **Not formal.** No new Lean, Rocq or Coq proof was written or compiled,
  the repository's Lean build and axiom audits were not rerun, and
  repository documentation is not treated as a kernel audit (all seven).
  07's `lean_integration.md` and the formalization sections of 01, 03, 04
  and 05 are proposals; 03's module names are "proposals, not files claimed
  to exist". The Python programs are finite exact checks: they do not prove
  soundness for all inputs, completeness for arbitrary horizons, global
  uniqueness or optimality of the arity bounds (the validation sections of
  01, 02, 04 and 07, and 06's "Limitations").
- **The universal problem is reduced, not solved.** No manuscript resolves
  the general single-fold or finite-fold Diophantine representation
  problem, and none gives a fixed-arity single-fold or finite-fold
  representation of unbounded (universal) halting. Part IX proves that a
  fixed-arity single-fold (finite-fold) universal halting polynomial exists
  if and only if every c.e. set has a single-fold (finite-fold)
  representation: a reduction to the open problem, not a solution of it.
  01, 03, 04, 05 and 06 each prove a form of this equivalence (06 for its
  separated one-counter schedules of depth four), printed once; 07 states
  the distinction without proving the equivalence, and 02 separates its
  restricted theorem from a universal first-halting extension.
- **Families, not fixed arity.** Every construction is a family indexed by
  a horizon, height, log length or schedule, whose number of variables grows
  with that parameter: 01's causal height `H` is a compiler parameter
  ("a family of ordinary polynomials, not one fixed-arity polynomial"), and
  representing the union over all `H` by MRDP preserves none of the root
  bijections; 03's single-fold statement is for each fixed log length; 05 is
  "a bounded-horizon theorem package"; 04's counts do not compete with
  universal polynomial pairs or with the project's optimized straight-line
  certificates; 07's horizon `T` is a construction parameter, and its
  witness bound supplies no computable bound on an unknown halting time,
  nor is an `O(T)` circuit small in `log T`. No construction improves the
  project's 75-operation universal certificate, which counts arithmetic
  operations, not witnesses (01's `RESEARCH_STATUS.md`; 04's integration
  section).
- **Real relaxation is not integral.** 05's quadratic has a real zero set
  that is a bounded rational polytope, but that polytope need not be
  integral: its example of a nonempty polytope with no lattice point shows
  that linear programming can find a fractional point and decide nothing
  about a genuine execution. Convexity is not an algorithm for the natural
  zeros.
- **01, scope.** The causal-history polynomial has one root per genuine
  trace: it removes duplicate interleavings, not distinct histories. The
  eleven witnesses of the worked accelerator are not claimed optimal.
  Complete finite enumeration at bounded height is a size statement, not a
  practical solver. There is no full SKI/Iota evaluation compiler (only a
  local head-rule component), and no efficient algorithm for arbitrary
  Diophantine equations. Independence means equality of partial sequential
  maps, not simultaneous token reservation.
- **02, scope.** The certificates do not decide global termination: a
  uniform procedure for "every initial state terminates" would decide a
  Hilbert's-tenth solvability problem. The construction does not introduce
  polynomial loop acceleration, closed forms or input-dependent termination
  bounds (Hark–Frohn–Giesl, Lommen–Meyer–Giesl), and its canonical
  arithmetic gadgets are not claimed new (Cantone–Cuzziol–Omodeo). The
  implementation counts (849 witnesses, 1,218 residuals for the degree-two
  example) are deliberately unoptimized, not minimal or universal-record
  claims. The code implements the sign-certificate core only, not automatic
  source recognition, the Boolean program front end or the fixed-period
  affine front end. The JSON checker certifies an assignment, not compiler
  correctness or uniqueness. A universal first-halting extension or a
  single-fold polynomial graph of `2^n` would cross a different boundary.
- **03, scope.** The comparison-network lower bound is optimal only within
  the sorting-network architecture; it is not a lower bound for arbitrary
  Diophantine encodings, and it does not show that Batcher's extra
  logarithmic factor is necessary. Source determinism removes multiple
  bounded executions but says nothing about the fibres of a fixed-variable
  arithmetization of arbitrary run length. Complete RAM, combinator,
  cellular and probabilistic front ends are not implemented. Full
  abstraction of the repository's lambda-to-combinator translations is not
  established. The linear backend's scalar size is linear, not its bit cost.
- **04, scope.** A Petri candidate firing word may be valid but
  noncanonical; its constructed assignment then has nonzero energy, as
  intended. SKI schedules are external rule/path lists: there is no
  linear-size compiler for existentially chosen unbounded paths. No
  general Diophantine solver, no new universal-variable records, and no
  full abstraction of the repository compiler chains.
- **05, scope.** The cellular-automaton and bounded-rewriting front ends are
  described and justified mathematically, not supplied as standalone
  translators. The repository was inspected, not rebuilt, and no result
  relies on an unverified numerical optimization in it.
- **06, scope.** Its universality is universality of **existential schedule
  parameterization** (globally shared parameters at depth two), not
  undecidability of ordinary unrestricted one-counter or Petri-net
  reachability. Single-foldness holds with all repetition parameters fixed.
  The canonicality filter tests whether the given expansion is canonical;
  it is not a normalizer and does not preserve existential reachability for
  every restricted schedule language. The trace-class bijection at fixed
  length has no polynomial-export front end in the prototype. Resource counts
  do not encode FIFO order. The prototype uses syntax trees, not DAG
  sharing, expands separated-scheme coefficients in unary, and its witness
  counts are not minimal. No cubic Diophantine classification is claimed.
- **07, scope.** The verifier checks that a supplied witness is a zero of
  the exported polynomial; it does not certify semantic correctness or
  uniqueness of an untrusted compiler output. Its DAG degree bound is
  conservative: the stream example reports 6, while the simplified
  polynomial has degree 4. The fixed-read FIFO-network theorem is proved,
  but the network-table compiler is not implemented; the shipped compilers
  cover cyclic-tag and one-queue deletion-tag systems. No universal
  optimality is claimed (a compiler that simulates the run could output the
  constant 0 or 1), the guard variable is not logically unavoidable, and
  the witness-height bound is an upper bound. The word-memory lower bound
  concerns faithful natural-number word codes with fixed polynomial
  insertion maps: it excludes neither conditional, floor, division or
  prime-exponent operations, nor finite sets of lengths, hidden control
  state, or continuous and rational encodings; switched affine dynamics do
  not make one everywhere-polynomial scalar map universal. No lower bound on
  the number of variables of arbitrary Diophantine representations is
  asserted, and no direct `T+1`-variable polynomial for an arbitrary `T`-step
  Rule 110 space-time diagram. Its research questions are not claimed to be
  established open problems, except the finite-fold one.

## Relation to the formal project

The report continues the Lean project `Computability/HilbertTenthProblem`.
It uses the project's existence interfaces `Diophantine.boundedForall_dioph`,
`Diophantine.exactIter_dioph` and `Diophantine.existsExactIter_dioph`
(`Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`)
and MRDP (`Diophantine.mrdp`, `Diophantine.mrdp_iff` in
`Lean/Diophantine/MRDP.lean`; this and the Lean paths below are relative to
`Computability/HilbertTenthProblem`) only as context: they assert that
representations exist and say nothing about how many witnesses a
representation has. The project formalizes the single-fold exponential
representation of Jones and Matiyasevich: `JM1984.RM.re_sfu` and
`JM1984.RM.re_single_equation` (`Lean/Diophantine/Paper1984/DPR.lean`), with
the predicate `JM1984.Exp.SFU` (`Lean/Diophantine/Paper1984/ExpDioph.lean`)
and the uniqueness lemma `JM1984.RM.sysQ_unique`
(`Lean/Diophantine/Paper1984/ExpSys.lean`); this report cites that
representation as a classical input. None of the report's own theorems is
formalized in Lean or Rocq, and the Python programs are finite checks, not
proofs. Placing the report beside a Lean development confers no formal
status on it.

Part VI also borders the project's tag-system route: the Lean certificate
for Jones's 1980 Theorem 5 stores intermediate queues as content and length
marker (`Jones1980.length_step'`, `Jones1980.content_step'` in
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/TagHistory.lean`),
and the project's notes
`Papers/1980/EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md` and
`EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md` treat causal prefixes and global
stream identities for operation-counted certificates. Part VI's theorems are
not formalized.

The manuscripts inspected the project at their pins; no file under
`Computability/HilbertTenthProblem` has changed between `e8bb0931d` and the
write, so their descriptions of it are current. 01, 03 and 04 also read
`Computability/CombinatoryLogic/README.md`, and 04 read
`Computability/CombinatoryLogic/Coq/SKPolynomial.v`, whose "polynomials" are
applicative SK terms, not Diophantine polynomials.

The other report of this category,
[probabilistic-quantum-and-continuous-computation](../probabilistic-quantum-and-continuous-computation/)
(`pqc:`), treats the Diophantine representability of probabilistic, quantum
and continuous computation and shares no theorem with this one.

## Build

pdfLaTeX, with the packages loaded in `article.tex` (base 05's preamble
plus `float`: fontenc, inputenc, amsmath, amsthm, mathtools, newtxtext,
newtxmath, geometry, microtype, booktabs, array, longtable, tabularx, float,
xcolor, enumitem, listings, fancyhdr, titlesec, tcolorbox, xurl, hyperref,
aliascnt and cleveref). The bibliography is internal; no BibTeX, external figures or
downloads are needed. Build in a scratch copy, so that no auxiliary file
lands in the collection:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build has 196 pages.

## Rerunning the checks

Every suite needs Python 3.10 or later and the standard library only. Every
suite rewrites its recorded outputs at fixed paths relative to its own
location, and most scripts import their siblings by delivered name, so run
them **on a copy with the delivered layout**, never in the report
directory. The recipes below build such copies, `r01` … `r07`, beside
`code/` and `data/`: run them in a scratch copy of the report directory
(copying `code/` and `data/` is enough), not in the collection. Where the
Windows `python` alias does not resolve, use `py`.

```sh
# 01: rewrites r01/examples/*.json and r01/data/{verification.json,verification.txt,export_verification.json}
mkdir -p r01/code
for f in causal_diophantine demo verify verify_exports; do cp code/01-causal-traces-$f.py r01/code/$f.py; done
(cd r01 && python code/demo.py && python code/verify.py && python code/verify_exports.py)

# 02: writes four JSON files into r02, then the independent check
mkdir -p r02
for f in certificates quartic_compiler run_tests verify_export; do cp code/02-poly-trajectories-$f.py r02/$f.py; done
(cd r02 && python run_tests.py && python verify_export.py quartic_example.json > independent_verification.json)

# 03: rewrites r03/artifacts/{example,linear_example}/ and the two test records
mkdir -p r03/code r03/artifacts
for f in canonical_memory linear_memory test_certificates test_linear_memory; do cp code/03-linear-memory-$f.py r03/code/$f.py; done
(cd r03 && python code/test_certificates.py > artifacts/test_run.txt && python code/test_linear_memory.py > artifacts/linear_test_run.txt)

# 04: rewrites r04/examples/*.json and r04/tests/results.json
mkdir -p r04/code r04/tests
for f in diophantine_compiler verify_certificate; do cp code/04-witness-faithful-$f.py r04/code/$f.py; done
cp code/04-witness-faithful-run_tests.py r04/tests/run_tests.py
(cd r04 && python tests/run_tests.py && python code/verify_certificate.py examples/fractran_first_halt.json examples/petri_fork_join.json examples/ski_SKII.json examples/ski_context.json > tests/certificate_verification.jsonl)

# 05: rewrites r05/results/ (run without -O: the assertions are the checks)
mkdir -p r05/code r05/results
for f in trace_polytope verify demo; do cp code/05-trace-polytopes-$f.py r05/code/$f.py; done
(cd r05 && python -B code/verify.py > results/verification_stdout.txt && python -B code/demo.py > results/demo_stdout.txt)

# 06: rewrites r06/verification/{test_results,substrate_results}.json
mkdir -p r06/code r06/verification r06/examples
for f in compiler substrates test_compiler verify_export; do cp code/06-counter-schedules-$f.py r06/code/$f.py; done
for f in multiplication_certificate multiplication_witness canonical_multiplication_certificate canonical_huge_witness; do cp data/06-counter-schedules-$f.json r06/examples/$f.json; done
(cd r06 && python code/test_compiler.py && python code/substrates.py \
  && python code/verify_export.py examples/multiplication_certificate.json examples/multiplication_witness.json > verification/export_resource_check.json \
  && python code/verify_export.py examples/canonical_multiplication_certificate.json examples/canonical_huge_witness.json > verification/export_canonical_check.json)

# 07: rewrites five r07/examples/*.json and r07/tests/results.json
mkdir -p r07/code r07/tests r07/examples
for f in queue_certificates compile_tag verify_certificate; do cp code/07-queue-causality-$f.py r07/code/$f.py; done
cp code/07-queue-causality-run_tests.py r07/tests/run_tests.py
cp data/07-queue-causality-ternary_tag_spec.json r07/examples/ternary_tag_spec.json
(cd r07 && python tests/run_tests.py && for e in stream quartic zero_slack ternary_tag; do python code/verify_certificate.py examples/${e}_example.json; done)
```

The shell redirections reproduce the recorded console files
(`*_run.txt`, `verification_stdout.txt`, `demo_stdout.txt`,
`certificate_verification.jsonl`, `independent_verification.json`, the two
`export_*_check.json`), which the scripts print but do not write. 04's
verifier prints one line per file in argument order; the recorded file lists
the examples alphabetically, as the delivered README's `examples/*.json`
expands. 07's general-tag front end can also be run on the shipped
specification:
`(cd r07 && python code/compile_tag.py --spec examples/ternary_tag_spec.json --output custom_tag.json)`
reproduces `ternary_tag_example.json`. Four recorded files have no script
that writes them: 01's and 03's `build_validation.json` and 06's
`pdf_quality.json` describe the delivered PDFs, and 06's
`determinism_check.json` records two runs of `test_compiler.py` under
`PYTHONHASHSEED` 1 and 2 compared without their elapsed times.

**Expected results.** In the merge every recipe was run as printed on a
scratch copy of the shipped `code/` and `data/` (Python 3.14.4, Windows),
and every regenerated file was compared with the shipped one after removing
carriage returns. All seven suites passed. Identical: 01's two examples and
`export_verification.json`; 02's four JSON files other than
`test_report.json`, and `independent_verification.json`; 03's six example
files; 04's four examples and `certificate_verification.jsonl`; 05's twelve
result files other than `verification.json` and `verification_stdout.txt`;
06's `substrate_results.json` and both export checks; 07's five examples and
`results.json` (`"status": "all exact checks passed"`; the four
certificates accepted with energy 0 and variables/residuals/degree bound
4/6/6, 7/9/4, 3/8/8 and 5/7/8). The other records differ only in elapsed
times and, for 01, in the Python version (3.13.5 recorded). The
`compile_tag.py` command above also reproduced `ternary_tag_example.json`.

**Hazards.**

- On Windows the regenerated files have CRLF line endings; the shipped
  files have LF. Compare with line endings normalized.
- Every suite overwrites its recorded outputs at paths fixed relative to the
  script (the parent of the script's directory in 01, 03, 04, 05, 06 and
  07; the working directory in 02). The shipped `code/` scripts that import
  a sibling fail at that import, because the siblings carry prefixes; an
  unprefixed copy placed in the report directory would write into
  `examples/`, `data/`, `artifacts/`, `results/`, `tests/` or
  `verification/` there. 01's `verify_exports.py` finds no `examples/` in
  the report and stops with an error.
- Do not run `code/05-trace-polytopes-build.py` here. It runs `verify.py` and
  `demo.py` from `code/` below its own directory and then `pdflatex` three
  times on `article.tex` in its own directory. As shipped it stops at once
  (`code/code/verify.py` does not exist; tested on a copy). A copy at the
  report root run with `--skip-tests` would run `pdflatex` three times on
  `article.tex`, which is now the merged article, in the report directory,
  overwriting `article.pdf` and leaving auxiliary files there. Use the
  recipe above; inside `r05`,
  `cp ../code/05-trace-polytopes-build.py build.py && python build.py --verify-only`
  runs the same two checks.
- The two Makefiles (`code/03-linear-memory-Makefile`,
  `code/07-queue-causality-Makefile`) use delivery paths and a `pdf` target
  that runs `pdflatex` on `article.tex`; do not use them here. GNU make is
  not installed on this machine in any case.
- The command-line compilers write where they are told: 03's
  `canonical_memory.py` and `linear_memory.py` (an output directory), 07's
  `queue_certificates.py` and `compile_tag.py` (`--output`) and 02's
  `certificates.py` (`--output`). 02's `quartic_compiler.py` and 06's
  `compiler.py` write `quartic.json` and `multiplication_certificate.json`
  into the working directory unless given `--output` or `--export`. Give
  them paths outside the report. 03's linear backend can exceed Python's
  decimal string limit for large logs (`PYTHONINTMAXSTRDIGITS=0` lifts it, for
  trusted input only).

## Disclosures

- **Shipped text that uses delivery names or names unshipped files.**
  - `01-causal-traces-RESEARCH_STATUS.md` and `01-causal-traces-SOURCE_AUDIT.md`
    speak of "the article", "the paper" and "the new report": manuscript 01's
    delivered text, now merged. They name no paths.
  - `02-poly-trajectories-sources.md` names `article.tex` (manuscript 02's,
    not shipped).
  - `03-linear-memory-SOURCE_PROVENANCE.md` names "this archive" and
    `artifacts/` (now `data/03-linear-memory-*`).
  - `04-witness-faithful-SOURCE_AUDIT.md` speaks of "this package" and "the
    compiled article", which is not shipped.
  - `06-counter-schedules-repository_context.md` speaks of "the article",
    manuscript 06's delivered text.
  - `07-queue-causality-provenance.md` names `article.tex`, `article.pdf`,
    "this ZIP", `tests/run_tests.py` and `tests/results.json` (now
    `code/07-queue-causality-run_tests.py` and
    `data/07-queue-causality-results.json`);
    `07-queue-causality-lean_integration.md` speaks of "the package".
    07's manuscript text calls it `notes/lean_integration.md`.
  - `code/03-linear-memory-Makefile` uses `code/…`, `artifacts/…` and
    `article.tex`; `code/07-queue-causality-Makefile` uses `code/…`,
    `examples/…`, `tests/run_tests.py` and `article.tex`;
    `code/05-trace-polytopes-build.py` uses `code/verify.py`,
    `code/demo.py` and `article.tex`.
  - Every script uses delivery names in its imports and paths: 01
    (`causal_diophantine`; `examples/`, `data/`), 02 (`certificates`,
    `quartic_compiler`; the four JSON names in the working directory), 03
    (`canonical_memory`, `linear_memory`; `artifacts/…`), 04
    (`code/` on `sys.path`, `diophantine_compiler`; `examples/`,
    `tests/results.json`), 05 (`trace_polytope`; `results/`), 06
    (`compiler`; `verification/…`), 07 (`code/` on `sys.path`,
    `queue_certificates`, `verify_certificate`; `examples/…`,
    `tests/results.json`).
  - Recorded data that names delivery files: 03's `build_validation.json`
    (`code/test_certificates.py`, `code/test_linear_memory.py`), 01's
    `export_verification.json` and 04's `certificate_verification.jsonl`
    (bare example names). 01's and 03's `build_validation.json` and 06's
    `pdf_quality.json` describe the delivered 29-, 31- and 30-page PDFs,
    which are not shipped.
- **Byte-identical duplicates within a manuscript** (checked with `cmp`):
  03's `test_results.json` and `test_run.txt`, `linear_test_results.json`
  and `linear_test_run.txt`, and `example-events.json` and
  `linear_example-events.json`; 05's `verification.json` and
  `verification_stdout.txt`. The console files are the scripts' printed
  JSON. No two files of different manuscripts are identical.
- **Missing final newlines.** Four of 06's JSON files end without a newline
  and are kept so: `canonical_huge_witness.json`,
  `canonical_multiplication_certificate.json`,
  `multiplication_certificate.json` and `multiplication_witness.json`.
- **Same delivered names, different files.** 04 and 07 both delivered
  `tests/results.json`, `tests/run_tests.py` and `code/verify_certificate.py`;
  they are different files, told apart only by their prefixes
  (`code/04-witness-faithful-verify_certificate.py` checks lists of
  sum-of-squares residuals, `code/07-queue-causality-verify_certificate.py`
  evaluates arithmetic DAGs). Likewise 02 and 06 each have a
  `verify_export.py`, 01 and 05 a `code/verify.py`, 02 a `run_tests.py`,
  03 and 06 a `test_results.json`, and 02 and 07 a `quartic_example.json`;
  all are different programs or data.
- **Two Cantone–Cuzziol–Omodeo papers.** 02, 04, 05 and 06 cite
  Cantone, Cuzziol and Omodeo, *On Diophantine singlefold specifications*,
  Le Matematiche 79(2) (2024), 585–620 (merged key `cco2024`). 07 cites a
  different paper by the same authors, *Six equations in search of a
  finite-fold-ness proof*, arXiv:2303.02208 (version 3, 2024; key
  `cco-six`). 01 cites a third, Cantone, Casagrande, Fabris and Omodeo,
  *Does every recursively enumerable set admit a finite-fold Diophantine
  representation?* (CEUR Workshop Proceedings 2396, 2019; key `ccfo2019`).
  03 cites none of them. The bibliography keeps all three.
- **Pins.** 01–06 inspected `e8bb0931d` and 07 inspected `725d2ebb6`; their
  statements about the repository are those of their pins. 06's
  `repository_context.md` says that its document reads were made on the
  main branch during the inspection that returned that tree, not from a
  checkout of the pinned tree; 01's `SOURCE_AUDIT.md` says a search index
  also returned an older revision, which it did not use.

## Merge decisions

The article's provenance appendix ("Provenance of this report") records the
same decisions.

- **Base: manuscript 05.** Of the four manuscripts that prove a
  trace-class root bijection, 05 needs the weakest hypothesis (any sound
  static commutation relation `I ⊆ I_max`, with interval guards and zero
  tests; 04 needs disjoint supports) and proves the strongest conclusion (a
  convex quadratic whose nonnegative real zero set is a rational polytope
  with exactly the natural zeros as lattice points). Its text supplies the
  preamble, the introduction (Section 1) and the first place of every shared
  result.
- **Layout.** Section 1 is 05's introduction plus an organization
  subsection; Section 2 is the conventions (the block prescribed for this
  report, a notation dictionary, reading rules, then every manuscript's own
  conventions); Section 3 prints each manuscript's title, author line,
  date, abstract, status statement and introduction; Parts I–IX follow by
  subject; then implementation and validation, formalization targets,
  research questions and conclusions, collected by manuscript; then the
  manuscripts' appendices, the provenance appendix and one bibliography.
  Every section title inside Parts I–IX carries the number of the
  manuscript it comes from, for example `[05]`.
- **Printed once.** The universal-halting equivalence, proved by 05, 01,
  03 and 04, is one theorem, `cdc:bd:thm:universal`, with items (a) every
  c.e. subset of ℕ, (a′) every c.e. relation of finite arity (01), (b) a
  fixed universal halting polynomial, (b′) of degree at most four (04), (c)
  a fixed polynomial for 05's decidable first-halting trace verifier, all
  in finite-fold and single-fold versions. The absence of a computable
  witness-height bound, proved by 02, 01, 03, 04 and 05, is one proposition,
  `cdc:bd:prop:nobound`, stated in 02's general form (any undecidable set)
  with the universal-halting form beside it. At the places where 01, 02,
  03 and 04 stated them, a `[write]` note gives each manuscript's letters
  and its own proof follows there. 06's finite-fold substrate equivalence and
  parameter-bound obstruction are different statements and are kept whole;
  07 proves neither and is credited in prose.
- **Second routes.** 04's `thm:petri` and 06's `thm:tracebijection`
  (different constructions and counts), 01's `prop:boxes` (the box
  formulas of 05's `thm:interval`) and 06's `thm:commutation` (the counter
  form of 05's `thm:commute`) keep their statements and proofs, with
  "second route" or "counter form" in their titles; 04's monitor,
  lower-bound family and counting theorem, and the Parikh refinements of
  01, 04 and 06, point in their titles to 05's versions. 01's height-bounded
  compiler `thm:history` is a different theorem and is kept whole.
- **Moved text.** 05's interval-guard theorem and guarded-program
  corollary (from its section on other substrates) open Part I and follow
  the quadratic certificate in Part II; its rewriting subsection is in
  Part VII. The substrate surveys of 01, 02 and 05 are split between Parts
  VII, VIII and IX. 02's first two introductory subsections open Part IV and
  its Section 2 is in the conventions; 07's word-code subsection opens Part
  VI and its first-failure section closes Part I. 07's word-memory section
  stays before its quartic section, as in the manuscript, because the
  quartic uses its two-coordinate memory. Every move is announced by a note
  at both ends.
- **Conclusions.** Those of 02, 03 and 07 close Parts IV, V and VI; those of
  05, 01, 04 and 06 are collected in one back-matter section.
- **Research questions.** The 74 questions (01 10, 02 10, 03 10, 04 10, 05
  12, 06 12, 07 10) are printed in 50 `question` environments: 43 single
  questions and 7 merged clusters (verified compiler interfaces, dynamic
  independence, counting, sharp degree and arity, SKI bridges, fixed-arity
  compression, restricted compression), each naming its sources and
  printing each source's text. Three notes: 05's degree-two certificate
  answers part of 01's question on sharp degree, arity and domain
  comparisons (for length-`T` classes; the height-bounded quartic and the
  integer domain stay open); Part VI answers 06's queue question for
  bounded runs of fixed-read FIFO networks (data-dependent read counts stay
  open); 05's question on ProveIt's operation-counted straight-line
  certificates stays a question.
- **Bibliography.** The 58 items of the seven bibliographies (without 07's
  two "companion" items, which were manuscripts 04 and 06) are 33 distinct
  works; each merged entry lists the manuscripts citing it and keeps every
  annotation. Two different Cantone–Cuzziol–Omodeo papers stay apart.
- **Corrections to the printed text** (delivered files untouched): 07's
  sentence citing its unpublished companions now names manuscripts 04 and
  06 of this report; 06 cited Jones–Matiyasevich for ProveIt's
  documentation and now cites the repository; 04's hard-coded "Section 2",
  "Section 3" and "Section 7" point to its sections here (three section
  labels added); where 01, 02, 03, 04, 05, 06 and 07 name their own files in
  prose, the shipped name is printed, and their command listings keep the
  delivered layout with a note; sentences in which 01, 03 and 05 describe
  their delivered packages (PDF, checksum ledger, README) carry notes on
  what is shipped.
- **Additions.** The conventions block, with one change to the prescribed
  wording: "Parts II, VI, VII and VIII" for the Parts in which `T` counts
  execution steps (the prescription listed II, VI and VIII; Part VII's
  FRACTRAN runs also have `T` steps). A notation dictionary; a reading
  paragraph (in printed manuscript text, "this article" is that
  manuscript); Part openings with source, scope, duplicates and hypotheses;
  the remark on the formalized exponential counterpart after 02's
  exponentiation boundary (`cdc:bd:rem:sfu`); the remark on the project's
  tag-system notes after 07's uncausal example (`cdc:qc:rem:tagnotes`);
  notes on 07's one-coordinate obstruction versus the pairings of 01 and 05,
  and on bounded cellular-automaton tableaux. All written text is marked
  `[write]`.
- **Macros.** One `\code` (01's `\texttt{\detokenize{#1}}`); 02's `\_`
  escapes inside `\code` removed; the pin macros `\repoSHA` (01 and 07,
  different commits), `\repoCommit` (02) and `\reposha` (04) printed as
  literal identifiers; 04's unused `\repo` URL macro dropped (03's `\repo`
  kept); 06's unused `\word` dropped in favour of 07's. No mathematical
  symbol was renamed; letters that change meaning between Parts are listed
  in the conventions.
