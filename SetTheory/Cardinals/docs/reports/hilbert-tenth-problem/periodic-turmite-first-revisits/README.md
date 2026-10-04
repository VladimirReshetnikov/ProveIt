# Periodic Turmite First Revisits

**Periodic turmites: first revisits, a literal Langton ant and its
Diophantine certificate**

This is a research report in four Parts, dated 3–4 October 2026, built from
six manuscripts: "Research Reports" 38, 40, 42, 44, 47 and 48 of the
Hilbert's-tenth programme's AI-assisted report pipeline. Part I (Report 38,
batch-83 manuscript 10) was written in batch 83 as a single-source report;
Parts II–IV (batch-88 manuscripts 03, 04, 07, 09 and 10, cluster T1) were
added in batch 88 because Report 40 answers Part I's open question 3 and the
other four continue Report 40. Every author line is "Mathematical research
report"; no archive names a person or tool.

| Part | Report | Batch / ms. | Archive (arrival) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| I | 38 | 83 / 10 | `Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip` (`3051d1446`; 504,531 B, SHA-256 `e5abfdbfbbc9c203bdfafb040cba7f8c280af8b031b02103c989aeb97e085277`; 47 files under `Research_Report38/`; main file 703 lines; 21-page PDF) | `5883b08b7` (see below) | `a51a439cd` | the whole of Part I, with the manuscript's numbering |
| II | 40 | 88 / 03 | `Literal_Periodic_Langton_Ant_and_Visit_Boundary_Package.zip` (`c5612efa1`; 8,242,235 B, SHA-256 `0c3acc1e36c0931ea490c7526e053ef1bd8a17ad5ea72ec36b97dc4c3548e47e`; 213 files under `Research_Report40/`, 159,096,079 B extracted; main file 830 lines; 32-page PDF) | `5883b08b7` | `ed7c76266` | Part II, numbered 40.k |
| III | 42 | 88 / 04 | `Arithmetic_Initialization_for_a_Periodic_Langton_Ant_Package.zip` (`c5612efa1`; 761,758 B, SHA-256 `9ee861d5092370fbfd7157c718833236fab9b6da9dccd3cc41c4798d8d3eea35`; 99 files under `ant-initialization-report42/`; 557 lines; 18 pages) | `5883b08b7`; Mathlib `ac77769f` | `ed7c76266` | first half of Part III, numbered 42.k |
| III | 44 | 88 / 07 | `Complete_Positive_Certificate_for_the_Literal_Periodic_Ant_Package.zip` (`c5612efa1`; 767,662 B, SHA-256 `3025a1efd5947e624a23f90a07dea7a826410d25944c3c968ea45edfd71013eb`; 103 files under `report44-recovered/`; 332 lines; 12 pages) — a **recovered edition** | `5883b08b7`; Mathlib `ac77769f` | `ed7c76266` | second half of Part III (its main theorem), numbered 44.k |
| IV | 47 | 88 / 09 | `Exact_Structured_Construction_of_the_Fixed_Ant_Coefficients_Package.zip` (`c5612efa1`; 1,344,412 B, SHA-256 `fa58914f5334f54a6c648bbaa68d6127bfe3e9de2bf9d711c95370b2310ab57f`; 95 files under `Research_Report47/`; 401 lines; 14 pages) | none of its own (inherits 44's) | `ed7c76266` | first half of Part IV, numbered 47.k |
| IV | 48 | 88 / 10 | `Exact_Fusion_of_the_Ant_Background_Polynomials_Package.zip` (`c5612efa1`; 2,162,628 B, SHA-256 `45f8dcf697012fc67cd9155f76980787fef8ff3cb4f4746ef54c4c3375c7bb65`; 80 files under `Research_Report48/`; 439 lines; 15 pages) | none of its own | `ed7c76266` | second half of Part IV, numbered 48.k |

**The pins.** Report 38 pins no commit for its mathematics. Its frozen
source audit (`source-packet-boundary-context-source-audit.md`) read two
research-tree notes, `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md`
(lines 305–401, blob `2e762cc5f31e`) and
`Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md`
(lines 1–95, blob `a70af5ccd954`), and pinned its repository searches to
commit `5883b08b7` (3 October 2026). That commit is taken as its pin.
Reports 40, 42 and 44 pin the same commit explicitly (Report 40's
bibliography entry "arithmetic", Reports 42 and 44's entry "history"); the
first note, the 174-operation bounded-history note they inherit, has SHA-256
`9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656`. Both
notes are unchanged at the write. Reports 42 and 44 also pin Mathlib commit
`ac77769fabe23cb237559e7f56578dbead91499f`
(`Mathlib/NumberTheory/PellMatiyasevic.lean`, 39,986 B, SHA-256
`993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`; not
shipped, see below), and Report 44 the Neary–Woods PDF (SHA-256
`6274cb68…`) and the endpoint source (`dd5a29f9…`). Reports 47 and 48 pin no
ProveIt commit and inherit Report 44's.

**Report 44 is a recovered edition.** Its own edition note: a pre-delivery
filesystem reset lost the previously verified Report 44 files, and this
edition was reconstructed from retained work and the authenticated earlier
reports, with a new release identity and fresh checks; the receipts under
`verification/historical/` (shipped as `04-ant-cert-verification-historical-QA.md`
and `data/04-ant-cert-verification-historical-RECOVERED_QA_RECEIPT.json`)
describe the lost bytes only. Only this edition exists in the repository. At
placement both of its complete arithmetic streams were regenerated on a copy
and reproduced the earlier audited SHA-256 identities (`c1690116…`
two-input, `85a16197…` one-input).

## The results

**Part I (Report 38).** For an explicitly listed cyclic L/R turmite rule, an
explicitly listed periodic colour tile, finitely many binary-encoded defects
and a binary start, the first repeated lattice *position* (heading ignored)
is decidable in polynomial bit time: the algorithm returns the exact first
repeated arrival `τ`, an earlier witness and a polynomial-size affine lane
representation of the path, or certifies that no position is ever revisited
and returns a translated periodic tail (Theorem 2.2); `τ ≤ T* = (K+1)(S(2B+1)+1)`
and every intermediate integer has polynomially many bits (Theorem 6.1).
Exact first occurrence of finite unions of heading, coordinate-congruence,
head-site and head-relative colour-stencil clauses on the certified domain
is decidable and implemented (Theorem 7.1), with no polynomial bound. As a
consequence, no undecidable language reduces to globally one-visit runs with
acceptance in that observation language (Corollary 12.1).

**Part II (Report 40).** One fixed doubly periodic binary background
(periods 576000 and 481238074400, given by a total colour query), the fixed
start `(288650, 75, E)` (coordinates east/**south**-positive) and a finite
loader changing exactly `2812 + 4(popcount ℓ + popcount r)` cells make the
binary RL ant (Langton's ant) simulate the fixed fifteen-state machine U15 of
Neary and Woods: every cell is visited at most twice over the whole infinite
run, also after simulated halting, and U15 reaches its undefined pair J1 iff
a pre-departure head state with heading S hits a fixed residue class
(Theorem 40.1.1, Theorem 40.12.2). The proof runs through 7 literal primitive
maps, a 32-state radius-one rule, a complete 862-NAND cell checked on all
2^24 inputs, an exact compressed program of 601,547,591 instruction rows, the
growing-layer and long-channel proofs and an exclusive accepting port. With
Part I this gives the **sharp one-versus-two-visit boundary** for
reachability with a fixed residue-and-heading predicate (Corollary 40.1.2),
subject to the published U15 encoding. Appendix 40.D pays an endpoint
selector for the accepting event (42 operations with prescribed numerals,
101 from literals 1 and 3), conditional on the inherited 174-operation
history.

**Part III (Reports 42 and 44).** Report 42: a fixed polynomial system of
2,306,387 operations, 234 equations and 396 positive witnesses, with no
length-indexed gates, turns two raw positive sentinel integers into the exact
initialized board and north-facing head of Part II's ant on any permitted
rectangle (Theorem 42.1.1), through an all-length binary recoder (binomial
parity and coefficient extraction) and a 70-operation power macro
specialized from Mathlib's `Pell.matiyasevic` and `Pell.eq_pow_of_pell`
(Lemma 42.4.1); its single-equation form has exact degree 2,304,000.
Report 44, the main theorem: **one fixed polynomial `F_2 ∈ Z[x, y, z_1..z_465]`
with `H(x,y) ⇔ ∃ z > 0, F_2(x, y, z) = 0`**, where `H` is halting of U15 on
the two sentinel-decoded side words; 2,307,457 operations, exact degree
2,304,000, leading part `2W^2304000`; a one-input form `F_1` with paid
Cantor pairing, 467 witnesses, 2,307,467 operations (Theorem 44.1.1).

**Part IV (Reports 47 and 48).** The same polynomial, equal at every integer
assignment, built from the literals 1 and 3 only:

| Source | `F_2` | `F_1` |
|---|---:|---:|
| Report 44, prescribed fixed coefficients | 2,307,457 | 2,307,467 |
| Report 44, literals 1 and 3, dense Horner prefix | 554,386,261,710,212,588 | 554,386,261,710,212,598 |
| Report 47, structured coefficients (Theorem 47.1.1) | 31,388,831 | 31,388,841 |
| Report 48, fused background polynomials (Theorem 48.1.1) | 14,658,934 | 14,658,944 |
| programme `5d7e884a5`: endpoint reuse (−9) and six shared rotation blocks (−38,146) | 14,620,779 | 14,620,789 |
| programme `57a6afbeb`: plus zero-folding and common-subexpression cleanup (−68) | 14,620,711 | 14,620,721 |

None is an erratum of another; each count is valid for its grammar. The
programme's counts are inherited-plus-delta (changed components emitted and
checked; no new complete stream emitted or hashed). The theorem is printed
once, as Theorem 44.1.1, with this table beside it.

**What the certificate is not.** `F_2` recognizes the *fixed* U15
sentinel-pair halting language. It is recursively enumerable and complete
only through Neary and Woods' published encoding of programs as U15 tapes,
which no Part implements. In the programme's words (`review_periodic_ant40_48_intake.md`),
it is "an ordinary-integer Diophantine recognizer of a fixed recursively
enumerable complete language", "not, by itself, an emitted per-program map
from the research tree's ordinary input variable into the published U15 tape
encoding"; "the external compilation dependency must not silently become a
free arithmetic input loader". So it is **not an ordinary-input loader for
the programme's input convention**, and it is not a universal polynomial in
the programme's sense without that qualification. It does not improve the
programme's 84-operation universal bound (`20aafb9a5`); its operation counts
use different coefficient conventions and are far larger. The ant never
physically halts; the background is infinite and periodic.

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs
and finite exact replay checks. Several theorems are explicitly conditional
on inherited results: the published U15 simulation, the research tree's
174-operation bounded-history theorem, Mathlib's Pell theorems, and (for
Parts III–IV) the earlier Parts. "In P" in Part I refers to its explicit
input model. No priority is claimed or certified.

**Already reviewed.** The Hilbert's-tenth research programme reviewed every
archive after arrival (notes in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`,
indexed in `Computability/HilbertTenthProblem/README.md`):

- **Report 38**: `review_turmite_first_revisit38_intake.md` (`308f14072`).
  It read the proofs and the active source text, and did not run the archived
  Python, replay the logs, audit the release verifier or certify the PDF.
  Verdict: the first-revisit, polynomial-bit-complexity and exact-observation
  arguments "pass this bounded proof read on their stated domains. No
  mathematical defect was found." Its scope points, all printed in Part I
  (its editorial preface and `[write]` notes in Sections 7, 11 and 12): the
  certified one-visit portion is decidable and supplies no new universal
  arithmetic bound; the complexity proof bounds every intermediate integer;
  the **strict first-arrival observation boundary**; **attribution** of
  turmite universality to Maldonado, Gajardo, Hellouin de Menibus and
  Moreira, *Nontrivial Turmites are Turing-universal*, arXiv:1702.05547; and
  an unimplemented **Boolean-DAG occurrence-certificate lead**, not a
  first-hit-minimality certificate and **not an ordinary-input universal
  loader** (printed in Section 12 with the letters changed to `χ, η, Λ`).
- **Reports 40–48**: `review_periodic_ant40_48_intake.md` (+`.json`,
  `cfbe37de7`), `review_ant47_48_intake.md` and
  `review_periodic_ant_sharing48.md` (`5d7e884a5`), and the successor packets
  `periodic_ant_endpoint_reuse48.md`, `ant48_rotated_occurrence_sharing.md`
  (`5d7e884a5`) and `ant48_rotated_occurrence_cleanup.md` with
  `review_ant48_rotated_occurrence_cleanup.md` (`57a6afbeb`). No defect was
  found in the read proofs, algebra, ledger arithmetic or source binding. It
  read 48 of the 590 archive members and checked independently the 1055-row
  recoder's 228 residuals, 888 coefficients and three outputs, the 174-row
  history DAG's closure, count and degree, 2,296,800 correction-exponent
  instances and 6,912,000 profile entries; no archived program ran, no
  complete stream was regenerated, and the physical templates, the history
  theorem and the published simulation were not re-certified. Its findings,
  all printed in the article (preface to the four Parts and `[write]` notes):
  the scope of the language (above); the Neary–Woods paper's last sentence of
  §3.5 names `c` in the halting transition while its Table 16 leaves
  `(u10, b)` = J1 undefined, and every report follows the table; the earlier
  programme toggle-tape components (105/158, 105/155) remain much narrower;
  no change to the 84 bound; Maldonado et al. give periodic-background, not
  blank-board, universality; and the two sharing opportunities in Report 48,
  since realized (table above).
- **The placement** `ed7c76266`: `review_periodic_ant_placement_ed7c76266.md`
  (+`.json`, `70bbc9ce2`). All 381 placed files are byte-identical to members
  of the reviewed archives; nothing new was introduced. It noted that the
  article and README still described Report 38 alone (this write adds Parts
  II–IV), that the README did not yet document Report 40's derived cell maps
  (see "Third-party material"), and that the count 14,620,779 quoted in the
  placement message predates the cleanup giving 14,620,711 / 14,620,721.

## Files

Every shipped file other than `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery (verified at placement against fresh
extractions). The directory holds 424 files: 43 of Part I and the report
(below), and 381 of Parts II–IV (listed with their delivered names after it).

```
README.md                                                 this guide
article.tex                                               the report: front matter and preface to the four Parts; Part I (the delivered Research_Report38.tex with ptr: labels, its editorial preface, [write] notes and Appendix C); Parts II-IV (Reports 40, 42, 44, 47, 48 with prefixed labels and [write] notes); provenance of Parts II-IV
article.pdf                                               the compiled report, 132 pages
INTEGRITY.md                                              Report 38: the delivered release's integrity and reproducibility contract
source-packet-PROOF.md                                    proof of the observation extension (signed progression calculus, colour compiler)
source-packet-README.md                                   the frozen source packet's README
source-packet-boundary-context-README.md                  README of the historical boundary context
source-packet-boundary-context-proof.md                   the original first-revisit proof, Presburger formulation, eventual periodicity
source-packet-boundary-context-review.md                  the historical review of the original boundary program
source-packet-boundary-context-source-audit.md            literature and repository source audit (the pin)
source-packet-complexity-review.md                        numerical and intermediate bit bounds for first revisit
source-packet-review.md                                   independent review of the observation code and mathematics (the iterator finding)
code/verify_release.py                                    the release verifier (identity gate, normal/-O replay); does not run here
code/seal_release.py                                      release sealing; rewrites MANIFEST.json, SHA256SUMS and verify_release.py in place
code/build_pdf.py                                         external pdfLaTeX rebuild of the delivered PDF
code/archive_release.py                                   deterministic ZIP creation and safe moved replay
code/archive_regression.py                                hostile-archive regression
code/tamper_regression.py                                 tamper regression on disposable copies
code/source-packet-one_visit.py                           active first-revisit engine (pinned)
code/source-packet-observations.py                        active observation compiler (pinned)
code/source-packet-test_boundary_regression.py            author tests, boundary part (pinned; = historical test_one_visit.py)
code/source-packet-test_observations.py                   author tests, observation part (pinned)
code/source-packet-independent_checks.py                  independent checker, seven groups (pinned)
code/source-packet-example.py                             the 2*10^100 first-hit example (pinned)
code/source-packet-verify_release.py                      the packet's own test gate (inert by design)
code/source-packet-boundary-context-one_visit.py          historical original engine (inert by design)
code/source-packet-boundary-context-review_checks.py      historical review checks (inert by design)
data/MANIFEST.json                                        the release inventory (delivered paths)
data/verification-expected-receipts.json                  stable expected outputs of the replay
data/verification-release-review.json                     the release's own review record (21-page PDF, delivered TeX)
data/verification-replay-plan.json                        the six pinned active programs and the replay commands
data/verification-source-lineage.json                     original/packaged path and SHA-256 of every packet file
data/source-packet-author-normal.log                      original author run, normal Python
data/source-packet-author-optimized.log                   original author run, python -O
data/source-packet-independent-normal.log                 original independent run, normal Python
data/source-packet-independent-optimized.log              original independent run, python -O
data/source-packet-independent-normal.txt                 a second recorded independent run (stream order and timing differ)
data/source-packet-independent-optimized.txt              a second recorded independent run, python -O
data/source-packet-example-result.json                    output of example.py
data/source-packet-release-receipt.json                   receipt of the packet's own test gate
data/source-packet-boundary-context-examples.json         historical examples of the boundary program
data/source-packet-boundary-context-review-check-results.txt   historical review-check counts
data/source-packet-boundary-context-test-results.txt      historical boundary test log
```

### Parts II–IV: shipped name and delivered name

Each line gives the shipped name and, after `<-`, the delivered path
relative to the archive's top directory. The rule: the archive's top directory is dropped, and so is the segment
`evidence/`; the remaining path is joined with `-` and given the
manuscript's local prefix (`02-literal-ant-` Report 40, `03-ant-init-`
Report 42, `04-ant-cert-` Report 44, `05-ant-coeffs-` Report 47,
`06-ant-fusion-` Report 48); `.md` goes to the report root, `.py` to
`code/`, everything else (`.json`, `.log`, `.txt`, `.bin`, `.diff`, included
`.tex`) to `data/`. Because `-` also occurs inside delivered names, the list
below, not the rule, is the authoritative map. Report 40: 17 root, 48 code,
71 data files; Report 42: 13, 12, 55; Report 44: 8, 15, 32; Report 47: 6,
18, 35; Report 48: 6, 10, 35.

```
# Report 40: 136 files, delivered under Research_Report40/
02-literal-ant-INTEGRITY.md  <-  INTEGRITY.md
02-literal-ant-enclosing-review-REVIEW.md  <-  evidence/enclosing-review/REVIEW.md
02-literal-ant-endpoint-CONTRACT.md  <-  evidence/endpoint/CONTRACT.md
02-literal-ant-endpoint-ENDPOINT_AUDIT.md  <-  evidence/endpoint/ENDPOINT_AUDIT.md
02-literal-ant-endpoint-FIVE_WITNESS_ENDPOINT_ADDENDUM.md  <-  evidence/endpoint/FIVE_WITNESS_ENDPOINT_ADDENDUM.md
02-literal-ant-endpoint-FOLDED_ENDPOINT_ADDENDUM.md  <-  evidence/endpoint/FOLDED_ENDPOINT_ADDENDUM.md
02-literal-ant-endpoint-README.md  <-  evidence/endpoint/README.md
02-literal-ant-endpoint-independent-audit-QA_REVIEW.md  <-  evidence/endpoint-independent-audit/QA_REVIEW.md
02-literal-ant-independent-audit-AUDIT.md  <-  evidence/independent-audit/AUDIT.md
02-literal-ant-independent-audit-AUDIT_V1.md  <-  evidence/independent-audit/AUDIT_V1.md
02-literal-ant-literal-interface-README.md  <-  evidence/literal-interface/README.md
02-literal-ant-literal-interface-SOURCE_PROVENANCE.md  <-  evidence/literal-interface/SOURCE_PROVENANCE.md
02-literal-ant-literal-interface-atlas-PROOF.md  <-  evidence/literal-interface/atlas/PROOF.md
02-literal-ant-literal-interface-copy-GLOBAL_GENERATOR_REVIEW.md  <-  evidence/literal-interface/copy/GLOBAL_GENERATOR_REVIEW.md
02-literal-ant-literal-interface-copy-REPORT.md  <-  evidence/literal-interface/copy/REPORT.md
02-literal-ant-literal-interface-copy-program_audit-ANALYSIS.md  <-  evidence/literal-interface/copy/program_audit/ANALYSIS.md
02-literal-ant-predecessor-README.md  <-  evidence/predecessor/README.md
code/02-literal-ant-archive_regression.py  <-  archive_regression.py
code/02-literal-ant-archive_release.py  <-  archive_release.py
code/02-literal-ant-build_pdf.py  <-  build_pdf.py
code/02-literal-ant-endpoint-audit_endpoint.py  <-  evidence/endpoint/audit_endpoint.py
code/02-literal-ant-endpoint-audit_five_witness_endpoint.py  <-  evidence/endpoint/audit_five_witness_endpoint.py
code/02-literal-ant-endpoint-audit_folded_endpoint.py  <-  evidence/endpoint/audit_folded_endpoint.py
code/02-literal-ant-endpoint-independent-audit-independent_dag_check.py  <-  evidence/endpoint-independent-audit/independent_dag_check.py
code/02-literal-ant-endpoint-replay_all.py  <-  evidence/endpoint/replay_all.py
code/02-literal-ant-endpoint-verify_literal_sources.py  <-  evidence/endpoint/verify_literal_sources.py
code/02-literal-ant-independent-audit-independent_interface_checks.py  <-  evidence/independent-audit/independent_interface_checks.py
code/02-literal-ant-literal-interface-atlas-check_initialization_observer.py  <-  evidence/literal-interface/atlas/check_initialization_observer.py
code/02-literal-ant-literal-interface-atlas-compile_input.py  <-  evidence/literal-interface/atlas/compile_input.py
code/02-literal-ant-literal-interface-atlas-generator.py  <-  evidence/literal-interface/atlas/generator.py
code/02-literal-ant-literal-interface-atlas-quantitative_ledger.py  <-  evidence/literal-interface/atlas/quantitative_ledger.py
code/02-literal-ant-literal-interface-atlas-verify_observer_polarity.py  <-  evidence/literal-interface/atlas/verify_observer_polarity.py
code/02-literal-ant-literal-interface-ca-build_ca_circuit.py  <-  evidence/literal-interface/ca/build_ca_circuit.py
code/02-literal-ant-literal-interface-ca-physical_program.py  <-  evidence/literal-interface/ca/physical_program.py
code/02-literal-ant-literal-interface-ca-verify_complete_tables.py  <-  evidence/literal-interface/ca/verify_complete_tables.py
code/02-literal-ant-literal-interface-ca-verify_program_ledger.py  <-  evidence/literal-interface/ca/verify_program_ledger.py
code/02-literal-ant-literal-interface-common-geometry_kit.py  <-  evidence/literal-interface/common/geometry_kit.py
code/02-literal-ant-literal-interface-copy-audit_atlas_compatibility.py  <-  evidence/literal-interface/copy/audit_atlas_compatibility.py
code/02-literal-ant-literal-interface-copy-build_copy.py  <-  evidence/literal-interface/copy/build_copy.py
code/02-literal-ant-literal-interface-copy-build_copy_family.py  <-  evidence/literal-interface/copy/build_copy_family.py
code/02-literal-ant-literal-interface-copy-build_delayed_copy.py  <-  evidence/literal-interface/copy/build_delayed_copy.py
code/02-literal-ant-literal-interface-copy-build_initial_anchor.py  <-  evidence/literal-interface/copy/build_initial_anchor.py
code/02-literal-ant-literal-interface-copy-build_marker_variants.py  <-  evidence/literal-interface/copy/build_marker_variants.py
code/02-literal-ant-literal-interface-copy-build_normalized_copy_family.py  <-  evidence/literal-interface/copy/build_normalized_copy_family.py
code/02-literal-ant-literal-interface-copy-build_pair_instructions.py  <-  evidence/literal-interface/copy/build_pair_instructions.py
code/02-literal-ant-literal-interface-copy-program_audit-verify_program_index_bounds.py  <-  evidence/literal-interface/copy/program_audit/verify_program_index_bounds.py
code/02-literal-ant-literal-interface-copy-review_global_generator.py  <-  evidence/literal-interface/copy/review_global_generator.py
code/02-literal-ant-literal-interface-copy-stub_geometry.py  <-  evidence/literal-interface/copy/stub_geometry.py
code/02-literal-ant-literal-interface-copy-translate_anchor.py  <-  evidence/literal-interface/copy/translate_anchor.py
code/02-literal-ant-literal-interface-copy-verify_copy_family.py  <-  evidence/literal-interface/copy/verify_copy_family.py
code/02-literal-ant-literal-interface-copy-verify_delayed_copy.py  <-  evidence/literal-interface/copy/verify_delayed_copy.py
code/02-literal-ant-literal-interface-copy-verify_header_entry_only.py  <-  evidence/literal-interface/copy/verify_header_entry_only.py
code/02-literal-ant-literal-interface-copy-verify_marker_neighbors.py  <-  evidence/literal-interface/copy/verify_marker_neighbors.py
code/02-literal-ant-literal-interface-copy-verify_marker_variants.py  <-  evidence/literal-interface/copy/verify_marker_variants.py
code/02-literal-ant-literal-interface-copy-verify_pair_instructions.py  <-  evidence/literal-interface/copy/verify_pair_instructions.py
code/02-literal-ant-literal-interface-nand-build_nand.py  <-  evidence/literal-interface/nand/build_nand.py
code/02-literal-ant-literal-interface-not-build_not.py  <-  evidence/literal-interface/not/build_not.py
code/02-literal-ant-literal-interface-plans-boolean_word_programs.py  <-  evidence/literal-interface/plans/boolean_word_programs.py
code/02-literal-ant-literal-interface-replay_all.py  <-  evidence/literal-interface/replay_all.py
code/02-literal-ant-literal-interface-strip-build_periodic_benchmark.py  <-  evidence/literal-interface/strip/build_periodic_benchmark.py
code/02-literal-ant-literal-interface-strip-verify_periodic_benchmark.py  <-  evidence/literal-interface/strip/verify_periodic_benchmark.py
code/02-literal-ant-predecessor-atlas-compile_input.py  <-  evidence/predecessor/atlas/compile_input.py
code/02-literal-ant-seal_release.py  <-  seal_release.py
code/02-literal-ant-tamper_regression.py  <-  tamper_regression.py
code/02-literal-ant-verify_release.py  <-  verify_release.py
data/02-literal-ant-MANIFEST.json  <-  MANIFEST.json
data/02-literal-ant-enclosing-review-REVIEW.json  <-  evidence/enclosing-review/REVIEW.json
data/02-literal-ant-enclosing-review-targeted-checks.json  <-  evidence/enclosing-review/targeted-checks.json
data/02-literal-ant-endpoint-MANIFEST.json  <-  evidence/endpoint/MANIFEST.json
data/02-literal-ant-endpoint-endpoint_audit_receipt.json  <-  evidence/endpoint/endpoint_audit_receipt.json
data/02-literal-ant-endpoint-endpoint_five_witness_fixed_numerals_source.json  <-  evidence/endpoint/endpoint_five_witness_fixed_numerals_source.json
data/02-literal-ant-endpoint-endpoint_five_witness_paid_numerals_source.json  <-  evidence/endpoint/endpoint_five_witness_paid_numerals_source.json
data/02-literal-ant-endpoint-endpoint_fixed_numerals_source.json  <-  evidence/endpoint/endpoint_fixed_numerals_source.json
data/02-literal-ant-endpoint-endpoint_folded_fixed_numerals_source.json  <-  evidence/endpoint/endpoint_folded_fixed_numerals_source.json
data/02-literal-ant-endpoint-endpoint_folded_paid_numerals_source.json  <-  evidence/endpoint/endpoint_folded_paid_numerals_source.json
data/02-literal-ant-endpoint-endpoint_paid_numerals_source.json  <-  evidence/endpoint/endpoint_paid_numerals_source.json
data/02-literal-ant-endpoint-five_witness_endpoint_audit_receipt.json  <-  evidence/endpoint/five_witness_endpoint_audit_receipt.json
data/02-literal-ant-endpoint-folded_endpoint_audit_receipt.json  <-  evidence/endpoint/folded_endpoint_audit_receipt.json
data/02-literal-ant-endpoint-fresh_replay.json  <-  evidence/endpoint/fresh_replay.json
data/02-literal-ant-endpoint-fresh_replay.log  <-  evidence/endpoint/fresh_replay.log
data/02-literal-ant-endpoint-independent-audit-authentication.json  <-  evidence/endpoint-independent-audit/authentication.json
data/02-literal-ant-endpoint-independent-audit-executable_boundary.json  <-  evidence/endpoint-independent-audit/executable_boundary.json
data/02-literal-ant-endpoint-independent-audit-external_qa_summary.json  <-  evidence/endpoint-independent-audit/external_qa_summary.json
data/02-literal-ant-endpoint-independent-audit-independent_dag_check.json  <-  evidence/endpoint-independent-audit/independent_dag_check.json
data/02-literal-ant-endpoint-independent-audit-optimization_guards.json  <-  evidence/endpoint-independent-audit/optimization_guards.json
data/02-literal-ant-endpoint-literal_source_verification.json  <-  evidence/endpoint/literal_source_verification.json
data/02-literal-ant-figures-primitive-grids.tex  <-  figures/primitive-grids.tex
data/02-literal-ant-figures-primitive-ports.tex  <-  figures/primitive-ports.tex
data/02-literal-ant-figures-primitive-rows.tex  <-  figures/primitive-rows.tex
data/02-literal-ant-independent-audit-authentication.json  <-  evidence/independent-audit/authentication.json
data/02-literal-ant-independent-audit-independent_interface_checks.json  <-  evidence/independent-audit/independent_interface_checks.json
data/02-literal-ant-independent-audit-replay_verification.json  <-  evidence/independent-audit/replay_verification.json
data/02-literal-ant-independent-audit-v1_v2_changed_paths.json  <-  evidence/independent-audit/v1_v2_changed_paths.json
data/02-literal-ant-literal-interface-INTERFACE_GATE.json  <-  evidence/literal-interface/INTERFACE_GATE.json
data/02-literal-ant-literal-interface-MANIFEST.json  <-  evidence/literal-interface/MANIFEST.json
data/02-literal-ant-literal-interface-atlas-empty_input_example.json  <-  evidence/literal-interface/atlas/empty_input_example.json
data/02-literal-ant-literal-interface-atlas-fresh_replay.json  <-  evidence/literal-interface/atlas/fresh_replay.json
data/02-literal-ant-literal-interface-atlas-fresh_replay.log  <-  evidence/literal-interface/atlas/fresh_replay.log
data/02-literal-ant-literal-interface-atlas-initialization_observer_receipt.json  <-  evidence/literal-interface/atlas/initialization_observer_receipt.json
data/02-literal-ant-literal-interface-atlas-input_loader_receipt.json  <-  evidence/literal-interface/atlas/input_loader_receipt.json
data/02-literal-ant-literal-interface-atlas-observer_polarity_receipt.json  <-  evidence/literal-interface/atlas/observer_polarity_receipt.json
data/02-literal-ant-literal-interface-atlas-quantitative_ledger.json  <-  evidence/literal-interface/atlas/quantitative_ledger.json
data/02-literal-ant-literal-interface-ca-complete_table_verification.json  <-  evidence/literal-interface/ca/complete_table_verification.json
data/02-literal-ant-literal-interface-ca-fixed_ca_cell.json  <-  evidence/literal-interface/ca/fixed_ca_cell.json
data/02-literal-ant-literal-interface-ca-physical_program.json  <-  evidence/literal-interface/ca/physical_program.json
data/02-literal-ant-literal-interface-ca-program_ledger.json  <-  evidence/literal-interface/ca/program_ledger.json
data/02-literal-ant-literal-interface-ca-radius_one_32_table.bin  <-  evidence/literal-interface/ca/radius_one_32_table.bin
data/02-literal-ant-literal-interface-common-primitive_catalog.json  <-  evidence/literal-interface/common/primitive_catalog.json
data/02-literal-ant-literal-interface-common-primitive_maps.json  <-  evidence/literal-interface/common/primitive_maps.json
data/02-literal-ant-literal-interface-copy-MANIFEST.json  <-  evidence/literal-interface/copy/MANIFEST.json
data/02-literal-ant-literal-interface-copy-delayed_copy_receipt.json  <-  evidence/literal-interface/copy/delayed_copy_receipt.json
data/02-literal-ant-literal-interface-copy-fixed_initial_anchor_patch.json  <-  evidence/literal-interface/copy/fixed_initial_anchor_patch.json
data/02-literal-ant-literal-interface-copy-global_generator_review.json  <-  evidence/literal-interface/copy/global_generator_review.json
data/02-literal-ant-literal-interface-copy-independent_family_receipt.json  <-  evidence/literal-interface/copy/independent_family_receipt.json
data/02-literal-ant-literal-interface-copy-left_start_anchor.json  <-  evidence/literal-interface/copy/left_start_anchor.json
data/02-literal-ant-literal-interface-copy-marker_variants_receipt.json  <-  evidence/literal-interface/copy/marker_variants_receipt.json
data/02-literal-ant-literal-interface-copy-pair_instruction_receipt.json  <-  evidence/literal-interface/copy/pair_instruction_receipt.json
data/02-literal-ant-literal-interface-copy-program_audit-node_bounds.json  <-  evidence/literal-interface/copy/program_audit/node_bounds.json
data/02-literal-ant-literal-interface-copy-program_audit-receipt.json  <-  evidence/literal-interface/copy/program_audit/receipt.json
data/02-literal-ant-literal-interface-receipts-boolean_word_programs.json  <-  evidence/literal-interface/receipts/boolean_word_programs.json
data/02-literal-ant-literal-interface-strip-periodic_benchmark.json  <-  evidence/literal-interface/strip/periodic_benchmark.json
data/02-literal-ant-predecessor-INTERFACE_GATE.json  <-  evidence/predecessor/INTERFACE_GATE.json
data/02-literal-ant-predecessor-MANIFEST.json  <-  evidence/predecessor/MANIFEST.json
data/02-literal-ant-predecessor-atlas-fresh_replay.json  <-  evidence/predecessor/atlas/fresh_replay.json
data/02-literal-ant-predecessor-atlas-input_loader_receipt.json  <-  evidence/predecessor/atlas/input_loader_receipt.json
data/02-literal-ant-verification-complete-preseal-replay.json  <-  verification/complete-preseal-replay.json
data/02-literal-ant-verification-expected-receipts.json  <-  verification/expected-receipts.json
data/02-literal-ant-verification-loader-v1-v2.diff  <-  verification/loader-v1-v2.diff
data/02-literal-ant-verification-original-preservation.json  <-  verification/original-preservation.json
data/02-literal-ant-verification-pdf-rebuild.json  <-  verification/pdf-rebuild.json
data/02-literal-ant-verification-preview-replay.json  <-  verification/preview-replay.json
data/02-literal-ant-verification-preview-tamper-regression.json  <-  verification/preview-tamper-regression.json
data/02-literal-ant-verification-release-review.json  <-  verification/release-review.json
data/02-literal-ant-verification-replay-plan.json  <-  verification/replay-plan.json
data/02-literal-ant-verification-source-lineage.json  <-  verification/source-lineage.json
data/02-literal-ant-verification-visual-qa.json  <-  verification/visual-qa.json

# Report 42: 80 files, delivered under ant-initialization-report42/
03-ant-init-recoder-degree-ADDENDUM.md  <-  recoder-degree/ADDENDUM.md
03-ant-init-science-COMPOSITION.md  <-  science/COMPOSITION.md
03-ant-init-science-DEGREE.md  <-  science/DEGREE.md
03-ant-init-science-PROOF.md  <-  science/PROOF.md
03-ant-init-science-README.md  <-  science/README.md
03-ant-init-science-REVIEW.md  <-  science/REVIEW.md
03-ant-init-science-REVISION.md  <-  science/REVISION.md
03-ant-init-science-dilation-PROOF.md  <-  science/dilation/PROOF.md
03-ant-init-science-recipe_assets-README.md  <-  science/recipe_assets/README.md
03-ant-init-science-reviews-composition-COMPOSITION_AUDIT_ADDENDUM.md  <-  science/reviews/composition/COMPOSITION_AUDIT_ADDENDUM.md
03-ant-init-science-reviews-dilation-AUDIT.md  <-  science/reviews/dilation/AUDIT.md
03-ant-init-science-reviews-periodic-AUDIT.md  <-  science/reviews/periodic/AUDIT.md
03-ant-init-verification-recoder-degree-AUDIT.md  <-  verification/recoder-degree-AUDIT.md
code/03-ant-init-archive_release.py  <-  archive_release.py
code/03-ant-init-build_pdf.py  <-  build_pdf.py
code/03-ant-init-recoder-degree-check_degree.py  <-  recoder-degree/check_degree.py
code/03-ant-init-science-audit_degree.py  <-  science/audit_degree.py
code/03-ant-init-science-bridge_dag.py  <-  science/bridge_dag.py
code/03-ant-init-science-check_bridge.py  <-  science/check_bridge.py
code/03-ant-init-science-check_composition.py  <-  science/check_composition.py
code/03-ant-init-science-compose_initialization.py  <-  science/compose_initialization.py
code/03-ant-init-science-dilation-dilation_check.py  <-  science/dilation/dilation_check.py
code/03-ant-init-science-polynomial_initialization.py  <-  science/polynomial_initialization.py
code/03-ant-init-science-replay.py  <-  science/replay.py
code/03-ant-init-verify_release.py  <-  verify_release.py
data/03-ant-init-MANIFEST.json  <-  MANIFEST.json
data/03-ant-init-dependencies-SOURCE-MANIFEST.json  <-  dependencies/SOURCE-MANIFEST.json
data/03-ant-init-recoder-degree-MANIFEST.json  <-  recoder-degree/MANIFEST.json
data/03-ant-init-recoder-degree-degree_receipt.json  <-  recoder-degree/degree_receipt.json
data/03-ant-init-science-MANIFEST.json  <-  science/MANIFEST.json
data/03-ant-init-science-composed_initialization_receipt.json  <-  science/composed_initialization_receipt.json
data/03-ant-init-science-composition_verification.json  <-  science/composition_verification.json
data/03-ant-init-science-data-pair_inline-dag.json  <-  science/data/pair_inline-dag.json
data/03-ant-init-science-degree_receipt.json  <-  science/degree_receipt.json
data/03-ant-init-science-dependencies-mathlib-primary_source_pin.json  <-  science/dependencies/mathlib/primary_source_pin.json
data/03-ant-init-science-dilation-final-evidence-check_receipt.json  <-  science/dilation/final-evidence/check_receipt.json
data/03-ant-init-science-dilation-final-evidence-exp-dag.json  <-  science/dilation/final-evidence/exp-dag.json
data/03-ant-init-science-dilation-final-evidence-forward-dag.json  <-  science/dilation/final-evidence/forward-dag.json
data/03-ant-init-science-dilation-final-evidence-pair-dag.json  <-  science/dilation/final-evidence/pair-dag.json
data/03-ant-init-science-dilation-final-evidence-pair_positive-dag.json  <-  science/dilation/final-evidence/pair_positive-dag.json
data/03-ant-init-science-dilation-final-evidence-reverse-dag.json  <-  science/dilation/final-evidence/reverse-dag.json
data/03-ant-init-science-dilation-final-manifest.json  <-  science/dilation/final-manifest.json
data/03-ant-init-science-full_empty_dag_receipt.json  <-  science/full_empty_dag_receipt.json
data/03-ant-init-science-lineage-MANIFEST.v1.json  <-  science/lineage/MANIFEST.v1.json
data/03-ant-init-science-output_boundary_receipt.json  <-  science/output_boundary_receipt.json
data/03-ant-init-science-polynomial_receipt.json  <-  science/polynomial_receipt.json
data/03-ant-init-science-recipe_assets-ASSET_MANIFEST.json  <-  science/recipe_assets/ASSET_MANIFEST.json
data/03-ant-init-science-recipe_assets-copy-delayed_copy.json  <-  science/recipe_assets/copy/delayed_copy.json
data/03-ant-init-science-recipe_assets-copy-marker_left_start.json  <-  science/recipe_assets/copy/marker_left_start.json
data/03-ant-init-science-recipe_assets-copy-marker_right_stop.json  <-  science/recipe_assets/copy/marker_right_stop.json
data/03-ant-init-science-recipe_assets-copy-normalized_copy.json  <-  science/recipe_assets/copy/normalized_copy.json
data/03-ant-init-science-recipe_assets-copy-pair_dup.json  <-  science/recipe_assets/copy/pair_dup.json
data/03-ant-init-science-recipe_assets-copy-pair_move_left.json  <-  science/recipe_assets/copy/pair_move_left.json
data/03-ant-init-science-recipe_assets-copy-pair_move_right.json  <-  science/recipe_assets/copy/pair_move_right.json
data/03-ant-init-science-recipe_assets-nand-nand_macro.json  <-  science/recipe_assets/nand/nand_macro.json
data/03-ant-init-science-recipe_assets-not-normalized_not.json  <-  science/recipe_assets/not/normalized_not.json
data/03-ant-init-science-recipe_assets-strip-periodic_benchmark.json  <-  science/recipe_assets/strip/periodic_benchmark.json
data/03-ant-init-science-reviews-composition-composition_audit_receipt.json  <-  science/reviews/composition/composition_audit_receipt.json
data/03-ant-init-science-reviews-composition-composition_residual_receipt.json  <-  science/reviews/composition/composition_residual_receipt.json
data/03-ant-init-science-reviews-composition-degree_receipt.json  <-  science/reviews/composition/degree_receipt.json
data/03-ant-init-science-reviews-composition-helper_boundary_receipt.json  <-  science/reviews/composition/helper_boundary_receipt.json
data/03-ant-init-science-reviews-dilation-independent_bridge_receipt.json  <-  science/reviews/dilation/independent_bridge_receipt.json
data/03-ant-init-science-reviews-dilation-independent_exp_dag_receipt.json  <-  science/reviews/dilation/independent_exp_dag_receipt.json
data/03-ant-init-science-reviews-dilation-independent_exp_receipt.json  <-  science/reviews/dilation/independent_exp_receipt.json
data/03-ant-init-science-reviews-dilation-independent_final_cli_receipt.json  <-  science/reviews/dilation/independent_final_cli_receipt.json
data/03-ant-init-science-reviews-dilation-independent_literal_dag_receipt.json  <-  science/reviews/dilation/independent_literal_dag_receipt.json
data/03-ant-init-science-reviews-periodic-audit_receipt.json  <-  science/reviews/periodic/audit_receipt.json
data/03-ant-init-science-reviews-periodic-boundary_receipt.json  <-  science/reviews/periodic/boundary_receipt.json
data/03-ant-init-science-reviews-periodic-modular_receipt.json  <-  science/reviews/periodic/modular_receipt.json
data/03-ant-init-science-reviews-periodic-wrapper_receipt.json  <-  science/reviews/periodic/wrapper_receipt.json
data/03-ant-init-science-reviews-root_dilation_readonly_QA.json  <-  science/reviews/root_dilation_readonly_QA.json
data/03-ant-init-science-uniform_wrapper_receipt.json  <-  science/uniform_wrapper_receipt.json
data/03-ant-init-science-validation_boundary_receipt.json  <-  science/validation_boundary_receipt.json
data/03-ant-init-science-verification.json  <-  science/verification.json
data/03-ant-init-verification-recipe-projections.json  <-  verification/recipe-projections.json
data/03-ant-init-verification-recoder-degree-independent_degree_receipt.json  <-  verification/recoder-degree-independent_degree_receipt.json
data/03-ant-init-verification-release-review.json  <-  verification/release-review.json
data/03-ant-init-verification-scientific-source-lineage.json  <-  verification/scientific-source-lineage.json
data/03-ant-init-verification-tooling-review.json  <-  verification/tooling-review.json
data/03-ant-init-verification-visual-review.json  <-  verification/visual-review.json

# Report 44: 55 files, delivered under report44-recovered/
04-ant-cert-certificate-PROOF.md  <-  certificate/PROOF.md
04-ant-cert-certificate-README.md  <-  certificate/README.md
04-ant-cert-certificate-RECOVERY.md  <-  certificate/RECOVERY.md
04-ant-cert-certificate-STRICT_GRAMMAR.md  <-  certificate/STRICT_GRAMMAR.md
04-ant-cert-certificate-history-CONTRACT.md  <-  certificate/history/CONTRACT.md
04-ant-cert-certificate-independent-audit-AUDIT.md  <-  certificate/independent-audit/AUDIT.md
04-ant-cert-certificate-one-input-AUDIT.md  <-  certificate/one-input/AUDIT.md
04-ant-cert-verification-historical-QA.md  <-  verification/historical/QA.md
code/04-ant-cert-archive_release.py  <-  archive_release.py
code/04-ant-cert-build_pdf.py  <-  build_pdf.py
code/04-ant-cert-certificate-audit_recovered_stream.py  <-  certificate/audit_recovered_stream.py
code/04-ant-cert-certificate-check_exact_degree.py  <-  certificate/check_exact_degree.py
code/04-ant-cert-certificate-check_output_boundaries.py  <-  certificate/check_output_boundaries.py
code/04-ant-cert-certificate-history-audit_history.py  <-  certificate/history/audit_history.py
code/04-ant-cert-certificate-history-pin_recovered_sources.py  <-  certificate/history/pin_recovered_sources.py
code/04-ant-cert-certificate-history-reconstruct_history.py  <-  certificate/history/reconstruct_history.py
code/04-ant-cert-certificate-independent-audit-audit.py  <-  certificate/independent-audit/audit.py
code/04-ant-cert-certificate-independent-audit-check_pins.py  <-  certificate/independent-audit/check_pins.py
code/04-ant-cert-certificate-independent-audit-history_identities.py  <-  certificate/independent-audit/history_identities.py
code/04-ant-cert-certificate-independent-audit-top_degree.py  <-  certificate/independent-audit/top_degree.py
code/04-ant-cert-certificate-merged_source.py  <-  certificate/merged_source.py
code/04-ant-cert-certificate-verify_packet.py  <-  certificate/verify_packet.py
code/04-ant-cert-verify_release.py  <-  verify_release.py
data/04-ant-cert-MANIFEST.json  <-  MANIFEST.json
data/04-ant-cert-certificate-MANIFEST.json  <-  certificate/MANIFEST.json
data/04-ant-cert-certificate-SOURCE_PINS.json  <-  certificate/SOURCE_PINS.json
data/04-ant-cert-certificate-degree-receipt.json  <-  certificate/degree-receipt.json
data/04-ant-cert-certificate-history-RECOVERY.json  <-  certificate/history/RECOVERY.json
data/04-ant-cert-certificate-history-SOURCE_PINS.json  <-  certificate/history/SOURCE_PINS.json
data/04-ant-cert-certificate-history-audit-normal.log  <-  certificate/history/audit-normal.log
data/04-ant-cert-certificate-history-history174.json  <-  certificate/history/history174.json
data/04-ant-cert-certificate-history-reconstruction-optimized.log  <-  certificate/history/reconstruction-optimized.log
data/04-ant-cert-certificate-history-source-retrieval_metadata.json  <-  certificate/history/source/retrieval_metadata.json
data/04-ant-cert-certificate-history-verification.json  <-  certificate/history/verification.json
data/04-ant-cert-certificate-independent-audit-MANIFEST.json  <-  certificate/independent-audit/MANIFEST.json
data/04-ant-cert-certificate-independent-audit-audited-source-pins.json  <-  certificate/independent-audit/audited-source-pins.json
data/04-ant-cert-certificate-independent-audit-component-pin-receipt.json  <-  certificate/independent-audit/component-pin-receipt.json
data/04-ant-cert-certificate-independent-audit-degree-direct-receipt.json  <-  certificate/independent-audit/degree-direct-receipt.json
data/04-ant-cert-certificate-independent-audit-history-receipt.json  <-  certificate/independent-audit/history-receipt.json
data/04-ant-cert-certificate-independent-audit-receipt.json  <-  certificate/independent-audit/receipt.json
data/04-ant-cert-certificate-independent-stream-receipt.json  <-  certificate/independent-stream-receipt.json
data/04-ant-cert-certificate-one-input-receipt.json  <-  certificate/one-input-receipt.json
data/04-ant-cert-certificate-output-boundary-receipt.json  <-  certificate/output-boundary-receipt.json
data/04-ant-cert-certificate-two-input-receipt.json  <-  certificate/two-input-receipt.json
data/04-ant-cert-verification-historical-RECOVERED_QA_RECEIPT.json  <-  verification/historical/RECOVERED_QA_RECEIPT.json
data/04-ant-cert-verification-independent-science-freeze.json  <-  verification/independent-science-freeze.json
data/04-ant-cert-verification-manuscript-review.json  <-  verification/manuscript-review.json
data/04-ant-cert-verification-pdf-build.json  <-  verification/pdf-build.json
data/04-ant-cert-verification-pdf-reproduction.json  <-  verification/pdf-reproduction.json
data/04-ant-cert-verification-replay-review.json  <-  verification/replay-review.json
data/04-ant-cert-verification-science-freeze.json  <-  verification/science-freeze.json
data/04-ant-cert-verification-science-moved-replay.json  <-  verification/science-moved-replay.json
data/04-ant-cert-verification-toolchain.json  <-  verification/toolchain.json
data/04-ant-cert-verification-tooling-review.json  <-  verification/tooling-review.json
data/04-ant-cert-verification-visual-review.json  <-  verification/visual-review.json

# Report 47: 59 files, delivered under Research_Report47/
05-ant-coeffs-science-PROOF.md  <-  science/PROOF.md
05-ant-coeffs-science-README.md  <-  science/README.md
05-ant-coeffs-science-SPLICE.md  <-  science/SPLICE.md
05-ant-coeffs-science-geometry-README.md  <-  science/geometry/README.md
05-ant-coeffs-science-verification-independent-prefix-audit-AUDIT.md  <-  science/verification/independent-prefix-audit/AUDIT.md
05-ant-coeffs-science-verification-independent-prefix-audit-JOIN_ADDENDUM.md  <-  science/verification/independent-prefix-audit/JOIN_ADDENDUM.md
code/05-ant-coeffs-archive_release.py  <-  archive_release.py
code/05-ant-coeffs-build_pdf.py  <-  build_pdf.py
code/05-ant-coeffs-science-check_splice_contract.py  <-  science/check_splice_contract.py
code/05-ant-coeffs-science-full_prefix.py  <-  science/full_prefix.py
code/05-ant-coeffs-science-geometry-build_profiles.py  <-  science/geometry/build_profiles.py
code/05-ant-coeffs-science-geometry-profile_api.py  <-  science/geometry/profile_api.py
code/05-ant-coeffs-science-geometry-scan_boundaries.py  <-  science/geometry/scan_boundaries.py
code/05-ant-coeffs-science-geometry-scan_motifs.py  <-  science/geometry/scan_motifs.py
code/05-ant-coeffs-science-geometry-verify_profiles.py  <-  science/geometry/verify_profiles.py
code/05-ant-coeffs-science-join_strict.py  <-  science/join_strict.py
code/05-ant-coeffs-science-occurrence_compiler.py  <-  science/occurrence_compiler.py
code/05-ant-coeffs-science-verification-independent-prefix-audit-check_closed_counts.py  <-  science/verification/independent-prefix-audit/check_closed_counts.py
code/05-ant-coeffs-science-verification-independent-prefix-audit-check_emitted_source.py  <-  science/verification/independent-prefix-audit/check_emitted_source.py
code/05-ant-coeffs-science-verification-independent-prefix-audit-check_independent.py  <-  science/verification/independent-prefix-audit/check_independent.py
code/05-ant-coeffs-science-verification-independent-prefix-audit-check_join_independent.py  <-  science/verification/independent-prefix-audit/check_join_independent.py
code/05-ant-coeffs-science-verification-independent-prefix-audit-check_profiles.py  <-  science/verification/independent-prefix-audit/check_profiles.py
code/05-ant-coeffs-science-verify_manifest.py  <-  science/verify_manifest.py
code/05-ant-coeffs-verify_release.py  <-  verify_release.py
data/05-ant-coeffs-MANIFEST.json  <-  MANIFEST.json
data/05-ant-coeffs-joined_evidence.tex  <-  joined_evidence.tex
data/05-ant-coeffs-science-MANIFEST.json  <-  science/MANIFEST.json
data/05-ant-coeffs-science-geometry-boundary_scan.json  <-  science/geometry/boundary_scan.json
data/05-ant-coeffs-science-geometry-motif_scan.json  <-  science/geometry/motif_scan.json
data/05-ant-coeffs-science-geometry-profile_audit.json  <-  science/geometry/profile_audit.json
data/05-ant-coeffs-science-geometry-profiles-B.masks.json  <-  science/geometry/profiles/B.masks.json
data/05-ant-coeffs-science-geometry-profiles-F.masks.json  <-  science/geometry/profiles/F.masks.json
data/05-ant-coeffs-science-geometry-profiles-H.masks.json  <-  science/geometry/profiles/H.masks.json
data/05-ant-coeffs-science-geometry-profiles-MANIFEST.json  <-  science/geometry/profiles/MANIFEST.json
data/05-ant-coeffs-science-geometry-profiles-Q_DUP.json  <-  science/geometry/profiles/Q_DUP.json
data/05-ant-coeffs-science-geometry-profiles-Q_MOVE_LEFT.json  <-  science/geometry/profiles/Q_MOVE_LEFT.json
data/05-ant-coeffs-science-geometry-profiles-Q_MOVE_RIGHT.json  <-  science/geometry/profiles/Q_MOVE_RIGHT.json
data/05-ant-coeffs-science-geometry-profiles-Q_NAND.json  <-  science/geometry/profiles/Q_NAND.json
data/05-ant-coeffs-science-verification-full-prefix-receipt.json  <-  science/verification/full-prefix-receipt.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-JOIN_MANIFEST.json  <-  science/verification/independent-prefix-audit/JOIN_MANIFEST.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-MANIFEST.json  <-  science/verification/independent-prefix-audit/MANIFEST.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-SOURCE_PINS.json  <-  science/verification/independent-prefix-audit/SOURCE_PINS.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-closed-count-receipt.json  <-  science/verification/independent-prefix-audit/closed-count-receipt.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-emitted-source-receipt.json  <-  science/verification/independent-prefix-audit/emitted-source-receipt.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-joined-independent-receipt.json  <-  science/verification/independent-prefix-audit/joined-independent-receipt.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-profiles-optimized.log  <-  science/verification/independent-prefix-audit/profiles-optimized.log
data/05-ant-coeffs-science-verification-independent-prefix-audit-profiles-receipt.json  <-  science/verification/independent-prefix-audit/profiles-receipt.json
data/05-ant-coeffs-science-verification-independent-prefix-audit-receipt.json  <-  science/verification/independent-prefix-audit/receipt.json
data/05-ant-coeffs-science-verification-input-provenance.json  <-  science/verification/input-provenance.json
data/05-ant-coeffs-science-verification-joined-strict-receipt.json  <-  science/verification/joined-strict-receipt.json
data/05-ant-coeffs-science-verification-profiles-relocated-receipt.json  <-  science/verification/profiles-relocated-receipt.json
data/05-ant-coeffs-science-verification-static-splice-receipt.json  <-  science/verification/static-splice-receipt.json
data/05-ant-coeffs-verification-manuscript-review.json  <-  verification/manuscript-review.json
data/05-ant-coeffs-verification-pdf-reproduction.json  <-  verification/pdf-reproduction.json
data/05-ant-coeffs-verification-relocated-science-replay.json  <-  verification/relocated-science-replay.json
data/05-ant-coeffs-verification-report44-provenance.json  <-  verification/report44-provenance.json
data/05-ant-coeffs-verification-science-freeze.json  <-  verification/science-freeze.json
data/05-ant-coeffs-verification-toolchain.json  <-  verification/toolchain.json
data/05-ant-coeffs-verification-visual-review.json  <-  verification/visual-review.json

# Report 48: 51 files, delivered under Research_Report48/
06-ant-fusion-audit_replay-README.md  <-  audit_replay/README.md
06-ant-fusion-independent_audit-AUDIT.md  <-  independent_audit/AUDIT.md
06-ant-fusion-independent_audit-GENERIC_PROOF.md  <-  independent_audit/GENERIC_PROOF.md
06-ant-fusion-science-PROOF.md  <-  science/PROOF.md
06-ant-fusion-science-README.md  <-  science/README.md
06-ant-fusion-verification-manuscript_review-REVIEW.md  <-  verification/manuscript_review/REVIEW.md
code/06-ant-fusion-archive_release.py  <-  archive_release.py
code/06-ant-fusion-audit_replay-replay_independent_audit.py  <-  audit_replay/replay_independent_audit.py
code/06-ant-fusion-build_pdf.py  <-  build_pdf.py
code/06-ant-fusion-independent_audit-audit_caches_weights.py  <-  independent_audit/audit_caches_weights.py
code/06-ant-fusion-independent_audit-audit_exact.py  <-  independent_audit/audit_exact.py
code/06-ant-fusion-science-checks.py  <-  science/checks.py
code/06-ant-fusion-science-fusion_source.py  <-  science/fusion_source.py
code/06-ant-fusion-verification-manuscript_review-check_manuscript.py  <-  verification/manuscript_review/check_manuscript.py
code/06-ant-fusion-verification-manuscript_review-check_old_main.py  <-  verification/manuscript_review/check_old_main.py
code/06-ant-fusion-verify_release.py  <-  verify_release.py
data/06-ant-fusion-MANIFEST.json  <-  MANIFEST.json
data/06-ant-fusion-audit_replay-MANIFEST.json  <-  audit_replay/MANIFEST.json
data/06-ant-fusion-audit_replay-replay-test-receipt.json  <-  audit_replay/replay-test-receipt.json
data/06-ant-fusion-audit_replay-replay-test.log  <-  audit_replay/replay-test.log
data/06-ant-fusion-audit_replay-write-guard-tests.json  <-  audit_replay/write-guard-tests.json
data/06-ant-fusion-block_groups.tex  <-  block_groups.tex
data/06-ant-fusion-independent_audit-MANIFEST.json  <-  independent_audit/MANIFEST.json
data/06-ant-fusion-independent_audit-audit-receipt.json  <-  independent_audit/audit-receipt.json
data/06-ant-fusion-independent_audit-audit-run.log  <-  independent_audit/audit-run.log
data/06-ant-fusion-independent_audit-caches-weights-receipt.json  <-  independent_audit/caches-weights-receipt.json
data/06-ant-fusion-independent_audit-caches-weights-run.log  <-  independent_audit/caches-weights-run.log
data/06-ant-fusion-independent_audit-finite-identities.json  <-  independent_audit/finite-identities.json
data/06-ant-fusion-independent_audit-frozen-after.json  <-  independent_audit/frozen-after.json
data/06-ant-fusion-release_evidence.tex  <-  release_evidence.tex
data/06-ant-fusion-science-INPUT_PINS.json  <-  science/INPUT_PINS.json
data/06-ant-fusion-science-MANIFEST.json  <-  science/MANIFEST.json
data/06-ant-fusion-science-checks-receipt.json  <-  science/checks-receipt.json
data/06-ant-fusion-science-checks-run.log  <-  science/checks-run.log
data/06-ant-fusion-science-fused-receipt.json  <-  science/fused-receipt.json
data/06-ant-fusion-science-fused-run.log  <-  science/fused-run.log
data/06-ant-fusion-verification-author-replay.json  <-  verification/author-replay.json
data/06-ant-fusion-verification-coordinating-review.json  <-  verification/coordinating-review.json
data/06-ant-fusion-verification-full-replay.json  <-  verification/full-replay.json
data/06-ant-fusion-verification-manuscript_review-check-run.log  <-  verification/manuscript_review/check-run.log
data/06-ant-fusion-verification-manuscript_review-input-snapshot.json  <-  verification/manuscript_review/input-snapshot.json
data/06-ant-fusion-verification-manuscript_review-old-main-check-receipt.json  <-  verification/manuscript_review/old-main-check-receipt.json
data/06-ant-fusion-verification-manuscript_review-pdf-text.txt  <-  verification/manuscript_review/pdf-text.txt
data/06-ant-fusion-verification-manuscript_review-review-receipt.json  <-  verification/manuscript_review/review-receipt.json
data/06-ant-fusion-verification-pdf-reproduction.json  <-  verification/pdf-reproduction.json
data/06-ant-fusion-verification-preservation.json  <-  verification/preservation.json
data/06-ant-fusion-verification-protected-after.json  <-  verification/protected-after.json
data/06-ant-fusion-verification-provenance.json  <-  verification/provenance.json
data/06-ant-fusion-verification-release-readiness.json  <-  verification/release-readiness.json
data/06-ant-fusion-verification-toolchain.json  <-  verification/toolchain.json
data/06-ant-fusion-verification-visual-review.json  <-  verification/visual-review.json
```

### Not shipped (Parts II–IV)

Of the 590 delivered files of the five archives, 381 are shipped and 209 are
not. All of them survive in the archives of the arrival commit:

```sh
git show c5612efa1:docs/incoming/Literal_Periodic_Langton_Ant_and_Visit_Boundary_Package.zip > r40.zip
git show c5612efa1:docs/incoming/Arithmetic_Initialization_for_a_Periodic_Langton_Ant_Package.zip > r42.zip
git show c5612efa1:docs/incoming/Complete_Positive_Certificate_for_the_Literal_Periodic_Ant_Package.zip > r44.zip
git show c5612efa1:docs/incoming/Exact_Structured_Construction_of_the_Fixed_Ant_Coefficients_Package.zip > r47.zip
git show c5612efa1:docs/incoming/Exact_Fusion_of_the_Ant_Background_Polynomials_Package.zip > r48.zip
```

- **Manuscripts, READMEs, PDFs and checksum manifests** (21 files): the five
  main `.tex` files and five delivery `README.md` files (replaced by
  `article.tex` and this README); seven PDFs (the five reports, Report 40's
  copy of `Research_Report38.pdf`, Report 48's copy of
  `Research_Report47.pdf`); four checksum manifests (Report 40's
  `SHA256SUMS`, and in its Report 38 companion `SHA256SUMS` and the two
  `manifest-sha256.json`), all verified at placement.
- **Third-party Mathlib files** (4): `PellMatiyasevic.lean` and
  `LICENSE.mathlib` in Report 42 (`science/dependencies/mathlib/`) and in
  Report 44 (`certificate/dependencies/mathlib/`). They are Mathlib commit
  `ac77769fabe23cb237559e7f56578dbead91499f`, file SHA-256
  `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`,
  Apache-2.0; the shipped pin record is
  `data/03-ant-init-science-dependencies-mathlib-primary_source_pin.json`.
  The archives never execute them.
- **Byte copies of repository files** (58), cited by path:
  - Report 40 `evidence/one-visit-companion/` (43 files): Report 38's
    package, byte for byte; these are Part I's shipped files (for example
    `evidence/source-packet/one_visit.py` = `code/source-packet-one_visit.py`,
    `Research_Report38.tex` = the article text of Part I as placed in
    `a51a439cd`).
  - Report 40 `evidence/literal-interface/ca/u15_table.json` =
    `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/data/16-universal-membrane-tm_table.json`.
  - The research tree: Report 42 `dependencies/HISTORY174.md`, Report 44
    `certificate/dependencies/HISTORY174.md` and
    `certificate/history/source/HISTORY174.md` =
    `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md`;
    Report 44 `certificate/history/source/` `EXPLORATION_BASE_THREE_PELL_KERNEL.md`,
    `EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md`, `HALF_PARAMETER_PELL_92_PROOF.md`,
    `PELL_RELAXED_AUXILIARY_PROOF.md`, `PELL_SIGNED_PROOF.md` = the files of
    the same names in `Computability/HilbertTenthProblem/Papers/1980/`, and
    `explore_ant_checkerboard_history.py.txt`,
    `explore_base_three_pell_kernel.py.txt` =
    `Computability/HilbertTenthProblem/Papers/verification/explore_ant_checkerboard_history.py`
    and `explore_base_three_pell_kernel.py`.
  - The committed archives: Report 47 `references/Report44_recovered_authenticated.zip`
    = the Report 44 archive; Report 48 `references/Research_Report47_reproducibility.zip`
    = the Report 47 archive, and its loose `references/Research_Report47.tex`
    and `references/MANIFEST.json` = members of that archive.
- **In-batch duplicates** (99), each shipped once, at its first occurrence
  in the order 40, 42, 44, 47, 48. Every one, by delivered name (`=` the
  shipped file it duplicates):

```
Report 40 evidence/endpoint/literal_source_verification.log = data/02-literal-ant-endpoint-literal_source_verification.json
Report 42 dependencies/ENDPOINT-FIVE-WITNESS.md = 02-literal-ant-endpoint-FIVE_WITNESS_ENDPOINT_ADDENDUM.md
Report 42 dependencies/literal-interface-gate.json = data/02-literal-ant-literal-interface-INTERFACE_GATE.json
Report 42 recoder-degree/degree_receipt_optimized.json = data/03-ant-init-recoder-degree-degree_receipt.json
Report 42 science/data/anchor_patch.json = data/02-literal-ant-literal-interface-copy-fixed_initial_anchor_patch.json
Report 42 science/dependencies/endpoint_CONTRACT.md = 02-literal-ant-endpoint-CONTRACT.md
Report 42 science/dependencies/literal_interface_PROOF.md = 02-literal-ant-literal-interface-atlas-PROOF.md
Report 42 science/dependencies/literal_interface_SOURCE_PROVENANCE.md = 02-literal-ant-literal-interface-SOURCE_PROVENANCE.md
Report 42 science/dilation/final-evidence/pair_inline-dag.json = data/03-ant-init-science-data-pair_inline-dag.json
Report 42 science/recipe_assets/atlas/generator.py = code/02-literal-ant-literal-interface-atlas-generator.py
Report 42 science/recipe_assets/ca/physical_program.json = data/02-literal-ant-literal-interface-ca-physical_program.json
Report 42 science/recipe_assets/ca/physical_program.py = code/02-literal-ant-literal-interface-ca-physical_program.py
Report 42 science/recipe_assets/common/primitive_maps.json = data/02-literal-ant-literal-interface-common-primitive_maps.json
Report 42 science/reviews/dilation/primary_source_pin.json = data/03-ant-init-science-dependencies-mathlib-primary_source_pin.json
Report 44 certificate/data/anchor_patch.json = data/02-literal-ant-literal-interface-copy-fixed_initial_anchor_patch.json
Report 44 certificate/data/endpoint_folded_fixed_numerals_source.json = data/02-literal-ant-endpoint-endpoint_folded_fixed_numerals_source.json
Report 44 certificate/data/pair_inline-dag.json = data/03-ant-init-science-data-pair_inline-dag.json
Report 44 certificate/dependencies/COMPOSITION.md = 03-ant-init-science-COMPOSITION.md
Report 44 certificate/dependencies/CONTRACT.md = 02-literal-ant-endpoint-CONTRACT.md
Report 44 certificate/dependencies/DEGREE.md = 03-ant-init-science-DEGREE.md
Report 44 certificate/dependencies/ENDPOINT_AUDIT.md = 02-literal-ant-endpoint-ENDPOINT_AUDIT.md
Report 44 certificate/dependencies/FOLDED_ENDPOINT_ADDENDUM.md = 02-literal-ant-endpoint-FOLDED_ENDPOINT_ADDENDUM.md
Report 44 certificate/dependencies/literal_interface_PROOF.md = 02-literal-ant-literal-interface-atlas-PROOF.md
Report 44 certificate/dependencies/mathlib/primary_source_pin.json = data/03-ant-init-science-dependencies-mathlib-primary_source_pin.json
Report 44 certificate/dependencies/PROOF.md = 03-ant-init-science-PROOF.md
Report 44 certificate/dependencies/recipe_assets/ASSET_MANIFEST.json = data/03-ant-init-science-recipe_assets-ASSET_MANIFEST.json
Report 44 certificate/dependencies/recipe_assets/atlas/generator.py = code/02-literal-ant-literal-interface-atlas-generator.py
Report 44 certificate/dependencies/recipe_assets/ca/physical_program.json = data/02-literal-ant-literal-interface-ca-physical_program.json
Report 44 certificate/dependencies/recipe_assets/ca/physical_program.py = code/02-literal-ant-literal-interface-ca-physical_program.py
Report 44 certificate/dependencies/recipe_assets/common/primitive_maps.json = data/02-literal-ant-literal-interface-common-primitive_maps.json
Report 44 certificate/dependencies/recipe_assets/copy/delayed_copy.json = data/03-ant-init-science-recipe_assets-copy-delayed_copy.json
Report 44 certificate/dependencies/recipe_assets/copy/marker_left_start.json = data/03-ant-init-science-recipe_assets-copy-marker_left_start.json
Report 44 certificate/dependencies/recipe_assets/copy/marker_right_stop.json = data/03-ant-init-science-recipe_assets-copy-marker_right_stop.json
Report 44 certificate/dependencies/recipe_assets/copy/normalized_copy.json = data/03-ant-init-science-recipe_assets-copy-normalized_copy.json
Report 44 certificate/dependencies/recipe_assets/copy/pair_dup.json = data/03-ant-init-science-recipe_assets-copy-pair_dup.json
Report 44 certificate/dependencies/recipe_assets/copy/pair_move_left.json = data/03-ant-init-science-recipe_assets-copy-pair_move_left.json
Report 44 certificate/dependencies/recipe_assets/copy/pair_move_right.json = data/03-ant-init-science-recipe_assets-copy-pair_move_right.json
Report 44 certificate/dependencies/recipe_assets/nand/nand_macro.json = data/03-ant-init-science-recipe_assets-nand-nand_macro.json
Report 44 certificate/dependencies/recipe_assets/not/normalized_not.json = data/03-ant-init-science-recipe_assets-not-normalized_not.json
Report 44 certificate/dependencies/recipe_assets/README.md = 03-ant-init-science-recipe_assets-README.md
Report 44 certificate/dependencies/recipe_assets/strip/periodic_benchmark.json = data/03-ant-init-science-recipe_assets-strip-periodic_benchmark.json
Report 44 certificate/dependencies/RECODER_PROOF.md = 03-ant-init-science-dilation-PROOF.md
Report 44 certificate/history/audit-optimized.log = data/04-ant-cert-certificate-history-audit-normal.log
Report 44 certificate/history/audit_receipt.json = data/04-ant-cert-certificate-history-audit-normal.log
Report 44 certificate/independent-audit/component-pin-replay.log = data/04-ant-cert-certificate-independent-audit-component-pin-receipt.json
Report 44 certificate/independent-audit/degree-direct-replay.log = data/04-ant-cert-certificate-independent-audit-degree-direct-receipt.json
Report 44 certificate/independent-audit/history-replay.log = data/04-ant-cert-certificate-independent-audit-history-receipt.json
Report 44 certificate/independent-audit/replay.log = data/04-ant-cert-certificate-independent-audit-receipt.json
Report 47 science/data/anchor_patch.json = data/02-literal-ant-literal-interface-copy-fixed_initial_anchor_patch.json
Report 47 science/data/main_receipts/one-input-receipt.json = data/04-ant-cert-certificate-one-input-receipt.json
Report 47 science/data/main_receipts/two-input-receipt.json = data/04-ant-cert-certificate-two-input-receipt.json
Report 47 science/data/recipe_assets/ASSET_MANIFEST.json = data/03-ant-init-science-recipe_assets-ASSET_MANIFEST.json
Report 47 science/data/recipe_assets/ca/physical_program.json = data/02-literal-ant-literal-interface-ca-physical_program.json
Report 47 science/data/recipe_assets/common/primitive_maps.json = data/02-literal-ant-literal-interface-common-primitive_maps.json
Report 47 science/data/recipe_assets/copy/delayed_copy.json = data/03-ant-init-science-recipe_assets-copy-delayed_copy.json
Report 47 science/data/recipe_assets/copy/marker_left_start.json = data/03-ant-init-science-recipe_assets-copy-marker_left_start.json
Report 47 science/data/recipe_assets/copy/marker_right_stop.json = data/03-ant-init-science-recipe_assets-copy-marker_right_stop.json
Report 47 science/data/recipe_assets/copy/normalized_copy.json = data/03-ant-init-science-recipe_assets-copy-normalized_copy.json
Report 47 science/data/recipe_assets/copy/pair_dup.json = data/03-ant-init-science-recipe_assets-copy-pair_dup.json
Report 47 science/data/recipe_assets/copy/pair_move_left.json = data/03-ant-init-science-recipe_assets-copy-pair_move_left.json
Report 47 science/data/recipe_assets/copy/pair_move_right.json = data/03-ant-init-science-recipe_assets-copy-pair_move_right.json
Report 47 science/data/recipe_assets/nand/nand_macro.json = data/03-ant-init-science-recipe_assets-nand-nand_macro.json
Report 47 science/data/recipe_assets/not/normalized_not.json = data/03-ant-init-science-recipe_assets-not-normalized_not.json
Report 47 science/data/recipe_assets/strip/periodic_benchmark.json = data/03-ant-init-science-recipe_assets-strip-periodic_benchmark.json
Report 47 science/main_source/data/endpoint_folded_fixed_numerals_source.json = data/02-literal-ant-endpoint-endpoint_folded_fixed_numerals_source.json
Report 47 science/main_source/data/pair_inline-dag.json = data/03-ant-init-science-data-pair_inline-dag.json
Report 47 science/main_source/history/history174.json = data/04-ant-cert-certificate-history-history174.json
Report 47 science/main_source/merged_source.py = code/04-ant-cert-certificate-merged_source.py
Report 47 science/specifications/atlas-generator.py.txt = code/02-literal-ant-literal-interface-atlas-generator.py
Report 47 science/specifications/ca-physical_program.py.txt = code/02-literal-ant-literal-interface-ca-physical_program.py
Report 47 science/verification/full-prefix-run.log = data/05-ant-coeffs-science-verification-full-prefix-receipt.json
Report 47 science/verification/independent-prefix-audit/counts-run.log = data/05-ant-coeffs-science-verification-independent-prefix-audit-closed-count-receipt.json
Report 47 science/verification/independent-prefix-audit/profiles-run.log = data/05-ant-coeffs-science-verification-independent-prefix-audit-profiles-receipt.json
Report 47 science/verification/independent-prefix-audit/run-optimized.log = data/05-ant-coeffs-science-verification-independent-prefix-audit-receipt.json
Report 47 science/verification/independent-prefix-audit/run.log = data/05-ant-coeffs-science-verification-independent-prefix-audit-receipt.json
Report 47 science/verification/joined-strict-run.log = data/05-ant-coeffs-science-verification-joined-strict-receipt.json
Report 47 science/verification/profiles-relocated-run.log = data/05-ant-coeffs-science-geometry-profiles-MANIFEST.json
Report 48 independent_audit/frozen-before.json = data/06-ant-fusion-independent_audit-frozen-after.json
Report 48 science/data/anchor_patch.json = data/02-literal-ant-literal-interface-copy-fixed_initial_anchor_patch.json
Report 48 science/data/physical_program.json = data/02-literal-ant-literal-interface-ca-physical_program.json
Report 48 science/data/profiles/B.masks.json = data/05-ant-coeffs-science-geometry-profiles-B.masks.json
Report 48 science/data/profiles/B.u16le = (not shipped) Report 47 science/geometry/profiles/B.u16le
Report 48 science/data/profiles/F.masks.json = data/05-ant-coeffs-science-geometry-profiles-F.masks.json
Report 48 science/data/profiles/F.u16le = (not shipped) Report 47 science/geometry/profiles/F.u16le
Report 48 science/data/profiles/H.masks.json = data/05-ant-coeffs-science-geometry-profiles-H.masks.json
Report 48 science/data/profiles/H.u16le = (not shipped) Report 47 science/geometry/profiles/H.u16le
Report 48 science/data/profiles/MANIFEST.json = data/05-ant-coeffs-science-geometry-profiles-MANIFEST.json
Report 48 science/data/profiles/Q_DUP.json = data/05-ant-coeffs-science-geometry-profiles-Q_DUP.json
Report 48 science/data/profiles/Q_MOVE_LEFT.json = data/05-ant-coeffs-science-geometry-profiles-Q_MOVE_LEFT.json
Report 48 science/data/profiles/Q_MOVE_RIGHT.json = data/05-ant-coeffs-science-geometry-profiles-Q_MOVE_RIGHT.json
Report 48 science/data/profiles/Q_NAND.json = data/05-ant-coeffs-science-geometry-profiles-Q_NAND.json
Report 48 science/owned_report44/data/endpoint_folded_fixed_numerals_source.json = data/02-literal-ant-endpoint-endpoint_folded_fixed_numerals_source.json
Report 48 science/owned_report44/data/pair_inline-dag.json = data/03-ant-init-science-data-pair_inline-dag.json
Report 48 science/owned_report44/history/history174.json = data/04-ant-cert-certificate-history-history174.json
Report 48 science/owned_report44/merged_source.py = code/04-ant-cert-certificate-merged_source.py
Report 48 science/owned_report47/occurrence_compiler.py = code/05-ant-coeffs-science-occurrence_compiler.py
Report 48 verification/manuscript_review/manuscript-check-receipt.json = data/06-ant-fusion-verification-manuscript_review-check-run.log
Report 48 verification/manuscript_review/old-main-run.log = data/06-ant-fusion-verification-manuscript_review-old-main-check-receipt.json
Report 48 verification/protected-before.json = data/06-ant-fusion-verification-protected-after.json
```

- **Large regenerable files** (27, 156,191,017 bytes): next section.

### Shipped files whose text uses delivery names or names unshipped files

Part I: `INTEGRITY.md` (`evidence/source-packet/`, `verification/`,
`SHA256SUMS`, `MANIFEST.json` at the root); `source-packet-README.md`
(`boundary-context/`, `manifest-sha256.json`, unprefixed program names, and
"run from this directory: `python example.py`, `python verify_release.py`");
`source-packet-boundary-context-README.md` and
`source-packet-boundary-context-proof.md` (`test_one_visit.py`);
`code/verify_release.py`, `code/tamper_regression.py`, `code/seal_release.py`,
`code/build_pdf.py`, `code/archive_release.py`, `code/archive_regression.py`
(`Research_Report38/`, `evidence/source-packet/`, `verification/`,
`SHA256SUMS`, `manifest-sha256.json`); `code/source-packet-verify_release.py`
(`manifest-sha256.json`, `boundary-context/`); `data/MANIFEST.json`,
`data/verification-replay-plan.json` and `data/verification-source-lineage.json`
(delivered paths throughout). The Python programs import each other by their
delivered module names (`one_visit`, `observations`), so none runs under its
shipped name. The article's Appendix A names the delivered files; a `[write]`
note there gives the shipped names.

Parts II–IV: **all** of them, in effect. Every delivered Markdown note,
receipt, manifest (`*MANIFEST*.json`, `SOURCE_PINS.json`, `INPUT_PINS.json`,
`*-lineage.json`, `replay-plan.json`) and program uses the delivered layout:
paths such as `evidence/literal-interface/copy/…`, `science/…`,
`certificate/…`, `references/…`, `verification/…`, module imports by
delivered names (`geometry_kit`, `physical_program`, `profile_api`,
`occurrence_compiler`, `merged_source`, …), and the unshipped files listed
above (the Report 38 companion, `ca/u15_table.json`, the heavy files, the
Mathlib file, `HISTORY174.md`, the reference archives, the `SHA256SUMS`
files, the delivery READMEs and PDFs). Specific cases:

- the five root `MANIFEST.json` files (`data/0N-…-MANIFEST.json`) inventory
  the delivered layout with POSIX modes; Report 40's records its
  `verify_release.py` with the `MANIFEST_SHA256` line zeroed (the documented
  normalized self-pin; the embedded pin equals the SHA-256 of the manifest,
  `f44d98ff…`);
- Report 42's `data/03-ant-init-science-lineage-MANIFEST.v1.json` is the v1
  inventory: 72 of its 73 entries match; the 73rd, `replay.py`, is the
  revision documented in `03-ant-init-science-REVISION.md`;
- Report 44's `data/04-ant-cert-certificate-history-SOURCE_PINS.json` has two
  entries that do not resolve here (an external `Research_Report40.tex` and a
  `/workspace/…` prototype path); Report 47's
  `data/05-ant-coeffs-science-verification-independent-prefix-audit-SOURCE_PINS.json`
  lists 34 `/workspace/shared/…` prototype paths (the report says these
  historical checkers "have prototype absolute paths"); Report 48's
  `science/INPUT_PINS.json` records absolute source paths "for provenance
  only";
- the article's Section 40.16 and Appendix 40.B, Section 42.11 and Appendix 42.A,
  Section 44.10 and Appendix 44.A, Section 47.10 and Appendix 48.B describe the delivered
  layout; `[write]` notes there give the shipped names.

## Reconstructing the excluded data

Vladimir, 2026-10-02: "Exclude heavy regenerable artifacts". Twenty-seven
delivered files larger than 1 MB (and Report 48's copies of three of them)
are not shipped; each is regenerated byte
for byte by shipped programs, and each is also in the arrival archive.

| Report | Delivered path | Bytes |
|---|---|---:|
| 40 | `evidence/literal-interface/ca/radius_half_11_table_le.bin` | 8,388,608 |
| 40 | `evidence/literal-interface/copy/atlas_compatibility_receipt.json` | 3,938,632 |
| 40 | `evidence/literal-interface/copy/copy_family_member.json` | 1,634,133 |
| 40 | `evidence/literal-interface/copy/copy_macro.json` | 1,628,560 |
| 40 | `evidence/literal-interface/copy/delayed_copy.json` | 8,608,726 |
| 40 | `evidence/literal-interface/copy/fanout2_family_member.json` | 2,945,961 |
| 40 | `evidence/literal-interface/copy/fanout3_family_member.json` | 4,266,879 |
| 40 | `evidence/literal-interface/copy/header_entry_only_receipt.json` | 3,925,619 |
| 40 | `evidence/literal-interface/copy/marker_left_start.json` | 6,098,452 |
| 40 | `evidence/literal-interface/copy/marker_neighbors_receipt.json` | 1,217,166 |
| 40 | `evidence/literal-interface/copy/marker_right_stop.json` | 5,538,382 |
| 40 | `evidence/literal-interface/copy/moved_copy_left_family_member.json` | 2,883,793 |
| 40 | `evidence/literal-interface/copy/moved_copy_right_family_member.json` | 2,733,092 |
| 40 | `evidence/literal-interface/copy/normalized_copy.json` | 2,125,043 |
| 40 | `evidence/literal-interface/copy/normalized_fanout2.json` | 4,683,054 |
| 40 | `evidence/literal-interface/copy/normalized_fanout3.json` | 7,281,954 |
| 40 | `evidence/literal-interface/copy/normalized_moved_copy_left.json` | 4,622,162 |
| 40 | `evidence/literal-interface/copy/normalized_moved_copy_right.json` | 4,473,623 |
| 40 | `evidence/literal-interface/copy/pair_dup.json` | 19,720,266 |
| 40 | `evidence/literal-interface/copy/pair_move_left.json` | 19,630,214 |
| 40 | `evidence/literal-interface/copy/pair_move_right.json` | 19,224,406 |
| 40 | `evidence/literal-interface/nand/nand_macro.json` | 5,934,033 |
| 40 | `evidence/literal-interface/not/normalized_not.json` | 1,479,762 |
| 40 | `evidence/literal-interface/strip/independent_cycle_certificate.json` | 9,752,497 |
| 47 | `science/geometry/profiles/B.u16le` | 1,152,000 |
| 47 | `science/geometry/profiles/F.u16le` | 1,152,000 |
| 47 | `science/geometry/profiles/H.u16le` | 1,152,000 |

Total 156,191,017 bytes. Report 48's three `science/data/profiles/*.u16le`
(3,456,000 bytes) are copies of Report 47's and are counted among the
in-batch duplicates.

**Retrieval.** The simplest route is the archive itself:

```sh
git show c5612efa1:docs/incoming/Literal_Periodic_Langton_Ant_and_Visit_Boundary_Package.zip > r40.zip
unzip -q r40.zip 'Research_Report40/evidence/literal-interface/*' -d /scratch/r40
git show c5612efa1:docs/incoming/Exact_Structured_Construction_of_the_Fixed_Ant_Coefficients_Package.zip > r47.zip
unzip -q r47.zip 'Research_Report47/science/geometry/profiles/*' -d /scratch/r47
```

**Regeneration, Report 40 (24 files; tested at placement: 24/24 equal, 52 s
on Windows with Python 3.14.4).** Work in a copy of the delivered layout of
`evidence/literal-interface/`, outside the repository: either extract it
from the archive and delete the 24 files, or rebuild it from the shipped
`*02-literal-ant-literal-interface-*` files under their delivered names (the
map above) plus `ca/u15_table.json` (a copy of the `quadratic-orthant-certificates`
file named above). Then run, from `/` (the programs locate their data from
their own paths and write their outputs in place),

```sh
L=/scratch/r40/Research_Report40/evidence/literal-interface
cd / && for c in copy/build_copy.py copy/build_copy_family.py \
  nand/build_nand.py not/build_not.py copy/build_normalized_copy_family.py \
  copy/build_delayed_copy.py copy/build_pair_instructions.py \
  strip/build_periodic_benchmark.py strip/verify_periodic_benchmark.py \
  copy/verify_copy_family.py copy/verify_delayed_copy.py \
  copy/verify_pair_instructions.py copy/audit_atlas_compatibility.py \
  copy/build_marker_variants.py copy/build_initial_anchor.py \
  copy/verify_marker_variants.py copy/verify_marker_neighbors.py \
  copy/verify_header_entry_only.py copy/translate_anchor.py \
  ca/build_ca_circuit.py ca/verify_complete_tables.py ca/physical_program.py \
  ca/verify_program_ledger.py copy/program_audit/verify_program_index_bounds.py \
  copy/review_global_generator.py plans/boolean_word_programs.py \
  atlas/check_initialization_observer.py atlas/verify_observer_polarity.py \
  atlas/quantitative_ledger.py; do python3 -B $L/$c || break; done
python3 -B $L/atlas/compile_input.py --selfcheck
```

that is, `copy/build_copy.py` and `copy/build_copy_family.py` (which write
the six `*family_member.json` and `copy_macro.json` files that the driver
does not list) and then the 28 `COMMANDS` of `replay_all.py`, in order.
Use normal Python, not `-O` (the scientific checks are assertions). On
Windows, Python writes text files with CRLF line endings; the placement test
forced LF text writes with a `sitecustomize.py` shim. Without one, compare
text outputs after removing `\r`. Note that `replay_all.py` itself and the
release verifiers compare against the heavy files, so restore them first.

**Regeneration, Report 47 (3 files; tested at placement: all 11 profile
artifacts byte-identical, 7 s).** In an extraction of the Report 47 archive,

```sh
cd /scratch/r47/Research_Report47 && python3 -B science/geometry/build_profiles.py --out /scratch/new-profiles
```

writes `B.u16le`, `F.u16le`, `H.u16le` (1,152,000 bytes each) and the eight
other profile files into the new directory (which must not exist); the
shipped `code/05-ant-coeffs-science-geometry-build_profiles.py` is that
program. Report 48's copies are the same three files.

Staging all 27 would have added about 156 MB, including three single files
of 19.2–19.7 MB; the archives of the five reports total 13,278,695 bytes.

## Labels and numbering

266 labels in all, every one with the prefix `ptr:`.

- **Part I** keeps its 61 labels (`ptr:` plus the delivered names, and the
  batch-83 write's `ptr:sec:preface`, `ptr:app:provenance`) and every number:
  sections 1–12, appendices A–C, its equation, statement and figure numbers.
  At the batch-88 write this was checked by comparing the `.aux` label
  numbers of the committed text with the new build: all 61 identical.
- **Parts II–IV**: the 192 delivered labels gained a sub-prefix per source:
  `ptr:la:` (Report 40, 53 labels), `ptr:ai:` (Report 42, 56), `ptr:pc:`
  (Report 44, 20), `ptr:sc:` (Report 47, 26), `ptr:fu:` (Report 48, 37).
  Their numbers carry the report number: section, statement and equation `k`
  of Report NN is printed `NN.k`, appendix X as `NN.X`.
- **Written at batch 88** (13): `ptr:part:fr`, `ptr:part:la`,
  `ptr:part:cert`, `ptr:part:src`, `ptr:sec:overview`, `ptr:it:scope`,
  `ptr:sec:prov88`, `ptr:la:sec:intro`, `ptr:ai:sec:intro`,
  `ptr:pc:sec:intro`, `ptr:pc:wr:sizes`, `ptr:sc:sec:intro`,
  `ptr:fu:sec:intro`.

Text written at a write is marked `[write]`; dated corrections in Part I
begin "Note added with Parts II–IV (batch 88, 3 October 2026)". Unmarked
text is the manuscripts' own. The write's own bibliography (the programme
notes) uses the labels W1–W5.

## Setting and notation

Part I: cyclic L/R turmite, rule word `w ∈ {L,R}^m`, explicitly listed `u×v`
tile `b`, finite defect map `D` (`K = |dom D|`), start `p_0`, heading `h_0`,
`y` north-positive; time `t` is the configuration **before departure**; `τ`
is the first time the head stands on a position it occupied before, whatever
the heading; `S = 4uv`. Its preface lists its own letter collisions (`L, R,
A, B, Q, q, a, b, c, s, r, C, E, F, H, M, N`).

Parts II–IV: the binary RL ant (colour 0 turns right, 1 left; turn, flip,
move), coordinates east/**south**-positive in Report 40, the rotation
`X = b − 75, Y = 288650 − a` (start facing north) in Reports 42 and 44. The
preface to the four Parts has a table of the letters the six reports reuse;
no symbol was renamed. The readings most likely to be confused:

- `u, v`: Part I's tile sides vs the rotated periods `u = 481238074400`,
  `v = 576000` of Appendix 40.D and Reports 42/44;
- `S`: Part I's `4uv` vs the horizontal period 576000 (which Reports 42/44's
  code calls `V`); `V = 400(R+2)` in Reports 40/47, renamed `L` in Report 48;
- `W`: Report 40's 960 column slots vs the history radix `3^w` (an
  independent degree-one variable in every degree count);
- `K`: Part I's defect count, Report 40's 958 active columns, Reports 47/48's
  957 pair indices, a repunit witness in 42/44;
- `F`, `H`: Report 44's final polynomials `F_2, F_1` and halting predicate
  `H(x,y)` (Report 48: `𝒫_2`, `𝓗`) vs footer and header profiles `F[x]`,
  `H[x]` (47/48) and other uses;
- **revisit** (Part I) is repetition of the position only; **visit** (Part
  II) is an arrival snapshot, and "at most two visits" is over the whole
  infinite run;
- **universal**: see "What the certificate is not" above.

## What is claimed, and what is not

**Part I** claims conventional mathematical proofs of:

- the total first-revisit algorithm with exact output or a no-revisit
  certificate with periodic tail `1 ≤ L ≤ 4uv`, `0 ≠ δ ∈ uZ × vZ`, at most
  `(K+1)4uv` lanes, polynomial bit complexity (Theorem 2.2), via the static
  shadow (Lemma 3.1), the projected-permutation lemma (Lemma 3.2), the exact
  rank-2/1/0 intersection primitive (Proposition 4.1), event ownership and
  termination (Propositions 5.1, 5.2);
- the numerical and representation bounds `τ ≤ T*`, endpoints `≤ 2B`,
  intermediate bounds `U`, `M`, bit width `β`, coarse `O(N_in^7)`
  (Theorem 6.1, Section 6);
- exact first hit for the observation language (Theorem 7.1), with the
  one-atom projection (Lemma 8.1), the Boolean invariant (Lemma 8.2) and the
  finite exact-minimum bracket (Proposition 8.3); the original Presburger
  route via Cooper (Section 7.2) as a second, unexecuted effective proof;
- eventual `L·Q_obs`-periodicity of finite observations on a fresh run
  (Section 9);
- the examples `τ = 2·10^100 + 2`, first hit `2·10^100`, unseen-defect hit
  `2·10^100 + 14` (Section 10);
- Corollary 12.1 (no reduction through globally one-visit runs).

Part I does **not** claim (its Sections 1, 6, 8–12, the delivered README,
`INTEGRITY.md`, the packet's notes, and the review):

- novelty or priority ("The report makes no novelty assertion"; "A limited
  source search is evidence about what was inspected, not a priority proof");
- any polynomial bound for the observation compiler's Boolean expansion or
  for general Presburger elimination; T* does not bound observation first-hit
  times; `U`, `M` are not bounds for arbitrary externally supplied lanes;
- anything about post-revisit dynamics, physical halting of an ordinary ant,
  or whole-board translation periodicity; and, as Report 38's own historical
  scope, a completed literal two-visit universal atlas, input loader or
  accepting port, or a sharp one/two-visit threshold (these are now Part II's
  Theorem 40.1.1 and Corollary 40.1.2; dated notes in Part I say so);
- that colour reconstruction holds after the departure at `τ` (the strict
  first-arrival boundary);
- the succinct-tile input model;
- that `first_hit` authenticates a hand-forged or mismatched result, or any
  property of arbitrary mutated Python objects or injected signed
  coefficients;
- that tests prove the theorems: "Tests supplement the proofs"; finite
  prefixes cannot establish infinite nonoccurrence; the complexity review's
  10,000 random bound checks (seed 301003) are historical, not replayable
  and not a premise; replay checks are "strong finite evidence, not machine
  checked proofs";
- that hash verification, test replay and proof validity substitute for one
  another; a hash manifest is not a digital signature; the verifier is "not
  an OS sandbox";
- turmite universality itself (third-party, cited);
- that the Kracht (2002) Presburger exposition read by the source audit is
  usable as an algorithm specification (the audit records reversed bounds
  in its bounded-interval display; it is not cited by the article).

**Parts II–IV** claim conventional proofs, relative to the dependencies
named, of: Theorem 40.1.1 with Lemma 40.3.1 (finite history verification of
the 7 primitives), Proposition 40.4.1, Lemma 40.5.1, Theorem 40.6.1 (all
2^24 inputs), the exact program of Section 40.7, Proposition 40.8.1,
Lemma 40.9.1, Lemma 40.10.1, Theorem 40.10.2, Proposition 40.11.1,
Lemma 40.12.1, Theorem 40.12.2, the bounds of Section 40.13 (including the
deliberately loose `B_C = 15274393040715416`), Corollary 40.1.2, and the
endpoint Theorem 40.D.1 with its 42/101-operation ledgers and residual
degrees; Theorem 42.1.1, Proposition 42.2.1, Lemmas 42.3.1–42.3.2,
Theorem 42.3.3, Lemma 42.4.1, Lemmas 42.6.1, 42.7.1, Theorem 42.8.1, the
strict ledger, Propositions 42.9.1–42.9.2 and Corollary 42.10.1;
Theorem 44.1.1 with its witness partition, the reconstructed history,
Proposition 44.7.1 (leading part `2W^2304000`), the paid Cantor pairing and
the strict grammar; Theorem 47.1.1 with Lemma 47.3.1, the finite ownership
of Section 47.4, Lemmas 47.5.1, 47.6.1, Propositions 47.5.2, 47.6.2, 47.9.1;
Theorem 48.1.1 with Lemma 48.3.1, Theorem 48.3.2, Proposition 48.4.1,
Lemma 48.4.2 (Lemma 47.6.1 restated in `Z[Y]`), Proposition 48.5.1 and the
complete ledger.

Parts II–IV do **not** claim (the manuscripts' own non-claims, all kept in
the article):

- novelty or priority: qualitative turmite universality and the two-visit
  principle are Maldonado et al.'s; Report 42's power macro is "an explicit
  specialization and a new paid composition, not discovery of Diophantine
  exponentiation or a replacement proof"; Report 40 asserts "no novelty or
  priority theorem";
- an implemented arbitrary-program-to-U15 encoding (it is the published
  Neary–Woods dependency), an ordinary-input loader for the programme's input
  convention, or a universal polynomial in the programme's sense (above);
- universality from a finite blank background, a physical stopping event,
  or a return-to-a-fixed-site detector; the ant runs forever, also after the
  simulated halt;
- that the sharp boundary is more than "a sharp boundary for this decision
  model, not a statement that every two-visit run is universal, nor a
  threshold for every conceivable output interpretation";
- a materialized dense period rectangle (277,193,130,854,400,000 cells) or
  601,547,591-row instruction list; the finite review of 263,525 cells "is
  not represented as an exhaustive enumeration"; the circuit builder's
  randomized checks are ancillary; Boolean agreement alone gives no tiling
  or visit bound; `B_C` "intentionally overcounts" and is "not an optimized
  timing claim"; no efficient uniform theorem for succinct tiles;
- any combined or universal count from the endpoint: "neither 174+42 nor
  174+101 is asserted here as a complete universal operation count"; Report
  42 is "not a merged universal arithmetic record" ("Simply printing
  174+2306387 would not do this"); the 396 witnesses are new internal ones
  only; witness tuples are not single-fold or finite-fold; the strict
  constants are specified, not expanded; "F alone is not a universal halting
  polynomial"; the degree-12 recoder statement "does not survive
  substitution of the board radix without recalculation"; no minimal-degree,
  sparse-optimal or operation-optimal claim;
- for Report 44: "These conservative counts are not operation records"; not
  a "universal operation record, efficient decision procedure, physical ant
  cessation, witness uniqueness or a finite-fold theorem"; the history,
  base-three/Pell, recoder and literal-interface theorems are inherited, and
  "finite checks do not replace them"; **no empty-right universality** ("We
  do not assert that family is non-universal; the required argument is absent
  here"); recovered-edition receipts are historical, not authentication;
  stream identity is not file identity; no minimum degree;
- for Reports 47 and 48: "a unit-cost arithmetic-source reduction, not a
  numerical bit-complexity or execution-time claim"; Report 47 "does not
  correct an erroneous old count" and "the old dense prefix and its bound
  remain valid for their original grammar"; Report 48's identity is not a
  quotient-ring identity, assumes no `W^576000 = 1`, no division by `W` and
  no nonzero `W`; no optimality, lower bound, priority, operation record,
  stronger ant theorem or stronger universality; modular checks are
  supplementary; the synthetic `R = 2` ownership check "does not simulate
  the actual machine or assert any ant behavior"; the free-coefficient body
  count 95,568/95,578 is "a separate free-coefficient model";
- that hashes, receipts or replays prove theorems, or that optimized Python
  is a scientific mode (two Report 40 commands, `copy/translate_anchor.py`
  and `copy/program_audit/verify_program_index_bounds.py`, are unsupported
  under `-O`);
- any improvement of the programme's 84-operation universal bound.

## Relation to neighbouring reports and to the formal project

The report is in the collection's `hilbert-tenth-problem` category (chosen
for Part I because its comparison targets are the programme's
turmite-interface notes, and the programme reviewed it and derived a
Diophantine component lead from it); Parts II–IV build the turmite interface
those notes ask for.

- **The programme's research tree** (read-only for this report). The notes
  `Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md` (line 394: "choose
  the exact macro-pattern whose occurrence is equivalent to simulated
  halting"; lines 11–15: the periodic-background compiler, the input
  perturbation and a halting observable as further obligations) and
  `Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md` (line 128) are
  answered by Part I from the negative side (no such event on globally
  one-visit runs, Corollary 12.1) and by Parts II–III from the positive side:
  Report 40 supplies the background, the loader and the event
  geometrically, and Reports 42 and 44 pay them arithmetically, with the
  174-operation history inherited. The programme index
  (`Computability/HilbertTenthProblem/README.md`) still lists, for Report 38,
  "first-hit minimality and an ordinary-input universal loader" as unpaid;
  that remains true in the programme's sense, since Part III's certificate is
  a recognizer of the fixed U15 sentinel-pair language, not an emitted
  ordinary-input loader (Part III does not need first-hit minimality). The
  index's later paragraphs record the five-report review, the sharing
  packets and the count 14,620,711 / 14,620,721, and that the universal
  bound remains 84 operations (`20aafb9a5`). The programme's earlier ant
  toggle-tape components (105/158, 105/155) are much narrower.
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**,
  Part XX: Research Reports 35 and 36 (batch-83 manuscripts 07 and 08,
  prefix `22-literal-sandpiles-`, labels `cdc:lp:`, placement `216bd81e1`)
  do for abelian sandpiles what Parts II–III do for the ant: a literal
  periodic substrate, a finite loader for the same machine U15 (there in a
  34-state lazy CA convention that Report 40 does not import) and a
  certificate. No shared theorem.
- **[`fixed-universal-polynomials`](../fixed-universal-polynomials)**: the
  programme's universal-polynomial chain (Grill route, complete74/80/84
  candidates, Reports 23–25, 33, 34, 37 and batch 88's Reports 39, 41, 43,
  45, 46). Parts III–IV give a different, vastly larger fixed polynomial for
  the U15 language through the ant; it does not bear on the 84-operation
  record. No shared theorem.
- **[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)**:
  holds the U15 table file that Report 40's `ca/u15_table.json` copies
  (`data/16-universal-membrane-tm_table.json`).
- **`five-particle-binary-automata`, `signal-machine-collision-certificates`**:
  other discrete-dynamics substrates of the category; they cite related work
  of Gajardo and Maldonado on cellular automata and pebble automata, not
  turmites. No shared theorem. No other report of the collection treats
  turmites, Langton's ant or first revisits.
- **The formal project.** **Placement beside a Lean/Rocq development confers
  no formal status**; no statement of this report is formalized. The
  standard theorem Part I invokes in Section 7.2, decidability of Presburger
  arithmetic by Cooper's quantifier elimination, is formalized in
  `Logic/PresburgerArithmetic`: Lean
  `PresburgerArithmetic.Formula.presburgerArithmetic_decidable` and
  `PresburgerArithmetic.Formula.holds_iff_quantifierEliminate`
  (`Lean/PresburgerArithmetic/Decision.lean`), and an independent Rocq proof
  of the one-variable step, `cooper_finite_criterion` and
  `cooper_step_decidable` (`Coq/Cooper.v`); Part I's executable route avoids
  it. Report 42's power macro specializes Mathlib's `Pell.matiyasevic` and
  `Pell.eq_pow_of_pell`; the repository's Lean development uses the first
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Cor26.lean`),
  but the specialization, the recoder, the initializer and the complete
  polynomial are not formalized. The inherited 174-operation history is a
  research-tree note, not a formal theorem.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory that also holds the three figure files of
Report 40 under their shipped names (`data/02-literal-ant-figures-primitive-grids.tex`,
`-ports.tex`, `-rows.tex`; the article inputs them from `data/`). Standard
packages (Latin Modern, AMS, mathtools, microtype, booktabs, array,
longtable, enumitem, fancyhdr, float, graphicx, TikZ, multicol, needspace,
hyperref, xurl). The committed build has 132 pages: no errors, no undefined
references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes, and one underfull box (badness 1019, in the
completeness proof of Theorem 44.1.1), which the delivered Report 44 has as
well. **Do not run the delivered `build_pdf.py` programs here**: they rebuild
the delivered manuscripts against the delivered PDFs' bytes.

## Rerunning the programs

The delivered release verifiers of all six reports check POSIX file modes,
the delivered layout and unshipped checksum files; they refuse to run on
NTFS and on this tree. Never run anything inside this directory: the
programs import each other by delivered names, and several write their
outputs beside themselves (Report 40's `replay_all.py` writes
`atlas/fresh_replay.json` under its own root).

**Part I.** Two routes:

1. **Full release replay**: re-extract the archive of the arrival commit on
   a POSIX host, outside the repository, and follow its `README.md` there:
   ```sh
   git show 3051d1446:docs/incoming/Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip > r38.zip
   ```
2. **The mathematical programs directly**: copy the six pinned active
   programs to a scratch directory outside the repository under their
   delivered names, and run them there (`py` is the Python launcher on this
   machine; any Python ≥ 3.10, standard library only):

```sh
R=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits
W=/path/outside/the/repository/r38; mkdir -p $W
for f in one_visit observations test_boundary_regression test_observations independent_checks example; do
  cp $R/code/source-packet-$f.py $W/$f.py; done
norm() { tr -d '\r' | sed -E "s/^Ran ([0-9]+) tests in [0-9.]+s$/Ran \1 tests in X/"; }
(cd $W && py -B -m unittest -v test_boundary_regression test_observations > a.out 2> a.err
          py -B independent_checks.py > i.out 2> i.err
          py -B example.py > example.json)
cat $W/a.out $W/a.err | norm | cmp - <(norm < $R/data/source-packet-author-normal.log)
cat $W/i.out $W/i.err | norm | cmp - <(norm < $R/data/source-packet-independent-normal.log)
tr -d '\r' < $W/example.json | cmp - $R/data/source-packet-example-result.json
# repeat with `py -B -O` against the *-optimized.log files
```

Keep stdout and stderr in separate files and concatenate them stdout first:
that is the order of the frozen `.log` files (the release verifier does the
same); a single combined redirect interleaves them differently. The `.txt`
twins of the independent logs record a second run with stderr first. On
Windows the outputs have CRLF line endings, hence the `tr`. At the batch-83
write (Windows, Python 3.14.4) all three runs passed in both modes (author
tests about 23 s, independent checks about 17 s), and all six comparisons
were equal after the elapsed-time normalization. The historical programs in
`boundary-context` and the packet's own `verify_release.py` are inert by
design and need not be run; the latter writes its receipt to a directory
of the caller's choice, so never point it into this tree.

**Parts II–IV.** Extract each archive from the arrival commit (commands
under "Not shipped") into a scratch directory outside the repository.

1. **On a POSIX host**, follow each delivery README there. The trusted
   manifest hash each verifier asks for is the SHA-256 of the archive's
   `MANIFEST.json`, which this directory ships byte-identically:
   | Report | `--manifest-sha256` (SHA-256 of `data/0N-…-MANIFEST.json`) |
   |---|---|
   | 40 | `f44d98ff3184e3c2ceeaaa8c0da40688056902338ee39d3f534091d5be9df5bd` (Report 40's verifier pins it itself: `python3 -I -B verify_release.py --replay`) |
   | 42 | `28996d7e02d312a663d782836e8864da20be08414c66095b012600d5a68e2da1` |
   | 44 | `19774ed643abca49fe660173cede28add779c8fd89740f47fb03b2c10ea1afa1` |
   | 47 | `317ad533eadbc816f595cb8f5ec262c400ab5a694b7d70559bc50988d4131819` |
   | 48 | `e3a4c689499c92600026719f7333a99da4ccd5717d900d2d6ebaa5eb9a36b361` |

   For example `python3 -I -B verify_release.py --manifest-sha256 <hash>
   --output /new/external/dir` (Reports 42, 44, 47, 48). These hashes come
   from this repository; they authenticate the extraction against the
   committed copy, not the archive's origin.
2. **On Windows** (how placement ran them): run the scientific programs of
   the extraction directly, not the verifiers. Report 40:
   `evidence/literal-interface/replay_all.py` (28 commands, 39 outputs
   compared byte for byte, about 150 s; it needs the 24 heavy files present)
   and `evidence/endpoint/replay_all.py` (4 commands, 10 outputs, 2 s).
   Report 44: `certificate/merged_source.py --output /fresh/two.json` and
   `--arity 1 --output /fresh/one.json` (each regenerates a complete stream;
   compare the recorded stream SHA-256 with `c1690116…` and `85a16197…`), with SymPy 1.14.0 for the history checks
   (`uv run --no-project --with sympy==1.14.0 python …`). Report 47:
   `science/geometry/build_profiles.py --out <new dir>` and the prefix and
   join programs (`science/full_prefix.py`, `science/join_strict.py`) as its
   README describes. Report
   48: `science/fusion_source.py --out <file>` and `science/checks.py --out
   <file>` (outputs byte-identical to `fused-receipt.json` and
   `checks-receipt.json`). Two Windows-only artefacts: Python writes text with
   CRLF (several drivers compare bytes, so force LF or compare after removing
   `\r`), and two programs key paths by `str(relative_path)`, so on Windows
   they write backslashes: Report 47's joined receipt (`pins` keys of
   `joined-strict-receipt.json`; equal after normalizing separators) and
   Report 48's `audit_replay/replay_independent_audit.py` (its baseline
   inventory check fails on Windows only; with `/` separators the relocated
   audit passes, about 2 minutes).

At placement (Windows, Python 3.14.4, on copies) every suite passed in this
way: Report 40's driver 28 commands / 39 outputs byte-exact and endpoint
4/10, both independent audits byte-identical; Report 42's replay (270 s)
including byte-identical dilation evidence; Report 44's complete streams
reproduced `c1690116…` and `85a16197…`, history byte-identical in normal and
`-O`; Report 47's prefix `6a01d7c1…`, joins `b235ba1d…` / `73786631…`, 11
profile artifacts byte-identical; Report 48's fused and checks receipts
byte-identical and the relocated independent audit PASS. All checksum
manifests verified.

## Discrepancies and disclosures

- The release-review records approve the delivered PDFs and manuscripts,
  not this `article.tex` and 132-page `article.pdf`:
  `data/verification-release-review.json` (Report 38: 21-page PDF, TeX
  `d81bc308…`) and `data/0N-…-verification-release-review.json`,
  `…-manuscript-review.json`, `…-visual-review.json`, `…-pdf-*.json` of
  Reports 40–48.
- `code/seal_release.py` (Report 38) and `code/02-literal-ant-seal_release.py`
  (Report 40) rewrite `MANIFEST.json`, `SHA256SUMS` and the `MANIFEST_SHA256`
  line of `verify_release.py` in place; `data/MANIFEST.json` and
  `data/02-literal-ant-MANIFEST.json` record `verify_release.py` with that
  line zeroed (the documented normalized self-pin). Never run them here.
- The delivered READMEs' replay, PDF and ZIP commands assume the delivered
  layout; they are summarized here, not reproduced.
- Report 44's edition note and its `certificate/README.md` (shipped as
  `04-ant-cert-certificate-README.md`) speak of a *corrected* horizontal
  geometric-repunit multiplier `h_x`. The correction concerns the lost draft
  of Report 44; Report 42's proof (`03-ant-init-science-PROOF.md`) already
  has the repunit.
- Report 44's reconstructed history replaces residual 46 by a unit-triangular
  combination with the same zero set (Section 44.3, and its
  `history174.json`); the programme note states the residual literally.
- Report 48's delivery README (not shipped) says that the frozen author
  README "calls the result a candidate awaiting audit"; the shipped
  `06-ant-fusion-science-README.md` is that author README ("This separate
  research candidate …"), kept byte for byte as historical text, and the
  article's Appendix 48.B says the same. The later independent audit is PASS.
- The Neary–Woods paper's §3.5 prose names the wrong halting symbol (`c`);
  its Table 16 leaves `(u10, b)` undefined; every report follows the table.
  The paper's PDF also carries wrong printed page numbers (Reports 40 and 44
  say so); the journal pagination 123–144 is authoritative.
- The staged binary `data/02-literal-ant-literal-interface-ca-radius_one_32_table.bin`
  contains CR bytes; it is binary for `.gitattributes`, and its blob is
  byte-identical to the delivery.
- Delivered author wording kept: "Mathematical research report" in every
  source introduction; the article's title page says "Mathematical research
  reports"; the PDF metadata author is empty.

## Third-party material and licence

The archives ship no licence file; the repository's MIT-0 default applies to
the delivered own text, code and data, **with one exception**: Report 40's
seven primitive cell maps,
`data/02-literal-ant-literal-interface-common-primitive_maps.json` and
`data/02-literal-ant-literal-interface-common-primitive_catalog.json`, are
numerical data that the report's authors extracted from the MetaPost figure
sources (`img/cable_a.mps`, `cable_b.mps`, `cable_c.mps`, `box.mps`,
`cruceA.mps`, `cruceB.mps`, `union.mps`) of Maldonado, Gajardo, Hellouin de
Menibus and Moreira, *Nontrivial Turmites are Turing-universal*,
arXiv:1702.05547; their source hashes are recorded in
`02-literal-ant-literal-interface-SOURCE_PROVENANCE.md` and in the catalogue.
The licence of those arXiv sources is not stated in the archive. The two
files are shipped with this credit and provenance and are **not covered by
the repository's MIT-0 licence**; reuse them under whatever terms the
original authors' sources allow. (The same practice as for the third-party
Waterfall data of batch 78.) The article's Figure 2 and Appendix 40.A are
drawn from these maps by the report's own generator.

Not shipped and not redistributed: Mathlib's `PellMatiyasevic.lean` and its
Apache-2.0 licence (cited by commit and hash above); the Neary–Woods,
Maldonado et al. and Cooper papers (cited only).
