# Groups as Diophantine Substrates

**Arithmetic van Kampen certificates, three commutative phases, pair order, affine matrix inputs, a universal matrix semigroup and chronological matrix certificates: low-degree certificates through the integral Heisenberg group and free matrix groups**

This is a research report dated 2–4 October 2026, built from six
manuscripts of ProveIt's incoming reports: manuscripts 03 and 05 of batch 76
(Parts I and II), manuscripts 09 and 13 of batch 78 (Parts III and IV),
manuscript 22 of batch 82 (Part V) and manuscript 07 of batch 91 (Part VI).
All six are AI-assisted research manuscripts: the first four are "prepared
for Vladimir Reshetnikov"; the fifth and sixth, "Research Reports" 32 and 55
of the pipeline that delivered batches 82 and 91, name no author ("Research
construction and reproducibility report"; "Report55"). They are called
*source 03*, *source 05*, *source 06*, *source 07*, *source 08* and *source
09* after the file prefixes of their shipped programs and data. The batch-76
prefixes are those manuscripts' numbers; the prefixes `06-`, `07-`, `08-`
and `09-` continue this report's own sequence and are **not** batch-78,
batch-82 or batch-91 manuscript numbers.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 03 (base) | batch 76, manuscript 03 | `arithmetic_van_kampen.zip` (`6914ccca6`); *Arithmetic van Kampen Certificates: Quartic equations, exact filling area, and optimal proof-DAG compression*, main file `arithmetic_van_kampen.tex`, 29-page PDF | `c58206ca1` | `2a04b60f2` | Part I (Sections 2–17) and Appendices A–C |
| 05 | batch 76, manuscript 05 | `three_commutative_phases_research.zip` (`6914ccca6`); *Three Commutative Phases Are Diophantine-Universal: A fibre-preserving Heisenberg compiler and a proposed resolution of the three-subgroup problem*, main file `article.tex`, 22-page PDF | `433df1be3` | `2a04b60f2` | Part II (Sections 18–31) and Appendices D–F |
| 06 | batch 78, manuscript 09 | `Order_Is_Not_a_Moment.zip` (`808b53ed8`); *Order Is Not a Moment: Exact Pair-Count Geometry and Diophantine Certificates for Heisenberg Computation*, main file `article.tex`, 26-page PDF | `4cccfa068` | `41e7f1189` | Part III (Sections 32–42) and Appendices H–I |
| 07 | batch 78, manuscript 13 | `ProveIt_Affine_Matrix_Diophantine_Research.zip` (`48ee077c7`); *Affine Matrix Inputs and Diophantine Universality: Sharp rigidity, exact period bounds, and computation with existential witnesses*, main file `article.tex`, 25-page PDF | `4cccfa068` | `41e7f1189` | Part IV (Sections 43–60) |
| 08 | batch 82, manuscript 22 ("Research Report 32") | `Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip` (`db37d18c8`); *A fixed universal matrix semigroup and bounded length Diophantine certificates*, main file `report32.tex`, 26-page PDF | none named | `2f58ab4e9` | Part V (Sections 61–76) and Appendices J–K |
| 09 | batch 91, manuscript 07 ("Research Report 55") | `Chronological_Diophantine_Matrix_Certificates_Package.zip` (`0d7f51c44`, 4 October 2026); *Chronological Diophantine Matrix Certificates: Fixed arity with an ordinary positive input*, main file `article/Report55.tex`, 21-page PDF | `750aeb4f7`, `d31e29030` | `22a8ca89e` | Part VI (Sections 77–90) and Appendices L–M |

Full pins: `c58206ca101d4744a015a0f0104646109357d943` (03),
`433df1be37188224dd00d0561bfb157949cd6320` (05),
`4cccfa06866b6b81b2467e1cf7514ea85ed0216d` (06 and 07),
`750aeb4f7834332deb2bec5f32fb470ff8254431` (09: the research programme's
five-register countdown receipt and five matrix notes) and
`d31e29030214c35083b0c2e052c8a3a5d0409eb0` (09: the counted-suffix proof).
All are ancestors of their placement commits. Source 08 names no ProveIt
commit and cites no repository file; it identifies its numerical data by the
SHA-256 of its coefficient file `core/data/semigroup.json` (shipped as
`data/08-matrix-semigroup-core-data-semigroup.json`, byte for byte). Every
repository file source 09 pins or copies (eleven files under
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`)
has the same blob at its pins and at this write, and its three SHA-256 pins
(countdown receipt `f365eb9b…`, counted-suffix receipt `3c803a9a…`,
context-transferred array `73f8cae2…`) match.
Appendix G of the article is the provenance.

Every result, proof, example, remark, limitation, research question and
audit of the six manuscripts is printed. No two of them share a theorem,
except that the first half of source 08's Lemma 65.1 (the Sanov shears are
free) is the injectivity half of Part I's Theorem 4.1 (Sanov), classical,
printed in Part V as a second proof. None cites another. Source 09's POWER
module (Section 80) is Lemma `ptr:ai:lem:exp` of the neighbouring report
`periodic-turmite-first-revisits`, printed as a marked second route. Source 03 treats
a finitely presented group as a proof-producing substrate and uses the
Heisenberg group as an *area
detector*; source 05 treats an ordered product of three abelian subgroups
of a Heisenberg power as the substrate and uses the Heisenberg group as the
*ambient group*; source 06 treats a three-generator submonoid of a
Heisenberg power and uses the group to *record order* (pair counts of
words); source 07 asks how an ordinary integer input can be loaded into a
fixed matrix subgroup, and uses the cyclic subgroup `⟨h(1,1,0)⟩` as its
test; source 08 builds one fixed positive *semigroup* of 229 literal
`SL_4(Z)` matrices whose membership problem simulates the Neary–Woods
universal machine `U_{15,2}` on finite tapes, with a free-group *marker* in
the lower block, and does not use the Heisenberg group; source 09 gives one
explicit polynomial of *fixed arity* and exact degree 12 (41,309 positive
witnesses, 184,016 gates) whose positive zeros recognize, for histories of
every length, the inputs accepted by the research programme's five-register
matrix countdown with two fixed contexts — under inherited interfaces,
membership of a target `T(x)` in a fixed semigroup of 195 singular integer
`7 × 7` matrices that descends from source 08's. The shared setup —
the integral Heisenberg group, its multiplication, inverse and power laws —
is printed once, in Section 1.2, with three tables of the letters the Parts
use differently (Tables 1–3); Part VI's letter table is Table 5, at the
start of Part VI, so that no earlier table number moved.

**Status: AI-assisted, unrefereed, not formalized.** Part II's main theorem
is a **proposed resolution, unrefereed**, of a published open problem; its
priority is not certified. Sources 06 and 07 state that their priority is
not established either; source 08 "makes no novelty or optimality claim".
Part V's many-one r.e.-completeness is **conditional** on the cited
Neary–Woods simulation chain (proved there only from finite `U_{15,2}`
tapes onward). Part VI's numerical theorem is relative to two pinned
mathlib Pell theorems, and its matrix reading is **conditional** on
research-programme interface theorems that it summarizes and does not
re-prove; its polynomial is for one fixture, not a universal polynomial.
Nothing in the report is formalized in Lean or Rocq.

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 186 pages (unnumbered title page, then pages 1–185)
README.md                                            this guide
03-van-kampen-SOURCES.md                             source 03's dependency, provenance and novelty notes, as delivered
07-affine-inputs-SOURCE_AUDIT.md                     source 07's source and claim audit, as delivered
08-matrix-semigroup-SANITIZED_PROVENANCE.md          source 08's record of its documentation adaptations and omitted caches
08-matrix-semigroup-core-PROOF.md                    core packet: proof of the fixed-semigroup reduction (rules, tiles, marker)
08-matrix-semigroup-core-README.md                   core packet README (delivery names)
08-matrix-semigroup-core-audit-REVIEW.md             core packet: independent mathematical review
08-matrix-semigroup-core-loader-audit-U15_DEPENDENCY_AUDIT.md  the U15 finite-input and r.e.-completeness dependency audit (cites Reports 16 and 23)
08-matrix-semigroup-fiber-PROOF.md                   fiber packet: proof of the exact fibre generating function
08-matrix-semigroup-fiber-README.md                  fiber packet README (delivery names)
08-matrix-semigroup-fiber-audit-REVIEW.md            fiber packet: independent review
08-matrix-semigroup-paired-PROOF.md                  paired packet: proof of the bounded-length SOS family and its counts
08-matrix-semigroup-paired-README.md                 paired packet README (delivery names)
08-matrix-semigroup-paired-audit-REVIEW.md           paired packet: independent mathematical review
09-chrono-matrix-audit_replay-README.md              source 09's portable replay adapter: usage and guards (delivery paths)
09-chrono-matrix-audit_replay-REPLAY_QA.md           the adapter's QA summary (28 rejected cases, moved/ZIP/read-only replays)
09-chrono-matrix-deps-NOTICE.md                      notice for the bundled mathlib Pell source and the four inherited matrix notes (none shipped here)
09-chrono-matrix-independent_audit-AUDIT.md          the independent exact-source and interface audit, PASS relative to the inherited theorems
09-chrono-matrix-manuscript_review-MANUSCRIPT_AUDIT.md  the pin-bound review of the 21-page manuscript, PASS
09-chrono-matrix-science-ARCHITECTURE.md             the scientific proof of the packing (selectors, slices, chronology, carries)
09-chrono-matrix-science-SOURCE_NOTES.md             the source's accounting of the literal DAG (also Report 58's POWER_SOURCE_NOTES.md)
09-chrono-matrix-science-review-PACKING_REVIEW.md    the independent review of the packing construction (sharper bound 2^103)
code/03-van-kampen-van_kampen.py                     source 03's exact matrix routines, Sanov decoder and symbolic compilers (SymPy; patched by db3b377f0, see below)
code/03-van-kampen-verify.py                         source 03's deterministic exact-arithmetic tests (imports van_kampen)
code/05-three-phases-build.sh                        source 05's three-pass pdflatex script (delivered layout; see below)
code/05-three-phases-heisenberg_compiler.py          source 05's standard-library exact-integer three-phase compiler (patched by db3b377f0, see below)
code/05-three-phases-verify.py                       source 05's 190,826-assertion verification (imports heisenberg_compiler)
code/06-pair-order-Makefile                          source 06's Makefile (delivered layout; see below)
code/06-pair-order-pair_geometry.py                  source 06's gap constructions, corner decision, polynomial gadgets and quartic export (standard library)
code/06-pair-order-verify.py                         source 06's finite checks; recomputes and compares with the bundled receipt (imports pair_geometry)
code/07-affine-inputs-verify.py                      source 07's exact-arithmetic reference implementation and 91,142-case verification (standard library)
code/08-matrix-semigroup-archive_release.py          source 08's release zipper/extractor (maintainer tool; needs the unshipped seals)
code/08-matrix-semigroup-build_release_inventory.py  source 08's sealing tool (maintainer only; rewrites the seals and the verifier's self-pin)
code/08-matrix-semigroup-build_report.sh             source 08's pdflatex script for report32.tex (not shipped; this report is the article)
code/08-matrix-semigroup-core-audit-independent_check.py  JSON-only core audit (rules, tiles, 229 matrices, marker sample, witness)
code/08-matrix-semigroup-core-compiler.py            the core compiler: builds semigroup.json, ledger.json, matrices.txt; target encoder
code/08-matrix-semigroup-core-tests-check_all.py     the core authored test suite (writes the accepting witness)
code/08-matrix-semigroup-fiber-audit-independent_check.py  JSON-only fibre audit (literal-tile graph coefficients)
code/08-matrix-semigroup-fiber-check_fibers.py       the fibre checker (stutter witnesses, matrix/SOS samples; writes CHECKS.json)
code/08-matrix-semigroup-paired-audit-independent_interface_check.py  independent paired interface, residual and invalid-input audit
code/08-matrix-semigroup-paired-audit-source_literal_check.py  JSON-only paired literal-matrix audit
code/08-matrix-semigroup-paired-paired_compiler.py   the bounded-length SOS compiler (ledger, export, certificate, verify)
code/08-matrix-semigroup-paired-tests-check_all.py   the paired authored suite (rewrites the 94-tile certificate and ledger)
code/08-matrix-semigroup-rebuild_release.sh          shortcut for verify_release.py --replay
code/08-matrix-semigroup-tamper_regression.py        18-case tamper regression of the release gate (works in temporary copies)
code/08-matrix-semigroup-verification-audit_literal_polynomials.py  release-level JSON-only reconstruction of all six r = 0, 1, 2 exports
code/08-matrix-semigroup-verify_release.py           the release verifier: identity gate, then --verify-only or --replay
code/09-chrono-matrix-audit_replay-replay_audit.py   source 09's replay adapter: runs the two independent checkers on fresh copies (needs the full frozen trees)
code/09-chrono-matrix-audit_replay-test_replay.py    the adapter's fail-closed QA (works in a new external workspace)
code/09-chrono-matrix-independent_audit-check_interfaces.py  independent check of all 195 matrices, 9,555 entries and the finite probes (writes its receipt beside itself)
code/09-chrono-matrix-independent_audit-check_source.py      independent symbolic audit of every residual of the DAG (writes its receipt beside itself)
code/09-chrono-matrix-manuscript_review-check_manuscript_data.py  the manuscript review's cross-check (hard-coded /workspace paths; not portable)
code/09-chrono-matrix-release.py                     release tool: verify / build-pdf / archive (needs the complete delivered inventory with POSIX modes)
code/09-chrono-matrix-science-build_certificate.py   the builder: writes evidence/polynomial-dag.json, build-receipt.json, coefficients.json (also Report 58's prior-build_certificate.py.txt)
code/09-chrono-matrix-science-check_semantics.py     the author's finite semantic probes (writes evidence/semantic-checks.json)
code/09-chrono-matrix-science-freeze_manifest.py     author tool: rewrites evidence/frozen-manifest.json
code/09-chrono-matrix-verification-check_layout.py   release QA: PDF bounding-box checks
code/09-chrono-matrix-verification-check_release_tools.py  release QA: guard, relocation, ZIP and PDF tests of release.py
data/03-van-kampen-commutator_budget_1.json          the one-budget compiler for [a,b]: 11 variables, 13 quadratic residuals
data/03-van-kampen-grid_1_1.json                     the shared dyadic grid compiler for [a^2,b^2]: 12 variables, 16 residuals
data/03-van-kampen-grid_1_1_witness.json             a satisfying assignment of the grid example (all values)
data/03-van-kampen-receipt.json                      source 03's recorded run: all checks passed (Python 3.13.5, SymPy 1.14.0)
data/03-van-kampen-render_check.json                 source 03's record of its own 29-page PDF build
data/03-van-kampen-export_check.json                 source 03's record of 4 + 4 sparse-polynomial evaluations
data/03-van-kampen-requirements.txt                  source 03's pin, sympy==1.14.0
data/05-three-phases-circuit.json                    compiler data and generator lists for the circuit example (Section 25.2)
data/05-three-phases-circuit_input.json              its quadratic specification
data/05-three-phases-multiplication.json             compiler data for xy − z = t: all fourteen basis matrices (Section 25.1)
data/05-three-phases-multiplication_input.json       its quadratic specification
data/05-three-phases-profinite_obstruction.json      compiler data for F(x) = 6x² − 5x in H × Z (Section 28)
data/05-three-phases-profinite_obstruction_input.json  its quadratic specification
data/05-three-phases-verification_receipt.json       source 05's recorded run: PASS, 190,826 assertions in 30 families
data/06-pair-order-canonical_c2_quartic.json         the canonical c = 2 quartic: 24 residuals and the expanded polynomial (297 terms, degree 4)
data/06-pair-order-verification_receipt.json         source 06's recorded test counts and the SHA-256 of pair_geometry.py
data/06-pair-order-worked_example.json               captured output of `pair_geometry.py decide 3 2 2 1 4` (the unique 24-witness tuple)
data/07-affine-inputs-verification.json              source 07's recorded run: PASS, 91,142 cases, seed 20261002
data/08-matrix-semigroup-core-PROVENANCE.json        core packet provenance (construction, authored code, data dependencies)
data/08-matrix-semigroup-core-audit-independent-results.json  receipt of the JSON-only core audit
data/08-matrix-semigroup-core-data-ledger.json       the core build ledger (counts and census; also delivered as core/evidence/build-ledger.json)
data/08-matrix-semigroup-core-data-matrices.txt      all 229 matrices as plain text
data/08-matrix-semigroup-core-data-semigroup.json    THE literal data: 229 SL_4(Z) matrices, alphabet, tiles (117,288 bytes; also delivered as paired/ and fiber/ copies)
data/08-matrix-semigroup-core-evidence-accepting-witness.json  the 14-step derivation, 94 tiles, 189 factors for [110A0] (also delivered as paired/ and fiber/ copies)
data/08-matrix-semigroup-core-evidence-check-normal.log      core suite receipt, ordinary run (byte copy delivered also as core/evidence/tests.json)
data/08-matrix-semigroup-core-evidence-check-optimized.log   core suite receipt, python -O (byte copy delivered also as tests-optimized.json)
data/08-matrix-semigroup-fiber-CHECKS.json           fibre checker receipt (also delivered as fiber/normal-run.json and optimized-run.json)
data/08-matrix-semigroup-fiber-MANIFEST.json         fiber packet manifest (inputs and their SHA-256)
data/08-matrix-semigroup-fiber-audit-normal.json     receipt of the fibre audit (also delivered as fiber/audit/optimized.json)
data/08-matrix-semigroup-paired-PROVENANCE.json      paired packet provenance and execution boundary
data/08-matrix-semigroup-paired-audit-REVIEW_BINDING.json  identities of the files the paired review read
data/08-matrix-semigroup-paired-audit-authored_tests_optimized.json  paired suite receipt, python -O (also delivered as paired/evidence/tests-optimized.json)
data/08-matrix-semigroup-paired-audit-cli_accepting_94_check.json  CLI check of the 94-tile certificate (also delivered as paired/evidence/accepting-cli-check.json)
data/08-matrix-semigroup-paired-audit-cli_r0_natural_check.json   CLI check of the r = 0 natural certificate
data/08-matrix-semigroup-paired-audit-independent_interface_check.json  receipt of the paired interface audit
data/08-matrix-semigroup-paired-audit-source_literal_check.json  receipt of the paired literal audit
data/08-matrix-semigroup-paired-evidence-portable-smoke.json     stdout digests of portable CLI smoke commands
data/08-matrix-semigroup-paired-evidence-tests.json  paired suite receipt, ordinary run
data/08-matrix-semigroup-paired-examples-accepting-94-certificate.json  the complete r = 94 certificate (12,220 natural auxiliaries)
data/08-matrix-semigroup-paired-examples-accepting-94-ledger.json  its arithmetic ledger
data/08-matrix-semigroup-paired-examples-r0-natural-sos.json  literal SOS polynomial, r = 0, natural targets
data/08-matrix-semigroup-paired-examples-r0-signed-sos.json   literal SOS polynomial, r = 0, signed targets
data/08-matrix-semigroup-paired-examples-r1-natural-sos.json  literal SOS polynomial, r = 1, natural targets
data/08-matrix-semigroup-paired-examples-r1-signed-sos.json   literal SOS polynomial, r = 1, signed targets
data/08-matrix-semigroup-paired-examples-target-collision.json  the length-two collision (20,109)/(110,20)
data/08-matrix-semigroup-verification-expected-receipts.json  the strictly typed replay expectations of verify_release.py
data/08-matrix-semigroup-verification-literal-polynomials.json  receipt of the release-level polynomial reconstruction
data/08-matrix-semigroup-verification-source-lineage.json  identities of the two source packets the release was built from
data/08-matrix-semigroup-verification-source-manifests-core.json    core packet integrity manifest
data/08-matrix-semigroup-verification-source-manifests-paired.json  paired packet integrity manifest
data/09-chrono-matrix-MANIFEST.json                  source 09's release manifest: paths, sizes, SHA-256 and POSIX modes of every other delivered file and directory
data/09-chrono-matrix-audit_replay-qa-receipt.json   the adapter's QA receipt
data/09-chrono-matrix-audit_replay-release-files.json  hashes of the adapter's files
data/09-chrono-matrix-deps-SOURCE_PINS.json          pins and roles of the four bundled matrix notes (commit 750aeb4f7)
data/09-chrono-matrix-independent_audit-audit-manifest.json  the independent audit's frozen manifest
data/09-chrono-matrix-independent_audit-connector-provenance.json  the audit's record of its read-only GitHub retrievals
data/09-chrono-matrix-independent_audit-interface-audit-receipt.json  receipt of check_interfaces.py (195 matrices, 9,555 entries, probes)
data/09-chrono-matrix-independent_audit-pell-dependency.json  the mathlib Pell pin (also Report 58's pell-dependency.json)
data/09-chrono-matrix-independent_audit-source-audit-receipt.json  receipt of check_source.py (184,016 gates, 41,309 witnesses, degree 12)
data/09-chrono-matrix-manuscript_review-data-check-normal.log  the manuscript cross-check's run (normal and optimized runs identical)
data/09-chrono-matrix-manuscript_review-data-receipt.json   its receipt
data/09-chrono-matrix-manuscript_review-review-manifest.json  the manuscript review's file pins
data/09-chrono-matrix-manuscript_review-visual-receipt.json  the review's page-by-page visual record
data/09-chrono-matrix-science-evidence-build-receipt.json   the builder's ledger receipt (DAG SHA-256 95e2563f…)
data/09-chrono-matrix-science-evidence-coefficients.json    the 97 fixed column maps, offsets and the radix threshold
data/09-chrono-matrix-science-evidence-frozen-manifest.json  the frozen science packet manifest (18 files)
data/09-chrono-matrix-science-evidence-semantic-checks.json  receipt of check_semantics.py
data/09-chrono-matrix-science-sources-provenance.json  blob pins of the seven research-programme files the packet copies
data/09-chrono-matrix-verification-final-latex.log   pdfLaTeX log of the delivered PDF build
data/09-chrono-matrix-verification-isolated-audit-replay.json  release-time record of the isolated replay
data/09-chrono-matrix-verification-pdf-layout-checks.json  receipt of check_layout.py
data/09-chrono-matrix-verification-pdf-rebuild-a.json  record of a sealed PDF rebuild (the identical rebuild-b is not shipped)
data/09-chrono-matrix-verification-provenance-preservation.json  record that the frozen packets were preserved byte for byte
data/09-chrono-matrix-verification-release-tool-tests.json  receipt of check_release_tools.py
data/09-chrono-matrix-verification-visual-review.json  the release's visual review record
```

The r = 2 exports `paired/examples/r2-signed-sos.json` and
`r2-natural-sos.json` are not shipped (see "Reconstructing the excluded
data"), and neither is source 09's literal polynomial DAG
`science/evidence/polynomial-dag.json` (same section).

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery, **except two batch-76 programs**:
`code/03-van-kampen-van_kampen.py` and
`code/05-three-phases-heisenberg_compiler.py` were patched in place by
commit `db3b377f0` ("Apply reviewed guard fixes to imported group
compilers", input-guard repairs reviewed in the Hilbert-tenth-problem
research programme), after placement and before Parts I and II were
written. (This README, as written in batch 76, said that all shipped files
were byte-identical; that was not true of these two.) The delivered bytes
survive in the arrival archives. Delivered name → shipped name:

- Source 03: `code/van_kampen.py`, `code/verify.py` →
  `code/03-van-kampen-*.py`; `examples/commutator_budget_1.json`,
  `examples/grid_1_1.json`, `examples/grid_1_1_witness.json`,
  `verification/receipt.json`, `verification/render_check.json`,
  `verification/export_check.json`, `requirements.txt` →
  `data/03-van-kampen-*`; `SOURCES.md` → `03-van-kampen-SOURCES.md`;
  `arithmetic_van_kampen.tex` → the base of `article.tex` (Part I).
- Source 05: `build.sh`, `code/heisenberg_compiler.py`, `code/verify.py` →
  `code/05-three-phases-*`; `examples/*.json` and
  `verification_receipt.json` → `data/05-three-phases-*`.
- Source 06 (inner directory `order_is_not_a_moment/`): `Makefile`,
  `code/pair_geometry.py`, `code/verify.py` → `code/06-pair-order-*`;
  `data/canonical_c2_quartic.json`, `data/verification_receipt.json`,
  `data/worked_example.json` → `data/06-pair-order-*`; `article.tex` →
  Part III and Appendices H–I of `article.tex`.
- Source 07 (inner directory `Affine_Matrix_Diophantine_Research/`):
  `verify.py` → `code/07-affine-inputs-verify.py`; `verification.json` →
  `data/07-affine-inputs-verification.json`; `SOURCE_AUDIT.md` →
  `07-affine-inputs-SOURCE_AUDIT.md`; `article.tex` → Part IV of
  `article.tex`.
- Source 08 (inner directory
  `universal-matrix-report32-release-20261003/`): every path is flattened
  by replacing `/` with `-` after the prefix `08-matrix-semigroup-`;
  programs (`*.py`, `*.sh`) go to `code/`, JSON, `.txt` and `.log` files to
  `data/`, and the Markdown proofs, reviews, packet READMEs, dependency audit
  and `SANITIZED_PROVENANCE.md` to the report root. For example
  `core/compiler.py` → `code/08-matrix-semigroup-core-compiler.py`,
  `core/loader-audit/U15_DEPENDENCY_AUDIT.md` →
  `08-matrix-semigroup-core-loader-audit-U15_DEPENDENCY_AUDIT.md`,
  `paired/examples/r1-signed-sos.json` →
  `data/08-matrix-semigroup-paired-examples-r1-signed-sos.json`.
  `report32.tex` → Part V and Appendices J–K of `article.tex`.
- Source 09 (package root `Chronological_Diophantine_Matrix_Certificates_Package/`):
  every path is flattened by replacing `/` with `-` after the prefix
  `09-chrono-matrix-`, with `dependencies/` shortened to `deps-`; programs
  (`*.py`) go to `code/`, JSON and `.log` files to `data/`, and the Markdown
  notes, reviews and audits to the report root. For example
  `science/build_certificate.py` →
  `code/09-chrono-matrix-science-build_certificate.py`,
  `independent_audit/AUDIT.md` → `09-chrono-matrix-independent_audit-AUDIT.md`,
  `dependencies/SOURCE_PINS.json` → `data/09-chrono-matrix-deps-SOURCE_PINS.json`,
  `MANIFEST.json` → `data/09-chrono-matrix-MANIFEST.json`.
  `article/Report55.tex` → Part VI and Appendices L–M of `article.tex`.

Not shipped: the manuscripts of sources 05, 06, 07, 08 and 09 (printed as Parts
II–VI), all six PDFs, all six delivered READMEs (this text and
`article.tex` replace them; source 08's is `RELEASE_README.md`), source
03's checksum ledger `SHA256SUMS.txt` (13 of 13 files verified at
placement), source 06's `SHA256SUMS` (9 of 9 verified at placement) and
source 08's seals `MANIFEST.json`, `SHA256SUMS` and `fiber/SHA256SUMS`
(its `verify_release.py --verify-only` passed on the archive at placement);
sources 05 and 07 shipped none. Of source 08's 80 files, 59 are shipped; the
other 21 are those six (manuscript, PDF, release README, three seals), the
two r = 2 exports (next section), twelve byte copies inside the release
(shipped once: the `paired/data/` and `fiber/data/` copies of
`semigroup.json` and `accepting-witness.json`, `core/evidence/build-ledger.json`
= `core/data/ledger.json`, `core/evidence/tests.json` and
`tests-optimized.json` = `check-normal.log` and `check-optimized.log`,
`fiber/normal-run.json` and `fiber/optimized-run.json` = `fiber/CHECKS.json`,
`fiber/audit/optimized.json` = `fiber/audit/normal.json`,
`paired/evidence/tests-optimized.json` =
`paired/audit/authored_tests_optimized.json`,
`paired/evidence/accepting-cli-check.json` =
`paired/audit/cli_accepting_94_check.json`), and `core/data/u15_table.json`,
which is byte-identical to
[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)'s
`data/16-universal-membrane-tm_table.json` (the same 30-cell `U_{15,2}`
table).

Of source 09's 68 files, 44 are shipped (8 at the root, 11 in `code/`, 25
in `data/`). The other 24: the manuscript `article/Report55.tex` (Part VI),
its PDF and the delivery `README.md`; the polynomial DAG
`science/evidence/polynomial-dag.json` (11,069,996 bytes, regenerable; next
section); the third-party mathlib file `dependencies/pell-source.lean`
(`Mathlib/NumberTheory/PellMatiyasevic.lean` at mathlib4
`ac77769fabe23cb237559e7f56578dbead91499f`, SHA-256 `993760c7…`) and its
`LICENSE.mathlib-Apache-2.0.txt` (Apache-2.0), cited, not redistributed;
eleven byte copies of research-programme files at their current paths
under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
— `science/sources/` `matrix193_countdown_rows.{md,json}`,
`matrix193_synchronized_rows.md`, `matrix193_context_absorption.{md,json}`,
`matrix195_counted_suffix.{md,json}`, and `dependencies/`
`group_directed_semigroup193.md`, `matrix193_gamma1_recode.md`,
`matrix193_kernel_row_projection.md`, `u15_unary_block_interface.md`; the
checksum list `manuscript_review/data-receipt-before-optimized.sha256`
(verified at placement); and six byte copies of shipped files
(`independent_audit/interface-audit.log` and `interface-replay.log` =
`interface-audit-receipt.json`, `source-audit.log` and `source-replay.log` =
`source-audit-receipt.json`, `manuscript_review/data-check-optimized.log` =
`data-check-normal.log`, `verification/pdf-rebuild-b.json` =
`pdf-rebuild-a.json`). No trusted manifest digest accompanied the delivery
(its README asks for one "from the trusted accompanying delivery"); the
arrival commit's archive blob is the identity. They survive in the archives
of the arrival commits:

```sh
git show 6914ccca6:docs/incoming/arithmetic_van_kampen.zip > avk.zip
git show 6914ccca6:docs/incoming/three_commutative_phases_research.zip > tcp.zip
git show 808b53ed8:docs/incoming/Order_Is_Not_a_Moment.zip > oinm.zip
git show 48ee077c7:docs/incoming/ProveIt_Affine_Matrix_Diophantine_Research.zip > amdr.zip
git show db37d18c8:docs/incoming/Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip > umsdc.zip
git show 0d7f51c44:docs/incoming/Chronological_Diophantine_Matrix_Certificates_Package.zip > cdmc.zip
```

(The last archive is 13,419,997 bytes, SHA-256 `ac5f61c6…`; it extracts to
68 files and 10 directory entries, with POSIX modes 0644, 0444 and 0600.)

No file of sources 06 and 07 was excluded as a heavy regenerable artifact
(the largest delivered file is source 07's 476,603-byte PDF). Source 08's
two r = 2 exports (1.27 MB together, 42% of its release) were excluded as
regenerable.
Source 09's polynomial DAG (11.1 MB, 83% of its 13.4 MB unpacked release) was
excluded as regenerable: its shipped builder rewrites it byte for byte.

## Reconstructing the excluded data

Source 08's two literal r = 2 sum-of-squares exports are not shipped:

- `paired/examples/r2-signed-sos.json`: 633,024 bytes, SHA-256
  `3dbe307c63b14f10fc8cdde91fc1dde5aa35b302333086741782604b70ef0c97`;
- `paired/examples/r2-natural-sos.json`: 636,038 bytes, SHA-256
  `5f27d31b13af124296729db2ed2333e015dd34835560693855619e7f09a93e5c`.

The shipped compiler writes them to standard output, byte for byte, in well
under a second each (Python 3.10 or newer, standard library only). It reads
the literal data from its packet's `data/semigroup.json`, so rebuild the
delivered layout in a scratch directory first. From the repository root, in
a POSIX shell (Git Bash works on Windows), with `W` a fresh directory
outside the repository:

```sh
D=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates
Q=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates
W=$(mktemp -d)/r32; mkdir -p "$W"
for f in "$D"/code/08-matrix-semigroup-* "$D"/data/08-matrix-semigroup-* "$D"/08-matrix-semigroup-*; do
  b=${f##*/08-matrix-semigroup-}
  case $b in
    core-*|fiber-*|paired-*|verification-*)
      d=$(printf '%s\n' "$b" | sed -E \
        -e 's#^(core|fiber|paired|verification)-(audit|data|evidence|loader-audit|tests|examples|source-manifests)-#\1/\2/#' \
        -e 't' -e 's#^(core|fiber|paired|verification)-#\1/#') ;;
    *) d=$b ;;
  esac
  mkdir -p "$W/$(dirname "$d")"; cp "$f" "$W/$d"
done
# the byte copies shipped once, and the U15 table shipped by quadratic-orthant-certificates
for p in paired fiber; do mkdir -p "$W/$p/data"
  cp "$W/core/data/semigroup.json" "$W/$p/data/semigroup.json"
  cp "$W/core/evidence/accepting-witness.json" "$W/$p/data/accepting-witness.json"; done
cp "$W/core/data/ledger.json" "$W/core/evidence/build-ledger.json"
cp "$W/core/evidence/check-normal.log" "$W/core/evidence/tests.json"
cp "$W/core/evidence/check-optimized.log" "$W/core/evidence/tests-optimized.json"
cp "$W/fiber/CHECKS.json" "$W/fiber/normal-run.json"
cp "$W/fiber/CHECKS.json" "$W/fiber/optimized-run.json"
cp "$W/fiber/audit/normal.json" "$W/fiber/audit/optimized.json"
cp "$W/paired/audit/authored_tests_optimized.json" "$W/paired/evidence/tests-optimized.json"
cp "$W/paired/audit/cli_accepting_94_check.json" "$W/paired/evidence/accepting-cli-check.json"
cp "$Q/data/16-universal-membrane-tm_table.json" "$W/core/data/u15_table.json"
# the two excluded exports
(cd "$W/paired" &&
 python3 -I -B paired_compiler.py export 2 --mode signed  > examples/r2-signed-sos.json &&
 python3 -I -B paired_compiler.py export 2 --mode natural > examples/r2-natural-sos.json)
sha256sum "$W"/paired/examples/r2-*-sos.json
```

The result is the delivered release minus six files (`report32.tex`,
`report32.pdf`, `RELEASE_README.md`, `MANIFEST.json`, `SHA256SUMS`,
`fiber/SHA256SUMS`): at this write all 74 reconstructed files were
byte-identical to the delivered ones, and the two exports took under two
seconds together (Windows 11, Python 3.14.4 through `py`). **On Windows the
shell redirection writes CRLF line endings** (666,416 and 669,594 bytes);
the files equal the delivered bytes, and the digests above, after CRLF → LF
conversion, for example
`py -c "import sys;p=sys.argv[1];b=open(p,'rb').read();open(p,'wb').write(b.replace(b'\r\n',b'\n'))" FILE`.
The recipe writes nothing into this directory.

The delivered bytes, together with the six files above, are in the arrival
archive (`git show` line in the previous section; extract with `unzip`).
The release's own verifier needs the complete delivered inventory: its
identity gate rejects any missing or extra file, so `verify_release.py`
runs only on an extraction of that archive, and
`verification/audit_literal_polynomials.py` reads all six r = 0, 1, 2
exports.

### Source 09's polynomial DAG

`science/evidence/polynomial-dag.json` (11,069,996 bytes, SHA-256
`95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034`, the
digest printed in Section 87 and recorded in
`data/09-chrono-matrix-science-evidence-build-receipt.json`) is the
authoritative literal graph of Part VI's polynomial. The shipped builder
regenerates it from the research programme's countdown receipt, which is
the same file at this write as at the source's pin and which the builder
checks by its SHA-256 (`f365eb9b…`). From the repository root, in a POSIX
shell (Git Bash works on Windows), with a fresh directory outside the
repository:

```sh
D=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates
N=Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue
B=$(mktemp -d)/science; mkdir -p "$B/sources"
cp "$D/code/09-chrono-matrix-science-build_certificate.py" "$B/build_certificate.py"
cp "$N/matrix193_countdown_rows.json" "$B/sources/"
(cd "$B" && python3 -I build_certificate.py > build-stdout.json)
sha256sum "$B/evidence/polynomial-dag.json"
```

The builder writes the DAG as bytes, so it is byte-identical on every
platform; at this write it took 2–9 s on Windows 11 (Python 3.14.4 through
`py`). It also writes `evidence/build-receipt.json` and
`evidence/coefficients.json`, which equal the shipped
`data/09-chrono-matrix-science-evidence-*.json` exactly on POSIX and after
CRLF → LF on Windows (the builder writes text with the platform newline).
The recipe writes nothing into this directory.

## Labels and numbering

Every label carries the prefix `gts:`; the report has 463 labels.

- Batch 76 (189 labels): source 03's 89 labels are `gts:vk:` plus their
  delivered names, and source 05's 64 are `gts:tp:` plus theirs; no source
  label was dropped or renamed apart from the prefix. Source 05's three
  Heisenberg equation labels (`gts:tp:eq:Hmult`, `gts:tp:eq:Hinv`,
  `gts:tp:eq:Hpower`) sit on the common Section 1.2. The merge added 36
  labels: twelve `gts:` labels of the front section, the two Parts and the
  provenance appendix (`gts:sec:front`, `gts:sec:parts`, `gts:sec:heis`,
  `gts:eq:commutator`, `gts:sec:notation`, `gts:tab:notation`,
  `gts:sec:relation`, `gts:sec:status`, `gts:sec:questions`,
  `gts:part:vk`, `gts:part:tp`, `gts:app:provenance`); `gts:vk:q:*` on
  source 03's twelve research questions and `gts:tp:q:*` on source 05's nine
  research directions; `gts:vk:sec:problem`; `gts:tp:rem:credit`; and
  `gts:tp:app:sources`.
- Batch 78 (+135 labels; none of the 189 was renamed or removed): source
  06's 55 labels are `gts:po:` plus their delivered names, and source 07's
  69 are `gts:ai:` plus theirs. The write added eleven: `gts:part:po`,
  `gts:part:ai`, `gts:tab:letters78`, `gts:po:sec:literature`,
  `gts:po:sec:projection`, `gts:po:sec:software`, `gts:po:sec:questions`,
  `gts:po:app:names`, `gts:po:app:provenance`, `gts:ai:rem:subgroup` and
  `gts:ai:rem:binomial`.
- Batch 82 (+64 labels; none of the 324 was renamed or removed): source
  08's 61 labels are `gts:um:` plus their delivered names (its bibliography
  keys carry `um-`). The write added three: `gts:part:um`,
  `gts:um:tab:letters` and `gts:um:app:sequence`.
- Batch 91 (+75 labels; none of the 388 was renamed or removed, and every
  one of them keeps its printed number, checked label by label against a
  build of the committed text): source 09's 73 labels are `gts:cm:` plus
  their delivered names (its bibliography keys carry `cm-`). The write
  added two: `gts:part:cm` and `gts:cm:tab:letters`.

Each Part keeps its source's numbering of statements, by section: source
03's Section *n* is Section *n* + 1 here (Sections 2–17); source 05's
Section *n* is Section *n* + 17 (Sections 18–31); source 06's Section *n* is
Section *n* + 31 (Sections 32–42); source 07's Section *n* is Section *n* +
42 (Sections 43–60); source 08's Section *n* is Section *n* + 60 (Sections
61–76; earlier versions of this README said 61–75); source 09's Section *n*
is Section *n* + 76 (Sections 77–90). Theorem *n.m* moves with its section. The two
statements the batch-78 write added, Remarks 46.3 and 53.2, follow every
source statement of their sections, so no source number changed. Source
03's appendices A–C keep their letters; source 05's appendices A–C are
Appendices D–F; Appendix G is the provenance; source 06's appendices A and
B are Appendices H and I (placed after G so that A–G keep their letters);
source 07 has none; source 08's appendices A and B are Appendices J and K;
source 09's appendices A and B are Appendices L and M.
Source 08's equations are numbered (V.*n*), *n* its own equation number;
its figure and its machine table are Figure 1 and Table 4 (the new letter
table is Table 3, and no earlier number moved). Source 09's equations are
numbered (VI.*n*), *n* its own equation number; its tables are unnumbered,
and the new letter table of Part VI is Table 5, printed at the start of
Part VI rather than in Section 1.3 so that Table 4 keeps its number. Text
written at the batch-76 merge is marked `[write]`, text written at the
batch-78 write `[write 78]`, text written at the batch-82 write `[write
82]`, text written at the batch-91 write `[write 91]`; text without a marker
is the source's own.

## Setting and notation

Sources 03–07 use the integral Heisenberg group with the same
convention, `h(a,b,c)h(a',b',c') = h(a+a', b+b', c+c'+ab')`; sources 08
and 09 do not use it (source 08's free pair `P, Q` is Part I's Sanov pair
`A, B`, and source 09's lower marker `P_0, Q` is source 08's `P, Q`).
Renamed symbols (no normalization changed anywhere):

- source 03's group `H = Z^3`, `(x,y,z) = h(x,y,z)` → `𝖧`, because Part I
  also uses `H` for a height bound;
- source 06's matrix `H(α,β,γ)` and group `ℍ` → `h(α,β,γ)` and `𝖧`;
- source 07's interpolation coordinates `λ_i(t)` and vector `𝛌(t)` →
  `θ_i(t)` and `𝛉(t)`, because `λ` is Part II's coordinate `2c − ab`.

Source 08 renames no symbol; only its macros `\mat` and `\norm` (the
maximum absolute row sum) are printed with this report's `\smallmat` and a
new `\umnorm`, with the same meaning.

Source 09 renames one symbol, with no change of normalization: its
**selector streams `E_i` (and the loader's `E_0`) are written `Λ_i`**
(Sections 83–86 and Appendix L), because it also writes `E_i` for the
inherited lower-marker matrices `E_i = Q^{−i} P_0 Q^i` of Section 79 (which
are Part V's `E_j`) and `E_0 = P_0` for the marker itself. Its digest macro
`\sha` is printed as `\cmsha` (source 03's `\sha` is a snapshot macro here).
The shipped notes and review of source 09 keep the source's `E_i`. Inside
its own text source 09 reuses `R` (`Ψ(U)^{−1}` in Section 79, the repetition
stream from Section 82 on), `b` (the base of a power in Sections 80–81, the
packing radix from Section 82 on), `a` and `H`; each use is confined to its
sections and is kept (Section 1.3 lists them).

Source 07's `\cref` cross-references (33) are printed as "Lemma …",
"Section …" and so on; one proof step of source 06 called "the second
phase" is printed as "the second stage". Bibliography keys of sources 06,
07 and 08 carry `po-`, `ai-` and `um-`, with entries unchanged. Tables 1–3
(Section 1.3) list the letters used differently, among them:

- `A, B` — Part I: shear matrices (and `a⁻¹`, `b⁻¹` in software words);
  Part II: phase homomorphisms; Part III: letters of the alphabet; Part IV:
  `A = VBV⁻¹`, a shear `B`, a lattice basis `B`, `B(t) = binom(t,2)` (Part
  II's `𝔟(t)`).
- `T` — Part II: the third phase `T(r) = h(−r,−r,𝔟(r))`; Part III: doubled
  pair counts `T_ij`; Part IV: the pencil `T(t,s) = h(t,t,s)` and a hit set.
- `a, b, c` — Part II: coordinates of `h(a,b,c)`; Part III: letter
  multiplicities (Part II's `2c − ab` reads `2γ − αβ` there, never
  `2n_C − n_A n_B`).
- `λ`, `ℓ` — Part I: label indices; Part II: `λ = 2c − ab`; Part III: `ℓ =
  (2α, 2β, λ)` and sign-split witnesses `λ_j^±`; Part IV: `θ_i` (source
  `λ_i`).
- `L, U, D, K, P, N, E` and others — see Table 2.
- Part V (Table 3): `A_i, B_i, C` are its 229 `4 × 4` generators and
  `A, …, O` the machine states, never Part I's shears (Part V calls those
  `P, Q`); `E_j = Q^{−j} P Q^j` and the target map `E(ℓ, ρ)`, not Part I's
  chart equation `E`; `D` the upper block of `C`; `U = U_{15,2}` the
  machine; `S` the semigroup; `r` the certificate length (number of tiles).
- Part VI (Table 5, at the start of Part VI): `x` the ordinary positive
  input and `𝒜` the accepted inputs; `T(x)` the `7 × 7` direct-input
  target; `B` the `2 × 2` loader matrix; `𝖠_i, 𝖡_i, 𝖢` the 193
  context-transferred generators (not Part V's 229 `A_i, B_i, C`); `H` the
  common packing offset `2^ℓ`; `C_0` the central matrix and `C_* = 2^104`
  the radix factor; `U, V` the context words `[110`, `A0]`; `Λ_i` the
  selectors.

Watch for these readings (Section 1.3):

- **Phase** (Part II) is one commuting factor of an ordered product of
  subgroups or submonoids — not a complex phase, a Fabius/Rvachev phase, or
  the "four-phase zero test" of `canonical-diophantine-certificates`
  Part XIII. Parts III and IV do not use the word.
- **History-free** (Part I's subtitle) means that no conjugator *word* is
  stored, only four chart integers. It is not the sense of
  `canonical-diophantine-certificates` Part XIV.
- **Compiler** is unrelated to the sparse-machine "universal compiler" with
  arithmetic-operation counts in the Hilbert-tenth-problem research notes;
  no operation record is claimed.
- **Slice**: Part I's Corollary 7.4 is a bounded-*area* slice; Part II's
  Corollary 20.3 is a *central* slice of `𝖧^N × Z^m`.
- **Moment** (Part III's title) is a gap-index sum `Σ(c−i)x_i`, not a
  probabilistic moment and not Part IV's moment curve `(t, t², …, t^k)`.
- **Pair count** (Part III) is the central coordinate of Part I's detector
  on a positive word, not a filling area.
- **Single-fold**: Part III over a complete pair profile, not over a
  projected target; Part IV over accepted inputs of languages already forced
  to be finite or periodic. Neither is a single-fold MRDP.
- **Exactly periodic** (Part IV) means a union of residue classes on all
  of `Z`; `Spec_c` (Part III) is a set of pair counts.
- **Universal** (Part V's title) means one fixed list of matrices whose
  membership problem simulates a universal Turing machine — not a universal
  polynomial, and with no arithmetic-operation count; its r.e.-completeness
  is conditional on the Neary–Woods chain.
- **Certificate length** `r` (Part V) is a number of tiles; `F_r` has
  `130r` witnesses, so the family has no fixed arity.
- **Fibre** (Part V) counts factorization words (equivalently tile
  sequences, or canonical roots) of one target; finite at each `r`, infinite
  over all `r`.
- **Chronological** (Part VI's title): the certificate stores one history
  in time order with every join enforced, not a multiset of local steps.
- **Fixed arity** (Part VI): one polynomial with a fixed list of 41,309
  witnesses for histories of every length (contrast Part V's `130r`). It
  is for one fixture, not a universal polynomial.
- **Gates** (Part VI) are binary additions, subtractions and
  multiplications with fixed numerals free — the convention of the research
  programme's "operations", so 184,016 gates and the 84-operation universal
  bound are counted the same way.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 03).** Sanov's chart (classical; proof included): the
  free group on two letters is exactly the integral points of
  `x + t + 4xt − yz = 0`. A fixed-itinerary quartic with `8m − 4` witnesses
  and `5m` residuals, and an all-label area-budget quartic with
  `(2s+13)m − 4` witnesses and `(2s+11)m` residuals, whose zeros are in
  bijection with (padded) factorizations and which accept exactly the words
  of area at most `m`. A small-witness height bound (from the
  Cornulier–Tessera bounded-conjugator lemma, imported) and a
  primitive-recursive decision of bounded-area slices. The compiler's
  minimal allocated arity equals `(2s+13)·Area − 4`, and the Dehn function
  correspondingly; the computable-cutoff equivalence with the word problem
  (classical, reproved through the compiler). A proof-DAG quartic with
  `4p + 8h + 4j + 4h_c − 4` witnesses. For `[a^(2^k), b^(2^ℓ)]` in
  `⟨a,b | [a,b]⟩`: area `2^(k+ℓ)`, exactly `k+ℓ` product gates (optimal in the
  stated calculus), and an `8(k+ℓ) − 4`-witness quartic. An addition-chain
  sandwich for rectangular commutators; no computable sharing bound; infinite
  native fibres.
- **Part II (source 05).** An integral binomial normal form of quadratic
  maps; three injective phase homomorphisms into `𝖧^N × Z^m` whose ordered
  product realizes every integral quadratic system with an exact
  fibre bijection; central embeddings into a pure power `𝖧^(N+m)`; with
  MRDP, three fixed free abelian subgroups of `𝖧^d` with computably
  enumerable complete product membership, even on a central affine cyclic
  line (**proposed** negative answer to the three-subgroup question of
  König–Lohrey–Zetzsche, Remark 6.7, and Roman'kov); decidability of two
  commuting phases for integer, natural and mixed exponents; free
  commutative monoid versions; an explicit quartic reverse compiler with
  `2n + 2N` parameters; exact counting, weights and height bounds; no
  computable search bound; an explicit three-subgroup product in `𝖧 × Z`
  (from `F(x) = 6x² − 5x`) that is not closed in the profinite topology.
- **Part III (source 06).** For three letters with multiplicities `a, b, c`
  and pair counts `K_AC = p ≤ ac`, `K_BC = q ≤ bc`, the realizable values of
  `K_AB` form a gapless interval with explicit endpoints (Theorem 35.3).
  A six-equation quadratic certificate with `2c + 4` natural witnesses for
  each externally fixed `c` (Theorem 34.2); for `c = 2`, endpoints from four
  bilinear corner values (Theorem 36.2) and a canonical quartic with 24
  natural witnesses, 24 residuals and 297 monomials that has exactly one
  witness tuple on each accepted profile (Theorem 37.1). Four letters:
  spectra `{bj : 0 ≤ j ≤ ⌊n/2⌋}`, hence arbitrarily large holes and an
  integral hole in the convex hull (Theorem 38.1, Corollary 38.2). A lift to
  three generators of `𝖧^r` with `3r` added equations (Theorem 39.1), and
  decidable membership in a three-generator submonoid of `𝖧^r` when the
  multiplicity of one generator is supplied (Theorem 40.1).
- **Part IV (source 07).** For every entrywise affine unimodular curve
  `L(n) = C + nD` in `SL_d(Z)` and every subgroup `K`, the hit set
  `{n : L(n) ∈ K}` is finite (at most `k ≤ d − 1` elements, `k + 1` the
  nilpotency index of `C⁻¹D`) or exactly periodic (Theorem 46.1), with the
  free basis `I+N, …, I+kN` of the evaluation group (Theorem 45.2), the
  sharp period `P_k(e)` (Theorem 47.4) and every nonempty set of at most `k`
  integers realizable. Single-fold degree-`2k` certificates for these rigid
  languages given a lattice basis; no uniform algorithm (Proposition 50.1);
  a commuting-polynomial extension. With the repository's quadratic loader
  (reconstructed and attributed, Theorem 52.1), input degree two is the
  least degree that can load a noncomputable c.e. set, in every dimension
  (Corollary 52.2). A `6 × 6` jointly affine multiplication gadget (Theorem
  53.1) and an affine abelian compiler into `SL_{6g+2}(Z)` with `2g` unique
  added coordinates and a quartic certificate (Theorem 54.1); with MRDP,
  every c.e. relation through a fixed free-abelian unipotent subgroup
  (Corollary 54.2); one quantified coordinate is decidable in the
  block-cyclic form (Proposition 56.1).
- **Part V (source 08).** One literal list of 229 matrices in `SL_4(Z)`
  (114 `A_i`, 114 `B_i`, one `C`; 1,831 nonzero entries, largest
  63,038,000) such that `U_{15,2}` halts on a finite tape `(ℓ, ρ)` iff the
  target `E(ℓ, ρ)` lies in the positive semigroup they generate (Theorem
  61.1, proved: a 93-rule directed rewriting system, Lemma 63.1; 114
  correspondence tiles with a fresh separator, Lemma 64.1; free conjugates
  `E_j` of a Sanov shear, Lemma 65.1; a free-group marker forcing the word
  form `A…A C B…B`, Lemma 66.1). With the cited Neary–Woods chain this makes
  membership many-one r.e.-complete — **conditional**, not reproved or
  implemented. For each length `r`, a literal sum of `17r + 4` squares in
  four signed target entries and `130r` natural witnesses, degree 4 for
  `r ≥ 1`, whose roots are in bijection with length-`r` tile sequences
  (Theorem 61.2); exact ledgers; a length-two target with two tile
  sequences (two such collisions among 12,996 sequences); the 94-tile,
  189-factor accepting certificate of `[110A0]`; infinite fibres of every
  accepted target (a stutter argument) and the exact rational generating
  function of the fibre of an accepted live input (Theorem 73.1, first
  terms 1, 0, 1, 0, 2, 1, 3, 2, 6, 5, 14, 7, 19 from `r = 94`).
- **Part VI (source 09).** One literal polynomial `𝒫(x, w_1, …, w_41309)`
  of exact total degree 12, a sum of squares of 23,618 residuals with
  184,016 binary gates (72,093 multiplications, 64,111 additions, 47,812
  subtractions), such that for every positive integer `x`, `x` is accepted
  by the pinned five-register countdown (initial rows
  `(35426321, −19628667)`, `(1, 0)`, counter `x`; one loader and 96 tile
  branches; accept at `X = Y`, `n = 0`) iff `𝒫(x, w) = 0` for some positive
  integers `w` (Theorem 77.2). Its pieces are proved in the Part: the
  fifteen-equation POWER module from the pinned mathlib theorems
  `Pell.matiyasevic` and `Pell.eq_pow_of_pell` (Section 80); exact binary
  containment by `(R+1)^M` digit parity (Lemma 81.1); paid slice partition,
  chronological joins, carry-free signed updates with `C_* = 2^104`, and
  the exact phase `LOAD^x TILE*` (Lemmas 83.1, 84.1, 85.1, 86.1); the
  ledgers `1475·26 + 491·5 + 504 = 41309` witnesses and
  `1475·15 + 491·3 + 20 = 23618` residuals; exact degree 12 from the
  monomial `w^8 g^4`. Under the research programme's faithful-group,
  lower-marker, context-transfer and synchronized-row theorems
  (**inherited, not re-proved**) this is membership of the target `T(x)` in
  the semigroup of 195 fixed singular integer `7 × 7` matrices; the
  control-language lemma 79.1 and the row implication are proved.

**Credit for the two-phase theorem (Remark 23.2).** For
*integer* exponents, source 05's two-phase decidability is a special case of
known results, which source 05 does not cite for it: König, Lohrey and
Zetzsche, Remark 6.7 (a product of two subgroups of a polycyclic group is
profinitely closed, hence has decidable membership), and Roman'kov, J. Group
Theory 28 (2025) (the product of two subgroups membership problem is
decidable in every finitely generated nilpotent group of class two). What
source 05 adds: a direct, elementary decision procedure for commuting lists
through the integral logarithmic coordinate `λ = 2c − ab`, reducing
membership to one integer linear system; and the natural and mixed exponent
domains, i.e. ordered products of two finitely generated commutative
submonoids (or of such a submonoid and an abelian subgroup), which are not
subgroup products. No priority is claimed for the latter; the literature on
submonoid products beyond those two papers was not searched.

**Credit added at the batch-78 write.** Parikh matrices (Mateescu, Salomaa,
Salomaa and Yu, 2001), which source 06 cites only through Teh: for an
ordered binary alphabet the Parikh matrix is source 06's recording factor
`h(n_X, n_Y, K_XY)`, and its binary realization lemma is the description of
binary Parikh matrices; the ternary Parikh matrix does not record `K_AC`, so
the interval theorem concerns 2-binomial data. Source 07's curve `Q(n)` is
the curve (12) of the research note `group_unipotent_input_loaders.md`,
which source 07 does not cite.

**Credit added at the batch-82 write** (none of it cited by source 08).
Lemmas 63.1 and 64.1 re-derive, for the same machine, the rewriting and
fresh-delimiter tile construction of the research notes
`neary_woods_explicit_universal_tm.md` (commit `f2622a68c`, 1 October 2026:
92 rules, 113 or 97 tiles, ending at `[halt]`) and
`gpcp_complete_fixed_program.md` / `gpcp_fixed_program_input_bridge.md`;
source 08 ends at a fresh letter `X` (93 rules, 114 tiles). No novelty is
claimed for the two lemmas. Table 4 (the `U_{15,2}` table) and its
`(u10,b)`/`(u10,c)` erratum are the collection's third printing, after
`qoc:wf:tab:tm` and `qoc:um:tab:tm` of `quadratic-orthant-certificates`;
all 30 cells were compared at this write. The first half of Lemma 65.1 is
Sanov's theorem (Part I, Theorem 4.1).

**Credit added at the batch-91 write** (none of it cited by source 09).
Section 80's POWER module is Lemma `ptr:ai:lem:exp` of
[`periodic-turmite-first-revisits`](../periodic-turmite-first-revisits)
(its Report 42): the same fifteen equations up to variable names, there
counted as 70 operations with 25 positive internal witnesses; it is printed
as a marked second route. The parity fact behind Lemma 81.1 is Lucas's
theorem modulo 2, the classical masking relation of the Jones–Matiyasevich
register-machine proof (J. Symbolic Logic 49 (1984) 818–829). Lemma 79.1
and the row implication (VI.9) re-prove the research programme's
counted-suffix and Γ₁(5) first-row notes, which source 09 cites.

The report does **not** claim:

- historical priority for any Part (sources 03–08 say so; source 09 makes no
  priority statement, and its POWER module is an earlier repository
  construction, Lemma `ptr:ai:lem:exp`); for Part
  II's main theorem, the placement check found no earlier resolution (the
  arXiv text of König–Lohrey–Zetzsche and the abstract of Roman'kov, which
  still states the three-subgroup case open), but that does not certify
  novelty, and Roman'kov's full paper was not read by source 05; source 07
  names the comparison with Leibman, Hu and Cahen–Chabert as its open
  priority audit; source 08 makes no novelty claim, and the batch-82 write
  did not survey the matrix-semigroup undecidability literature;
- a finite-fold or single-fold Diophantine representation of c.e. sets or of
  group word problems; Part I's native fibres are generally infinite, Part
  II transfers fold bounds only conditionally (the four-square conversion can
  change multiplicities), Part III's canonical quartic is single-fold over a
  complete profile but not over a projected matrix target, Part IV's
  added circuit coordinates are unique only given the source witnesses, and
  Part V's roots are in bijection with tile sequences, not with targets, and
  are infinitely many over all lengths on every accepted target;
- a universal arithmetic-operation record, an improvement of the universal
  degree-four bound or of the repository's 87-operation benchmark (the
  figure at the batch-78 write; the research programme's figure has since
  fallen, to 84 operations at `20aafb9a5`), an optimized ambient dimension, an
  instantiated universal presentation, Higman subgroup, Roman'kov monoid,
  polynomial, or universal *subgroup* matrix table. Part V does instantiate
  a universal matrix table, but for a positive *semigroup* (no inverses
  adjoined), conditionally on the Neary–Woods chain, and its evaluator
  charges (`11246r − 9036` multiplications and `3804r − 2700` additions for
  `r ≥ 1`) belong to one unoptimized evaluator;
- for Part V: an implemented loader from arbitrary programs to finite
  `U_{15,2}` tapes (its encoder starts at a finite tape), inverse closure, a
  minimal generator count (the research programme has since lowered it to
  197 and then 193; see below), or a decision procedure (the fibre formulas
  presuppose an accepted input);
- that its counts are minimal: they are the literal counts of the stated
  compilers; Part I's lower bound is a lower bound in its stated proof
  calculus, and Part IV's dimension `6g + 2` and its gadget are not claimed
  optimal;
- one fixed-arity polynomial: Part I's budget and circuit shape, Part
  III's separator count `c` and Part V's certificate length `r` are external
  data, and MRDP's fixed-arity polynomial preserves neither fibres nor the
  area ledger;
- that Part II answers the open question of the repository note
  `heisenberg_two_generator_membership.md` (do three generators of a
  Heisenberg *submonoid* suffice for undecidability?) — it does not; it
  concerns ordered products of three *subgroups*. **Part III answers it in
  part** (exact ternary word realizability; decidability with a supplied
  multiplicity), and leaves the unrestricted three-generator question open;
- that Part IV's classification is computable from subgroup generators (it
  proves that it is not, uniformly), or that its degree threshold bounds
  anything but the input degree of its stated interface; the degree-two
  half rests on the external effective Higman embedding (Mikaelian) through
  the repository construction it reconstructs;
- for Part VI: a universal polynomial or an arbitrary-program compiler (the
  contexts `[110` and `A0]` are one fixture; program-dependent matrices
  would need a newly computed radix factor); an improvement of the
  84-operation universal bound, a shortest circuit or optimality; a
  finite-fold or unique-witness representation (offsets and quotients
  vary), a real-witness equivalence (the positive-integer domain is part of
  the theorem), a witness-size bound or a computable bound on the offset
  from `x`; a mortality theorem, inverse-closed group membership or a
  193-generator Pell391-loader result; a materialized numerical zero (no
  complete nested-Pell witness was generated; Lean and the upstream
  programs were not run). Its audits and reviews come from the pipeline
  that wrote it; the research programme's review `a9ab9a698` is the outside
  check, and covers the DAG's arithmetic only;
- any Lean or Rocq verification. The finite checks illustrate; they do not
  prove.

**Open items of Part VI (Vladimir's rule of 4 October 2026: no unproved
claim is dropped).** Two claims of source 09 are used, not proved, in this
report; both stay where the source states them and are listed as open,
with the source's sketch and what is missing, in the `[write 91]` note
after its questions (Section 90): (a) the matrix-interface equivalence of
Theorem 77.2 — the source proves the row implication and the
control-language lemma but takes the finite-graph basis proof of
`H′ ∩ ⟨U_0⟩ = {I}`, the free-group marker argument and the context
telescoping from the research programme's notes; (b) the program-family
interpretation — it needs the Neary–Woods simulation premise and an
implemented compiler with per-program radix factors. The POWER semantics
rest on the pinned mathlib theorems (formal in mathlib, not re-run here).
No statement of source 09 was found false.

## Relation to neighbouring reports and to the formal project

This is one of twelve report directories of the collection's
`hilbert-tenth-problem` category at the batch-82 write and at the batch-91
write (seven at the batch-78 write), which are organized by substrate family; finitely
presented, nilpotent and matrix groups, and since batch 82 a matrix
semigroup, form this one.

- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**,
  Part VI (its sources 11 and 16; `pqc:dr:thm:main`): Mihailova's
  fibre-product compiler from finite presentations to rotation gates in
  `SO(4, Z[1/5])`, c.e.-complete membership of a fixed finitely generated
  subgroup, and quartic certificates for bounded *words*. Part I has the same
  input but certifies relator area and proof-DAG size in a free subgroup of
  `SL_2(Z)`; Part II has a statement of the same kind for a product of three
  abelian subgroups of a unitriangular group. Step 3 of Part IV's Theorem
  52.1 prints Mihailova's generators again (`pqc:dr:prop:mihailova`), as a
  marked second route with that pointer — the one re-proof of a
  neighbouring report's result in this report. The bounded-search argument
  of `pqc:qm:cor:nobound` recurs, for different statements, in Part I
  (Corollary 8.3, Theorem 13.2) and Part II (Proposition 27.1).
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  executions compiled to canonical arithmetic zeros. Part I's native compiler
  is explicitly not canonical; Part II compiles in the reverse direction.
  Its Part XIV uses "history-free" in another sense; its research-question
  remark on four-squares conversions is Part II's four-square caveat, also
  repeated by sources 06 and 07. Since batch 83, its Part XX (manuscript 22,
  Report 35, `cdc:lp:thm:loader`) drives a literal periodic sandpile loader
  with the same `U_{15,2}` and the same imported program-to-tape encoder; its
  provenance record says the pinned table was "supplied from the prior
  matrix-semigroup construction". Neither report implements the encoder; no
  shared theorem (reciprocal note of 3 October 2026 in Section 1's relation
  list).
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**: no overlap.
- **[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)**
  (Parts III and V): the same `U_{15,2}` table and erratum
  (`qoc:wf:tab:tm`, `qoc:um:tab:tm`); Part V's Table 4 is the third
  printing, and source 08's serialized table is that report's data file
  `16-universal-membrane-tm_table.json`. No shared theorem.
- **[`fixed-universal-polynomials`](../fixed-universal-polynomials)**,
  Part I, and **[`five-particle-binary-automata`](../five-particle-binary-automata)**,
  Part II (Reports 23 and 16 of the same pipeline, placed in the same
  batch): source 08's dependency audit cites them for the finite `U_{15,2}`
  input convention only (Report 16's loader and table, Report 23's
  ordinary-input frame); Part V uses nothing else from them.
- **[`stochastic-and-thermal-exactness`](../stochastic-and-thermal-exactness)**,
  Part I (`ste:ee:thm:pcp`): Post correspondence to integer matrix
  *mortality*, with the instance as input; Part V has one fixed semigroup
  and the target as input. Same classical idea, no shared theorem.
- **Within this report**: Part III's recording map is Part I's area detector
  applied to one pair of letters; Part III's logarithmic map carries Part
  II's `λ = 2c − ab` (the third derivation in the repository); Part II's
  three-subgroup theorem shows that Part IV's subgroup hypothesis is
  necessary, and answers the negative half of Part IV's question 9 for
  three-factor products (Remark 46.3); Part IV's cyclic test
  `⟨h(1,1,0)⟩` is Part II's binomial device in a different cyclic subgroup
  (Remark 53.2). Part V's free pair is Part I's Sanov pair; Part V answers
  Part IV's question 10 ("charge a complete universal matrix certificate")
  **in part** — a numerically instantiated universal alphabet, but for a
  positive semigroup and with bounded-length certificates, so the subgroup
  alphabet and the fixed-arity unbounded checker remain open (dated
  `[write 82]` note there) — and does **not** answer question 9 for
  positive-word semigroups, since its target map is not an affine curve.
  Its question 7 (a uniform unbounded polynomial) is what remains of
  question 10. **Update (4 October 2026, batch 91).** The fixed-arity
  unbounded checker now exists in part, for a semigroup: Part VI gives one
  fixed-arity polynomial (41,309 witnesses, degree 12, 184,016 gates) for
  histories of every length of the research programme's 195-generator
  singular `7 × 7` successor of Part V's semigroup, for one pair of fixed
  contexts, and the programme's uniform compilers pay the same histories
  for every valid program recipe in 1,393 operations at exact degree 71,105
  (1,399 at 35,587). The subgroup alphabet remains open, and neither
  construction is below the 84-operation bound (dated `[write 91]` notes at
  Part IV's question 10 and Part V's question 7, which Part VI answers in
  part: it pays sequences and arithmetic at fixed arity but not
  canonicality).
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:
  `group_commutator_universal_substrate.md` (universal subgroup membership
  in `SL(4,Z)` along a fixed quadratic curve; Part IV's Theorem 52.1 is its
  attributed reconstruction); `group_unipotent_input_loaders.md` (a free
  pair in `SL_2(Z)` without an arithmetic image; Part IV reprints its curve
  (12) as `Q(n)`); `heisenberg_two_generator_membership.md` (the coordinate
  `2c − ab`; two-generator submonoids decidable; its three-generator
  question is not answered by Part II and is answered in part by Part III);
  `group_affine_input_obstruction.md` (the paired-SL₂ case, `k = 1`, of
  Part IV's rigidity theorem; that note and two others restrict the
  degree-two conclusion to SL₂–SL₄ interfaces, which after Part IV applies
  to the single-coset shape only); `group_complete_matrix_compiler.md`
  (does part of Part IV's question 10; the programme's README calls its
  numerical universal alphabet uninstantiated — Part V supplies one only for
  a positive semigroup in the block form `diag(SL_2(Z), free group)`, not
  for that compiler's inverse-closed `diag(L_r, L_r)` interface); the affine
  mortality notes (a different interface);
  `group_projective_label_aligned_lanes.md` (source 03's own comparison);
  `neary_woods_explicit_universal_tm.md` and the `gpcp_*` notes (Part V's
  Lemmas 63.1 and 64.1 re-derive their construction; credit above).
- **Reviews of the batch-78 archives in that programme**, written before
  this placement: `incoming_substrate_review_808b53ed8.md` with
  `incoming_parallel_order_review_808b.md` (commit `126028588`, source 06)
  and `affine_matrix_square_projection_review808b.md` (commit `a1264b55c`,
  source 07). They found no mathematical defect and replayed both programs.
  They prove two reductions, printed in the article as dated `[write 78]`
  notes: source 06's quartic finalizer can leave eight sign-split products
  unsquared (289 monomials, eight fewer multiplications, nonnegative on the
  real orthant), or ten residuals (287 monomials, natural zeros only); and
  each square gate of source 07's compiler can drop one 3-dimensional block
  and one coordinate (dimension `6g − 3s + 2`; the worked example 20 → 17).
  The shipped files are the unreduced delivered ones.
- **The programme's review of the batch-82 archive**, written on the day it
  arrived and before this write: `review_incoming_matrix_grill.md` (commit
  `32da04296`), which read source 08's archive as data (no archived program
  executed), reconstructed the 93 rules, 114 tiles and 229 matrices, the
  coefficient census, the 189-factor accepting product and the six exported
  polynomials with their evaluator charges, found no discrepancy, and
  derived a **197-generator subset** (delete the copy tiles of the fifteen
  states and `X`; valid inputs only); and its successor
  `group_directed_semigroup193.md` (commit `0f7d618f4`), a **193-generator**
  semigroup with terminal word `[J1]` (91 rules, 96 tiles; accepting example
  83 tiles, 167 factors; largest entry 31 instead of 26 magnitude bits).
  Neither claims minimality, inverse closure or a Diophantine gate bound;
  both keep the Neary–Woods dependency. They are summarized in a dated
  `[write 82]` note at Part V's question 4, not printed. The shipped files
  are source 08's, unpatched. (Their helpers read the archive at its
  retired `docs/incoming/` path; it survives in `db37d18c8`.)
- **Part VI and the research programme** (all read-only here): source 09
  pins `matrix193_countdown_rows.{md,json}` (five-register countdown),
  `matrix193_synchronized_rows.md`, `matrix193_context_absorption.{md,json}`
  and `matrix193_gamma1_recode.md`, `group_directed_semigroup193.md`,
  `matrix193_kernel_row_projection.md`, `u15_unary_block_interface.md` at
  `750aeb4f7`, and `matrix195_counted_suffix.{md,json}` at `d31e29030`; all
  are unchanged at this write. At that pin the programme recorded
  "Unbounded fixed-arity packing remains unpaid"; source 09's "missing
  arbitrary-duration packing" was true then. The programme then filled the
  gap **by another route** the same night, before the archive arrived
  (`0d7f51c44`, 10:16 −0700): marked-loader packing (`b388dc588`, 02:34),
  the uniform grammar `matrix193_uniform_context_packing.md` (`bbb73e0c7`,
  176,586 operations, degree 2,360,653), atomic packing
  `matrix193_atomic_context_packing.md` (`7f7b87500`, 4,155 operations,
  degree 34,045), down to `matrix193_shared_action_fusion.md` (`a32e1b139`,
  10:12: 1,399 / 1,396 / 1,396 / 1,393 operations, 141–139 positive
  witnesses, exact degrees 35,587 / 53,345 / 53,347 / 71,105), uniform over
  valid program recipes with eight fixed coefficient ports. Part VI is the
  low-degree end of that trade-off (dated note in Section 78). The local
  countdown polynomial was also lowered after the pin, to 133 operations at
  degree 10 over the integers (`matrix193_centered_crt_selector.md`,
  `47b11748c`).
- **The programme's review of the batch-91 archive**,
  `review_new_arithmetic_0d7f51c44.md` with its manifest (commit
  `a9ab9a698`, 10:45 on the arrival day, before this write). It read the
  delivered README, `science/ARCHITECTURE.md` and `science/SOURCE_NOTES.md`
  completely, parsed the whole DAG as inert data and executed no archived
  program. It confirms 184,016 = 72,093M + 111,923A gates, operands,
  topological order and liveness, the 41,309 witnesses, the 113,163-gate
  body and 70,853-gate finalizer over all 23,618 residuals, and exact
  degree 12 (restricting the first POWER call's 13th residual to `w, g`
  gives `−w⁴g² − 2w³g²`, whose leading form is the `−w⁴g²` printed in
  Section 87). It reports **no defect**, calls the packet "a useful paid
  low-degree reference, with much larger cost and witness count than the
  current work", finds no lower paid unbounded compiler, and leaves the
  universal 84/187 and 85/155 points unchanged. It did not recertify the
  inherited Pell and group semantics or the chronological proof.
- **[`periodic-turmite-first-revisits`](../periodic-turmite-first-revisits)**:
  Section 80's POWER module is its Lemma `ptr:ai:lem:exp` (second route).
- **[`signal-machine-collision-certificates`](../signal-machine-collision-certificates)**,
  Part X (the pipeline's Report 58, batch 91, written at the same time as
  this Part): its five-signal certificate uses this Part's POWER module,
  and its delivered package bundles byte copies of three files shipped
  here — `code/09-chrono-matrix-science-build_certificate.py`,
  `09-chrono-matrix-science-SOURCE_NOTES.md` and
  `data/09-chrono-matrix-independent_audit-pell-dependency.json` (there
  `science/sources/prior-build_certificate.py.txt`, `POWER_SOURCE_NOTES.md`
  and `pell-dependency.json`; blobs `2be2a834a`, `85713ebac`, `9fed8753a`).
  The collection ships them only here; do not delete or rename them without
  updating that report.
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**,
  Part XXI (Reports 50 and 52–54, batch 91, written at the same time):
  fixed-arity packed sandpile certificates with the same expanded
  binary-containment masks. Source 09's packing review read the source notes
  of a packet named `sandpile-repeated-target-20261004` (by that name Report
  53's; shipped there as `26-repeated-target-science-SOURCE_NOTES.md`; the
  review records no digest, so byte identity is not established). No theorem
  is shared.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. Parts I, II and IV import MRDP only
  as a classical theorem (Parts III and V do not use it; Part V's
  universality comes from the Neary–Woods machine); the project's formal
  endpoint is `Diophantine.mrdp`, `Diophantine.mrdp_iff` and
  `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26), described by `Lean/MRDP.md` (cited by source 03) and
  `Lean/Diophantine/Common/MRDPCore.lean` (cited by sources 05 and 07);
  both files are unchanged from the sources' pins to the write. The project
  has formalized none of this report's statements: its Hilbert-tenth-problem
  Lean development has no free-group chart, Heisenberg-group, word
  pair-count, Dehn-function, subgroup-product, affine-matrix-curve,
  matrix-semigroup, correspondence-tile or `U_{15,2}` module, and no
  module for Part VI's countdown, packing, selector or containment
  statements. Its Lean development does use mathlib's `Pell.matiyasevic`
  (`Lean/Diophantine/Paper1976/Cor26.lean`), but for the four-equation
  system of Jones–Sato–Wada–Wiens Corollary 2.6, not for Part VI's
  fifteen-equation module; Part VI uses the theorem as a pinned external
  dependency (mathlib4 `ac77769f`). The Lean module names in Part III's
  formalization route are suggestions.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
microtype, booktabs, longtable, enumitem, fancyhdr, needspace, seqsplit,
listings, TikZ, xurl, hyperref). The batch-82 build had 154 pages: no undefined
references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes. The log has three underfull lines: badness
3118 in the `[write]` note on shipped file names at the start of Section 14
(present since batch 76), badness 1147 in the proof of Theorem 45.2 (source
07's text), and badness 2165 in the bibliography entry for Bogopolski and
Ventura. The batch-83 reciprocal note (3 October 2026; one item in Section
1's relation list, no label, macro, package or bibliography entry) leaves
the build at 154 pages with the same log and the same three underfull
lines; its page (printed page 19) was rendered and inspected.

The batch-91 write (Part VI) brings the committed build to **186 pages**
(unnumbered title page, then pages 1–185), with no undefined references or
citations, no multiply defined labels, no duplicate destinations, no
overfull boxes, and the same three underfull lines as before (badness 3118,
1147 and 2165, in the same three places); the new bibliography entries of
source 09 are set ragged right, as in the source, and add none. The log
also has five "Infinite glue shrinkage found in box being split" notices
from longtable page breaks (one before this write); they are informational.
To keep the title page on one page the main title is set on one line, the
subtitle is rebalanced over three lines, and two fixed vertical spaces of
the title page are smaller; the provenance table of Appendix G is now a
longtable, because the new row made it taller than a page; no text of
either changed apart from the `[write 91]` additions. All 388 earlier labels
keep their printed numbers (checked label by label against a build of the
committed text). Pages inspected at this write: the title page, the Part VI
opening and letter table (printed pages 144–145), Sections 77–78 (147), the
ledger (160), the questions and open items (166), the provenance
table (172), Appendices L–M (178) and the end of the bibliography
(185).

## Rerunning the programs

The verification programs of all six sources depend on their delivered
layout, and several write into it. **Never run them in place.** Copy `code/` and
`data/` to a scratch directory and recreate the delivered layout there
(`py` is the Python launcher on this machine; the delivered texts say
`python` or `python3`). Run without `-O`: sources 06 and 07 rely on
assertions.

```sh
# source 03 (needs SymPy 1.14.0)
mkdir -p r03/code r03/examples r03/verification
cp code/03-van-kampen-van_kampen.py r03/code/van_kampen.py
cp code/03-van-kampen-verify.py r03/code/verify.py
cd r03
uv run --no-project --with sympy==1.14.0 python code/verify.py --receipt verification/receipt.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py budget 1 --relator abAB --output examples/commutator_budget_1.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py grid 1 1 --output examples/grid_1_1.json
cd ..
# source 05 (standard library only)
mkdir -p r05/code r05/examples
cp code/05-three-phases-heisenberg_compiler.py r05/code/heisenberg_compiler.py
cp code/05-three-phases-verify.py r05/code/verify.py
cd r05 && py code/verify.py && cd ..   # writes r05/verification_receipt.json and r05/examples/*.json
# source 06 (standard library only)
mkdir -p r06/code r06/data
cp code/06-pair-order-pair_geometry.py r06/code/pair_geometry.py
cp code/06-pair-order-verify.py r06/code/verify.py
for f in canonical_c2_quartic verification_receipt worked_example; do cp data/06-pair-order-$f.json r06/data/$f.json; done
cd r06
py code/verify.py                                    # recomputes and compares with data/verification_receipt.json; never pass --write
py code/pair_geometry.py decide 3 2 2 1 4 > decide.json   # compare with data/worked_example.json
py code/pair_geometry.py export ../export06.json     # compare with data/canonical_c2_quartic.json
cd ..
# source 07 (standard library only)
mkdir -p r07
cp code/07-affine-inputs-verify.py r07/verify.py
cp data/07-affine-inputs-verification.json r07/verification.json
cd r07 && py verify.py --output verification.replayed.json && cd ..   # always pass --output
```

At the batch-76 write (Windows; `PYTHONUTF8=1`) sources 03 and 05 passed:
source 03's run (uv selected Python 3.13.5) reproduced the receipt and both
exported polynomials, and source 05's (Python 3.14.4) the receipt and all
six example files, each equal to the shipped file apart from line endings
(the Windows runs write CRLF; the shipped files are LF). That record does
not say whether the delivered or the `db3b377f0`-patched programs were run;
the message of `db3b377f0` reports that the patched programs pass both
author suites unchanged. The other three files of source 03 —
`grid_1_1_witness.json`, `render_check.json` and `export_check.json` — are
not written by any shipped program; the witness was rechecked at placement.
To compile a quadratic specification with source 05's compiler, run
`py code/heisenberg_compiler.py examples/multiplication_input.json out.json`
in `r05`.

At the batch-78 write (Python 3.14.4, `PYTHONUTF8=1`) the source 06 and 07
recipes above passed: source 06's verifier in 29 s (59 s at placement),
matching its receipt, including the SHA-256 of `pair_geometry.py`; the
`decide` output and the export equal `data/06-pair-order-worked_example.json`
and `data/06-pair-order-canonical_c2_quartic.json` as JSON; source 07's run
passed all 91,142 cases in about 5 s, and its output equals
`data/07-affine-inputs-verification.json` as JSON. Source 07's program never
compares with its receipt; compare the two files yourself, as above.

### Source 08

Source 08's release is sealed: `verify_release.py` first checks the exact
delivered inventory against `MANIFEST.json` and `SHA256SUMS`, which are not
shipped, and rejects any missing or extra file. Two routes:

1. **The sealed verifier, on the arrival archive.** Extract the archive
   (`git show` line under "Delivered names") into a scratch directory and,
   inside `universal-matrix-report32-release-20261003/`, run
   `python3 -I -B verify_release.py --verify-only` (identity gate only; at
   this write it passed in about 2 s: 78 payload files, status PASS) and
   `python3 -I -B tamper_regression.py > ../tamper.json` (18 cases; passed
   at placement in 37 s). `python3 -I -B verify_release.py --replay`
   (equivalently `sh rebuild_release.sh`) replays every component in
   fresh temporary copies; **it is POSIX-only**: on Windows it stops after
   about four seconds with "Core rebuild byte inequality: semigroup.json",
   because the delivered programs write text with the platform newline
   (below). The end-to-end replay was not rerun at placement or at this
   write.
2. **Single components, on the reconstructed layout** of "Reconstructing
   the excluded data" (`$W`). For example, from `$W`:
   `python3 -I -B core/compiler.py build > ../core-build.json` (stdout
   equals `core/data/ledger.json`; **rewrites** `core/data/semigroup.json`,
   `ledger.json` and `matrices.txt`), `python3 -I -B fiber/check_fibers.py >
   ../fiber.json` (stdout equals `fiber/normal-run.json`; rewrites
   `fiber/CHECKS.json`), `python3 -I -B core/audit/independent_check.py >
   ../core-audit.json` (compare with `core/audit/independent-results.json`,
   which it rewrites), `(cd paired && python3 -I -B paired_compiler.py
   verify examples/accepting-94-certificate.json)` (output equals
   `paired/audit/cli_accepting_94_check.json`: 1,602 residuals, all zero).
   At this write these four runs on Windows (Python 3.14.4), in this order,
   reproduced the receipts except for the one digest explained next, and
   the
   rebuilt `semigroup.json`, `ledger.json`, `matrices.txt` and `CHECKS.json`
   equal the delivered bytes after CRLF → LF. On Windows, run the core
   audit **before** the compiler build or on a fresh copy: after a Windows
   build the rewritten CRLF `semigroup.json` changes the digest the audit
   records (observed: `17452e8a…` instead of `506144b3…`). At placement all
   twelve replay components were rerun this way with LF output forced
   (ordinary mode; all but the export and certificate commands also under
   `-O`): every receipt and rebuilt file matched.

Run source 08's programs with `-I -B` as the release does; they rely on no
assertions (the release gate rejects `assert` statements).

### Source 09

Source 09's delivered tools are bound to its delivered layout and POSIX
file modes: `release.py verify` checks the complete inventory, sizes,
SHA-256 and **POSIX modes** against `MANIFEST.json` and refuses on NTFS
("Unexpected manifest mode"), and the replay adapter
`audit_replay/replay_audit.py` needs the complete frozen 19-file `science/`
and 12-file `independent_audit/` trees, which are not shipped as such
here (the DAG, seven research-programme copies and four log copies are
missing). Never run them in this directory. Two routes:

1. **The delivered tools, on the arrival archive, on a POSIX system.**
   Extract `cdmc.zip` (`git show` line under "Delivered names") preserving
   modes, and follow its README: `python3 -I release.py verify
   --manifest-sha256 <digest>` (no trusted digest was delivered; the
   archive's identity is its blob in `0d7f51c44`), and `python3 -I -S
   audit_replay/replay_audit.py --packet <abs>/science --audit
   <abs>/independent_audit --output <fresh external dir>`. On Windows the
   adapter's final byte gate fails: the checkers write their receipts with
   CRLF line endings (observed at placement; the receipts are otherwise
   equal).
2. **Direct runs on a reconstruction, from the shipped files** (any
   platform). From the repository root in a POSIX shell (Git Bash works),
   with `W` a fresh directory outside the repository and `PY` your Python
   (`python3`, or `py` on Windows):

```sh
D=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates
N=Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue
W=$(mktemp -d)/r55; P=$W/science
mkdir -p "$P/evidence" "$P/review" "$P/sources" "$W/audit" "$W/b/sources"
cp "$D/09-chrono-matrix-science-ARCHITECTURE.md" "$P/ARCHITECTURE.md"
cp "$D/09-chrono-matrix-science-SOURCE_NOTES.md" "$P/SOURCE_NOTES.md"
cp "$D/09-chrono-matrix-science-review-PACKING_REVIEW.md" "$P/review/PACKING_REVIEW.md"
for f in build_certificate check_semantics freeze_manifest; do
  cp "$D/code/09-chrono-matrix-science-$f.py" "$P/$f.py"; done
for f in build-receipt coefficients frozen-manifest semantic-checks; do
  cp "$D/data/09-chrono-matrix-science-evidence-$f.json" "$P/evidence/$f.json"; done
cp "$D/data/09-chrono-matrix-science-sources-provenance.json" "$P/sources/provenance.json"
for f in matrix193_countdown_rows.json matrix193_countdown_rows.md matrix193_synchronized_rows.md \
         matrix193_context_absorption.json matrix193_context_absorption.md \
         matrix195_counted_suffix.json matrix195_counted_suffix.md; do
  cp "$N/$f" "$P/sources/$f"; done
# rebuild the DAG in a throwaway copy, so that the LF receipts in $P stay as shipped
cp "$P/build_certificate.py" "$W/b/"; cp "$P/sources/matrix193_countdown_rows.json" "$W/b/sources/"
(cd "$W/b" && $PY -I build_certificate.py > build-stdout.json)
cp "$W/b/evidence/polynomial-dag.json" "$P/evidence/"
# the two independent checkers write their receipts beside themselves
for f in check_source check_interfaces; do
  cp "$D/code/09-chrono-matrix-independent_audit-$f.py" "$W/audit/$f.py"; done
$PY -I "$W/audit/check_source.py" "$P" > "$W/source.out"
$PY -I "$W/audit/check_interfaces.py" "$P" > "$W/interfaces.out"
# optional, last: the author's semantic probes rewrite $P/evidence/semantic-checks.json
(cd "$P" && $PY -I check_semantics.py > ../semantics.out)
```

   Compare `$W/audit/source-audit-receipt.json`,
   `$W/audit/interface-audit-receipt.json` and
   `$P/evidence/semantic-checks.json` with
   `data/09-chrono-matrix-independent_audit-source-audit-receipt.json`,
   `…-interface-audit-receipt.json` and
   `data/09-chrono-matrix-science-evidence-semantic-checks.json`. At this
   write (Windows 11, Python 3.14.4 through `py`) the whole recipe took
   about 45 s and all three receipts equal the shipped files after
   CRLF → LF (1,759 / 720 / 604 bytes as written, 1,701 / 697 / 584 as
   shipped); `check_interfaces.py` verified the 18 frozen author files,
   including the rebuilt DAG, against `frozen-manifest.json`. At placement
   the same checkers passed on an extraction of the archive, also under
   `python -O`. Do not pass the shipped `data/` receipts' directory as the
   checkers' location: they overwrite receipts of the same names.

`check_manuscript_data.py` hard-codes `/workspace/shared/…` paths and is not
portable; `test_replay.py`, `check_release_tools.py` and `check_layout.py`
test the release tools and the PDF, need the delivered layout, and were not
rerun; `freeze_manifest.py` is an author tool that rewrites
`evidence/frozen-manifest.json`.

## Discrepancies and disclosures

- The shipped `code/05-three-phases-build.sh` keeps the delivered layout: it
  changes to its own directory (`code/`) and runs pdflatex three times on
  `article.tex`, which is not there; it would not build this report. Use the
  build command above.
- The shipped `code/06-pair-order-Makefile` also keeps the delivered layout.
  Its targets run `python3 code/verify.py`, write
  `data/canonical_c2_quartic.json` (`export`), build `article.tex` with
  latexmk (`pdf`) and run `latexmk -c` and `rm -rf code/__pycache__`
  (`clean`). Run from this directory it would build *this* report and look
  for delivered names; do not run it in place. `code/06-pair-order-verify.py
  --write` overwrites the receipt of its layout.
- `code/07-affine-inputs-verify.py` writes `verification.json` in the
  current directory unless `--output` is given (argparse default), which
  would overwrite a receipt of that name; its source README advised bare
  `python` on Windows.
- Source 03's `SOURCES.md` and the reproduction section of Part I (Section
  14.3) name delivered paths (`code/verify.py`, `verification/receipt.json`,
  `examples/*.json`, `requirements.txt`, `arithmetic_van_kampen.tex`), and
  Part I's software section names `verification/receipt.json` and
  `code/van_kampen.py`; Part II names `code/heisenberg_compiler.py`,
  `code/verify.py`, `examples/multiplication.json` and
  `multiplication_input.json`; Part III's software section (Section 41)
  names `code/pair_geometry.py`, `code/verify.py`, `data/*.json`,
  `README.md`, `Makefile` and `article.tex`/`article.pdf`; Part IV's
  (Section 58) names `verify.py`, `verification.json` and `SOURCE_AUDIT.md`.
  These are delivered names (map above); `[write]` and `[write 78]` notes at
  those places give the shipped names. `03-van-kampen-render_check.json`
  describes source 03's own 29-page PDF, which is not shipped.
  `07-affine-inputs-SOURCE_AUDIT.md` calls source 07's manuscript "the
  article"; it is Part IV here.
- Source 03's `SOURCES.md`, `07-affine-inputs-SOURCE_AUDIT.md` and all
  four batch-76 and batch-78 sources' repository sections describe the
  repository at their pins (`c58206ca1`, `433df1be3`, `4cccfa068`). Every
  repository file they cite is unchanged from the pin to the write. None of
  them knew the related repository material listed above, and sources 06
  and 07 could not know Parts I and II; the report adds it (Section 1.4 and
  the notes in the Parts). Source 08 cites no repository file and knew none
  of Parts I–IV.
- The bounded-conjugator lemma of Part I is imported from
  Cornulier–Tessera (Lemma 2.D.2), not proved; it is needed only for the
  height bound and the bounded search. Part II's description of Roman'kov's
  paper rests on its abstract (source 05 did not read the full paper); the
  report's credit sentences rest on the same abstract and on the arXiv text of
  König–Lohrey–Zetzsche. Part IV's degree-two upper bound imports the
  effective Higman embedding (Mikaelian, arXiv:2507.04347), not run or
  reproduced.
- The delivered title pages are replaced by one title page; each source's
  title, subtitle (where present), abstract and status statement open its
  Part verbatim. The author line "Research report/manuscript prepared for
  Vladimir Reshetnikov" is kept, with "AI-assisted" added. Source 08's
  author line ("Research construction and reproducibility report") and date
  are quoted in Part V's opening, and its table of contents is dropped.

Source 08 (batch 82):

- **Delivery names.** Part V's Sections 61, 72, 73 and 74, Appendix K and
  its bibliography entries `um-Core`, `um-Paired`, `um-Fiber` name delivered
  paths (`core/data/semigroup.json`, `core/evidence/accepting-witness.json`,
  `paired/examples/…`, `paired/data/…`, `core/`, `paired/`, `fiber/`); the
  `[write 82]` notes after Section 74 (the general rule, with examples) and
  Appendix K give the shipped names, and the map under "Delivered names"
  above covers every file. The
  shipped Markdown files (`08-matrix-semigroup-*.md`), the receipts and
  manifests in `data/` and every program use delivered paths and name
  unshipped files: `report32.tex`/`report32.pdf` (`build_report.sh`),
  `RELEASE_README.md`, `MANIFEST.json`, `SHA256SUMS`, `fiber/SHA256SUMS`
  (`verify_release.py`, `build_release_inventory.py`,
  `archive_release.py`, `tamper_regression.py`), the r = 2 exports and the
  twelve in-release byte copies (`verify_release.py`'s inventory,
  `verification/audit_literal_polynomials.py`) and `core/data/u15_table.json`
  (`core/compiler.py`, `core/audit/independent_check.py`,
  `verify_release.py`). Restore them as in "Reconstructing the excluded
  data", or use the archive.
- **Windows replay hazard (not patched).** `core/compiler.py` (lines 231
  and 258), `core/audit/independent_check.py` (193),
  `fiber/check_fibers.py` (226), `paired/tests/check_all.py` (215–216) and
  `tamper_regression.py` write text with the platform newline. On Windows
  the rebuilt files are CRLF (`semigroup.json` 125,774 bytes instead of
  117,288), so `verify_release.py --replay` fails its byte comparison; after
  CRLF → LF they equal the delivered bytes. Section 74's "portable replay"
  and `RELEASE_README.md`'s instructions hold on POSIX systems. Several of
  these programs also **overwrite recorded outputs** in their own tree
  (`core/data/*`, `core/audit/independent-results.json`,
  `fiber/CHECKS.json`, `paired/examples/accepting-94-certificate.json` and
  `-ledger.json`); `verify_release.py` itself runs them only in temporary
  copies.
- **Overstatements in the delivered abstract**, kept verbatim with `[write
  82]` notes in Part V's opening: it states many-one r.e.-completeness before
  its qualifier (the completeness is conditional on the Neary–Woods chain;
  the local equivalence is proved), and it credits the infinite fibres to
  the generating function, whereas they follow from the stutter argument at
  the start of Section 73 and Theorem 73.1 counts the fibre of an accepted
  live input.
- **Collisions.** Section 72 names one of the two excess length-two
  collisions, `(20,109)`/`(110,20)`; the other is `(20,111)`/`(112,20)`
  (`[write 82]` note there). Both were confirmed at this
  write by enumerating all 12,996 length-two products from the shipped
  `semigroup.json` (12,994 distinct targets).
- **Re-derivations and re-printings, not cited by source 08**: Lemmas 63.1
  and 64.1 (research-programme construction), Table 4 and its erratum
  (`quadratic-orthant-certificates`), the first half of Lemma 65.1 (Sanov;
  Part I). See "Credit added at the batch-82 write".
- Section 74 counts "488,281 words of length at most eight" over five
  letters; the count includes the empty word (`Σ_{k=0}^{8} 5^k`). Harmless.
- `08-matrix-semigroup-core-loader-audit-U15_DEPENDENCY_AUDIT.md` refers to
  Reports 16 and 23 by release-directory names; they are
  `five-particle-binary-automata` Part II and `fixed-universal-polynomials`
  Part I in this collection. The inert upstream bi-tag encoder it discusses
  (`upstream_u15_builder.py.txt`) belongs to Report 23's release and is
  shipped there as
  `code/11-grill-poly-input-research-literal-upstream_u15_builder.py.txt`.
- The Neary–Woods citation of source 08 (Fundamenta Informaticae 91(1)
  (2009) 123–144, DOI 10.3233/FI-2009-0036; author PDF paginated 105–126) is
  correct as delivered.

Source 09 (batch 91):

- **Delivery names.** Part VI's Sections 87–89, Appendix M and its
  bibliography entries `cm-science`, `cm-audit`, `cm-pell` and the
  research-note entries name delivered paths (`science/evidence/polynomial-dag.json`,
  `science/sources/`, `dependencies/`, `independent_audit/`,
  `audit_replay/`, `verification/`, `article/Report55.tex`); the `[write
  91]` notes in Sections 87 and 89 and at the end of Appendix M give the
  shipped names, and the map under "Delivered names" covers every file.
  Every shipped Markdown file, manifest, receipt and program of source 09
  uses delivered paths and names unshipped files (the DAG, the copies under
  `science/sources/` and `dependencies/`, `pell-source.lean` and its
  licence, the four log copies, `pdf-rebuild-b.json`, `Report55.tex`,
  `Report55.pdf`, `README.md`); several also carry historical absolute
  paths `/workspace/shared/…` (`AUDIT.md`, `PACKING_REVIEW.md`, the
  audit manifest, the LaTeX log, `check_source.py` and
  `check_interfaces.py` as defaults, `check_manuscript_data.py` as
  constants).
- **Windows hazards (not patched).** `build_certificate.py`,
  `check_semantics.py`, `freeze_manifest.py`, `check_source.py`,
  `check_interfaces.py` and `check_manuscript_data.py` write text with the
  platform newline and overwrite files next to themselves or in their
  packet; on Windows their outputs are CRLF and equal the shipped LF files
  after conversion (the DAG is written as bytes and is identical).
  `release.py verify` refuses on NTFS; the replay adapter's byte gate fails
  on Windows. Use the routes under "Rerunning the programs".
- **Selector letter.** The source writes its selector streams `E_i`; Part
  VI writes `Λ_i` (Setting and notation). The shipped notes keep `E_i`.
- **Leading form.** Section 87 prints the degree-six homogeneous term of the
  13th POWER residual as `−w⁴g²`; the programme's review restricts the
  residual to `−w⁴g² − 2w³g²`. Both are right: `−2w³g²` has degree five.
- **"Missing arbitrary-duration packing"** (Section 78) was true at the
  source's pin and was filled the same night by the research programme by
  another route (dated `[write 91]` note there; "Relation" above). The
  source's "the repository's prior 84-operation benchmark" is still the
  current universal bound (commit `20aafb9a5`).
- **Packing review inputs.** `09-chrono-matrix-science-review-PACKING_REVIEW.md`
  lists `/workspace/shared/sandpile-repeated-target-20261004/SOURCE_NOTES.md`
  among the files it read; by its name that is the source notes of Report
  53 (`canonical-diophantine-certificates` Part XXI), but the review records
  no digest for it. The same review shows that `2^103` already suffices as
  the radix factor (its Section 3); the article keeps `2^104`.
- **Same-pipeline audits.** `AUDIT.md`, `MANUSCRIPT_AUDIT.md`,
  `PACKING_REVIEW.md` and the release QA were produced by the pipeline that
  wrote the manuscript; they call themselves independent of the author
  packet, not of the pipeline. The research programme's review
  (`a9ab9a698`) is the outside check.
- **Shared files.** Three shipped files of source 09 are also the delivered
  `science/sources/` files of
  [`signal-machine-collision-certificates`](../signal-machine-collision-certificates)
  Part X (Report 58), which does not ship them again: keep them under their
  current names.
- The research-note bibliography entries of source 09 credit "Vladimir
  Reshetnikov, ProveIt research sources" for the first note and "ProveIt
  research sources" for the rest, as delivered.
