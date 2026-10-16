# Batch 149, source 01: engineering review

Reviewed on a fresh scratch copy at `/tmp/zfc-review149-source01-engineering-w5on4q5k/package`. Original input was `/tmp/zfc-review149-root-tf20tx9y/01`; pinned sources were copied from its sibling `pinned`. The old grammar helper was recovered from `docs/incoming/zfc_small_machines_20261016.zip` at the report's exact ProveIt pin `96836f9eea3540e96322c3d28c7127a582aae223`. Upstream data/backend pin: `297ab8df7e5de329605c3875b4934643b371a5e3`.

No repository files or delivered sources were edited. No Lean or Coq build was run. Release manifests/checksum enforcement were skipped by an in-memory AST loader; semantic assertions, state-count assertions, grammar checks, and certificate checks remained enabled. File identities output by existing programs are identifiers, not release-manifest verification. Root owns both PDFs; fibers separately owns the full mathematical/kernel/template review, including the 100,000-case base-three/base-four actual-emitter audits and 24-permutation test, which I did not duplicate.

## Fixed compiler outputs: PASS

`compiler/compiler_controls.py` regenerated **all 11 distributed control artifacts byte-for-byte**, including `compiler-controls.json`, both named tables, both numbered tables, both DAGs/maps, the original reference DAG, and the original RM certificate. See `fixed-replay-comparison.json` and `fixed-replay.log`.

* Original full source: attributed seed 341 / exponent 4; 185 macro tokens, 26 grammar productions, residual length 77, **207 decision + 62 framework = 269 working states**, 538 total rows, blank zero, start 0, halt 269 excluded from count. This is reproduced prior work, preserving the full original logical/equality/theory frontend.
* PSC+IR: seed 46 / exponent 4; 192 closed primitive tokens, 28 productions, residual length 90, **221 + 62 = 283**, 566 total rows, start 0, halt 283. Keeps GEN and all eight original logical/equality rows in their original order and original base-four encoding `Imp0 / Rel1 / All2 / Eq3`. Its changed theory word is fresh-offset PSC (`k=c+2`), then `All(1, Rel(1,1)->F)`, then gated membership/equality vacuity and the original cleanup tail. There is no primitive-Bottom retagging.

Numeric table identities emitted by the replay are respectively `b40b90fdcf3a09475d3a2314dc3707bcf51a6302a3fdbba3c6afcde6ed1109de` and `207a9dc63dd31d4154c40147c7366ee9659ac1253f89cd616c54918d20d3a5e7`.

The named sources have respectively 537 and 565 rows, with sole missing row `1.inc/read1`. Normalization supplies write 1, move R, terminal halt. This preserves tape contents and halting under undefined-row halting, while adding a final move; it does not preserve the final head position or establish a complete binary interpreter theorem. The generator charges initialization and re-extracts every compiled decision edge.

## Independent certificate and negative controls: PASS

The included independent string/integer path engine, importing neither the generator nor binary compiler, verifies **4,533 related operation sites** between the actual original **219-node** reference and the **207-node** compressed source: 2,601 increments, 1,931 decrement tests, one halt, with both decrement successors checked. Both unfold to 6,460 sites; maximum contracted control chain is four. This certificate is against the original full source, unlike source 02's certificate against its newly emitted conjunction layout.

The delivered swapped-branch self-test passes. Six further mutations were rejected: wrong initial index, missing record, duplicate record, changed operation/register, changed zero successor, and changed positive successor. See `independent-certificate.json`, `certificate-mutations.json`, and the two review scripts/logs.

This is finite executable RM evidence and an ordinary operation-bisimulation argument. It does not instantiate the finite certificate in Lean, prove DAG/control semantics in Lean, or prove binary simulation/theory calibration. No analogous original-to-PSC equivalence certificate is claimed or expected: PSC changes the theory word.

## Conservative table reduction audits: PASS, no reduction found

Both complete tables parsed under the standard deterministic binary, two-way, blank-zero convention. Every working state is graph reachable. Exact-step bisimulation has singleton classes (12 refinement rounds for 269; 11 for 283). The radius-4 local-window / 64-step search finds no safe state merge. Start reuse is unavailable because the start has a reachable incoming edge. The shared auditor's 11 self-tests pass. See `original-269-audit.json` and `psc-ir-283-audit.json`.

These checks support the stated table counts and find no reduction in these conservative families. They give no global state lower bound.

## Search reproduction and historical-driver limitation

I reconstructed the precisely described **1,024-member PSC family** (seeds 0..255, exponents 1,2,4,8) using the delivered `strict_repair` and `transform`. The full 192-token word agrees with the saved word; every token is closed under the helper-bound check, and every compressed grammar expands exactly to that word. The winning record and **every saved state-histogram bin reproduce exactly**: seed 46, exponent 4, 283 states, 221 decision nodes, 28 productions, residual 90, and exactly five 283-state winners. Every one of the 1,024 tables was actually compiled, every decision edge re-extracted, and its state/framework count checked. Framework-state distribution: 61 in 5 trials, 62 in 479, 63 in 470, 64 in 66, and 65 in 4. Python3.12 and3.13 agree trial-for-trial, including actual compiled costs. See `psc-search-replay.json` and the actual-backend replay logs.

**Correction to the first version of this review:** I initially estimated each trial as decision nodes plus 62 states. Wade's `TMBuilder.generate` actually uses a variable dispatcher whose cost is controlled by maximum consecutive left-child depth. With the unchanged register/control leaves, framework cost is 55 fixed states plus that dispatcher depth. Correcting this review calculation resolves the apparent histogram mismatch completely. It was a review error, not a defect in the delivered search record. The superseded incorrect calculation is retained as `psc-search-replay-incorrect-fixed62.json`; its claimed mismatch is withdrawn. The fixed 269/283 tables and their prior checks were never affected.

The other searches remain **historical summary evidence, not replayed suites**: the 2,048-trial safe rho8 sweep, 10,240-trial helper-boundary sweep, and 20,000 block-rotation sweep appear only in `compiler/compiler-audit.txt:82-94` and `audit-summary.json`. Their drivers are absent; the five boundaries, full parameter schedules, rotation proposal rule and random seed are not all specified. Their negative results are correctly not stated as lower bounds. The independently regenerated 269 control does establish the reported best fixed result without relying on these missing search drivers.

## Intake assessment and current-tree comparison

No engineering defect invalidates the two delivered fixed controls or the original RM certificate. Exact winners, the complete 1,024-member PSC histogram, and the certificate are reproduced. Preserve only the historical-driver limitation in reconciliation; the other optional historical sweeps are not all independently replayable. The earlier claimed PSC histogram mismatch has been explicitly retracted above.

The 269 control duplicates the previously supplied original-source Re-Pair result; current repository work also reproduces 269 while correcting overlap counting on the unchanged full word. Source 02 in the same batch obtains 268 by an additional propositional conjunction-layout rewrite, not by exactly the same original word. Source 01's PSC+IR 283 is a separate full-logical-engine measurement, not a bound for the new binder-certificate checker. Its proposed complete binder checker has no compiled state count.

The pinned report predates the current finite-sort obstruction to the reduced C/G machines. Thus its statement that 248 has an unresolved logical-calibration gap is historical; it does not supersede the current retirement of that frontend. Its stronger identity-quantifier PSC obstruction applies to its explicitly defined PSC-only lane, rather than to ordinary one-sorted PSC. This engineering review establishes neither an emitted-code PSC calibration nor any new internal `ZFC proves NH(M) iff Con(ZFC)` endpoint.

## Reproduction/evidence

All commands and compact joined results are in `engineering-review.json`. Run from this scratch directory:

```
uv run --no-project python run_without_hash_enforcement.py package/compiler/compiler_controls.py --repo pinned --prior-grammar prior_grammar.py --output fixed-replay
uv run --no-project python run_without_hash_enforcement.py package/compiler/recheck_included_certificate.py --self-test --output independent-certificate.json
uv run --no-project python review_certificate_mutations.py
uv run --no-project python review_psc_search.py
uv run --python 3.12 --no-project python review_psc_search.py
```

The last two commands reconstruct the optional PSC sweep with complete backend costs, preserving exact-word/cost assertions and matching the delivered histogram. The incorrect fixed-62 review calculation is separately preserved and withdrawn. The table-audit commands are recorded verbatim in the joined evidence. No release checksums, network fetch, theorem-prover build, or PDF build were needed for this engineering review.
