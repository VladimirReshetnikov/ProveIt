# Reproduce batch 162

Placement `a1dc32a6fd` preserves 155 ancillary files from 169 delivered files.
The [placement map](data/intake-162-placement.json) includes the 14 archive-only
manuscripts, constituent TeX/PDFs, printed tables and delivery READMEs. Recover
the original nested packages into a new directory outside the checkout:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_162.py \
  --repo "$PWD" --output /tmp/zfc-batch162-recovered
```

The output roots are `/tmp/zfc-batch162-recovered/62-audit247/zfc-prefix247`
and `/tmp/zfc-batch162-recovered/63-context246/zfc-context246`. Optional
`--source 62` or `--source 63` restores just that package. The helper uses
committed arrival archives, compares placed bytes directly with original
payloads, restores original nested names and creates a recovery record.
The [validated recovery](data/intake-162-recovery.json) restored all 169 files
and checked all 155 placed byte pairs. Recovery runs no verifiers or compiler.
Delivered `.log` files were placed as `.txt`; their original extensions are
restored here. Checksum manifests are preserved without interpretation.

| Source | Arrival | Committed archive |
| --- | --- | --- |
| 62 | `f94653113962b4c7d446c7d0cbd3b03a69d534da` | `docs/incoming/zfc-prefix247.zip` |
| 63 | `8cdc55ff9281b0aaba49bf74b0b225d57f12b893` | `docs/incoming/zfc-context246-20261018.zip` |

Run the suites in further writable copies because they refresh result files.
The following paths must be new. All commands use Python's standard library,
with assertions enabled and `PYTHONOPTIMIZE` unset. There is no required
compiler, external package, network request or checkout dependency beyond
the initial archive recovery. Root bounded each main suite by 300 seconds;
the recorded successful durations are observations, not fixed runtime limits.

## Source 62: seven checks, with retained fresh outputs

```sh
cp -a /tmp/zfc-batch162-recovered/62-audit247/zfc-prefix247 /tmp/zfc-source62-rerun
cd /tmp/zfc-source62-rerun
env -u PYTHONOPTIMIZE python3 -B code/verify.py --in-place
```

The `--in-place` flag is for this writable copy. It keeps fresh JSONs and logs
under `results/`. Without the flag, the driver copies the package into a
temporary directory, performs the same checks and deletes the fresh results
on return. No delivered checker was patched during intake.

The [outer replay record](data/intake-162-source62-replay.json) and
[fresh summary](data/intake-162-source62-fresh-verification.json) record all
seven successful stages in 4.840 seconds:

1. Exact reconstruction, both numberings, printed table and full Coq-to-Lean tree comparison.
2. Universal block/list and register-macro induction templates.
3. All 8,391 guarded symbolic instruction cases.
4. Independent selector premises and 225 finite full-tape marking cases.
5. Canonical sparse blank bootstrap.
6. Independently parsed old-label dense bootstrap and ordinary exact bisimulation census.
7. 8,391 finite literal instruction cases, totaling 3,647,370 transitions.

The canonical machine SHA256 is
`58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`;
its old-label SHA256 is
`0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`.
It is exactly source 61's 247-state machine. Both startup implementations
reach the same whole-tape frame after 741,241 moves: head −5, marker −6,
header 245, gap 250, logical primaries `[3,0,0,0,3,0,0,0,0]`, 235 value-one
spares and 487 one-cells.

The [source-only review](intake-162-source-62.md) and
[root replay supplement](data/intake-162-source62-review-replay-supplement.json)
separate mathematical review from actual execution and record code identity.
The optional bootstrap-search results, PDF review/build metadata, logical
review and delivery proof-review text were inherited; they were not regenerated
by these seven commands. Source 61's larger instruction regressions, separate
arithmetic regressions and full-PC audit remain separate prior evidence.
The optional C++ search is not required or replayed. Its look-ahead discrepancy
can admit distance 100,001; it does not affect the exact gap-250 startup.

## Source 63: nine primary checks

```sh
cp -a /tmp/zfc-batch162-recovered/63-context246/zfc-context246 /tmp/zfc-source63-rerun
cd /tmp/zfc-source63-rerun
env -u PYTHONOPTIMIZE python3 -B code/verify_all.py
```

The main driver refreshes `results/verification-summary.json` and the
functional result files. It does not call the separate bulk-manifest script
`code/check_hashes.py`; intake did not run that script. Exact table/source
binding checks in the mathematical verifiers remain enabled.

The [outer replay record](data/intake-162-source63-replay.json) and
[fresh summary](data/intake-162-source63-fresh-verification-summary.json)
record all nine stages passing in 11.832 seconds:

1. Rebuild the 246 table from the pinned predecessor and check delivery bytes.
2. Check the contextual fold equations and excluded state/read pairs.
3. Compare the printed transition table.
4. Check four block, three register and nine selector induction templates.
5. Parse the full source and verify all 8,391 full-PC guarded cases, plus 342 oracle guards.
6. Replay the exact blank startup in both numberings and compare complete tape support.
7. Run 33,564 finite literal instruction cases, totaling 14,197,744 transitions.
8. Run 16,200 finite exact-time arithmetic cases, totaling 8,359,100 transitions.
9. Run 3,600 finite register-box regressions.

The [independent main-replay review](data/intake-162-source63-review-replay-supplement.json)
records unchanged code/inputs and compares substantive fresh results with the
delivery. Contextual folds, macro inductions and the full affine-source review
are identical; bootstrap and finite-regression JSONs differ only in timing
fields. The aggregate summary includes Python, command and runtime metadata.
The full-PC audit shares the imported affine engine; its separate target
construction does not constitute an independent second binary semantics.

## Source 63: two additional actual replays

These were run separately after the nine-stage suite, from another writable
copy. They can also be run from `/tmp/zfc-source63-rerun`:

```sh
env -u PYTHONOPTIMIZE python3 -B reviews/audit246.py reviews/prior250
env -u PYTHONOPTIMIZE python3 -B code/independent_rebuild.py \
  --baseline sources/prefix250_old.tm --output /tmp/zfc-source63-independent-rebuild
```

Use a new output directory for the standalone reconstruction. The first
command rewrites `reviews/audit246-results.json`; its bundled `prior250`
subset supplies the exact inherited modules and inputs. Their standalone
entry points belong to a larger historical package and are not required.
The second command writes `zfc_fold246_old.tm`, `zfc_fold246.tm`,
`renumbering-and-table-audit.json` and `independent-bootstrap-audit.json`
under the chosen output directory.

The [extra replay record](data/intake-162-source63-extra-replay.json) records
both actual PASS results, in 3.533 and 0.204 seconds. The bundled audit freshly
rechecks the four block, three macro and nine selector inductions, all 8,391
guarded cases from a complete source parse, and sparse/dense whole-tape
startup. Its induction engine is inherited, not newly independent. The
standalone reconstruction independently verifies the exact table, all 494
restricted quotient pairs with six exclusions, and its own finite startup.

The final canonical table SHA256 is
`89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`;
its old-label identity is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
It has 246 working states, 492 rows, canonical start 0/old 95, dispatcher
88/old 96 and separate halt 246/old 254. The exact 410,735-step startup has
head −5, marker −6, header 176, gap 181, logical primaries
`[3,0,0,0,3,0,0,0,0]`, 167 value-one spares and 351 one-cells; every other
cell is zero. Its own initializer is required because the restricted
quotient excludes the old blank start `(97,0)`.

The source review and its first replay supplement predate these extra runs;
their original source-only/not-yet-executed statements remain unchanged.
The separate fresh extra-run record supplies the later results. Files named
`results/independent-rebuild.json`, `results/independent-bootstrap.json`,
`results/independent-theory-audit.json`, `results/source-identity.json` and
PDF quality/build records in the delivered package were not refreshed by
the main suite. Fresh standalone reconstruction outputs live under the
chosen external directory, rather than silently replacing those records.

The delivered independent-fold TeX note refers to absent `build246.py` at
line 213. The existing primary command is `code/check_bootstrap.py`, and
the additional replay is `reviews/audit246.py` as above. No delivered file
was changed to repair that historical reference. The optional C++ initializer
search was not compiled or rerun; no failed search is a lower bound.

These commands supply finite endpoints and reviewed symbolic certificates.
They do not rebuild the inherited Lean dependency closure, produce a new
exact 247/246 kernel theorem, prove Con(ZFC) or unconditional nonhalting,
or supply the user's equivalence internal to PA.

The complete regenerated-output comparisons are retained for
[source 62](data/intake-162-source62-replay-comparison.json) and
[source 63](data/intake-162-source63-replay-comparison.json). The later
[independent extra-run review](data/intake-162-source63-review-extra-replay-supplement.json)
confirms the bundled audit matches delivery and both independently rebuilt
tables match the candidate exactly. All fresh JSONs and captured stdout are
retained under the corresponding `data/intake-162-source62-fresh-` and
`data/intake-162-source63-fresh-` prefixes.
