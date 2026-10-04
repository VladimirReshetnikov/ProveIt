# Independent audit: hardened literal ant interface release v2

## Finding

PASS. The external v2 archive is authenticated and safely extracted; the full normal replay, exact-output comparisons, optimization refusals and independent interface checks pass. The v1 Python returned-head alias is fixed. No remaining blocker was found in the requested proof/receipt/code consistency or replay scope.

This is an independent review and computational replay of the stated mathematical construction, not a formal proof-assistant certification. The published arbitrary-program-to-U15-pair universality dependency remains separate and is not supplied by this audit.

## Canonical artifact identity

- ZIP: `/workspace/shared/literal-turmite-interface-release-20261003-v2.zip`
- ZIP bytes: 7,115,852
- ZIP SHA-256: `70a2a87ddb1ab018ec8c795dad56d053f66855a9b47ab7f3a9b64cf1164b852f`
- Manifest SHA-256: `e31de0a0a06b917c60071d500b72dd7891cd74bea103e449685c0041c9b0f615`
- Loader SHA-256: `3bf032f5dbf00b2622f4010e702ab9951ad99a3f38f86b7892d4375bc7e8cb58`
- Generator SHA-256: `20d3cf2c57226910dff679b05a2209f7f6513d62bce824e448e3c94b7dfa5f67`
- Global proof SHA-256: `a8b4a65ad97a06f3c854a9d133e67dca240d6212749f42ed6c4a92b30318483b`
- Independently regenerated replay receipt SHA-256: `5c5a91531cda7807fb237e95610ddcc6da5d1dfad124ebb43c65e8061baab065`

All 92 manifest entries match. The archive has exactly those files plus MANIFEST.json, under a single top-level directory. All 93 files match the release's corresponding files byte-for-byte. CRC checks pass; there are no duplicate members, traversal/absolute paths, symlinks, special files or encrypted entries. Uncompressed size is 157,297,515 bytes.

The supplied on-disk v2 root has two pre-existing Python cache files excluded from the ZIP and manifest: generator and physical_program bytecode caches. They were recorded but never executed. The clean authenticated ZIP is the canonical artifact. This is a packaging distinction, not an extra executable in the delivered archive.

## What was inspected

For v1, read README, replay driver, complete global proof, complete independent geometry review and complete compressed-program analysis. Inspected all 34 Python import/dynamic-execution paths and the relevant generator, loader, observer, physical grammar and finite replay implementations. Own dynamic imports resolve only packaged modules; the grammar audit's dynamic exec executes its authenticated own physical_program source. Only the driver invokes subprocesses, using the current interpreter, own paths and cwd `/`. No network-library or upstream executable path was found.

Compared v2 against v1 exactly. Only six files differ: loader, loader receipt, replay receipt, README, gate and manifest. The complete loader diff was inspected. No physical template, Boolean circuit, table, primitive map, generator, global proof, geometry review or fixed initialization changed. The v2 executable-path review therefore reduces to the fully inspected loader change plus the identical v1 executable set.

The finite U15 table and primitive maps remain numerical data. No upstream code, saved arithmetic schedule, external source archive, network operation, dense board or complete 601,547,591-row expansion was executed. Full third-party articles/source archives/rendered article pages are absent from the packet.

## Full independent replay

Executed the driver only in this audit's separately extracted tree. The driver then created its own temporary worktree and intentionally regenerated there.

- Normal exit status: 0, empty stderr
- Own replay commands: 28, all successful
- Scientific outputs: 39, all byte-exact against authenticated files
- Replay receipt itself: byte-exact
- Explicit optimized-mode guards: 27, all reject `-O`
- Unsupported standalone optimized entries: exactly `copy/translate_anchor.py` and `copy/program_audit/verify_program_index_bounds.py`, not executed under optimization
- Additional driver/loader refusal tests: `-OO`, `PYTHONOPTIMIZE=1` and `PYTHONOPTIMIZE=2`, all rejected before execution
- Source identity: all 34 Python files unchanged

The replay rechecks all 2^24 Boolean assignments, observer transport/polarity, finite local histories, finite geometry review and exact compressed arithmetic grammar certificates. Global infinite-run/two-visit correctness is attributed to the accompanying ownership/alias/controller induction and long-channel inequalities, not to bounded trajectories alone. No dense expansion was demanded or substituted for those arguments.

## Additional independent interface tests

Independently reconstructed 85 complete finite changed-cell maps using the authenticated anchor and a separately written arithmetic placement formula. Checked nearest-head-first reversal, A0 head, marker fields, exact count `2812 + 4*(popcount(left)+popcount(right))`, support bounds, fixed start, periods and accepting clauses. Zero-only endpoint lengths include 0, 1, 2, 3, 4, 7, 16 and 31. The endpoint marker remains length-dependent even when popcount is zero.

Eighteen invalid-bit calls reject booleans, floats, negative/out-of-range values, strings and None. Four attempts to pass anchor, hardware, program or observer parameters reject with TypeError; the public compiler signature remains exactly `(left, right)`.

Seventy-two extra signed/large-coordinate periodicity probes pass. Independently recalculated observer row 601,515,562, active column 910 and both residue/heading clauses; local DUP trace checks confirm exactly one accepting departure iff its left bit is 1 and none in later output reads.

The independent mutation test compares two complete results, verifies disjoint mutable-container identities and caller-list identities, mutates caller inputs, then destructively replaces all 2,838 nested mutable containers of one returned result. The other result and a later fresh result remain canonically byte-equivalent. The minimal old reproducer that changed returned `fixed_initial_head[0]` to 123 no longer affects later calls. The packaged selfcheck additionally tests separation from private cached values on three cases.

## Preservation and scope

Rechecked the original frozen v1 and v2 trees, including the v2 pre-existing excluded caches, against snapshots taken before this audit's execution. File bytes, modes and nanosecond modification times are unchanged; directory modes and modification times are unchanged. Both external ZIPs also retain bytes, modes and modification times. Reading may affect access times; no access-time preservation is claimed. Temporary regeneration metadata is intentionally mutable and is not claimed unchanged.

No scientific interface value changed from v1. The only fixed issue was same-process mutability of returned metadata, not a counterexample to the physical theorem. The ant continues after simulated halt, only the second observation clause is reachable on valid primary-loaded runs, and arbitrary-program compilation, finite-blank-background universality, fixed-site return and 174-operation arithmetic composition remain outside the established scope.

## Reproduction evidence

- `authentication.json` and `authenticate_extract.py`
- `original_baseline.json`
- `v1_v2_changed_paths.json`
- `replay.stdout.log`, `replay.stderr.log`, `replay.exitcode`
- `independent_interface_checks.py`, `independent_interface_checks.json`
- `verify_replay_and_preservation.py`, `replay_verification.json`
- Earlier v1 review: `/workspace/shared/literal-interface-independent-audit-20261003/AUDIT_V1.md`
