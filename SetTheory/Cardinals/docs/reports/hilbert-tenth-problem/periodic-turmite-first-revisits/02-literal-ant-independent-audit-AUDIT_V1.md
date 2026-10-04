# Independent audit of the original frozen literal ant interface packet

Result: authenticated and fully reproducible, with one Python API robustness caveat that the construction lead is hardening in a separate revision. No physical-theorem counterexample or global geometry/compressed-program blocker was found.

## Authentication and preservation

- External ZIP: 7,105,997 bytes, SHA-256 `41081f538ca24e527cbf295626760f3339ed9dd9d171e725fb35131166d6a650`
- Manifest SHA-256: `a82fdb40349bdb3be08b7454f706232c0a7ac9d855484336abc8bb87497fcd0a`
- 92 manifest entries, plus the manifest itself: all 93 archive members match the frozen tree exactly
- ZIP CRCs pass; no duplicate names, traversal, absolute paths, symlinks or special-file entries
- Independently extracted exact files under this audit directory; the driver never ran in the frozen release
- All original file bytes, modes and nanosecond modification times, all original directory modes and modification times, and external ZIP bytes/mode/modification time were preserved
- This preservation claim does not apply to temporary worktree generation metadata; those files are deliberately regenerated

## Executable and source scope

Read README, driver, complete global proof, complete geometry review, complete compressed-program analysis and relevant implementation paths. The packet has 34 Python files. Static import/dynamic-loader inspection found standard-library imports plus own packet modules. Dynamic `exec` in the compressed-program audit executes the authenticated own `ca/physical_program.py`, not an external schedule. Dynamic importlib loaders resolve own geometry/build modules. Only the driver launches subprocesses, all through the current Python interpreter and authenticated own entry-point paths in its temporary tree, with cwd `/`. No network library or external command execution path was found.

The seven primitive maps and fixed U15 table are pinned numerical data. No upstream code or saved arithmetic schedule was executed. Full third-party articles, source archives or rendered article pages are absent. The qualitative prior result and the unimplemented arbitrary-program-to-U15 compiler dependency remain expressly separated from the literal implementation.

## Replay

- Normal driver: exit 0, 28 own commands passed
- Scientific regeneration: all 39 outputs byte-identical
- Replay receipt itself also byte-identical to original, SHA-256 `09d280310a3287d02edd195d629c243691680f0926eb864a8bea9d20f473c1be`
- All 27 explicitly guarded driver/component entry points rejected `-O`
- Exactly two documented unguarded standalone scripts remained unsupported and unexecuted under optimization: `copy/translate_anchor.py`, `copy/program_audit/verify_program_index_bounds.py`
- Additional driver and loader tests reject both `-OO` and `PYTHONOPTIMIZE=1/2`
- All 34 Python source files stayed byte-identical

## Independent interface checks

Independently reconstructed 85 complete changed-cell maps from the authenticated anchor and the declared arithmetic placement formula. Covered nearest-head-first reversal, head A0, endpoint marker, exact support count and bounds, period, fixed head and accepting clauses. Zero-only word lengths include 0, 1, 2, 3, 4, 7, 16 and 31. Eighteen invalid-bit calls and four caller-supplied hardware/anchor/program/observer parameter attempts were rejected. Seventy-two extra signed/large-coordinate periodicity probes passed. The observer row/column and both accepting clauses were independently recalculated, and local DUP accepting-event counts and absence during later reads were checked.

The complete replay separately rechecked all 2^24 Boolean assignments and observer transport, finite local histories, 263,525-cell geometry review, and exact arithmetic grammar certificates. The global proof uses the finite ownership/alias facts, long-channel inequalities and controller induction rather than claiming finite trajectory tests prove the infinite theorem. No dense tile or full 601,547,591-row expansion was needed or attempted.

## Reproduced API caveat

The original `compile_input(left,right)` has the correct fixed two-argument signature, but returns its cached anchor's mutable `fixed_initial_head` list directly. In one Python process:

1. Call `p = compile_input([], [])`
2. Set `p['fixed_initial_head'][0] = 123`
3. Call `q = compile_input([], [])`
4. `q['fixed_initial_head']` is now `[123, 75, 1]`

This changes only in-memory returned/cached metadata, not the packaged board or any file. CLI/fresh-process usage and ordinary non-mutating calls pass. It is not evidence against the physical theorem, but prevents claiming that returned initialization objects are isolated from future calls. The lead was notified immediately and is preparing a separate hardened release; the original remains untouched.

## Evidence

`authentication.json`, `original_baseline.json`, `source_scope_inventory.json`, `replay.stdout.log`, `replay.stderr.log`, `replay.exitcode`, `replay_verification.json`, `independent_interface_checks.py`, `independent_interface_checks.json`, `extra_optimization_checks.json`.
