# WIP: native queue streams and research continuation

This directory is an explicitly scoped research handoff on
`codex/diophantine-native-stream-wip`. Start with
[CONTINUATION_PROMPT.md](CONTINUATION_PROMPT.md). No local-machine files are
needed to continue in an independent clone.

**The established complete universal bound remains 76.** The native-stream
component costs six operations with external bounds, or eight with a paid
joint bound; finite-controller arithmetic and power geometry remain unpaid.
The proposed five-operation loader has no completed proof or implementation.

## Preserved and runnable work

The component proof and source live in their normal project locations:
- [Native-stream proof](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md).
- [Native-stream checker](../../verification/explore_native_stream_raw_queue.py)
  and [receipt](../../verification/explore_native_stream_raw_queue.json).

The author gates passed. An independent final proof/source/receipt review
completed during this handoff with no findings, including the signed-code
capacity argument. Fresh exact receipt replay passed: 31,980 arbitrary scalar
tuples, 131,160 forward FIFO runs, and 463 paired-controller histories covering
43,665 transitions. This is a full review of the **conditional component**,
not a proof of an arithmetic controller or of a smaller universal bound.

This directory's four independent audit scripts preserve earlier machine and
stream evidence. Their import paths have been adapted to the migrated layout.
The bridge-rewrite proof/checker/receipt records no saving: schedules76,76,77,77.
The checker now compares its saved receipt by default; `--write` regenerates it.
[native_ternary_controller_encoding.md](native_ternary_controller_encoding.md)
preserves the unfinished controller analysis.

Run from the repository root with Python3.10 or later. The handoff dependency
is pinned in `requirements.txt`:

```sh
python3 -m pip install -r Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/requirements.txt
python3 Computability/HilbertTenthProblem/Papers/verification/explore_native_stream_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_queue_base_three_streams.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_delayed_blank_loader.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_constant_length_one_blank.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_finite_state_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_complete76_bridge_rewrites.py
```

These commands use repository-relative paths; they do not require Windows,
Lean, TeX, an old checkout or credentials for the retired repository. A Windows
handoff replay is recorded in `VALIDATION.json`; no Linux execution is claimed.
The full historical checker environment may require additional dependencies.

## Archived earlier untracked research

`legacy-untracked/current/` preserves the remaining formerly untracked
research notes, scripts and receipts without promoting their conclusions.
`legacy-untracked/MANIFEST.json` lists original relative paths, archive paths,
sizes and canonical-LF SHA256 hashes. This archive excludes the three native
stream files installed above and includes the other untracked files beneath
the old research `current/` directory. It is a selective research preservation,
not a backup of build products or the entire old `tmp/` directory.

These are historical WIP artifacts with different scopes, abandoned candidates
and negative results. Counts in them are not current complete bounds. Their
old relative links or source-loading assumptions may need adaptation before
execution; the archive has not been run as a suite. Use maintained project
sources for dependencies and do not regenerate a receipt merely to conceal a
mismatch. No newly discovered complete bound below76 was found in the handoff
inventory.

The original files remain intact in the originating checkout. The remote
continuation depends only on this branch and the migrated tracked dependencies.
