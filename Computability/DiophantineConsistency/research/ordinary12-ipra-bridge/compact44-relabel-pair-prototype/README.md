# Planned coherent paired compact table correspondence replay

This is a **prelaunch plan**, not a completed paired replay. The 58-module manifest covers a fresh compile of the pinned compact 943-row table over each independently audited successor sibling, the explicit color/index arrays, 35 bounded row cuts and joins, the assembled 942-row equality, the two color permutations, 15 bounded inverse-index cuts and their index-permutation assembly, and the final conjunction. Each source is bound to a specific committed anchor and SHA-256. The external array and inverse checkers bind the displayed arrays to the separately audited finite permutation receipt; the JSON-to-Lean table binding remains an external source-data check.

`replay.py` is prepared to rerun the independently audited successor, 943-table and finite-relabeling checks; verify all committed source anchors and source hashes; copy immutable source snapshots; compile the topologically ordered modules over each successor sibling; check each direct import, source/object/companion guard, exact named axiom report and sibling match; and retain actual per-child and wrapper evidence. It verifies a supplied full `--expected-head` and tracked-worktree cleanliness before and after its audit and each child. It does not prevent between-check filesystem races or prove package-transitive and dynamic-import completeness. The compiler uses the inherited sampled RSS/disk monitor, not a hard quota; `lean --deps` has only a leader timeout, without sampled resource or descendant-group enforcement.

The full replay has **not** been launched. Before any real run, obtain an independent exact-byte prelaunch review, establish an externally stable HEAD and exclusive Lean slot, confirm at least 4 GiB free on `/tmp`, and start Python and its audit children with a trusted clean native-loader environment. The no-Lean preflight is also pending. A representative command, substituting the actual 40-character stable HEAD, is:

```
env -u LD_PRELOAD -u LD_LIBRARY_PATH -u LD_AUDIT python3 -I -S replay.py --preflight --expected-head <HEAD> --output /tmp/ipra-compact-relabel-pair-check
```

The corresponding real command omits `--preflight` and uses a fresh direct `/tmp/ipra-compact-relabel-pair-*` output. Successful completion would establish only the finite Lean table equality and supplied color/index permutation facts over the checked provider. It would not establish existence of matching left neighbors in arbitrary model tilings, compact44 checker calibration, the 12-variable iPRA bridge, or global minimality.
