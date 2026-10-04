# Report60 portable replay release validation

Status: **PASS**, with no outstanding adapter-review blocker.

The final tool authenticates nine explicit input trees containing 137 files.
It runs the unchanged independent physical, geometry and arithmetic checkers;
the quadratic science/audit companion is authenticated and preserved inertly.
Exactly seven stable output-byte comparisons are required per full replay.

## Final source bindings

- Adapter SHA256: `7a537eeaf0e26d3c720527343f2a0cd1321d3d3486046ee947ef3b5d76b9b71e`
- Selftest SHA256: `7fd51425d3f2f23f68d256d527adab669d2d0f1fa76223b860e6770d5079ece2`
- Input pins SHA256: `c9794e791685c5a03e87d15a2b3bb0727847372b38fb067b3c8f7d64da1a3818`

## Verified results

- Complete normal replay and complete read-only, differently named relocated
  Python `-O` replay both pass all seven byte comparisons
- The 25-case final selftest passes, including corruption/link/path/fresh-output
  negatives, actual blocked historical reads, protected writes, and comparator
  rejection of nonidentical output
- A separate reviewer ran 22 independent synthetic probes and a complete
  Python `-OO` replay against the final exact adapter; all passed
- Original scientific sources still match their frozen audit snapshots in
  bytes, modes and nanosecond mtimes; all three independent checker hashes remain
  unchanged
- The writer's actual release science/audit/dependency subtrees were separately
  preflight-authenticated against the final nine-tree pin set

See `validation/SUMMARY.json`, the complete before/after inventories and guard
logs under `validation/`, and `independent-review/REVIEW.md`. The latter states
exact limits: selected trees are authenticated, the outer release is preserved,
Python/SymPy/mpmath are trusted runtime inputs, and the I/O hook supplements
reviewed pinned code rather than sandboxing hostile Python.

The executable files were tested before these inert validation/review payloads
were copied into the final tool directory. Their final hashes above are the
exact tested hashes. These additions contain evidence only and do not alter any
executable checker, adapter, selftest, scientific packet, or expected output.

`REPLAY_PACKAGE_MANIFEST.json` authenticates every file in this tool package,
excluding itself. Copy the entire directory verbatim into
`tools/portable-replay`; use the explicit command documented in `README.md`.
