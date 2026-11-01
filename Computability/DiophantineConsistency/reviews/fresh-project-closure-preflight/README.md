# AQ29 source snapshot preflight, not a proof replay

`manifest.json` records the 1,210-module source-declared project DAG for `DiophantineConsistency.IPRAAQ29NativeChecks`. It hashes each source snapshot and records 106 distinct external module names. `source-audit.json` records that all 1,210 workspace sources were tracked and matched both the snapshot and audited Git HEAD at the observation. The corresponding temporary snapshot was `/tmp/ipra-aq29-fresh-source-closure-v2`.

This is a point-in-time source audit. It does not assert that the files remain current after later commits or edits, that the line-based import parser is the Lean parser, or that Lean compilation, package-transitive ancestry, dynamic imports, or an independent replay has succeeded.
