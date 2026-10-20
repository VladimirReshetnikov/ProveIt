# Verification layers

- `macro_diamonds.json` and `joint_*.json` are freshly generated positive-block
  all-tape proofs for the three actual K220 alternatives. The macro receipt's
  K220 label is produced by the release checker, not edited after the fact.
- `variant_only_smoke.json` is a weaker release-author smoke run, deliberately
  skipping inherited calibration replay. It does not certify that chain.
- `baseline_full_replay.json`, `baseline_full_runtime.json`, and
  `baseline_full_runtime_audit.json` are unchanged historical receipts from the
  separately completed fresh K220 full replay on 2026-10-20. The independent
  runtime receipt has the same mathematical data as the retained upstream
  runtime receipt but a different measured execution time and hence hash.
- `independent_core_audit.py` imports no packet checker and regenerates parsing,
  state census, BFS relabeling, universal finite-window joins, and exact complete
  blank startup directly from the literal tables. Its receipt is separate from
  the package author's proofs.
- `independent_default_replay.json` records an independent offline copy replay
  of the default driver against the provisional 24-file core snapshot, whose
  exact manifest is `default_snapshot_manifest.json`. Documentation, report,
  exploratory material, and independent receipts were added afterward; all
  portable/machine/vendor files remain byte-identical. Final sealing audits
  check that relationship and replay the extracted alternatives.
  Default mode reconstructs/calibrates the retained chain
  and audits its stored baseline runtime; it freshly proves the variant joins.

Neither a finite startup nor 6,167 finite tests proves consistency calibration.
The 6,167 baseline cases cited in the certified chain are symbolic unbounded
primitive-interface proofs, with separate source and logical calibration.
No layer claims a new proof-assistant kernel endpoint for the variant bytes.
