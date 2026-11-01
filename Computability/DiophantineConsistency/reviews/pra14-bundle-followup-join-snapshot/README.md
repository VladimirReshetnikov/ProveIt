# Decoder-bundle follow-up 14-equation/PRA join: frozen input

The 73 suffix sources are unchanged from `reviews/pra14-post-merge-join-snapshot/`; this packet references those exact frozen source paths and hashes without copying them again. The frozen parent input and graph-only audits are in `reviews/pra14-bundle-followup-snapshot/`. The guarded source-directed driver is the prior post-merge join driver and recompiles all 73 suffix modules from those frozen sources against the decoder-bundle-refresh parent, once that parent passes. Direct external objects and parent outputs are guarded; external transitive and parent original-reuse ancestry remain inherited.

The negative test `negative-parent-precondition-state.json` used the still-running previous parent and failed before compilation with `parent is not PASS`. It tests only that precondition. After the separate decoder-bundle-refresh parent has completed PASS, run the authenticated launcher with its resulting provider path:

```sh
python3 Computability/DiophantineConsistency/reviews/pra14-bundle-followup-join-snapshot/run.py --parent /tmp/REPLACE_WITH_PASSED_BUNDLE_REFRESH_PROVIDER
```

Author and independent builds and a source-byte comparison to the then-current workspace remain required. Any eventual result is the classical candidate-PRA theorem; the native iPRA objective is separate.
