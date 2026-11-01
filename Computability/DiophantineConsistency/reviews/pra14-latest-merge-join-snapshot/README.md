# Latest-merge 14-equation/PRA join: fixed build input

This is a prepared 74-module source-directed rebuild, not a proof result. The suffix adds `PRARewritingWitnessBound` to the preceding 73-module graph because the updated `PRAWitnessCalculus` imports it. Two changed files and that newly added file are frozen under `frozen/`; 71 unchanged sources are referenced by exact hash from previous frozen packets. `current-suffix-graph.json` records current declared imports, and the static topological/source-byte precheck passed. It does not replace compilation or audit dynamic imports.

The authenticated launcher rebuilds every suffix source on the latest-merge fixed 847 parent, guarding inherited sources, objects, logs, direct external objects/companions and the 74 suffix sources before and after compilation. The parent fixed source tree and matching audits are in `reviews/pra14-latest-merge-source-snapshot/`; its author rebase is running at `/tmp/pra14-full-transitive-86qtvo7f`. The negative test in `negative-parent-precondition-state.json` correctly rejected this still-running parent before compiling any module. Once it reports explicit PASS, launch:

```sh
python3 Computability/DiophantineConsistency/reviews/pra14-latest-merge-join-snapshot/run.py --parent /tmp/pra14-full-transitive-86qtvo7f
```

Author and independent replay, plus an audit of then-current workspace source hashes, remain separate. Earlier strict-source manifests are guarded only as historical evidence, not as authentication of the changed/new sources. Parent reused-object original environments are reconstructed from surviving objects; package-transitive ancestry and dynamic imports remain inherited. The eventual result is the classical candidate-PRA endpoint, not the ordinary native iPRA theorem.
