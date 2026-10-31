# Candidate-PRA set-term result graph: author replay

`PRAHistorySetTermResult.PRA_has_setTermResultCode` constructs a primitive-recursive step code and an actual candidate-PRA proof of the result graph for Foundation's set-language term blueprint. The author run `/tmp/pra-history-set-term-result-1gapyo15` passed after rebuilding 24 modules from the merged source graph; post-run checks rehashed all 102 reachable project sources, all 24 new objects and full logs, 78 unchanged parent objects, and the explicitly listed `ZFCinPA.Instances` source and object. Source snapshots, full logs, state, and reauthentication results are in `author-evidence/`; the checks report only `propext`, `Classical.choice`, and `Quot.sound` as Lean metatheory axioms. Other Foundation and package ancestry is inherited.

Run an independent same-parent replay using:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-set-term-result-author-replay/author-driver.py
```

The parent and baseline are pinned in the driver and `baseline.json`; compare all resulting source, object, and full-log hashes with the frozen author state. The independent same-parent replay `/tmp/pra-history-set-term-result-lh70f470` also passed; all 24 source/object/full-log rows and the 102 source-graph hashes matched. Its state, source snapshots and full logs are in `independent-evidence/`. This theorem is a local result-graph building block: it does not establish the whole Foundation refutation predicate bound or the desired PRA equivalence.

After it finishes, run `python3 Computability/DiophantineConsistency/reviews/pra-history-set-term-result-author-replay/compare.py /tmp/PEER_ROOT` to compare the 24 source/object/full-log rows, rehash the peer artifacts, and check the reachable source-graph hashes. This comparison does not extend the inherited package boundary.

The driver places its local overlay first and then the Lake-provided `LEAN_PATH`; this is not a package-only environment. The source graph audit follows explicit `import DiophantineConsistency.*` lines, and `ZFCinPA.Instances` is separately pinned. Dynamic imports, other project namespaces reachable through inherited objects, and the transitive package boundary are not fully authenticated by this packet.

A second independently launched same-parent replay at
`/tmp/pra-history-set-term-result-9pd300bf` also passed; `compare.py` rehashed
its 24 source/object/full-log rows and 102 source-graph hashes against the
author. Its terminal state is frozen in `root-state.json`. This additional
replay does not extend the inherited external-object boundary.
