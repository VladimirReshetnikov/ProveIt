# Latest-merge 86-operation classical PRA join: fixed input

This prepared 111-module build references the 108 adaptive-86 modules and three draft theorem/check sources previously frozen in `reviews/pra86-classical-join-snapshot/`, by exact hash. Its intended parent is the latest-merge 847+74 classical join, which includes the newly imported rewriting-witness module. The adapted driver recompiles the entire 111-module suffix without workspace object fallback and audits the parent, direct dependencies and package objects. The current static declared-import precheck passed; the negative precondition test correctly rejected the preceding 73-module parent. Neither test is a proof compilation.

After the separately prepared latest-merge classical 74-module join passes, invoke:

```sh
python3 Computability/DiophantineConsistency/reviews/pra86-latest-merge-classical-join-snapshot/run.py --parent /tmp/REPLACE_WITH_PASSED_LATEST_74_JOIN
```

The final `PRA86ZFCStrict` source is still a draft awaiting a coherent compilation. Independent replay and a then-current workspace source audit remain separate. Original reused-object ancestry is reconstructed from surviving objects; package transitive ancestry and dynamic imports remain inherited. Even a successful theorem is a classical candidate-PRA result, not the ordinary native iPRA endpoint.
