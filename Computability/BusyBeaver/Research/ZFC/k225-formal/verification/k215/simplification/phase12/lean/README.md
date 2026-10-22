# Phase12 Lean evidence

The import cut passed the Lean checks. General well-founded model construction and the semantic content of a ZF model now live in two small modules; the historical WFModel and ZFNative wrappers preserve their exported results. L2Lib222 imports the formula-code definitions directly. The endpoint closure falls from192 to179 project modules while its theorem statements and the exact215-state machine remain unchanged.

The primary check contains184 providers:179 endpoint modules plus five separately selected decoder-prefix modules. Fifteen modules were freshly checked and169 reused from phase11 after exact transitive source/import validation. Both unchanged endpoint clients passed with ten named standard-axiom reports and no audit warnings. The project logs contain20 warning occurrences:four in freshly checked, unchanged KLowerQHyp/L2Control222 sources and16 in reused logs. All nine site batches keep their exact phase11 source/object/log bindings; none was recompiled.

A separate compatibility check contains67 project modules and two typed clients. It reused52 primary providers and12 phase11 providers, and freshly checked WFModel, ZFNative, the unchanged WFTheory facade and both clients. The clients restate the old model-construction and ZFNative theorem types and emit ten named reports. WFTheory emits its five existing reports. All five fresh invocations have zero warnings; seven warning occurrences come from reused logs. Together the two runs cover199 distinct project modules. This is not a fresh199-module build.

Both actual outer processes exited zero. The independent raw-record reviews rehashed sources, imports, dependency objects, logs, tools and before-input bindings. No proof/compiler failure or retry occurred. The first collector rejected an assumption that both inventories explicitly import Init; its raw failure is preserved, and the successor derives each inventory’s actual external-import list (primary Init, compatibility empty). The earlier preparation without WFTheory, two root metadata-reader corrections and the later adoption wording correction are preserved as history; they are not proof failures. The wording correction clarifies that the producer source changed while no producer was executed.

Seven exact compiled source files and one maintained producer import substitution were adopted. An independent reader treated the producer's AST tables as data and reproduced all three maintained L2 outputs exactly, without importing or executing the producer. The original canonical generate_l2k222.py bytes remain an explicit historical snapshot for each raw before.inputs record. The current producer is checked separately. The other three producer files and two retired-template absences retain their phase11 boundaries.

`execution.tar.gz` stores the new raw runs, clients, maps, plans, controls, history and exact source/log aliases. `basis-reference.json` pins the published [phase11 packet](../../phase11/lean/README.md), which supplies unchanged evidence in place. No compiled objects or ancestor archives are copied. The reader calls exact pinned local predecessor validators; it never runs archive-member code.

From a repository containing this packet and its referenced predecessors:

```sh
python -B review_saved.py --basis-repo /path/to/Proofs --repo /path/to/Proofs --output /tmp/phase12-saved-review.json
```

Omitting `--repo` checks historical saved evidence only. With `--repo`, all199 current project sources, the eight adoption files and the retained producer/absence boundary are compared with the accepted records. Saved verification checks recorded object-hash provenance; only the collector's separate live postcheck rehashes actual objects. The packet performs no new Lean compilation, machine runtime test, Rocq check or internal PA proof.
