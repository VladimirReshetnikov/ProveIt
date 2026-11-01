# Post-merge 14-equation/PRA join: frozen build input

This is a prepared fixed-source build, not a completed proof. The current declared-import graph has the same 73 suffix modules and order as the preceding checked snapshot. Nine changed source files are frozen under `frozen/`; 64 unchanged files are explicitly referenced by hash in the earlier `pra14-zfc-join-snapshot/frozen/` packet, rather than duplicated. `current-suffix-graph.json` records the declared edges. The prior strict-source manifests are retained and guarded as historical evidence only: they do not independently authenticate the nine changed sources.

The source-directed driver is adapted from the accepted prior join driver to read those exact source locations. It builds all 73 suffix modules afresh atop a completed 847-module post-merge parent, with package-only object resolution and before/after guards on the complete parent and direct external inputs. The fixed 847-source graph, 16 source deltas, and two matching graph audits are in `reviews/pra14-post-merge-source-snapshot/`. Its actual guarded rebase is running at `/tmp/pra14-full-transitive-bbfwtdv_`.

`negative-parent-precondition-state.json` records a test through the authenticated launcher against that still-running parent: it failed with `parent is not PASS` before compiling any suffix. This is only a precondition test and does not validate the remaining replay path. After the parent reaches explicit PASS, launch:

```sh
python3 Computability/DiophantineConsistency/reviews/pra14-post-merge-join-snapshot/run.py --parent /tmp/pra14-full-transitive-bbfwtdv_
```

The author build and an independent replay are both required. Source-byte comparison to the then-current workspace is separate. Parent reused-object ancestry is reconstructed from surviving objects, and external package transitive ancestry and dynamic imports are inherited. Any eventual endpoint is the classical candidate-PRA theorem, with native intuitionistic iPRA remaining a separate objective.
