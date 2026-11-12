# Static natural-82 endpoint import inventory

This is a **read-only lexical source inventory** rooted at the unelaborated `Natural82Endpoint.lean`. Its initial-import-header scan follows 169 unique bare draft modules, records their topological order and source hashes, and identifies 36 directly named qualified project sources with paths and hashes. It rejects duplicate bare-module candidates for a traversed import, missing directly named qualified source files, and cycles within the bare closure. Its receipt hashes the current endpoint source, including its five unexecuted `#print axioms` commands; hashing source is not an axiom replay.

The duplicate-candidate search is limited to `.lean` files under this
project's `research` tree; it does not rule out competing source or object
providers elsewhere.

Against the pinned [root74 endpoint inventory](../ordinary14-root74-endpoint-import-inventory/README.md), 158 bare drafts are shared, 11 are added, and the separate `Root74Endpoint` adapter is omitted. None of the 158 shared original draft-source hashes changed from that snapshot. The additions are `P86NaturalCancel`, `RingNatural86To74`, `Natural86Model`, `Natural86Endpoint`, `P82NaturalForced`, `RingNatural82To86`, `Natural82Model`, `Predecessors82`, `PartialShift82To74`, `GraphPredecessors82`, and `Natural82Endpoint`. The list is a set comparison; the receipt supplies the actual topological order. Five direct qualified names are added relative to the root74 original headers and none are removed.

The entire 162-draft [natural86 inventory](../ordinary14-natural86-endpoint-import-inventory/README.md) is included, with seven additional bare drafts for the natural82 graph, model, predecessor and endpoint chain. No new direct qualified source name is introduced relative to that natural86 snapshot.
That comparison checks module-name inclusion; the independent review also
compares the 162 common source hashes.

An [independent review](../../reviews/ordinary14-natural82-endpoint-import-inventory-independent/README.md)
checks the observed source headers, paths, ordering and inventory comparisons.

The reviewed [root74 slim overlay](../ordinary14-root74-slim-overlay/README.md) contains inert snapshots for the 158 shared modules and the unused `Root74Endpoint` adapter; it does **not** include the 11 new modules. The recorded original source hashes of those shared modules still match the current sources. This does not create or validate a combined overlay. In particular, the receipt's list of directly qualified names absent from the slim overlay compares the **original endpoint-closure headers** with the overlay's rewritten headers: it includes `C44Short15Facts`, whose imports the overlay deliberately replaces. It is not an actual Lean-resolved set of missing providers, nor proof that overlay edits or new modules are compatible.

The scan parses only initial, simple import lines in the bare source closure; it does not parse arbitrary Lean syntax, follow any qualified project's transitive imports, inspect external Foundation/Mathlib/toolchain or runtime imports, check object hashes/ancestry or companions, resolve Lean search paths, detect all possible output collisions, reserve a build slot, run Lean, or establish resource/build readiness. The provider observations from earlier root74 packets are not inherited automatically by this larger chain. No proof elaboration, model transfer, iPRA derivability, coefficient-byte binding or PDF binding follows from this inventory. The endpoint and its source-only dependencies remain unelaborated.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural82-endpoint-import-inventory/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural82-endpoint-import-inventory/inventory.json
```
