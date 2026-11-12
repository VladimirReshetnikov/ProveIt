# Isolated root74 slim-helper source overlay

This source-only packet snapshots all 159 reachable bare draft modules from the
reviewed static root74 endpoint inventory, including the separately reviewed
`CompactPortBoundsSlim` helper already imported by the root74 positive bridge.
The original source clients remain unchanged. All files under `source/` have
the inert suffix `.lean.src` to avoid colliding with existing bare module name
lookup. A future isolated build would need to copy these bytes to a new source
root with the `.src` suffix removed, under a separately reviewed and guarded
build plan. This packet does not materialize or build that root.

The six affected inherited root78 clients contain exactly four heavy import
replacements and six `port_bounds` reference replacements, identical to the
reviewed root78 slim overlay. The checker pins both prior inventory hashes,
verifies every original/overlay byte and source hash, the exact six named
changes and their counts, the new namespace and helper reachability, bare-name
uniqueness, acyclicity, and the `Root74Endpoint` dependency path. Of the 159
snapshots, 138 are byte-identical to the reviewed root78 slim overlay; 21 names
are new relative to that overlay and only `Root78Endpoint` is no longer in the
root74 closure. The new and omitted names, original/overlay hashes, changed byte
lengths and full topological order are listed in `inventory.json`.

The same inventory recursively follows parsed initial project-source import
headers: at this snapshot it records 30 directly qualified sources, 1,127
reachable project source files and 92 external names. The parser strips nested
comments and recognizes common header modifiers, but is not Lean's resolver.
`C44Short15Facts` is absent from this lexical route. The external/package
transitive source and runtime imports, generated dependencies, objects,
companions, search-path resolution and provider provenance are not established.
Counts are planning observations, not Lean build stage counts or evidence of
coherent providers.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-slim-overlay/check_source.py | cmp - research/ordinary14-root74-slim-overlay/inventory.json
```

The source refactor is unelaborated; it does not establish the graph/model
bridge, Lean compatibility, model/iPRA endpoint, or physical coefficient/byte
or PDF binding. No Lean run or provider replay was performed. Current disk
availability remains below the established Lean-run floor.

Independent source review: [root74 slim overlay](../../reviews/ordinary14-root74-slim-overlay-independent/README.md).
