# Static natural86 endpoint draft import inventory

This source-only inventory follows initial import headers rooted at the
proposed `Natural86Endpoint.lean`. At this snapshot it resolves 162 unique bare
draft modules in topological order and records 36 directly imported qualified
project-source paths with SHA-256 hashes. It rejects duplicate bare module
names, missing direct qualified source paths and cycles within that draft
closure. Compared with the root74 inventory it adds `P86NaturalCancel`,
`RingNatural86To74`, `Natural86Model` and `Natural86Endpoint`, and omits the
separate `Root74Endpoint` adapter; the root74 positive bridge is still an
inherited dependency.

This is a static initial-header source inventory, not Lean import resolution.
It does not follow qualified-source transitive imports or external package and
runtime imports; inspect provider objects/companions; establish exclusive slot,
disk or guarded-build readiness; elaborate any proof or axiom report; prove an
iPRA endpoint; or bind physical coefficient/port bytes or a PDF. The graph,
source ring/model bridge, root74 bridge and this endpoint remain unelaborated.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-natural86-endpoint-import-inventory/check_source.py | cmp - research/ordinary14-natural86-endpoint-import-inventory/inventory.json
```

No Lean run occurred.

Independent source review: [natural86 endpoint import inventory](../../reviews/ordinary14-natural86-endpoint-import-inventory-independent/README.md).
