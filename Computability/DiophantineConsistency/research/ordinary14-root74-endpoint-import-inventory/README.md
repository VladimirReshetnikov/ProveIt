# Static root74 endpoint draft import inventory

This source-only inventory follows initial import headers from the proposed
`Root74Endpoint.lean`, resolves 159 unique bare draft modules topologically,
and records 31 directly imported qualified project-source paths and SHA-256
hashes at this snapshot. It rejects duplicate bare names, missing direct
qualified sources and cycles in the bare draft closure. The proposed endpoint,
its positive bridge, literal graphs and model clients remain unelaborated.

This is a static source inventory, not Lean dependency resolution. It does not
follow qualified-source transitive imports or external package/runtime imports,
inspect provider objects or companions, assess disk/slot/prelaunch readiness,
prove the model/iPRA endpoint, or bind any physical coefficient/byte/PDF file.
The direct slim port-bounds import does not remove heavy dependencies inherited
through the separate root78 bridge.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-endpoint-import-inventory/check_source.py | cmp - research/ordinary14-root74-endpoint-import-inventory/inventory.json
```

Independent source review: [root74 endpoint import inventory](../../reviews/ordinary14-root74-endpoint-import-inventory-independent/README.md).
