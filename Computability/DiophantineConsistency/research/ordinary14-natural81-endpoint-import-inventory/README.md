# Static natural-81 endpoint import inventory

This is a **read-only lexical inventory** of the unelaborated `Natural81Endpoint.lean`
and its initial source import headers, adapted from the earlier
[natural-82 inventory](../ordinary14-natural82-endpoint-import-inventory/README.md).
It records 173 topologically ordered bare draft modules and 38 directly named
qualified project sources, including the endpoint source's five unexecuted
axiom-report commands. The duplicate bare-source search is confined to `.lean`
files under this project's research tree; it is not a global source or object
search and does not resolve Lean's actual search path.

The pinned natural-82 inventory's 169 module names are all included, with four
additional drafts: `P81NaturalForcedJ`, `Natural81JShift`, `StrictK0Symbolic`
and `Natural81Endpoint`. Two qualified project sources are added to the direct
header set: `CompactKernelSplit` and `CompactSymbolicModelIff`. This comparison
checks module-name inclusion, not the hashes of the shared natural-82 snapshot.
The [independent review](../../reviews/ordinary14-natural81-endpoint-import-inventory-independent/README.md)
also checks the 169 shared source hashes against that snapshot.
The [root74 slim overlay](../ordinary14-root74-slim-overlay/README.md) contains
158 shared draft snapshots but lacks 15 of this endpoint's drafts; its original
source hashes for shared drafts still match the current original sources. The
listed qualified differences compare original headers against deliberately
rewritten overlay headers and are not a resolved provider cut.

The checker follows only simple initial import headers of the bare draft
closure. It does not traverse qualified-source or external package imports,
inspect object ancestry or companions, establish search order or collision
freedom, reserve resources, run Lean, or establish an iPRA derivation. This
is not a combined overlay or a build-ready plan. The physical coefficient
and PDF association remain separate.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural81-endpoint-import-inventory/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural81-endpoint-import-inventory/inventory.json
```
