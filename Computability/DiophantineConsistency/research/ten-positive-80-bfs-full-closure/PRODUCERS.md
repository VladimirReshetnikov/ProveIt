# New-module direct producer comparison

`audit-producers.py` independently reads the captured serialized headers and the retained successful author receipts for each of the 12 newly introduced modules. `observations/producers01/` records exit 0: all 12 selected output paths/hashes match their own producer receipts, their current source bytes and direct source imports match those captured headers, and all 16 serialized direct project-import edges have matching selected path, SHA-256 and resolved-target pins in the respective producer receipt. Repeated automatically imported `Init` entries are excluded from this project-edge count and were covered only by the captured outside selection.

The captured stdout SHA-256 is `21c012d589b30c78035ccad1ecf8754ad2fb590bd4dc1b2d32fdff20f372ba27`. This checks recorded direct object pins, not all companion files at producer time, an independent Lean replay, unpinned transitive historical sources, or package-transitive/dynamic ancestry. The underlying closure capture is unchanged.

The [independent producer audit](../../reviews/bfs-full-closure-producers-independent/README.md) also checks the 12 retained producer sources, outputs and logs, and all 16 direct project edges; it does not remove the inherited boundaries above.
