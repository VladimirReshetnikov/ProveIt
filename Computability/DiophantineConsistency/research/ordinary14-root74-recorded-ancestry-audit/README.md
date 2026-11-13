# Read-only recorded project ancestry from the root74 frontier

This is a bounded, point-in-time inspection of retained build records and
files. It never invokes Lean or writes into the retained evidence. Starting
from the 31 **lexical** project frontier names in the earlier
[provider survey](../ordinary14-root74-provider-survey/README.md), it follows
recorded direct project edges in the selected P72 extension and its linked
base. It stops at external package or toolchain names; those are not followed
transitively. The seed list is not a proven Lean dependency resolution.

At the captured observation, the reachable recorded graph contains 627 P72
and 919 base project producers, 4,414 recorded direct edges, and 80 distinct
external leaf names. Each reached producer's retained source and `.olean`
hash agree with its record. Reached P72 sources also match the separately
pinned P72 source-snapshot manifest. All reached P72-to-P72 and base-to-base
project edges point backward in their respective recorded producer orders.
Every recorded project edge's path, current object hash, and resolved
producer object agree with the producer's recorded object hash. The 919 base
objects also have the recorded P72 link and currently resolve to that base
object. The 80 external direct leaf names, recorded paths, sampled realpaths,
and hashes are in the receipt; the inspector does **not** follow their
providers. Each external name had one distinct recorded-path/observed-realpath/
hash tuple in this sample.

For the reached producers, the inspector compares all retained P72
`direct_guard` slots and all base `outputs` slots to the current filesystem,
including their recorded absence. The 29,860 distinct sampled guard paths
comprise 1,751 present and 28,109 absent slots; no recorded mismatch was
observed. Slots include companions and competing locations, but their
presence or absence does not establish which files Lean loads. The P72
producers' own `.olean` hashes are checked; unrecorded P72 output companions
are not inferred from them.

The selected progress, source-snapshot, base-link and base-state metadata,
the base snapshot manifest, and the earlier observation are hash pinned.
The selected P72 progress record also pins its last row, but it does not
independently authenticate each earlier row. The receipt's digest of reached
row files records what was observed here, not proof of their historical
authenticity. The current reads are not an atomic snapshot: path/hash caches
avoid duplicate reads and cannot detect between-observation mutation. The
inspection does not establish current workspace source identity, immutable
inputs, complete output-companion coverage, transitive Foundation/Mathlib or
toolchain ancestry, implicit imports, dynamic/runtime loading, exclusive
resource allocation, or actual Lean search-path resolution. Matching hashes,
links and recorded order do not alone establish provider compatibility.

The three source candidates `FreeJ13`, `FreeJ13Halt`, and
`DiscreteOrderedRingFacts` from the earlier lexical survey are not existing
producer seeds in this audit. This is neither a guarded build plan nor a Lean
elaboration, iPRA proof-existence theorem, or physical-byte/PDF binding.

An [independent review](../../reviews/ordinary14-root74-recorded-ancestry-independent/README.md)
reconstructs the recorded graph separately and confirms these bounded
observations, with the same historical-record and closure limitations.

Retained paths must remain available for the following replay; the command
only reads them and writes JSON to stdout:

```
python3 -I -S -B research/ordinary14-root74-recorded-ancestry-audit/inspect.py | cmp - research/ordinary14-root74-recorded-ancestry-audit/observation.json
```
