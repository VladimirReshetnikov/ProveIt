# Natural-80 P72/base recorded ancestry: read-only expansion

This inspection expands the earlier [root74 recorded-ancestry audit](../ordinary14-root74-recorded-ancestry-audit/README.md)
from its 31 lexical frontier seeds to the 40 project frontier names in the
reviewed [natural-80 qualified cut](../ordinary14-natural80-qualified-provider-cut/README.md).
It reads the retained P72 and linked-base records and files; it does not invoke
Lean, create build outputs or mutate evidence. The source seeds are a lexical
cut, not a resolved Lean dependency set.

The nine additional natural-80 seed names are listed in `observation.json`.
Following only recorded direct project edges from all 40 seeds reaches **627
P72 producers and 919 base producers**, with **4,414 recorded edges** and
**80 distinct external leaf names**. A second reachability traversal of the
same recorded edges starts from the earlier 31 seeds and reaches exactly the
same set: the nine added seed names were already inside that recorded closure.
The resulting module and external-leaf digests, external binding observations,
producer/edge counts and guard-slot counts match the pinned earlier receipt.
This is equality of the **recorded project closures at this observation**, not
proof that either is the full set of objects Lean or the runtime will load.

For the reached records, the inspector checks retained source and `.olean`
hashes, P72 snapshot source hashes, recorded producer order, recorded direct
project edge hashes and resolved producer targets, and all 919 recorded base
links. It compares **29,860 distinct recorded guard/output slots** with the
current filesystem: 1,751 present and 28,109 absent; no mismatch was observed.
It also checks recorded paths and hashes for the external direct leaves but
stops there. The five absent-in-selected-P72 qualified source candidates in
the natural-80 plan are not existing producer seeds in this audit and must be
handled as separate source stages.

## What this permits and what it does not

The result allows the earlier reviewed root74 evidence to be compared directly
with the natural-80 frontier **as recorded**: no extra project producer is
needed merely to cover those nine additional observed frontier names in that
recorded graph. It does **not** authenticate all earlier P72 row records: the
pinned progress metadata independently anchors its final row, while hashes of
other rows remain observations. Nor does it establish the 80 external leaves'
transitive package/toolchain provenance, implicit or runtime imports, required
companion files, actual Lean search order, or compatibility of the recorded
objects. The reads are non-atomic and use caches; changes during or after the
inspection may be missed. No resource slot or immutable filesystem snapshot
is reserved. Matching hashes are not a Lean resolution or proof check.

The separately reviewed [189-stage lexical plan](../ordinary14-natural80-ordered-provider-plan/README.md)
provides the candidate source order. A [read-only materialization blueprint](../ordinary14-natural80-source-materialization-plan/README.md)
maps those 189 pinned inputs to prospective source and output names without
selecting or creating a root. A build would still need a separately reviewed
fail-closed runner; protected source/provider/companion snapshots or sufficient
independent isolation and revalidation; a full package/toolchain/runtime and
implicit-import plan; exact per-stage `lean --deps` resolution; exclusive
resource monitoring; collision-safe fresh outputs; executed axiom reports;
and independent postflight. No executable Lean launcher is authorized by this
receipt. The current free space was below the existing strict 5.1 GB floor at
preparation and must be sampled again before any future run.

An [independent review](../../reviews/ordinary14-natural80-recorded-ancestry-independent/README.md)
reconstructs the recorded seed closure and replays the pinned prior file
checks, without establishing unrecorded provider or runtime ancestry.

Run from `Computability/DiophantineConsistency` while the pinned retained
roots still exist:

```sh
python3 -I -S -B research/ordinary14-natural80-recorded-ancestry-audit/inspect.py | cmp - research/ordinary14-natural80-recorded-ancestry-audit/observation.json
```
