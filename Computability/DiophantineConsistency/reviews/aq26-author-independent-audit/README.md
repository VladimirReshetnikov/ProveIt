# Independent audit of the AQ28 → AQ27 → AQ26 author extension

[`audit.py`](audit.py) independently checked the completed historical
author-only [v2 trial](../aq26-author-trial-v2/README.md). Its actual tool
session `33701` exited 0 and produced [receipt.json](receipt.json), SHA-256
`1a9c80075983306e93c2146ceb26841a436e5c479fd10cf7e5fb62290f98398c`.
The audit was run at idle I/O priority and nice 19, with hash reads rate-limited
to 8 MiB/s. It is an artifact and recorded-input audit, not another Lean replay.

The audit checked all 24 ordered addition sources against their pinned Git
blobs and the preserved source copies, all compiled objects and logs, recorded
direct-import resolution, and all 75 exact diagnostic declarations. It also
checked the endpoint statement shapes for AQ28, AQ27 and AQ26 and rejected
Lean errors and `sorryAx` in every successful log. The reports' allowed
`propext`, `Classical.choice`, and `Quot.sound` are Lean metatheory
dependencies, not added axioms of the object theory.

For the parent, it rehashed all 1,210 frozen source, object and log rows,
13,150 recorded direct-input companion guards, all 1,540 inventoried fresh
Foundation artifacts, and all 12,100 overlay companion guards. It repeated
key source, object, log and guard checks at the end and verified that the
reviewed script itself did not change. The parent recorded 15 workspace
source drifts and was already independently artifact-audited. This audit
does not claim that the new 24 modules have an independently replayed peer.

The earlier [failed attempt](../aq26-author-attempt-1/README.md) was also
checked: its actual recorded process exit was 1, the first three modules
passed, and `AdaptiveAQ28Transport` failed on the unresolved `subst_id` with
subsequent `sorryAx` reports. The pinned v2 source differs from the earlier
24-source set only in the three transport files, each changing the unqualified
name to `DiophantineConsistency.AdaptiveAQ30Transport.subst_id`. The v2
run's recorded successful logs contain no errors or `sorryAx`.

The audit requires normal Python and explicitly refuses `-O`/`-OO`; both
negative controls were observed to exit 1. It makes no claim of a second Lean
replay, a standard-theory AQ26 proof, source-current or PDF identity, a
source-to-object proof for inherited packages, a dynamic-load trace, or
protection from transient mutations between observations. The Foundation
build wrapper's outer exit was not observed. All such limitations of the
parent remain inherited.
