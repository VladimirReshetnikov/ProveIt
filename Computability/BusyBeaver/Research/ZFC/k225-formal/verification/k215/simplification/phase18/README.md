# Phase18: shared macro proofs

**The combined Lean check, independent result review and evidence capture pass.**
This continues [phase17](../phase17/README.md), parent
`7a1273555ba3c2d4f6db087567309f692660ec72`, and preserves upstream main
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The 215-state machine and endpoint
statements are unchanged. The internal PA endpoint and a minimum-state theorem
remain open.

The 222 macro library now shares the reference 254 proofs through
`RMTransfer.Closed`. Exactly 204 old-range nodes form a closed agreement set after
removing fifteen ancestors of changed nodes 136 and 149. One transfer theorem
supplies 53 unchanged run contracts. The rotated 136 loop and its fetch cases
remain local. `L2Lib254` imports `Code254` directly; `L2Root254` explicitly imports
its enumerator. Phase17's original-domain seed, direct `C222` compiler, computed
trees and shorter AX words remain in place.

Across the same 199 selected project modules, source size falls from 2,084,576 to
2,057,203 bytes: **27,373 bytes / 683 Lean lines** removed (155 upstream and 528
local lines). Retiring the unused 74-line / 3,806-byte `generate_l2k222.py`, then
adding one line / 109 bytes to keep `generate_l2dom.py` synchronized with the
shared declarations, gives **31,070 bytes / 756 lines** of net maintenance savings.
Both producer changes were reviewed as source; neither generator was executed.
The endpoint imports four shared reference modules and grows from 174 modules /
1,749,188 bytes to **178 / 1,767,300**. These are distinct source scopes.

The frozen combined check covers **214 providers**: 199 project modules and
fifteen typed clients, with **107 fresh compilations and 107 exact-source reuses**,
plus two fresh endpoint audits. All nine 215 site batches were checked fresh:
105 blocks cover 4,751 leaves / 6,176 outcomes. All fourteen earlier client sources
are unchanged; their 83 reports, the new macro client's ten baseline reports,
five `WFTheory` reports and ten endpoint audit reports match the frozen
expectations exactly. No assumption-profile exception was added.

Accepted provider records contain 16 warning occurrences (9 fresh); the fresh warning headlines already appeared in the same modules. All fifteen typed clients and both endpoint audits have zero warnings.

The initial run timed out at forward-certificate batch 12 after 120 seconds,
with an empty compiler log and no accepted object. Its raw failure and the 23
completed providers are preserved. A one-line resource-policy change extends
forward-certificate batches to 900 seconds, matching site batches. The same
source map and acceptance checks then passed on resume; retained successful
120-second records were not rewritten.

A later command-session interruption stopped the supervisor during site batch 2.
Its partial record remains `COMPILING`, with no known compiler exit status; the
physical object observed afterward was excluded. The 153 completed providers
were retained, and a detached supervisor reran that batch and completed the same
checks without changing the owner, proof sources or budgets.

The shared `L2K.AS` type passes the required record-syntax, encoding and run-contract
client. The separate old record identity and generated qualified namespace are
retired: optional `L2K.AS.mk` / `L2K.AS.np` probes fail. Their partial `sorryAx`
output is excluded, and the original all-probe smoke runner remains failed.
A maintained four-root census found no qualified generated-name caller among
32,415 Lean files. The unused `L2K.while_AS` and `L2K.inc_AS` are also retired,
leaving 87 of 89 old source-declared names; this does not preserve every generated
name. The required six-library smoke check and ten-report macro client pass.

Attribution: Vladimir Reshetnikov's upstream
[733e83e049](https://github.com/VladimirReshetnikov/ProveIt/commit/733e83e049adf1bb8c5e8d8ba76927b138cf452c),
coauthored by Claude Opus 5.5, supplies nine Profile/syntax and RegisterPath
simplifications, preserved here. Independent source reviews cover the finite
transfer resource, contracts, callers, producer repair and actual compiler evidence.
No full compilation of the other machine variants is claimed.

See [source measures](integration/source-metrics-final.json),
[source adoption](integration/source-adoption.json),
[producer repair](integration/producer-sync-adoption.json),
[macro review](integration/macro-peer/README.md),
[smoke readback](integration/macro-peer/SMOKE-RUN2.md),
[upstream review](integration/main-review/review.json), and
[combined Lean evidence](lean/README.md).
