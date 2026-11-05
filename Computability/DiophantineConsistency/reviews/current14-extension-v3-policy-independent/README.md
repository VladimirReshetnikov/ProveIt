# Independent review of the v3 dependency policy and wiring

The frozen v3 driver, coordinator/verifier, supervisor and two-client runner were reviewed without launching Lean, the coordinator, supervisor or a retry. Their 14 source/control hashes and author control receipt are rechecked by [check.py](check.py); [result.json](result.json) records the principal pins. This is a source and synthetic-control review, not evidence of a successful extension or of an observed outer supervisor exit.

The shared `deps.py` policy accepts one occurrence of each recorded dependency and permits a second occurrence only for `Init` with the identical lexical path. It rejects a third `Init`, duplicate non-`Init`, unrecorded or missing paths and distinct modules mapped to one path. The v3 driver invokes the policy while resolving dependencies, authenticates the selected producer and companions, and then validates the **original raw stdout lines** before compilation. The v3 terminal verifier applies the same validator to the hashed raw stdout and recorded direct map. The later v3 client runner calls the same driver policy and retains its source, guard and before/after log checks. Path strings that merely normalize or resolve to the same object are not accepted as distinct raw spellings.

The check independently applies the policy to the retained five-line failure stdout, accepting its two identical `Init` paths without altering the log. It exercises rejection of a third `Init`, a duplicate non-`Init`, an alternate `Init` path, a dot-path spelling, a missing recorded dependency and an unrecorded extra. The author also provided focused pure controls and a 61-row coordinator fixture with the duplicate and negative cases.

A separate [nonempty synthetic terminal](nonempty-controls.py) uses the actual pinned v3 verifier with a symlinked base producer, toolchain `Init` occurring twice, and 60 fresh project dependencies. It accepts that fixture and rejects a third `Init`, conflicting path, non-`Init` duplicate, wrong producer hash or project route, extra import, wrong session group and unexpected overlay file. Its recorded [result](nonempty-result.json) is deterministic. It does not trace real processes or prove a successful Lean dependency path.

The reviewed driver, coordinator, supervisor and client runner use distinct v3 output paths; the v2 failure evidence remains untouched. Coordinator and supervisor pins route to v3, and the new dependency helper is included among the driver/coordinator integrity pins. The earlier source reviews' limits continue: session receipts are driver-reported, warnings are permitted by the extension verifier, memory/disk monitoring is sampled, and transitive, dynamic, forced-death and between-observation provenance remain outside the guarantees. The v3 supervisor's own outer session exit and a successful real extension still require separate observation and audit.

No blocker was found in the narrow duplicate-`Init` repair and reviewed wiring. The first actual v3 positive path is still untested and may encounter another failure; preserve its evidence if so.

Read-only reproduction:

```
python3 -I -S -B path/to/current14-extension-v3-policy-independent/nonempty-controls.py
python3 -I -S -B path/to/current14-extension-v3-policy-independent/check.py
```

Neither command invokes Lean or any build.
