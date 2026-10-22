# Phase18 Lean evidence

The [terminal result](result.json), [actual evidence review](result-review.json)
and [independent readback](../integration/resumed-peer/README.md) pass for 214
providers: 199 project modules and fifteen typed clients. There are 107 fresh
checks and 107 source-transitive phase17 reuses, plus two fresh endpoint audits.
The endpoint selects 178 modules / 1,767,300 source bytes. All nine site batches
were checked fresh, covering 105 blocks / 4,751 leaves / 6,176 outcomes.

All fourteen old client sources and their 83 reports are exact. The new macro
client matches its ten-report baseline; five WFTheory and ten endpoint reports
match exactly. All clients and audits have zero warnings. Provider records have
16 warning occurrences (9 fresh);
every fresh warning headline already occurred in the same module.

The [initial timeout](../integration/runtime/initial-timeout-record.json) and
[external session interruption](../integration/runtime/interruption.json) are preserved. Failed or incomplete records
remain unaccepted; the final review checks the subsequent fresh retries and all
retained records. Only forward-certificate time limits changed, from 120 to 900
seconds. Proof sources, exact profiles and the selected plan stayed fixed.

The [archive](evidence.tar.gz), [alias index](index.json) and [capture receipt](capture.json)
contain 616 distinct blobs, 933 logical entries
and 894 source aliases. The 552-file accepted raw
subset includes source, log and record evidence. Additional context preserves
original raw statuses and source reviews; six local before snapshots are retained.
Eleven exact phase17 packet boundaries remain external. No object files are shipped.
Archive SHA-256: `6b3d8326f9d13c4889975e865e6a1a4c94bba1e6593e4576673f0a2d41b3909c`.
The [independent capture review](capture-peer/actual-review.json) checks its bytes.

Capture did not replay captured scripts or proofs. The published packet is
inert data; the owned capture helper read and hashed its explicit inputs. [Clients](clients/) and [audits](audits/) are also readable unpacked.
The [frozen plan](check-plan.json), [historical runner](check.py),
[actual auditor](review_actual.py), [capture helper](capture.py) and
[capture map](capture-config.json) retain their absolute-path evidence bindings.
For fresh endpoint reproduction use the portable driver in
[the maintained Lean instructions](../../../lean/README.md) with a new output.
The 215-state machine is unchanged. No full-stack check of other variants,
internal PA endpoint or minimum-state theorem is claimed.
