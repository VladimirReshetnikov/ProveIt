# Complete equal-length nine-variable verification: stages 102–104

The guarded equal-length-root verification replay completed its final three
stages: `ModelRepBinomial`, `ModelRepFinal` and the enumerator-based
`IPRAExplicitZFCFinal` endpoint. Both the author and verification ledgers now
record all **104 stages**. The retained [`audit.json`](observations/stages-102-104/audit.json)
checks the entire 1–104 prefix, including the earlier CURRENT2011 endpoint
and both source-named axiom-report sets.

Of the 104 author/verification output object pairs, **84 are byte-identical**.
For each of the remaining **20**, the complete files become byte-identical
after replacing their single embedded author source pathname with the
same-length verification pathname. There are 31 differing direct-input hash
pairs across 28 stages. The audit accepts each only if it is exactly the
author/verification pair of a previously checked predecessor; all direct and
candidate/companion guards then agree after normalizing overlay roots and
mapping only those checked predecessor hashes. Sources and complete compiler
logs match under source-path normalization. The audit checks whole object
files; it does not prove Lean's binary-format semantics or claim that the
raw differing hashes match.

The CURRENT2011 stage-80 endpoint, stage-81 axiom client and enumerator-based
stage-104 endpoint output objects are byte-identical. The audit checks all
15 stage-81 and four stage-104 source-named axiom reports. Each lists only
`propext`, `Classical.choice` and `Quot.sound` as Lean metatheory
dependencies, not object-theory axioms. Matching output bytes do not by
themselves prove that path-normalized different raw imports are semantically
interchangeable.

[`run.py`](run.py) starts the three guarded stages individually, checks
`/proc/meminfo` `MemAvailable` before each and samples memory and Lean
processes every two seconds under the explicit two-Lean-process resource
decision. Each final stage has samples showing overlap with the compact
rebuild; at most two Lean processes were observed, and the lowest sampled
`MemAvailable` was 18,166,716 KiB. [`check_overlap.py`](check_overlap.py)
rechecks the recorded samples. Its earlier BusyBeaver-only filter and output
are retained separately; that filter missed compact modules from the
DiophantineConsistency source root. These are sampled observations, not
continuous monitoring or a cgroup-limit proof.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the full-prefix
comparison, sources, receipts, dependency listings and compiler logs under
[`observations`](observations/). The prior [1–101 prefix](../nine-variable-ipra-equal-length-stages-97-101-monitored/README.md)
is a separate frozen packet. The verification used the author's registered
warning baselines and historical parent provider. Project, package and
dynamically loaded ancestry inherited from that provider, as well as any
file or PDF transcription, remains outside this audit. The live `/tmp`
overlays are needed to repeat it.
