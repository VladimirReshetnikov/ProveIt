# Independent scoped interpreter-limit retry prelaunch review

Checker session 84719 exited 0 and recorded `result.json`. All three source
files and manifest semantics are byte-identical to the prior no-alias opacity
retry; only source path fields differ. The reconstructed runner differs only
in the interpreter option `-M2800` → `-M3600`, fresh output path, manifest
pin and descriptive labels. It preserves the 4 GiB sampled session RSS cap,
10 GiB host-memory floor, 120-second per-invocation timeout, 5 GB disk
precheck, one thread and prior provider guards. Sampling can miss short spikes
or escaped descendants.

The checker independently inspects four prior failed sign25 stage receipts
and their interpreter-memory-exception logs, records sampled peaks, reruns
the concrete bridge audit and the no-Lean preflight. This is a scoped retry
motivated by those failures, not proof of their exact cause or a guarantee of
success. No endpoint is claimed; launch still needs the exclusive slot and
resource checks, and inherited provider/ancestry qualifications remain.
