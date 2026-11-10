# Sign20 direct expression equivalence fresh retry candidate

Attempt 01 failed before Lean due to stale evaluator family keys. This fresh
retry uses family 20 and 21 and their corresponding expression evaluator
modules, with a separate output path; the source, union and surveyed
providers are unchanged. The proposed result is symbolic Fin20/Fin21
zero-existence equivalence, not a Lean/JSON binding, degree theorem or iPRA
endpoint. Historic partial-producer and point-observation qualifications apply.

The guard uses `-M2800`, one thread and 120 seconds, a monitored 4 GiB RSS
cap, 10 GiB available-memory floor and 5 GB disk precheck. Independent
prelaunch review and a coordinated exclusive Lean slot are needed.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
[independent prelaunch review](../../reviews/nine-sharing-sign20-expression-equivalence-retry01-prelaunch-independent/README.md)
passed before launch.
The fresh retry passed its stage and postflight with author-observed outer
session `22244` exit 0; see `attempt01/README.md`. The
[independent terminal audit](../../reviews/nine-sharing-sign20-expression-equivalence-retry01-terminal-independent/README.md)
passed; the packet and stage inputs are frozen.
