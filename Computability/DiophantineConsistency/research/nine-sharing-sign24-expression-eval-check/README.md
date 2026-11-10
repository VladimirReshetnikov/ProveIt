# Sign24 direct expression and evaluation guarded check

This four-stage candidate defines abstract and current-port Fin24 expressions
by removing the distinguished input from sign24 and checks evaluation at
input one. It adapts the checked sign25 stages. No Lean/JSON or byte binding,
Lean degree theorem, model-zero equivalence or iPRA endpoint follows from
these stages alone.

The guard uses the independently audited sign24 syntax/squares base. It
surveys the generic input-removal provider and current-data provider through
successful stages of earlier overall failed runs, crediting only the observed
successful stages. It checks direct source, object, log, overlay, and
dependency observations but not complete transitive or dynamic ancestry.
Lean invocations use `-M2800`, one thread and 120 seconds, with a monitored
4 GiB RSS cap and 10 GiB available-memory floor; launch requires at least
5 GB free disk. The upstream syntax carries its inherited 4,000,000-heartbeat
option; no new heartbeat option is introduced in these stages.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After an
independent prelaunch review, attempt 01 passed with author-observed outer
session `56656` exit 0; see `attempt01/README.md`. The [independent terminal
audit](../../reviews/nine-sharing-sign24-expression-eval-terminal-independent/README.md)
passed; the packet and stage inputs are frozen.
