# Sign19 syntax and squares guarded candidate

This source-only two-stage candidate proposes compiling Fin20 sign19 syntax
and instantiating the checked sign33 square-sum lemma on its 10 residuals.
The author parser compares syntax to the external sign19 AST; this is not a
Lean/JSON theorem, degree theorem, model bridge or iPRA endpoint.

The fresh-output guard uses `-M2800`, one thread and 120 seconds per stage,
a monitored 4 GiB RSS cap, 10 GiB available-memory floor and 5 GB disk
precheck. Provider surveys are point observations, not a complete transitive
or dynamic ancestry trace. Independent candidate and prelaunch reviews and
a coordinated Lean slot are needed before running Lean.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
[independent prelaunch review](../../reviews/nine-sharing-sign19-seed-squares-prelaunch-independent/README.md)
passed before launch. Attempt 01 failed when the first syntax compilation
reached its 120-second timeout; author outer session `10092` exited 1. See
`attempt01/README.md`. The [independent failure audit](../../reviews/nine-sharing-sign19-seed-squares-failure-independent/README.md)
passed; the packet is frozen and no syntax or squares theorem is claimed.
