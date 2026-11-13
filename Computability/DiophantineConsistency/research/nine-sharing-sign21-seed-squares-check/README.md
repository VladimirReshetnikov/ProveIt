# Sign21 syntax and squares guarded check

This two-stage candidate proposes compiling the Fin22 sign21 syntax and
instantiating the checked sign33 square-sum lemma on its 12 residuals. The
author-side source checker parses the syntax back to the pinned, independently
audited external sign21 AST. This is not a Lean/JSON theorem, Lean degree,
external coefficient-byte binding, model bridge, or iPRA endpoint.

The guard adapts the audited sign22 syntax/squares runner. It pins the source,
checker, author result, external AST and manifest, and surveys captured
sign33/Jones providers and direct dependencies. These are point observations,
not a complete transitive or dynamic ancestry trace. It requires 5 GB free
disk, 10 GiB available memory and no live Lean before launch. Each Lean
invocation uses `-M2800`, one thread, 120 seconds, a monitored 4 GiB RSS cap
and 10 GiB available-memory floor. Generated syntax retains the inherited
4,000,000-heartbeat setting; no new increase is requested.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent prelaunch review, attempt 01 passed with author-observed outer
session `62165` exit 0; see `attempt01/README.md`. The [independent terminal
audit](../../reviews/nine-sharing-sign21-seed-squares-terminal-independent/README.md)
passed; the packet and stage inputs are frozen.
