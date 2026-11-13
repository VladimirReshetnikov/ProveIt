# Sign23 syntax and squares guarded check

This two-stage candidate proposes to compile the Fin24 sign23 syntax and
instantiate the existing generic sign33 square-sum lemma on its 14 rows.
The author-side AST transcription check parses the source back to the pinned,
independently audited sign23 external AST. It is not a Lean/JSON theorem or
proof of coefficient-byte binding, degree, a model bridge, or an iPRA endpoint.

The runner adapts the audited sign24 syntax/squares guard. It pins the syntax,
checker, author result, external AST and source manifest, surveys the captured
sign33 and Jones providers and checks direct dependencies. These are point
observations with inherited transitive and dynamic ancestry qualifications.
It requires 5 GB free disk, 10 GiB available memory and no active Lean before
launch. Each Lean invocation uses `-M2800`, one thread, 120 seconds, a
monitored 4 GiB RSS cap and 10 GiB available-memory floor. The generated
syntax retains the 4,000,000-heartbeat option from the previous generator;
no new increase is requested.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent prelaunch review, attempt 01 passed with author-observed outer
session `85583` exit 0; see `attempt01/README.md`. The [independent terminal
audit](../../reviews/nine-sharing-sign23-seed-squares-terminal-independent/README.md)
passed; the packet and stage inputs are frozen.
