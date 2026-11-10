# Sign24 syntax and squares guarded check

This two-stage client proposes to compile the Fin25 sign24 syntax and
instantiate the previously checked sign33 square-sum lemma on its 15 rows.
The candidate syntax was independently parsed back to the external AST by
the author-side source check. That is not a Lean-to-JSON theorem, a proof of
coefficient-byte binding or an all-model bridge.

The runner is adapted from the sign25 syntax/squares check. It verifies the
captured sign33 squares and Jones providers, pins the source copies, manifest,
author-side AST transcription files and external candidate, and checks direct
provider observations. Before launching Lean it requires at least 5 GB free
disk, 10 GiB available host memory and no other live Lean process. Each Lean
invocation uses `-M2800`, one thread, a 120-second timeout and monitored 4 GiB
RSS / 10 GiB available-memory limits. The generated syntax keeps the
inherited `set_option maxHeartbeats 4000000`. Point observations and the
sampled monitor do not establish complete transitive or dynamic ancestry.

The author-side `python3 -I -S -B run.py --preflight` returned zero and is
recorded in `preflight-author-record.json`; it ran no Lean. This is an
uncompiled candidate; independent prelaunch review is requested before a
Lean slot is assigned. Attempt 01 subsequently passed with author-observed
outer session `97737` exit 0; see `attempt01/README.md`. Independent terminal
audit passed at [the independent review](../../reviews/nine-sharing-sign24-seed-squares-terminal-independent/README.md).
The packet and its stage inputs are frozen.
