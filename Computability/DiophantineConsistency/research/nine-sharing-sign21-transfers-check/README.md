# Sign21 normalized-S residual transfers guarded check

This two-stage candidate proposes all 12 old/new residual evaluations under
the natural normalized-S lift, split into two six-row Lean modules. The guard
pins their source, author-side AST and offset check, manifest and coordinate
producer. The author checker reuses a previous author's parser and is not an
independent Lean semantics proof. No beta-port premise is added in this step.

The runner checks producer sources, objects, logs, direct dependency guards
and overlay links. These are point observations with inherited ancestry, not
a complete transitive or dynamic dependency trace. Each Lean invocation uses
`-M2800`, one thread and 120 seconds, with 4 GiB monitored RSS, a 10 GiB
available-memory floor and 5 GB free-disk precheck. The upstream syntax
provider retains its inherited 4,000,000-heartbeat option; these stages add none.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
coordinate producer passed independent terminal audit. After independent
prelaunch review, attempt 01 passed with author-observed outer session `54244`
exit 0; see `attempt01/README.md`. The [independent terminal audit](../../reviews/nine-sharing-sign21-transfers-terminal-independent/README.md)
passed; the packet and stage inputs are frozen. The assembled bridge and
endpoint remain separate.
