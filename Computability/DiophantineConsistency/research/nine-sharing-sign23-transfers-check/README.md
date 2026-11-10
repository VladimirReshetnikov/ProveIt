# Sign23 Delta residual transfers guarded check

This two-stage candidate proposes all 14 old/new residual evaluations under
the natural Delta lift. It splits the 14 transfers evenly across two Lean
modules. The guard pins their source, author-side AST and offset check,
manifest, and coordinate-retry producer. The author checker itself uses the
preceding sign24 author's parser; it is not an independent Lean semantics
proof. This client does not add any beta representation assumption.

The runner checks producer sources, objects, logs, direct dependency guards
and overlay links. These are point observations with inherited ancestry, not
a full transitive or dynamic dependency trace. Each Lean invocation uses
`-M2800`, one thread and a 120-second limit, with 4 GiB monitored RSS,
10 GiB available-memory floor and 5 GB free-disk precheck. The upstream
syntax provider retains the 4,000,000-heartbeat option; these stages add none.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
coordinate-retry producer passed independent terminal audit. After independent
prelaunch review, attempt 01 failed with author-observed outer session `91309`
exit 1: the first module's `Dc2_eval` left a numeral-embedding goal and its
report contains `sorryAx`. See `attempt01/README.md`; the [independent failure
audit](../../reviews/nine-sharing-sign23-transfers-terminal-independent/README.md)
passed and the packet is frozen. No transfer, assembled bridge or endpoint is
claimed here.
