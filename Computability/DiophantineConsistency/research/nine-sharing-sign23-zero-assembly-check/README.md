# Sign23 forward/reverse zero assembly guarded check

This two-stage candidate proposes sign23→sign24 and sign24→sign23
pointwise zero directions using the checked natural Delta lift and the
14-row transfer retry. The first stage enumerates 15 old residuals and the
second enumerates 14 new residuals. No beta-port premise is needed for this
particular substitution; any premise inherited from earlier reductions is
not discharged by this client.

The guard checks the captured transfer-retry base, source and manifest pins,
the assembly generator and external candidate hash, producer objects, logs,
direct guards and overlay links. These are point observations, not a
complete transitive or dynamic ancestry trace. It retains `-M2800`, one
thread and 120 seconds per Lean invocation, a monitored 4 GiB RSS cap, 10 GiB
available-memory floor and 5 GB disk precheck. The syntax provider retains its
inherited 4,000,000-heartbeat setting; these sources add none.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
transfer retry passed independent terminal audit. After independent prelaunch
review, attempt 01 passed with author-observed outer session `11810` exit 0;
see `attempt01/README.md`. The [independent terminal audit](../../reviews/nine-sharing-sign23-zero-assembly-terminal-independent/README.md)
passed; packet and stage inputs are frozen. Lean/JSON binding, Lean degree
theorem and iPRA endpoint remain separate.
