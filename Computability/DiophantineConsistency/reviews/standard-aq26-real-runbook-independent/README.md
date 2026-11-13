# Independent static review of the historical AQ26 launch runbook

`audit.py` checks the runbook's shell and embedded Python syntax, its pinned
parent manifest and task policy, target/report counts, the presence of explicit
terminal-observation and historical-basis gates, and five synthetic negative
controls against the parent-observation checker. It does not launch the real
run or fabricate evidence for it. Run under ordinary Python, not `-O` or
`-OO`; the audit fails closed under optimization.

The receipt records the runbook and tool hashes and the parent state status
observed at the audit point. The state file alone is not evidence that a
process is live or has exited successfully. Package-transitive and dynamic
ancestry, between-observation mutations, real completion and Lean proof
replay remain outside this static review. A fresh parent observation and all
preflight checks are still mandatory immediately before any actual run.

The [receipt](receipt.json), SHA-256
`9a3225236714b03195ba931f29defda7a2fdccb89a43c5326047b1f25e37cb3a`,
was reproduced byte-for-byte in the independently observed audit invocation,
which exited 0. Both optimized-mode controls exited 1 before reading inputs.
At that observation, the parent state said `RUNNING`, and the original
coordinator PID `2782024` was independently observed live. This is a
point-in-time observation, not a parent completion. The reviewed runbook is
the exact byte version committed as `27fe7f8067`.
