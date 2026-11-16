# Addition recurrence and prefix restriction

These conditional source proof transformations retain addition-trace predecessor witnesses and the recurrence/prefix clauses under an explicitly supplied inclusive graph restriction and the displayed ordinal, successor and equality premises. They do not construct the restriction or prove a2.

Replay: `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-addition-restriction-prefix.sh /home/codex/.codex/worktrees/62ff/Proofs /dev/shm/pa194-add-restriction-prefix-repo`. Direct graph inputs are pinned to repository builds; the lower retained staged addition closure remains separately audited. The older lower closure is prioritized to avoid a previously observed Lean import-time crash in a mixed path order.
