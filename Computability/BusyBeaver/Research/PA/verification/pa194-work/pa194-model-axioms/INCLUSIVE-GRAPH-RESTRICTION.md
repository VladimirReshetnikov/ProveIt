# Inclusive source graph cut

Ports the first module of the vendored inclusive graph-restriction derivation to current shared source syntax. It defines the inclusive domain, entry predicate, graph cut and restriction, and gives natural-deduction introductions and eliminators for the entry witnesses and the cut, under the explicitly assumed separation instance. It does not yet derive the graph-restriction edge laws, addition predecessor extraction, or SourceFacts.a2.

Replay: `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-inclusive-graph-restriction.sh /home/codex/.codex/worktrees/62ff/Proofs /dev/shm/pa194-inclusive-graph-restriction-repo`. The direct import source and the repository-rebuilt import object are pinned. Other transitive dependencies are loaded from staged paths in the checker.
