# Addition coherence with predecessor witnesses

`additionCoherenceOutputs` obtains isomorphism of two successor results from an explicit coherence induction-hypothesis frame and two explicitly assumed `addPredecessorResult` witnesses. `additionCoherenceOutputRight` performs the one-witness part. This does not extract predecessor witnesses from arbitrary addition traces and does not prove `SourceFacts.a2`.

The typed `addPredecessorResult` syntax is introduced here; a later port of `RelationalAdditionRestrictionEndpoint` should import and reuse it.

Replay: `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-addition-coherence-witness.sh /home/codex/.codex/worktrees/62ff/Proofs /dev/shm/pa194-add-coherence-witness-repo`. The direct Syntax/Rules/Frame objects are repository-rebuilt and pinned. The lower retained staged closure still carries the separately documented provenance caveat.
