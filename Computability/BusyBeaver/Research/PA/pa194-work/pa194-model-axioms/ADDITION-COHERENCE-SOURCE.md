# Strong model-level full-source addition coherence

The five modules assemble the pointwise successor case, quantified successor step, uniform ordinal induction, and a model-level full-source proof of the strong global addition-coherence statement. Its source premises are discharged by the equality/empty/adjunction/intersection, graph Separation and exact negated-property Separation suppliers. It does not itself prove the exact `SourceFacts.a2` field; the separate guarded target/quote branch supplies that conversion.

Replay: `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-addition-coherence-source.sh /home/codex/.codex/worktrees/62ff/Proofs /dev/shm/pa194-add-coherence-source-chain-repo`. Direct predecessor and zero-case inputs are pinned to repository-rebuilt objects. The retained older lower addition closure is prioritized to avoid a recorded mixed-path import crash and retains its byte-provenance caveat.

The guarded wrappers `PA194AdditionA2Source.source_a2` and
`PA194AdditionA3Source.source_a3` now provide the exact `SourceFacts.a2` and
`sA3` premises in each PRA model with a classical IΣ₁ arithmetic reduct.
Each converts a source derivation back to the matching guarded target by
the checked quotation and instantiation lemmas.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms
bash "$dir/check-addition-a2-source.sh" "$PWD" /dev/shm/pa194-add-a2-source-new
bash "$dir/check-addition-a3-source.sh" "$PWD" /dev/shm/pa194-add-a3-source-new
```

The two replays pin the repository-built coherence and target modules.
The graph, Separation and arithmetic foundations retain their earlier stages.
