# Equality-to-isomorphism SourceFacts field

`PA194SourceEIQuote` proves the exact standard syntax identity between `sinst tau0 sEI` and the three-universal equality-to-order-isomorphism sentence. `PA194SourceEIField.source_ei` applies the independently repository-replayed closed full-source proof to the exact `SourceFacts.ei` field.

The field holds for a nonempty model of the candidate PRA theory whose induced arithmetic reduct models IΣ₁. This is a model-level internal-provability statement for the full-separation adjunctive source theory. It does not establish the other SourceFacts fields, an iPRA derivation, or a machine/consistency equivalence.

Replay from a clean output directory with:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-ei.sh /home/codex/.codex/worktrees/62ff/Proofs /dev/shm/pa194-source-ei-repo
```

The script rebuilds both included modules, checks the listed repository source and direct object hashes, and rejects Lean errors or `sorryAx` in their reports. The remaining transitive dependencies are imported from the pinned staged build paths in the checker, not all rebuilt by this check.
