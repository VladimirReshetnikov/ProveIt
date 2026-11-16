# Predecessor of a successor multiplication result

This source chain preserves previous-output witnesses, recurrence and prefixes under inclusive graph restriction. It constructs the restriction using the exact open Separation instance, then opens both original multiplication witnesses to prove `PA194MulRecurrenceNew.resultPredecessor`: every product of a successor has a domain-valued predecessor product and an addition result from that product and the base. Premises are explicit source equality, domain of the predecessor, successor relation, the original `mulResult`, and the open inclusive-Separation instance.

This is a structural predecessor theorem, not `sM3`: independent products still require coherence, and the requested reversed addition order requires an addition-commutativity bridge. Full-source discharge and native iPRA transfer remain separate.

From the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-result-predecessor.sh "$PWD" /dev/shm/pa194-mul-result-predecessor-repo
```

The checker rebuilds all eight local sources in one output, rejects `sorryAx` and checks ten axiom reports. It retains the repository-source-replayed `/dev/shm/pa194-add-restriction-inside-repo`, `/dev/shm/pa194-inclusive-graph-properties-repo`, `/dev/shm/pa194-inclusive-graph-rules-repo`, repository inclusive graph edge/base objects, `/dev/shm/pa194-source-m1-chain-repo`, and earlier addition/Foundation objects. This is not a complete source-closure rebuild.
