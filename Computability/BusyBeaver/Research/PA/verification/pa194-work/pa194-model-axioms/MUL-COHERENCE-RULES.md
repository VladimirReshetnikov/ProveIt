# Multiplication coherence specialization rules

`atIndices` specializes the five universally quantified variables of the typed multiplication-coherence predicate, `shift` transports it under an eigenvariable shift, and `use` applies the specialized implication to explicit source domain, isomorphism and multiplication-result premises. These are ordinary typed Foundation derivation constructors with all premises explicit. They do not establish coherence, its successor induction case, `sM3` or native iPRA transfer.

From the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-coherence-rules.sh "$PWD" /dev/shm/pa194-mul-coherence-rules-repo
```

The incremental checker rebuilds both sources, rejects `sorryAx`, and checks three axiom reports. It retains the repository-rebuilt `/dev/shm/pa194-mul-coherence-base-repo`, repository zero-coherence and `m1` chain, and earlier addition/Foundation objects.
