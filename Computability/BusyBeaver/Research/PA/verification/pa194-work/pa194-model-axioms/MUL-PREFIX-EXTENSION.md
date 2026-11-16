# Multiplication prefix under graph extension

`prefixExtension` constructs a Foundation source derivation of every clause of the extended `mulPrefix`, combining the existing graph-domain, functionality, range and old-edge preservation results with the checked multiplication recurrence extension. Premises explicitly include source equality, the domains of the old input, new input and new output, the input successor, the old prefix, its endpoint edge, the new addition result, and an exact graph extension.

This is conditional on those explicit witnesses. It does not construct the addition output or extended graph, perform ordinal induction, prove `SourceFacts.m1`, or establish native iPRA transfer.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-prefix-extension.sh "$PWD" /dev/shm/pa194-mul-prefix-extension-repo
```

This incremental checker rebuilds one source, rejects `sorryAx`, and checks one axiom report. It retains `/dev/shm/pa194-mul-recurrence-full-repo` and its previously source-replayed graph, addition and Foundation baselines.
