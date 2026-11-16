# Multiplication recurrence under exact graph extension

`recurrenceShift` checks the source syntax under shifting. `extension` constructs a typed Foundation derivation of the complete universally quantified multiplication recurrence for the extended graph. Its `Inputs` explicitly supply the extended input domain, the old-to-new input successor, the old endpoint edge, the exact graph extension, the addition result used for the new output, and the old graph's recurrence; it additionally takes `FormulaEquality`. The proof applies the separately checked pointwise old/new-edge construction at all three universally quantified indices.

This proves recurrence preservation only: the other prefix clauses, existence of the addition output and the extended graph, ordinal induction, full `SourceFacts.m1`, and native iPRA transfer remain open.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-recurrence-full.sh "$PWD" /dev/shm/pa194-mul-recurrence-full-repo
```

The incremental checker rebuilds two sources, rejects `sorryAx`, and checks three axiom reports. It retains `/dev/shm/pa194-mul-recurrence-at-repo` and previously built old/new-edge, addition-graph, and Foundation objects.
