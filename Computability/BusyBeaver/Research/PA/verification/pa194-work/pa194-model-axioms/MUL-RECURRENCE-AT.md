# Multiplication recurrence at one graph edge

`recurrenceAt` specializes the actual `mulRecurrence` to any source indices, deriving the prior-value witness from an old edge and an input successor. `extensionAt` combines this with separately checked old-edge preservation and new-edge construction to derive the same witness for any displayed edge of an exact graph extension. It has explicit source equality, domain, input successor, endpoint, addition-result, old recurrence, extension, edge and successor premises. Both are typed Foundation natural-deduction constructions in arbitrary contexts.

This is a pointwise recurrence step. Universal introduction to a whole recurrence, output and graph existence, induction, full `SourceFacts.m1` and native iPRA transfer remain open.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-recurrence-at.sh "$PWD" /dev/shm/pa194-mul-recurrence-at-repo
```

This incremental replay rebuilds two sources, rejects `sorryAx`, and checks two axiom reports. It retains `/dev/shm/pa194-mul-previous-preserve-repo`, `/dev/shm/pa194-mul-recurrence-new-repo`, `/dev/shm/pa194-mul-result-transport-repo` and other pinned addition and Foundation objects.
