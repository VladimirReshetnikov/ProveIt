# Multiplication recurrence: new-edge case

`mulPrevious` describes a predecessor output in the multiplication trace whose sum with the fixed base is the current output. `newCase` constructs this witness from explicitly supplied domain/successor facts, the old endpoint edge, the exact graph extension, the addition result for the new output, and source equality facts. It uses predecessor uniqueness, preservation of the old edge and the separately checked `addResult` output-equality transport. Its result is a typed Foundation natural-deduction proof in an arbitrary context.

This covers the new-edge branch only: old-edge preservation, the complete recurrence, existence of the addition output and extended graph, induction and full `m1` remain open. It does not assert an iPRA theorem.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-recurrence-new.sh "$PWD" /dev/shm/pa194-mul-recurrence-new-repo
```

The incremental checker rebuilds this source, rejects `sorryAx`, and verifies two axiom reports, using retained dependencies including `/dev/shm/pa194-mul-result-transport-repo`, retained addition-graph objects, and Foundation overlays.
