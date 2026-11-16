# Multiplication predecessor preservation

`preservePrevious` transports a `mulPrevious` witness from an old graph to an exact graph extension. It is a typed source natural-deduction proof in an arbitrary context and uses only the explicitly supplied exact-extension and predecessor-witness proofs. Together with the separately checked new-edge case it supplies one part of a future multiplication recurrence-extension proof. It does not prove the complete recurrence extension, multiplication totality or any native iPRA theorem.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-mul-previous-preserve.sh "$PWD" /dev/shm/pa194-mul-previous-preserve-repo
```

This incremental source replay checks one axiom report and rejects `sorryAx`, retaining `/dev/shm/pa194-mul-recurrence-new-repo`, `/dev/shm/pa194-mul-result-transport-repo`, and the pinned addition and Foundation overlays.
