# Addition-output equality transport

`outputTransport` takes an explicit source equality `a = b` and a source derivation of `addResult x base a`, and produces a source derivation of `addResult x base b` using `FormulaEquality.substituteOne`. It works in an arbitrary source context with a supplied `FormulaEquality`; no isomorphism congruence, multiplication recurrence, full `m1` field, or iPRA theorem is claimed. It can discharge the changed-output-equality subcase of a multiplication-prefix graph extension.

Run from the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-mul-result-transport.sh "$PWD" /dev/shm/pa194-mul-result-transport-repo
```

This incremental source replay checks one axiom report and rejects `sorryAx`. It retains previously built dependencies, including `/dev/shm/pa194-forward-mul-zero-repo` and Foundation overlays.
