# Multiplication step from an existential addition output

`fromEndpoint` eliminates an existential `addOutput` witness and constructs an extended graph with the new multiplication prefix. The proof has explicit equality, empty and adjunction, old/new input domain, input successor, old prefix, endpoint edge and `addOutput` premises. Both the addition-output element and the new graph are actual existential witnesses. The source derivation does not itself establish addition totality, construct the endpoint, perform ordinal induction, prove `SourceFacts.m1`, or establish an iPRA theorem.

From the repository root, run the witness checker with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-addition-witness.sh --out /path/to/fresh-output
```

The checker builds standalone imports in dependency order against the root Lake
workspace. It rejects `sorryAx` and requires the `fromEndpoint` axiom report.
If the output directory already contains checked prerequisite objects, the
checker can reuse them.
