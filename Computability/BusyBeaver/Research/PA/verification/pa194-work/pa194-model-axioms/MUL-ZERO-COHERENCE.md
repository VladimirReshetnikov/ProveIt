# Multiplication coherence at zero

The source proofs first show that an actual multiplication prefix at a zero input has output equal to its displayed zero, using graph domain/functionality and source equality. They then open an arbitrary `mulResult` witness to show its output is zero. Finally, `zeroCoherence` proves that products of isomorphic inputs are isomorphic when the first input is zero, using the checked zero-transport and empty-order-isomorphism theorems. The proofs use the actual relations and explicit source equality; they assume no canonical empty representative or graph restriction.

This is the base case of multiplication coherence, not its successor/induction case, `sM3`, or a native iPRA theorem.

From the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-mul-zero-coherence.sh "$PWD" /dev/shm/pa194-mul-zero-coherence-repo
```

The incremental checker rebuilds three sources in one output, rejects `sorryAx` and checks four axiom reports. It retains the repository-rebuilt `/dev/shm/pa194-source-m1-chain-repo`, order-isomorphism source objects, and previously built addition/Foundation dependencies.
