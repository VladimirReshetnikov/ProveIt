# Conditional guarded interpretation

`PA194GuardedInterpretationReduction.lean` assembles `Interpretation` from the five-case axiom reduction, the unconditional source inhabitation proof, and the Leibniz witness construction. It assumes `TermFacts` for the full source theory, the five remaining fixed typed axiom suppliers, and a translated closed-induction supplier for every internally valid arity-one PAeq property (including nonstandard codes). `refutation_of_remaining` transports an internal ordinary PAeq proof of falsity to a source-theory proof of falsity under exactly those assumptions.

From the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-interpretation-reduction.sh "$PWD" /dev/shm/pa194-interpretation-reduction-repo-NEW
```

The replay compiled the new module and its two axiom reports without `sorryAx`. It uses the repository-built `/dev/shm/pa194-interpretation-axioms-repo`, `/dev/shm/pa194-source-inhabited-repo`, `/dev/shm/pa194-leibniz-repo` and other retained overlays enumerated in the checker; Foundation and package objects are prebuilt. It is a model-uniform Lean result for candidate PRA + classical IΣ₁, not an object-level native iPRA proof. In particular, it establishes neither the assumed suppliers nor physical scheduler synchronization.
