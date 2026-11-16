# Guarded isomorphism transitivity supplier

This source replay checks a typed derivation of domain-guarded transitivity of ordinal order isomorphism, its exact `tHyp sIt` quotation, and its proof in the internal full adjunctive/separation source theory. The typed proof uses actual graph composition; its fixed equality, empty, adjunction, intersection, and composition-Separation premises are discharged by previously built source suppliers. The model wrapper applies to every candidate PRA model with classical IΣ₁; it is not itself a native iPRA proof, the full `SourceFacts` instance, a PA compiler, or physical scheduler correspondence.

From the repository root, run in a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-it.sh "$PWD" /dev/shm/pa194-source-it-repo
```

The checker rebuilds all three local modules from the repository directory, rejects `sorryAx`, and checks five axiom reports. Its `LEAN_PATH` uses retained prebuilt objects, principally `/dev/shm/pa194-name-facts-updated-repo`, `/dev/shm/pa194-composition-source-repo`, and `/dev/shm/pa194-composition-transitivity-repo`, and the retained Foundation workspace. It is an incremental source replay, not a fresh rebuild of the entire dependency closure.
