# Seven-clause predecessor order-bijection

This adapts the vendored PA196 predecessor-totality and order-bijection proofs to the unified local Foundation syntax, reusing the previously checked local subgraph inheritance lemmas for functionality, injectivity and order preservation. `predecessorOrderBijection` proves that an explicit strict cut h is an order-bijection between displayed predecessors p and q, given the original order-bijection between their successor containers, the two successor relations, the endpoint edge, actual graph entries and exact strict-edge characterization. Both left and right totality are derived.

All the displayed cut, successor and endpoint properties are explicit source-proof premises. This is a Foundation natural-deduction theorem; it does not by itself construct the cut, prove the endpoint edge, prove successor cancellation or establish native iPRA/machine equivalence.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-predecessor-bijection.sh "$PWD" /dev/shm/pa194-predecessor-bijection-repo-NEW` from the repository root. The checker compiles the four modules in one fresh output against hash-pinned prebuilt dependencies, including the repository-replayed predecessor-typing modules. The successful output is `/dev/shm/pa194-predecessor-bijection-replay`.
