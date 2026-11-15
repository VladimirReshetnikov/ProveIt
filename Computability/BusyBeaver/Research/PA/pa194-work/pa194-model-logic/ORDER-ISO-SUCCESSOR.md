# Extending an order isomorphism to successor ordinals

This source-natural-deduction port of the vendored `RelationalIsoSuccessor*` construction adds the pair of predecessor endpoints to an existing order-bijection graph and checks all graph-entry, typing, totality, injectivity, and order clauses. `orderIsoSuccessor` derives an isomorphism between displayed successor ordinals from an isomorphism between their predecessors, under explicit source equality, empty-set, adjunction, domain and successor assumptions.

This package does not itself prove the translated PAeq successor-congruence axiom, the corresponding internal proof-code graph, or a guarded compiler.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-order-iso-successor.sh "$PWD" /dev/shm/pa194-order-iso-successor-repo-NEW
```

The checker rebuilds thirteen source modules and a five-report axiom audit against the repository-replayed inverse-rule and unified source-syntax objects and the other explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
