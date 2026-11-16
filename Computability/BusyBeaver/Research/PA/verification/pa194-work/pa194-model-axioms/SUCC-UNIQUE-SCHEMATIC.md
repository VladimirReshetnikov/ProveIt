# Schematic uniqueness through relational composition

The standard first-order sentence `schema` says: if all elements satisfying a unary predicate are E-related, and a binary relation sends E-related inputs to E-related outputs, then all outputs reachable from that predicate through the relation are E-related. `schema_valid` proves this in every structure; `certificate` uses the existing schematic derivation machinery to obtain a proof of every internal predicate instance in every Δ₁ internal theory.

This is an auxiliary logical certificate. It does not identify the unary predicate, E or the binary relation with the PA194 term-value, order-isomorphism or successor formulas; nor does it derive their uniqueness or coherence premises from `NameFacts.uSucc`. Therefore it does not prove the `uSucc` field or any native iPRA or machine equivalence.

The checker rebuilds the source and verifies the source and direct imported object hashes; transitive imports remain prebuilt. From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-succ-unique-schematic.sh "$PWD" /dev/shm/pa194-succ-unique-schematic-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
