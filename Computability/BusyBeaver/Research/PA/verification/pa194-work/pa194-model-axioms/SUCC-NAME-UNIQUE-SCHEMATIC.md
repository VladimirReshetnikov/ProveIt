# Schematic uniqueness of successor names

`namingSchema_valid` formalizes a first-order implication for arbitrary unary P and binary E and S. A name of P is an element E-related to a P-value; a name of a successor is E-related to an S-output of a P-value. If P-names are unique up to E, every P-value is E-related to itself, E is symmetric and transitive, and S preserves E between inputs, then successor-names are unique up to E. `namingCertificate` supplies every internal instance as a source proof via the schematic proof transformer.

This theorem has no identification of P, E or S with the PA194 value, order-isomorphism or successor codes, and does not establish the corresponding source premises. It therefore does not yet prove `NameFacts.uSucc` or a native iPRA or machine result.

The checker rebuilds the source and verifies its source and direct object pins; transitive imports remain prebuilt. From the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-succ-name-unique-schematic.sh "$PWD" /dev/shm/pa194-succ-name-unique-schematic-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
