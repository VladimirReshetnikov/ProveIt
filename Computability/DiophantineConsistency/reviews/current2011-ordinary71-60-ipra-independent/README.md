# Independent review: 71/60 standard-iPRA endpoint

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
It verifies the exact orientation and formulas of both standard-iPRA
derivability statements for the positive-shifted literal 71/60 syntax at
`CurrentWindowCarry2011.ports`: one uses intuitionistic negation of the mapped
native ZFC-refutation predicate, and the other uses Foundation's mapped
Gödel–Gentzen translated consistency sentence. These Lean theorems witness
existence of internal derivations; neither proves either side on its own.

The source's polynomial bridge composes the checked same-valuation 71/60 ↔
67/94 all-model lemma with `FreshCarrier94.bridge94`. The latter has an
existential witness-changing reverse step; the composition does not assert
that a 71/60 solution and a maintained 65/150 solution use identical
coordinates. The external graph/degree audit and literal row mapping remain
separate from the Lean object-language theorem.

The checker verifies the actual successful child and outer session 77676,
three exact axiom reports, output object, and all 525 recorded direct/nested
guard slots. It verifies the selected model-join and 67/94 endpoint objects
and reruns their independent reviews with matching results. The latter chain
includes source/graph and fixed-byte degree evidence. The recorded provider
is not a fresh independent second base rebuild; package-transitive, dynamic
and between-observation ancestry remain inherited. No Lean replay was run in
this audit.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary71-60-ipra-independent/check.py
```
