# Independent review: 70/84 standard-iPRA endpoint

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
It verifies the exact orientation and formulas of both standard-iPRA
derivability statements for the positive-shifted literal 70/84 syntax at
`CurrentWindowCarry2011.ports`: one uses intuitionistic negation of the mapped
native ZFC-refutation predicate, and the other uses Foundation's mapped
Gödel–Gentzen translated consistency sentence. These Lean theorems witness
existence of internal derivations; neither proves either side on its own.

The polynomial bridge composes the checked same-valuation 70/84 ↔ 67/94
all-model lemma with `FreshCarrier94.bridge94`. The latter has an existential
witness-changing reverse step; the composition does not assert that a
70/84 solution and a maintained 65/150 solution use identical coordinates.
The external graph/degree audit and literal row comparison remain separate
from the Lean object-language theorem.

The checker verifies actual outer session 92210 and its child exit, three
exact axiom reports, output object and all 800 recorded direct/nested guard
slots. It verifies the selected model-join and 67/94 endpoint objects and
reruns their independent reviews with matching results. The recorded provider
is not a fresh independent second base rebuild; package-transitive, dynamic
and between-observation ancestry remain inherited. No Lean replay was run in
this audit.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary70-84-ipra-independent/check.py
```
