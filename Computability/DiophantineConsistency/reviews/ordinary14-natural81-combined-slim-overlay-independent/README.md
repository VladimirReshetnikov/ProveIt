# Independent source review: natural-81 combined slim overlay

The [inert overlay](../../research/ordinary14-natural81-combined-slim-overlay/README.md) matches its documented source selection and lexical inventory. Both its checker and this separate receipt reproduce. This verifies source bytes and simple initial import headers only: it does not establish Lean parsing, elaboration, actual dependency resolution, provider/companion closure, axiom closure, an iPRA theorem or physical equation binding.

The independent checker pins the overlay and both source inventories; verifies all 173 original and copied source bytes, the complete module set and no symlink snapshots; and reconstructs each of the six root74 slim rewrites and the two predecessor witness-order edits. It compares all 158 shared snapshots with the original root74 slim snapshots; confirms the other 13 additions are unchanged; parses actual initial simple imports, checks the 173-stage topological order and lexical reachability from the endpoint, and rehashes all 37 directly named qualified project sources. The seven added qualified names are differences in source headers, not resolved or missing Lean object providers. The checker does not expand their transitive dependencies.

There is a further **likely parser hazard** in the selected snapshot: `PartialShift82To74.lean.src` still declares the unescaped identifier `def partial`. The separately proposed [keyword alternatives](../../research/ordinary14-natural-partial-keyword-patch/README.md) rename that declaration and its uses in `PartialShift82To74` and `GraphPredecessors82`; those modules are separate from the two witness-order edits in `Natural81JShift` and `Predecessors82`. This receipt checks the exact 8- and 7-token keyword renames against the overlay snapshots, so the proposed changes compose textually with these witness fixes. It does not produce a combined overlay or run the Lean parser. The existing overlay still selects the original keyword-bearing files and must not be described as containing that later fix.

The source parser in this review is intentionally limited to the observed initial import form. The original candidate receipt is pinned and its broader claims remain subject to the stated source/provider and resource limitations.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural81-combined-slim-overlay-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural81-combined-slim-overlay-independent/result.json
```
