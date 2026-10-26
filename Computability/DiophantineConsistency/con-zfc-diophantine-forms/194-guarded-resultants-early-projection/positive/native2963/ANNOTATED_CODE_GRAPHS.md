# Direct polynomial graphs for local numeric-checker operations

`Lean/DiophantineConsistency/AnnotatedCodeGraphs.lean` supplies explicit
`GraphRep` data for elementary operations of the annotated numeric checker.
These are direct arithmetic graphs with literal expression data and checked
natural-number semantics; they are separate from expanding the corresponding
`ScalarPRCode` programs into primitive-recursion traces.

A useful local simplification represents predecessor with no extra natural
witnesses. For natural input `n` and output `o`, the equation is

```text
(n² + o²) (o + 1 − n)² = 0.
```

If its first factor vanishes, both natural coordinates are zero. Otherwise
its second factor forces `o+1=n`. This covers exactly `o=Nat.pred n`, including
zero. The literal graph polynomial has degree four. The numeric atom
constructor also needs no extra witnesses: its equation is `o=n²+1`, because
`Nat.pair 0 n=n²` for every natural `n`.

The remaining graphs combine the supplied square-pairing inverse-coordinate
graphs with direct input substitution and the one-slack equality-branch
constructor. The following witness counts are proved for the actual data:

| Graph | Extra natural witnesses |
| --- | ---: |
| Predecessor | 0 |
| Tree outer left component | 4 |
| Tree outer right component | 4 |
| Tree left child | 5 |
| Tree outer kind | 14 |
| Guarded workspace-list head | 11 |
| Guarded workspace-list tail | 9 |
| Numeric atom constructor | 0 |
| Numeric fork constructor on two inputs | 8 |

Counts include all intermediate values introduced by the actual composition
constructors. They are not counts for a full proof checker or for a closed
consistency equation. Tree kind checks only an outer constructor; it does not
establish recursive syntax validity.

`Lean/checks/AnnotatedCodeGraphs.lean` reduces the actual predecessor and atom
graph expressions on valid and invalid small inputs, checks the representation
interfaces, verifies every published witness count, and audits their axioms.
The module imports neither the old proof enumerator nor a Jones encoding.

The bounded list-lookup graph, whole syntax-computation table validator,
seventeen-rule arithmetic validator, sealed-axiom expansion, and complete
numeric checker graph remain separate obligations. No claim about internal
model-omega verification or a smaller closed equation follows from these
local graph data alone.
