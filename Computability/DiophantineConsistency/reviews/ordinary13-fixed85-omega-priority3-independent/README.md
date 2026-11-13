# Independent review: priority-3 Omega alternatives

The author receipt reproduces. This review covers only the three pinned
priority-3 alternatives, their exact source deltas, and their bounded lexical
consumer closures. No Lean build, tactic elaboration, provider override,
compiled-object selection, axiom report or endpoint validation was performed.

For `Residue90FirstNormGap`, the original graph definition is
`k=(v9+1)+(v10+1)`. The alternative derives 2≤k by adding the two independent
1≤v+1 bounds. For `Residue90CompactGraphGamma`, `q=1+J*beta` and the
existing hb states J*beta>0, so adding 1 to 1≤J*beta gives 2≤q. For
`Residue90GammaModel`, nonnegativity of q³+q yields
`R≤R+(q³+q)`; adding 1 gives `R+1≤R+q³+q+1`. These are the exact inequalities
needed at the three original tactic locations.

The checker reconstructs every byte of each alternative from its pinned
original using just the stated proof replacement and any added NormNum/Ring
imports. Namespaces and all theorem headers remain identical. The explicit
`add_le_add`, numeral normalization and associativity rewrites have the
correct mathematical orientation, but have not been checked by Lean in the
abstract model. Calling the original `omega` a lexical elaboration hazard
does not prove an actual failure.

Within the pinned fixed-85 lexical graph, the three reverse-reachable local
closures have sizes 49, 50 and 52 respectively, including the replaced module.
A future isolated selection must map each alternative to its *original*
logical module name and prevent the historical same-namespace source/object
from being selected as well. The renamed inert files do not perform that
rewiring. These counts do not include unscanned external transitive imports,
object/dynamic library collisions or authenticated provider ancestry. No
concrete mathematical or source-interface mismatch was found.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-fixed85-omega-priority3-independent/check.py | cmp - reviews/ordinary13-fixed85-omega-priority3-independent/receipt.json
```
