# Optional decoder searches below 194

These two heuristic runs searched binary AX associations, seven-head emission
orders, and independent parameter permutations using the **actual PA194NS fixed
controller rows after its existing controller fold**. They found no effective
AX reader cost below 60, hence no screened state count below `134 + 60 = 194`.

The source is derived from the supplied PA194Q `logic_anneal.cpp` and
`screen.cpp`, extended with tracked seven-head reordering and parameter changes
at the correct moving head boundaries. The low-temperature run uses the same
mutation family with a different annealing temperature. Attribution to the
supplied ProveIt search code is retained; these general search ideas are not
claimed as new mathematical results.

`ncs_seeds.txt` freezes all fixed rows and the three initial trees: primary67,
alternative68, and the exchanged quantifier-distribution head. `leaf_attrs.txt`
freezes the macro path constraints. No repository or network access is needed
to repeat the searches from these inputs.

```sh
c++ -O3 -std=c++17 ordered_search.cpp -o /tmp/pa194ns-ordered
/tmp/pa194ns-ordered ncs_seeds.txt leaf_attrs.txt /tmp/pa194ns-run1 600 202611132138
c++ -O3 -std=c++17 ordered_plateau.cpp -o /tmp/pa194ns-plateau
/tmp/pa194ns-plateau ncs_seeds.txt leaf_attrs.txt /tmp/pa194ns-run2 480 202611132141
```

The observed runs made 9,027,164 and 8,332,404 proposal slots, respectively,
for a total of 17,359,568. These counts include skipped, repeated and rejected
mutations. They are not counts of distinct complete Turing machines. A fixed
time limit also makes the number of proposals hardware-dependent.

The screen counts compatible previous-bit folds within its restricted template
and penalizes invalid scanner/structured-leaf attributes. A favorable score
would still require exact source semantics, universal physical verification,
complete blank initialization, and a logical calibration. No such sub-194
candidate was produced. The search results imply no optimality or state lower
bound. The accepted PA194NS construction does not depend on rerunning them.
