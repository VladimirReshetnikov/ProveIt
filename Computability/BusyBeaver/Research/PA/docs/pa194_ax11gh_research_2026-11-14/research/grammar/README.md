# Joint AX11GH / AX11GHS grammar searches

These are new, completed stochastic searches in a specified decoder family; neither established a 193-state blank-start machine or any general lower bound.

| Fixed part | Seed | Time allocation | Proposals | Accepted | Qualifying hits | Best effective reader score |
|---|---:|---:|---:|---:|---:|---:|
| AX11GH | 202611142377 | 420 s | 2,373,130 | 175,774 | 0 | 60 |
| AX11GHS, after the fixed 41/330 fold | 202611142459 | 420 s | 3,119,627 | 235,581 | 0 | 60 |

Each input contains 134 effective fixed controls. A reader score of 59 would nominate a 193-state table; 60 corresponds to 194. `summary.json` and the complete logs record the observed results. A hypothetical hit would still need correct source jump targets, simultaneous fold proofs, universal frame contracts, a blank startup, and logical calibration.

The code adapts the supplied AX11G terminal-grammar search and pricing engine. The new changes use the GH and statically folded GHS fixed tables, enable independent parameter permutations in the six unrestricted heads, and give two- and four-increment macro terminals their actual word lengths before applying the head intervals. Shared subtree rotations change all shared occurrences. Near the frontier the screen checks simultaneous compatibility of disjoint local history folds. Structural penalties guide exploration and are not proof certificates.

The sole initial word is the exact 190-token new AX emitter. The head intervals are 18..34, 35..53, 54..69, 70..85, 86..101 and 102..120 in its expanded macro word. Permutations change the three parameter-copy terminals within a head; they do not silently permute the guarded tail. The retained finite source/template checkers apply to the accepted machines, not every exploratory seed.

From this directory, with a C++17 compiler:

```sh
c++ -O3 -std=c++17 search.cpp -o /tmp/pa194-grammar-search
/tmp/pa194-grammar-search templates.txt leaf_attrs.txt /tmp/gh-search 420 202611142377
/tmp/pa194-grammar-search hs_templates.txt leaf_attrs.txt /tmp/ghs-search 420 202611142459
```

The exact fixed-row input tables, leaf attributes, C++ sources, complete logs, empty hit CSVs and final retained seed grammars are included. Wall-clock stopping makes iteration counts dependent on execution speed; rerunning the same seed is not promised to reproduce the exact final pool. The accepted constructions are frozen and do not depend on rediscovering any stochastic winner. Original compiler/runtime licenses are preserved under `../../construction/licenses/`.
