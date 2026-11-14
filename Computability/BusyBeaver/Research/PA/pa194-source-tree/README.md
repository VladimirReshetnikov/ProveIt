# PA194 formal source tree

`generate.py` combines the pinned upstream `PA196/Program.lean` with the
original PA194 packet's pinned 68-rule separate-head AX grammar: it replaces
the upstream `x67` definition with the grammar root. It verifies the source
file against both its hash and the archived reference, checks the grammar
hash and its acyclic dependency graph, and emits a Lean source tree. The
small grammar-to-Lean translator is an explicit source-generation boundary.

`PA194SourceFacts.lean` uses the imported formal tree and resolver to check
3,673 source sites, 4,780 branch outcomes, and the exact entry site 25
(path `100000`, decrement register 8, successors 27 and 26). These are
standard-Lean source facts, not an internal PRA/iPRA simulation or a
consistency theorem. Check from the repository root with:

```sh
Computability/BusyBeaver/Research/PA/pa194-source-tree/check.sh
```
