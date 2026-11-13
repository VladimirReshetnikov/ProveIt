# Independent review: eta/zeta-natural unit and norm bridge

The generated source transcribes all 85 rows of the pinned probe with the correct 13 inputs and four arbitrary signed ports. Its exported `k` is `eta+zeta`, and its `r0` is exactly `(k-R)-1`. A separate hash-consed expression-tree check verifies the exact grouping of the first, main, auxiliary and strong factor patterns, the output factor product, and all residual shapes; these are structural identities for the proposed `rfl` statements, not merely evaluated examples. The first-pattern exclusion was independently checked for all 1,024 residue combinations modulo four, and its displayed `first_bad` and `he` expressions have the same syntax.

The resulting proposed four unit factors and signed residual norms do not require the ports to be natural or beta to be positive. They are consistent with the two known signed-port full zeros, which have all four factors +1. The modular patterns themselves are not a compact-port obstruction or a zero map.

The existing `FreeJ13` and magnitude/unit interfaces, the `rfl` reductions, finite-model arithmetic, casts and all proof terms remain unelaborated. Graph/model/provider closure and an endpoint are not established. The checker reproduces the author's receipt and pins its inputs; from `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-eta-zeta-natural-unit-norm-structural-independent/check.py | cmp - reviews/ordinary13-eta-zeta-natural-unit-norm-structural-independent/receipt.json
```
