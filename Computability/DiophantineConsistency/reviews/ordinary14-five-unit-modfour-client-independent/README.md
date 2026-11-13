# Independent review: five-unit mod-four client

**PASS at source and finite-arithmetic scope.** The proposed client passes the
same natural `m,x,k`, `m≥2`, the exact first signed pair, the same four
remaining pairs, and the product equivalence to
`FiveUnitFactsDraft.five_positive_of_direct_first`. Its q/r/t residue shapes
match the argument order and exact formulas of `main_bad`, `aux_bad`, and
`strong_bad`, respectively. The unrestricted fourth pair is the guard, and
no extra restriction on its sign is used.

Independently, modulo four a square is 0 or 1; `a²+4a+3` is 0 or 3;
therefore `Q=(a²+4a+3)(f²−1)` is 0 or 1. The main and strong residues are
among 0,1,2, and the auxiliary residue is 0 or 1. None equals −1 modulo four.
The checker computes these finite residue sets separately, verifies the
auxiliary rearrangement across all 256 residue assignments, pins the exact
source dependencies, and reproduces the author receipt.

This checks neither Lean elaboration nor that any literal graph zero
provides the pair/product, residue-shape and `m≥2` hypotheses. It proves no
74/75 graph equivalence, provider compatibility, iPRA endpoint, or physical
byte/PDF binding. No Lean run was performed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-five-unit-modfour-client-independent/check.py | cmp - reviews/ordinary14-five-unit-modfour-client-independent/observation.json
```
