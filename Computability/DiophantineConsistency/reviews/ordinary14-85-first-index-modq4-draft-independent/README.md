# Independent source review: 85 first-index congruence

The direct 85 residue and q⁴-magnitude clients use the same positive valuation
and graph zero. The q⁴ modulus is positive. From `Y=q³*slot7`, the explicit
natural witness `4*X*q²*slot7²*s` proves `q⁴ | 4*X*Y²*s` without assuming
q divides X. The magnitude-to-modulo order, multiple removal and final symmetry
match the stated congruence.

The checker pins both interfaces, replays author and independent dependency
receipts, and checks bounded congruences including both rank-difference signs
and q not dividing X. These controls are not graph zeros. This is source
review only; no Lean elaboration, modulus removal, exact index, provider
compatibility, external-file binding or iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-first-index-modq4-draft-independent/check.py > /tmp/first-modq4-85-independent.json
cmp /tmp/first-modq4-85-independent.json reviews/ordinary14-85-first-index-modq4-draft-independent/result.json
```
