# Direct-ordinate 86-operation candidate

This is an unbound **candidate graph**, not an established equivalent equation. Starting from the pinned 87-operation graph, the auxiliary signed ordinate is `V = f²*(T*c − R) − c` and the old positive offset witness appears only in `y_old = V + u_old`. The candidate deletes that addition and instead uses a new positive witness `y` directly in the auxiliary factor:

```text
old: y_old = V + u_old
     Fa = y_old² − Q*(y_old² − V²)
new: Fa = y² − Q*(y² − V²)
```

The new graph has 86 live binary operations (47 multiplication, 21 addition, 18 subtraction), with all 13 witnesses and four symbolic ports live. This counts the unshifted output DAG and is not a degree certificate or minimality claim. [`audit.py`](audit.py) pins the 87-row parent, checks topology and output liveness, confirms the old offset has no other use, and verifies the exact integer-polynomial identity for the auxiliary factor under the **signed** substitution `u_old = y − V`; a sign mutation is rejected. The generated [candidate](candidate.json) SHA-256 is `e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f`. Normal Python and `python -O` produce identical [audit output](AUDIT.json).

The substitution by itself does **not** prove that the two equations have the same zero set over natural numbers: `y − V` must correspond to a strictly positive old offset, and the old signed ordinate can be negative. The independently replayed conditional [ordinate-gap lemmas](../../reviews/adaptive-ordinate-gap-independent.md) show one route: assuming the auxiliary Pell norm with coefficient at least two and the signed rank residue `SignMod c |V| R`, `2 ≤ R`, `2*R < c`, they give `|V| < y` and reconstruct a positive offset whose signed ordinate equals `y`. These assumptions have **not yet been derived from this changed literal equation**. The old-to-new direction, the actual factor/unit extraction for the modified graph, the new-to-old direction, literal Lean binding, and any HA/PRA proof transfer remain open. No 86-operation equivalent equation is claimed here.
