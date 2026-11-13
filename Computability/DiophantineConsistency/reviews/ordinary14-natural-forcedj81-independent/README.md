# Independent review: forced-J natural 81-operation graph

The [candidate](../../research/ordinary14-natural-forcedj81/README.md) is an external zero-existence reduction from the [82-operation parent](../../research/ordinary14-root74-natural-forced82/README.md) under `beta>0`, `K0>0`, with arbitrary integer `MC` and `MF`. It has 14 natural inputs, an explicit 81-operation graph, and exact specialized degree 107 at the authenticated compact ports, conditional on the independently reviewed parent's degree upper bound. The count is an upper bound, not a minimality claim. This review does not establish Lean elaboration, iPRA derivability, provider compatibility, or PDF binding.

The complete graph edit removes precisely `J=n_J+1` and replaces each use of `J` with `n_J`, so the new polynomial at `n_J=J` equals the parent's polynomial at `n_J=J-1`, with all other values unchanged. A parent zero maps forward by incrementing its natural coordinate. For the reverse map, the final output is a product of five integer factors minus one; at a zero each factor is an integer unit. If `J=0`, then `qm=0`, `q=1`, `X=w>=1`, `qF=-n_F<=0`, `alpha>=1`, and `C=qF-alpha<=-1`. The actual graph has `guard=C*(X+K0)-n_F-qm*n_h`; at `J=0` this equals the candidate's displayed `C*(X+K0)+qF-qm*n_h`, and is at most `-2` because `K0>=1`. Hence it cannot be a unit, so `J>=1`; the natural predecessor gives the parent zero. This argument does not use the factor-sign or negative-Pell exclusions at `J=0`. `beta>0` is retained as a parent hypothesis.

The independent checker verifies the exact parent-to-candidate edit, topology and liveness, and the rows for the guard and product. It authenticates all four gzip/raw ports against the pinned P72 and P115 bindings and independently verifies `K0>0`. Its 107th finite difference on the ray with all inputs equal to `x`, modulo 1,000,000,007, has leading coefficient 419359493. This proves the degree lower bound; the matching upper bound is inherited from the parent because the substitution is affine. It is distinct from the candidate's coefficient-propagation method. Neither finite checking nor the parent's external assumptions constitute a Lean proof.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-independent/result.json
```
