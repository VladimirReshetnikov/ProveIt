# Independent check of the universal 60-graph zero

The literal 60-operation carrier candidate has a standard-integer zero for **every** choice of its four nonnegative integer ports. In the candidate's declared input order the witness is

```text
(n_J, n_F, n_C, n_w, n_s, n_h, n_tau, n_eta, n_zeta, n_gamma)
  = (0, K0, 0, 1, 0, 0, 3363, 1527, 850, 292).
```

Each entry is natural for any natural K0. Thus this candidate also has a zero when the ports are the fixed compact natural numerals. It is not a new equation whose lack of solutions can be used as the desired consistency characterization. This witness does not determine whether the earlier 61-operation graph has a zero, nor prove an existential inequivalence between the two graphs.

Substitution into the exact pinned JSON rows gives `q=X=Y=U=C=1`, `F=K0+1`, and `R=0`. The last equality holds for all beta and masks: the rank factor `q²−1` and the J-multiplied mask term both vanish. The carrier is `C*(X+K0)−F=0`, with `b*h=0`. Moreover

```text
k=2378, ell=2378, c=3905,
a=2, H=11, Delta=15,
shift=292−2377=−2085,
Dstar=(1+2*3905)+11*shift=−15124.
```

The negative intermediate is valid because the graph's subtractions are integer polynomial operations. The exact identities `3363²=1+2*2378²` and `15124²=1+15*3905²` make the normalized first and main residuals zero. Consequently all three squared residuals and the final output vanish.

The direct inverse of the carrier-coordinate rewrite would reconstruct `alpha=q−F−C=−K0−1`, never a positive shifted alpha. This establishes failure of that coordinate inverse at this witness; it does not exclude some other witness map.

The separate checker verifies the original author's receipt and independently evaluates all 60 ordered literal rows using sparse integer polynomials in the four formal port variables. It checks the declared input and port order, the intermediate identities above, and that the output is the zero polynomial. This uses finite exact ring arithmetic and does not assume any value for beta, K0 or either mask. The receipt reproduces from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary10-carrier60-all-ports-second-independent/check.py | cmp - reviews/ordinary10-carrier60-all-ports-second-independent/receipt.json
```

No Lean, build, model transport, provider authentication, axiom audit, or parent-equivalence proof was performed.
