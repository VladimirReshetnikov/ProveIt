# Fixed-payload scalar boundary obstruction

`check.py` evaluates only the `R` and `c` dependency cones of the pinned 74-row JSON, with the exact retained compressed/raw beta, MC and shifted MF payloads. Write `beta=q-1`, `L=MC`, `H=MF-beta`. The checker verifies `q=2^(67*8807)`, `beta>=31`, `0<=L,H<beta`, `q=0 mod 4`, and `L=2 mod 4`. These are the retained fixed coefficient payloads; connecting them to Lean's fixed symbolic ports remains a separate proof boundary.

Set `J=1`, `F=3`, `C=q-3` and use the candidate's integer operations. Then `F,C>0`, `F+C=q`, `G=q(q-F)-C=(q-1)(q-3)`, and

```
R = G*(q^2-1)+L+q*((q-1)+H)
  = q^4-4q^3+3q^2+3q+L-3+qH.
```

For all `q>=32`, `L,H<=q-2`, this has `3q<R` and

```
q^4-(R+q^3+q+1)
 = 3q^3-3q^2-4q+2-L-qH
 >= 3q^3-4q^2-5q+4 > 0.
```

The lower bound follows since `G>3` and `q^2-1>q`; the final strict margin follows from `q>=32`. When `q=0 mod 4` and `L=2 mod 4`, the displayed rank formula gives `R=3 mod 4`. Further set `eta=zeta=1`, `s=R+1`; the candidate `Y=q^3*s` and `c=(eta+zeta)*Y+eta` obey `c>2R`. The checker also verifies `R>=67*8807` but does not construct `2^R` or a power-aligned `w`.

This demonstrates that these scalar rank-window, parity and c-size facts, even at the exact retained beta/MC/MF payloads, are insufficient **on their own** to derive `F+C<q`. `K0` does not occur in the evaluated cones and is set to zero only inside the partial evaluator. The selected `w=1` is a placeholder; the script evaluates no full output and does not establish any first/second Pell relation, power alignment, fixed-port zero, fixed-BFS guard failure, 74/75 inequivalence or iPRA statement. Stronger actual graph, Pell, parity/carry and kernel constraints could still force the fixed-BFS guard.

Run `python3 -I -S -B research/trace74-fixed-bfs-scalar-boundary/check.py` from `Computability/DiophantineConsistency`. Source SHA-256 `66bccdcc129b730f4c46befc53d26e7db9baa320da3afe3f8ee9834ff0296772`; captured `observation.json` SHA-256 `2bc1bc720ff7efc6ecb29ddaf823705fcae730415eeceaaedb0cbcff2e0e843b`. This is an exact external calculation, not a Lean theorem.

The [independent audit](../../reviews/trace74-fixed-bfs-scalar-boundary-independent/README.md) recomputed the selected payloads/cones and verified the inequality argument. It does not establish a full graph zero.
