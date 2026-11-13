# Binding the free-f² graph and forward map

This finite check binds the [free-f² symbolic zero](../p64-free-fsquare75-symbolic-full-zero/README.md) to the pinned 76Y graph. It authenticates the original 76 rows and the unchanged three-file author packet; confirms that `f` occurs only in `f2 := f*f` and that `f2` feeds exactly `f2_minus_one` and `f2_quotient`; removes the square row; and supplies the independent positive coordinate `F2` in those two places. All 75 retained rows are compared with the verifier's explicit separate row list and checked live in the output.

The verifier separately compares 21 expanded semantic expressions at named cut points, covering both norms, main carrier, rank, transport, auxiliary expression and final sum of squares. It flattens and sorts only addition and multiplication for associativity and commutativity; subtraction stays ordered. The resulting 75-row graph's canonical JSON hash is recorded in `result.json`.

The use analysis makes the forward substitution `F2=f*f` preserve every graph row over a commutative ring, with positive `F2` on positive natural inputs. As an additional finite check, the script compares all six named residual/output values at 120 deterministic integer valuations. This is not a Lean theorem and finite examples are not the proof of the ring identity.

The graph binding does not expand the huge witness or prove its arithmetic argument. It does not establish a reverse witness map, positive-zero existence equivalence, any fixed-compact44 conclusion or iPRA endpoint. The separate symbolic witness has `F2` nonsquare and therefore blocks the direct pointwise inverse at its particular natural ports.

Run from any directory:

```
python3 -I -S -B path/to/p64-free-fsquare75-graph-binding/check.py
```

The deterministic result and file hashes are frozen in `result.json`. The author packet is authenticated and is not changed.
