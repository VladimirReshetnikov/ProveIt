# Binding the free-X graph and forward map

This finite checker binds the [free-X symbolic zero](../p64-free-x75-symbolic-full-zero/README.md) to the pinned 76Y graph. It authenticates the original 76-row graph and the three frozen author packet files, checks that the `X := w*q` gate feeds exactly `E` and `b0`, deletes that gate and substitutes `w` in those two operands. All 75 retained rows are compared with the verifier's separate row list and checked live in the output.

It separately verifies 21 expanded semantic formulas at explicit cut points, covering the first norm, carrier, rank, transport, strong and auxiliary residuals, and final output. Expansion uses only associativity and commutativity of addition and multiplication; subtraction is ordered. The canonical JSON hash of the resulting 75-row graph is recorded in `result.json`.

For the forward map, the verifier checks every direct graph use of `w` and `z`: `w` appears only in the original X gate and `K0+w`; `z` appears only in the transport right side. An independent integer-polynomial calculation verifies the identity

```
(K0+q*w) C − F − (z+w*C)(q−1)
  = (K0+w) C − F − z(q−1).
```

A wrong-sign negative control is also rejected. Given an original positive zero, its transport equation has `(K0+w)C=F+z(q−1)>0`, so `C>0`; the map `w_new=q*w`, `z_new=z+w*C` is therefore positive and preserves the other coordinates and all residuals. This order/positivity step is a mathematical argument, not established by the polynomial calculator. The construction is a forward witness map; the free graph's exhibited zero has `q ∤ w`, so the direct pointwise inverse is unavailable.

The checker does not expand the huge zero witness or prove existence equivalence, a fixed-compact44 conclusion, an iPRA theorem, or full source ancestry. It is a finite structural check and not a Lean theorem.

Run from any directory:

```
python3 -I -S -B path/to/p64-free-x75-graph-binding/check.py
```

The output and hashes are frozen in `result.json`. Existing author packet files are read and authenticated but not changed.
