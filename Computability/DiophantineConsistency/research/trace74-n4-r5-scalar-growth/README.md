# Conditional scalar growth for the `n=4, r=5` branch

This is an ordinary-integer scalar proof certificate, not yet a Lean theorem or graph binding. Let `q≥32`, `X≥32`, `Y≥1`, and let

```text
P = X Y²
k = 128P³+192P²+80P+8
c = 16(Y(X+1)+1)⁴−12(Y(X+1)+1)²+1.
```

If `kY<c`, then **`X>4Y³`**. Indeed `kY≥128X³Y⁷`; with `t=Y(X+1)+1≥1`, the formula for `c` gives `c≤16t⁴`. Since `Y≥1`, `t≤Y(X+2)`, and for `X≥32` the polynomial certificate gives `(X+2)⁴≤2X⁴`. Thus

```text
128X³Y⁷ ≤ kY < c ≤ 16[Y(X+2)]⁴ ≤ 32X⁴Y⁴.
```

All cancelled factors are positive, yielding `4Y³<X`. The checker verifies `(2X⁴−(X+2)⁴)` after `X=32+u` has strictly positive coefficients `760816,104928,5352,120,1` in increasing powers of `u`.

If also `Y≥q³` and `H=4Y(X+1)−1`, then

```text
H > 16Y⁴ ≥ 16q³Y³ > 16368qY³.
```

The last inequality uses the exact identity `16q³−16368q = 16q(q²−1024)+16q`, positive for `q≥32`. This lower size bound is intended to combine with a **separate** graph-projection divisibility reduction; neither that reduction nor the underlying `n=4,r=5` graph binding is established by this packet.

Run `python3 -I -S -B research/trace74-n4-r5-scalar-growth/check.py` from `Computability/DiophantineConsistency`. It rejects missing isolation/no-site flags and optimized Python. The receipt records source/output hashes. Model transfer, Pell ordinate binding, checked weighted projection, any 74 zero, and an iPRA consequence remain separate.

Independent review: [scalar growth audit](../../reviews/trace74-n4-r5-scalar-growth-independent/README.md) (PASS). The review checks the identities and inequality argument; it does not provide a Lean proof or graph binding.
