# A scalar `n=4, r=5` Pell witness

This ordinary-integer example shows that the paired ordinate equations, the window `n<r<2n`, positive carrier split, and the basic `q` divisibility of `X,Y` do not by themselves exclude the `n=4, r=5` branch. It is **not** a 74 graph zero, a fixed-BFS-port witness, or an iPRA claim.

Take `q=32`, `beta=31`, `J=1`, `Y=q³=32768` and `X=8Y³=281474976710656`. Set `P=XY²`, `A=Y(X+1)`,

```text
k = 2*ycoord 4 (2(P−1)+1)
c = ycoord 5 (A−1)
eta = c−kY
zeta = k−eta.
```

The exact integer checker verifies `eta,zeta>0`, `k=eta+zeta`, `c=kY+eta`, `q|X`, `q³|Y`, `q=beta*J+1`, and `4<5<8`. It evaluates both Pell ordinates by their recurrence and checks independently the polynomial forms

```text
k = 128P³+192P²+80P+8
c = 16(A+1)⁴−12(A+1)²+1.
```

The same scalar construction works for **every ordinary integer `q≥2`**: take `Y=q³`, `X=8Y³`, `n=4`, `r=5`, and define `k,c,eta,zeta` as above. The checker verifies the fourth- and fifth-ordinate polynomials symbolically, substitutes `X=8Y³`, and expands `eta` and `zeta` at `Y=2+u`. All coefficients in both shifted polynomials are strictly positive, proving `eta,zeta>0` for `Y≥2`. Thus the scalar family also applies arithmetically at `q=beta+1` for the retained symbolic beta and `J=1`; it still does not assign the remaining BFS ports or satisfy the full graph equations.

Run `python3 -I -S -B research/trace74-n4-scalar-pell-witness/check.py` from `Computability/DiophantineConsistency`. The checker rejects missing isolation/no-site flags and optimized Python; the receipt records source/output hashes. It does not supply the omitted 74 variables, factor equations, rank residue or symbolic fixed tuple. Additional graph constraints could rule out this scalar configuration.

The [independent arithmetic audit](../../reviews/trace74-n4-scalar-pell-witness-independent/README.md) reproduced the exact witness and the shifted positivity coefficients. It also separately verified `c>2q⁴` for this scalar family by expanding `c(q)−2q⁴` at `q=2+u` into 49 strictly positive coefficients. This is still not a full graph-zero or fixed-tuple claim.
