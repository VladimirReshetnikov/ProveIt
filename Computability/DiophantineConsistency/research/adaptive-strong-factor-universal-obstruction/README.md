# Strong-residual deletion fails for arbitrary coefficient ports

In the 13-variable sum-of-squares graph, write the residuals as

```text
A0 = Z² − M²(1 + ℓ(ℓ+k))
A1 = D² − U²(1 + Δc²)
A2 = y² − Q(y²−V²) − 1
A3 = I² − Q,  I = c²i,  Q = Δ(f²−1).
```

Dropping `A3` would also remove witness `i`, but the remaining three
residuals do **not** universally imply it. For the arbitrary integer ports
`β=0`, `K0=−2`, `MC=−326`, `MF=0`, take the thirteen positive witnesses

```text
J=F=α=f=i=T=X=r=y=γ=1,  Y=3, η=27, ζ=49.
```

Then `q=1`, `k=76`, `c=255`, `a=6`, `Δ=63`, `U=3`, `M=0`,
`Bt=0`, `R=−326`, `Z=0`, and `D=−6072`. Since
`1+63·255²=2024²` and `D=−3·2024`, both `A0` and `A1` vanish.
Also `f=y=1` gives `Q=0` and `A2=0`, but `I=65025` and
`A3=65025²=4228250625>0`. The dropped equation is therefore zero while
the original sum of squares is positive at this positive-witness assignment.

`check.py` evaluates every row of the pinned 87-operation candidate graph,
checks all thirteen witness values are positive, checks these exact integer
identities, and verifies the original output equals the positive square of
`A3`. It actually exited 0 in normal Python; optimized Python is deliberately
rejected. No Lean theorem is claimed here.

This is a counterexample at symbolic integer ports: in particular, `β=0` and
`K0<0` do not satisfy the maintained equation's fixed positive ports. It
rules out a port-uniform deletion argument and does not decide whether some
different, fixed-port argument could eliminate a variable. It also does not
assert existence of a zero for the maintained equation or any ZFC result.
