# Thirteen-input C-fold obstruction to dropping the Y shift

Deleting `Y=n_Y+1` from the proposed [13/97/28 natural C-fold graph](../ordinary13-natural-cfold97-degree28/)
and using `n_Y` directly gives the included 96-gate graph. It has a zero
with `Y=0` at the toy and authenticated compact44 ports. Thus a zero does
not force `Y>0`. At the toy ports the 97 parent at the same natural vector
is nonzero, so that unchanged-coordinate transfer also fails. This does
**not** prove different global zero-existence truth values, or settle
consistency, a Lean theorem, or an iPRA endpoint.

An [independent review](../../reviews/ordinary13-natural96-unshift-y-obstruction-independent/README.md)
checks the graph edit and both concrete witnesses, without asserting a global
zero-existence separation.

## Deterministic witness

For integer ports `beta>=2`, `K0>=1`, `MC>0`, `MF>0`, choose positive
`X ≡ 1−K0 (mod beta)`; the checker chooses the least positive
representative. Put

```
b=beta, q=b+1,
R=(b−1+b²)*(q²−1)+MC+MF*q,
Bt=X+q*(K0−1),  r=Bt/b+1.
```

The assumptions give `R>0`, `Bt>0`, and `b | Bt`, so `r` is a positive
integer. Set the ordinary graph coordinates to

```
J=1, F=1, alpha=b−1, f=2, i=3, T=R, X=X,
Y=0, r=r, eta=1, zeta=R, u=2, gamma=1.
```

All remaining natural input shifts can be inverted. Direct evaluation gives

```
U=ell=0, c=1, k=R+1, C=1,
Z=q³*b*r−q³*Bt=q³*b=M,
Dstar=0, Q=9, V=−1,
A0=A1=g72=0, Fa=1, output=0.
```

At toy ports `(beta,K0,MC,MF)=(2,1,1,1)` the deterministic values are
`X=2`, `R=44`, `Bt=2`, and `r=2`. The 13 inputs in candidate order are

```
(1,0,0,2,2,43,1,0,2,0,43,1,0).
```

The checker evaluates every candidate gate at this witness and verifies the
97 parent is nonzero at the same vector. It authenticates all P72/P115
port bindings and compressed/raw bytes, verifies the hypotheses, constructs
the corresponding actual-port witness using exact integer arithmetic, and
evaluates every candidate gate. The concrete witnesses do not establish or
refute global zero-existence equivalence.

```
python3 -I -S -B research/ordinary13-natural96-unshift-y-obstruction/check.py > /tmp/natural13-unshift-y.json
cmp /tmp/natural13-unshift-y.json research/ordinary13-natural96-unshift-y-obstruction/result.json
```
