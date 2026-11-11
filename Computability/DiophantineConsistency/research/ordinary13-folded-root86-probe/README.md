# Conditional 86-gate absorption of the first-root coordinate

This is an **unproved positive-domain candidate**, not an iPRA endpoint or a
replacement for the reviewed [free-J 88/30 graph](../ordinary13-four-square88-30/README.md).
It has 86 live binary gates, the same 13 input slots and four compact44 fixed
ports, and the degree calculation below gives exact specialized degree 26
subject to independent review. It has a precise **all-integer coordinate
bijection**, but its preservation of strictly positive witnesses is open.
No new Lean, file/PDF, consistency, or global-minimality claim is made.

The parent has

```
g31=ell+k+r,
folded_g31=g31−k*Bt,
Z=M*folded_g31+Y*qm−q³*Bt.
```

Replace the old r by a new input `rho`, set `g31=ell+k+rho`, and use it
directly in Z. This deletes the `k*Bt` and subtraction gates. No other source
row uses r, and Bt is independent of r. Therefore the polynomial outputs
agree exactly under

```
rho = r−k*Bt,       r = rho+k*Bt.
```

These are inverse polynomial maps over every integer valuation. On the
positive domain, forward mapping additionally requires `r−k*Bt>0`; reverse
mapping requires `rho+k*Bt>0`. Neither is proved for all full graph zeros.
Consequently the 86 graph cannot yet inherit the parent's positive-zero or
iPRA endpoint. Even a full zero violating a same-coordinate repair would
not by itself decide unrestricted zero-existence equivalence.

## Local positivity obstruction

The pinned parent graph at the following **toy** ports and positive inputs
has its first residual zero:

```
beta=3, K0=4, MC=1, MF=4,
J=1, F=2, alpha=1, X=4, Y=256, eta=zeta=1, r=23,
all remaining witnesses = 1.
```

It has `q=4`, `Bt=12`, `k=2`, `E=1024`, `ell=524288`,
`M=q³*(q−1)=192`, `Z=M*524289`, and `A0=0`. However
`rho=r−k*Bt=−1`. The first equation's other root would give
`rho=−1048579`, also negative. The other residuals are nonzero, so this is
not a full graph zero and does not settle the missing positive-domain maps.
It does show that the first factor, positive toy data and positive Bt alone
cannot establish the desired forward sign.

## Degree and checks

In the absorbed graph define

```
delta0=M*(k+rho)+Y*qm−q³*Bt,   Z=M*ell+delta0.
```

The exact identity

```
A0=2*(M*ell)*delta0+delta0²−M²*(1+ell*k)
```

gives `deg(A0)<=13`: `deg(M*ell)<=8` and `deg(delta0)<=5`.
For the second residual put `W=U*X+H*shift`. Since
`Dstar=U*a*c+W` and `Delta=a²+H`,

```
A1=2*U*a*c*W+W²−U²*(1+H*c²),
```

so `deg(A1)<=13`. The other two residual degrees are at most 13 and 10.
The complete four-square output therefore has degree at most 26. A full
actual compact44-port evaluation on the all-inputs-equal ray modulo
1,000,000,007 has degree 26 and leader **610010950**, yielding exact
specialized integer degree 26. These graph/degree checks are external, not a
Lean `totalDegree` theorem or a file-semantics theorem.

The checker verifies the complete graph delta, topology and liveness; both
sparse-polynomial cancellation identities; exact substitution on the stated
local control; both compact44/P115 port bindings and the full modular ray.
The positive-domain obligations and local obstruction require ordinary
mathematical reasoning and are submitted for independent review.

```
python3 -I -S -B research/ordinary13-folded-root86-probe/check.py > /tmp/folded-root86.json
cmp /tmp/folded-root86.json research/ordinary13-folded-root86-probe/result.json
```

Independent scoped review is recorded in
`../../reviews/ordinary13-folded-root86-probe-independent/`; its distinct
weighted full-graph ray has degree 26 and leader 590126902 modulo 1,000,000,007.
