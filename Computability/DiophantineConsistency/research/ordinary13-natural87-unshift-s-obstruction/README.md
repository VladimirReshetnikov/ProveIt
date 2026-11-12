# Thirteen-input obstruction to dropping the s shift

Deleting `s=n_s+1` from the proposed [13/88/99 natural graph](../ordinary13-natural-unit-product88/)
and using `n_s` directly yields the included 87-gate graph. It has a zero
with `s=0` at the toy ports below and at the authenticated compact44 ports.
Consequently `s>0` is not forced by a zero. At the toy ports the 88 parent
evaluated at exactly the same natural coordinates is nonzero, so that
particular unchanged-coordinate transfer also fails. This does **not** prove
that the graphs have different global zero-existence truth values, or settle
consistency, a Lean theorem, or an iPRA endpoint.

An [independent review](../../reviews/ordinary13-natural87-unshift-s-obstruction-independent/README.md)
checks the graph edit and concrete witnesses, without extending that limited
conclusion to global zero-existence equivalence.

## Deterministic construction

Assume integer ports `beta>=2`, `K0>=0`, `MC>0`, `MF>0`. Choose a positive
`w ≡ 1−K0 (mod beta)`; the checker uses the least positive representative.
Put

```
b=beta, q=b+1,
R=(b−1+b²)*(q²−1)+MC+MF*q,
k=R+1, B=q*w+K0−1, t=B/b,
r=k*B+t−k+1.
```

The hypotheses give `R>0`, `B>0`, and `b | B`, so `t` and `r` are positive
integers. Use ordinary coordinates

```
J=1, F=1, alpha=b−1, f=2, i=3, T=R, w=w,
s=0, r=r, eta=1, zeta=R, y=1, gamma=1.
```

After inverting the remaining input shifts, every 87-graph input is
nonnegative. The rank computed by the graph is `R`, and direct evaluation
gives

```
Y=U=ell=0, c=1, k=R+1, Bt=B,
Z=b*(k+r−k*B)−B=b,
Dstar=0, Q=9, V=−1, F0=F1=Fa=Fs=1, output=0.
```

For toy ports `(beta,K0,MC,MF)=(2,1,1,1)`, we get `w=2`, `R=44`, `B=6`,
and `r=229`; the 13 inputs in candidate order are

```
(1,0,0,2,2,43,1,0,229,0,43,1,0).
```

The checker evaluates every gate at the toy witness and verifies the
88 parent is nonzero at the same vector. It then authenticates all P72/P115
port bindings and compressed/raw bytes, verifies the port hypotheses,
constructs the corresponding large witness as integers, and evaluates
every 87-graph gate. These concrete counterexamples do not establish or
refute a global zero-existence equivalence.

```
python3 -I -S -B research/ordinary13-natural87-unshift-s-obstruction/check.py > /tmp/natural13-unshift-s.json
cmp /tmp/natural13-unshift-s.json research/ordinary13-natural87-unshift-s-obstruction/result.json
```
