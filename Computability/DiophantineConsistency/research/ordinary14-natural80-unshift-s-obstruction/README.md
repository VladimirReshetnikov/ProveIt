# Obstruction to dropping the s input shift

Deleting the `s=n_s+1` gate from the proposed
[14/81/107 natural graph](../ordinary14-natural-forcedj81/) and using `n_s`
directly gives the included 80-gate graph. It has a zero with `s=0` at both
the toy ports and the authenticated compact44 ports. Thus a proof that every
zero forces `s>0` is impossible. At the toy ports the 81 parent evaluated at
the very same natural coordinates is nonzero, so an unchanged-coordinate
transfer is also false there. This packet does **not** establish that the
80-gate graph has a different global zero-existence truth value from the 81
parent, or settle consistency, a Lean theorem, or an iPRA endpoint.

An [independent review](../../reviews/ordinary14-natural80-unshift-s-obstruction-independent/README.md)
checks both concrete witnesses and this limited conclusion.

## General construction

For arbitrary integer ports satisfying `beta >= 2`, `K0 >= 0`, `MC > 0`,
and `MF > 0`, choose a positive integer `w` with
`w ≡ 1−K0 (mod beta)`. One deterministic choice is the least positive
representative, taking `beta` when the ordinary remainder is zero. Let

```
q = beta+1
R = (beta−1+beta²)*(q²−1) + MC + MF*q.
```

Use the ordinary graph coordinates

```
J=1, F=1, alpha=beta−1, f=2, i=3, T=R,
w=w, s=0, r=1, eta=1, zeta=R, y=1, gamma=1,
n_h=(q*w+K0−1)/beta.
```

The divisibility condition makes `n_h` a nonnegative integer and the port
assumptions make `R>0`, so all candidate inputs are nonnegative after the
remaining input shifts are inverted. Direct evaluation gives

```
Y=U=ell=0, c=1, k=R+1, Dstar=0, Q=9, V=−1,
F0=F1=Fa=Fs=guard=1, output=0.
```

At toy ports `(beta,K0,MC,MF)=(2,1,1,1)`, the deterministic choice is
`w=2` and `R=44`. The input vector in the 80 graph's candidate order is

```
(1,0,0,2,2,43,1,0,1,0,43,1,0,3).
```

The checker evaluates every gate on this vector and confirms that the
81 parent, at this same vector, has nonzero output. It then authenticates
the P72/P115 bindings and all four compressed/raw port bytes, verifies that
their values satisfy the displayed hypotheses, constructs the corresponding
large witness symbolically as integers, and evaluates every 80-graph gate.
These are concrete counterexamples; they do not prove or disprove an
equivalence between the two graphs' zero-existence statements.

```
python3 -I -S -B research/ordinary14-natural80-unshift-s-obstruction/check.py > /tmp/natural14-unshift-s.json
cmp /tmp/natural14-unshift-s.json research/ordinary14-natural80-unshift-s-obstruction/result.json
```
