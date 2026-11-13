# Unshifting s in the natural-79 graph: an explicit obstruction

Deleting `s=n_s+1` from the reviewed [14/79/107 natural graph](../ordinary14-natural-forced-w79/README.md), and using `n_s` directly, produces the included 78-operation probe. This probe has an explicit natural zero with `s=0` at both the toy ports below and the authenticated compact44 ports. Hence a proposed proof that every probe zero has `s>0` is false. At the toy ports the 79 parent evaluated at the **same natural vector** is nonzero, so that particular unchanged-coordinate transfer also fails. This is an external obstruction, not an assertion that the two graphs have different global zero-existence truth values, a new consistency equation, Lean/iPRA theorem, PDF binding, or minimality claim. An [independent review](../../reviews/ordinary14-natural78-unshift-s-obstruction-independent/README.md) checks the graph edit and witnesses.

## Explicit witness

For integer ports `beta>=2`, `K0>=0`, `MC>0`, `MF>0`, choose the least positive `w` satisfying `w ≡ 1-K0 (mod beta)`, and define

```
q = beta+1,
R = (beta-1+beta²)*(q²-1)+MC+MF*q.
```

Assign the probe's natural input slots, in its pinned JSON order, as follows:

```
n_J=1, n_F=0, n_alpha=beta-2, n_f=2, n_i=2, n_T=R-1,
n_w=w, n_s=0, n_r=1, n_eta=0, n_zeta=R-1,
n_y=1, n_gamma=1, n_h=(q*w+K0-1)/beta.
```

The congruence makes `n_h` integral and nonnegative; `R>0` makes its two predecessor inputs natural. All remaining slots are plainly nonnegative. The probe has `J=1`, `alpha=beta-1`, `T=R`, `s=0`, `eta=1`, `k=R+1`, `gamma=1`, `f=2`, `i=3`, `r=y=1` and `X=q*w`. Direct graph substitution yields

```
Y=U=ell=0, c=1, Dstar=0, Q=9, V=-1,
F0=F1=Fa=Fs=guard=1, out=0.
```

In particular the arbitrary large integer port values can be used without assuming a zero of the original construction. For toy ports `(beta,K0,MC,MF)=(2,1,1,1)`, `w=2`, `R=44`, and the input vector is

```
(1,0,0,2,2,43,2,0,1,0,43,1,1,3).
```

The checker evaluates both literal DAGs at that vector and finds the probe zero and the parent nonzero. It pins both JSON graphs, verifies the exact one-gate deletion, reauthenticates all four P72/P115 compressed and raw port bytes, and evaluates the constructed zero at those actual ports. Those file checks do not establish a Lean/file association or PDF semantics. The witness adapts the independently reviewed [earlier unshifted-s obstruction](../ordinary14-natural80-unshift-s-obstruction/README.md) to the current 79 graph's direct `w` and `gamma` slots.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural78-unshift-s-obstruction/check.py | cmp - research/ordinary14-natural78-unshift-s-obstruction/result.json
```
