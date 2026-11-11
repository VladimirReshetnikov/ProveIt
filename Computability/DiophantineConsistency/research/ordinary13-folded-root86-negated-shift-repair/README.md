# A finite scalar-repair criterion for Bt<=0

This is an external criterion submitted for independent review. Given a
positive zero of the sign-reversed 86/26 candidate with `beta>0`, `K0>=0`
and `Bt<=0`, it identifies exactly when a specified nonnegative scalar
shift produces a positive parent zero by first making Bt positive. The
criterion does **not** prove that the required shift exists for every
candidate zero, and does not settle unrestricted 86/88 existence
equivalence or constitute a Lean/iPRA theorem.

Write `b=J*beta>0`, `q=b+1` and let

```
A = q*(X+K0*q+1) > 0,
L = b / gcd(b, X+K0*q+1),
D = min(F−1, floor((alpha−1)/b)),
delta0 = L * ceil((1−Bt)/(A*L)).
```

The candidate first residual forces b|Bt, as shown in the independently
reviewed `../ordinary13-folded-root86-negated-positive-bt/` packet. For an
integer `delta>=0` consider

```
F' = F−delta,      alpha' = alpha−b*delta.
```

Keep J, X, Y, eta, zeta and all other non-first inputs fixed. The literal
scalar rows give

```
G'=G,   R'=R,   C'=C+q*delta,   Bt'=Bt+A*delta.
```

Thus all non-first residuals stay zero, and F',alpha' are positive exactly
when `delta<=D`. Because gcd(q,b)=1 and b|Bt, the divisibility b|Bt' holds
exactly when L|delta. Under the stated Bt<=0 assumption, delta0 is the least
nonnegative multiple of L for which Bt'>0. Therefore such a shift exists
**if and only if** `delta0<=D`.

If this condition holds, q³|Y and b|Bt' make s=Y/q³ and t'=Bt'/b positive
integers. The original first and main residuals supply the same positive Pell root
tau and the lower bound `tau−ell>Y/q³` established in the independently
reviewed positive-Bt repair. No shifted candidate zero is assumed. Hence

```
r_old = k*(Bt'−1)+t'−s+(tau−ell) > 0.
```

Choosing this integer parent first coordinate makes the parent first
residual vanish, while the remaining residuals agree with the original
candidate zero. This is an explicit positive parent witness.

The parent-to-candidate forward construction in
`../ordinary13-folded-root86-negated-forward/` uses `delta=b` in the opposite
direction. Its starting parent necessarily has Bt>0 (otherwise its first
root is too large), so undoing that exact shift meets the criterion and recovers its original
F and alpha. Retaining the known original first coordinate recovers the
original parent tuple; the displayed +tau formula may instead choose the
other first root. This
observation does not imply that arbitrary Bt<=0 candidate zeros satisfy the
criterion. The checker verifies exact scalar identities, the gcd/ceiling
criterion and its failures on finite controls; it does not establish a
full-zero counterexample or replace the unbounded proof.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-shift-repair-independent/`.
