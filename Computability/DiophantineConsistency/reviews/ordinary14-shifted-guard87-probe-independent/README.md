# Independent review: shifted 87-gate guard probe

**PASS, scoped to the stated probe.** The exact guard identity, both stated
conditional maps, actual-port partial seed, two main-norm exclusions, gate
count and degree check. The reverse positive-zero existence implication is
open: the partial seed is not a full zero, and no unrestricted nonequivalence
is proved. This is external mathematics, not Lean/iPRA, PDF/file binding or
a global minimum.

Writing b=q−1, the identity

```
C*(X+K0*q)−F−b*omega = Bt−b*(omega−F)
```

is exact. A quotient-guarded zero maps by omega=t+F; a probe zero maps back
only on the stated branch omega>F. With beta>0, K0>=0 and the guard zero,
C>0 and F<=b−1. If b<=K0, then
`Bt>=X+(K0−F)q>0`, so omega>F. In the complementary unresolved branch,
`C*(X+K0*q)=b*omega+F<=qF<q²`, giving X<q². The cited stronger X or rank
claims are not inferred without their extra hypotheses.

For the actual-port partial seed, J=K0+2 gives `b>F=K0+1`, so
`alpha=b−F>0`, C=1 and omega=K0=F−1>0. The guard is zero and Bt=−b.
With X=1, Y=q³ and m=Y², the first-index-one values
`k=2`, `tau=2m+1`, `sigma'=2` satisfy the first norm and Z=M*tau; main
norm k=2 fails by the reviewed consecutive-squares argument. For index two,
`k=8m+4`, `tau=8m²+8m+1`, `sigma'=4m+4` again give Z=M*tau.
For Y>=8,

```
kY−psi_A(3) = 8Y³−16Y²−28Y−15 > 0,
psi_A(4)−k(Y+1) = (Y+1)(56Y²+128Y+52) > 0,
A=2Y+2.
```

The positive Pell-ordinate sequence is strictly increasing and classifies
positive unit solutions, so no `c=kY+eta` with `0<eta<k` can satisfy the
main Pell norm in that second case. These are only two partial seeds, not a
proof that the unresolved branch has or lacks a full zero.

The checker pins the 88/26 parent, exact 87-row graph delta, source receipts
and both P72/P115 compact44 byte bindings. It replays the author checker and
computes a nonuniform independent modular full-graph ray; the reviewed
upper bound and nonzero degree-26 coefficient establish exact specialized
degree 26. Finite numerical controls supplement the symbolic inequalities.
