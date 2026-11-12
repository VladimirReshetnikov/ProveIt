# First-norm boundary for the 82→84 companion carrier

The exact control in [result.json](result.json) is a positive assignment to
all 13 inputs of the [13/82 residue graph](../ordinary13-residue-first82/).
It satisfies the graph's **first norm**, positive q³-scale, compact-style
scalar port bounds and rank window, but its companion transport for the
[13/84 graph](../ordinary13-qcube-unscale84/) is zero. Thus those facts alone
do not imply the strict companion positivity needed by the reviewed
same-other-coordinates root-switch construction, nor `X>=q²`.

It is **not a full graph zero**: its main, auxiliary and strong residuals and
its complete output are nonzero. The tuple is a small toy tuple satisfying the
same inequalities, not the authenticated compact44 tuple. It does not disprove
a full-zero consequence, the global existence equivalence, an alternative
witness map or an iPRA endpoint.

## Reproducible assignment

Set

```
beta=46, K0=0, MC=MF=1, J=1, q=47,
F=1, alpha=45, X=47, s=1, Y=q³,
m=X*Y², k=8*m+4, tau=8*m²+8*m+1,
eta=1, zeta=k-1, ell=m*k,
Pprime=46, t=1, r=k*(Pprime-1)+t+tau-ell,
f=2, i=1, T=1, y=1, gamma=1.
```

Every input is positive. The Pell identity
`tau²=1+m*(m+1)*k²` holds exactly, and `ell<tau<ell+k`; the 82 graph gives
`C=1`, `Pprime=b=46`, `Z=b*tau` and first residual zero. The 84 carrier at
the same non-first inputs is

```
B = C*(X+K0*q)-F*q = 0,
```

while `X=q<q²`. Moreover `R=4771536` satisfies `24<=R` and
`R+q³+q+1<=q⁴`, with `0<MC<beta` and `0<MF<2*beta`.
The standard natural numbers form an intended IΣ₁ model, so this is also a
counterexample to any proposed all-model implication whose hypotheses are
limited to these displayed facts. It says nothing about the missing main,
strong, auxiliary, index-residue or full-zero hypotheses.

The checker pins both graphs, evaluates every operation with exact integer
arithmetic, verifies each stated inequality and first-norm equality, and
confirms all three remaining residuals and the complete output are nonzero.
It deliberately makes no Lean execution or provider claim.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B research/ordinary13-residue82-firstnorm-companion-obstruction/check.py`
and compare with [result.json](result.json).
