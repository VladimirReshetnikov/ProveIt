# Four existing-input guards that cannot replace h

This external argument concerns the proposed 89/26 guarded graph
`../ordinary14-guarded-fold89-26/`: its guard is `Bt−h=0`, with `h` a
positive extra input. Under the hypotheses below, setting h equal to any one
of four existing positive inputs makes the equation have **no positive
zeros**. This does not rule out a different guard, a more general
reparametrization, or a 13-input equation. It is submitted for independent
review and is not a Lean theorem.

Write `b=J*beta`, `q=b+1`, `C=q−F−alpha`, and assume `beta>0`, `K0>=0`.
At a putative positive zero of the guarded four-square system, the first
residual forces `b|Bt` and `q³|Y`, as in the reviewed
`../ordinary13-folded-root86-negated-positive-bt/` packet. The guard makes
`Bt>0`, so `C>0`. Thus

```
1 <= F,alpha <= b−1,    Bt is a positive multiple of b.
```

Hence `Bt=F` and `Bt=alpha` are both impossible. If additionally
`beta>1`, then `Bt=J` is impossible: `J*beta=b` cannot divide positive J.

For the first-root input `sigma`, assume in addition `K0<q²`. The reviewed
positive-Bt Pell descent gives

```
k >= 8*X*Y²+4,   t=Bt/b>=1,   tau²=1+m*(m+1)*k²,
ell=m*k, m=X*Y².
```

Since `C<=b−1`, `Y>=q³`, and `X>=1`,

```
Bt < b*(X+K0*q) < q*X+q^4 < 2*X*q^6 < k/4.
```

Thus `Bt+t<=2Bt<k/2`. If `sigma=Bt`, the signed first expression obeys

```
Z/M = ell+k−Bt+s−t > ell+k/2,    s=Y/q³>0.
```

But `k>2` and the norm equation require `|Z/M|=tau<ell+k/2`, since
`(ell+k/2)²−tau²=k²/4−1>0`. This contradiction rules out `h=sigma`.

The proposed 89/26 packet's fixed-port condition `0<=K0<(beta+1)²`
implies `K0<q²` for all positive J. Its authenticated compact44 beta is
greater than 1, so all four exclusions apply at those ports. Only the first
three use the weaker hypotheses explicitly stated above.

```
python3 -I -S -B research/ordinary14-guarded-fold89-reuse-exclusions/check.py > /tmp/guard-reuse.json
cmp /tmp/guard-reuse.json research/ordinary14-guarded-fold89-reuse-exclusions/result.json
```

The finite checker pins the guarded graph and exercises the scalar and bound
calculations; it does not replace the unbounded proof.

Independent external review is recorded in
`../../reviews/ordinary14-guarded-fold89-reuse-exclusions-independent/`.
