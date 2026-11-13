# Thirteen-input q-cubed modified carrier: 83 operations, degree 60

This **proposed** graph has 13 strictly positive inputs, 83 live arithmetic
operations and exact degree 60 at the authenticated compact44 ports. It
applies the reviewed q-X main-carrier substitution to the separately proposed
[`13/84` q-cubed unscaled graph](../ordinary13-qcube-unscale84/). The
positive-zero comparison below depends on that parent's proof and on a
fact-level replay of the cited existing calibration. Both the parent packet
and this construction require independent review. No modified-graph Lean,
iPRA endpoint, JSON/PDF binding, fresh provider replay or global minimum is
claimed.

## Exact carrier substitution

Write `b=J*beta`, `q=b+1`, `Y=q³*s`, `U=Y*q²`, `E=X*Y`,
`k=eta+zeta`, `C=q−F−alpha`, and
`Bt=C*(X+K0*q)−F*q`. Replace the parent's positive X input by a positive w
and define `X=q*w`. Replace positive `gamma_old` by positive `gamma_prime`
with `gamma_prime=gamma_old+w`. Since `E*q=U*w`,

```
U*gamma_old + E*q − (k−R−1) = U*gamma_prime − (k−R−1).
```

All other residuals agree. This is an identity for signed integer inputs,
not by itself a positive-domain equivalence. The graph adds `X=q*w` and
deletes the old `E*q` gate and its addition, reducing 84 operations to 83.

## Parent to proposed graph

At the authenticated ports the parent's positive-zero map supplies a
positive zero of the `13/87` free-J direct-auxiliary graph; its reviewed
auxiliary-root map then supplies the original free-J 13-input zero. The
`FreeJ13Halt.forward` proof maps this to a 12-input literal zero preserving
J, F, alpha, X, Y and hence q and R. The existing
`FreeJPowerFinish.graph_power` and `FreeJPowerProjection.graph_projection`
theorem statements give `X=2^R` and `q|3X`, respectively, under the
authenticated port bounds. These are external uses of source theorem
statements, not a fresh build or modified-graph Lean theorem.

The authenticated `beta=2^B−1` has `B=590069>=4`. As in the reviewed
[`14/84` main-carrier packet](../ordinary14-qcube84-probe/), if
`q|3*2^R` then `q=2^j` or `3*2^j`. The second case would imply
`3*2^j=1 (mod beta)` because `beta|q−1`. Reducing j modulo B yields a
two-bit residue strictly between 1 and beta, including the wrap case
`2^(B−1)+1`, a contradiction. Hence `q|X`. Set `w=X/q>0` and
`gamma_prime=gamma_old+w>0`; the carrier identity gives a new positive zero.
This step uses the actual Mersenne beta, not merely `q|3X` and gcd(3,X)=1.

## Proposed graph to parent

At a new positive zero, the four squares vanish. Its first norm is

```
Z=b*(ell+k+r−k*Bt)−Bt,
Z²=b²*(1+m*(m+1)*k²),
ell=m*k,  m=X*Y².
```

Thus `b|Z` and `b|Bt`; write `t=Bt/b` and `tau=|Z|/b>0`. If `Bt<=0`,
then `t<=0` and the norm gives

```
r=k*Bt+t−ell−k ± tau < 0,
```

because `tau<ell+k`, contradicting positivity. Thus `Bt>0`. At the
authenticated ports `K0>=0`; from `Bt=C*(X+K0*q)−F*q>0` it follows
that `C>0` and `F+alpha<q`. This directly supplies the positive scalar
gap without assuming a parent zero.

The modified main residual, strong and direct-auxiliary residuals are the
same norm data used in the reviewed
[`14/84` modified-carrier replay](../ordinary14-qcube84-probe/). Its
positive-root orientation uses `Y=q³*s`, `q>=3` and the positive scalar gap;
these hold here. The first Pell norm above supplies its positive first root.
The direct-auxiliary graph instead takes positive y; the reviewed
[`13/87` auxiliary-root proof](../ordinary13-aux-root87-36/) uses only the
first, main and strong norms to prove `|V|>1` and `|y|>|V|`, so
`u=y−V>0` supplies the positive auxiliary coordinate if needed. No old
positive r or old gamma is assumed.

The fact-level replay from those norms gives the scalar rank window,
`q⁴|(R+1−k)`, and the exact Pell indices with `mu=q⁴`, using the strong
input `i_prime=i`. The modified main orientation yields

```
d=X+a*c+H*(gamma_prime−W),  W>=0.
```

`P72Power.power_of_mod` supplies `X=2^R`, and the same-index trace identity
then gives `gamma_prime=gamma0+W` with `gamma0>=2^(R−2)`. Since
`q>=47`, `w=X/q<gamma0`; hence `gamma_old=gamma_prime−w>0`. With that
coordinate and `X=q*w`, the exact carrier identity gives a positive parent
zero. This is an external replay of source-level arithmetic, not a direct
application of the old literal-zero wrappers; their original first-coordinate
positivity hypotheses have not been supplied for the new graph.

## Exact count and degree

The checker pins the entire parent and candidate graphs, verifies the single
source delta, topology and liveness, and checks the exact signed substitution
on 160 assignments. It authenticates the P72/P115 bytes and checks the
Mersenne and port bounds. All 13 inputs and all four fixed leaves are live.

At fixed ports `deg X<=2`, `deg Y<=4`, `deg U<=6`, `deg a<=6`,
`deg c<=5`, `deg H<=6`, `deg ell<=11`, `deg Bt<=3` and `deg Z<=12`.
Thus the first residual has degree at most 24, the strong residual at most
22 and the direct auxiliary residual at most 30. For the main residual put
`Dstar=U*a*c+delta`, where
`delta=U*X+H*(U*gamma_prime−k+R+1)`. Then

```
A1=2*U*a*c*delta+delta²−U²*(1+H*c²),
```

and `deg(U*a*c)<=17`, `deg(delta)<=13`, so `deg A1<=30`. The sum of
four squares has degree at most 60. A full all-inputs-equal ray at the
authenticated ports modulo 1,000,000,007 has degree 60 and leading
coefficient 619528110, proving exact specialized integer degree 60.

```
python3 -I -S -B research/ordinary13-qcube-main83/check.py > /tmp/qcube-main83.json
cmp /tmp/qcube-main83.json research/ordinary13-qcube-main83/result.json
```

The finite controls do not replace the unbounded arithmetic above or a Lean
proof of any graph/model/endpoint bridge.

Independent external review is recorded in
`../../reviews/ordinary13-qcube-main83-independent/`.
