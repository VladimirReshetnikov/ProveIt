# Six forced inputs: 13 naturals, 89 operations, degree 56

This external mixed shift of the [13/82 positive residue-adjusted carrier](../ordinary13-residue-first82/)
leaves `J`, `X`, `f`, `y`, `gamma` and the first-root coordinate `r`
unshifted; the other seven inputs are shifted. Its graph has 13 natural
inputs, 89 live binary operations and exact degree 56 at the authenticated
compact44 ports. It saves one operation compared with the separate
[13/90/56 mixed graph](../ordinary13-natural-residue-forced90-degree56/).
The gamma direction below retains that packet's **standard-integer** proof
boundary; no new all-model or iPRA endpoint is claimed.

## Forcing the first-root input

Write

```
b=J*beta, q=1+b, Y=q³*s, m=X*Y², k=eta+zeta, ell=m*k,
C=q-F-alpha, P=C*(X+K0)-F, Z=b*(ell+k+r-k*P)-P.
```

For the following local model argument assume an ordered natural IΣ₁ model,
positive represented beta, a represented natural K0 with `K0+1<=q²`, and
natural r; F, alpha, s, eta and zeta are shifted and hence positive. The
[13/91 forcing arguments](../ordinary13-natural-residue-forced91-degree56/)
apply without r being positive and force J,X,f,y positive, even with gamma
merely natural. Therefore b>0, q>=2, X>=1, Y>=q³, m>0 and k>=2.

The first norm at a zero is

```
Z²=b²*(1+ell*(ell+k)).
```

First P>0. If P<=0 then `Z>=b*(ell+k)`, since r>=0; but
`(ell+k)²-(1+ell*(ell+k))=ell*k+k²-1>0`, contradicting the norm. Hence
`C>0` because `P=C*(X+K0)-F>0`; also `C<q`. The norm and model
square-divisibility of the magnitude give `b | Z`, and the source identity
then gives `b | P`. Write `P=b*t` for a positive model natural t. Since b>=1,
`t<=P`. The same norm gives a positive natural tau with

```
tau²=1+m*(m+1)*k²,       tau>ell.
```

The extra kernel bound forces P<m:

```
P < q*(X+K0) <= X*q*(K0+1) <= X*q³ <= X*Y² = m.
```

The second inequality uses X>=1 and natural K0; the last uses `Y>=q³`
and q>=2. If r=0, the signed root relation is

```
0 = k*(P-1)+t-ell ± tau.
```

The plus branch is strictly positive since P,t>=1 and tau>ell. For the
minus branch, `P<m`, `t<=P` and `k>=2` give

```
k*(P-1) < k*m = ell,       t < m <= k*m = ell.
```

Thus `k*(P-1)+t < 2*ell < ell+tau`, making the minus branch strictly
negative. Both contradict r=0. Thus r>0. The magnitude reflection, ordered quotient
and exact graph binding are mathematical obligations for a model client;
no Lean elaboration is reported here.

For the authenticated compact ports, `beta>=46` and the checker reads all four
raw/gzip P72 and P115 bindings and verifies
`K0+1 <= (beta+1)²`. With J>=1 this implies the local
`K0+1<=q²` bound. In an arbitrary model, that last implication is conditional
on explicit beta/K0 natural-port representations and the represented
inequality; the raw-byte calculation is **not** a Lean proof of that cast.
The compact symbolic-kernel source bounds may be used to prove it, but no
compatible provider proof is asserted here.

The other five unshifted inputs are positive at every **standard** zero by the
[13/90 argument](../ordinary13-natural-residue-forced90-degree56/). Its gamma
proof only used r>=0 in the C<=0 contradiction, so it remains valid here.
Thus standard zero maps to and from the positive 82 parent follow by using the
six forced values directly and predecessors for the seven shifted coordinates.
The graph is exactly the positive-parent polynomial at that mixed substitution;
it is not claimed equal at the same tuple to the fully shifted polynomial.

## Size, proof status, and reproduction

The checker verifies all 89 graph rows and liveness, exact mixed-shift wiring,
the actual first-root rows, P72/P115 compact port hashes and bounds, and the
A1 cancellation identity. The four residual degree bounds are 22, 28, 28, 22;
an all-inputs-equal ray modulo 1,000,000,007 has nonzero degree-56 coefficient
58796952 at the authenticated ports. This proves exact degree 56 at that tuple.
The separately reviewed 82 parent has external standard-integer calibration and
provider limits. The gamma transfer, this kernel-bound model cast, positive
root model client, earlier parent chain and iPRA endpoint remain open in Lean.
The compact port tuple is not the current-2011 PDF tuple. No global minimum is
claimed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-residue-forced89-degree56/build.py
python3 -I -S -B research/ordinary13-natural-residue-forced89-degree56/check.py
```

The deterministic source/byte/ray receipt is [receipt.json](receipt.json).
It does not invoke Lean or prove the unbounded model argument.
