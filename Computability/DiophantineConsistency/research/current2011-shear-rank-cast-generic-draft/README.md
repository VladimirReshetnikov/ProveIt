# Generic natural-to-difference-ring rank cast

This source-only draft addresses the algebra behind the two explicit cast
premises in the [forward index client](../current2011-shear-forward-index-binding-draft/README.md).
It has **not** been elaborated or kernel checked, and it does not prove the
current-port-specific cast tuple or the 72/46 zero bridge.

For model naturals `q,F,alpha,MC,MF,J`, assume

```
1<=q, F<=q, 1<=q².
```

Writing `ι` for the standard semiring embedding into the model difference
ring, bounded natural subtraction gives

```
ι(q−1)=ι(q)−1,
ι(q−F)=ι(q)−ι(F),
ι(q²−1)=ι(q)²−1.
```

Each follows by applying `ι` to `a−b+b=a` when `b<=a`; no general
subtraction-preservation claim is made. Semiring preservation then gives
the exact equality

```
ι(((q−1)*(q−F)+alpha)*(q²−1)+(MC+q*MF)*J)
 = ((ι(q)−1)*(ι(q)−ι(F))+ι(alpha))*((ι(q))²−1)
   +(ι(MC)+ι(q)*ι(MF))*ι(J).
```

Likewise `ι(k*Y+eta)=ι(k)*ι(Y)+ι(eta)` needs no subtraction. The positive
natural scalar gap `0<q−F−alpha` implies `F<q`, hence the needed `F<=q`.
Positive beta and J give q>=2 and q²>=1. The draft records all of these
as explicit generic interfaces; it does not silently identify the natural
rank with the signed `Carrier65.core.rank`.

To close the actual forward client, a separate caller must connect the
same shifted coordinates and the current integer port tuple to these
embedded natural values, apply the positive gap and q bounds, and simplify
the two fields. In particular the high port is `highPort+beta` exactly
once. The literal child evaluator, auxiliary norm extraction, natural
positive witness, both full zero maps and iPRA transfer remain open.

[`RankCast.lean.src`](RankCast.lean.src) contains the proposed lemmas and
unverified tactics. The checker pins the referenced sources and runs
bounded integer controls including an example where omitting `F<=q` makes
the cast identity false. These controls do not establish elaboration,
provider closure, graph binding or an all-model theorem.

```
python3 -I -S -B research/current2011-shear-rank-cast-generic-draft/check.py > /tmp/shear-rank-cast.json
cmp /tmp/shear-rank-cast.json research/current2011-shear-rank-cast-generic-draft/result.json
```

No Lean/build or staging operation is performed.
