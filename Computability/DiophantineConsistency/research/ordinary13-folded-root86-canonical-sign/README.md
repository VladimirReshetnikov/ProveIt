# Canonical halt witness has negative folded coordinate

This source-traced, external argument is submitted for independent review.
At the authenticated compact44 ports, the **particular standard-natural
witness assembled by the existing halt-to-free-J construction**, if its halt
premise holds, has `r−k*Bt<0`. Thus the direct coordinate map cannot use that
canonical witness for the 86/26 folded graph. This is a conditional statement:
it does not assert a halt, an actual zero, failure of an alternative witness
construction, or unrestricted 88/86 existence nonequivalence. It is not a new
Lean/iPRA theorem, PDF/file semantics binding, or source ancestry replay.

## The source route

`CompactHaltFirstSeed.FirstData` and `CompactFirstTransportSeed` use
`q=2^(590069*N)`, `Xgraph=2^R`, `Y=sY*q³`, `k=eta+zeta`,
`ell=Xgraph*Y²*k`, a first Pell root tau, and a positive transport z with

```
(q*K0+Xgraph)*C = q*F+(q−1)*(q*z),
(q³*(q−1))*(ell+k+r)+Y*(q−1)
  = (q³*(q−1))*tau+(1+(q−1)*k)*q³*((q−1)*(q*z)).
```

The literal free-J graph has `Bt=(q*K0+Xgraph)*C−q*F`; hence
`Bt=(q−1)*q*z`. Dividing the second displayed integer equality by positive
`q³*(q−1)` and using `Y=sY*q³` gives exactly

```
r − k*Bt = tau − ell − k − sY + q*z.                (1)
```

`ArithmeticOuterSeed.SeedRelations` gives
`tau²=1+m*(m+1)*k²`, `m=Xgraph*Y²`, and
`k=2*ycoord(h,2*(m−1)+1)` with `R=2h−1`. Its recurrence has
`ycoord(2,2*(m−1)+1)=2*(2m+1)` and is increasing in the time index.
`CompactConstructedRank.rank_properties` gives `R>2*(590069*N)`, so `h>=2`
and

```
k >= 4*(2m+1) > 8*Xgraph*Y².                       (2)
```

`FreeJHaltModelZero` retains this same r as its 12-variable valuation's
coordinate 7, and `FreeJ13Halt.backward_ports` copies that coordinate to
13-variable coordinate 8. The reviewed 87-to-88 transformation keeps r and rewrites the gap exactly,
using `y²−V²=u*(y+V)` with `y=V+u`, and replaces the unit-product
finalizer by four residual squares. The polynomial fold then uses the same
first-root r.

## Bounding the positive transport term

`CompactHaltPackedWord.haltLength T=581197^(2T+4)>=2` for standard natural T.
Therefore `q>=2^(2*590069)`. The source uses the symbolic `paramKernel rho` as K0; its existing
`CompactCellProductBound.symbolic_kernel_lt` gives `K0<2^592884<q`.
Independently, the authenticated compact44 K0 payload has 592884 bits; its
association with the symbolic term retains the existing external binding
qualification. Since `R>2*(590069*N)`,
`Xgraph=2^R>q²>K0*q`. The packing constraints give `0<C<q` and `F>0`.
Consequently, using positive q,z,

```
q*z = ((q*K0+Xgraph)*C−q*F)/(q−1)
    < (q/(q−1))*(q*K0+Xgraph)
    < 2*(q*K0+Xgraph) < 4*Xgraph.                  (3)
```

Here q>=4. Because sY>=1, `Y=sY*q³>=q³`, so in particular Y>=2. From (2),
`k/4>2*Xgraph*Y²>=8*Xgraph>q*z`.

Finally m>=1 and k>=2 imply

```
(ell+3k/4)²−tau²=(m/2+9/16)*k²−1>0,
```

and the chosen first Pell root tau is positive. Thus
`tau<ell+3k/4`; (1) and (3) yield

```
r−k*Bt < −k/4−sY+q*z < 0.
```

This does not depend on the separately rejected auxiliary completion: it
traces the existing completeness construction's retained first and main seed.
The source checker pins the referenced Lean source bytes and the two external
compact44 bindings, checks the exact port payload hashes and finite size bound,
and checks representative integer inequalities. It does not compile Lean,
replay transitive providers, or certify the unbounded argument by computation.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-canonical-sign-independent/`.
