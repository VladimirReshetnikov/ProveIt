# Positive candidate valuation for the free-J graph

`CompactPositiveValuation.valuation` defines the candidate 12-coordinate
valuation in the exact free-J coordinate order. For the constructed rank
`R`, `u=590069*N`, `Y=sY*Exp.exp u^3`, and `a=Exp.exp R*Y+Y`, its entries are

```
rep 590069 N, Fw ..., alpha ..., f-1, auxT, Exp.exp R,
Y, r, eta, zeta, delta a*i+(y-auxw), gamma.
```

`positive` proves every entry is strictly positive in an arbitrary model of
`IΣ₁`, assuming the symbolic compact `PackingInput`, positive `sY`, `auxT`,
`r`, `eta`, `zeta`, `i`, `gamma`, and the exact auxiliary-Pell abscissa
identity `f=xcoord (R*ycoord R a) a`. These are explicit inputs, not asserted
unconditionally. Its proof uses the packing's rank and scalar bounds and
the Pell-coordinate positivity theorem. In particular, positivity of slot
10 follows from `delta a*i>0` and does not itself require an ordering of
`auxw,y`; a later **graph** binding needs `auxw≤y` to interpret `y-auxw`
as an exact difference in the model difference ring.

The last coordinate is the positive **adaptive** gamma, distinct from the
outer seed's gammaOld; `auxw` is the auxiliary Pell coordinate, distinct
from the shifted-transport power. The valuation does not itself establish
its graph-expression bindings, construct the input witnesses, prove the
literal zero, bind retained coefficients/PDF bytes, or give an iPRA proof.

An earlier exploratory candidate used the incorrect slot 10
`delta a*i+auxw`. The exact ordinary-tail bridge requires instead
`delta a*i+(y-auxw)`, and only this corrected source is the successful
result described here. Attempt01 failed on parser spacing; attempt02
compiled the earlier wrong candidate but was rejected for lint warnings;
attempt03 failed on a local lemma name. Their snapshots/logs remain as
historical evidence and are not imported by the final result.

The bounded single-author `observations/attempt04` actually exited 0 without
warnings or `sorryAx`. The named Lean metatheory axiom report is exactly
`[propext, Classical.choice, Quot.sound]`, not an object-theory axiom list.
Source SHA-256:
`ec11564650f612f6a20e8591ef4b9ec7ad4cddc332eb8ef48b7ea1c0eba3d3ca`;
object SHA-256:
`52cf3f8f8886ddcdc2c82044b36381da10a345ff9a7e56d7ffa423cd6b2b46c3`.
The exact source, dependency/companion guards, terminal receipt and selected
project/root inventories are retained under that attempt. The 531 shared
seed/halt project names matched at preflight; recorded inventories and
direct guards were unchanged at the final checks. These point-in-time checks
do not authenticate full transitive, package or dynamic provenance. This is
a mixed-provider exploratory author result, not a paired replay or
independent artifact audit, and does not claim continuous monitoring.
