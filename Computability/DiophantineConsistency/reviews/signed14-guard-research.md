# Signed14 guard follow-up: one valid reduction and two failed shortcuts

The117/312 lead below has now been materialized and accepted in
`candidates/constructive-integer14-guard-reduced/`; the complete
root review is `integer14-guard-root-peer.md`. The unmaterialized
wording below records the state of the initial research note. Its failed
shortcuts and finalizer tradeoff remain distinct from the accepted sibling.

This note leaves all frozen119/121 packets, page files and Lean untouched.
The subsequent13Z/135-operation/degree536 endpoint is separately sealed at
`candidates/integer13-quadratic-trace`. The statements below concern the
14Z/119-operation/degree312 endpoint and are ordinary mathematical leads,
not another materialized or accepted frontier packet.

## Removing the explicit v-square factor is sound

Replace the119 guard

    Pair(v^2 G,eta*zeta,t)=Pos(p1,p2,p3)

by

    Pair(G,eta*zeta,t)=Pos(p1,p2,p3),
    Pair(x,y,t)=xy-(t^2-x-y+1)^2,
    Pos(p1,p2,p3)=1+p1^2+p2^2+p3(p3+1).

Keep its squared-guard/unit-product finalizer and entire three-root norm
unchanged. This deletes the two gatesv*v andG*(v*v). A complete literal
remap/checker has not been materialized; the anticipated count is117 and
the same exact degree312, still14 unrestricted integers.

At a new zero the unit-product finalizer first gives guard=norm=0. The
pair lemma givesG>0 andeta*zeta>0. Forv!=0 the original weak-scale
separation proof applies unchanged. It recovers integral roots and the
same old core constraints.

The formerly excludedv=0 branch can instead be ruled out without a size
assumption. HereY=a=ell=0,H=Delta=3 andDtau=1. The interval guard gives
c(k-c)>0, soc!=0. ConsequentlyQ=9i^2c^4>=9 and all three radicands
Df,1,Dy are positive, with

    Df=1+3i^2c^4, Dy=(QV^2-1)/(Q-1).

A norm factor makes a signed sum off=sqrt(Df),1,y=sqrt(Dy) rational.
After subtracting the signed1, let its rational value ber=epsilon*f+nu*y.
If r=0 then f=y. But that equality would give

    V^2=Df-(Df-1)/Q=Df-1/3,

contradicting integerV,Df. Thus r!=0 and

    f=(r^2+Df-Dy)/(2epsilon*r)

is rational, then y is rational. The integer-square lemma makesf integral;
the already retained adjacent-Pell descent makesy integral. Hence the
factor equation givesU|Z. Its reduction moduloM=2q^2, usinggcd(H,M)=1,
forcesM|(v-q^2). Atv=0 this would say2q^2|q^2, impossible sinceq!=0.
This discharges the exceptional branch before using the old weak-scale
hierarchy, without circularity.

Therefore every new zero hasv!=0,G>0,eta*zeta>0 and the same vanishing
norm as the old endpoint. Regenerate the four old private guard witnesses
using the pair lemma forv^2G andeta*zeta; keep every core coordinate andn.
Conversely an old zero hasG>0 andeta*zeta>0. Regenerate the new four
private witnesses usingG directly, retaining its vanishing norm. This
proves the full two-way integer-existence reduction, including arbitrary
signed assignments, with no canonical-completeness gap. It does not
remove a quantified coordinate.

The old leading guard term is-eta0^4 becausePeta has degree14, while
v^2G has degree6. Replacing it byG of degree4 leaves that term unchanged.
The same degree312 leading coefficient therefore survives. This argument
is specific to the three-root endpoint; it must not be silently reused
for an unrelated norm whose exceptional roots have different relations.

## The obvious three-witness replacement fails universally

Deleting one square fromPos would give the proposed equation

    Pair(x,y,t)=1+p^2+z(z+1).

It is not equivalent tox>0,y>0. Atx=1,y=9, positivity ofPair forces
t^2=9, soPair=9. The right side would requirep^2+z(z+1)=8. Since
z(z+1) is nonnegative, its only possible values up to8 are0,2,6;
none leaves a square. Thus no witnesses exist. This is an exact finite
counterexample, not a numerical extrapolation. Deleting the triangular
term instead fails already atx=1,y=4.

The inherited Pell argument does not currently license dropping the
eta*zeta sign condition orG>0. The interval bound is used to compare
f,tau,y before extraction and to bootstrap the first and main indices;
G>0 licenses the native rank packing. Reusing those conclusions to infer
their own hypotheses would be circular. A new proof could conceivably
avoid them, but no such unbounded implication or canonical map is claimed
here. The13Z trace result keeps both conditions and extracts their guard
root inside the norm.

## A separate finalizer tradeoff

Replacing the119 outputN+B^2+N*B^2 byN^2+B^2 preserves its integer zero
set pointwise as a conditionN=B=0. It costs118 operations and has exact
degree512 becauseN has exact degree256. This is a lower-operation,
higher-degree alternative, not a dominance improvement. No sibling has
been emitted for this minor tradeoff.
