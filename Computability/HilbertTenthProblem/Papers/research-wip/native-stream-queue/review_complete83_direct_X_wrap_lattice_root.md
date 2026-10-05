# Root review: factor-seven wrap bound and authentic index lattice

PASS at the stated necessary-condition scope. I read the full final
197-line author note, including its disclosed discarded scalar diagnostic,
and checked the proof against the previously reviewed boundary,
wrap-isolation and authentic-outer lemmas. The direct-X83 construction
remains open; this report neither supplies a wrapped zero nor excludes
every wrap.

With the author's notation, X>=2 and Y>=q^3 give
log4<L<log(4X) and M>log(4X)+6log q. The lower ratio estimate is exactly

    vXY < R*L/M+(2-epsilon)-2log(4AY)/M+2E0/M.

Since E0<1<log(4AY), replacing the final terms by3 is strict for both
signs. Starting from X<q and q>=16 gives L/M<1/5. The outer upper bound
R<q^3(q-1) and 3/q^3<1/5 then give vXs<q/5. This forces4X<q,
so L/M<1/7 and the same argument gives7vXs<q. Every step is all-size;
there is no extrapolation from the earlier q<=64 census.

For fixed(q,X,s,v), the two ratio intervals share width<1 and differ by
2M/L>14. Their convex hull width is below9log_2(q)+1<q^2-1; the last
inequality follows from log_2(q)<q and9q+1<q^2-1 at q>=16. The exact
outer source places R in one residue class modulo q^2-1, because
J=(q-1)/(B-1) is fixed by q and the fixed compiler. Consequently the
hull has at most one allowed R, and its disjoint intervals determine at
most one epsilon. The shifted MF_source, rather than the decoded native
mask, is correctly used in this residue class. The real interval test
is external proof notation and is not counted as a circuit gate.

The author's retained Review remark1 is also exact. Since
P-1=2XY^2 and psi_P(n)=n modulo P-1, setting k=2psi_P(n) makes
k-2n divisible by4XY^2. Hence h=v+(k-2n)/(XY) is a positive integer
and h=v modulo4Y. The norm identity follows from
P^2-1=4XY^2(XY^2+1). Positive eta,zeta are available because k>2;
their c=kY+eta obeys the ratio inequalities but is not shown to equal
the main Pell coefficient. This distinction prevents an invalid full-zero
claim. In the example q even>=16, X=2, Y=q^3, R=3q^3+3, both signs
give R<2n<2R, R=3 modulo4 and7vXs=14<q. The numerical outer bounds
hold, while the authentic congruence and main norm remain unclaimed.

**Review remark 1 (scope of the rejected shortcut).** The positive partial
completion satisfies the exact first Pell norm and index, so no congruence
consequence of those equations alone can rule it out. This refutes only
the proposed congruence-only exclusion; adding the main projection, outer
packing or input conditions may still eliminate it. The author's
discarded square test is not evidence for any stronger assertion.

The companion review JSON authenticates final author bytes and all three
committed dependencies. No author helper, finite diagnostic or saved
source array was executed, imported, evaluated or propagated during this
review. Fresh byte/hash metadata checks accompanied the handwritten
argument. No global lower bound, full compiler fixture, revised operation
count or new universality theorem is certified.
