# Boundary for combining complemented guards and zero-word elimination

The published complemented-guard104 proof retains a supplied positive
zero word Z, hence D<H and gap=(R-3)D/6<J/3 before the mask. Removing
Z and substituting Z=H-D saves one arithmetic addition formally, but
removes this premise. This note does **not** establish a103 construction.
It narrows the missing bound and records a local carry example.

## 1. Proving D<q would suffice

Keep the104 geometry, positive sign pair and paid input/time equations.
The positive factored lower block and the four-field program argument
still give intrinsic R>=9, q>=R^3, and 0<A_i<A<WH/(W-1)<J, where
J=(q-1)/2, W=R^3 and H=(q-1)/(R-1). Put g=(R-3)/6 and gap=gD.
After the retained kernel and geometry recover powers of three, g is
an integer and the packed integer is a Boolean ternary word.

Assume additionally D<q; this is the unproved premise. Write
gap=kq+t0, 0<=t0<q. Then k<g. The first normalized guard coefficient
is (t0-A0) mod q. If t0<A0, it exceeds q-J>J and is rejected by the
Boolean block mask. Otherwise its outgoing carry is k. The next
track coefficient A0+k is strictly less than q: indeed

    A0+k < WH/(W-1)+g < q/(R-2)+R < q,

using R>=9 and q>=R^3. Thus this track has no outgoing carry. The same
argument applies to the second guard/track pair. The supplied positive
Km<H also has no carry, so the fused zero pair has no incoming carry.

That pair is H+(q-1)D=(H-D)+qD. If D>H while D<q, its two normalized
chunks are

    low=q+H-D, high=D-1.

For both to be at most J would require D>=J+H+1 and D<=J+1,
contradicting H>0. Hence the Boolean masks force D<=H. This argument
even uses only the two chunk size bounds, not their full digit sets.

Once D<=H is recovered, gap<J/3 follows and the entire complemented
guard104 decoder applies. The fixed marked prefix supplies Z>0, as in
the separate zero-fusion proof. Therefore the genuine remaining issue
is excluding D>=q under the complete new system. A separate inequality
D+slack=q would pay back the one saved addition and is not a reduction.

## 2. High D can create local aliases

The D<q hypothesis is not merely a convenience of the pair argument.
Take

    R=9, q=R^4=6561, H=820, W=729,
    D=q+H=7381, gap=D,
    A0=A1=9, Kp=1, Km=819.

The first eight fields, evaluated with the complemented guards and
fused zero pair, normalize to

    [1,811,10,811,10,819,0,819],

with a carry of one into the following program block. All eight are
Boolean ternary words. Nevertheless Z=H-D=-6561 is negative, and the
supplied gap is larger than J. The positive sign pair and the gap
equation hold.

The time equation holds at the ordinary integer input x=291609, but
this fails the mandatory bound 2x<R. Thus the example is **not** a
counterexample to the actual103 proposal, whose input bound and full
controller equations remain present. It shows why the eight local masks
alone cannot restore the missing sign of Z.

## 3. A stronger family retains the paid input and complete counter time

In fact the paid input is insufficient to recover D<q from the counter
subsystem. Take an honest raw counter history with its true-zero head
subset Z0, which has initial bit zero. Let g=(R-3)/6 and retain its raw
tracks A0,A1 and complementary signs Kp,Km. The honest guards imply
that each Ai is supported on g(H-Z0). In particular Ai vanishes at
every zero-event block and is disjoint from gZ0.

Now replace the complementary zero field and gap by

    Dnew=H+qZ0, gapnew=gDnew.

Their formal zero word H-Dnew=-qZ0 is negative. Their first eight packed
chunks normalize to

    Kp, gH-A0, A0+gZ0, gH-A1, A1+gZ0, Km, 0, H-Z0,

with outgoing carry Z0 into the first program field. All eight chunks
are Boolean. To verify this without a carry assumption, use

    gapnew-Ai=(gH-Ai)+qgZ0,
    (H-Dnew)+qDnew=q(H-Z0)+q²Z0.

The subtraction gH-Ai removes a Boolean subset of gH. The additions
Ai+gZ0 join disjoint Boolean supports, so each is at most gH<J<q and
propagates no further carry. Signs retain their original ranges and
supports. These identities give the asserted eight chunks exactly.

Every supplied raw track, sign and gap remains positive. The gap source
6gapnew=(R-3)Dnew holds. Crucially the time equation and paid input bound
retain their exact old coordinates:

    W(A0+A1+Kp-Km)=A0+A1-2x,  0<2x<R.

Thus this is a complete counter-subsystem alias, not the earlier example
whose input bound failed. If the original zero word is nonzero, then
Dnew>q and the missing positivity of Z is violated. Its positive packed
lower block is below q9, so the crude packed bound cannot exclude it.

The checker instantiates the existing six-state counter path at R=27,
for x=1 and x=2. They have 12 and18 serial blocks respectively. Both
preserve the exact input and time relation and pass all eight masks,
with a positive carry Z0 into the program. The represented controller
is not asserted to survive that carry. In particular its raw D operand
and first program-field coefficient have changed, so neither the ROM
equation nor the remaining program-mask support tests follow. The
full103 proposal remains open; any proof must use those program
constraints, not only the counter masks and the paid input.

## 4. Evidence and open scope

`../verification/explore_complemented_guard_zero_bound.py/.json` checks
the conditional pair and guard bounds, the exact local alias, and both
honest-counter instances of Section3. Its
finite tuples are not claimed to satisfy the full controller or Pell
system.

An earlier bounded solver probe returned UNKNOWN on two even-height
instances and parity-based UNSAT on odd-height instances. These results
are not used as mathematical evidence; the explicit family above is
the maintained reproducible result. No source or certificate in the
published104 family is changed by this note.
