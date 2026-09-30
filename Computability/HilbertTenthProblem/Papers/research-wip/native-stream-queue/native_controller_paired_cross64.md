# A complementary-lane filtered paired queue in64 operations

The local Boolean rule

    a0+d1=1                                           (1)

gives a different filtered queue architecture. Every physical read pair
has two possible append pairs: a0 is fixed and a1 is free. In particular
a raw input trit2 no longer forces one complete label, so the previous
[raw-input obstruction](native_controller_paired_raw_obstruction.md)
does not apply to this family.

The exact queue component costs **64=32M+32A**, with19 equations and29
strictly positive witnesses besides ordinary x. A chosen centered carry
specialization costs69, or71 with even time and width. A fully general
affine carry relation costs71, or73 with that alignment. These are exact
finite-machine relations, not universal representations. Loading under a
chosen controller and correct accepting computation remain unproved.

## 1. Literal filter, field bounds and raw-kernel proof

Retain the44-operation raw Boolean ternary kernel, including X=wq and
Y=3s+1, and the six-operation Horner packing from
[Boolean55](input_bridge_boolean_ternary60.md). Supply the same seventeen
positive kernel coordinates. Compute the six additional additions

    X_bound=r+bound_beta,
    H=F0+F3, twiceH=H+H, repunit=twiceH+1,
    other=F1+F2, other_bound=other+alpha,

and compare X_bound=X, repunit=q, other_bound=q. Thus this typing and
filter source costs56=28M+28A. Its exact outer equations are

    r=F0+qF1+q^2F2+q^3F3,
    r+bound_beta=X,
    2(F0+F3)+1=q,
    F1+F2+alpha=q.                                   (2)

Before any power or digit conclusion, F0,F3>0 gives q>=5, and every Fi
lies strictly between0 and q by(2). Therefore

    q^3+q^2+q+1 <= r < q^4, r>=156,
    X>r, Y>=4, E=XY>r+1, a=Y(X+1)>2r+1.

Writing A0=a+3 and P=2XY^2+1 gives P>A0 and6XY^2>a. These are exactly
the numerical hypotheses of the raw kernel proof in Boolean55 Section2.
That argument never uses the old joint bound after these facts have been
established. In detail, the first index is n=r+1 modulo E and n>=r+1;
the ratio interval forces the main index p>=n+1>=158. This gives the
strong auxiliary rank and half-parameter bounds, recovers p=2r+1, and
the signed positive-branch theorem forces r even. The first index is
then exactly r+1. Using the lower ratio estimate first gives Y>=X^r and
a>X^(r+1), which justifies the upper small-error estimate. The exponent
congruence modulo6a+8 has representatives X and3^(2r+1), both below a,
so X=3^(2r+1). Consequently q=3^t with t>=2, and the ratio gives

    Y=floor((X+1)^(2r)/X^r).

As Y=3s+1, the central binomial coefficient is1 modulo3. There is no
ternary doubling carry in r. The already proved bounds Fi<q ensure
that the packing has no field carries, hence every Fi is a positive
Boolean ternary word. Its parity sum is even because r is even and q odd.

Now H=(q-1)/2 is the ternary repunit. In F0+F3=H the position residual
is in[-1,1], so successive reductions modulo3 prove exactly(1).
Conversely(1) gives that equality. The other bound becomes automatic
after typing: F1,F2<=H implies F1+F2<=q-1. There is **no bound on the
sum of all four fields** in this source.

For the positive converse take any q=3^t, t>=2, positive Boolean fields
with F0+F3=H and even total sum. Pack r as in(2), set J=2r+1,
X=3^J, w=X/q, Y=floor((X+1)^(2r)/X^r), s=(Y-1)/3,
bound_beta=X-r, and alpha=q-F1-F2. All are positive integral: the
Boolean packing has even population, so its central binomial coefficient
is1 modulo3. Use the full positive plus-kernel construction from
Boolean55 Section3 at these actual X,Y,r. Every ratio, growth, auxiliary
congruence and positivity hypothesis is the same; its only outer joint
slack is replaced by the new positive alpha just specified. This is a
fresh raw-kernel converse and does not assume a positive old joint slack.

## 2. Direct paired transport from a positive split of2x

Add positive x,W,L,width_beta,I0,I1 and the eight operations

    I=2x; split=I0+I1;
    tail0=W*F0; transport0=I0+tail0;
    tail1=W*F1; transport1=I1+tail1;
    width=I+width_beta; divisor=W*L.

Compare split=I, F2=transport0, F3=transport1, width=W and divisor=q.
These are4M+4A above56, giving64=32M+32A and19 equations. The exact
projection is a synchronized pair of Boolean width-m queues, with
q=3^t, W=3^m, m>=1 and t>=m+1, initial positive Boolean words I0,I1
summing to2x<W, terminal queues both zero, all four word tracks nonzero,
and local rule(1). The FIFO identities are

    F2=I0+W*F0, F3=I1+W*F1.                           (3)

They prove the initial Boolean digits, local queue recurrences and empty
endpoints exactly as in the reviewed paired63 proof. Every Fi<q and
positive append streams give q>W. Conversely any such run gives(3) and
positive width_beta,L. Also

    sum Fi=2x+(W+1)(F0+F1)

is even, so the fresh positive kernel converse from Section1 applies.
The bound on F1+F2 is automatic for all Boolean fields below q. This
establishes both directions for arbitrary runs, without padding or a
changed endpoint.

## 3. Two sweeps supply every ordinary positive input

Every positive even integer2x has a positive Boolean ternary split:
split any trit2 as1+1; if no trit2 occurs, its positive even digit sum
gives at least two1s to distribute between the rails. Choose such I0,I1
and a power W=3^m>6x. Write Hm=(W-1)/2 and put

    q=W^2, t=2m,
    F0=Hm-I1, F1=Hm,
    F2=I0+W*(Hm-I1), F3=I1+W*Hm.                     (4)

All four fields are positive Boolean words. In the first sweep choose
a1=1 everywhere and a0=1-d1. The queues become(Hm-I1,Hm). In the
second sweep choose a1=0; its read d1 is everywhere1, so a0=0 and
both queues become empty. Formula(4) records these exact two sweeps.
It has F0+F3=(q-1)/2, F1+F2<q, and automatic even total sum. Thus all
outer coordinates and the full kernel map are positive. For even block
alignment choose m even; t=2m is then also even.

This proves bare-component completeness. It does not assert that an
arbitrary nonzero controller accepts these runs.

## 4. Centered and general affine controllers

Fix arbitrary integer coefficients and endpoints in

    3c_next=c+h+u0*d0+u1*d1+v0*a0+v1*a1,
    c_initial=cs, c_terminal=cf.                      (5)

Using a0=1-d1, put g0=v1, g1=u0, g2=u1-v0. Its exact global equality
is

    g0*F1+g1*F2+g2*F3+(h+v0-2cf)H=cf-cs.             (6)

There are two useful schedules. If the fixed constants are **chosen**
to satisfy h+v0=2cf, three scalar products and two additions, followed
by a free comparison, cost5=3M+2A and give69=35M+34A. This restriction
is a design choice, not a theorem forced by empty queues.

For arbitrary constants, multiply the already computed H by the fixed
offset h+v0-2cf and add it. These two extra operations give the fully
general71=36M+35A. Both variants have20 equations and29 positive witnesses
besides x. Signed fixed numerals and computed registers are allowed.

Telescoping(5) proves(6). Conversely successive reductions modulo3 of
the reconstructed global equation recover every integral intermediate
carry and the stated final value. Thus both schedules certify the whole
affine carry graph on the eight physical labels allowed by(1), not a
selected finite-state subgraph.

At an empty endpoint the last m append pairs are00. Equation(1) makes
their secondary reads1, but does not fix their primary reads. Hence this
tail does not justify imposing h+v0=2cf as a necessary endpoint condition.
The general schedule avoids any such assumption.

## 5. Two operations give even temporal and width blocks

Supply positive time_root,width_root and compute their squares, compared
freely with q,W. Since q=3^t and W=3^m are already proved powers, these
two products impose precisely even t and even m. Conversely the roots
are3^(t/2),3^(m/2), so they are positive integral. This gives

| Variant | M | A | Total | Equations | Positive witnesses besides x |
|---|---:|---:|---:|---:|---:|
| Complementary-lane queue |32|32|64|19|29|
| Chosen centered controller |35|34|69|20|29|
| Centered, even time and width |37|34|71|22|31|
| General controller |36|35|71|20|29|
| General, even time and width |38|35|73|22|31|

This is arithmetic block alignment only. No selected two-step alphabet,
phase-dependent interpretation, loader or halting convention follows
from the square equations.

## 6. A natural history interpretation and evidence boundary

For arbitrary Boolean states u,v define Code(u,v)=(1-u,v), with no
disjointness restriction. Equation(1) permits
`Code(u,v)->Code(u',w)` exactly when u'=v. This remains true coordinate
by coordinate for arbitrary Boolean state vectors in aligned blocks.
Thus it copies the current logical bit to the next history slot while
freely choosing the next logical bit. In the centered specialization its
microscopic controller is exactly

    3*k_next=k+g0*w+g1*(1-u)+g2*v.

All eight Boolean triples(u,v,w) are allowed by the physical filter.
This is an unrestricted second-order Boolean history interface, unlike
the disjoint edge codes of the earlier filter. A controller must still
verify the intended update rule. It does not supply an arbitrary finite
state alphabet or a cellular-automaton compiler for free.

The [checker](native_controller_paired_cross64.py) audits the complete
five source DAGs, independent polynomial residuals and the inherited
norm correction. It checks untyped preliminary bounds, finite Boolean
typing and direct paired semantics, two explicit positive maps for each
of200 inputs, and local/global carry equivalence including nonzero
offsets. The [receipt](native_controller_paired_cross64.json) is replayed
by default. Huge Pell coordinates are provided by the proved parametric
map rather than materialized. Independent full proof, source and fresh
default review passed, including the converse without the old joint
bound and both controller endpoint scopes. The complete universal bound
remains76.
