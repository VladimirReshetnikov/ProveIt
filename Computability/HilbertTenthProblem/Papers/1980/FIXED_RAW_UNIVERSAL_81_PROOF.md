# An 81-operation fixed-index universal certificate

For every recursively enumerable set S of positive integers, there are
effectively computable fixed positive compiler numerals for which the
system below has positive integer witnesses exactly when the raw input
x belongs to S. The complete certificate uses **81 operations: 44
multiplications and 37 additions/subtractions**, with **33 positive
existential witnesses and 21 equations**. Numerals and equality tests
are free; multiplication by a numeral is charged.

The [complete source and checker](../verification/explore_fixed_raw_universal_81.py)
and [receipt](../verification/explore_fixed_raw_universal_81.json) retain
the full outer and Pell schedules of the
[82-operation construction](FIXED_RAW_UNIVERSAL_82_PROOF.md).
The change removes the addition x+2: a stationary first machine step
and a relocated Start window make the two marker centers exactly x
cells apart. The fixed-base input relation becomes W=B^x.

This is a mathematical proof with symbolic and finite computational
checks, not a proof-assistant formalization. Full astronomical Pell
tuples are not numerically materialized. The existing TeX/PDF and Lean
artifacts retain their separately stated historical counts.

## 1. A fixed machine and two windows at distance x

Normalize a fixed semidecision machine for S to use a one-sided tape
with origin0, never visiting a positive coordinate. The initial tape
has x+2 ones, at positions -(x+1),...,0; its head is in state q0 at0.
Its first transition writes the origin flag2 and **stays** at0 in a
distinct nonhalting state q1. From q1, a fixed algorithm counts the
unary input, subtracts2, and simulates a semidecision procedure for S.
The usual folded two-track simulation makes this one-sided without
bounding its eventual space usage. Accepting halt is absorbing; all
other missing transitions can enter a nonhalting loop. This fixed
machine halts on the stated unary input exactly for x in S.

Use precisely the boundary, phase, and exact transition clauses of
the [helical tableau](EXPLORATION_HELICAL_UNARY_TABLEAU.md), with this
new machine. A vertical boundary is a uniform V at all times; row
boundary bits propagate horizontally only between non-V cells.
Initialization has the phase form

    L^a I^u Q R^b, a,b,u>=1.

Here L and R are blank and headless, I is a headless1, and Q is a1
with head q0. The required inputs use u=x+1>=2. No head may escape
through a V; each last interior row has a halted head.

Let H denote the horizontal boundary tile. Use the following fixed
three-by-three windows, writing `(symbol,head,phase)` for interior tiles.
The new Start S3 is centered on the **last I**, one cell left of Q:

    H                 H                  H
    (1,nohead,I)      (1,nohead,I)       (1,q0,Q)
    (1,nohead,none)   (1,nohead,none)    (2,q1,none).

The End E3 is centered on the **first I**:

    H                 H                  H
    (0,nohead,L)      (1,nohead,I)       (1,nohead,I)
    (0,nohead,none)   (1,nohead,none)    (1,nohead,none).

The stationary first step is essential: it leaves the last I headless
in the next row. Thus both windows are fixed for every u>=2, including
u=2, where their centers are adjacent. Every initialized strip with
u>=2 has these windows, and their center separation is u-1. If u=1,
neither window occurs: the two-I substring required by either is absent.
Conversely every S3 is a last I followed by Q, and every E3 is a first
I followed by another I, both on an initialization row.

All symbols, states, local rules and the two windows are independent
of x. Apply the exact three-by-three window lift, giving one fixed
alphabet and a ternary relation on center, right and next windows.

## 2. Exact cyclic semantic theorem, including short intervening strips

For each positive x, the normalized machine halts on x+2 ones if and
only if there are N,h>=1 and a cyclic lifted word satisfying:

* the fixed ternary relation at offsets0,-1,-h;
* exactly one S3, at index0;
* x<N and an E3 at index x.

Completeness can give exactly one E3 as well.

For soundness, pull back by the index -z-h*y modulo N. The exact lift
overlaps reconstruct a valid original plane, periodic in each axis.
S3 gives an initialized Q immediately to its right. The phase graph
has no directed cycle containing Q, so horizontal periodicity forces
vertical boundaries on both sides. Choose the nearest pair. Row
boundaries are uniform inside this strip; vertical periodicity gives
a next one. The bounded rectangle between them starts with the exact
unary row. The transition and no-escape induction keeps exactly one
genuine head, and its final row is halted. This is the same finite-run
argument as in the helical theorem and does not depend on the marker
being centered on the head.

Walk left x cells from S3. The visited cyclic indices1,...,x are all
distinct and nonzero, so the path contains no S3. Its endpoint is E3.
Suppose this E3 belonged to a different vertical strip. Its first I
is followed by another I, so that strip has u>=2 and therefore has
its own S3 at its last I on this same initialization row. Entering
that strip from the right would cross that S3 strictly before E3,
a contradiction. Any intervening u=1 strips, which have neither
marker, do not alter this argument about the destination strip.
Therefore the endpoint is the first I of the distinguished strip.
The separation is u-1=x, so its initial unary length is u+1=x+2.
Its halt is exactly acceptance of the raw input x.

This argument permits arbitrary N and h. It assumes neither h|N nor
that h is the physical width of the recovered strip. The phase-row
crossing statement concerns only strips containing a marked endpoint;
it does not incorrectly assert that every initialized Q yields S3.

For completeness take any finite halting run, put u=x+1, and let e<=0
be its least visited coordinate. Choose

    a>=max(2,1-e-u), w=a+u+4,
    Htime>=max(3,number_of_transitions+2).

Use the base array G with one constant V column and one horizontal
boundary row; the initial interior row is L^a I^u Q R^2. Put the
genuine run inside, then repeat its absorbing halt. Extend by

    T(z,y)=G[z mod w, (y+floor(z/w)) mod Htime].

Every seam is valid by the uniform V and the absence of horizontal
row-boundary propagation across V. The plane has periods (w,-1)
and (0,Htime). Take h=w, N=w*Htime, and place a base cell (r,s) at

    i=-(r-(w-4))-h*(s-1) mod N.

The origin w-4 is the last I, rather than the Q at w-3. This is a
bijection, as in the helical theorem, and actual cyclic windows
give the exact lifted relation. There is one S3 at0 and one E3 at
u-1=x. Both lie away from V. We have x<w<N and, from the freely
chosen padding, N>=4. The width may be arbitrarily large after the
halting run is known; no input-only computable space bound is imposed.

## 3. The complete arithmetic source

Use the unchanged native compiler of the 82 proof, enumerating E3
as state0 and S3 as state1. Its numerals B=2^d, CS, DC, DR, DY, MC,
MF and the cell bit width d depend only on this fixed machine.
Its two marker slots are absent in Z, and its native mask populations
sum to d. The complete witness list remains

    q,P,C,v,J,align,F,alpha,z,Z,
    a,c,dmain,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,muP,delta,phiP,rho.

The source names and their mathematical aliases are exactly as in
Section2 of the 82 proof. In particular `cell_bits` is d and the
source coordinate `d` is dmain. Put

    u_binary=d*x, Lambda=q^2, D0=q^3,
    X=w*D0, Yp=s*D0, Delta=a^2+4a+3, Uaux=j*c-(2r+1).

The seven outer equations are

    (B-1)J=q-1,                     P*v=q,
    (B-1)align=P-1,                 C+alpha+u_binary=q,
    (DC+B*DR+DY*P)C=F+z*(q-1),
    r=(Lambda-Z-qF)*(Lambda-1)+(MC+q*MF)J,
    C=CS+Z+W.                                            (1)

The ten kernel equations are unchanged:

    X*Yp^2*(X*Yp^2+1)*k0^2=tau*(tau+1),
    c=Yp*k0+eta,                    k0=eta+zeta,
    k0=r+1+h0*X*Yp,
    a=Yp*(X+1),
    dmain=X+a*c+gamma*(4a+3),
    dmain^2=Delta*c^2+1,
    (i*c^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)*(Uaux^2-yaux^2)=1-yaux^2,
    Uaux=of-c.                                            (2)

The four input equations are

    kappa=u_binary+delta*(a+1),      c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+a*kappa+rho*(4a+3).                              (3)

These are all21 equations. All33 existential witnesses and the raw
input x must be positive integers. No extra power, mask, inequality,
marker or period predicate is imposed outside this source.

## 4. Arithmetic soundness and positive completeness

The preliminary arguments of the 82 proof apply unchanged with
u_binary=d*x in place of d*(x+2). Positivity of (1) first gives
q>=P>=B, Z<C<q, W<C<q, and 0<u_binary<q. The mask ranges then imply
F<q and q^2<=r<q^4. The retained kernel is applied at D0=q^3 before
any power interpretation. It recovers X=2^(2r+1), c=psi_(a+2)(2r+1),
a>X, the central-binomial divisibility, q=B^N and P=B^h.

The norm and gap in (3) give kappa=psi_(a+2)(v0) with0<v0<2r+1.
Reduction modulo a+1 gives v0=u_binary modulo a+1; both are below
a+1, so v0=u_binary. Reusing the kernel's modulus4a+3 gives

    muP-a*kappa = 2^u_binary mod(4a+3).

Since 2^u_binary<2^q<2^r<X<a and W<q, (3) proves the exact equality
W=2^u_binary=B^x. Thus x<N. The inverse packed mask proof recovers
Z AND MC*J=0 and F AND MF*J=0. The insertion C=CS+Z+W types the
whole word with Start at0 and End at x. The two positions are
distinct since x>0. Exact transport, at-most-one clauses and occupancy
propagation under shift1 give the fixed ternary relation and exactly
one of each marker. The semantic theorem of Section2 proves x in S.

For completeness use the padded cyclic word of Section2 with dummy
bits0. Set q=B^N, P=B^h, W=B^x, Z=C-CS-W, with the same repunit,
geometry and transport quotients as in the 82 proof. There are N>=4
nonzero genuine cells, so removing the two distinct marker cells
leaves Z>0. This uses the actual completeness padding: soundness
only supplies N>x, which alone would not imply N>=4.

Native cell bounds give C<=(B-2)J and q-C>=J+1. Because N>x,

    J>=B^(N-1)>=B^x=2^u_binary>u_binary,

so alpha=q-C-u_binary>0. Positive wrap quotients give z>0.
The two masks vanish and the actual packed r is odd, since Z is
even, MC and J are odd, and qF is even. Its exact popcount gives
the required binomial divisibility. The unchanged fresh positive
kernel construction supplies all seventeen coordinates of (2) at
this actual r; an earlier numerical Pell tuple is not reused.

For (3), choose kappa=psi_(a+2)(u_binary), muP=chi_(a+2)(u_binary),
and set delta=(kappa-u_binary)/(a+1), phiP=c-kappa,
rho=(muP-a*kappa-W)/(4a+3). The retained Pell congruences give
integrality. Here u_binary=d*x>=4, so kappa>u_binary and delta>0;
u_binary<q<2r+1 gives phiP>0. Finally

    muP-a*kappa=2*kappa-psi_(a+2)(u_binary-1)>kappa>=2(a+2)>W,

which gives rho>0. Thus every supplied witness is strictly positive,
including x=1. The proof uses only u_binary>=2 at this final step;
the former u_binary>=12 was not an essential hypothesis.

## 5. Exact cost and evidence

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Geometry, transport, masks, bound register and markers |12|12|24|
| Retained positive Pell kernel |25|18|43|
| Fixed-base raw-input bridge, including d*x and stronger bound |7|7|14|
| **Complete source** |**44**|**37**|**81**|

The schedule removes `raw_t=x+2` and replaces `scaled_t=d*raw_t`
with `scaled_t=d*x`. The two affected source residuals are precisely
the raw bound and the input index congruence; the other19 residuals,
all outer instructions and all kernel instructions are unchanged.
The checker expands every residual, including the retained acyclic
correction by a preceding norm equation, and checks that all supplied
fixed aliases depend only on compiler numerals.

Semantic tests cover the stationary first step, fixed windows at
distance x, x=1, one-I strips lacking both windows, all helical seams,
noncanonical strides with h not dividing N, duplicate marker words,
malformed initialization and rejected nonhalting truncations. A
separate mixed-strip enumeration tests the revised crossing argument.
Common arithmetic examples include the smallest input and dummy bits
at either marker. Their moderate Pell parameters are independent of
the full packed index; full positive kernel completeness is proved
mathematically above. No global optimality claim follows.
