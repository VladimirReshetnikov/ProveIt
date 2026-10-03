# Necessary conditions for a filtered dual-rail FIFO controller

These elementary lemmas constrain the specific carry architecture appended
to the [native FIFO](native_dualrail_fifo67.md). They retain its Boolean
digit filters. They do not apply an unfiltered full-trit decision theorem,
and do not prove either universality or decidability of the remaining
coefficient family.

Write the two **read** weights as r0,r1 and the two **append** weights
as a0,a1, regardless of their field order in a particular source. Let
h,cs,cf be arbitrary fixed integers. The filtered carry transition is

    3k_(j+1)=k_j+h+r0*d0_j+r1*d1_j+a0*b0_j+a1*b1_j,
    k_0=cs, k_t=cf.                                    (1)

All four labels are Boolean. Scalar reads and appends are their pairwise
sums. The FIFO has W=3^m, q=3^t, t>=m, initial value I with 0<I<W,
and final value zero. Its transport identity is D=I+WA with 0<=D<q.
The original zero-sum variant has h=0,K=0,cf=0, where K is the sum of
the four weights. The later even-K variant uses h=0,cf=-K/2. The
lemmas below cover the fully general filtered controller, including
nonabsorbing endpoints. A zero-label loop at the endpoint would require
h=2cf, which is not assumed.

## 1. Centering the offset and bounding all carries

Put z_j=2k_j-h, zs=2cs-h and zf=2cf-h. If gamma_j denotes the four
weighted labels, equation (1) becomes

    3z_(j+1)=z_j+2gamma_j.                               (2)

This gives an exact zero-offset normalization with doubled label weights.
Conversely, any integral path for (2) starting at zs stays congruent to
h modulo2: the increment is even and division by3 preserves parity.
Thus k_j=(z_j+h)/2 is integral and recovers (1). This normalization does
not remove any paid arithmetic term involving the source's width.

Let P be the sum of positive weights and N minus the sum of negative
weights, over all four coefficients. Any one-step increment gamma lies
in [-N,P]. Define the centered bounds

    L=min(zs,-N), U=max(zs,P).

Induction in (1), or its finite geometric sum, gives

    L<=z_j<=U for every j.                               (3)

Indeed [L,U] is invariant under z -> (z+2gamma)/3. It contains every
centered integer carry, even when zs lies outside the attracting
interval [-N,P].

Unbounded total lengths require

    zf in [-N,P].                                       (4)

If (4) fails, contraction bounds t uniformly in terms of the fixed
coefficients and endpoints. For h=0,cf=-K/2, it specializes to
P<=2N and N<=2P. The next lemma gives a
stronger bound on queue width rather than just total length.

## 2. The empty FIFO forces a read-only terminal block

The exact transport D=I+WA<q gives A<q/W=3^(t-m). Therefore the last
m append trits are zero. Their two Boolean labels must both be zero;
the nonunique splitting of trit1 is irrelevant here. This is also the
fact that the final queue contains the last m appended trits.

Let PR be the sum of positive read weights and NR minus their negative
sum. Set e=z_(t-m). Across the last m transitions, only read increments
occur, and these lie in [-NR,PR]. Multiplying their geometric sum gives

    e-NR(W-1)<=W*zf<=e+PR(W-1).                         (5)

Together with (3), this proves an effective finite-width obstruction:

    if zf<-NR, then W<=floor((-L-NR)/(-zf-NR));
    if zf>PR, then W<=floor((U-PR)/(zf-PR)).              (6)

A bound below one means no positive width is possible. Since I<W, each
case bounds the ordinary inputs as well. In the I=2x variant,
`x<=floor((W_bound-1)/2)`; in the I=6x+2 variant,
`x<=floor((W_bound-3)/6)`.

Consequently a necessary condition for unbounded ordinary inputs is

    -NR<=zf<=PR.                                        (7)

For h=0,cf=-K/2, this reads -NR<=-K<=PR. It is stronger than (4),
because the read-only interval is contained
in the full-label interval. It does not assume that terminal carry is
absorbing or that the length can be padded after acceptance.

At an endpoint there is further rigidity, without an immediate finite
width bound. If zf=-NR, let gamma_j be the read increments of the last
m steps. Equation (5) sharpens to the exact equality

    2 sum_(j=0)^(m-1) (gamma_j+NR)*3^j=-e-NR<=-L-NR.     (8)

Every summand is nonnegative. Thus all sufficiently late increments in
that terminal block must be exactly -NR, with an index cutoff depending
only on the fixed coefficients and cs. For nonzero read weights this
fixes each read label to its minimizing value. A zero read weight leaves
its label free. Likewise, at zf=PR,

    2 sum_(j=0)^(m-1) (PR-gamma_j)*3^j=e-PR<=U-PR,        (9)

so all sufficiently late increments maximize the read sum. These are
constraints on the end of a run, not a classification of its earlier
computation.

## 3. A sign obstruction that uses the entire FIFO identity

Suppose both read weights have the same strict sign sigma in {1,-1},
and sigma*zf<=0. Define

    mu=min(sigma*r0,sigma*r1)>0,
    beta=min(sigma*a0,sigma*a1), s=sigma*zs,
    B=floor(max(2*max(0,-beta),abs(s))/(2mu)).            (10)

Then every accepted positive initial queue satisfies **I<=B**.

To prove it, let D0,D1 and A0,A1 be the nonnegative represented Boolean
read and append words. Since D=D0+D1 and A=A0+A1, the global telescoping
form of (1) gives

    q*sigma*zf
      =s+2sigma*r0*D0+2sigma*r1*D1
                   +2sigma*a0*A0+2sigma*a1*A1
      >=s+2mu*D+2beta*A
      =2mu*I+2(mu*W+beta)*A+s.                          (11)

If I>B, then 2mu*I>|s| and mu*W+beta>0 because W>I. The right side is
strictly positive, whereas the left side is nonpositive. This is a
contradiction. No relaxation of the Boolean labels is used to claim a
converse; (11) is only a valid lower bound on actual witnesses.

In particular, the zero-sum, zero-terminal architecture cannot represent
an infinite ordinary-input set when both read weights have the same
strict sign. More generally this applies to any zero-label absorbing
terminal carry, since h=2cf then makes zf=0. To escape the obstruction,
same-sign read weights require sigma*zf>0. Combined with (7), positive
read weights of total S require 0<zf<=S. For the even-K special case
this says -S<=K<0; sign reversal gives the negative-read case.

If both read weights equal u and both append weights equal -u, and the
terminal zero-label state is absorbing (h=2cf), the exact global
equation reduces further to

    u*(I+(W-1)A)+cs-cf=0.

For u nonzero this again bounds I. For u=0 it imposes only cs=cf, so
the bare FIFO projection is all positive inputs or none, according to
that fixed equality. This special case is not representative of the
remaining opposite-sign or zero-read-weight families.

## 4. Evidence and scope

The [checker](pell_kernel_dualrail_carry_structure.py) directly enumerates
small coefficient systems and integral read-only terminal blocks. It
checks the effective width bounds, both exact endpoint deficit formulas,
the sign-dominance inequality, and the transport implication that the
last m append trits are zero. The [receipt](pell_kernel_dualrail_carry_structure.json)
records this finite evidence; the universal statements are proved above.
Independent full scoped proof/source/default review passes, including
the signed endpoint inequalities and the same-sign dominance argument.

The remaining coefficient region is not classified. These tests neither
construct a universal filtered controller nor show that every filtered
controller is decidable. The complete universal bound remains76.

Independent complete proof/source review and fresh default-receipt replay
passed, including the centered parity, both width bounds, endpoint
identities and sign obstruction. No findings were reported.
