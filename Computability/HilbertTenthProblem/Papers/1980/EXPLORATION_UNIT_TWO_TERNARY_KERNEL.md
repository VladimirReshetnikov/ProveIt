# Unit-two ternary masks and a general-scale Pell kernel

This note supplies a counted component for ternary history and ripple
experiments. It does not claim a universal construction. It proves a
43-operation kernel at a general positive scale, in two fixed sign
variants, and the direct mask r=P0,D0=L. The proof includes the small
q=3 cases needed by the four-field ripple; no unpaid q>=9 guard is used.

The companion checker is `../verification/explore_unit_two_ternary_kernel.py`.
The earlier frozen native-positive 48-operation component is unchanged.

## 1. Direct mask and its sharp overflow endpoint

Let N>=1 and L=3^N. For 0<=P0<L,

    L | binom(2P0,P0)

holds exactly when P0 has N ternary digits whose lowest digit is two
and whose other digits are one or two. Indeed, there are at most N
carries when P0 is doubled. The unit position carries exactly when
its digit is two; with an incoming carry, a later digit carries
exactly when it is positive. Beyond the N positions no further carry
can occur. Kummer's theorem proves the assertion and exact valuation N.

This mask remains sound in the larger window

    0<=P0<=(3L-1)/2.                                 (1)

More precisely, divisibility in (1) forces P0<L and the stated digits.
To see the overflow rejection, put Jbig=(L-1)/2 and write P0=L+x
for 0<=x<Jbig. At the highest digit where x differs from the all-one
Jbig, x has zero, while every higher digit is one. That zero kills any
incoming carry, the higher ones cannot restart it, and neither can
the extra top one. At least two of the N+1 positions lack carries,
so the valuation is at most N-1. At x=Jbig all N+1 digits of P0 are
one and no position carries at all. This also rejects the closed
endpoint (3L-1)/2.

The first false acceptance is

    Pplus=(3L+1)/2.

Its lowest digit is two and its other N digits are one, giving
valuation N+1. The next integer Pplus+1 is also accepted: its lowest
digit is zero, its next digit is two, and the higher digits are one.
It has valuation N. Thus the extra position can compensate for a
missing unit carry beyond the sharp window. When N is even, Pplus
is even and Pplus+1 is odd; neither fixed parity removes the need
for a bound. These endpoints differ from those of the mask r=3P0+2.

The field interfaces below use the strictly smaller upper range
P0<3(L-1)/2, which is safely contained in (1).

## 2. A kernel with no square-scale assumption

Let D0,r be positive supplied integers satisfying

    D0>=81, r>=27, r<2D0, D0<r^2.                     (2)

No particular formula for D0, and no integer square root, is assumed.
For a fixed sign sigma in {+1,-1}, write

    U=wD0, Y=sD0, E=UY, Q=UY^2, P=2Q+1,
    a=Y(U+1), A=a+3, M=6a+8, D=A^2-1=a^2+M,
    Jmain=2r+1, R=ic^2, K=R^2,
    u=jc+sigma Jmain.

The ten source equations are

    tau(tau+1)=(E^2+U)(Yk)^2,
    c=Yk+eta, k=eta+zeta,
    k=r+1+hE,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+Dc^2,
    R^2=D(f^2-1),
    K(u^2-y_aux^2)=1-y_aux^2,
    u=of+sigma c.                                    (3)

Besides the parameters D0,r, the remaining sixteen supplied variables
are positive integers. The sign is a fixed choice of certificate;
it is not a freely selected or uncharged input. The plus variant is
used for an even-r converse and the minus variant for an odd-r converse.
Their soundness argument does not need that parity assumption.

The plus schedule is the retained 43-operation base-three core. For
the minus variant change just

    u=Jmain+jc   to   u=jc-Jmain,
    u_rhs=c+of   to   u_rhs=of-c.

Each still uses one arithmetic operation. Both variants have exactly
25 multiplications and18 additions/subtractions, with10 free comparisons.

## 3. Soundness at the smaller preliminary thresholds

Positivity and (2) imply

    U,Y>=D0>=81,
    E>=D0^2>r+1,
    a>=D0(D0+1)>2r+1.                                (4)

The first triangular norm is the ordinary Pell norm with parameter P.
Thus k=psi_P(t), and P=1 modulo E gives t=r+1+vE with v>=0.
The main norm gives c=psi_A(p), d=chi_A(p). Since
P-A=UY(2Y-1)-Y-2>0 and c>Yk>k, one has

    p>=t+1>=r+2>=29.

In particular c>A^6>AD^2, c>Y(r+1)>Jmain, and0<2p<=c.
These are the generic relaxed auxiliary-rank hypotheses. The proof in
`PELL_RELAXED_AUXILIARY_PROOF.md` yields

    f=chi_A(m), p|m, c|m, R=D psi_A(m)

for a positive index m, with0<2p<=c<=m. Its former threshold66
was used to obtain the large-coordinate inequality, not as an
independent extra hypothesis; p>=29 supplies that inequality here.

The computed u is positive in both sign variants. For sigma=-1,
u=jc-Jmain>=c-Jmain>0; for sigma=+1 this is immediate. The last norm
is therefore the ordinary positive Pell equation

    (Ru)^2-(R^2-1)y_aux^2=1.

Its index z is odd, as an even chi index is plus or minus one modulo R.
For z=2h0+1, the integer polynomial chi_R(z)/R=Q_h0(R^2) satisfies

    Q_h0(1-A^2)=(-1)^h0 psi_A(z),
    Q_h0(0)=(-1)^h0 z.

These identities and their recurrences are proved in
`HALF_PARAMETER_PELL_92_PROOF.md`, Section3. Here u=sigma c modulo f.
Squaring therefore gives the same congruence psi_A(z)^2=c^2 modulo f,
and hence chi_A(2z)=chi_A(2p) modulo chi_A(m). The chi step-down lemma
at comparison index2p<=m gives z=plus or minus p modulo m, hence
modulo c. Since c|R, the other polynomial identity and
u=sigma Jmain modulo c give Jmain=plus or minus p modulo c.

Both Jmain and p lie in (0,c). The alternative Jmain+p=c is impossible
because c=psi_A(p)=p modulo2 and Jmain is odd. Thus p=Jmain in either
sign variant. This argument has not assumed any parity of r.

If v>=1, E>r and

    (2P-1)-4A=4Y(U(Y-1)-1)-11>0

give c/k<1/2, contradicting c/k>Y. Hence t=r+1. For
xi=(U+1)^(2r)/U^r the same elementary Pell bounds now give

    c/k>xi,
    c/k<xi*(1+3/a)^(2r).

The larger index range and smaller scale still give

    6r/a<12/(D0+1)<=12/82<1/2.

Consequently c/k<xi*(1+12r/a), Y>=U^r, a>U^(r+1), and

    0<c/k-xi<24r/(U+1).                              (5)

The recurrence of chi_A(j)+(3-A)psi_A(j) gives 3^j modulo M.
The exponent equality implies U=3^Jmain modulo M. Since U>=81>9,
both positive values lie below M:

    U<a<M, 3^Jmain=3*9^r<U^(r+1)<a<M.

Thus U=3^Jmain. In particular D0, which divides U, is a power of
three. Now U>48r and (5) is below1/2. The exact binomial expansion
xi=F+T has0<T<1/6 and F=binom(2r,r) modulo U. The positive interval
forces Y=F, and therefore

    D0 | binom(2r,r).                                 (6)

This proves soundness of both fixed-sign kernels at (2).

## 4. Full positive converse for the appropriate fixed sign

Suppose (2) holds, D0 is a power of three, (6) holds, and

    sigma=(-1)^r.

Choose Jmain=2r+1, U=3^Jmain and
Y=floor((U+1)^(2r)/U^r). Since D0<r^2<U, w=U/D0 is a positive
integer. The binomial expansion and (6) similarly give positive
integral s=Y/D0. Choose a,A,P,c,d,k at their canonical indices
Jmain and r+1. The ratio estimates give positive integral
eta=c-Yk, zeta=k-eta. The formulas

    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E,
    gamma=(d-U-ac)/M

are positive integral by the same norm, index and exponent congruences;
in particular d-ac=3c-psi_A(Jmain-1)>2c>U.

Choose

    m=2cJmain, f=chi_A(m), i=D psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(Jmain), u=chi_R(Jmain)/R.

The power expansion of (d+c sqrt(D))^(2c) gives
c^2|psi_A(m), so i is positive integral. Since Jmain is odd,
u is an integer polynomial in R^2. Its two congruences are

    u=(-1)^r c=sigma c modulo f,
    u=(-1)^r Jmain=sigma Jmain modulo c.

Therefore set

    o=(u-sigma c)/f, j=(u-sigma Jmain)/c.               (7)

They are integers. Pell growth gives u>c>Jmain, so both are positive
for either sign. Their definitions are precisely the two signed
equalities in (3), and the norm at R proves the last norm. This
supplies every positive witness. It does not claim existence for
the opposite sign when r has a fixed parity.

The negative sign uses ordinary signed intermediate registers. Positivity
of u follows independently from c>Jmain; the gaps u^2-y_aux^2 and
1-y_aux^2 remain negative, as allowed by the certificate convention.

## 5. Applying the kernel to packed fields

Let f>=4 be a fixed integer, and suppose before decoding that

    q>=3, q^(f-1)<=P0<3(q^f-1)/2.

Set D0=q^f and r=P0. Then D0>=81,r>=27,r<3D0/2<2D0, and
D0<r^2. Section3 first gives that q is a power of three and that
D0 divides the central binomial coefficient. Section1 then proves
P0<q^f, its lowest ternary digit is two, and all other digits are
native positive. No prior assumption that D0 is a power of three
has entered the kernel bounds.

Conversely, for a decoded native word with unit two and the chosen
parity, Section4 supplies the full positive kernel. For f=4 the
scale costs two operations q2=q*q,D0=q2*q2; comparing r=P0 is free.
Thus this conditional mask/kernel costs45 operations. For f=6 the
scale costs three operations q2=q*q,q3=q2*q,D0=q3*q3, giving46.
Packing, bounds, input interfaces and any source of parity must be
counted separately. Variable powers are never treated as free.

The finite checks verify both43 primitive variants and all source
residuals, the sharp mask window, actual general-scale bounds,
canonical ratio cases at the smaller thresholds, and small exact
auxiliary constructions of both signs. Small auxiliary examples
are explicitly scoped to that construction, not complete large-index
kernel solutions. No complete universal machine is claimed.
