# Squaring the remaining scale makes both asymmetric compilers accept every input

Deleting the remaining cubed scale from the reviewed
[asymmetric87/88 sources](complete75_asymmetric_scale_tradeoffs.md) gives
**86=47M+39A** with normalized strong norm and **87=46M+41A** with ordinary
strong norm. Both particular shortcuts are refuted. For every fixed
actual modified complete75 compiler and every positive ordinary input x,
each new source has a full positive integer nineteen-coordinate zero.
All eight retained factors equal1.

This is a constructive existence theorem for actual compiler slices.
Its finite recipe does not materialize the gigantic compiler numerals,
packed words or complete Pell witnesses. The sound75 certificate and87
polynomial, their asymmetric87/88 variants, and other candidates are
unchanged. The smaller counts here are costs of incorrect representations,
not new universal bounds.

The argument adapts the established
[squared-scale counterconstruction](complete75_squared_scale_refutation.md)
to the current modified masks, half-binomial index and nineteen-coordinate
source. The new obligations are alignment at R itself, the stronger raw
bound, both current strong treatments, and the positive shared-gamma split.
The [checker](complete75_asymmetric_squared_scale_refutation.py) and
[receipt](complete75_asymmetric_squared_scale_refutation.json) audit the
guarded literal changes and the complete coordinate substitution.

## 1. Exact source and retained factors

The parent computes q=(B−1)J+1, q² and q³, then X=wq and Y=sq³. The new
source deletes only `n2=q²*q` and redirects `sn2=s*n2` to `s*q²`:

    X=wq, Y=sq².                                           (1)

No other row changes. The guard checks the entire selected canonical
asymmetric parent, the exact three scale rows and the sole private consumer
of the deleted row. Every emitted gate is an ancestor of the polynomial.
There remain nineteen positive witnesses, one comparison and eight factors.
The certificate costs85 or86 operations; subtraction of1 gives the86 or87
polynomial. Over the rationals, every surviving register agrees with its
parent under s_old=s_new/q. That map need not be integral at a new zero.

For reference, the supplied coordinates are

    J,F,alpha,zplus,f,h,i,j,o,s,w,tau_gap,eta,zeta,y,Z,delta,rho,sigma.

Use the source definitions

    C=q−F−Z−alpha−2dx, W=C−Z, k=eta+zeta,
    a=Y(X+1), A=a+2, Delta=A²−1, H=4a+3, E=XY,
    c=kY+eta, D=X+ac+(rho+sigma)H,
    u=2dx+b, kappa=u+delta*Delta, mu=W+a*kappa+rho*H,
    R=(q²−Z−qF)(q²−1)+(MC+q(MF+B−1))J,
    V=of−c, Tfirst=XY²k+tau_gap.                         (2)

In order, the factors are

    N0=Tfirst²−XY²(XY²+1)k²,
    N1=D²−Delta*c²,
    N2=mu²−Delta*kappa²,
    N3=Taux²(V²−y²)+y²,
    Nk=k−hE−R,
    Nt=(DC+B*DR+X)C+q−F−zplus(q−1),
    Ns, Nl=V−jc+k−hE.                                  (3)

For the normalized source, Ns=f²−Delta*(ic²)² and
Taux²=Delta²(ic²)². For the ordinary source,
Ns=1+(ic²)²−Delta(f²−1) and Taux²=Delta(f²−1).
The polynomial is the product of these eight factors minus1. No equation,
input factor or linear sign has been discarded.

## 2. Actual modified compiler bounds

Fix the compiler produced by
[the modified complete75 recipe](complete75_half_binomial_compiler.md),
using `new_constants(compile_windows(windows,alphabet))`. Its cached old
MC and MF properties are not the new source constants. Write

    a0=2^b, B=a0^L=2^d, K=m+1, Emax=max(native positions),
    T=popcount(DC).

Here b,L,d are powers of5, K≥16, L>7Emax and Emax≥K−1. Start and End
have native positions0 and1; an ignored low dummy has position e>1.
The modified masks satisfy

    popcount(MC)=d−K, popcount(MF)=K,
    MC=2 mod4, MF=4 mod8.                              (4)

There are at most two copies of K clause coefficients and five unit
monomials in DC. Since each coefficient is below a0, T≤2Kb+5. Hence

    d−K−2(T+2)
      ≥(3K−6)b−K−14≥2K−20>0.                          (5)

This uses L≥7K−6. It holds for the actual compiler, independently of the
language or the input.

Fix any x>0. Choose a power of5

    N>max(25d,2x+1), q=B^N, J=(q−1)/(B−1),
    t=dN, u=2dx+b, W=2^u=a0*B^(2x).                   (6)

Begin with C0=1+W. Add any Boolean subset of the ignored low dummy at
the cells permitted in Section3, and put

    C=1+W+a0^e sum B^i, Z=C−W,
    Cright=BC mod(q−1), F=DC*C+(DR+1)Cright.            (7)

Every selected cell and the End cell have i+1<N. All native digits of
C and Cright are0 or1. The pointwise coefficient argument in
[the bounded projection proof, Section3](complete75_bounded_projection_elimination99.md)
uses only these low-bit bounds: coefficients of F are at most a0/4−1,
and those of2C+F are at most a0/4+1. Support lies below the cell boundary.
It does not require the local computation predicates to hold. Thus

    2C+F<q/3,
    alpha=q−F−Z−C−2dx>q/6>0.                          (8)

For the last inequality use Z<C and2dx<t<q/2. This pays exactly the
current source's stronger alpha bound.

No F-mask condition is imposed. Nevertheless

    popcount(C)≤N+2,
    popcount(F)≤(T+2)(N+2)≤2(T+2)N<(d−K)N.            (9)

The low mask genuinely is satisfied:

    (Z−1) AND(MC*J+1)=0, Z+MC*J<q.                    (10)

All its set bits are native low bits except the excluded End bit; the
origin is removed in Z−1, and the permitted dummy bits remain low bits.
The native MF coefficients are at most a0/2−2, including its new constant
digit4. Together with the F bound this gives F+MF*J−1<q.

Set S=Z−1+qF and Tmask=MC*J+1+q(MF*J−1). Then

    0<S<S+Tmask<q²,
    R=(q²−S)(q²−1)+Tmask.                             (11)

The exact two-block binary population identity and(10) give

    popcount(R)
      =2t+(d−K)N+1+popcount(F+MF*J−1)−popcount(F)
      ≥2t+2.                                         (12)

The strict integer inequality in(9) already leaves at least one bit of
margin; the displayed bound does not assume that the F mask vanishes.
Also Z<C<q/6 and F<q/3 imply

    S<q²/3+q/6<q²−1, hence R>q²>3q+1.                (13)

Equation(11) gives R<q⁴. Every dummy contribution is divisible by4,
so Z=1 mod4 and(4) makes R=3 mod4.

## 3. Align the actual main index

Adding the dummy at cell i changes R by −Gamma*B^i, exactly, where

    Gamma=a0^e(q²−1)[1+q(DC+B*DR+B)].                  (14)

Indeed the changes in C and Z are a0^e B^i, and that in F is
(DC+B*DR+B)a0^e B^i. Internal placement removes cyclic wrap for this
individual contribution. Since b,d,N are powers of5, B=q=2 mod5.
The bracket in(14) is2DC−DR mod5, a unit by the compiler's retained
optional high-monomial correction. Thus Gamma is invertible modulo t=dN.

The proved [Boolean five-adic subset lemma](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md)
supplies distinct cells i=4j,0≤j<N/5, and optionally i=1, with

    sum B^i=(R_initial−d)*Gamma^(-1) mod t.             (15)

Their largest index is4N/5−4, so i+1<N. The dummy is distinct from
the markers even if their cell indices coincide. Equations(14)–(15) yield

    R=d mod t.                                        (16)

This is alignment at the actual half-binomial main index R. The older
construction's2r+1 target is not substituted here. All inequalities and
populations above hold for every Boolean subset and survive this choice.

Now set X=2^R. Since2^t=q=1 mod(q−1), equation(16) gives X=B mod(q−1).
Moreover X>B by(13). With

    kr=(BC−Cright)/(q−1)≥0,
    z=(DR+1)kr+[(X−B)/(q−1)]C>0, zplus=z+1,            (17)

we have (DC+B*DR+X)C=F+z(q−1). This is the actual temporal multiplier
of the source; it has not been replaced by a freely chosen rotation.
Equation(17) makes Nt=1.

## 4. The half-binomial and strong positive coordinates

Put r=(R−1)/2 and

    M=binom(2r,r)+sum_(j=1..r) binom(2r,r+j) X^j,
    Y=M/2.                                           (18)

The exact central-binomial valuation is

    v2(Y)=popcount(r)−1=popcount(R)−2≥2t.               (19)

Every other term in M is divisible by X=2^R, which has larger valuation
than its central term. Therefore s=Y/q² and w=X/q are strictly positive
integers, as required by(1). The canonical formulas and estimates in
[the half-binomial converse, Section6](pell_kernel_half_binomial42.md)
apply at this fresh X,Y. The old q³ divisor is used there to establish
scale integrality; here(19) supplies the needed q² integrality. The actual
bound Y≥X^r/2 establishes its growth and ratio estimates independently
of this smaller divisor.

Using chi_A and psi_A for the Pell sequences, set

    a=Y(X+1), A=a+2, Delta=A²−1, H=4a+3, E=XY,
    P=2XY²+1, n=(R+1)/2,
    c=psi_A(R), D=chi_A(R),
    k=2psi_P(n), Tfirst=chi_P(n),
    eta=c−kY, zeta=k(Y+1)−c,
    h=(k−R−1)/E,
    tau_gap=Tfirst−XY²k=psi_P(n)−psi_P(n−1).            (20)

The canonical strict ratio Y<c/k<Y+1 proves eta,zeta>0. The recurrence
modulo E gives k=2n mod E; strict Pell growth gives h>0. The final
identity follows from P−1=2XY² and proves tau_gap>0. The first two
factors N0,N1 equal1. Set gamma=(D−ac−X)/H. The projection recurrence
gives its integrality, and D−ac=2c−psi_A(R−1)>c>X gives positivity.

For the five auxiliary coordinates use the canonical multiple

    m=2cR, f=chi_A(m), t_aux=psi_A(m),
    Taux=Delta*t_aux,
    y=psi_Taux(R), V=chi_Taux(R)/Taux,
    o=(V+c)/f, j=(V+R)/c.                              (21)

The Pell composition identity gives
psi_A(m)=c*psi_(chi_A(R))(2c). Modulo c the latter factor is
2c*chi_A(R)^(2c−1)=0, so c² divides t_aux. Use

    i=t_aux/c² for the normalized source,
    i=Delta*t_aux/c² for the ordinary source.          (22)

Both choices are positive integers. The exact norm gives
f²−1=Delta*t_aux² and Taux²=Delta(f²−1), so Ns=1 in both sources.
Since R is odd, Taux divides chi_Taux(R). The canonical quotient
congruences give

    V=(-1)^((R−1)/2)c=−c mod f,
    V=(-1)^((R−1)/2)R=−R mod c.                        (23)

One may obtain the first by reducing the odd-chi quotient polynomial
at Taux²=1−A² mod f; the second follows at Taux²=0 mod c.
R=3 mod4 fixes both signs. Thus o,j are positive integers. The Taux
Pell norm gives N3=1, while V−jc=−R and k−hE=R+1 give Nl=1 and Nk=1.
This checks the ordinary strong treatment as well as the normalized one;
no positive inverse between their arbitrary witness tuples is asserted.

## 5. Original input bridge and the shared gamma

The supplied ordinary input remains x. Equation(6) gives odd u=2dx+b≥3,
and N>2x+1 gives u<t<R. Put

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa−u)/Delta,
    rho=(mu−a*kappa−2^u)/H.                            (24)

For odd u, psi_A(u)=u mod Delta; strict growth makes delta>0. The
sequence z_j=chi_A(j)−a*psi_A(j) starts1,2 and satisfies the Pell
recurrence. Modulo H its values are2^j. For A≥3 its growth gives
z_u>2^u, hence rho is a positive integer. Equation(24), W=2^u and(2)
make the retained input norm N2=1 with the positive root mu.

It remains to pay the source's shared-gamma condition, rather than use
independent input and main projection coordinates. For j≥2, exactly

    z_j−z_(j−1)−psi_A(j)=(2A−3)psi_A(j−1)>0.           (25)

Since u<R, already the last increment proves z_R−z_u>c>X. Consequently

    H(gamma−rho)=z_R−z_u−X+2^u>0.                     (26)

Set sigma=gamma−rho. Both rho and sigma are positive integers, and their
sum recovers the required main gamma. All nineteen supplied coordinates
have now been constructed as positive integers. Equations(17),(20)–(24)
make every factor in(3) equal1, so the literal complete polynomial is zero.

Nothing in Sections2–5 assumes that x belongs to the compiled language.
They apply to every actual modified compiler and every x>0. In particular,
use the explicit stationary rejecting machine and exact fixed compiler
recipe in [the rejecting-slice packet, Sections1–3](complete75_weakened86_rejecting_compiler.md).
Its first transition enters a nonhalting stationary loop, so its language
is empty. Only that machine invariant and compiler recipe are reused here,
not the different weakened86 collapse theorem. This gives an actual
false-input slice, for example x=1, for each source in this packet.

## 6. Literal audit and evidence limits

`rewrite` supports only the two complete canonical asymmetric sources.
`mapped_values` supplies all nineteen coordinates from formal first/main/
input/auxiliary root placeholders using exact rational or symbolic division.
The checker executes the actual complete source and independently compares
all eight factors in(3), the reconstructed C,W,kappa,mu, and the full
product minus1. Its ordinary-strong reduction includes the actual residual
correction; it does not assume that the off-zero ordinary auxiliary factor
equals the normalized one.

The default audit also checks every source gate and count, the rational
parent replay, malformed callers, actual sparse modified layouts and the
correct exporter, the exact dummy-change identity and finite constructive
five-adic targets, binary population identities, and separate exact Pell
components including the positive shared-gamma split. These finite checks
corroborate the general proof; they are not numerical full compiled zeros.

One saved scalar-mask illustration has B=16,N=5,q=1048576,x=1,
MC=6,MF=12,DC=3,DR=5 and

    R=1122038196262802486093415,
    popcount(R)=56, v2(Y)=54.

Here q² divides the canonical Y but q³ does not. It demonstrates why the
parent inverse need not be integral. These scalar constants are explicitly
not an actual compiled program, and its enormous Pell integers are not
materialized. Actual-compiler false positives follow from the full proof
above, including the independent rejecting-machine invariant.

Author writer91086 and fresh replay47283 passed on the same source and
receipt. The exact audit includes256 whole-register parent identities
(128 signed), four symbolic nineteen-coordinate/eight-factor/output maps,
256 rational full-factor/output maps(128 signed),14 malformed callers,
four actual sparse modified layouts,192 constructive five-adic targets,
429 shifted-population identities, five main-index margin cases, five
first/main ratio components, six normalized/ordinary auxiliary blocks and
100 positive input/shared-gamma components. All nine local links resolve.
Native's independent full proof/source/dependency review and fresh66596
passed with no findings. Its separate literal executor checked192 complete
rational parent/register maps(96 signed),192 manual nineteen-coordinate/
eight-factor/whole-output maps(96 signed), and both full opcode, closure
and liveness audits. Its earlier separate construction audit checked six
new actual sparse layouts,300 independently constructed five-adic targets,
437 shifted-population identities, six small normalized/ordinary auxiliary
blocks and100 shared-gamma components. The review included actual modified
mask/export scope, R=d mod t, alpha and R>q² margins, half-binomial
integrality, every positive coordinate and the rejecting-machine corollary.
All nine local links and whitespace checks passed. No finite fixture was
treated as a materialized complete compiled Pell zero.
