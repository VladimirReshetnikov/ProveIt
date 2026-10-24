# Twelve unrestricted integers by a monotone intersective carrier

This note specifies an ordinary integer polynomial and proves the new
arithmetic reduction. Its native/compiler and syntactic ZFC calibration are
the explicitly inherited ordinary results of the pinned source-34/source-71
family. It neither proves Con(ZFC) nor claims a new kernel-checked endpoint.

## 1. Literal variables and fixed constants

The twelve independent integer coordinates are

    j, C, z, h, r, v, w, T, c, n, t, s.

Use the exact six constants of the source-13 root-fusion package:
beta, K0, MC, MF, cone_A, cone_B, where beta=2^1064921-1, MF is already
shifted, cone_A=2^1113, and cone_B=2^666104. No new huge numeral is used.

Define, by ordinary polynomial abbreviations,

    J=6j+1, q=beta J+1, W0=12w+4,
    X=q W0, Y=(2v+1)q^3, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W0)C-z(q-1), alpha=q-F-C,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    P=G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg=(3P-4)s^2+1,
    I=s r c^2,
    Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4 I T)-c,
    Cy=Q V^2-1, Da=delta Cy,
    Dt=1+XY^2(XY^2+1)k^2,
    Dm=1+Delta c^2, b0=X+ac.

The multiplier I is allowed to be even. Its nonvanishing is proved from
the final equation, before any strong-rank theorem is invoked.

Set u=HT-b0 and define the two integer polynomials

    A=u^5+10u^3 Dm+5u Dm^2
       +32H^2(u^3+3u Dm)+H^3(u^2+Dm)+31H^4 u+31H^5,
    B=5u^4+10u^2 Dm+Dm^2
       +32H^2(3u^2+Dm)+2H^3 u+31H^4.

Thus, in the quadratic algebra d^2=Dm,

    A+B d = ((u+d)^2+31H^2)((u+d)^3+H^2(u+d)+H^3).

Finally put

    S=I H^5,
    ell=XY^2,
    b_bound=1+c^2+R+c^2(s^2+r^2)(T^2+1),
    K=T^2+c^2+1,
    ba=Q(Df b_bound+c^2+1),
    bf=Delta+I^2+3,
    bt=2+ell^2+k^2,
    w1=512 K^2+1,
    w2=w1(2ba+1),
    w3=w2(2bf+1),
    w4=w3(2bt+1),
    Z=S n-A,
    A0=B^2 Dm,
    A1=S^2 w1^2 Da,
    A2=S^2 w2^2 Df,
    A3=S^2 w3^2 Dt,
    A4=S^2 w4^2 Dg.

For the fixed universal five-root polynomial

    F32(Z;A0,...,A4)=product_{epsilon in {-1,1}^5}
                        (Z-sum_i epsilon_i sqrt(Ai)),

the equation is

    F32(Z;A0,A1,A2,A3,A4)=0.

The formal product is an ordinary polynomial over Z: each sign change
permutes the factors, eliminating every odd radical power. A literal
division-free circuit is supplied by build_twelve.py. No root, division,
variable exponent, implicit witness, or uninstantiated coefficient remains.

## 2. The monotone intersective quintic

Let

    pi(x)=(x^2+31)(x^3+x+1)=x^5+32x^3+x^2+31x+31.

It has three simultaneous properties.

1. For every nonzero integer m, there is a with m|pi(a).
2. It has no zero in any real field extension of Q of degree at most two.
3. Its derivative is strictly positive on R.

For (1), the cubic discriminant is -31. For any odd prime p!=31, either
the cubic has a root in F_p, or it is irreducible. In the irreducible case
Frobenius permutes its three roots as a 3-cycle. The Vandermonde product
of their differences is fixed by that even permutation, hence belongs
to F_p, and its square is -31. Thus the quadratic factor has a root.
All selected roots are simple. At p=31 the cubic has the simple root 3
(the derivative is 28 mod31). At p=2, -31=1 mod8 is a square in Z_2.
Simple-root Hensel lifting for odd p and the elementary odd-square
lifting for p=2 give roots modulo every prime power. Finite CRT finishes.

For (2), the quadratic has no real zero. The cubic has no rational root
by the rational-root test (neither +1 nor -1 is a root), so it is
irreducible. A degree-three element cannot belong to a field extension
of degree one or two.

For (3),

    pi'(x)=5x^4+96x^2+2x+31>0,

because the discriminant of 96x^2+2x+31 is negative and its leading
coefficient is positive.

For nonzero integer H, the homogeneous quintic

    Phi_H(x)=H^5 pi(x/H)

is also strictly increasing: its derivative is H^4 pi'(x/H)>0. Since
Dm>0 below, putting d=sqrt(Dm)>0 gives

    B=(Phi_H(u+d)-Phi_H(u-d))/(2d)>0.

An exact algebraic positivity certificate is

    B=5u^4+10u^2 Dm+Dm^2+32H^2 Dm
      +95H^2 u^2+H^2(u+H)^2+30H^4>0.

Moreover A+B d and A-B d are both nonzero, by property (2). Consequently
A^2-B^2 Dm is nonzero. This conclusion does not assume Dm is a square.

The earlier repo quintic (x^2+23)(x^3-x-1) is not globally monotone. The
31-quintic is chosen specifically for its positive odd coefficient after
quadratic reduction and its zero-free property in real quadratic fields.
No historical-priority claim for the quintic itself is made.

## 3. Unconditional realness and nonzero bootstrap

For every integer input, J=6j+1 is odd and nonzero, so q is even and
|q|>=beta-1>=16. W0=4(3w+1) is nonzero, hence |X|>=64.
The odd multiplier in Y gives |Y|>=4096. Therefore
|a|>=63*4096, H is nonzero, and Delta=(a+2)^2-1>1.
In particular Dm>=1 and Df>=1. Writing ell=XY^2, the integer inequality
ell(ell+1)>=0 gives Dt>=1.

Q=(Delta I)^2 cannot equal one: if I=0 it is zero, and otherwise it is
at least Delta^2>1. Thus delta is always nonzero. If I=0, then Da=1.
If I!=0, the definition I=s r c^2 forces c!=0 and |I|>=c^2. Hence
Df=1+Delta I^2>|c|+1. With b=c-R+4IT, either b=0 and |V|=|c|>=1,
or b!=0 and |V|>=Df-|c|>1. Thus Cy>0 and Da=delta Cy>0.
All four radicands Dm,Df,Dt,Da are therefore positive on every integer
assignment. Each weight wi is a product of odd integers, so is nonzero
on every assignment. Positivity of ba will be proved only after
recovering the guards; unconditional nonvanishing is enough for the
bootstrap.

Suppose the final norm polynomial is zero. If S=0, all radicands except
A0 vanish and the norm specializes exactly to

    (A^2-B^2 Dm)^16,

which is nonzero by Section2. Therefore S!=0. Since H!=0, this proves
I!=0 and consequently s!=0, r!=0, and c!=0.

One conjugate linear factor vanishes over C. If Dg<0, its term is the
only nonzero imaginary term: the other four radicands and center are
real, and its coefficient S w4 is nonzero. This is impossible.
Thus Dg>=0. Because s is a nonzero integer, P<=0 would imply
Dg=(3P-4)s^2+1<=-3. Hence P>0. The joint-positivity lemma then gives
G>0 and eta*zeta>0. This is the essential order: S!=0, realness, guards,
and only then square-root extraction and native decoding.

## 4. Homogeneous bounds, product weights, and integrality

First G>0 already implies R>0; no Pell square extraction is needed for
this fact. Put U=cone_A F and Vc=cone_B C. The determinant inequality
UVc>(q-U-Vc)^2 implies U,Vc,q have a common nonzero sign and
|U|+|Vc|<2|q|. Since both cone coefficients are at least two, F,C and
alpha=q-F-C have that same sign. The fixed constants satisfy
0<MC<beta<MF. If q=Q0>0, then J>0 and

    q(q-F)-C=Q0 alpha+(Q0-1)C>0.

If q=-Q0<0, write F=-F0,C=-C0,alpha=-alpha0 with all three positive.
Then

    q(q-F)-C=Q0(C0+alpha0)+C0>0,
    J<0, MC-Q0 MF<0.

Both summands defining R are positive in either sign case. Thus R>0.

The coefficient in V is b=c-R+4IT. Because I=s r c^2 and R>0,

    |b| <= c^2+R+c^2(s^2+r^2)(T^2+1) < b_bound,
    |V| <= Df b_bound+c^2+1.

Here 4|srT|<=(s^2+r^2)(T^2+1). The following three bounds are immediate
from 2|xy|<=x^2+y^2 and the displayed definitions:

    sqrt(Dt) <= ell^2+k^2+2 = bt,
    sqrt(Df) <= Delta+I^2+3 = bf,
    sqrt(Da) < Q|V| <= Q(Df b_bound+c^2+1) = ba.

For the auxiliary inequality use Q>1 and
Da=(Q-1)(QV^2-1)<Q^2 V^2. These bounds are strictly positive.

The first radical admits a much smaller bound after division by S.
Put x0=u/H and z0=sqrt(Dm)/|H|. The unconditional estimates in Section3
give |a|>3 and |X|<|H|. Consequently

    |a/H|<1/3,
    |b0/H|<1+|c|/3,
    x0^2<=3(T^2+c^2+1)=3K.

Also H^2/4-Delta=3a^2+2a-3/4>1. Since c is nonzero,

    z0<|c|/2, z0^2<=K.

The exact expression for the quintic's odd coefficient gives

    B/H^4=5x0^4+10x0^2 z0^2+z0^4
          +96x0^2+32z0^2+2x0+31
        <=76K^2+323K+32<=431K^2.

For the linear term use 2|x0|<=x0^2+1. Finally |I|>=c^2 and K>=1,
so

    (B/|S|)sqrt(Dm)=(B/H^4)z0/|I|
       < (431/2)K^2 <256K^2.

This bound uses the actual homogeneous scaling of the main radical.

Divide a vanishing conjugate factor by S. The five radical magnitudes
occur in this order,

    (B/|S|)sqrt(Dm), w1 sqrt(Da), w2 sqrt(Df),
    w3 sqrt(Dt), w4 sqrt(Dg).

The first magnitude is less than w1/2. Adding w1 sqrt(Da) gives a sum
less than w1(ba+1/2)=w2/2; adding w2 sqrt(Df) gives a sum less than
w3/2; adding w3 sqrt(Dt) gives a sum less than w4/2. Each nonzero
later radical has unweighted magnitude at least one, because its
radicand is a nonnegative integer. Delete the Dg term if it is zero.
The remaining list is strictly superincreasing. In a rational linear
combination of square roots of positive rational numbers, contributions
from each nontrivial square class must sum to zero. Such a nonempty
class cannot cancel because its largest magnitude exceeds the sum of
all its smaller magnitudes. Consequently all five roots are rational.

Each of Dm,Df,Dt,Dg,Da is an integer, so its rational square root is an
integer. Denote signed roots by d,f,tau,g,ytilde. The auxiliary root
y=ytilde/delta is initially rational, and satisfies

    Q V^2-(Q-1)y^2=1.

The adjacent-coefficient Pell descent makes y integral. For completeness:
write |y|=u/b in lowest terms. The equation gives b^2|(Q-1). For V>1
and y>0 replace

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first coordinate is integral; the reduced denominator of y' stays
b because 2Q-1=1 modb. The norm is preserved. The inequalities
y>V and (Q-1)y<QV give -V<V'<V, and the norm excludes V'=0.
Descent reaches |V|=1, where |y|=1, without changing b. Thus b=1.

The signed root d in the vanishing factor satisfies

    S n=A+B d+S(w1 ytilde+w2 f+w3 tau+w4 g),

after absorbing signs into the integer roots. Therefore

    I H^5 | A+B d = Phi_H(d-b0+HT).

In particular H^5 divides the homogeneous quintic. Its monicity forces
H|(d-b0). Indeed, if p^e||H and v_p(d-b0+HT)=b<e, its leading fifth
power has valuation 5b and every remaining term has larger valuation;
the result cannot be divisible by p^(5e). Set gamma=(d-b0)/H in Z.

## 5. Restoration to the generalized signed strong kernel

At a zero, set rho=Delta I=Delta s r c^2. Then rho is nonzero and

    rho^2=Delta(f^2-1),
    rho^2 V^2-(rho^2-1)y^2=1,
    d=X+ac+gamma H,
    d^2-Delta c^2=1,
    tau^2-XY^2(XY^2+1)k^2=1.

Also

    V=f o-c, o=f(c-R+4IT),
    V=c j_aux-R,
    j_aux=Delta s^2 r^2 c^3(c-R)+4 s r c Df T.

The last identity follows by expanding V+R:

    V+R=Delta I^2(c-R)+4 I Df T.

The transport and index equations are built into F,k. The two strict
guards are G>0 and eta*zeta>0. G restores the common signs of F,alpha,C.
The signed-rank and delayed orientation proof of the inherited source
applies with an arbitrary nonzero multiplier rho/c^2, not just an odd
one. Here its strong-rank divisibility has an especially direct proof.
Put B0=|a+2|. The main and normalized Pell identities classify
|c|=psi_B0(p), |I|=psi_B0(m), and |f|=chi_B0(m). Since c^2 divides I,
strong divisibility of this Lucas sequence gives p|m. Write m=p k0.
The multiplication formula gives

    psi_B0(p k0)/psi_B0(p)=k0 chi_B0(p)^(k0-1) modulo |c|.

The left side is divisible by |c| and chi_B0(p) is coprime to |c|.
Therefore |c| divides k0; in particular p|m and |c||m, exactly the
strong-rank inputs used by the inherited auxiliary step-down proof.
The odd auxiliary index follows from
chi_|rho|(2m)=(-1)^m modulo |rho|, valid for every |rho|>1.

One must not claim an immediate literal restoration
r_old=(Delta s r-1)/2, which need not be integral. Instead use the
generalized signed-kernel theorem with nonzero multiplier and the same
unbounded proof: first/main Pell classification gives ranks p>n>=24,
the preceding normalized argument gives m divisible by p and |c|,
the signed auxiliary step-down gives p=R, the first-rank congruence gives
R=2n-1, and the main-root residue yields X=sign(c)*2^R. The fixed
X=2 mod3 then gives X=2^R>0. The established signed-Y and native decoding
complete the reduction to a finite refutation. The separate independent
audit has checked that no odd-multiplier use occurs in this proof.

This is an ordinary arithmetic generalization of the source theorem;
the old literal Q41 coordinate chart is not being claimed for even rho/c^2.

## 6. Full interpolation of the new auxiliary coordinate

Here is the central new completeness lemma. Let A0>1 be even, let
Delta=A0^2-1, let R=3 mod4, and c=psi_A0(R)>0. Assume c=R mod4.
For every prescribed positive N there exist positive integers n0,I,f
such that

    I=psi_A0(n0), f=chi_A0(n0), 4N c^2|I,

and, for this same fixed I,f, EVERY residue class modulo I contains an
integer T for which

    V=f^2(c-R+4IT)-c,
    (Delta I)^2 V^2-((Delta I)^2-1)y^2=1

has an integer y. Thus the strong witness is fixed before the requested
class is chosen.

### Choosing the strong witness

The determinant-one Pell recurrence matrix is invertible modulo 4N c^2.
Its finite order supplies a positive index with psi_A0(index)=0 modulo
that modulus. Take a positive even multiple, also a multiple of R if
desired. Then I is divisible by 4N c^2 and f^2-Delta I^2=1.
In particular I is even, f is odd, and gcd(f,I)=1.

### Valuation fact and the correct squared-modulus period

For each prime p dividing I=psi_A0(n0),

    v_p(I)>=v_p(n0).

For odd p this is the standard Lucas lifting formula. It also has an
elementary proof: take the first zero index rho_p modulo p. If p divides
Delta, the recurrence gives rho_p=p and v_p(psi_A0(p))>=1. Otherwise
rho_p divides p-1 or p+1, so p does not divide rho_p. Binomial expansion
of a norm-one unit whose second coordinate is divisible by p gives
v_p(psi_A0(k rho_p))=v_p(psi_A0(rho_p))+v_p(k).
These cases give the inequality. At p=2 and even A0, odd-index psi is
odd, and for even n0 the doubling formula gives exactly

    v_2(psi_A0(n0))=v_2(n0)+v_2(A0).

Let alpha=A0+sqrt(Delta). Since alpha^n0=f+I sqrt(Delta),

    alpha^(4n0)=1-4f alpha^n0 modulo f^2.

Raising this congruence to the positive power f gives

    alpha^(4n0 f)=1 modulo f^2.

Thus lambda=4n0 f is a period for the Pell coordinates modulo f^2.
Using only 4n0 would be incorrect. Because gcd(f,I)=1 and the valuation
inequality holds, we have

    gcd(lambda,4I^2) divides 4I.

### Interpolating an arbitrary class

Fix any integer a specifying T=a modulo I. The two congruences

    L0=R modulo lambda,
    L0=R-4Ia modulo 4I^2

are compatible by the preceding gcd result. Choose a positive solution.
It is 3 modulo4. Put S0=Delta I and

    V0=chi_S0(L0)/S0, y=psi_S0(L0).

For odd L0, chi_S0(L0)/S0 is an integer polynomial in S0^2.
The exact Chebyshev identities give

    V0=-psi_A0(L0)=-c modulo f^2,
    V0=-L0 modulo 4S0^2.

The second modulus really includes the factor4. To verify it, the
polynomials Q_m(X)=chi_s(2m+1)/s, X=s^2, satisfy

    Q_0=1, Q_1=4X-3,
    Q_(m+1)=(4X-2)Q_m-Q_(m-1),

and hence Q_m(X)=(-1)^m(2m+1) modulo4X by induction.
Since 4I^2 divides 4S0^2, V0=-R+4Ia modulo4I^2.
Furthermore c-R is divisible by4 and f^2=1+Delta I^2, so

    f^2(c-R)=c-R modulo4I^2.

It follows that the numerator

    N0=V0+c-f^2(c-R)

is divisible by f^2 and is 4Ia modulo4I^2. Since
gcd(f^2,4I^2)=1, it is divisible by 4If^2, and

    T=N0/(4If^2)=a modulo I.

In the last congruence one uses f^2=1 modulo I after dividing N0 by
4I. The Pell identity gives the required auxiliary norm, and rearrangement
gives V0=f^2(c-R+4IT)-c. This proves full residue interpolation.

## 7. Completeness from a canonical native witness

The inherited canonical family supplies the seven outer coordinates
j,C,z,h,v,w,c and the required native data (with its displayed source
restrictions). In particular A0=a+2 is even, R=3 mod4,
c=psi_A0(R), d=chi_A0(R), and gamma=(d-b0)/H is an integer.
The guards G>0 and eta*zeta>0 hold. Choose t by the joint-positivity
lemma so P>0.

For P=1 choose s=1,g=0. For P>=2, the positive number 3P-4 is 2 mod3,
so it is nonsquare. Ordinary Pell existence supplies positive s,g with

    g^2-(3P-4)s^2=1.

Use the interpolation lemma with N=s to obtain I,f with 4s c^2|I.
Set r=I/(s c^2). This gives exactly the defining strong I=s r c^2.
The congruence c=R mod4 needed in the lemma follows from the native
A0=2 mod4: psi_A0(m+2)=-psi_A0(m) mod4 and R is odd.

Choose an intersective root a modulo I for pi(a+gamma). The lemma
provides T=a modulo I and an auxiliary norm root y, with I,f already
fixed. Thus I divides pi(T+gamma). With ytilde=delta y, all five
radicands Dm,Da,Dg,Dt,Df are integer squares. Moreover

    A+B d=H^5 pi(T+gamma)

is divisible by S=IH^5. Finally choose

    n=(A+B d)/S+w1 ytilde+w2 f+w3 tau+w4 g.

The weights depend on all previously selected data and not on n. This
is an integer, and one of the conjugate factors vanishes. Witness
selection is noncircular: native data, then t, then s, then I/f/r,
then an intersective residue and T/y, then the weights and n.

## 8. Degree and exact leading coefficient

The degrees are

    a:6, Delta:12, R:5, P:44, I:4, Df:20, Q:32,
    V:25, Da:114, Dt:34, Dm:14, Dg:46,
    u:7, A:35, B:28, S:34, b_bound:6,
    K:2, ba:58, bf:12, bt:20,
    w1:4, w2:62, w3:74, w4:94, Z:35.

The five radicand degrees are 70,190,212,250,302. The last is uniquely
largest, so the degree of the norm is exactly 16*302=4832 if its leading
form is nonzero. Write q0=6beta j, W00=12w,

    a0=2q0^4 W00 v=2^7 3^5 beta^4 j^4 w v,
    I0=s r c^2, Y0=2v q0^3.

The leading forms of Dg and the last radicand are

    Dg_top=-3s^2 Y0^4 h^4 a0^4,
    A4_top=-3*2^44 (T^2+c^2)^4 a0^34 I0^10
           *c^4(s^2+r^2)^2 T^4 s^2 Y0^8 h^4.

The degree-4832 homogeneous part of the final polynomial is A4_top^16.

The coefficient of

    j^2560 w^544 v^672 h^64 s^256 r^160 c^384 T^192

is exactly

    2^5024 3^3120 beta^2560 > 0.

The exponents sum to 4832. Choosing T^128 from (T^2+c^2)^64 and s^64
from (s^2+r^2)^32 both have coefficient one. No relation among the
other fixed coefficient ports can affect this certificate. The literal
circuit has 248 live operations: 64 additions, 153 multiplications,
31 subtractions.

### Compact companion of degree16000

The same construction and proof also work with the shorter bound

    L_compact=1+B^2 Dm+Dt+Df+Da+Dg^2, W=2L_compact+1,
    A0=B^2 Dm, A1=S^2 W^2 Da, A2=S^2 W^4 Dg,
    A3=S^2 W^6 Dt, A4=S^2 W^8 Df.

It is positive unconditionally and bounds the same five magnitudes.
It needs no R-positivity argument for separation. In this ordering the
weighted roots are B sqrt(Dm)/|S|, W sqrt(Da), W^2 sqrt(Dg),
W^3 sqrt(Dt), W^4 sqrt(Df). Each earlier sum is less than W^j/2,
which gives the identical separation proof. Its degree is 114;
the five radicand degrees become 70,410,570,786,1000, with degree16000
for the norm. Put

    R0=-q0^3(W00 C-q0 z), b=4I0 T-R0.

Its leading form is 2^448 a0^1728 I0^1088 b^256. The coefficient of
j^6912 w^1728 v^1728 s^1344 r^1344 c^2688 T^256 is exactly
2^13056 3^8640 beta^6912>0. This companion has 223 live operations:
53 additions, 139 multiplications, 31 subtractions. Both circuits factor
Dt as 1+Ltau(Ltau+k), Ltau=XY^2 k.

## 9. Boundary of the result

The principal polynomial has twelve unrestricted integer variables and
exact degree4832. Its compact companion has the same variables and
degree16000. Both use the same six explicit fixed integer payloads as the
incoming thirteen-integer construction. It is not the fewest-variable
known consistency equation: the repository has ten-integer forms of
much higher degree. The construction offers a new intermediate tradeoff
and a reusable native full-residue interpolation theorem.

The new mathematical equivalence, the inherited ordinary consistency
calibration, the finite circuit/coefficient checks, and the uncompleted
proof-assistant/object-ZFC obligations must be reported separately.
