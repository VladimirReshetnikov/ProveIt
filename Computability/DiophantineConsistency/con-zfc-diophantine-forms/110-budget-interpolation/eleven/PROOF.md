# Eleven unrestricted integers by a centered budget, intersective interpolation, and parity

This note combines the prior centered-budget theorem with the late monotone-intersective construction, and uses an early squareclass projection followed by odd-radicand separation with four fixed powers of two. The interpolation and quintic arguments in Sections 2 and 6 are retained from the credited late precursor, not claimed as new here. All proof dependencies are copied and authenticated locally.

This note specifies an ordinary integer polynomial and proves the new
arithmetic reduction. Its native/compiler and syntactic ZFC calibration are
the explicitly inherited ordinary results of the pinned source-34/source-71
family. It neither proves Con(ZFC) nor claims a new kernel-checked endpoint.

## 1. Literal variables and fixed constants

The eleven independent integer coordinates are

    j, C, z, h, r, v, w, T, c, n, s.

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
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    Dg=4(3Budget-4)s^2+1,
    I=2 s r c^2,
    Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4 I T)-c,
    Cy=Q V^2-1, Da=delta Cy,
    Dt=1+XY^2(XY^2+1)k^2,
    Dm=1+Delta c^2, b0=X+ac.

The multiplier I is even by definition. Its nonvanishing is proved from
the final equation, before any strong-rank theorem is invoked.

Set u=HT-b0 and define the two integer polynomials

    A=u^5+10u^3 Dm+5u Dm^2
       +32H^2(u^3+3u Dm)+H^3(u^2+Dm)+31H^4 u+31H^5,
    B=5u^4+10u^2 Dm+Dm^2
       +32H^2(3u^2+Dm)+2H^3 u+31H^4.

Thus, in the quadratic algebra d^2=Dm,

    A+B d = ((u+d)^2+31H^2)((u+d)^3+H^2(u+d)+H^3).

Finally put

    S=I H^5,       Ltau=XY^2 k,
    CenterShift=(2Q-1)V+4Ltau,
    Z=S(n+CenterShift)-A,
    A0=B^2 Dm,
    A1=4 S^2 Da,
    A2=S^2 Df,
    A3=16 S^2 Dt,
    A4=64 S^2 Dg.

The direct companion has CenterShift=0; the auxiliary-only companion has
CenterShift=(2Q-1)V. These shifts are integer-polynomial bijections in n.
The primary version is the displayed double-centered one. The four
non-main roots have coefficients 2,1,4,8 respectively after division by S;
in the order strong,auxiliary,first,guard their 2-adic valuations are 0,1,2,3.

For the fixed universal five-root polynomial

    F32(Z;A0,...,A4)=product_{epsilon in {-1,1}^5}
                        (Z-sum_i epsilon_i sqrt(Ai)),

the equation is

    F32(Z;A0,A1,A2,A3,A4)=0.

The formal product is an ordinary polynomial over Z: each sign change
permutes the factors, eliminating every odd radical power. A literal
division-free circuit is supplied by build.py. No root, division,
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
If I!=0, the definition I=2s r c^2 forces c!=0 and |I|>=c^2. Hence
Df=1+Delta I^2>|c|+1. With b=c-R+4IT, either b=0 and |V|=|c|>=1,
or b!=0 and |V|>=Df-|c|>1. Thus Cy>0 and Da=delta Cy>0.
All four radicands Dm,Df,Dt,Da are therefore positive on every integer
assignment. The four fixed coefficients 2,1,4,8 are nonzero on every assignment;
no variable separating weight or bound is required.

Suppose the final norm polynomial is zero. If S=0, all radicands except
A0 vanish and the norm specializes exactly to

    (A^2-B^2 Dm)^16,

which is nonzero by Section2. Therefore S!=0. Since H!=0, this proves
I!=0 and consequently s!=0, r!=0, and c!=0.

One conjugate linear factor vanishes over C. If Dg<0, its term is the
only nonzero imaginary term: the other four radicands and center are
real, and its coefficient 8S is nonzero. This is impossible.
Thus Dg>=0. Because s is a nonzero integer, Budget<=1 would imply
Dg=4(3Budget-4)s^2+1<=-3. Hence Budget>=2. In particular k!=0,
Derr<q^2, and |eta/k|<1/2. Writing U=cone_A F and Vc=cone_B C,
the disk inequality gives 0<U/q<2 and 0<Vc/q<2 for either sign of q.
Since cone_A,cone_B>=8,

    0<F/q+C/q<2/cone_A+2/cone_B<=1/2<1.

Therefore F,C,alpha all have q's nonzero sign. With Z0=|Y| and K=|k|,

    K(Z0-1/2)<|c|<K(Z0+1/2),
    sign(c)=sign(kY).

We have not yet proved eta>0 or k-eta>0. The essential order is
S!=0, realness, centered budget and common signs, then root extraction
and signed rank recovery. No old determinant inequality is inferred.

## 4. Early main-root projection and fixed parity separation

### 4.1 Integer projection forces the main root

Every radicand is now nonnegative. Write d=sqrt(Dm), and let the
remaining roots be sqrt(Da),sqrt(Df),sqrt(Dt),sqrt(Dg), with independent
signs in a vanishing factor. All radicands are integers. Projection of
this factor onto the rational squareclass keeps precisely the rational
radicals; every such radical is an integer. Irrational squareclass
contributions cancel separately by linear independence of distinct
squarefree radicals.

The factor has the form

    S(n+CenterShift)=A+ed B d+S(2ea sqrt(Da)+ef sqrt(Df)
                                       +4et sqrt(Dt)+8eg sqrt(Dg)).

If d were irrational, projection would give S|A, hence H|A. This is
impossible already modulo 3. Indeed q=2, W0=1, X=2 modulo 3, so

    a=H=Delta=0 modulo 3,
    b0=2, u=HT-b0=1, Dm=1 modulo 3.

The displayed expression for A therefore gives

    A=u^5+10u^3 Dm+5u Dm^2=1+1+2=1 modulo 3.

Since H=0 modulo 3, H cannot divide A. Thus d is rational and integral.
Let d_s=ed d be the signed main root in the factor. Project again to
obtain S|A+B d_s. Therefore

    I H^5 | A+B d_s = Phi_H(d_s-b0+HT).

Monicity of Phi_H forces H|(d_s-b0). For each prime p with p^e||H,
if the argument had valuation b<e then its leading fifth power would
have valuation 5b and every other homogeneous term would have strictly
larger valuation, contradicting divisibility by p^(5e). Thus

    gamma=(d_s-b0)/H in Z.

This recovers the signed main root and its congruence before separating
the other four radicals. It does not assert those radicals are rational
merely because their sum is rational.

### 4.2 Four odd radicands and distinct 2-adic valuations

All four remaining radicands are positive odd integers. Indeed I is
even, Delta is odd, and therefore

    Df=1 modulo 4,       Q=0 modulo 4,
    delta=Cy=-1 modulo 4,       Da=1 modulo 4.

Also X is a multiple of 8, so Dt=1 modulo 8; Dg=1 modulo 4. Since
Dg>=0 is odd, Dg is strictly positive. Df,Dt,Da were already positive.

Subtract the integral main-root contribution from the factor and divide
by S. The signed sum

    f + 2 ytilde + 4 tau + 8 g

is rational, where the nonnegative roots of Df,Da,Dt,Dg carry the
independent signs inherited from the factor. A positive odd integer
radicand has the form h u^2 for odd squarefree h and odd integer u.
Within any nontrivial squareclass h, the participating signed rational
coefficients are therefore odd multiples of distinct powers from
1,2,4,8. The coefficient of least 2-adic valuation is unique, so this
sum cannot be zero. Independence of squarefree radicals excludes every
nontrivial class. All four roots are rational and hence integers.
Denote the signed integer roots by f,ytilde,tau,g.

This is an arithmetic separation, not a numerical magnitude estimate.
It applies to every signed input satisfying the already proved
bootstrap. No ordering of the four magnitudes is assumed.

Since Da=delta Cy, the rational y=ytilde/delta satisfies

    QV^2-(Q-1)y^2=1.

Adjacent-coefficient Pell descent makes y integral. If y=a/b in lowest
terms, b^2 divides Q-1; the transformations

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserve the norm, the integrality of V', and the reduced denominator b.
With positive signs and |V|>1, -|V|<V'<|V|; the norm excludes V'=0.
Descent reaches |V|=|y|=1, so b=1.

## 5. The centered signed kernel with arbitrary nonzero strong multiplier

### 5.1 Exact recovered arithmetic

Put rho=Delta I. It is nonzero and c^2 divides rho. The recovered roots give

    f^2-Delta I^2=1,
    rho^2=Delta(f^2-1),
    rho^2 V^2-(rho^2-1)y^2=1,
    d_s=X+ac+gamma H,       d_s^2-Delta c^2=1,
    tau^2-XY^2(XY^2+1)k^2=1.

The two needed auxiliary congruences are exact:

    V=f o-c,              o=f(c-R+4IT),
    V=c j_aux-R,
    j_aux=4 Delta s^2 r^2 c^3(c-R)+8 s r c Df T.

Indeed V+R=Delta I^2(c-R)+4 I Df T. Transport is an identity by the
definition of F, and k=R+1+hE. The centered budget supplies common
nonzero signs of F,C,alpha and

    |c/k-Y|<1/2,       sign(c)=sign(kY).

We do not set r_old=(2 Delta s r-1)/2, which is not integral. The incoming strong multiplier is deliberately even.

### 5.2 Signed rank bootstrap, with the nonodd step proved explicitly

The inherited common-sign packing estimates, valid for the authentic
coefficient tuple and both signs of q, give

    Q0=|q|>=16,        Q0(Q0^2-1)<R<Q0^4-2.

Let U0=|X|>=4Q0, Z0=|Y|>=Q0^3, M0=|E|=U0 Z0>3R+1,
K=|k|, C0=|c|, B0=|a+2|, P0=|2XY^2+1|. Then
B0>R, P0>B0>=2, and C0>K. Consecutive-product and ordinary Pell
classification supply n,p>=1 with

    K=2 psi_P0(n),       C0=psi_B0(p),       p>n.

Writing xi=sign(X),sigma=sign(k), the first recurrence modulo M0 gives

    sigma xi^(n-1) 2n = R+1 modulo M0.

If its sign is positive, n>=(R+1)/2; if negative, n>R. Thus p>n>=24,
and Pell growth gives C0>2p and C0>2R. These deductions require only
K(Z0-1)<C0<K(Z0+1) and sign(c)=sign(kY), both stronger consequences of
the centered guard. They do not require eta>0.

Now f^2-(B0^2-1)I^2=1 with nonzero I supplies m>=1 such that

    |f|=chi_B0(m),       |I|=psi_B0(m).

Since C0^2 divides I, strong divisibility of the Pell sequence first gives
p|m. Write m=pv0 and D=chi_B0(p). Composition gives

    I_abs=C0 psi_D(v0),       D^2-1=(B0^2-1)C0^2,
    psi_D(v0)=v0 D^(v0-1) modulo C0.

Because gcd(D,C0)=1 and C0 divides psi_D(v0), C0 divides v0.
Consequently p C0 divides m, C0 divides m, and m>2p. This proves all
strong-rank inputs without any oddness assumption on I/c^2 or rho/c^2.

For the auxiliary norm use the Pell parameter S0=|rho|>1. Its positive
abscissa S0|V| equals chi_S0(ell), with ordinate |y|=psi_S0(ell).
The index ell is odd because chi_S0(2t)=(-1)^t modulo S0, whereas its
abscissa is divisible by S0. Writing ell=2t+1, the exact quotient
polynomial Q_t(S0^2)=chi_S0(ell)/S0 has

    Q_t(0)=(-1)^t ell,
    Q_t(1-B0^2)=(-1)^t psi_B0(ell).

Since rho^2=Delta(f^2-1) and c divides rho, the congruences V=-c mod |f|
and V=-R mod C0 yield

    psi_B0(ell)=+/-psi_B0(p) modulo |f|,
    ell=+/-R modulo C0.

Squaring the first and using chi_B0(2t)=1+2Delta psi_B0(t)^2 gives
chi_B0(2ell)=chi_B0(2p) modulo chi_B0(m). The inherited elementary
signed abscissa step-down applies since m>2p and yields
ell=+/-p modulo m. One proof reduces the index by shifts and reflections
to a signed chi_B0(t), 0<=t<=m; a negative residue cannot equal
chi_B0(2p), since 2chi_B0(m-1)<chi_B0(m), and strict growth identifies
the positive residue. Therefore R=+/-p modulo C0. With
0<R,p<C0/2 this forces p=R.

The negative first-index branch is now impossible, and no-wrap gives
2n=R+1, hence R is odd. The same sign-uniform Pell ratio estimate and
main-root congruence as in the centered source give

    |Y|>2^R,       X=sign(c) 2^R.

For clarity, the ratio lower bound is
C0/K>=(1/2)(((2B0-1)^2)/(2P0))^((R-1)/2), whose inner quotient exceeds
|X|-3>=61. Combined with C0/K<|Y|+1 this gives |Y|>2^R. The two main
Pell identities modulo H then select the signed power; the absolute
bounds turn the congruence into equality. No odd strong multiplier is
used in either step. Since X=2 modulo 3 and R is odd, sign(c)=+1 and
X=2^R. The surviving first-index sign gives k>0; then sign(c)=sign(kY)
gives Y>0.

### 5.3 Centered half-binomial recovery

Now A0=a+2>1, c=psi_A0(R)>0, and k=2psi_(2XY^2+1)((R+1)/2)>0.
The uniform centered half-binomial theorem is applicable with the exact
same outer coordinates. To make the use explicit, write R=2t+1 and

    L0=(X+1)^(2t)/(2X^t),
    Lratio=c/k,
    Mbin=binom(2t,t)+sum_{j=1}^t binom(2t,t+j)X^j,
    theta=sum_{j=1}^t binom(2t,t+j)/X^j.

Then Mbin is even, 0<theta<1/4 and L0=Mbin/2+theta/2. The elementary
Pell recurrence bounds, with X=2^R and Y>X, give

    0<Lratio-L0<12t/(X+1)<1/8.

This follows uniformly from
L0<Lratio<=L0(1+2/((X+1)Y))^(2t) and the centered upper bound
Lratio<Y+1/2; it is not a large-Y limit. Hence

    Mbin/2<Lratio<Mbin/2+1/4.

Since Y is an integer and |Lratio-Y|<1/2, Y=Mbin/2 and

    0<eta/k<1/4.

Thus eta>0 and k-eta>0. This argument is the centered source's late
orientation/interval restoration; it does not impose an unjustified
positive guard before recovering the ranks.

### 5.4 Optional literal odd-kernel restoration by fresh witnesses

To link to the exact ordinary calibration without an unrecorded change
of coordinate chart, one may now regenerate an odd strong/auxiliary
pair while holding every outer coordinate fixed. Since q,Y are even,
A0=a+2 is even. Since R is odd, c=psi_A0(R) is odd. Set

    Istar=psi_A0(Rc),       fstar=chi_A0(Rc).

Composition and the congruence in Section 5.2 give c^2|Istar. Its index
Rc is odd and A0 is even, so Istar is odd. Delta is odd as well. Thus
rho_star=Delta Istar is an odd multiple of c^2 and

    r_old=(rho_star/c^2-1)/2 in Z.

Put Sstar=rho_star, t=(R-1)/2, and let Q_t be the same odd quotient
polynomial. Set

    Vstar=(-1)^(t+1) Q_t(Sstar^2),
    ystar=psi_Sstar(R).

The norm is unchanged by this chosen sign of Vstar. Since
Sstar^2=Delta(fstar^2-1), the two quotient evaluations give

    Vstar=-c modulo fstar^2,
    Vstar=-R modulo c.

Therefore ostar=(Vstar+c)/fstar and jstar=(Vstar+R)/c are integers.
They restore Vstar=fstar ostar-c=c jstar-R and the ordinary odd strong
and auxiliary rows. The definition k=1-Vstar+c jstar+hE is still the
same k=R+1+hE. The already recovered eta,k-eta and native common signs
supply all old positivity representations; X=2^R restores the old square
coordinate 2^((R-1)/2). Thus an actual old signed Q41 zero exists using
fresh private witnesses, and its pinned ordinary compiler/calibration
theorem supplies a finite syntactic ZFC refutation.

This is existential regeneration only after rank and interval recovery,
not the false claim that the incoming multiplier 2Delta s r is odd.

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

## 7. Canonical completeness in the required witness order

The authentic source34 canonical family supplies the outer coordinates
j,C,z,h,v,w,c and native data, with A0=a+2 even, R=3 modulo 4,
c=psi_A0(R), d=chi_A0(R), and gamma=(d-b0)/H integral. Its prescribed
half-binomial Y gives, uniformly and independently of strong witnesses,

    Derr<=q^2/2,       0<eta/k<1/4,
    Budget>q^2 k^2/4>0.

These are the exact centered-budget completeness estimates, not an
assumption that arbitrary determinant-guard witnesses satisfy Budget>0.

Canonical Budget exceeds q^2 k^2/4>=64, so in particular it is at
least 2. Put D=3Budget-4, a positive nonsquare because D=2 modulo 3.
Ordinary Pell existence gives g0^2-D u0^2=1 with g0,u0>0. Squaring
this unit supplies

    g=g0^2+D u0^2,       s=g0 u0>0,
    g^2-4D s^2=1.

Use the interpolation lemma of Section 6 with N=2s. It fixes I,f such
that 8s c^2|I and every residue class modulo I remains available for T.
Set r=I/(2s c^2), which is integral and nonzero. The lemma requires
c=R modulo 4: here A0=2 modulo 4, and the odd-index recurrence gives
psi_A0(R)=R modulo 4.

Choose an intersective root a modulo I for pi(a+gamma). The same
already-fixed I,f admit T=a modulo I and an auxiliary norm root y by
Section 6. Hence I|pi(T+gamma). Put ytilde=delta y. All five radicands
Dm,Da,Dg,Dt,Df are now integer squares, and

    A+B d=H^5 pi(T+gamma)

is divisible by S=I H^5. Choose

    n=(A+B d)/S+2ytilde+f+4tau+8g-CenterShift.

This is an integer and makes one norm factor zero. The witness order is
native data and Budget, then s, then fixed I/f/r, then an intersective
residue and T/y, then CenterShift and n. Budget depends only on the native
outer coordinates, so the strong/Pell choices cannot invalidate it.
There is no circular selection of I after the desired residue is known.

## 8. Literal circuit, degree, comparison and proof boundary

The final degree and operation certificates are in DEGREE_PROOF.md and
METRICS.json. They apply to the fixed parity coefficients of Section 1, not
the predecessor's variable separating weights. The literal circuit has
exactly the eleven displayed unrestricted integer coordinates and six
fixed numeral ports. A denominator-free universal five-root evaluator
and full coefficient identity check are supplied locally.

The reduction has an integer zero exactly when the same inherited
source34/compiler and finite-refutation calibration has a finite ZFC
refutation. Under those ordinary theorems, ZFC proves universal
nonvanishing equivalent to Con(ZFC). This does not assert consistency,
global minimality, historical priority for the intersective polynomial,
or a new formal kernel/object-ZFC certificate.

The contribution is the composition of the centered budget with the
prior full-residue interpolation and the early main-root projection.
It removes the predecessor's nearest-square coordinate and replaces
all variable separating weights by four fixed powers of two. The twelve-integer low-degree
budget construction remains a different Pareto tradeoff. Finite circuit,
coefficient and proof-cut checks are distinguished from the unbounded
semantic proof and its inherited calibration.


## 9. Exact local source interfaces

- `provenance/interpolation12/INTERPOLATION12.md`: monotone intersective quintic, full-residue auxiliary interpolation and original twelve-integer construction. Sections 2 and 6 above retain its arguments with credit and notices.
- `provenance/centered17/BUDGET_PROOF.md` and `provenance/centered17/PROOF.md`: normalized strong rank, canonical normalized completion and centered-budget interface.
- `provenance/centered18/PROOF.md`: signed centered interval and uniform late half-binomial extraction, including canonical budget margin.
- `provenance/centered17/upstream/WAVE11_GUARDS_PROOF.md` and `provenance/centered18/upstream/PROOF44.md`: signed rank/power and authentic common-sign packing bounds.
- `provenance/rootfusion/`: exact ordinary source34/compiler/calibration interfaces and explicit formalization boundary.

All copies are pinned in SOURCE_PINS.json. The fixed coefficient payloads and complete finite reconstruction recipe are the shared authenticated `../guard/coefficients` directory in this deliverable bundle. No external archive or network access is required.
