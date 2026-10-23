# Twenty-four unrestricted integers: signed saturation synthesis

New result, 22 October 2026, relative to the audited inputless K215 compiler
in ProveIt snapshot a477d0fc8b6feda53796835564a988015e744d4d.

The literal positive norm circuit is package 21's `norm12_product.json`,
UNCHANGED. The new theorem enlarges its witness domain and changes only
the polynomial parametrization of the domain. Use one entire authentic
compiler tuple (beta,K0,MC,MF), with MF the shifted high mask. The delivered
numeric backend is the new complete parity-layout Wang943 tuple, d=5^10,
proved in ../coefficients/PARITY_COEFFICIENT_PROOF.md. Package 19's old
compact tuple is another compatible backend, but the four ports must
never be spliced between layouts.

## 1. Domain and literal polynomial

Require only J,F,alpha,z,eta,zeta > 0. Put i=2i0+1, s=2s0+1,
w=w0^2, and allow h,T,r to be arbitrary integers. Replace each of the six
positive variables by a distinct copy of

    Pos(x,y,t)=1+x^2+y^2+t(t+1).

This leaves 18+6=24 unrestricted integers. The six other coordinates are
i0,s0,w0,h,T,r. All arithmetic below is polynomial arithmetic; every
temporary letter is an abbreviation, never an additional unknown.

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    ell=E kY, A=1+ell(ell+k), G=1+Delta c^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R, Nt=(K0+w)C+(q-F)-z(q-1),
    D=1+Delta i^2 c^4, Q=(Delta i c^2)^2, d=Q-1,
    v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, Baux=2Qvb,
    Bnd=v^2+D+2b, L=1+H Bnd, S=X+ac+Hr.

For a polynomial p(t), reduce modulo t^2-g to p0+p1*t and define
Norm_g,t(p)=p0^2-g*p1^2. Define

    N=Norm_G,u Norm_A,t( [d(S-Lu-HLt)^2-H^2 e]^2-H^4 Baux^2 D ).

The proposed polynomial is P=Nk*Nt*(1+N)-1. The system is Nk=1,Nt=1,N=0.
The sum of squares is (Nk-1)^2+(Nt-1)^2+N^2.

## 2. Unit guard and outer bounds

The unchanged norm circuit has N=N0^2-G*N1^2 where 8 divides N1 as
an integer polynomial. Thus N is a square modulo four. If P=0, all
three factors Nk,Nt,1+N are integer units, and 1+N cannot equal -1.
Therefore N=0 and Nk=Nt is either 1 or -1. For the system these facts
are immediate with the positive unit signs.

Write epsilon=Nk and nu=Nt. Since F,z are positive,
(q-F)-z(q-1)=1-F-(z-1)(q-1)<=0. With K0+w>=2,
C<=-1 would make Nt<=-2. Hence C>=0 and q-F=C+alpha>0.
The authentic compiler mask bounds (proved in the inherited inputless
interface) then give

    q>=16, q(q^2-1)<R<q^4-2, R-2>3q+1.

No sign of s,h,T,r was assumed. Set Z=abs(Y)>=q^3. X>=0,
abs(a)=(X+1)Z>=q^3, abs(c)>k(Z-1)>1, abs(H)>1, and

    Delta >= (q^3-1)(q^3-3)>q^4>R.

The last elementary inequality holds already for q>=16. Since i is
nonzero, D=1+Delta*i^2*c^4>Delta+abs(c). It follows that

    G>1, D>1, Q>1, 1<b=c+RD<Q,

because Q-b=(Delta-R)D-Delta-c>=D-Delta-abs(c)>0.
Also ell=X*k*Y^2>=0 and A>=1. Thus Bnd is positive.

## 3. Coherent algebraic roots and signed separation

Since N is the product of eight factors over u=+-sqrt(G),
t=+-sqrt(A), f=+-sqrt(D), N=0 supplies a coherent triple with

    y=(S-Lu-HLt)/H,
    d y^2=e-Baux f=Q(vf-b)^2-1.

Work in a finite normal splitting field containing these numbers. Every
conjugate y' satisfies abs(y')<Bnd. Indeed put M=abs(v)*sqrt(D)+b>1.
The real numbers Q(vf'-b)^2-1 lie between -1 and QM^2-1; since QM^2>2,
their absolute values are <=QM^2-1. Hence

    abs(y')^2 <= (QM^2-1)/(Q-1) < 2M^2,
    Bnd=v^2+D+2b >= 2M > abs(y').

This explicitly covers imaginary y branches. Put U=abs(H)*Bnd>2.
Although L may be negative, abs(L)>=U-1, so

    abs(L)*sqrt(G)>U,

since sqrt(G)>2. If X>0, then X>=q and abs(E)>=1. We have
abs(c)<2kZ, sqrt(G)<(abs(a)+2)*abs(c), sqrt(A)>ell=kZ*abs(E),
and abs(H)>=4abs(a)-3. Therefore

    abs(H)*sqrt(A)-sqrt(G)
      > kZ*((4abs(a)-3)*abs(E)-2(abs(a)+2))
      >= kZ*(2abs(a)-7)>2.

Consequently

    abs(HL)*sqrt(A)>abs(L)*sqrt(G)+abs(H)*Bnd.

If t were irrational, an automorphism of the normal closure would flip
its sign. Subtracting S=Lu+HLt+Hy from its conjugate contradicts this
strict dominance bound. Thus t is rational. At X=0 one has A=1, so
t is rational directly, and no dominance assertion is needed.
With t rational, an automorphism flipping u would contradict
abs(L)*sqrt(G)>abs(H)*Bnd. Hence u is rational too. Since their
squares are integers, u,t are integers. The linear equation makes y rational.

## 4. Pell saturation, degeneracies, and integrality

Use the rational Pell saturation lemma: if m>=2 and V are integers and
m^2 V^2-(m^2-1)y^2=1 for rational y, then y is an integer.
A proof is included in the report and in upstream 21's NORM12_PROOF.md.

If T!=0, then v!=0, b>1, Baux!=0. The formula
f=(e-d y^2)/Baux shows f is rational; f^2=D makes f integral.
Now V=vf-b is an integer, and Q=m^2 with m=abs(Delta*i*c^2)>=2,
so saturation makes y integral. If T=0, the same lemma applies directly
with V=b and again makes y integral, without first reconstructing f.
Because L=1 modulo H, the equality S=Lu+HLt+Hy now gives

    gamma=(u-X-ac)/H=r-Bnd*u-L*t-y in Z.

If X=0, the main norm u^2-Delta*c^2=1 and u=ac+H*gamma imply
H divides 1. This contradicts abs(H)>1. Hence X>0 and w>0.
If T=0, then

    y^2=b^2+(b^2-1)/(Q-1).

The strict interval 1<b<Q puts this value strictly between b^2 and
(b+1)^2, contradicting integer y. Therefore T!=0 and f is integral
in every case. The recovered roots obey all four normalized core norms:

    t^2-ell(ell+k)=1,
    (X+ac+H*gamma)^2-Delta*c^2=1,
    f^2-Delta*i^2*c^4=1,
    Q*[c(Tf-1)-R*f^2]^2-(Q-1)*y^2=1.

Here y,t,f,gamma may have either sign.

## 5. Eliminate the negative scale and decode

The signed scale exclusion of upstream 23 ODD_SCALE_27_PROOF.md,
Sections 1-4, applies to exactly these reconstructed equations. Its
proof requires the normalized multiplier i to be nonzero; it does not
require it to be positive. Taking abs(i) leaves all four equations
unchanged. It permits signed roots, h, T, and gamma and the equal unit
signs Nk,Nt above. It proves s>0. For clarity its key argument is:

If s<0 put Z=-Y, B=(X+1)Z-2, c0=-c and P0=2XZ^2+1.
The first/main Pell classifications and the normalized rank/auxiliary
congruences recover p=R. Their strict ratio interval gives
R=2r0+1 and Z>X^r0/2>2^R. The two signs of the main Pell root give
either X+2^R=0 modulo H or X*2^R=1 modulo H. The strict bounds
0<X+2^R<abs(H) and 1<X*2^R<XZ<abs(H) rule out both. Thus s>0.

All prescribed scale and guarded variables are now positive. The
signed normalized inputless compiler theorem (ordinary multiplier
i_ordinary=Delta*abs(i)) recovers a genuine blank K215 halt. It also
forces Nk=Nt=1, so the product and the system have the same existence
condition. The sum of squares has the system's exact zero set.

## 6. Completeness

Start with an actual blank K215 halting computation. The authentic
compiler's independent power-of-five width/height padding can take
q=2^(dN) with dN odd. Its canonical rank R is odd and gives
w=2^R/q=2^(R-dN), a positive square. The normalized strong index m=cR
gives an odd positive i, as established in upstream 21 SIGNED_DOMAIN_29.md.
The exact native population calculation in upstream23 Section5 gives

    popcount(R)=3log2(q)+2,
    v2(Y)=popcount(R)-2=3log2(q).

Thus s=Y/q^3 is positive odd. The six remaining guarded quantities are
positive. Every positive integer is Pos(x,y,t): apply the three-square
theorem to 4n-3, which is 1 modulo4, and separate its one odd square.

For the canonical roots define r=gamma+Bnd*u+L*t+y. It is an integer
(indeed positive), and makes one norm factor vanish. Hence P=0 and
the three-equation system holds after the 24-variable substitution.

The finite consistency equivalence is consequently
ZFC proves [exists a 24-integer zero] iff [ZFC has a finite refutation].
Negating yields the requested ZFC-provable equivalence with Con(ZFC).
This is an ordinary proof internalizable in ZFC, using the inherited
compiler and exact-machine calibration. It is not a new Lean/Rocq result.

## 7. Exact arithmetic metrics

Six Pos substitutions cost 42 gates; the two odd affine maps cost 4;
the square map costs1. With package21's unchanged circuits the totals are:

    three equations: 24 integers, 159 gates, maximum degree2416;
    single product: 24 integers, 163 gates, degree2432;
    sum of squares: 24 integers, 166 gates, degree4832.

The recommended three-equation presentation saves two more gates. Replace
the old positive z by z_new+1 and write transport as
(K0+w)C=F+z_new(q-1), then compare N0^2 directly with G*N1^2.
The source theorem after soundness recovers C>0 and w>q>F, so every old
solution has z_old>=2 and the shift preserves existence in both directions.
Six independent Pos maps are still used, now including z_new. The direct
comparison eliminates the subtraction defining N. The resulting shifted
system has 24 integer unknowns, three equations, 157 gates and residual
degrees 12,4,2416. The unchanged product uses the old z and remains163 gates.

All binary additions/subtractions/multiplications, including fixed scalar
multiplications, are charged. Fixed coefficient ports have degree0 and
are not existential variables. Comparisons in a system are not charged.

For the exact degrees, give J,F,alpha,z,w,eta,zeta weight2 and all other
core variables weight1. The same unique leading branches as package21
give N degree2416, Nk degree12 and Nt degree4. Put q0=beta*J and
k0=eta+zeta. The product's highest weighted homogeneous form is

    -2^80 h i^48 k0^112 w^113 s^225 q0^836 (q0-F)^16
      *[w(q0-F-alpha)-z*q0].

After the actual substitutions its monomial

    J_x^1706 * h * z_x^2 * i0^48 * eta_x^224 * w0^226 * s0^225

has coefficient +2^353*beta^853. It is nonzero for the fixed beta>0
and has degree2432. The norm's leading monomial similarly has coefficient
2^352*beta^848 and degree2416. Thus these are uniform exact degrees,
not degree estimates based only on a few small coefficient evaluations.

The new product improves all three recorded metrics of every 26-integer
wave3 product: fewer variables, fewer gates, and smaller degree. It does
not improve the 67-operation positive polynomial, the positive quartic
lifts, the 27-integer low-degree forms, or the nine-natural-variable
Jones representation. No global minimality is asserted.
