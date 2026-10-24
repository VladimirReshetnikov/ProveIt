# Coprime fusion: ten strictly positive unknowns, degree 266

This is an ordinary unbounded arithmetic reduction relative to the pinned
source/native/refutation calibration. It is not a new formal proof in Lean
or an encoded internal-ZFC certificate, and no optimality claim is made.
All fixed ports are the complete coherent original compact44 tuple from
commit 84e16e43092614bae262ca59651cb9d77e31a255. A separately calibrated
BFS tuple can instantiate the uniform argument only as an entire tuple;
its K0 is not identified with or substituted into this packet's tuple.

## 1. Complete equation and the structural change

The independent variables are J,F,alpha,i,T,x,Y,n,eta,zeta > 0. The
fixed ports obey beta odd, beta >= 31, K0 > 0 and 0 < MC < beta < MF < 2beta.
Define, using ordinary integer polynomial expressions,

    q=beta*J+1, X=q+x, mu=q²+1, A=mu*Y*(X+1)+1,
    Delta=A²-1, H=4A-5, k=eta+zeta, c=k*Y+eta,
    Vfirst=X*mu²*Y², D=Vfirst*(Vfirst+1)*k²+1,
    G=(q-1)*(q-F)+alpha,
    R=G*(q²-1)+(MC+q*MF)*J, e=k-R-1,
    C=q-F-alpha, B=(q*K0+X)*C-q*F,
    E=i*c², Fstrong=1+Delta*D*E²,
    Q=Delta²*D*E², delta=Q-1,
    b=c*(T+alpha)-R, V=Fstrong*b-c, Dnum=Q*V²-1,
    L=H*D*E+b, W=1+q*(q-1)*L,
    P=q⁴*(q-1), M=P*mu²*H, Kpos=X*(3c-2X)+2,
    Z=P*mu²*(H*(n+V)+Kpos)
      +H*(mu²*(q*(q-1)*Y-q³*W*B-(q-1)*X)-P*e),
    a=D*Fstrong, s=delta*Z², u=delta*M²*a, v=M²*Dnum.

The equation is

    N=(s-v-u)²-4*u*v=0.                                  (1)

Every displayed abbreviation is a polynomial; only the ten named inputs
are quantified. The literal complete binary-arithmetic schedule is in
equation.json. It uses 98 live operations: 59 multiplications, 21 additions
and 18 subtractions. Its register I denotes E, NOT the later actual Pell
ordinate. Dtau denotes D and Df denotes Fstrong.

The new idea is to put D into the strong squared ordinate, making D and
Fstrong automatically coprime, then replace three separate radicals by
sqrt(D*Fstrong) and the auxiliary radical. Once D=tau² is recovered, the
actual strong ordinate is Iactual=tau*E. It is an integer, but need not
be a polynomial in the ten inputs. No polynomial Iactual is asserted.

The carrier has exact rational center

    Z/M=n+V+Kpos/H+Y/q³-W*B/[q(q-1)]-X/q⁴-e/mu².           (2)

These divisions are proof notation only.

## 2. Root extraction before all parity and transport claims

For every positive input, q>=32, X>q, A>4, c>=3, E>=c² and D>1.
The elementary parent bounds delta>c²-1>0, Fstrong>c+2 and
Fstrong<delta hold even more strongly after inserting the factor D>1.
If b=0, V=-c and c²<Dnum/delta<c²+1. If b is nonzero,
|V|>=Fstrong-c>1, so Dnum/delta>0. Thus both radicands a and
Dy=Dnum/delta are strictly positive before any root is rational.

They are unequal. If delta*a=Dnum, reduce modulo the positive integer
D>1. Since Q is a multiple of D, the left side is zero modulo D,
whereas Dnum=Q*V²-1 is -1 modulo D, impossible.

The universal identity

    (z²-a-y²)²-4*a*y²
       = product over eps,nu in {+1,-1} of (z-eps*sqrt(a)-nu*y)

shows that (1) gives Z/M=eps*sqrt(a)+nu*sqrt(Dy). The sum cannot be
zero, by the unequal-radicand argument. A nonzero rational signed sum of
two square roots of positive rationals makes both square roots rational:
square and solve linearly for either radical. As a is an integer,
sqrt(a) is an integer. Moreover gcd(D,Fstrong)=1 because
Fstrong=1 modulo D. Unique prime factorization therefore gives

    D=tau², Fstrong=f², tau,f positive integers.

Set Iactual=tau*E. Then

    f²-Delta*Iactual²=1,
    Q=(Delta*Iactual)²,
    c² divides Iactual, and Iactual>=c.

The parent's adjacent-Pell rational-to-integral descent, now with the
integer S=Delta*Iactual, gives y=sqrt(Dy) a positive integer. The signed
center has consequently become

    Z/M=eps*tau*f+nu*y.                                  (3)

The extraction does not assume q even, mu²|e, B>=0 or a selected sign.

## 3. Main folding and transport, in the required order

The retained all-index strong/auxiliary folding lemma applies to A,
c,Iactual,f,V,y: A>=3, c<=Iactual, f>2Iactual and
V=f²*b-c=-c modulo f. It recovers c=psi_A(p) for an odd p>=1.
The first Pell equation D=tau² gives

    k=2*psi_(2Vfirst+1)(n0), tau=chi_(2Vfirst+1)(n0), n0>=1.

As in the zero-offset parent, n0=1 would imply c=2Y+1 strictly between
psi_A(1)=1 and psi_A(2)=2A. Thus n0>=2 and

    c>kY>=k>=4*(2Vfirst+1)>8X*mu²*Y².                    (4)

The unchanged mask bound gives R<c*alpha/4, and hence b>0,
V>0, |e/mu²|<b/2, 0<y-V<b/2. The last bound follows from
Dy=V²+(V²-1)/delta and Fstrong<delta, exactly as in the parent.
Also c>2X, so Kpos>0.

The new transport majorant is polynomial and needs no extra assumption:
f<A*Iactual, so tau*f<A*D*E. Since D=Vfirst*(Vfirst+1)*k²+1>X and E>=1,

    tau*f+X/q⁴ < (A+1)*D*E < H*D*E.                    (5)

Here H=4A-5>A+1 because A>2. If B<=-1, W=1+q(q-1)L and L>0
imply W*B/[q(q-1)]<-L. Solve (2)-(3) for n and use (5), the two b/2
bounds, Kpos/H>0 and Y/q³>0 to obtain

    n< H*D*E+b-L=0,

contradicting positivity. Hence B>=0. Its definition forces C>0, and the
unchanged mask estimate then gives 3q<R<q⁴-2.

The normalized strong-rank and signed auxiliary-index lemmas need only
c²|Iactual, c>2R, c>2p, V=-c modulo f and V=-R modulo c.
All these hold, so p=R. The oddness of p gives R odd, and the original
mask parity argument gives q even and J odd. This chronology does not
use denominator coprimality before it is licensed.

## 4. First index, whole-product projection, and source reconstruction

Now gcd(mu²,q⁴(q-1)H)=1, because gcd(mu,q)=1, q is even and
H=-1 modulo mu. Since (3) is integral, separating the single modulus
mu² in (2) proves mu²|e. The first Pell congruence and comparison
2Vfirst+1>A are unchanged; the parent's short-index argument gives
n0=(R+1)/2. Write R=2r+1, r>=48.

The exact zero-offset ratio lemma for
A=mu*Y*(X+1)+1 and Pfirst=2X*mu²*Y²+1, uniform in X>=32, gives

    xi < psi_A(2r+1)/psi_Pfirst(r+1) < xi*(1+1/[Y(X+1)])^(2r),
    xi=(X+1)^(2r)/X^r.

It yields Y>X^r/3 and X^(r+1)<3Y(X+1)<H. Every expression in these
arguments is unchanged by the strong-root fusion.

The integral center (3) gives H|P*Kpos. Since H is odd and

    Kpos=H*X*c-2*Kquad, Kquad=X*(X+2(A-2)c)-1,

cancel only 2 and apply the universal projection lemma to get

    H | q⁴(q-1)*(X-2^R)*(2^R*X+1).

The complete right-side product has absolute value strictly less than
X^(r+1)<H, using X>=q>=32 and r>=48 exactly as in the direct-base
parent. Thus X=2^R, not just a primewise choice of branches. This makes
Kpos/H integral. No factor q or q-1 is cancelled through H.

Removing the now integral terms from (2) leaves
Y/q³-WB/[q(q-1)]-X/q⁴ integral. Clearing its denominator and reducing
modulo q proves q|X. Hence q=2^kappa and R>3q>4kappa, so q⁴|X.
Write w=X/q and Bt=(K0+w)C-F; then B=q*Bt. The remaining partial
fractions give q³|Y and q-1|Bt, since W=1 modulo q-1. Consequently
t=Bt/(q-1)>=0 is an integer. The unchanged fixed-minus auxiliary
parity lemma gives R=3 modulo 4, and the same ratio rounding proves
that Y is the source half-binomial.

Reconstruct the parent's fresh UNSCALED source at A_source=Y(X+1)+2,
using J,F,alpha,w,Y and the recovered source data. This does not reuse
Iactual or identify the scaled parameter with the source parameter.
The pinned source61/native/controller theorem gives a finite refutation.
This proves soundness relative to the same coherent native calibration.

## 5. Completeness with genuinely new positive witnesses

A finite refutation supplies the parent's canonical source data with
X=2^R>q, R=3 modulo 4, r=(R-1)/2>=48, q³|Y, q⁴|X and t>=0.
Keep J,F,alpha,Y, set x=X-q>0, and form the new zero-offset first and
main parameters. The retained ratio lemma supplies positive integers

    c=psi_A(R), k=2*psi_Pfirst(r+1), tau=chi_Pfirst(r+1),
    eta=c-kY>0, zeta=k-eta>0,
    rho=(k-R-1)/mu²>=1.

Choose a positive index m for which tau*c² divides psi_A(m). Such an
index exists by finiteness of SL_2(Z/(tau*c²)Z): the recurrence matrix
[[2A,-1],[1,0]] is invertible, so a positive power is the identity and
its corresponding psi value is zero modulo tau*c². Put

    Iactual=psi_A(m), i=Iactual/(tau*c²)>0, f=chi_A(m).

Then E=i*c² and Fstrong=1+Delta*D*E²=f² exactly. The actual strong
ordinate has the extra first-root divisor without any unsupported claim
about divisibility of the parent's former ordinate.

The retained universal auxiliary-completeness lemma applies because
R=3 modulo 4, c=psi_A(R), c|Iactual, and the strong Pell equation holds.
It supplies Tstar,uaux>0 with
V=f²*(c*Tstar-R)-c and y=V+uaux satisfying QV²-(Q-1)y²=1.
Its same explicit growth estimate gives Tstar>alpha; set T=Tstar-alpha>0.
There is no need to match a previous auxiliary witness.

The universal projection gives the positive integer kpos=Kpos/H<X*c.
As in the parent, f>(A-1)*Iactual>X*c>kpos, and tau>Y>=Y/q³.
In fact tau*f>tau+f because tau,f>=3. Therefore

    tau*f > Y/q³+kpos.

Let W be the actual new polynomial transport weight, sY=Y/q³ and
uX=X/q⁴. Define the integer

    n=W*t+rho+tau*f+uaux-sY-kpos+uX.

It is strictly positive, including t=0. Substitute in (2): the center
is tau*f+y, so a factor in the quartic norm vanishes. Every coordinate
is a strictly positive integer. This proves completeness; no positive
pointwise inverse between the old and new i,n coordinates is claimed.

## 6. Exact degree, not just syntactic degree

All variables have degree 1; fixed ports have degree 0. The literal
bounds are A4, D16, E5, Fstrong34, Q42, V38, L25, W27, M13, Z51.
The raw syntactic norm bound is 288. Put Z0=Z-MV. Its degree is 40,
with unique highest part supplied by -H*mu²*q³*W*B.
Writing omega=s-v gives the universal centered identity

    omega=delta*Z0²+2*delta*M*V*Z0-M²*(V²-1).

The three terms have degrees at most 122,133,102 respectively, so
omega has degree 133. Also u has degree 118, v has degree 144.
Consequently N=(omega-u)²-4uv has degree at most 266, with omega²
uniquely dominant (the other possible bounds are 251,236 and262).

For an attained leading coefficient set q0=beta*J, X0=q0+x,
k0=eta+zeta, B0=(q0*K0+X0)*(q0-F-alpha)-q0*F. The complete leading form is

    omega0=2^7*q0^63*X0^15*i^5*Y^31*k0^16*B0*(q0-F).

The highest-x part of omega0² has x exponent32. Selecting alpha²,
F² and eta^32 gives the nonzero coefficient

    [J^126*x^32*i^10*Y^62*eta^32*alpha²*F²] N
        =2^14*beta^126 > 0.

The exponents sum to266. Thus the exact total degree is266 for the
complete compact44 tuple, not merely for generic symbolic ports.

## 7. Scope and dependencies

Both directions use the universal Pell classification, composition,
folding, normalized rank, signed index, fixed-minus parity, projection,
auxiliary-completeness and ratio/source reconstruction lemmas retained
in candidates/ten-positive-direct-zero-offset/PROOF.md and
candidates/ten-positive-zero-offset/{PROOF.md,source/ORIGINAL_PROOF.md,
source/QUADRATIC_PROOF.md,source/WEIGHTED_PROOF.md}. Their hypotheses
are checked above; the new first/strong coprime fusion is proved here.
The equivalence to syntactic Con(ZFC) inherits the exact native/source
calibration of that pinned commit. Finite tests check transcription,
algebra and degree but do not prove those unbounded source theorems.
