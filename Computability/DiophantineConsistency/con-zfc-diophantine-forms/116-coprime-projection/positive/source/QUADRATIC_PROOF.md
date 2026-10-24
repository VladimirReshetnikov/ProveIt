# A three-root norm with a quadratic projection

This is an ordinary unbounded arithmetic proof. Lean remains paused. It
proves an equivalence of positive zero existence with the frozen
`ten-positive-scaled-norm-reuse` endpoint, not a pointwise equality of
their two polynomials. Consequently it inherits exactly the same native
compiler/refutation boundary as that endpoint. No consistency or absence
of zeros is asserted independently.

Write A for the frozen proof's A', Delta=A^2-1, H=4A-5, a'=A-2,
P=q^3(q-1), M=P mu^2 H. Retain all ten positive unknowns and every
definition in the frozen endpoint through the transport data, except the
changes specified below. All unqualified Pell facts/lemmas and the old
ordinary endpoint theorem mean those proved/reviewed in
`source/original-proof.md`, with its unchanged hypotheses. The fixed-port
conditions used here are beta odd, beta>=11, 0<MC<beta<MF<2beta and K0>0.
The authentic compact44 tuple, and the separately calibrated page tuple,
both satisfy these conditions.

## 1. The new equation

Put

    Kquad = X(X+2a'c)-1,
    Z = P mu^2 [H(n+V)+Kquad]
        + H[mu^2((q-1)Y-q^3 W Bt)-P e].

Thus

    Z/M = n+V + Kquad/H + Y/q^3 - W Bt/(q-1) - e/mu^2.       (1)

Retain the three radicands

    s = delta Z^2,
    u = delta M^2 Dtau,
    v = delta M^2 Df,
    w = M^2 Dnum.

For arbitrary s,u,v,w define

    sigma1=u+v+w, sigma2=uv+(u+v)w, sigma3=uvw,
    F8(s;u,v,w)=((s-sigma1)^2-4sigma2)^2-64sigma3 s.          (2)

The new single equation is F8(s;u,v,w)=0. Its literal complete circuit
has106 live binary operations. The old Dmain and fourth norm radicand
are not computed. The scalar Kquad is not the fixed native port K0.

The elementary identity

    F8(x^2;ra^2,rb^2,rc^2)
      = product_(eps1,eps2,eps3) (x-eps1 ra-eps2 rb-eps3 rc)   (3)

is the standard octic norm, checked here by full independent sparse-ring
expansion. Hence, for positive inputs, the new equation is equivalent to
a signed relation

    Z/M = eps1 tau + eps2 f + eps3 y,                        (4)

where tau=sqrt(Dtau), f=sqrt(Df), y=sqrt(Dnum/delta). The prefactor in
(3) is delta^4 M^8, which is positive. Positivity and the three-root
noncancellation proof below are established before any integrality is
inferred.

## 2. Recovering the omitted main Pell root

The key lemma does not assume that c already is a Pell value.

**Lemma 2.1 (folding the psi sequence modulo a strong root).** Let A>=3,
Delta=A^2-1, m>=1, f=chi_A(m), I=psi_A(m). For every integer v, there
exist p with 0<=p<=m and eps in {1,-1} such that

    psi_A(v) = eps psi_A(p) (mod f).

Indeed alpha^(2m)=-1 modulo f in the quadratic ring, since
chi_A(2m)=2f^2-1 and psi_A(2m)=2fI. Therefore
psi_A(t+2m)=-psi_A(t) modulo f, including negative t. Reduce v modulo
2m to t in [0,2m). If t<=m use p=t. Otherwise use p=2m-t and
psi_A(2m-p)=psi_A(p) modulo f. The reduction contributes only a sign.
This is a congruence for all integer indices, not a finite sample or a
claim that the huge index v itself is small.

**Lemma 2.2 (main classification from strong and auxiliary equations).**
Suppose A>=3, c,I,f are positive integers, c<=I,

    f^2-Delta I^2=1,
    S=Delta I,
    S^2 V^2-(S^2-1)y^2=1,
    V=-c (mod f),

where V is an integer and y is a positive integer. Then
c=psi_A(p) for some p>=1.

First S>=2 and V!=0. Strong Pell classification gives
f=chi_A(m), I=psi_A(m) with m>=1. Also Delta>=8, so f>2I.
Classify the positive Pell pair (S|V|,y) for parameter S:

    S|V|=chi_S(v), y=psi_S(v), v>=1.

The recurrence gives chi_S(2j)=(-1)^j modulo S. Since S divides
chi_S(v) and S>=2, v is odd, say v=2h+1. Write
chi_Z(2h+1)=Z Q_h(Z^2). The exact polynomial identity from the frozen
proof's P8 gives

    |V|=Q_h(S^2),
    Q_h(1-A^2)=(-1)^h psi_A(2h+1).

Because S^2=Delta(f^2-1)=1-A^2 modulo f, we obtain
psi_A(v)=+c or -c modulo f; the possible sign of V is included.
By Lemma2.1, psi_A(p)=+c or -c modulo f for some 0<=p<=m.
Now 0<=psi_A(p)<=I and 0<c<=I, while I+c<=2I<f. The congruence with
minus c would make a positive number psi_A(p)+c strictly between0 and f
divisible by f. The remaining congruence has difference of absolute value
less than f, so psi_A(p)=c. Since c>0, p>=1. Set Dm=chi_A(p).
This proves Dm^2-Delta c^2=1 without a main-Pell radicand in the equation.

## 3. Soundness through the first-index and ratio bounds

Assume the new equation at a positive input. All bounds in old Section5
that involve only tau,f,y remain unchanged; none requires Dmain to be a
square. Specifically, with b=c(T+alpha)-R:

* If b=0, c<y<c+1, tau>2c+1, and f>tau+2c+1.
* If b!=0, tau<f and y>2f.

Thus the three roots are positive, no nonempty signed subsum vanishes,
and the rational signed sum (4) makes each root rational by old L1.
Their squares make tau,f integral. Old adjacent-coefficient descent L2
makes y integral; Q>1 and V integer are already known. These estimates
hold for both signs of V before any source equation has been recovered.

Apply Lemma2.2: I=i mu c^2>=c, and V=Df b-c=f^2 b-c=-c modulo f.
It follows that c=psi_A(p), Dm=chi_A(p) for p>=1. Classifying the first
Pell equation gives k=2psi_P'(n0), tau=chi_P'(n0). Old Section6.6 now
applies verbatim: n0=1 would imply c=2Y+1 strictly between psi_A(1)
and psi_A(2). Hence n0>=2 and c>8X mu^2Y^2>=8q^5. Consequently b>=1,
V>0, and0<y-V<b/2 exactly as in old Section6.7.

Subtracting n+V from (4) and using(1), the right side is an integer.
Since mu^2 is coprime to q^3(q-1)H, old partial-fraction L3 gives
mu^2|e. Put rho=e/mu^2 and s0=Y/q^3, t=Bt/(q-1). Then

    n=eps1 tau+eps2 f+(eps3 y-V)-Kquad/H-s0+Wt+rho.            (5)

Here Kquad>0. The old transport proof becomes simpler: if Bt<=-1 then
Wt<-L, |rho|<b/2+c(T+alpha)/2, and tau+f<3(A-1)I. Thus (5) gives

    n < 3(A-1)I+b+c(T+alpha)/2-L < 0,

because L=4(A-1)I+b+c(T+alpha). This contradicts n>0. Therefore
Bt>=0, C>0, and the unchanged masks imply

    3q<R<q^4-2.                                                (6)

All hypotheses of the old rank/index lemmas now hold: c>2R, c>2p,
c^2|I, V=-c modulo f and V=-R modulo c. They give p=R. The first-index
argument of old Section6.13 gives n0=(R+1)/2. Write R=2r+1. The actual
ports ensure q>=32; (6) gives r>=48. The old ratio lemma L4(a) yields

    Y>X^r/3,   X^(r+1)<3a<H.                                 (7)

No assertion about the fourth signed root was used in this derivation.

## 4. The squared projection has no extra branch

**Lemma4.1 (whole-product height).** If X>=q>=32, R=2r+1 and r>=30,
then

    q^4 2^(2R+2)X^2 < X^(r+1).

To see this, X^(r-1)>=q^4 32^(r-5)=q^4 2^(5r-25), and
5r-25>4r+4=2R+2 for r>=30. Multiply by X^2. This proves the strict
inequality at the minimal stated q,r, with no asymptotic assumption.
Our actual r>=48 is more than sufficient.

After mu^2|e, multiply the integral relation by q^3(q-1):

    H | q^3(q-1) Kquad.                                      (8)

Now c=psi_A(R), Dm=chi_A(R). Old projection L5 says

    Dm-a'c=2^R, Dm+a'c=2^(-R) (mod H).

Here H is odd. Hence

    2^R Kquad = (X-2^R)(2^R X+1) (mod H).                     (9)

Combining(8),(9), H divides the integer

    D=q^3(q-1)(X-2^R)(2^R X+1).

For X>=1,R>=1, each factor |X-2^R| and 2^R X+1 is at most
2^(R+1)X. Therefore

    |D| < q^4 2^(2R+2)X^2 < X^(r+1) < H.

An integer multiple of positive H with absolute value less than H is0.
The factor 2^R X+1 is strictly positive, so **X=2^R**. This excludes all
mixed-prime branches of the quadratic congruence by the size of the
whole product; no cancellation through a possibly noncoprime factor or
primewise choice of a square root is used.

With X=2^R, (9) and odd H give H|Kquad. L5 also gives
H|(Dm-X-a'c). Set

    kappa0=Kquad/H, g=(Dm-X-a'c)/H.

Both are positive integers. For g, use
Dm-a'c=2c-psi_A(R-1)>c>X; the last inequality follows already from
n0>=2 and c>8X mu^2Y^2. Dividing(1)'s integral relation after these
two projections also gives q^3|Y and q-1|Bt, by the same coprimality
argument as old Section6.16.

## 5. Explicit maps of positive zero existence

**New zero to old zero.** Retain every unknown except replace n by

    n_old=n+kappa0+g.

This is a positive integer. All other kernel registers, including V,
are unchanged. The old normalized center is the new normalized center
plus Dm/H, because

    n_old+(X+a'c)/H = n+Kquad/H+Dm/H.

Thus (4) makes an old four-root factor vanish, with fourth sign+1.
The original frozen endpoint has a strictly positive zero.

**Old zero to new zero.** Apply the old soundness proof to an arbitrary
positive zero, recovering the positive integers tau,f,y,Dm, the same
kernel parameters, X=2^R, s0=Y/q^3>=1, t=Bt/(q-1)>=0 and
rho=e/mu^2>=1. The latter follows from
e=2psi_P'(r+1)-2(r+1)>0. Let u0=y-V>0 and retain every unknown other
than n, setting

    n_new=Wt+rho+tau+f+u0-s0-kappa0.                          (10)

This is an integer. It is strictly positive: tau>k>Y>=s0 because
n0>=2 and k>=4P'>Y. Also

    0<kappa0=(X^2+2(A-2)cX-1)/(4A-5)
                < X+cX/2 < Xc < f.

The first strict upper bound uses H>X and2(A-2)/H<1/2; c>=3 gives
the next. The final bound follows from
f>(A-1)I>=mu^2(a+2)c^2>Xc. All other terms of(10) are nonnegative.
With this n_new, (1) is exactly tau+f+y, so the three-positive-root
factor vanishes. This supplies a new positive zero.

These maps prove equivalence of positive zero existence with the frozen
endpoint, including both directions without a new native-calibration
claim. They do not assert a bijection of the entire zero sets or a
pointwise polynomial identity. Composing the frozen endpoint theorem
gives the same ordinary refutation/consistency equivalence, with its
existing internal-ZFC/Lean obligation still open.

## 6. Exact degree408

Only the projection summand of Z has changed. Kquad has degree9, so
the new summand P mu^2 Kquad has degree17. It does not change the
degree27 leading form of Z0=Z-MV, which is still

    -H0 q0^4 q0^3 W0 Bt0.

Thus omega=s-w has degree102 and the same nonzero leading form
omega0=2Q0 Z00 M0 V00 as in old Section8, at beta>0. The other degrees
are s116,u78,v84,w116. In the centered expression w=s-omega,

    s-sigma1=omega-u-v,

so its square has degree at most204, sigma2 at most200, and
sigma3*s at most394. Therefore the new norm has degree at most408,
with unique leading part omega0^4. This is nonzero: omega0 is the
same nonzero product of leading forms proved in the frozen endpoint.
The exact degree is408, while the uncentered syntactic bound is464.
Full sparse-ring norm/centered expansions and actual-tuple line controls
are retained separately; finite lines are not used to prove the upper
bound.
