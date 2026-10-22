# Independent audit of the twelve-positive-variable four-root construction

Audit date: 22 October 2026. This is an ordinary mathematical proof audit,
not a new proof-assistant certificate. The conclusion is conditional on the
same authentic fixed compiler coefficients and imported compiler/Pell
theorems as the existing thirteen-variable construction.

## Verdict

The proposed twelve-variable system is sound. Its Galois separation and
rational-denominator arguments are valid, including nongeneric cases where
the square roots generate a field of degree less than four.

The proposed completeness index `m=2cRH` is not justified and is false as a
general Pell divisibility assertion. Replace it by an index divisible by
`2cR` and the order of the Pell unit modulo `Hc^2`. This repairs completeness
without changing any supplied variable, polynomial, or arithmetic circuit.
With that repair, the system has a positive solution exactly when the
existing normalized fifteen-variable system has one.

The conclusion concerns the three-equation system and its sum of squares.
No claim about a cheaper product of integer-unit factors is needed here.

## 1. The literal system

Retain the eleven positive coordinates

    J, F, alpha, z, h, j, T, s, w, eta, zeta,

and add one positive coordinate `t`. Thus there are twelve supplied
positive-integer unknowns. In the old normalized system replace `i` by
the computed expression `Hj`; there is no additional supplied `i`.

Use the fixed coefficients `beta, K0, MC, MF`, with the authentic shifted
MF convention, and the common polynomials

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    C=q-F-alpha,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)C+q-F-z(q-1).

Define the following computed expressions, not new witnesses:

    L=E(kY), A1=1+L(L+k), A2=1+Delta c^2,
    i=Hj, D=1+Delta i^2 c^4,
    Q=Delta(D-1)=(Delta i c^2)^2, d=Q-1,
    v=cT, b=c+RD, S=Dv^2+b^2,
    e=QS-1, B=2Qvb,
    W=2(S+1),
    K=1+H(2W+1), M=1+2K A2+2H W,
    Z=Ht+K(X+ac), u=HM.

Here `K` is the new separation weight, not the fixed coefficient `K0`.
For formal quadratic roots r and sigma put

    F(r,sigma)=[d(Z-u r-K sigma)^2-H^2 e]^2-H^4 B^2 D.

The polynomial Res12 is the product of F over the four independent formal
sign choices `r=+/-sqrt(A1)`, `sigma=+/-sqrt(A2)`. It is an integer-coefficient
polynomial in the supplied unknowns: equivalently multiply in the free
rank-four algebra with `r^2=A1`, `sigma^2=A2`; sign invariance leaves only
the constant basis coefficient. This also supplies a denominator-free
finite algorithm to write the polynomial.

The three equations are

    Nk=1, Nt=1, Res12=0.

Their sum of squared residuals is one integer-coefficient polynomial with
exactly the same positive zero set. This audit does not assert a degree or
operation count without the separately emitted literal circuit.

## 2. Elementary positivity and bounds before any Pell classification

Every geometric quantity q,X,Y,E,k,c,a,H,Delta is positive. The equation
Nt=1 forces C>0, since

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0

and K0+w is positive. The authentic positive mask coefficients then give
R>0. Consequently v,b,B are strictly positive. Also D>1, Q>2, d>0,
A1>1, A2>1, and W,K,M are positive. In particular no division below uses
a possibly zero denominator. The stronger pre-Pell packing bounds needed
by the imported signed compiler theorem are unchanged from that theorem.

## 3. A zero of the resultant gives algebraic roots

The specialized product is a product of four real numbers. If it is zero,
choose signs giving real numbers r,sigma with

    r^2=A1, sigma^2=A2, F(r,sigma)=0.

Let Lfield=Q(r,sigma), a totally real multiquadratic Galois extension of Q,
possibly of degree one or two. Put

    y=(Z-HM r-K sigma)/H,
    f=(e-dy^2)/B.

Then `f,y` belong to Lfield, and F=0 gives `f^2=D`. Moreover

    dy^2=e-Bf.

For every Q-automorphism g of Lfield, write y'=g(y), f'=g(f). All the
coefficients in this identity are rational integers, so

    d(y')^2=e-Bf',  f'=+/-sqrt(D).

Every y' is real because Lfield is totally real. Since v,b>0,

    2vb sqrt(D)<=Dv^2+b^2=S,
    d(y')^2<=e+B sqrt(D)<=2QS-1<2QS.

As Q/(Q-1)<2, this gives `(y')^2<4S`, and hence

    |y'|<2sqrt(S)<2(S+1)=W.

This uniform bound applies to every actual field conjugate. It does not
assert that every independently chosen formal sign pair is a field
automorphism, which would be false when the two radicals are dependent.

## 4. The weights force both square roots to be rational

The defining identity for y is

    Z=HM r+K sigma+H y.

If a Q-automorphism g changed the sign of r, subtraction of its conjugate
identity would give

    2HM |r| <= 2K sqrt(A2)+2H W.

But |r|>1 and

    HM >= M > K sqrt(A2)+H W,

using H>=1, A2>=1, and the displayed definition of M. This is a strict
contradiction. Thus every automorphism fixes r, so r is rational and,
because r^2 is an integer, r is an integer.

Now suppose an automorphism changed the sign of sigma. It already fixes
r, so subtraction gives

    2K sqrt(A2)<=2H W.

This contradicts `K>2H W` and `sqrt(A2)>1`. Therefore every automorphism
also fixes sigma. Hence sigma is rational and is an integer.

This argument uses only the fixed-field theorem for a finite Galois
extension and remains valid when A1, A2, or their product is a square.
There is no irreducibility or genericity assumption.

It follows that y is rational, and then f is rational. As `f^2=D` is an
integer, f is an integer as well. These integers need not initially have
positive signs; the signed-core theorem below is exactly what is needed.

## 5. The denominator step restores integral gamma and y

Since r and sigma are integers, the formula for y shows its reduced
denominator divides H. The equation `dy^2=e-Bf` has an integer right side,
so the square of that reduced denominator divides d. But `i=Hj` gives

    Q=Delta^2 H^2 j^2 c^4,  d=Q-1=-1 (mod H),

and therefore gcd(H,d)=1. Hence y is an integer.

Set

    gamma=(sigma-X-ac)/H.

The exact defining identity rearranges to

    t=Mr+K gamma+y.

Thus K gamma is an integer. The reduced denominator of gamma divides H,
whereas `K=1 (mod H)` gives gcd(K,H)=1. Consequently gamma is an integer.

Equivalently, once y is integral the equation for Z gives
`K(sigma-X-ac)=0 (mod H)`, and K is invertible modulo H. This proves the
same conclusion without referring to a reduced denominator for gamma.

## 6. Exact restoration of the normalized source equations

Take `tau=r` and `Dmain=sigma`. Then

    tau^2=1+L(L+k),
    Dmain=X+ac+gamma H,  Dmain^2-Delta c^2=1,
    f^2-Delta i^2 c^4=1.

Furthermore, with

    V=vf-b=c(Tf-1)-Rf^2,

the equality `f^2=D` yields

    e-Bf=Q(Dv^2+b^2-2vbf)-1=QV^2-1.

Thus `Q V^2-(Q-1)y^2=1`, exactly the original normalized auxiliary norm,
and `Q=Delta(f^2-1)=(Delta i c^2)^2`. The index and transport equations
were retained unchanged.

The precise signed-domain theorem required here is Sections 1-5 of
`diophantine_zfc_round2/integers/SIGNED_DOMAIN_PROOF.md`: only
J,F,alpha,z,i,s,w,eta,zeta need be positive; f,h,T,tau,y,gamma may be
arbitrary integers. In the present construction h and T happen still to
be positive. That proof explicitly handles a signed main root and gamma,
rather than invoking the all-positive theorem on an inadmissible tuple.
Its domain extension therefore proves soundness for the authentic fixed
compiler. The coefficient transfer preserves its prerequisites, including
the shifted-mask convention and low-bit invariants.

## 7. The suggested completeness index needs correction

It is not generally true that

    c=psi_A(R), H=4(A-2)+3  ==>  Hc^2 divides psi_A(2cRH).

For example choose a=2, A=4, Delta=15, H=11, R=3 and c=psi_4(3)=63.
Then m=2cRH=4158, and exact recurrence modulo 11 gives

    chi_4(m)=9 (mod 11), psi_4(m)=3 (mod 11).

Thus not even H divides psi_4(m). This is a counterexample to that
unrestricted divisibility assertion, not an authentic accepting packed
core and not a counterexample to the final twelve-variable construction.
The old binomial proof supplies c^2 divisibility at index 2cR, but merely
multiplying the index by H does not supply the missing H factor when H
has primes that do not divide that starting lower Pell coefficient.

## 8. Repaired completeness by a finite Pell period

Start with an original all-positive normalized solution, or an accepting
computation and its original completeness witnesses. Keep the exterior
core q,R,X,Y,k,c,a,Dmain,tau,gamma unchanged. The source theorem gives

    A=a+2, Delta=A^2-1,
    c=psi_A(R), Dmain=chi_A(R), R=3 (mod 4).

The last congruence is a completeness-side native-mask invariant, not an
assumption used in the new soundness proof. Its derivation is recorded
in Section 5 of `diophantine_zfc_round2/pell/START_ONLY14_PROOF.md`; the
new coefficient recipe retains MC=2 (mod 4).

Let N=Hc^2. In the finite ring

    (Z/NZ)[xi]/(xi^2-Delta),

the element alpha=A+xi is a unit with inverse A-xi. Its order e0 is finite
and at most N^2, because the ring has N^2 elements. Choose

    m=2cR e0.

Then alpha^m=1 in this ring, so

    chi_A(m)=1 (mod N), psi_A(m)=0 (mod N).

In particular `i_new=psi_A(m)/c^2` is a positive integer divisible by H.
Put `j=i_new/H`, a positive integer. If an explicit index avoiding an
order notation is preferred, use

    m=2cR*(N^2)!.

Since the positive integer e0 is at most N^2, it divides (N^2)!, so this
choice has the same property. The index and its factorial are proof-only
choices of an existential witness; they add no term to the polynomial.

Now regenerate the auxiliary witnesses by

    f=chi_A(m), rho=Delta psi_A(m),
    y=psi_rho(R), V=chi_rho(R)/rho,
    o=(V+c)/f, T=(o+Rf)/c.

These divisions are integral and positive as follows. Since R is odd,
write R=2u0+1. The standard integer polynomial Q_u0 satisfies

    chi_Z(R)=Z Q_u0(Z^2),
    Q_u0(-Delta)=(-1)^u0 psi_A(R),
    Q_u0(0)=(-1)^u0 R.

Here u0 is odd because R=3 (mod 4). The identity
`rho^2=Delta(f^2-1)` therefore implies

    V=-c (mod f), V=-R (mod c).

The first congruence makes o a positive integer. Also f^2=1 (mod c),
so gcd(f,c)=1, and

    f(o+Rf)=V+c+Rf^2=0 (mod c).

Hence T is a positive integer. The defining identity is precisely
`V=c(Tf-1)-Rf^2`, and Pell's equation at base rho gives

    rho^2 V^2-(rho^2-1)y^2=1.

The regenerated f,i_new,T,y thus satisfy the source normalized strong
and auxiliary equations, now with `i_new=Hj` as required.

Finally compute all the new polynomial weights from these regenerated
witnesses and put

    t=K gamma+M tau+y.

It is a positive integer. With r=tau and sigma=Dmain, the equation
`Z=HM r+K sigma+H y` and the restored auxiliary norm give F=0. Thus the
resultant vanishes and all three equations of the twelve-variable
system hold.

## 9. Scope of the conclusion

After the completeness correction, both directions are rigorous relative
to the inherited normalized signed-core and authentic compiler theorems.
The construction gives an explicit twelve-positive-variable polynomial
by sum of squares. Its lack of positive solutions has exactly the same
ZFC-provable equivalence to Con(ZFC) as the source construction. It does
not prove Con(ZFC), certify the imported machine/compiler proofs anew,
or establish a global minimum for the number of variables.
