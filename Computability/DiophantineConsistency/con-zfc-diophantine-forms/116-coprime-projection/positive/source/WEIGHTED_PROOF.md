# A fixed root weight replaces the strong lower-bound shift

This ordinary arithmetic construction has ten strictly positive integer
unknowns. It retains the entire four-port compact44 tuple and all front
definitions of the frozen102-operation degree388 endpoint, with only

    I=i*c^2,
    F8(delta*Z^2;9*delta*M^2*Dtau,delta*M^2*Df,M^2*Dnum)=0.    (1)

The literal evaluator has102 operations and exact degree368. The extra
root weight replaces the old unconditional bound I>=mu*c^2. No extra
prime is inserted into the Pell parameter or carrier denominator.
The previous endpoint, all pages and all Lean files remain unchanged.
This is an ordinary unbounded proof, not a new Lean or encoded object-ZFC
derivation, a proof of consistency, or an optimality claim.

## 1. Complete equation and parameter conventions

The only independent coordinates are

    J,F,alpha,i,T,w,Y,n,eta,zeta in Z_{>0}.

With the coherent fixed tuple satisfying

    beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta,

put

    q=beta*J+1, X=w*q, k=eta+zeta, c=k*Y+eta, a=XY+Y,
    mu=q^2+1, A=mu*(a+2)+1, Delta=A^2-1, H=4A-5,
    V0=X*mu^2*Y^2, Dtau=V0*(V0+1)*k^2+1,
    G=(q-1)*(q-F)+alpha,
    R=G*(q^2-1)+(MC+q*MF)*J, e=k-R-1,
    C=q-F-alpha, Bt=(K0+w)*C-F,
    I=i*c^2, Df=1+Delta*I^2, Q=Delta^2*I^2, delta=Q-1,
    b=c*(T+alpha)-R, V=Df*b-c, Dnum=Q*V^2-1,
    L=H*I+b, W=1+(q-1)*L,
    P=q^3*(q-1), M=P*mu^2*H,
    Kquad=X*(X+2*(A-2)*c)-1,
    Z=P*mu^2*[H*(n+V)+Kquad]
          +H*[mu^2*((q-1)*Y-q^3*W*Bt)-P*e].

For any s,u,v,w define

    F8(s;u,v,w)=[(s+w-u-v)^2-4*(s*w+u*v)]^2-64*s*w*u*v.

Equation(1) is a polynomial with only fixed integer coefficients and
binary arithmetic operations; radicals and divisions below are proof
abbreviations. The page convention A_page=A-1 is not used in this proof.
The authentic original tuple and separately calibrated whole BFS tuple
both satisfy the box. Their different K0 values are not identified.

The retained center identity is

    Z/M=n+V+Kquad/H+Y/q^3-W*Bt/(q-1)-e/mu^2.                 (2)

The independent eight-conjugate identity shows that(1) is equivalent to

    Z/M=epsilon1*3*tau+epsilon2*f+epsilon3*y,               (3)

where tau=sqrt(Dtau), f=sqrt(Df), y=sqrt(Dnum/delta), with three signs.
The prefactor is delta^4*M^8>0. Positivity is justified next, before
rationality or integrality of any root is assumed.

## 2. Positivity and a finite-modulus noncancellation lemma

At every positive input, q>=32, mu>=1025, A>4, c>=3 and I>=c^2>=9.
The old elementary bounds that do not require I>=mu*c^2 remain valid:

    Q-1>c^2-1>0, Df>c+2, Df<Q-1.

If b=0 then V=-c and c<y<c+1. Otherwise |V|>=Df-c>1,
|V|<y<2|V|. Thus all three radicands are positive rationals.
The adjacent-coefficient descent and Pell facts in the retained proofs
are used with these same hypotheses.

Here is the replacement for every superincreasing-root argument. Modulo
mu the definitions give

    Dtau=1, Df=1, delta=-1, Dnum=-1.                         (4)

In particular delta is a unit modulo mu. Multiplying the three real
roots3*tau,f,y by sqrt(delta) gives positive roots whose integer
squares are

    U=9*delta*Dtau, V2=delta*Df, W2=Dnum,
    (U,V2,W2)=(-9,-1,-1) modulo mu.                         (5)

A signed zero subsum with one term is impossible by positivity. A signed
zero pair3*tau=+/-f or3*tau=+/-y would make the corresponding squares
equal, so mu would divide8. This is impossible since mu>=1025. The one
remaining pair f=+/-y is impossible independently of the modulus: its
squared equality Df=Dnum/delta would give

    Q*(V^2-Df)=1-Df=-Delta*I^2,
    V^2-Df=-1/Delta,

using Q=Delta^2*I^2 and I>0. The left side is an integer, whereas
Delta>1 makes the right side a noninteger rational. This argument does
not assume that either root already is rational.

A signed zero sum of all three roots would imply

    F8(0;U,V2,W2)=0.

The polynomial is homogeneous of degree4 in its squared-root arguments.
By(5), reducing modulo mu gives

    mu | F8(0;9,1,1)=2025=3^4*5^2.                           (6)

But q^2+1 is coprime to3, since the square residues modulo3 are0,1.
Consequently(6) would imply mu|25, again impossible. This proves that no nonempty
signed subsum of3*tau,f,y vanishes. It holds before q parity, source
soundness, divisibility of e or any Pell classification. It does not
assume a selected prime divisor of mu or appeal to sampled roots.

The rational signed-sum character lemma now applied to(3) makes all
three roots rational. Their integer squares make tau and f integers;
adjacent-coefficient descent makes y an integer as well. Thus the three
ordinary positive Pell equations are recovered without the full-mu
strong lower bound.

## 3. Main folding first, then the weighted transport bound

Since I>=c, c^2|I, and V=Df*b-c=-c modulo f, the retained all-index
strong/auxiliary folding lemma gives

    c=psi_A(p), p>=1 and odd.

The strong equation is f^2-Delta*I^2=1. Its auxiliary parameter is
S=Delta*I, and S^2*V^2-(S^2-1)*y^2=1. All hypotheses, including
2I<f and c<=I, hold without mu|I or I>=mu*c^2. The folding uses both
signs of V, and its signed-period/reflection reduction preserves the
odd auxiliary index. No q parity or carrier integrality is used.

The first Pell equation gives

    k=2*psi_(2V0+1)(n0), tau=chi_(2V0+1)(n0), n0>=1.

As before n0=1 would give k=2,c=2Y+1 strictly between psi_A(1) and
psi_A(2). Hence n0>=2 and

    c>kY>=k>=4*(2V0+1)>8*X*mu^2*Y^2>8*mu.                (7)

This late bound restores precisely the needed transport inequality;
there is no claim that it forces the input i to be at least mu.
Indeed tau<(V0+1)k<2*X*mu^2*Y*c, using k<c/Y. Since I>=c^2,

    4*tau<8*X*mu^2*Y*c
           <mu*X*Y*c^2<(A-1)*I.

Also I>1 gives the sharper exact bound f<A*I, since
f^2=A^2*I^2-I^2+1<A^2*I^2. Therefore

    3*tau+f<(2*A-1)*I<(4*A-5)*I=H*I.                    (8)

The last inequality uses A>2. The weight introduces no unresolved
hierarchy premise; (8) is proved after root extraction and main folding.

The unconditional mask estimate is R<q^4+(alpha+2)q^2. By(7),

    R<c*alpha/4.

Exactly as in the frozen short-transport proof, b>0 and |e|<b:
if R>=0 then R<c(T+alpha)/4, so b>3c(T+alpha)/4 and both
k-1,R+1<b; if R<0 then e=k+|R|-1>0 and b-e=c(T+alpha)-k+1>0.
Thus the still rational rho=e/mu^2 satisfies |rho|<b/2. Also
V>0 and0<y-V<b/2 by the adjacent radicand identity and Df<Q-1.

Subtract n+V from(3), and set only rational s0=Y/q^3>0,
t=Bt/(q-1), kappa=Kquad/H>0 for now. The exact relation is

    n=epsilon1*3*tau+epsilon2*f+(epsilon3*y-V)
           -kappa-s0+W*t+rho.                              (9)

If Bt<=-1 then L=HI+b>0,W>0 and W*t<-L. Equations(8),(9) give

    n<3*tau+f+(y-V)+|rho|-L<HI+b-L=0,

contradiction. Thus Bt>=0, C>0 and the unchanged mask bounds give

    3q<R<q^4-2.

The normalized strong rank and signed auxiliary-index lemmas now give
p=R, because c^2|I, c>2R, c>2p and the two fixed-minus residues hold.
Neither this step nor(7)--(9) used q even or mu^2|e.

## 4. Deferred parity, whole-product projection and source restoration

Odd p makes R odd. If q were odd, beta odd would make J even;
q^2-1 and J even would make R even. Thus q is even and J odd.
Only now use the coprimality

    gcd(mu^2,q^3*(q-1)*H)=1.

Subtract the integer signed-root side of(3) in(2) and apply the retained
partial-fraction lemma to obtain mu^2|e. The unchanged first Pell
congruence and bound P'=2V0+1>A give n0=(R+1)/2. Write R=2r+1,
so r>=48. Ratio bounds apply with the unchanged scaling lambda=mu:

    Y>X^r/3, X^(r+1)<3a<H.

Multiplying the integral weighted signed relation by q^3(q-1) gives
H|q^3(q-1)*Kquad. The integer coefficient3 does not change this
integrality conclusion. The projection identity yields

    H | q^3(q-1)*(X-2^R)*(2^R*X+1).

For X>=q>=32 and r>=30, the old strict whole-product bound is

    |q^3(q-1)*(X-2^R)*(2^R*X+1)|
        <q^4*2^(2R+2)*X^2<X^(r+1)<H.

It forces X=2^R, without cancelling a possibly nonunit factor of H.
Consequently H|Kquad, q^3|Y and q-1|Bt, by the same explicit partial
fractions as before. The fixed-minus parity lemma gives R=3 mod4;
the ratio rounding recovers the same half-binomial Y. These statements
are independent of the relative order of tau,f,y. The strong rank uses
c^2|I and f>2c only, both retained. The carrier denominator still is
q^3(q-1)*mu^2*H, not a multiple modified by a new prime.

Finally construct the fresh unscaled positive source61 coordinates
from J,F,alpha,w,R,X,Y and these divisibilities, exactly as in the
retained ORIGINAL_PROOF Section6.18. They have their own strong
ordinate psi_(a+2)(R*c_o), divided by c_o^2. They do not divide the
current I by mu or reuse the current i. The actual positive-J source
theorem yields a finite syntactic refutation even when J=1; no old
j=(J-1)/2 witness is inserted. The uniform whole-BFS native theorem is
used for that tuple, not an identity between its K0 and the original K0.
This proves soundness in the required order.

## 5. Canonical completeness with explicit positive maps

A finite refutation supplies the canonical zero of the frozen102/388
endpoint, with its three positive integral roots tau,f,y and all-positive
center Z_old/M=tau+f+y. Keep every old positive coordinate except put

    i_new=i_old+q^2,
    n_new=n_old+2*tau.

Both are strictly positive integers. The new strong ordinate is
I_new=(i_old+q^2)c^2=I_old, so all Pell radicands, R,b,V,L,W,M and the
projection term are unchanged. The center changes by exactly2*tau,
and is therefore3*tau+f+y. The all-positive weighted factor of(1)
vanishes. This is a constructive completeness map from the canonical
old witnesses; no approximation or sign choice is required.

Conversely a new positive zero yields a finite refutation by Sections2--4,
and hence the old canonical witnesses. No pointwise inverse
old_i=i_new-q^2 is asserted to be positive. The two endpoints are
related by positive zero existence, not equality of their polynomials
or a bijection of all positive zero sets. Their inherited ordinary
no-positive-zero/Con(ZFC) equivalence is consequently the same.

## 6. Exact degree368 and complete literal scope

All ten variables have degree1; the fixed ports have degree0. The new
front degrees are

    I5,Df20,Q30,V24,L10,W11,M13,Z37.

Write Z=M*V+Z0. The unique leading Z0 term is the transport term,
of degree25. The four squared-root arguments have degrees104,74,76,104.
The constant9 does not alter these degrees. With s=delta*Z^2 and
w=M^2*Dnum, the centered difference is

    omega=s-w=delta*Z0^2+2*delta*Z0*M*V-M^2*(V^2-1).

Its unique leading degree92 part is omega0=2Q0*Z00*M0*V00.
In the independent centered octic, omega^4 uniquely has weight368;
all competing first-square terms have degree at most180 versus184,
and the last product has degree358<368. Thus the polynomial degree
is at most368.

For an attained coefficient put

    q0=beta*J, c0=(eta+zeta)*Y, a0=q0*w*Y,
    A0=q0^2*a0, I0=i*c0^2,
    R0=q0^3*(q0-F), Bt0=w*(q0-F-alpha), H0=4A0,
    Q0=A0^4*I0^2, V00=-A0^2*I0^2*R0,
    W0=q0*H0*I0, Z00=-H0*q0^7*W0*Bt0, M0=H0*q0^8.

Their exact product is

    omega0=2^7*q0^46*i^5*w^10*Y^19*(eta+zeta)^10
                      *(q0-F-alpha)*(q0-F).

Selecting alpha^4,F^4,eta^40 in omega0^4 gives

    [J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4]P
        =2^28*beta^184>0.

The exponents sum to368. The weight does not affect this leading form,
since the weighted smaller radicand does not contribute at weight368.
The other three fixed ports do not occur in this coefficient.

The literal102-operation schedule and complete cut certificate delete
only the private old shift addition, replace I by i*c^2, and multiply
the first norm radicand by9. Every other parent definition,
including all13 tail gates, is retained. Independent complete norm,
modulus, degree, topology and four-port checks accompany this ordinary
proof. Finite controls are transcription checks, not substitutes for
any of the unbounded arguments above.
