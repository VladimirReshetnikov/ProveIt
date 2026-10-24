# Equal-weight extraction from the zero-offset Pell kernel

Research note, 24 October 2026. The statements below are elementary ordinary
mathematics; no Lean/Rocq formalization or global minimality is claimed.

## 1. A square-gap identity

For integers x >= 2 and t >= 1 define

    Delta = t(x+1)(t(x+1)+2),
    v = t^2 x,
    D = x t(x+1)(t(x+1)+2)(t^2 x+1).

Then Delta*v*(v+1) = t^2 D and D is not a square, even in Q.

Indeed put m=floor(x/2) and h=t^2*x*(x+1)+t*x+m. If x=2m, direct expansion gives

    D-h^2 = m[2t^2 + 4(m+1)t - m] > 0,
    (h+1)^2-D = 2m(4m+1)t^2 - 4m^2*t + (m+1)^2 > 0.

Here m>=1, and the second expression is at least
`(4m^2+2m)t+(m+1)^2`, using t^2>=t. If x=2m+1, direct expansion gives

    D-h^2 = t^2*x*(x+2) + 2t*x*(m+2) - m^2 > 0,
    (h+1)^2-D = [t*x-(m+1)]^2 > 0.

Here x>=3 and m>=1, so tx>=2m+1>m+1. The first expression is positive
already after replacing t by1. Thus h^2<D<(h+1)^2 in both cases.
An integer that is a rational square is an integer square: reduce the
rational square root to lowest terms. This proves the claim. The exceptional
case x=t=1 gives D=16; it is outside the claimed domain.

Consequently the equation

    Delta*I^2 = v(v+1)*k^2

has no solution with nonzero integer I,k. Multiplying by Delta would make
D=[Delta*I/(tk)]^2, contrary to the lemma.

## 2. An elementary rationality lemma for three radicals

Let a,b,c be positive rational numbers, pairwise distinct, and suppose

    (a+b-c)^2 != 4ab.

If a signed sum u+v+w is rational, where u^2=a,v^2=b,w^2=c, then u,v,w
are all rational.

Proof. Write s=u+v+w. If s=0, squaring w=-u-v twice gives the prohibited
identity. Thus s is nonzero. For K_a=s^2+a-b-c, squaring
`2vw=K_a-2su` gives

    4s*K_a*u = K_a^2 + 4s^2*a - 4bc.

At least one of K_a,K_b,K_c is nonzero because equality of all three
to zero would give a=b=c. Applying the corresponding identity proves
that at least one root is rational. The sum r of the other two is then
rational and nonzero (otherwise their squares coincide). For example,
`v=(r^2+b-c)/(2r)` and w=r-v. This proves the lemma without any assumption
about independence of quadratic field extensions.

## 3. Uniform separation of the three Pell radicands

Let x>=2,t>=1, and let an integer modulus mu>3 divide t. Use Delta,v from
Section1. Let I,k be positive integers with I>=k and let V be a nonzero
integer. Set

    d_tau = 1+v(v+1)k^2,
    d_f = 1+Delta I^2,
    Q = Delta^2 I^2,
    delta = Q-1,
    Dnum = Q V^2-1,
    d_y = Dnum/delta.

All three d values are positive. In particular Delta>v+1>1, Q>1 and
V^2>=1. They are pairwise distinct:

1. d_tau=d_f would give Delta I^2=v(v+1)k^2, prohibited by Section1.
2. d_tau=d_y would give

       Q(d_tau-V^2)=d_tau-1.

   But d_tau-V^2 is an integer and

       0 < d_tau-1=v(v+1)k^2 < Delta^2 I^2=Q,

   using Delta>v+1 and I>=k. This is impossible.
3. d_f=d_y would give

       d_f-V^2=(d_f-1)/Q=1/Delta,

   contradicting integrality of its left side and Delta>1.

Finally the triangle identity is impossible. Clearing its denominator
would give

    [delta(d_tau+d_f)-Dnum]^2 - 4delta^2*d_tau*d_f = 0.

Because mu divides t, modulo mu we have

    Delta=v=Q=0, delta=Dnum=-1, d_tau=d_f=1.

The displayed integer is therefore -3 modulo mu, whereas mu>3.
Applying Section2 proves:

> Every rational signed sum of the three unweighted positive square roots
> sqrt(d_tau), sqrt(d_f), sqrt(d_y) makes all three roots rational.

The first two are automatically integers. The inherited adjacent-Pell
descent lemma supplies integrality of the third in the actual kernel;
that descent is not replaced or weakened here.

## 4. Application to the accepted ten-positive zero-offset kernel

Take the literal complete99-operation source at ProveIt commit
84e16e43092614bae262ca59651cb9d77e31a255:

    Computability/DiophantineConsistency/candidates/ten-positive-zero-offset/

Its positive inputs satisfy

    q=beta*J+1>=32, X=wq>=32, mu=q^2+1>3,
    t=muY, A=t(X+1)+1,
    Delta=A^2-1, V0=t^2X,
    k=eta+zeta>=2, c=kY+eta>k,
    I=i*c^2>=c^2>k,
    V=Df*b-c, b=c(T+alpha)-R, Df=1+Delta I^2.

Thus Section3 applies with x=X and v=V0. V is nonzero before any
equation: b is integral, and Df>2c, so b<=0 gives V<=-c and b>=1 gives
V>=Df-c>c. The positivity and all-index hypotheses therefore hold on
the entire supplied positive domain, before transport, parity, rank
recovery or any use of the target equation.

For the standard radical polynomial

    F8(s;a,b,c) = [(s+c-a-b)^2-4(sc+ab)]^2 - 64scab,

replace the old equation

    F8(delta Z^2; 9delta M^2 Dtau, delta M^2 Df, M^2 Dnum)=0

by

    F8(delta Z^2; delta M^2 Dtau, delta M^2 Df, M^2 Dnum)=0.     (NEW)

Since delta,M are positive, the radical factorization of F8 says that
NEW makes Z/M a signed sum of the three unweighted roots. Section3
therefore supplies exactly the rational roots needed by the retained
descent and folding proof. No formal independence of radicals is assumed.

### Soundness

After rationality and adjacent descent, the original proof restores
integer tau,f,y and then the original Pell indices. Its transport bound
`3tau+f<HI` is stronger than the new bound `tau+f<HI`. All normalized
center equations change only by replacing the signed term3tau by tau.
Every subsequent rank, parity, index, whole-product projection and
half-binomial step has exactly the same hypotheses, and its conclusions
are unchanged. The retained source reconstruction gives a finite ZFC
refutation with the same coherent coefficient tuple.

### Completeness

Use the canonical source witnesses constructed in the parent's
zero-offset completeness proof, rather than claiming a pointwise inverse
for every weighted zero. With its notation, choose

    n = W*t_transport + rho + tau + f + u - s - kappa,
    s=Y/q^3>=1, rho=(k-R-1)/mu^2>=1,
    u=y-V>0, kappa=Kpos/H>0.

Every term is integral. The parent proves tau>k>Y>=s and f>kappa;
hence n>0. The normalized center is tau+f+y, making one factor of NEW
zero. Thus every finite refutation gives a positive zero.

The equivalence uses the two existence directions above. No pointwise
positive inverse between arbitrary weighted and unweighted zero tuples
is asserted.

### Literal operations and degree

Delete the single row `Dtau9 = 9*Dtau` and redirect
`fa=dM2*Dtau9` to `fa=dM2*Dtau`. This gives98 live binary operations:
58 multiplications,23 additions,17 subtractions. It changes the polynomial;
the proof establishes equivalence of positive solvability, not polynomial
identity or equality of the zero sets at unchanged inputs.

Here is a complete polynomial identity controlling the change. Abbreviate

    s=delta*Z^2, a=delta*M^2*Dtau, b=delta*M^2*Df,
    c=M^2*Dnum, d=s-c,
    E_w=d^2-2(s+c)(w*a+b)+(w*a-b)^2,
    P_w=E_w^2-64w*s*c*a*b.

Then, identically in the polynomial ring,

    E_9-E_1=16a[5a-(s+b+c)],
    P_9-P_1=16a[5a-(s+b+c)](E_9+E_1)-512scab.       (DIFF)

The exact centering identity, with Z=M*V+Z0, is

    d=delta*Z0^2+2delta*M*V*Z0+M^2*(1-V^2).

The source degrees of (a,b,s,c,d) are (74,76,104,104,92). The unique
leading part of d is d0=2Q0*M0*V0_aux*Z00, which is nonzero; thus E_w
has unique highest part d0^2 of degree184 for w=1 or9. In DIFF the
first product has degree362 and leading part -64a0*c0*d0^2, while the
last term has degree358. Here s0=c0 and all a0,c0,d0 are nonzero.
Thus P_9-P_1 has exact degree362, proving that the two polynomials are
different for the actual positive fixed beta as well as in the universal
four-port family. Both have exact degree368 and the same leading part
d0^4. Written explicitly, that part is:

    omega0^4,
    omega0=2^7*q0^46*i^5*w^10*Y^19*(eta+zeta)^10
           *(q0-F-alpha)*(q0-F), q0=beta*J.

The selected coefficient remains2^28*beta^184 at
J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4. The literal centered-identity
and degree checks should accompany publication; this note records the
unbounded mathematical proof, not a replacement for those finite checks.

## 5. Direct-base companion

The source

    candidates/ten-positive-direct-zero-offset/

uses X=q+x>q>=32 and the same zero-offset A=muY(X+1)+1. No step of
Sections1--3 uses q|X, so the same rationality theorem applies before
the direct carrier recovers q divisibility. Its signed-center inequality
`3tau+f+X/q^4<HI` again implies the required unweighted bound. The same
late-q-divisibility, whole-product projection and source reconstruction
remain valid. Completeness transfers from the fresh unweighted98 source
with the parent's exact direct-carrier map

    x=X-q,
    n_direct=n98+(q-1)^2*L*t_transport+X/q^4>0.

The source numerator still scales by q and the common denominator by q,
so all four norm arguments scale by q^2 and the scalar output by q^8.
This gives104 live operations (62 multiplications,24 additions,18
subtractions) and unchanged exact degree340. Its leading form is the
parent's omega0^4, where

    omega0=2^7*q0^39*X0^9*i^5*Y^19*(eta+zeta)^10*B0*(q0-F),
    X0=q0+x, B0=(q0*K0+X0)*(q0-F-alpha)-q0*F.

In this direct source the degrees of (a,b,s,c,d) are
(68,70,96,96,85). Hence E_w has exact degree170 and DIFF has exact
degree334 with the same nonzero leading expression -64a0*c0*d0^2.
The scalar norm degree340 and its full leading component are unchanged.

Both results retain all ten strictly positive unknowns and the complete
fixed coefficient recipe. They neither use a new uncalibrated verifier
nor claim to solve consistency or global Diophantine minimality.

## 6. The auxiliary index gap removes two further operations

This section combines a further ordinary argument with Sections1--5. It
gives96 operations at exact degree360 in the scaled coordinate X=wq,
and102 operations at exact degree332 in the direct coordinate X=q+x.
The98/368 and104/340 equations remain as independently checked proof
stages. All four circuits are supplied.

The change is to use the already computed positive auxiliary parameter b
itself as the transport majorant:

    scaled: W = 1+(q-1)b,
    direct: W = 1+q(q-1)b.

Delete the rows HI=H*I and L=HI+b and redirect the final multiplication
to the existing b register. The product H*I remains a proof abbreviation;
it is not a paid evaluator row in either final circuit.

### 6.1 Chronology and the fifth-index gap

Assume a positive zero of the new circuit. Equal-weight extraction from
Sections1--3 applies to every rational center and is unchanged. The
retained adjacent-coefficient descent and strong/auxiliary folding give
positive integral tau,f,y and c=psi_A(p) for a positive odd index p.
The first Pell classification and its n0=1 exclusion give the same
c>8Xmu^2Y^2. The parent's pretransport mask estimate gives
R<c*alpha/4. Thus, with T,alpha>=1,

    b=c(T+alpha)-R > c(T+3alpha/4)>c.

None of these conclusions uses transport positivity, q parity, the
identity p=R, or q divisibility in the direct-coordinate construction.

Since c>=3 and psi_A(1)=1, the odd index p is at least3. Hence

    c>=psi_A(3)=4A^2-1=4Delta+3.

Put S=Delta*I, so Q=S^2. The integer auxiliary equation is

    (S*V)^2-(S^2-1)*y^2=1.

Here V=Df*b-c>0 and S>=2. Positive Pell classification gives
S*V=chi_S(v) for a positive index v. The recurrence modulo S gives
chi_S(v)=0 modulo S only for odd v, so v is odd. Further,

    V=Df*b-c > (Df-1)c=Delta*I^2*c>4Q.

The possibilities v=1 and v=3 respectively have

    chi_S(1)/S=1,
    chi_S(3)/S=4Q-3.

Both are excluded. Consequently v>=5, and monotonicity of positive
Pell traces gives

    V>=chi_S(5)/S=16Q^2-20Q+5>8Q^2.                  (GAP)

The last inequality holds for Q>=3; here Q is much larger. This is an
unbounded Pell-index argument, not a conclusion from finite testing.

### 6.2 The short transport majorant

All following inequalities hold before transport. Since A>4,
Delta=A^2-1 and H=4A-5 satisfy Delta-H=(A-2)^2>0. Also

    Df=1+Delta*I^2<Q,
    Q-1>2Df,
    b=(V+c)/Df>8Q>2HI.

For example Q-1-2Df=Delta(Delta-2)I^2-3>0, and Q>HI follows
from Delta>H, I>=1 and Delta I>1. These inequalities require no
interpretation of any previously unpaid majorant.

The auxiliary norm implies y>V>1 and

    y-V=(V^2-1)/[(Q-1)(y+V)]
        < V/[2(Q-1)] < Df*b/[2(Q-1)] < b/4.

For e=k-R-1 we need only an upper bound, not an absolute-value bound:

    b-e=c(T+alpha)-k+1>0,
    e/mu^2 < b/mu^2 < b/4.

The retained first/strong-root bound gives tau+f<HI<b/2 in the
scaled construction, and tau+f+X/q^4<HI<b/2 in the direct one.
It follows that the complete non-transport positive upper bound for n
is strictly below b.

In the scaled construction let Bt=(K0+w)C-F. If Bt<=-1, then

    W*Bt/(q-1) <= -b-1/(q-1)<-b.

The signed-center equation, with Kpos/H and Y/q^3 positive, would give
n<0. Thus Bt>=0 and C>0. In the direct construction the same argument
uses B=(qK0+X)C-qF and W*B/[q(q-1)]<-b when B<=-1. The extra
positive term X/q^4 is already included in the strict b/2 bound above.

After transport positivity the old rank, parity, coprimality, projection,
half-binomial and source-reconstruction arguments proceed unchanged. In
particular W is still1 modulo q-1, and direct W is still1 modulo
q(q-1). This proves soundness for the complete same fixed tuple.

### 6.3 Fresh positive completeness

Starting from a finite refutation, construct the same canonical kernel
witnesses as in Section4. Their auxiliary b is positive and their
transport quotient t_transport is nonnegative. Define the shorter W
above and take

    n=W*t_transport+rho+tau+f+(y-V)-s-kappa.

Here rho>=1, tau>Y>=s, f>kappa and y-V>0, so n>0 independently of
how much W has decreased. The normalized center is tau+f+y and the
unweighted norm vanishes. This is a fresh canonical existence map;
subtracting the old majorant contribution from an arbitrary old n is
not asserted to preserve positivity.

For the direct companion, the same exact map as in Section5 applies
between the two short-majorant circuits:

    x=X-q>0,
    n_direct=n_scaled+(q-1)^2*b*t_transport+X/q^4>0.

Their common kernel is unchanged, their numerators and denominators
scale by q, and the norm output scales by q^8. Thus a finite
refutation also produces a positive zero of the102-operation equation.

### 6.4 Exact degrees: the leading term changes

One must not infer the new degree merely from d^4. Reusing b lowers
the degree of Z0 to19 in both coordinate systems. The front degrees
of (a,b_norm,s,c_norm,d) in Section4's norm notation are now

    scaled: (74,76,104,104,86),
    direct: (68,70,96,96,80).

The symbol b_norm in this display means delta*M^2*Df, not the
auxiliary parameter b. In the centered norm bracket the leading term is
now -4*c_norm,0*b_norm,0, since the term d^2 has smaller degree.
The full scalar output therefore has leading part

    16*c_norm,0^2*b_norm,0^2.

For the scaled source this is

    2^20*q0^184*w^36*i^20*Y^76*(eta+zeta)^40*(q0-F)^4,
    q0=beta*J,

of degree360. Its monomial
J^184*w^36*i^20*Y^76*eta^40*F^4 has coefficient2^20*beta^184>0.
For the direct source the leading part is

    2^20*q0^156*(q0+x)^36*i^20*Y^76*(eta+zeta)^40*(q0-F)^4,

of degree332. Its monomial
J^156*x^36*i^20*Y^76*eta^40*F^4 has coefficient2^20*beta^156>0.
The complete sparse leading polynomials of each front register are
checked against these formulas in verify.py; the huge full polynomial
does not have to be expanded to establish the degree.

Restoring weight9 at this same shortened majorant changes the polynomial
by exact degree358 in the scaled source and330 in the direct source.
The identity DIFF remains valid. Its two highest contributions combine
as (+256-512)*a0*c0^2*b0=-256*a0*c0^2*b0, which is nonzero.
The pinned99/368 and105/340 parents have higher degree than these new
96/360 and102/332 outputs, so the final polynomials are also certainly
different from those original parents.

### 6.5 Counts and status

| Circuit | Positive unknowns | Binary operations | Multiplications/additions/subtractions | Exact degree |
|---|---:|---:|---:|---:|
| equal-weight proof stage | 10 | 98 | 58/23/17 | 368 |
| direct equal-weight proof stage | 10 | 104 | 62/24/18 | 340 |
| auxiliary-index gap, scaled | 10 | 96 | 57/22/17 | 360 |
| auxiliary-index gap, direct | 10 | 102 | 61/23/18 | 332 |

The new local proofs are complete ordinary proofs conditional only on
the explicitly retained parent Pell/source/calibration lemmas. The full
fixed coefficient bytes are supplied and authenticated. No independent
proof of consistency, global minimality, new native calibration or new
end-to-end proof-assistant certificate is claimed.
