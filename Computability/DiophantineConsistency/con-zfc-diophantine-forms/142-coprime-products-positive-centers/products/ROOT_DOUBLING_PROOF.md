# Thirteen positive variables: 72 operations, exact degree 465

This note independently verifies the doubled-pair composition proposed in
this session. Pell doubling and coprime product-square finalizers are inherited
mechanisms, notably from package 133. The present application retains P66's
low-cost outer arithmetic and avoids its three independent root variables.
It improves the degree of this session's three-anchor 72/521 construction
without increasing its operation count. The triple-anchor graph is therefore
not part of the recommended delivery.

The full literal circuit is `equation_13_doubled.json`. Its fixed ports are
the coherent indexed943/radix67 P66 values `beta,K0,MC,MF` pinned by the
retained binding and payloads. The graph has 41 multiplications, 19 additions,
and 12 subtractions, with every gate, input and fixed port live.

## Complete polynomial

The thirteen quantified coordinates are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t > 0.

Use all the common outer polynomial abbreviations in PROOF.md. In particular

    A=1+ell*(ell+k),
    Delta=(a+2)^2-1,
    N1=D^2-Delta*c^2,
    Nk=k-h*E-R,
    Nt=(K0+w)*(q-F-alpha)+(q-F)-z*(q-1).

Now define the following abbreviations, not new variables:

    U=i*c^2,
    b=Delta*U^2*A,
    F0=1+b,
    G=A*F0,
    f2=1+4*b*F0=(1+2*b)^2,
    Q=4*Delta*b*F0,
    V=f2*(c*T-R)-c,
    Eprod=Q*(t^2-G*V^2)-t^2+G.

The equation is

    N1*Nk*Nt*(3*Eprod+1)-1=0.                (D13)

The graph calls b `aa`, f2 `f2`, and the final integer factor `Eunit`.
In particular f2 is computed by polynomial operations alone. It is not an
existentially supplied square root or an exponentiation with variable exponent.

## Coprime product extraction

Since all coordinates are positive, A>1, Delta>0, U>0, b>0, F0>1, G>0,
and Q>1. The exact identities

    gcd(A,F0)=1,
    Q=4*Delta^2*U^2*G

imply

    gcd(G,Q-1)=gcd(G,Q*V^2-1)=1.             (1)

At any zero of (D13), each factor is an integer unit. The factor
3*Eprod+1 cannot be -1 because it is 1 modulo 3. The factor N1 cannot
be -1 because Delta is 0 or 3 modulo 4, so N1 modulo 4 is a square or a
sum of two squares. Consequently

    N1=1, Eprod=0, Nk*Nt=1.                  (2)

Writing B=Q-1 and Caux=Q*V^2-1, the folded residual gives

    B*t^2=G*Caux.                           (3)

By (1), for every prime p dividing G, valuation in (3) yields
2*v_p(t)=v_p(G). Hence G=g^2 for an integer g>0, and g divides t.
Set y=t/g>0. Equation (3) gives

    Q*V^2-(Q-1)*y^2=1.                      (4)

Also G=A*F0 with gcd(A,F0)=1, so both factors are squares:

    A=tau^2, F0=f0^2,
    tau>0, f0>0, g=tau*f0.                  (5)

The two prime-valuation applications are valid for all positive integers,
not just for squarefree moduli. No conjecture or density statement about
Pell solutions occurs in the extraction.

## Exact recovery of a positive P66 zero

Define the proof-only integral coordinates

    f=1+2*b,
    i_old=2*i*g,
    S_old=Delta*i_old*c^2.

Since U=i*c^2 and G=A*(1+b),

    f^2-1=4*b*(1+b)=4*Delta*U^2*G
         =Delta*i_old^2*c^4,
    S_old^2=4*Delta^2*U^2*G=Q.              (6)

Thus f2 in the new polynomial is exactly f^2, and its V is exactly the
parent V=f^2*(c*T-R)-c. By (4), (5) and (6), the first, main, auxiliary,
and normalized strong P66 factors are all 1. The two remaining factors
have product 1 by (2). Reintroducing positive tau,f,y and replacing i by
i_old therefore gives a positive zero of the precise parent P66 equation.

This implication uses no choice of canonical witnesses, no presumption
that V>0, and no division by a symbolic polynomial. The latter positivity
is a conclusion of the existing parent soundness argument when needed.

## Canonical completeness by a seed Pell pair and doubling

A finite syntactic refutation gives canonical outer P66 witnesses, including

    A=tau^2,
    c=psi_(a+2)(R), R=3 mod4,
    N1=Nk=Nt=1.

It also supplies an initial normalized strong pair. The finite matrix-period
argument in PROOF.md allows this pair to be replaced by positive f0,j with

    f0^2=1+Delta*j^2*c^4,
    tau | j.

For example, apply the argument with modulus tau. Set i=j/tau>0. With
U=i*c^2, the displayed definition of b gives

    b=Delta*U^2*A=Delta*j^2*c^4=f0^2-1,
    F0=f0^2, G=tau^2*f0^2.

The doubled strong pair is

    f=2*f0^2-1=1+2*b,
    i_old=2*j*f0=2*i*tau*f0.

Its normalized strong equation follows by expanding
(2*f0^2-1)^2-1=4*f0^2*(f0^2-1). The squared-modulus completion of the
parent P66 proof now supplies fresh positive T,y for this doubled pair.
The R=3 mod4 hypothesis and the same unscaled main Pell base are retained,
so the parent's completion theorem applies exactly as stated.

Finally set t=tau*f0*y. Then equation (3) holds and Eprod=0. All remaining
factors are +1, proving (D13). This is a canonical existence map from a
refutation; it does not assert that the three removed root coordinates of
an arbitrary old zero satisfy a new divisibility relation.

The two implications, composed with the named inherited P66/native/refutation
calibration, give an ordinary proof formalizable in ZFC of

    (D13 has no strictly positive integer zero)  iff  Con(ZFC).

No consistency assumption is used to prove this biconditional.

## Degree and arithmetic certificate

Using the leading symbols Q0,k0,e0,c0,A0,L_t from PROOF.md, the exact
upper degrees of U,b,F0,G,f2,Q,V,Eprod are respectively

    11,56,56,78,112,124,118,438.

The leaders of b,G,f2,Q,V are respectively

    i^2*A0*e0^2*c0^4,
    i^2*A0^2*e0^2*c0^4,
    4*i^4*A0^2*e0^4*c0^8,
    4*i^4*A0^2*e0^6*c0^8,
    4*i^4*A0^2*e0^4*c0^9*T.

In Eprod, the unique highest-degree contribution is -Q*G*V^2. Its
leader is

    -64*i^14*A0^8*e0^16*c0^30*T^2.

Multiplying by 3*N1*Nk*Nt gives the nonzero degree-465 form

    1536*gamma*h*i^14*A0^8*e0^19*c0^31*T^2*L_t.

In particular the monomial

    J^282*w^35*s^82*eta^47*i^14*T^2*gamma*h*z

has coefficient -1536*beta^282. This is nonzero for the actual fixed
coefficient tuple. It establishes exact degree after specialization,
independently of the numerical degree controls.

The independent verifier checks the complete literal graph against a
separate scalar formula, computes an actual univariate specialization at
the pinned coefficients modulo 1000000007, checks its degree and leading
coefficient, checks every live arithmetic row, and rejects an altered
reachable arithmetic operation. Those finite checks support the delivered
objects; this written argument proves the unbounded existence equivalence.
