# Thirteen positive variables: 72 operations, exact degree 433

The complete literal circuit is `equation_13_anchored.json`. All constants
are the coherent indexed943/radix67 P66 ports pinned in this packet. The
circuit has 41 multiplications, 19 additions and 12 subtractions; all gates,
inputs and fixed ports are live.

This construction removes the independent first-root, strong-root, and
auxiliary-root coordinates tau,f,y. The coprime product mechanism has
predecessors in the repository. The present selective construction adds
the main base a+2 and the already-computed main root D as two inexpensive
anchors, and recovers the omitted first square before restoring the
normalized strong equation. It improves this session's intermediate
72/465 doubled-pair construction and 72/521 full-radicand construction.
Those dominated intermediate graphs are not required by this package.

## 1. Complete polynomial

The thirteen unknowns are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t > 0.

Use the common outer abbreviations in PROOF.md, including

    A=1+ell*(ell+k), Delta=(a+2)^2-1,
    N1=D^2-Delta*c^2, Nk=k-h*E-R,
    Nt=(K0+w)*(q-F-alpha)+(q-F)-z*(q-1).

Define only polynomial abbreviations

    a0=a+2,
    m=a0*D*i,
    I=m*c^2,
    W=Delta*A*I^2,
    F2=1+W,
    Q=Delta*W,
    G=A*F2,
    V=F2*(c*T-R)-c,
    Eprod=Q*(t^2-G*V^2)-t^2+G.

The single equation is

    N1*Nk*Nt*(3*Eprod+1)-1=0.                (P13)

F2 is an abbreviation; no square root, rational expression, factorial,
variable exponent, or additional quantified coordinate occurs here.

## 2. Unit extraction and coprimality

At a zero every factor is an integer unit. Since 3*Eprod+1 is 1 modulo 3,
it cannot be -1. Since Delta is 0 or 3 modulo 4, the same norm-residue
argument as for P14 gives N1=1. Therefore

    Eprod=0, N1=1, Nk*Nt=1.

All of A,F2,Q,G are positive and Q>1. Put B=Q-1 and
Caux=Q*V^2-1. The folded polynomial identity gives

    B*t^2=A*F2*Caux.                        (1)

The following coprimalities are the entire extraction argument.

First, A divides Q and F2=1 modulo A. Consequently

    B=Caux=-1 modA,
    gcd(A,F2*B*Caux)=1.                      (2)

Second, Q=Delta*(F2-1), so

    B=Delta*F2-a0^2.                        (3)

As m contains a0, F2=1 modulo a0. Hence gcd(F2,a0)=1 and (3) implies

    gcd(F2,B)=1.                            (4)

Third, V=-c modulo F2 and Q=-Delta modulo F2. Using the already-established
main norm N1=1,

    Caux=-Delta*c^2-1=-D^2 modF2.            (5)

As m contains D, F2=1 modulo D. Thus (5) implies

    gcd(F2,Caux)=1.                         (6)

These deductions do not assume that A,F2 or Q is already a square.
The complete G need not divide Q; separate congruences (2), (4) and (6)
supply precisely the needed coprimality.

## 3. Recovering all three roots

For a prime p dividing A, valuation in (1) and (2) gives
2*v_p(t)=v_p(A). Thus A=tau^2 for a positive integer tau. The same
argument using (2), (4) and (6) shows F2=f^2 for a positive integer f.
In fact f>=2 because F2>1.

Since gcd(A*F2,B)=1 and A*F2=(tau*f)^2, equation (1) implies
(tau*f)|t. Set y=t/(tau*f)>0. Cancelling gives

    Q*V^2-(Q-1)*y^2=1.                      (7)

Now set the parent multiplier to

    i_old=tau*m=tau*(a+2)*D*i.

Then the definitions give

    f^2=1+Delta*i_old^2*c^4,
    Q=(Delta*i_old*c^2)^2.                  (8)

Therefore tau,f,y,i_old and the retained positive coordinates satisfy
the parent first, main, strong and auxiliary norms. The remaining factors
have product 1. This is an exact positive P66 zero and hence, by its
inherited calibration, yields a finite syntactic ZFC refutation.

No early assumption that V>0 is needed. The quotient y is positive since
t,tau,f are positive; the parent's soundness argument establishes any
subsequent sign facts about V. No division by a symbolic polynomial is
performed by the equation itself.

## 4. Completeness and preservation of the canonical rank

A finite refutation supplies canonical P66 outer witnesses, with

    A=tau^2, c=psi_(a+2)(R), R=3 mod4,
    N1=Nk=Nt=1.

Apply the finite matrix-period construction of PROOF.md, Section 4,
with modulus

    M=tau*(a+2)*D.

This produces a normalized strong pair f,j with M dividing j and

    f^2=1+Delta*j^2*c^4.

Set i=j/M>0. Then m=(a+2)*D*i=j/tau, and the new abbreviations give

    W=Delta*j^2*c^4, F2=f^2,
    Q=(Delta*j*c^2)^2, G=(tau*f)^2.

Choose fresh positive auxiliary T,y for this strong pair using Section 4
of the retained parent P66 proof. Its R=3 mod4 condition and unscaled
main base a+2 have been preserved. The resulting V satisfies (7).
Finally take t=tau*f*y. Then (1) holds and Eprod=0. All remaining factors
are +1, proving P13=0.

This direction is an existence construction from the canonical source.
It does not assert that an arbitrary old multiplier is divisible by M,
or that old auxiliary witnesses stay fixed while the pair is powered.

Together with soundness, the argument is formalizable in ZFC and proves

    (P13 has no strictly positive integer zero) iff Con(ZFC).

The equivalence assumes neither consistency nor inconsistency. It composes
with the named ordinary parent/native calibration, not a newly produced
end-to-end Lean/Rocq or encoded object-language proof.

## 5. Exact degree and attained leading coefficient

Using Q0,k0,e0,c0,A0,L_t from PROOF.md, the degrees of m,I,W,F2,Q,V,G,
and Eprod are respectively

    18,28,90,90,102,96,112,406.

The final product adds 18+7+2 degrees, giving 433, not 435. This exact
arithmetic corrects an initial degree-sum estimate caught by the independent
polynomial-degree check before release.

The leading terms are

    m:    i*e0^2*c0,
    W:    i^2*A0*e0^6*c0^6,
    Q:    i^2*A0*e0^8*c0^6,
    V:    i^2*A0*e0^6*c0^7*T,
    G:    i^2*A0^2*e0^6*c0^6,
    Eprod: -i^8*A0^5*e0^26*c0^26*T^2.

Consequently the complete degree-433 leader is

    24*gamma*h*i^8*A0^5*e0^29*c0^27*T^2*L_t.

In particular

    J^268*w^39*s^76*eta^37*i^8*T^2*gamma*h*z

has coefficient -24*beta^268. It is nonzero for the fixed beta>0.
Thus the degree is attained at the actual coefficient tuple and is not
merely a syntactic gate bound.

The independent verifier authenticates those coefficient bytes, compares
this complete graph with a separately written scalar formula, checks an
actual-coefficient modular univariate specialization and its leading term,
checks the parent prefix and all live gates, and rejects a reachable
arithmetic mutation. Those finite checks support the delivered objects;
the unbounded proof is the argument above.
