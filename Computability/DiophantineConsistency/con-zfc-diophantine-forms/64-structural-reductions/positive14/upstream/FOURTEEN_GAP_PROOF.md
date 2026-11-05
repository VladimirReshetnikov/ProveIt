# A degree-52 equation in fourteen positive unknowns

## Statement and precise comparison

This adapter defines one polynomial in exactly fourteen strictly positive
integer variables, of total degree 52 and arithmetic circuit cost 79.
Its positive solvability is equivalent, by ordinary mathematics formalizable
in ZFC, to the existence of a finite ZFC refutation. The four fixed integer
coefficients are the complete package-31 Wang943 tuple, with the high mask
already shifted. `coefficients/ports.json` and the four materialized gzip
payloads fix them; none is an existential parameter.

The comparison is the incoming wave-7 Support Sensitive package's
fourteen-positive-variable equation, degree 56 and 79 operations. The
new equation decreases its degree by four without increasing its variable
count or evaluator size. It does not improve the nine-positive or
ten-integer variable-count frontier, nor the fewest-operation frontier.
No global optimality or literature-priority claim is made.

The three ingredients are: the incoming fourteen-coordinate quotient
absorber; the positive auxiliary gap from the earlier gap constructions;
and a stronger modulus in the auxiliary quotient. The last saves the gate
otherwise needed by the gap. The minima finalizer is an already established
local device, applied to this combination.

## Explicit formula

The supplied unknowns, all positive, are

    J,F,alpha,z,f,i,T,s,w,tau,eta,zeta,e,gamma.

Write the four fixed ports as beta,K0,MC,MF. Define computed abbreviations

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y, H=4*a+3,
    Delta=a^2+H=(a+2)^2-1, ell=E*k*Y,
    b0=X+a*c, G=1+Delta*c^2,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    U=4*q^4, r=k-R-1,
    Dstar=U*b0+H*(U*gamma-r), M=Dstar^2-U^2*G,
    I=i*c^2, Aaux=Delta*(f^2-1), W=I^2-Aaux,
    V=f^2*(c*T-R)-c, y=V+e,
    Na=Aaux*(V^2-y^2)+y^2,
    N0=tau^2-ell*(ell+k),
    Nt=(K0+w)*C+q-F-z*(q-1).

The equation is

    P = M^2 + W^2 + Na^2 + (N0*Nt-1)^2 - 1 = 0.

`polynomial.json` is a division-free straight-line definition expanding
every abbreviation with exactly 79 binary +, -, or * gates. Squaring is a
multiplication and multiplication by a small numeral is charged.

## 1. The local minimum block

For every positive assignment, Aaux is nonnegative. If f=1 then Aaux=0
and W=I^2>1, so W^2+Na^2>1. If f>=2 then Aaux>1. In this case Na cannot
vanish. Otherwise

    Aaux*V^2=(Aaux-1)*(V+e)^2

would make Aaux*(Aaux-1) the square of a rational number. Neither V nor
V+e can vanish: either would force both to vanish, contrary to e>0.
A rational square root of an integer is integral, but

    (Aaux-1)^2 < Aaux*(Aaux-1) < Aaux^2.

This is impossible. Hence W^2+Na^2>=1. Equality forces W=0 and Na=+1
or -1. When W=0, Aaux=I^2 and

    Na=I^2*V^2-(I^2-1)*y^2.

Modulo four this is a square, so it cannot equal -1. Therefore, tuplewise,

    W^2+Na^2=1  iff  W=0 and Na=1.

It follows that P=0 is exactly the conjunction

    M=0, W=0, Na=1, N0*Nt=1.                 (1)

The consecutive-product negative Pell equation excludes N0=-1: putting
n=XY^2>=2, the equation x^2-n(n+1)t^2=-1 admits the usual descent under
the unit 2n+1-2 sqrt(n(n+1)). Its second coefficient is a strictly smaller
positive integer. Consequently (1) also gives N0=Nt=1.

No compiler or consistency assumption is used by the minimum-block proof.

## 2. Soundness by an explicit map to the incoming fourteen-variable form

At a new zero, set T_old=f*T and y_old=abs(V+e). Then

    V=c*(T_old*f-1)-R*f^2.

Also y_old>0. Indeed y_old=0 in Na=1 would imply Aaux*V^2=1, whereas
W=0 makes Aaux=I^2>1. Thus all fourteen supplied coordinates of the
incoming Support Sensitive construction are positive, and its four
residuals vanish: its main residual and ordinary strong residual are M,W;
its auxiliary residual is Na-1; and its remaining residual is N0*Nt-1.

The complete inherited quotient-absorption argument is retained in
`upstream/FOURTEEN_PROOF.md`. For clarity its proof order is as follows.
Transport gives C>0, q>=16 and 3q<R<q^4-2. The main residual makes
g=Dstar/U an integral positive square root of G. One obtains U|H*r.
For H=4Y(X+1)+3, U=4q^4, gcd(U,H)<=3, hence
mu=U/gcd(U,H)>=4q^4/3>R+1. First-norm classification yields
k=2 psi_(2XY^2+1)(n), and k=2n modulo 4XY^2, a multiple of U.
Thus 2n=R+1 modulo mu, giving n>=25 before strong-rank recovery.

This early lower bound supplies the ordinary strong lemma's essential
hypothesis c>(a+2)*Delta^2. That lemma gives f=chi_(a+2)(m), p|m,
c|m, c^2|f^2-1, and m>2p, where c=psi_(a+2)(p). The auxiliary Pell
congruences give p=R. Since n<p=R, the same modulus now forces exactly
2n=R+1. Hence r is divisible by E and U; the omitted positive quotient
h=r/E and the old positive carrier gamma_old=gamma-r/U are recovered.
The ordinary signed compiler and the calibrated K215 machine then give
a finite ZFC refutation. This order does not assume k>E before h is
reconstructed, nor cancel Delta in the ordinary strong norm.

## 3. The stronger auxiliary congruence and constructive completeness

It remains to prove that requiring T_old to be a multiple of f loses no
canonical witness. This is the substantive new local observation.

Start with a canonical normalized compiler point, whose actual packed
index satisfies R=3 modulo 4. Put A=a+2, Delta=A^2-1, and use the usual
integer Pell sequences chi_A and psi_A. The established converse chooses

    m=2*c*R, f=chi_A(m), I_norm=psi_A(m),
    i_norm=I_norm/c^2, rho=Delta*I_norm,
    V=chi_rho(R)/rho, y=psi_rho(R).

Here c=psi_A(R); i_norm is a positive integer, f^2=1+Delta*I_norm^2,
and all quantities are integral. Set i=Delta*i_norm for the ordinary
strong coordinate, so I=ic^2=rho and Aaux=rho^2.

Write R=2r0+1. The odd quotient polynomial Q_r0 obeys

    chi_z(2r0+1)=z*Q_r0(z^2),
    Q_r0(1-A^2)=(-1)^r0*psi_A(R),
    Q_r0(0)=(-1)^r0*R.

Since R=3 modulo 4, r0 is odd. The exact identity

    rho^2=Delta*(f^2-1)

therefore gives the STRONGER congruence

    V=Q_r0(rho^2) = -c modulo f^2,            (2)

not just modulo f. Also rho is divisible by c^2, so V=-R modulo c,
and f^2=1 modulo c. Consequently, with o=(V+c)/f^2,

    o is a positive integer, o+R=0 modulo c,
    T=(o+R)/c is a positive integer.

This yields exactly V=f^2*(c*T-R)-c. No search, enlargement of an
auxiliary index, extra congruence hypothesis, or new compiler padding is
needed: the canonical point already satisfies (2).

Since R>=3 and rho>1, V>=chi_rho(3)/rho=4rho^2-3>1. The auxiliary
Pell norm gives

    (rho^2-1)*(y^2-V^2)=V^2-1>0,

and y,V are positive. Hence e=y-V is a positive integer. Finally the
incoming quotient-absorption construction replaces its old carrier by
gamma=gamma_old+r/U; r is a positive multiple of U. The remaining
coordinates are unchanged. This supplies a positive zero of the new P.

Combining soundness and completeness proves in ZFC

    (there is no positive zero of P) iff Con(ZFC).

This does not prove either side of that equivalence.

## 4. Exact degree, not just a syntactic bound

All fourteen unknowns have degree one and the fixed ports degree zero.
The main residual has exact degree 26. To see its cancellation, set
D0=b0+H*gamma. Then

    M=U^2*(D0^2-G)-2*U*H*r*D0+H^2*r^2,
    D0^2-G=2*a*c*(X+H*gamma)+(X+H*gamma)^2-H*c^2-1.

The latter has degree 18, and the other two terms in M have degree at
most 25 and 20. With q0=beta*J and k0=eta+zeta, its leading form is

    M_top=128*w^2*s^3*k0*gamma*q0^19.

The strong residual W has degree 22. Although y and V each have degree
eight, the exact gap identity

    Na=V^2-(Aaux-1)*e*(2V+e)

gives degree at most 23. Finally N0*Nt-1 has degree at most 24.
Thus only M^2 reaches degree 52, with nonzero leading form

    P_top=16384*w^4*s^6*(eta+zeta)^2*gamma^2*(beta*J)^38.

This proves degree 52 uniformly for beta!=0. On the full diagonal its
leading coefficient is 65536*beta^38, strictly positive for the authentic
tuple. The independently written checker expands the main residual
exactly, checks the gap identity, audits the full circuit and coefficients,
and replays complete degree-52 univariate polynomials modulo three primes.
Finite checks support the transcription and exact-degree claims; the
unbounded semantic endpoint uses the preserved inherited proofs.

## 5. Scope and further questions

The degree reduction is a modest, concrete frontier improvement. The
larger prospect is to absorb another supplied quotient without losing
the positivity bounds needed before Pell index recovery. For example,
deleting the positive transport quotient immediately loses the proof
that C=q-F-alpha is nonnegative; an unqualified CRT substitution does
not repair that problem. Reducing the absorber from 4q^4 would also
require a new proof for the exceptional factor 3 in gcd(U,H), or a
coherent restriction of the canonical compiler domain. Neither further
reduction is asserted here.
