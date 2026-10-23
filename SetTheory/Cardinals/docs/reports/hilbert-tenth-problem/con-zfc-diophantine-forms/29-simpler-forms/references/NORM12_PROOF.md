# A twelve-positive-variable Diophantine equation for Con(ZFC)

## Scope and exact input

This note gives a new algebraic reduction of the fixed blank-input K215
compiler interface. It uses one entire certified coefficient tuple
`(beta,K0,MC,MF)`, where beta=B-1 and MF is the shifted high-mask port.
The default instance for this delivery is the complete restricted-T4 tuple
in `../coefficients/COEFFICIENTS.json`. The T4 tuple in package 11 at
repository commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035` remains a
valid complete alternative. The new adapter is proved separately.

The inherited result used below is the **signed normalized blank-interface
theorem**: the six-factor normalized Pell system, with the prescribed
positive coordinates and with signed main/root/auxiliary coordinates as
specified below, encodes exactly the blank halting of K215. Its ordinary
strong-equation version and signed-coordinate proof are in packages 11,
12, and 14. The normalized version reduces to the ordinary version by
`i_ordinary=Delta*i`. Package 09's root-amalgamation proof explicitly proves
the weak index/transport sign recovery needed by the product finalizer.

This is an ordinary mathematical proof, formalizable in ZFC. It is not a
new Lean/Rocq proof and does not establish Con(ZFC).

## 1. Twelve supplied positive integers

The free unknowns are exactly

    J,F,alpha,z,h,i,T,s,w,eta,zeta,r > 0.

Every other letter below is an abbreviation for a polynomial in these
twelve unknowns and the four fixed coefficients.

    q = beta*J+1;
    Cw = q-F-alpha;
    X = w*q;  Y = s*q^3;  E = X*Y;
    k = eta+zeta;  c = k*Y+eta;
    a = E+Y;  H = 4*a+3;  Delta = a^2+H;
    ell = E*k*Y;  A = 1+ell*(ell+k);
    G = 1+Delta*c^2;
    R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J;
    Nk = k-h*E-R;
    Nt = (K0+w)*Cw+q-F-z*(q-1).

The strong and auxiliary quantities are

    D = 1+Delta*i^2*c^4;
    Q = (Delta*i*c^2)^2;  d = Q-1;
    v = c*T;  b = c+R*D;
    e = Q*(D*v^2+b^2)-1;
    Baux = 2*Q*v*b.

The two new weight and parameter expressions are

    Bnd = v^2+D+2*b;
    L = 1+H*Bnd;
    S = X+a*c+H*r.

No numerical value of the astronomical fixed coefficients needs to be
expanded in order to specify this polynomial.

## 2. A finite polynomial norm, not additional quantified roots

Use temporary *formal* indeterminates u and t to write

    F(u,t) = [d*(S-L*u-H*L*t)^2-H^2*e]^2-H^4*Baux^2*D.

For an arbitrary polynomial p(z), reduce it modulo z^2-g to p0+p1*z and
define

    Norm_g(p) = p0^2-g*p1^2.

This is an explicit operation on finite polynomials with integer
coefficients. Define

    N = Norm_G,u( Norm_A,t(F(u,t)) ).

The norm is a polynomial solely in the original twelve supplied integers.
It introduces no existential variables and no non-polynomial operation.
The JSON circuit gives its complete expression as binary +,-,* gates.

Our three-equation presentation is

    Nk = 1,  Nt = 1,  N = 0.                         (S12)

The main single polynomial is

    P12 = Nk*Nt*(1+N)-1.                             (P12)

A conservative sum-of-squares alternative is

    Q12 = (Nk-1)^2+(Nt-1)^2+N^2.                    (Q12)

The theorem is that each of S12, P12=0, and Q12=0 has a positive integer
solution iff K215 halts on its blank tape. Therefore ZFC proves that its
lack of positive integer solutions is equivalent to Con(ZFC).

## 3. Rational auxiliary Pell roots are automatically integral

**Lemma.** Let m>=2 and V be integers. If y is rational and

    m^2*V^2-(m^2-1)*y^2=1,

then y is an integer.

Write y=a/b in lowest terms, b>0. The equation implies b^2 divides
m^2-1. Set D0=(m^2-1)/b^2. This is a positive nonsquare integer: if it
were a square, m^2-1 would be a square, impossible between consecutive
integer squares. We have two positive Pell solutions, after taking
absolute values where necessary,

    m^2-D0*b^2=1,
    (m*|V|)^2-D0*|a|^2=1.

Neither ordinate is zero. Let epsilon=x1+y1*sqrt(D0) be the least positive
integer Pell unit >1. The usual elementary Pell classification gives

    m=chi_j, b=psi_j, m*|V|=chi_l, |a|=psi_l,

where epsilon^n=chi_n+psi_n*sqrt(D0), j,l>=1.

For completeness the needed divisibility fact is

    chi_j divides chi_l  iff  l is an odd multiple of j.

Indeed chi_(2j)=2*chi_j^2-1 and psi_(2j)=2*chi_j*psi_j imply
chi_(n+2j)=-chi_n modulo chi_j. Reflection gives
chi_(2j-n)=-chi_n modulo chi_j. Reduce l modulo 2j and reflect it into
0<=n<=j. For n<j, 0<chi_n<chi_j; the only possible divisible case is
n=j. Thus l=(2h+1)j. The elementary multiplication identities for Pell
units now give psi_j divides psi_l. Therefore b divides a, and their
coprimality forces b=1.

This lemma is essential: the bare assertion that a rational root of
`d*y^2=e-Baux*f` is integral would be false for general d,e. Here the
special Pell shape supplies precisely the missing integrality.

## 4. Coherent roots exist whenever the polynomial norm vanishes

Over an algebraic closure, the defining norm is the product

    product_(u=+-sqrt(G), t=+-sqrt(A), f=+-sqrt(D))
      [d*(S-L*u-H*L*t)^2-H^2*e+H^2*Baux*f].

If N=0, at least one factor vanishes. Choose its coherent triple of roots
u,t,f and put

    y=(S-L*u-H*L*t)/H.

Then

    u^2=G, t^2=A, f^2=D,
    d*y^2=e-Baux*f=Q*(v*f-b)^2-1,                (1)
    S=L*u+H*L*t+H*y.                            (2)

There is no independent choice of incompatible signs here: all four
roots come from one vanishing factor.

## 5. The two separation estimates

For S12 the outer equations give Nk=Nt=1. For P12 the parity argument in
Section 8 first gives N=0 and Nk=Nt in {1,-1}. In either situation the
inherited weak transport bootstrap, valid for Nt=+/-1, gives

    Cw>=0, q>=16, 0<R<q^4-2, E>=q^4>R+2.

These assertions use the exact certified mask and transport constants.
They do not use the main/root equations being reconstructed. In
particular b,v,D,Q,d,Bnd,L,H are positive, D,Q>1, and Q is a square.

Work in a finite normal splitting field containing u,t,f,y. Every field
embedding sends f to +/-sqrt(D). From (1), every conjugate y' satisfies

    |y'|^2 <= [Q*(v*sqrt(D)+b)^2-1]/(Q-1)
            < 2*(v*sqrt(D)+b)^2.

Because v^2+D>=2*v*sqrt(D),

    Bnd=v^2+D+2*b >=2*(v*sqrt(D)+b)>|y'|.       (3)

This also bounds complex conjugates; no unproved total-reality claim is
being used. It follows directly that

    L*sqrt(G)>H*Bnd.                            (4)

The other needed separation is

    H*sqrt(A)-sqrt(G)>1.                        (5)

Here is a short proof independent of asymptotic estimates. We have
sqrt(A)>ell. Since Delta=(a+2)^2-1 and c>1,
sqrt(G)<(a+2)*c. Also c=kY+eta<k(Y+1)<=2kY. Since E,Y>=1 and a>=2,

    H*ell-(a+2)*c
      > kY*(H*E-2*(a+2))
      >= kY*(H-2a-4)
      = kY*(2a-1)>1.

This proves (5), hence, using L=1+H*Bnd,

    H*L*sqrt(A)>L*sqrt(G)+H*Bnd.                 (6)

## 6. Rationality and integrality of the recovered roots

If t were irrational, some automorphism of the splitting field would
send t to -t. Apply it to (2) and subtract. The left side remains S.
The magnitude of the changed t term is exactly 2HL*sqrt(A). The other
two changed terms have total magnitude at most

    2L*sqrt(G)+2H*Bnd,

strictly smaller by (6). Contradiction. Thus t is rational and hence
integral because t^2=A is an integer.

If u were irrational, some automorphism would send it to -u while fixing
the now rational t. Subtracting (2) would yield

    2L*sqrt(G)<=2H*Bnd,

contradicting (4). Thus u is rational and integral.

Equation (2) now makes y rational. Since Baux>0, equation (1) gives

    f=(e-d*y^2)/Baux,

so f is rational and hence integral because f^2=D is an integer. Finally,
V=v*f-b is an integer and Q=m^2 with m=Delta*i*c^2>=2. Equation (1) is
exactly the lemma of Section 3; therefore y is an integer too.

The role of the Pell integrality lemma cannot be replaced by congruence
alone: (2) initially yields only H*y integral.

## 7. Restore the omitted main coordinate and apply the compiler

As L=1+H*Bnd, reducing (2) modulo H gives

    u = S = X+a*c modulo H.

Thus

    gamma=(u-X-a*c)/H

is an integer. No positivity claim about gamma is needed; the inherited
signed-domain theorem permits it. The restored quantities satisfy

    t^2-ell*(ell+k)=1;
    (X+a*c+gamma*H)^2-Delta*c^2=1;
    f^2-Delta*i^2*c^4=1;
    Q*((c*(T*f-1)-R*f^2)^2-y^2)+y^2=1.

The auxiliary identity uses f^2=D and b=c+RD, so
v*f-b=c*(T*f-1)-R*f^2 exactly. These are the first, main, normalized
strong, and auxiliary factors of the inherited blank compiler. The
coordinate conversion i_ordinary=Delta*i produces its ordinary strong
equation without changing Q.

For S12, Nk=Nt=1; for P12, the inherited signed-rank argument applies
with their common unit sign and forces both to +1. It is the same
weak-sign extension already used by package 09's thirteen-variable
product. The signed ordinary interface therefore recovers a blank K215
halting computation in either case.

Conversely, take a canonical positive normalized blank-compiler witness.
Write its main root as u=X+a*c+gamma*H and its first root as t>0. Define

    r=gamma+Bnd*u+L*t+y.

This is a positive integer. It gives S=L*u+HL*t+H*y exactly. The chosen
roots make a factor in the displayed norm product vanish, so N=0.
The canonical index and transport factors are 1, proving completeness
simultaneously for S12, P12, and Q12.

## 8. Why the shorter product finalizer is sound

The emitted pair-ring computation writes the inner norm as N0+N1*u with
N1 divisible by 8 as an integer polynomial. Consequently

    N=N0^2-G*N1^2 = N0^2 modulo 64,

and, in particular, 1+N cannot be -1 modulo 4.

For an explicit parity verification, put x=S+L*u. Then
x^2=V0+V1*u with V1=2SL even. The inner formula after eliminating t is

    [(C^2+K-Z)^2-4*C^2*K],
    C=d*(x^2+H^2*L^2*A)-H^2*e,
    K=4*d^2*H^2*L^2*A*x^2,
    Z=H^4*Baux^2*D.

The odd coefficient of C is even, that of C^2 is divisible by 4,
and that of K is divisible by 8. Thus the odd coefficient of C^2+K-Z
is divisible by 4, that of its square is divisible by 8, and that of
4*C^2*K is divisible by 8. This proves the assertion about N1.

The emitted evaluator uses the identical polynomial

    (C^2-K-Z)^2-4*K*Z

to save six gates: Z is scalar, so multiplying the coefficient pair for K
by Z is cheaper than multiplying two general coefficient pairs. The
parity proof and all root semantics concern the same polynomial.

If P12=0, its three integer factors Nk,Nt,1+N are units. The last factor
cannot be -1, so it is 1, N=0, and Nk=Nt are equal unit signs. This is
exactly the weak-sign situation handled in Sections 5-7.

## 9. Exact degree and literal circuit cost

All fixed coefficients have degree zero. Key exact degrees are

    c=5, a=H=6, Delta=12, R=4, ell=11, A=G=22,
    Q=46, D=34, v=6, b=Bnd=38, L=44, S=11.

In the emitted pair-ring evaluator, a0=H^2 L^2 A has degree 122;
V0 has degree 110; V1 degree 55. Therefore C0 has degree 168 from its
unique highest term d*a0, whereas C1 has degree 101. N0 has degree 672
with leading term C0_top^4, and N1 has degree at most 605. Thus

    deg(N)=1344,

since N0^2 has degree 1344 and G*N1^2 has degree at most 1232.

For a completely explicit uniform certificate set q0=beta*J and
k0=eta+zeta. The leading form is

    N_top=2^80*i^48*k0^112*w^112*s^224*q0^832*(q0-F)^16.

It is nonzero for every beta>0. The product P12 has exact degree
1344+7+2=1353. Its leading form is

    -2^80*h*i^48*k0^112*w^113*s^225*q0^836*(q0-F)^16
      *[w*(q0-F-alpha)-z*q0].

For example, the coefficient of

    J^853*h*z*i^48*eta^112*w^113*s^225

is +2^80*beta^853, which is nonzero. The sum-of-squares polynomial has
exact degree 2688, because N^2 is its unique highest-degree summand.

The delivered self-contained emitter charges every binary arithmetic
operation, including multiplication by fixed numerals, and checks
liveness of every gate and supplied port:

| Presentation | Variables | Equations | Degree | Operations | Multiplications | Add/subtract |
|---|---:|---:|---:|---:|---:|---:|
| S12 | 12 positive | 3 | max 1344 | 112 | 71 | 41 |
| P12 | 12 positive | 1 | 1353 | 116 | 73 | 43 |
| Q12 | 12 positive | 1 | 2688 | 119 | 74 | 45 |

The accompanying checks compare the norm gate-by-gate against an
independent eight-dimensional multiquadratic conjugate-product evaluator
on 24 signed assignments. They also check the finalizers, parity, liveness,
and leading forms. Such finite checks corroborate the algebra and ledger;
the proofs above, not these tests, establish semantic equivalence.

This improves the reviewed explicit family from thirteen to twelve
positive variables. It trades increased degree and arithmetic size for
that reduction. It does not supersede the existing 67-operation equation,
the low-degree systems, or classical existence theorems with nine
unknowns, and it makes no global optimality claim.

