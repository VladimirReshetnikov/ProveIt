# The86 candidate accepts every input on the actual compiler's parity class

This successor to the [fixed scalar negative family](complete75_weakened86_full_negative_family.md)
removes the special width and mask choices. The theorem concerns the
unchanged86=48M+38A polynomial, its19 strictly positive supplied coordinates,
and its degree203. It does not modify the established75 certificate or
the [sound87 polynomial](complete75_normalized_strong87.md).

Fix positive integers d,b,DC,DR,MC,MF with d odd and not divisible by3,
b odd, MC even, and B=2^d. No other mask hypothesis is needed below.
For every positive input x, the86 polynomial has infinitely many full
positive zeros with R<0 and negative input Pell root. All actual modified
helical compiler constants satisfy these parity conditions: d and b are
powers of5 and MC=2 modulo4. Thus the weakened polynomial accepts every
positive input on every such compiled program slice. Its proposed
universal soundness fails for every compiled language omitting an input.

The construction uses Dirichlet's theorem on primes in a coprime arithmetic
progression, and irrational rotation. It proves existence and gives an
effective exact search recipe; no enormous compiler numeral, prime or full
witness tuple is claimed to have been materialized. The
[checker](complete75_weakened86_all_input_collapse.py) and
[receipt](complete75_weakened86_all_input_collapse.json) audit the finite
identities and the literal source, separately from these existence theorems.

## 1. Outer data and an even wrap lemma

Choose N to be a sufficiently large power of5 that, with D=dN and q=B^N,

    q>2dx+2, q>=16, M=q^2-1=3m, 3 not dividing m.

The last fact follows from v3(4^D-1)=1+v3(D)=1. Set

    Jrep=(q-1)/(B-1), F=2, alpha=q-2-2dx, zplus=1, C=0,
    K=q(q-2)M+(MC+q(MF+B-1))Jrep, u=2dx+b.             (1)

All supplied outer coordinates are positive. K is even, u is odd and
u>=3. The transport factor is exactly-1, independently of DC and DR.

We need signs epsilon,t,omega,sigma in{1,-1} and an even integer j_wrap
such that

    0<j_wrap<2M,
    j_wrap=omega+t(M*sigma-K-2epsilon) modulo3M.        (2)

Here j_wrap is a wrap coefficient, not the supplied auxiliary coordinate j.
The quantity on the right is even. Therefore its even representatives
form one residue class modulo6M.

For epsilon=-1, let r=M-K+3. Choices of the other three signs include
r,r-2M,-r and-r+2M modulo6M: take t=omega=1 and either sigma, then
negate both t and omega. If r is not a multiple of2M, at least one of
these residues lies strictly between0 and2M. Indeed, if r and r-2M
both avoid that interval, one lies between4M and6M, whose negative lies
in the desired interval. If r is a multiple of2M, change epsilon to+1;
the new r is r-4, which is not a multiple of2M because M>=3. This proves
(2) for every even K. In particular j_wrap<=2M-2.

## 2. Choose X and a coprime prime progression for Y

Choose an integer e satisfying

    e=t modulo18M, e=t modulo D, e=3 modulo4, e>=3D.   (3)

These conditions are compatible: D is odd, the first two residues agree,
and lcm(18M,D) has exactly one factor2. One may increase e along the
resulting arithmetic progression. Then e is odd, 3 does not divide e,
gcd(e,D)=1, and

    X=2^e, gcd(X+1,M)=3, v3(X+1)=1.                 (4)

For the gcd assertion, any common divisor of2^e+1 and2^(2D)-1 divides
2^gcd(2e,2D)-1=3, and both numbers are divisible by3. The valuation
assertion follows from the odd-exponent identity
v3(2^e+1)=1+v3(e). Hence q^3 divides X.

We will choose Y=q^3*s so that

    A=Y(X+1)+2=-1 modulo M,
    H=4A-5=3*ell, ell prime, ell=2 modulo3, ell>3M.  (5)

Put Cprime=4q^3(X+1)/3. The coefficient q^3(X+1)/3 is a unit modulo m.
Choose s0 modulo m with

    [q^3(X+1)/3]*s0=-1 modulo m.

For s=s0+m*z, the number ell=Cprime*s+1 is congruent to-3 modulo m.
Its progression has coprime first term and difference: its first term
is1 modulo every prime dividing Cprime, and is coprime to m since
3 does not divide m. Also Cprime*m is a unit modulo3. Restrict z to
one residue modulo3 to impose ell=2 modulo3. The resulting progression
still has coprime first term and difference.

By [Dirichlet's theorem](https://arxiv.org/abs/0808.1408v2), this progression
contains arbitrarily large primes. Choose one large enough that s>=1,
ell>3M, and A>M. Equations(5) follow. In particular

    A=5 modulo9, a=A-2=Y(X+1), Delta=A^2-1,
    E=XY, P=2XY^2+1, H=4a+3.                       (6)

This use of Dirichlet's theorem is explicit; a finite search cutoff or
probable-prime test is not being used as an existence proof.

## 3. Exact periods and the negative input root

Write chi_A(r)+psi_A(r)*sqrt(Delta)=(A+sqrt(Delta))^r. The following
identities hold:

    (chi_A(2M),psi_A(2M))=(1,0) modulo M,
    (chi_A(18),psi_A(18))=(1,0) modulo9,
    (chi_A(ell-1),psi_A(ell-1))=(1,0) modulo ell.    (7)

The first uses A=-1 and Delta=0 modulo M. The second is a direct
recurrence at A=5 modulo9. For the third, A=5/4 and Delta=9/16 modulo
ell, so the two eigenvalues are2 and1/2; Fermat's theorem applies.
Consequently

    L=12M(ell-1)

is a Pell-state return period modulo MH=9m*ell, by CRT, and is divisible
by4. It is also a return period for2 modulo H. Since ell>3M,

    gcd(L,MH)=3M.                                    (8)

Moreover(3),(7) imply

    c_e=psi_A(e)=t modulo3M.                         (9)

Modulo M, oddness gives psi_A(e)=e=t. Modulo9, e=t modulo18 and the
second return identity give psi_A(e)=t. Their lcm is3M.

Choose a fixed input Pell index v according to the sign sigma in(2):

    sigma=-1: v=u;        sigma=+1: v=A*u.

The first index is odd; the second is even because A is even. In both
cases psi_A(v)=u modulo Delta: odd indices give psi_A(v)=v, while even
indices give psi_A(v)=A*v modulo Delta and A^2=1 modulo Delta. Thus

    kappa=psi_A(v), chi_v=chi_A(v),
    delta=(kappa-u)/Delta>0, Fv=chi_v+a*kappa.          (10)

All are fixed after choosing X,Y. Since a=0 modulo3 and A=-1 modulo3,
Fv=sigma modulo3. This is the only property of Fv used in(2).

## 4. A main-index progression paying all congruences

For p=e+Lz the Pell state c=psi_A(p) is constant modulo MH. Define

    Numerator=K+2epsilon-omega*p+j_wrap*c-M*Fv,
    rho=Numerator/(MH), Z=rho*H+Fv,
    R=K-MZ=omega*p-j_wrap*c-2epsilon.                 (11)

At z=0, the numerator is divisible by3M, by(2),(3),(9),(10).
Changing z changes it by-omega*L modulo MH. Equation(8) therefore
solves Numerator=0 modulo MH by one linear congruence in z, with
solutions modulo ell. Choose a nonnegative solution z0 and put

    p_base=e+L*z0, S0=L*ell.

All p=p_base+S0*r satisfy the integral-rho condition and p=3 modulo4.
Because 2^L=1 modulo H, they also satisfy2^p=X modulo H. The recurrence
for chi_A(p)-a*psi_A(p), modulo H, has initial values1,2 and coefficient
2A=5/2; hence this expression equals2^p modulo H. Therefore

    gamma=(chi_A(p)-a*c-X)/H                          (12)

is an integer.

Let T_E be any Pell-state return period modulo E. Such a positive
period exists: the multiplication matrix has determinant1 and is
invertible over the finite ring. Replace S0 by

    S=lcm(S0,E,T_E).

This freezes p and c modulo E while preserving all preceding conditions.
Set lambda=-epsilon and fix n0 modulo E/2 by

    2n0=lambda+omega*p_base-j_wrap*psi_A(p_base) modulo E. (13)

The right side is even because j_wrap is even and p_base and lambda
are odd. Since P=1 modulo E, every n=n0 modulo E/2 satisfies
k=2psi_P(n)=2n modulo E. Thus

    h=(k-omega*p+j_wrap*c-lambda)/E                  (14)

is integral and the actual first-index factor k-hE-R equals epsilon.
The auxiliary target is R+epsilon-lambda=omega*p-j_wrap*c.

## 5. Positivity and infinitely many strict-ratio hits

Restrict to a sufficiently large tail of the p progression. The fixed
constants in(10) are finite, and c grows faster than p. We may require

    c>p+M*Fv+K+M*X+2, c>2M.                         (15)

Since2<=j_wrap<=2M-2, equations(11),(15) imply Numerator>0 and R<0.
Also psi_A(p-1)<c/(2A-1), so A>M gives

    M*gamma*H=M*(2c-psi_A(p-1)-X)>(2M-1)c-MX
                 > Numerator.

Thus rho and sigma_coord=gamma-rho are positive integers. Here
sigma_coord is the supplied coordinate named sigma, not the sign in(2).
Z is positive, and the literal input root is

    C-Z+a*kappa+rho*H=-chi_v<0.

The numerator in(14) is positive for this tail, so h is positive whenever
the first index n is positive.

For the ratios put lambda_A=A+sqrt(A^2-1), lambda_P=P+sqrt(P^2-1),

    theta=log(lambda_A)/log(lambda_P),
    beta=log(sqrt(P^2-1)/(2Y*sqrt(A^2-1)))/log(lambda_P),
    h_ratio=log((Y+1)/Y)/log(lambda_P), N0=E/2.

We have A<P<2A^2-1, so1/2<theta<1. The square classes of their
discriminants differ: Delta is odd, whereas
v2(P^2-1)=e+2v2(Y)+2 is odd. Thus the two quadratic fields differ and
theta is irrational, by the [outer-family argument](complete75_weakened86_infinite_outer_family.md).

Along p=p_base+S*r, irrational rotation modulo N0 makes
p*theta+beta enter

    (n0+h_ratio/3,n0+2*h_ratio/3) modulo N0

infinitely often, including arbitrarily late hits satisfying(15). For
each hit let n=floor(p*theta+beta). It satisfies(13); n/p tends to theta,
so n<p<2n eventually. The exact conjugate-error estimate of the outer
theorem, with epsilon0=1/[12(Y+1)], proves

    kY<c<k(Y+1), k=2psi_P(n).

This argument uses arbitrary fixed positive Y, not its being a power of2.
Set eta=c-kY, zeta=k(Y+1)-c and
tau_gap=chi_P(n)-XY^2*k=psi_P(n)-psi_P(n-1). They are positive integers.
The odd gaps2n-p are unbounded.

## 6. Complete positive coordinates and the literal polynomial

The [positive auxiliary lift](complete75_weakened86_auxiliary_sign_lift.md)
allows either omega since p=3 modulo4. One explicit choice is

    m_aux=p*c, f=chi_A(m_aux), t_strong=psi_A(m_aux),
    i=t_strong/c^2, T=Delta*t_strong,
    ell_aux=p                 if omega=+1,
    ell_aux=p+2*m_aux         if omega=-1,
    V=chi_T(ell_aux)/T, y_aux=psi_T(ell_aux),
    o=(V+c)/f, j=(V+omega*p-j_wrap*c)/c.             (16)

The cited quotient congruences make every value integral. Positivity
needs no further search: c>2p, c>2M, T>=c^2 and ell_aux>=3 give
V>=4c^4-3>2Mc+p, hence j>0. The other four values are positive.

Equations(1),(10)--(16), w=X/q^3 and s=Y/q^3 specify all19 supplied
coordinates. In literal source order the factors are

    (1,1,1,1,epsilon,-1,1,-epsilon).

Their product is1, and the final polynomial is zero. In particular,
computed C=0 and the negative input root do not violate the supplied
positive domain: C and the input root are computed expressions, not
members of the19 supplied coordinates. This distinction is the point
where the weakened source differs from its sound87 parent.

## 7. Verification scope and compiler consequence

The checker proves symbolic identities for the unchanged full source,
tests the even-wrap covering and the CRT/period formulas, and includes
a small modular host with a recursively checked Lucas primality
certificate. That host tests the number-theoretic mechanism; it is
explicitly not a full candidate zero or an actual compiler instance.
No finite audit replaces Dirichlet's theorem, irrational rotation, or
the parametric positive-lift proof.

Actual modified compiler constants have d,b powers of5 and MC even.
They therefore satisfy the theorem for every positive input x, regardless
of their large masks or machine coefficients. Realizing the old d4,b1 toy
masks is unnecessary. Applying the theorem to a compiled rejecting
program supplies a false-input zero; more generally any compiled proper
subset of the positive integers loses soundness under this weakening.

Author receipt generation and a fresh default replay pass. The finite
receipt includes12 symbolic complete eight-factor/output identities,
192 rational output identities (96 signed),12,672 exhaustive even-K
wrap cases (192 boundary cases),20 width/sign records,68 input-index
checks and204 modular progression checks. Its63-bit host prime is
certified by60 recursively verified Lucas-certificate nodes.

Two independent full proof/source reviews and fresh default replays pass,
with no findings. Franklin's separate companion-matrix oracle checked200
input/main/first progressions,4,479 wrap cases at seven additional odd
moduli, and256 independently executed full-output identities (128 signed).
Native's own companion-matrix oracle checked256 progressions and68 extra
width/sign cases, independently verified the recursive prime certificate,
and checked256 complete eight-factor/output identities (128 signed) with
its own literal executor and manual coordinate formulas. Both reviews
checked the parametric existence and positivity arguments, rather than
inferring them from finite fixtures. Native also checked the actual
compiler's power-of-five widths and even modified mask in its source.
The source and receipt are frozen after these reviews.
