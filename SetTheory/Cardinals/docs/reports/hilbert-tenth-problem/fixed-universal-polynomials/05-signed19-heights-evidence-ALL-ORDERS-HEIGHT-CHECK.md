# Independent check: all-orders height and inverse-height refinement

3 October 2026. Read-only inputs: `PROOF-PACKET.md` and
`HEIGHT-ASYMPTOTICS-CHECK.md` in this directory. This note changes neither input,
executes no upstream program, and makes no new claim about the counting
function. Parameters are fixed throughout; no uniformity across compiler or
scale choices is asserted.

## Hash-bound supplement verdict

**PASS, with no corrections required.** The complete final
`ALL-ORDERS-SUPPLEMENT.md` was read and checked against the derivation below.
The exact factorization, uniformly convergent coefficient expansion, joint
analytic inverse construction, triangular rational-coefficient recurrence,
and transfer of every fixed-order inverse remainder are valid. The supplement
correctly distinguishes the convergent model from the exact height/cutoff.

This verdict binds specifically to SHA256:

    ALL-ORDERS-SUPPLEMENT.md
    8b31ef158c9ada5b3a26cffd97c25c038a62ff707ee00a28eb24e40fd99b71b5

The frozen input hashes were also checked:

    PROOF-PACKET.md
    ff9d116c90b058be082c2c9d6ee051ccf537d80821c14d10b28aec9a96d5a533
    HEIGHT-ASYMPTOTICS-CHECK.md
    489e7b85b5329f3f40b0343183e61e9aa19fa844fe9d7143a265e51941278407

## 1. Exact factorization and the flat remainder

Write

    d = sqrt(Delta), ell = (1/2) log Delta, epsilon = exp(-alpha p),
    m = p(epsilon^(-1)-epsilon)/(2d),
    A_p = d(1-1/p), B_p = d log Delta/(alpha p),
    F(p) = (2m+p-1)(alpha m+ell), C0 = alpha/(2 Delta).

Direct multiplication, without asymptotic truncation, gives

    2m+p-1 = p/(d epsilon) (1+A_p epsilon-epsilon^2),
    alpha m+ell = alpha p/(2d epsilon) (1+B_p epsilon-epsilon^2),
    F(p) = C0 p^2 epsilon^(-2)
             (1+A_p epsilon-epsilon^2)(1+B_p epsilon-epsilon^2).   (1)

The checked hyperbolic estimate is

    log y = F(p)+O((m+p) exp(-2 alpha m)).

Since F(p) is asymptotic to 2 alpha m^2 and p=o(m), taking its logarithm
proves

    log log y = 2 alpha p+2 log p+log C0
                +log(1+A_p epsilon-epsilon^2)
                +log(1+B_p epsilon-epsilon^2)+r(p),             (2)
    r(p) = O(exp(-2 alpha m)/m).

All logarithms in (2) are real for sufficiently large p. For every fixed
K>0, r(p)=o(epsilon^K): indeed m is asymptotic to
p exp(alpha p)/(2d), and -2 alpha m+K alpha p-log m tends to minus
infinity. Thus the residual is beyond every fixed exponential order in p.

## 2. A uniformly convergent coefficient expansion

For real C define

    S_0(C)=2, S_1(C)=-C,
    S_n(C)=-C S_(n-1)(C)+S_(n-2)(C)  (n>=2).

The roots r_+, r_- of r^2+C r-1=0 satisfy

    1+C epsilon-epsilon^2=(1-r_+ epsilon)(1-r_- epsilon),
    S_n(C)=r_+^n+r_-^n.

Consequently, on the logarithm branch equal to zero at epsilon=0,

    log(1+C epsilon-epsilon^2)
        = -sum_(n>=1) S_n(C) epsilon^n/n.                     (3)

This is a convergent identity, not merely a formal series. Choose M with
|A_p|,|B_p|<=M for every sufficiently large p, and put

    R=(M+sqrt(M^2+4))/2.

Both roots have modulus at most R. Hence |S_n(C)|<=2R^n for every
C occurring here. For any fixed 0<rho<1/R, (3) converges absolutely and
uniformly for these C and |epsilon|<=rho. Its tail after order N is at most

    2(R|epsilon|)^(N+1)/((N+1)(1-R|epsilon|)).                 (4)

The two logarithms in (2) therefore give, for every fixed N>=1,

    log log y = 2 alpha p+2 log p+log C0
                +sum_(n=1)^N h_n(1/p) exp(-n alpha p)
                +O_N(exp(-(N+1) alpha p)),                  (5)

where

    h_n(z) = -[S_n(d(1-z))+S_n(d log Delta z/alpha)]/n.

Each h_n is a polynomial in z of degree at most n. This follows directly
from the recurrence; equivalently, for n>=1,

    S_n(C) = sum_(k=0)^floor(n/2)
               [n/(n-k)] binom(n-k,k) (-C)^(n-2k).

For checks against the frozen first and second corrections,

    h_1(z) = d[1+(log Delta/alpha-1)z],
    h_2(z) = -2-(Delta/2)[(1-z)^2+(log Delta/alpha)^2 z^2].

The second expression is identical to the coefficient in the earlier
height-check note after simplification. Equation (2) also equals the entire
convergent series in (3), plus r(p). The remainder constant in (5) may depend
on N and the fixed parameters.

## 3. Rigorous all-orders inversion

Let t=alpha^(-1) W(sqrt(2 alpha Delta log B)), so

    2 alpha t+2 log t+log C0=log log B.

Let Phi(p) denote the right side of (2) with r(p) omitted. Set
z=1/t, E=exp(-alpha t), and p=t+u. Define near (u,z,E)=(0,0,0)

    w = z/(1+zu), v = E exp(-alpha u),
    G(u,z,E) = 2 alpha u+2 log(1+zu)
               +log(1+d(1-w)v-v^2)
               +log(1+(d log Delta/alpha)wv-v^2).             (6)

Using the logarithm branches vanishing at 1, G is jointly holomorphic in
a complex neighborhood of the origin, with

    G(0,z,0)=0, G_u(0,z,0)=2(alpha+z).

The analytic implicit-function theorem gives a holomorphic U(z,E), on a
sufficiently small polydisc, satisfying G(U(z,E),z,E)=0 and U(z,0)=0.
Its expansion

    U(z,E)=sum_(j>=1) beta_j(z) E^j                         (7)

converges uniformly on smaller polydiscs. In particular its order-N tail
is O_N(E^(N+1)) uniformly for small real z>=0. Thus
p_hat=t+U(1/t,exp(-alpha t)) exactly inverts the model Phi for large t.

The coefficients beta_j are not merely analytic near z=0: they are rational
functions of z, with constants depending on alpha,d,log Delta and possible
finite poles only at z=-alpha. To see this, expand G in u and E. Every
coefficient is polynomial in z, and the coefficient of u E^0 is
L(z)=2(alpha+z). The E^j equation determines beta_j by dividing a polynomial
in z and beta_1,...,beta_(j-1) by L(z). Induction proves the rational claim.
More specifically, a denominator L(z)^(2j-1) suffices. In a term u^r E^s
contributing to order j, induction bounds the denominator before the last
division by L to power 2(j-s)-r. Apart from the isolated linear term,
r+2s>=2, giving the bound 2j-1 after division; the r=0 terms satisfy it
as well.

For example, with H=h_1 and J=h_2,

    beta_1(z) = -H(z)/L(z),
    beta_2(z) = z^2 H(z)^2/L(z)^3
                -H(z)[alpha H(z)+z^2 H'(z)]/L(z)^2
                -J(z)/L(z).

In particular beta_1(0)=-d/(2 alpha) and beta_2(0)=1/alpha. The first
coefficient reproduces the frozen first inverse correction exactly.

Finally, the actual cutoff p_B exists uniquely and satisfies p_B=t+O(E),
as already proved in the frozen height check. Also p_hat=t+O(E), and
Phi'(p)=2 alpha+2/p+O(exp(-alpha p)) is bounded below by alpha for large p.
Since log log y(p_B)=Phi(p_B)+r(p_B)=Phi(p_hat), the mean value theorem gives

    |p_B-p_hat| <= |r(p_B)|/alpha
                 = O(exp(-c t exp(alpha t)))                (8)

for some fixed c>0. Here m(p_B) is asymptotic to
t exp(alpha t)/(2d), which justifies the last bound. The right side of (8)
is o(E^K) for every fixed K. Combining (7) and (8) establishes, for each
fixed N>=1,

    p_B = t+sum_(j=1)^N beta_j(1/t) exp(-j alpha t)
              +O_N(exp(-(N+1) alpha t)).                    (9)

Thus the proposed b_j(t) may rigorously be taken as beta_j(1/t). They are
rational in 1/t and analytic at 1/t=0.

## 4. Boundaries of this refinement

The convergent analytic series (7) represents the model inverse p_hat-t.
For the actual cutoff, (9) is an all-orders asymptotic expansion, with the
beyond-all-orders difference (8). The implicit-function argument does not
make that nonanalytic flat difference vanish or show equality of the
actual cutoff to the convergent series.

These height refinements do not remove the rotation discrepancy, justify
an exact substitution through a progression floor, or provide a new second
counting coefficient. The counting qualifications in the frozen packet
remain unchanged.
