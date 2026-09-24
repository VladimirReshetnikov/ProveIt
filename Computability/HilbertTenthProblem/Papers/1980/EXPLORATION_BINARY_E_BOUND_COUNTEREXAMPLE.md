# A full positive counterexample to the one-sided e bound

The published 90-operation binary construction uses

    sigma=(e-ell)(x+g)^2, ell+sigma+alpha=q.

Replacing the second equation by `e+alpha=q` saves one addition.
The exact 89-operation arithmetic and a partial bootstrap are recorded
in `EXPLORATION_BINARY_E_BOUND.md`. The replacement is nevertheless
unsound. For every admissible binary index and every positive input x,
the changed system has positive witnesses. In particular the index
of an inconsistent circuit accepts every positive input.

The mechanism differs from the common-code-shift counterexample. Both
codes here are canonical and remain below q. The unrestricted code
variable g instead makes the packed index arbitrarily large while
the first exponential's supplied value U and the main parameter a
stay fixed. Its modular congruence wraps, and a positive extra period
in the first Pell index supplies the strict interval. A quadratic
equidistribution argument proves the existence of the required periods.

Fixed numerals are free throughout. This is a rejection of the stated
89-operation candidate, not a lower bound for universal certificates.

## 1. Fix the codes, then let the packed index vary

Fix an admissible index `(V,H,T_L)` from `BINARY_PRODUCT_90_PROOF.md`,
with its binary polynomials ell0,e0, positive difference D=e0-ell0,
length L, and H=H0-1. Fix any positive queried input x. Choose a
sufficiently large power of two B and put

    b=B-H0-1>x, beta=b-x, theta=B-2=H+b,
    q=B^L, n=q^8, lambda=(q^2-1)/(B-1),
    ell=ell0(B), e=e0(B), alpha=q-e.

All these supplied witnesses are positive. In particular, D(B)>0
by its positive leading reset, and 0<ell<e<q for large B. The fixed
congruence quotient

    t_code=(ell+e*q-V)/(B-2)

is a positive integer: evaluate the nonconstant polynomial
ell0(T)+T^L e0(T) at B and at 2. Here and below t_code is the
source's code-congruence witness, distinct from a Pell sequence index.

Write Omega=e-ell>0, S2=ell+e*q, and, for an integer g>0, define

    C(g)=x+g, sigma(g)=Omega*C(g)^2,
    S(g)=g+q^2*S2+q^4*sigma(g),
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b),
    r(g)=S(g)*(n^2-n)+Tplus*(n^2-1).             (1)

Tplus is fixed, positive, and below n. The function r(g) is an
integer quadratic with positive leading coefficient

    (n^2-n)*q^4*Omega.

It is strictly increasing for g>0. Every coding equation of the
changed system holds for every such g. No mask is an additional
source equation: in the valid 90-operation proof the masks are
consequences of the Pell and range argument, which is precisely
what the weakened bound disrupts.

Choose the initial value g0=B. By increasing B before fixing it,
one can require

    ell+Omega*(x+B)^2<q.

This follows from deg(D)<K and the compiler's L>3K+2, which give
deg(D(T)*(x+T)^2)<L; also deg(ell0)<K<L. Thus
the original stronger bound holds at the seed g0, and the original
elementary packing ranges give

    0<S(g0),Tplus<n, n^2-1<=r0=r(g0)<2n^3.       (2)

No mask or binomial divisibility is asserted at this seed. The code
polynomial ell0 has zero constant term, so B divides ell. Hence
S(g0),Tplus,r0 are even.

## 2. Fix the main Pell parameter and preserve the wrapped congruence

Set

    u0=2r0+1, U=2^u0, Y=n^2,
    a=Y*(U+1), A=a+2, DA=A^2-1,
    E=U*Y, Q=U*Y^2, P=2Q+1, DP=P^2-1,
    M=4a+3.

These quantities will remain fixed as g increases. The source
witnesses `w=U/n^2` and `s=Y/n^2=1` are positive integers. Indeed,
n is a power of two, and (2) gives U>n^2. The same seed bounds give

    a>U>n, q^3=B^(3L)<n, and L<2r0+1.

Let Phi be Euler's totient of the positive odd integer M, and
restrict g to the integer progression

    g(j)=B+2B*Phi*j, j=0,1,2,... .              (3)

Because r is an integer polynomial,

    r(g(j))=r0 modulo Phi.

Euler's theorem applies to 2 modulo M. Writing r=r(g(j)), J=2r+1,
we consequently have

    2^J=2^u0=U modulo M.                       (4)

Moreover g(j) is divisible by B, so r is even and J=1 modulo 4.
The sequence r tends to infinity, although a,U,Y remain fixed.

For each j choose the main Pell coordinates

    c=psi_A(J), d=chi_A(J).

They satisfy d^2-DA*c^2=1. The polynomial Pell recurrence gives

    chi_A(J)-(A-2)*psi_A(J)=2^J modulo 4A-5.

Together with (4), this makes

    gamma=(d-U-a*c)/(4a+3)

an integer. It is positive: the recurrence identity

    d-a*c=2c-psi_A(J-1)>c>U

holds here, since J>=u0>2 and c>A>U. Thus the first exponential
source equation holds with a positive quotient even though
`U != 2^J` for every j>0. This is the modular wrap needed below.

## 3. Two distinct quadratic units

Define positive real numbers

    z=A+sqrt(A^2-1), zP=P+sqrt(P^2-1),
    Hlog=E*log(zP),
    beta_log=(2*log(z)-log(zP))/Hlog.

First, beta_log>0. Since z>2A-1 and zP<2P, it suffices that
(2A-1)^2>2P. Direct expansion gives

    (2A-1)^2-2P
      =4Y^2*(U^2+U+1)+12Y*(U+1)+7>0.           (5)

Second, beta_log is irrational. The integer Y=n^2 is divisible
by four, so A=2 modulo four and DA is odd. In contrast,

    v_2(DP)=u0+2*v_2(Y)+2

is odd, since u0 is odd. Thus DA and DP have distinct square
classes, and their real quadratic fields are distinct. If
log(z)/log(zP) were rational, positive powers of z and zP would
coincide. Their common value would belong to the intersection of
the two fields, namely the rationals. No positive power of z can
be rational: its conjugate is its reciprocal, which would force
that power to equal 1. This contradiction proves irrationality
of the logarithmic ratio and hence of beta_log.

## 4. An elementary quadratic density lemma

If f(j) is a real quadratic polynomial with irrational leading
coefficient, its fractional parts visit every nonempty open interval
of the circle infinitely often.

Here is a proof sufficient for this use. For any nonzero integer m,
put a_j=exp(2*pi*i*m*f(j)). Apply Cauchy--Schwarz to the average
of H translates of the sum of a_j, with endpoint errors O(H/N).
For fixed H, the resulting differencing bound is

    limsup_N |(1/N) sum_(j<N) a_j|^2
      <= 1/H +(2/H) sum_(h=1)^(H-1)
            (1-h/H) limsup_N |(1/N) sum_(j<N-h) a_(j+h)*conj(a_j)|.

Each inner sum is a geometric sum whose ratio is not 1: its phase
is linear in j with irrational coefficient 2*m*h times the leading
coefficient of f. After division by N it tends to zero. Letting
H tend to infinity proves that every nonconstant integer Fourier
average tends to zero.

To turn this into the stated interval assertion, take a nonnegative
continuous periodic function supported inside the desired interval
and having positive integral. Approximate it uniformly by its Fejer
means, which are trigonometric polynomials. Uniform approximation
follows directly from the nonnegative kernels

    F_H(t)=(1/H)*(sin(pi*H*t)/sin(pi*t))^2:

their integral is 1 and their mass outside any neighborhood of zero
tends to zero. The preceding Fourier averages therefore imply that
the averages of the chosen function tend to its positive integral.
Infinitely many indices must lie in its support. This proves the
lemma without a quantitative or probabilistic approximation claim.

## 5. Choose the extra first-index period by density

For an integer v>=0, set the first Pell index

    tP=r+1+v*E, k=psi_P(tP).

The normalized closed form

    psi_A(J)=z^(J-1)*(1-z^(-2J))/(1-z^(-2))

and its P analogue give the exact identity

    log(c/k)=r*(2*log(z)-log(zP))-v*Hlog+C0+epsilon,
    C0=log((1-zP^(-2))/(1-z^(-2))),
    epsilon=log((1-z^(-2J))/(1-zP^(-2tP))).     (6)

For v>=0, epsilon tends to zero as j tends to infinity, since
J=2r+1 and tP>=r+1 both tend to infinity. This estimate is uniform
over all choices v>=0.

Write

    ell_log=log(1+1/Y)>0,
    delta_log=ell_log/Hlog, 0<delta_log<1,
    gamma_log=(C0-log(Y))/Hlog.

By (1), (3), and the irrationality in Section 3, the polynomial

    f(j)=beta_log*r(g(j))+gamma_log

has an irrational quadratic leading coefficient. The density lemma
therefore supplies infinitely many arbitrarily large j with

    delta_log/3 < fractional_part(f(j)) < 2*delta_log/3.

For these j take v=floor(f(j)). Because beta_log>0, v is positive
for all sufficiently large selected j. Increase j further until
|epsilon|<ell_log/6. Substitution in (6) yields

    log(Y)+ell_log/6 < log(c/k)
                      < log(Y)+5*ell_log/6 < log(Y+1).

Thus the exact integer Pell coordinates, not merely their leading
approximations, satisfy

    Y<c/k<Y+1.                                (7)

Consequently eta=c-Y*k and zeta=(Y+1)*k-c are positive integers.
They give the source's two interval equalities.

Set tau=(chi_P(tP)-1)/2. The parameter P is odd, so tau is a
positive integer, and its exact norm gives

    tau*(tau+1)=(E^2+U)*(Y*k)^2.

Also psi_P(tP)=tP modulo P-1, and E divides P-1=2UY^2. Since
tP=r+1+vE, the quotient

    h=(k-r-1)/E

is integral. It is positive because tP>=r+1>1 and psi_P(tP)>tP.
Every first-norm and first-index equation now holds. The extra
period v is strictly positive, exactly the case that the weakened
bootstrap could not eliminate.

## 6. Supply every remaining positive Pell witness

The relaxed and half-parameter auxiliary construction is unchanged.
Since c=psi_A(J) and J=1 modulo four, the positive generic
construction in `HALF_PARAMETER_PELL_92_PROOF.md` applies:

    m=2cJ, f=chi_A(m), i=DA*psi_A(m)/c^2, R=i*c^2,
    y_aux=psi_R(J), u_star=chi_R(J)/R,
    o=(u_star-c)/f, j_aux=(u_star-J)/c.

All these quotients are positive integers and satisfy the relaxed
norm, the two congruence expressions for u_star, and

    R^2*(u_star^2-y_aux^2)=1-y_aux^2.

Here j_aux is the source's auxiliary witness, distinct from the
progression index j. This construction uses the true main index J;
it does not assume any identity U=2^J.

For the fixed second Pell index choose

    kappa=psi_A(L), mu=chi_A(L),
    phi=c-kappa, Delta=(psi_A(L)-psi_2(L))/a.

The inequality J>L makes phi positive. Since L>=2 and A>2,
Delta is positive, and the polynomial recurrence modulo a makes
it integral. The fixed parameter remains exactly T_L=psi_2(L).

The second exponential has its actual value q=B^L. Its recurrence
congruence modulo MB=DA-(A-B)^2 gives the integer quotient

    rho=(mu-q-(A-B)*kappa)/MB.

The modulus is positive because A>U>n>B. Its numerator is positive:

    mu-(A-B)*kappa=B*kappa-psi_A(L-1)
                    >(B-1)*kappa>q,

using kappa>=A>n>q. Both the second norm and its exponential equation
are exact. Their witnesses need not vary with the progression except
for the positive gap phi.

This supplies all 34 positive unknowns: the unchanged coding values,
the variable g,sigma,r, w and s=1, all first/main/second Pell
coordinates, the interval witnesses, every exponent and index
quotient, and the retained relaxed and half-parameter auxiliaries.
Every one of the changed system's 22 source equations holds.

No central-binomial divisibility or uniform upper bound on r is
used in this extension. For the selected large j, r grows beyond
every fixed multiple of n^3 while U and a stay fixed. This is allowed
by e+alpha=q and is prevented by the published combined bound.

## 7. Consequence and evidence boundary

Apply the construction to the fixed index of an inconsistent circuit.
That represented set is empty, but every positive x has positive
witnesses for the weakened system. The 89-instruction arithmetic
is therefore not a universal encoding of the intended represented set.

The companion arithmetic checker is
`../verification/explore_round37_e_bound.py`. It checks all 89
primitive instructions and all 22 polynomial source residuals. The
counterexample above is a general existence proof using the proved
density lemma. It does not claim a numerically materialized full
Pell witness or a finite search bound on the selected progression
index. Such a bound is unnecessary for refuting the equivalence.
