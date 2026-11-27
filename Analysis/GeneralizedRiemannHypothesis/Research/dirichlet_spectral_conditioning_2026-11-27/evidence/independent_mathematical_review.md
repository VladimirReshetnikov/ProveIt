# Independent mathematical review: microcanonical gamma theorem

Reviewer: independent algebra/proof-review agent. Date: 27 November 2026.

## Conclusion

The general finite-band bridge theorem and the growing-low-frequency-block
total-variation theorem are mathematically valid with the hypotheses and exact
normalizations below. The sharp product-gamma comparison has the claimed normal
distribution profile and the Riemann-zero critical constant is correct. This
review checks the argument, not worldwide novelty or a Lean formalization.

The main safeguards are:

1. Use the exact saddle and exact tilted means in the fluctuation theorem.
   The leading regular-variation mean profile suffices only for a law of large
   numbers. Its deterministic error need not be smaller than the fluctuation
   scale.
2. Bridge coordinates must use fixed, distinct, finite thresholds
   `0 < c_1 < ... < c_k < infinity`. Adding the total coordinate at infinity
   would destroy the asserted total-variation convergence to a degenerate
   bridge coordinate. Weak convergence at that endpoint is a different claim.
3. Remove any separately observed fixed gamma coordinates from the first band
   before applying independence and the local central limit theorem; their
   centered contribution is restored as a vanishing translation.
4. Count repeated spectral values with multiplicity. The result needs no
   simplicity, gap, or independence hypothesis about the deterministic spectrum.
   If repeated values are aggregated into one gamma variable, its shape must
   be theta times the multiplicity.

## 1. Hypotheses and existence

Let `(gamma_j)` be a locally finite multiset in `(0,infinity)`, tending to
infinity, and let `N(T)=#{j:gamma_j<=T}` be regularly varying of index
`alpha in (0,p)`. Let `theta>0`, let `G_j` be independent Gamma variables
of shape theta and rate 1, and write

    lambda_j = gamma_j^p,
    X = sum_j G_j/lambda_j,
    K(t) = theta sum_j log(1+t/lambda_j).

Regular variation and `alpha<p` imply `sum_j 1/lambda_j<infinity`, for
example by partial summation and a Potter bound with exponent smaller than p.
Consequently `X<infinity` almost surely (its expectation is finite), and
`K(t)<infinity` for every finite `t>=0`. Differentiation is justified on
compact t-intervals by the same summable bound.

For `0<x<E X`, the equation

    K'(t) = theta sum_j (lambda_j+t)^(-1) = x

has a unique solution `t>0`. The left-hand side is continuous, strictly
decreasing, starts at `E X`, and decreases to zero by dominated convergence.
As `x` decreases to zero, this t tends to infinity. Put `u=t^(1/p)`.

The exponential tilt is the probability measure

    dP_t/dP = exp(-t X+K(t)).

Under `P_t`, the variables `G_j` are independent Gamma(theta,
rate `1+t/lambda_j`). Equivalently,

    H_j := t G_j/lambda_j = a_j Y_j,
    a_j = t/(lambda_j+t) = 1/(1+(gamma_j/u)^p),

where the `Y_j` are independent Gamma(theta,1). The product assertion can be
verified first on cylinder sets by independence and Laplace transforms, then
extended to the sigma-algebra. There is no need to assert an unjustified
equivalence of arbitrary infinite product measures.

Write

    m = E_t sum H_j = t x,
    v = Var_t(sum H_j) = theta sum a_j^2 = t^2 sigma^2,
    sigma^2 = theta sum (lambda_j+t)^(-2).

## 2. Regular-variation constants

With `beta=alpha/p`, Stieltjes regular-variation estimates give

    theta sum a_j       ~ theta C_1 N(u),
    theta sum a_j^2     ~ theta C_2 N(u),

where

    C_1 = integral_0^infinity alpha r^(alpha-1)/(1+r^p) dr
        = alpha*pi/(p*sin(pi*alpha/p)),
    C_2 = integral_0^infinity alpha r^(alpha-1)/(1+r^p)^2 dr
        = (1-alpha/p) C_1.

To justify these statements, the rescaled counting measures converge vaguely
on `(0,infinity)` to `alpha r^(alpha-1) dr`. Near zero a Potter bound with
an exponent strictly below alpha controls the mass. At infinity use a Potter
exponent strictly between alpha and p for the first integrand, and hence also
for the second. These bounds give the needed uniform integrability.

In particular `v` tends to infinity, `t x` is asymptotic to a positive
multiple of `N(u)`, and `sigma/x` tends to zero. For fixed `c>0`, the mean
fraction and variance fraction converge respectively to

    A(c) = C_1^(-1) integral_0^c alpha r^(alpha-1)/(1+r^p) dr,
    V(c) = C_2^(-1) integral_0^c alpha r^(alpha-1)/(1+r^p)^2 dr.

Repeated values of gamma cause no difficulty. Regular variation itself rules
out a single atom with a positive asymptotic fraction of `N(u)`: compare the
jump at u with `N(u)-N((1-epsilon)u)` and then let epsilon decrease to zero.

## 3. A uniform local central limit argument

Consider the total tilted sum, a fixed positive-width spectral band, the
infinite band beyond a fixed positive multiple of u, or the complement of
`{gamma<=h}` with `h=o(u)`. Center the selected sum of the H_j and divide
by its standard deviation. Its variance is of order `N(u)` in every case
needed for the theorem.

For a centered sum divided by `sqrt(v)`, the modulus of its characteristic
function is

    product_j (1+a_j^2 w^2/v)^(-theta/2).

Each relevant band contains a fixed compact interval of values of gamma/u
with positive width, and thus at least `c N(u)` coefficients a_j bounded
below by a fixed positive constant. For the complement of a low block use
gamma/u in `[1,2]`; since `h=o(u)`, all those coefficients remain in the
complement eventually. Since `v` is comparable with `N(u)`, the modulus is
bounded by

    (1+C w^2/N(u))^(-c' N(u))

with positive constants C and c'. For all sufficiently large N(u) this has
an integrable envelope independent of u: the function
`n log(1+z/n)` is increasing in n, so one may bound it using a fixed,
sufficiently large initial n. This supplies the Fourier domination missing
from a mere distributional central limit theorem.

The characteristic functions converge pointwise to the appropriate Gaussian.
Indeed `max a_j<=1` and

    theta sum a_j^3 / v^(3/2) <= 1/sqrt(v) -> 0.

Taylor expansion of the logarithm of the characteristic function therefore
has a vanishing cubic remainder. Fourier inversion and dominated convergence
give uniform convergence of the normalized densities to Gaussian densities.
This proves the local limit statements required by the conditioning step,
including a uniform bound on those densities.

## 4. Conditioning and the exact normalizing factor

Let

    W = (t X-t x)/sqrt(v),
    D_t = E_t[exp(t(X-x)) 1_{X<=x}].

If f_t is the density of W, then exactly

    D_t = (1/sqrt(v)) integral_0^infinity exp(-y) f_t(-y/sqrt(v)) dy.

The uniform local limit theorem and the uniform density bound imply

    sqrt(v) D_t -> phi(0) = 1/sqrt(2*pi).

Consequently the familiar saddlepoint small-ball expression is

    P(X<=x) ~ exp(t x-K(t)) / sqrt(2*pi*v).

This expression is a consequence here, not an additional unverified premise.

The scaled slack is `Y=t(x-X)>=0` under the event. The change of variable
from a standardized sum to Y has Jacobian `1/sqrt(v)`, or
`1/sqrt(v_R)` when a remainder variance v_R is used. The exponential
factor from undoing the tilt is `exp(-Y)`, with this sign.

## 5. Growing-block conditioning is valid in total variation

Let `I_t={j:gamma_j<=h(t)}` with `h(t)/u -> 0`. Write

    S_I = sum_{j in I_t} H_j,
    m_I = theta sum_{j in I_t} a_j,
    v_I = theta sum_{j in I_t} a_j^2,
    v_R = v-v_I.

One has `N(h)/N(u)->0`, even if h does not tend to infinity. For any fixed
epsilon>0, eventually h<=epsilon*u, whence the limsup of this ratio is at
most epsilon^alpha; then let epsilon decrease to zero. Thus
`v_I<=theta N(h)=o(v)` and `v_R~v`.

Let f_R be the density of the centered remainder sum divided by `sqrt(v_R)`.
Use as a reference measure `Q_t` the product of the exact canonical law of
the vector `(H_j)_{j in I_t}` and an independent Exp(1) variable y. The
joint conditional density of that vector and the slack, relative to Q_t,
is exactly

    R_t(H_I,y) =
      f_R((m_I-S_I-y)/sqrt(v_R)) / (sqrt(v_R) D_t),   y>=0.

Under Q_t, `(m_I-S_I)/sqrt(v_R)` tends to zero in probability by Chebyshev,
and `y/sqrt(v_R)` does likewise. Uniform density convergence gives
`f_R((m_I-S_I-y)/sqrt(v_R))->phi(0)` in probability. Also
`sqrt(v_R)D_t->phi(0)`. Hence `R_t->1` in Q_t-probability.

The argument remains valid even though Q_t lives in changing dimensions.
For every t, `E_Qt R_t=1`; therefore

    E_Qt |R_t-1| = 2 E_Qt (1-R_t)_+ -> 0,

because the last integrand is bounded by 1 and tends to zero in probability.
This proves total-variation convergence and requires no unstated uniform
integrability of unbounded likelihood ratios. It also proves the stronger
joint statement: the whole growing low block and the slack are asymptotically
independent, and the slack has the Exp(1) law.

Under the canonical law each H_j is Gamma(theta, rate
`1+(gamma_j/u)^p`). If instead each coordinate is scaled by
`t+gamma_j^p` rather than t, then the corresponding canonical coordinates
are exactly independent Gamma(theta,1). This alternative exact scaling
does not eliminate the transition for the common t-scaling stated in the
main theorem.

## 6. Sharp comparison with independent unit-rate gamma variables

Put `s_j=(gamma_j/u)^p` for j in I_t. Let P_can be the canonical product
with rates `1+s_j`, and Q the unit-rate Gamma(theta) product on the same
coordinate space. Define

    tau_t^2 = theta sum_{j in I_t} s_j^2.

Under Q the log likelihood of P_can relative to Q is

    L_t = sum_{j in I_t} [theta log(1+s_j)-s_j Y_j],

where the Y_j are independent Gamma(theta,1). Since
`max s_j <= (h/u)^p ->0`, if `tau_t^2->tau^2<infinity`, then

    E_Q L_t -> -tau^2/2,
    Var_Q L_t -> tau^2,
    theta sum s_j^3 <= (max s_j) tau_t^2 ->0.

The triangular-array characteristic-function expansion proves
`L_t -> Normal(-tau^2/2,tau^2)`, including the degenerate tau=0 case.
No Lyapunov ratio with a vanishing denominator is needed in that case.

Since `(1-exp(L_t))_+` is bounded and continuous,

    TV(P_can,Q) = E_Q (1-exp(L_t))_+
                -> 2 Phi(tau/2)-1.

For `tau_t^2->infinity`, the Hellinger affinity is exactly

    Aff(P_can,Q) = product_{j in I_t}
        [2 sqrt(1+s_j)/(2+s_j)]^theta.

Its logarithm is `-(1+o(1)) tau_t^2/8`, since max s_j tends to zero.
The affinity tends to zero, and `TV>=1-Aff` gives TV tending to 1.

The conditioning theorem transfers these limits to the conditional low-mode
vector by the triangle inequality. The same argument also shows the moving
profile

    TV(conditional low block, Q)
       = 2 Phi(tau_t/2)-1 + o(1)

without assuming that tau_t converges: otherwise choose a counterexample
subsequence, then a subsubsequence on which tau_t converges in the compactified
interval `[0,infinity]`, and use one of the established limits.

In particular TV tends to zero if and only if tau_t tends to zero. Necessity
can also be checked directly: for all sufficiently small max s_j,
`Aff<=exp(-c tau_t^2)` for a constant c>0, so a subsequence with tau_t bounded
away from zero prevents TV from tending to zero. If h remains bounded,
the block is uniformly finite and tau_t necessarily tends to zero; the
statement still holds, including the empty-block case.

## 7. Finite-band Brownian bridge and its joint independence

For fixed finite positive `c_1<...<c_k`, divide the spectrum into k+1
successive bands. The last band extends beyond c_k u to infinity. Each band
has variance asymptotic to a strictly positive fraction of v; the fractions
are the successive differences of `V(c_i)`, ending with `1-V(c_k)`.

The centered, sqrt(v)-normalized band sums have independent densities that
converge uniformly to normal densities of those variances. If separately
observing a fixed finite collection of gamma coordinates, remove them from
the first band before making this independence assertion. Their sum divided
by sqrt(v), after exact centering, tends to zero under the reference law.

Use cumulative coordinates z_1,...,z_k and slack y. With the fixed-coordinate
translation denoted delta/sqrt(v), the independent band arguments are

    z_1-delta/sqrt(v),
    z_2-z_1, ..., z_k-z_(k-1),
    -y/sqrt(v)-z_k.

The joint conditional density is the product of the band densities, the
fixed-coordinate canonical density, and

    exp(-y)/(sqrt(v)D_t),  y>=0.

The Jacobian is exactly `1/sqrt(v)`. Pointwise convergence gives the density
of a Gaussian independent-increment vector conditioned to have total zero,
an independent Exp(1) slack, and independent unit-rate Gamma(theta) fixed
coordinates. The Gaussian cumulative covariance is

    Cov(Z(c_i),Z(c_j)) = V(min(c_i,c_j))-V(c_i)V(c_j).

The limit density integrates to 1. Scheffe's lemma therefore gives total
variation, not merely weak convergence. Distinct finite positive thresholds
make this Gaussian covariance nondegenerate.

At c=infinity the original centered coordinate equals `-y/sqrt(v)` and is
not identically zero, while the proposed bridge endpoint is identically zero.
Those marginal laws have TV distance 1 for every finite t. Accordingly an
endpoint may be included in weak convergence or an LLN, but not in this
nondegenerate finite-dimensional total-variation statement. An identically
zero coordinate at c=0 is harmless if treated as a common Dirac factor,
although omitting it keeps the density formulation simple.

Uniform convergence of the cumulative mass profile in probability follows
from the finite-coordinate LLN, monotonicity, and finite grids for the
continuous distribution function A(c). The tail at infinity is controlled
by the slack: `X/x = 1-y/(tx) ->1`. No functional total-variation claim is
needed or warranted.

## 8. Riemann-zero specialization and constants

For positive Riemann zero ordinates counted with multiplicity,

    N(T) ~ T log(T)/(2*pi).

With p=2 this gives alpha=1, C_1=pi/2, C_2=pi/4, hence

    x ~ theta log(u)/(4u),
    v ~ theta u log(u)/8,
    sigma^2 ~ theta log(u)/(8u^3),
    A(c) = (2/pi) arctan(c),
    V(c) = (2/pi) [arctan(c)+c/(1+c^2)].

Karamata's moment estimate yields, as h tends to infinity,

    sum_{gamma<=h} gamma^4
      ~ (1/5) h^4 N(h)
      ~ h^5 log(h)/(10*pi).

Thus

    tau_t^2 ~ theta h^5 log(h)/(10*pi*u^4).

At `h=c (u^4/log u)^(1/5)`, for fixed c>0,
`log h/log u ->4/5`, so

    tau_t^2 -> 2 theta c^5/(25*pi).

The coefficient `2/(25*pi)` is correct. The sharp profile is consequently

    2 Phi( sqrt(2 theta c^5/(25*pi))/2 ) - 1.

If using the xi product under RH, take one gamma variable per positive
ordinate counted with its zero multiplicity; the pairing of zeros at
`+i gamma` and `-i gamma` produces one factor `1+s/gamma^2`, not two.
There is no extra factor of two in theta. The randomness in the theorem
comes from the auxiliary gamma variables, not from an assumption that
the Riemann zeros are random.

## 9. Scope of this review

The proof uses only regular variation, gamma characteristic functions,
elementary exponential tilting, Fourier inversion with an explicit envelope,
and a likelihood comparison. Its application to a reciprocal xi transform
uses the relevant zero-location theorem and paired canonical product.

The growing-dimensional canonical approximation and its sharp common-scale
breakdown are stronger than a fixed-coordinate Gibbs conditioning principle.
Nonetheless the broader methods are classical, so novelty should be claimed
for the precise theorem and its spectral application relative to the supplied
article and the sources actually checked, not as established global priority.

## 10. Additional review: macroscopic breakdown of canonical independence

The root's further formula is correct. Let h/u tend to a fixed
`c in (0,infinity)` and let `rho=V(c) in (0,1)`. Here compare the entire
conditional low-block law with its actual canonical tilted product, not with
the unit-rate product. Put

    Z_u = (S_I-m_I)/sqrt(v),
    rho_u = v_I/v -> rho.

Under the canonical product, `Z_u` converges to Normal(0,rho). The normalized
remainder density, using total sqrt(v) as scale, converges uniformly to
`phi_(1-rho)`. The proof of the local limit for the moving endpoint h/u is
the same as before: variance convergence follows by squeezing between fixed
nearby endpoints, and fixed positive-width intervals inside the remainder
supply the Fourier envelope.

The exact conditional marginal likelihood, relative to the tilted product on
the block, is

    R_u(S_I) = [1/(sqrt(v) D_t)]
      integral_0^infinity exp(-y) g_R(-Z_u-y/sqrt(v)) dy,

where g_R is the density of `(S_R-m_R)/sqrt(v)`. It depends only on the
block sum. Since g_R converges uniformly and the limiting Gaussian has a
bounded derivative, uniformly over every value of Z_u the integral differs
by o(1) from `phi_(1-rho)(-Z_u)`. Indeed the Gaussian-translation error is
at most a constant times `integral y exp(-y)dy/sqrt(v)`.
Consequently the likelihood is uniformly o(1) from

    r_rho(Z_u) = (1-rho)^(-1/2)
                exp(-Z_u^2/[2(1-rho)]).

Using the bounded overlap functional,

    TV = 1-E_can min(1,R_u),

gives the limit between Normal(0,rho*(1-rho)) and Normal(0,rho).
The two normal densities cross where

    z_*^2 = -(1-rho) log(1-rho).

The narrower normal has excess mass for `|z|<z_*`, so the limit is exactly

    D(rho) = 2 [
      Phi(sqrt(-log(1-rho)/rho))
      - Phi(sqrt(-(1-rho)*log(1-rho)/rho)) ].

Thus the proposed formula and its signs are correct. D(rho)>0 for
`0<rho<1`, D(rho) tends to 0 as rho decreases to 0, and D(rho) tends to 1
as rho increases to 1. An elementary expansion gives
`D(rho) ~ phi(1)*rho` as rho decreases to zero; the difference of the two
normal arguments is rho/2 to first order.

The same limit holds if the slack is included and the comparison law tensors
the canonical block with Exp(1): the y-dependence of the exact likelihood is
a vanishing translation on the sqrt(v) scale. Thus the conservation correction
acts only through the block sum at this scale.

For `h/u->infinity`, no local limit for a possibly tiny remainder variance
is needed. For every fixed c, projection onto the smaller block gamma<=cu
cannot increase TV, hence the liminf is at least D(V(c)). Let c tend to
infinity to obtain TV tending to 1.

Together with the low-block theorem, this gives a full canonical phase
diagram: if h/u tends to c in the compactified interval [0,infinity], the
distance tends to D(V(c)), with endpoint values 0 and 1. In particular,
asymptotic canonical independence holds if and only if h=o(u).
Necessity without a convergent ratio follows by taking a subsequence on which
h/u is bounded below and projecting onto a fixed positive multiple of u.

This is a distinct second transition from the earlier unit-rate-gamma
threshold: accumulated differences between the exact individual rates matter
already at a sublinear h, while conditioning itself creates a persistent
collective dependence only once h is of order u.

## 11. Review of the actual LaTeX draft

The full agent draft `research/microcanonical.tex` was read after the
independent derivation above. Its equations `mc:eq:jointdensity` and
`mc:eq:blockratio` are consistent: it uses total sqrt(v), rather than the
remainder's own standard deviation, throughout those changes of variable.
The Fourier envelope and its tail estimate are valid. Its bounded-density
argument for L1 convergence in changing dimensions is also sufficient.

No mathematical correction was required. One minor exposition request was
sent to the author: repeat the assumption h tends to infinity next to the
Riemann-specialized asymptotic involving `h^5 log h`. The general moment
asymptotic already states this qualification, but it should remain visible
when the specialized formula is read on its own.

## 12. Optional equivalent formulation by number of Riemann modes

There is a clean mode-count version of the fifth-power height threshold.
Write `n=N(u)` and observe the first `k=k(u)` modes, counted with
multiplicity. If

    k ~ kappa n^(4/5),   kappa>0,

then

    tau_u^2 -> (125 theta/256) kappa^5.

To verify the constant, the critical height
`h=c (u^4/log u)^(1/5)` gives

    N(h)/N(u)^(4/5) -> (4c/5) (2*pi)^(-1/5).

Thus `c=(5 kappa/4)(2*pi)^(1/5)`, and substitution into
`2 theta c^5/(25*pi)` yields `125 theta kappa^5/256` exactly.
The corresponding profile is

    2 Phi( sqrt(125 theta kappa^5/256)/2 ) - 1.

An independent verification uses
`gamma_j ~ 2*pi*j/log j` and
`sum_(j<=k) gamma_j^4 ~ (2*pi)^4 k^5/[5(log k)^4]`;
since `log k/log n ->4/5`, the coefficient is
`1/[5(4/5)^4]=125/256`.

Repeated ordinates do not obstruct the first-k formulation. A spectral
jump is o(N(h)) under regular variation, so cutting partway through a
repeated value changes the asymptotic counting and moment estimates by
relative o(1). The core growing-block argument also applies directly to
the first k indices, since all of them have gamma_j<=gamma_k=o(u).

This translates the two distinct scales into counts: common unit-rate
gamma behavior persists for `k=o(n^(4/5))`, while exact canonical gamma
independence persists through `k=o(n)`. The statement about breakdown
beyond the four-fifths scale presupposes the sublinear block regime if
using the first growing-block theorem; at macroscopic and larger blocks,
the second transition also prevents canonical independence.
