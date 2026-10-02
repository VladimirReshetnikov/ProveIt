# Optional complementary regime: exponentially small success/failure

This is an application of the established Beta-renewal identity, not a new probabilistic mechanism. The central theorem is in PROOF.md. This note first establishes the leading rare tail, then proves all fixed integer correction orders on compact ratio ranges separated from the transition. It does not give a single error-function formula bridging both regimes.

Let rho=k/m be the exact integer ratio. For rho in a fixed compact subset of (0,1) or (1,infinity), define

I(rho)=1-rho+rho log rho.

Then the rare probability T_m(k), equal to 1-p_m(k) for rho<1 and p_m(k) for rho>1, satisfies

T_m(k)= exp(1-1/rho) sqrt(rho) /
        [abs(rho-1) sqrt(2pi m)]
        * exp(-m I(rho)) * (1+O(1/m)),                         (1)

uniformly on that compact subset. It is essential to use exact rho=k/m. Replacing it by a limiting rho without controlling k-rho*m changes the constant.

## Proof

For Y=mBeta(1,m), let M_m(t)=E exp(tY), K_m=log M_m. For t in a compact real interval below1, and in a fixed small complex neighborhood of it, direct density expansion gives

M_m(t)=1/(1-t)+m^(-1)[1/(1-t)^2-1/(1-t)^3]+O(m^-2),
K_m(t)=-log(1-t)+m^(-1)[1/(1-t)-1/(1-t)^2]+O(m^-2).       (2)

The same expansion holds with any prescribed fixed number of derivatives. To justify it, split the density integral at y=m^eta with eta small. On the first interval Taylor-expand (m-1)log(1-y/m) to the required finite order. The remainder is bounded by a polynomial in y times a fixed integrable exponential after decreasing the neighborhood. On the complementary interval use exponential domination, uniformly in t. No analyticity in 1/m of the full mgf is used or needed.

There is a unique real saddle t_m satisfying K'_m(t_m)=1/rho; uniform strict convexity and (2) give

t_m=1-rho+O(m^-1),   K''_m(t_m)=rho^-2+O(m^-1).

The tilted law has density exp(t_m y)f_m(y)/M_m(t_m). Its mean is1/rho, its variance stays bounded above and below, its moments have uniform exponential bounds, and it satisfies the same uniform nonlattice and bounded-variation Fourier estimates as in PROOF.md. In particular the central density Edgeworth expansion is uniform in the present parameter range.

Let S=sum_{i<=k}Y_i. Exponential tilting gives exactly

T_m(k)=exp(k K_m(t_m)-t_m m)
       integral_0^infinity exp(-abs(t_m)u) g_{m,k}(epsilon u) du,

where g_{m,k} is the tilted density of S-m, epsilon=+1 for the upper tail (rho<1) and -1 for the lower tail (rho>1); it is zero outside its support. Since |t_m| is bounded away from0, the density expansion at u=O(1), integrated against this exponential weight, yields

integral =1/[abs(t_m)sqrt(2pi k K''_m(t_m))]*(1+O(k^-1)).

For precision, a uniform density Edgeworth expansion through order k^-1 with uniform O(k^-3/2) error after normalization suffices: near the origin the odd first correction is O(u/k), while the Gaussian changes by O(u^2/k). Their weighted integrals are O(k^-1); the uniformly bounded remainder and exponential weight are integrable. The region u larger than a slowly growing multiple of log k is negligible by the weight and the uniform O(k^-1/2) bound on the density.

Finally, the saddle displacement does not affect the order1 exponential correction because the limiting exponent is stationary at t0=1-rho. Substitution in (2) gives

kK_m(t_m)-t_m m=-m I(rho)+(rho-1)/rho+O(m^-1).

Together with k=rho*m and K''_m(t_m)=rho^-2+O(m^-1), this proves (1).

## Possible continuation

Higher finite orders follow by retaining more terms in (2), solving the saddle recursively, and integrating the tilted density polynomials; all coefficients are explicit rational functions of rho away from rho=1. A transition-uniform error-function saddle expansion would be a stronger synthesis. The all-orders supplement below supplies the rare-tail coefficient algorithm; a transition-uniform exponentially improved expansion remains outside scope.

## All finite integer orders and coefficient algorithm

The preceding argument can be made into an arbitrary-fixed-order theorem. On the same compact rho-ranges, for every J>=0,

T_m(k)= exp(1-1/rho) sqrt(rho) /[abs(rho-1)sqrt(2pi m)]
        * exp(-m I(rho))
        * [1+sum_{j=1}^J c_j(rho)m^(-j)+O_J(m^(-J-1))].       (3)

The c_j are rational functions of rho, with possible poles at0 and1. The compact range excludes these singular endpoints. The first correction, including the true saddle shift, is

c1(rho)=-(rho^4+10rho^3-17rho^2+24rho-6)
          /[12rho^3(rho-1)^2].                               (4)

Here is an explicit finite algorithm and remainder proof for (3), beyond the leading-only calculation above.

1. Put epsilon=1/m. Expand

   (m-1)log(1-y/m)=-y+sum_{j>=1}epsilon^j[y^j/j-y^(j+1)/(j+1)]

   through any required finite order. Exponentiate formally, integrate each polynomial coefficient against exp(-(1-t)y) on (0,infinity), and take the finite formal logarithm. This gives

   K_m(t)=-log(1-t)+sum_{j=1}^L epsilon^j B_j(t)+O(epsilon^(L+1)),

   with rational B_j and derivative-uniform remainder on the specified complex neighborhoods. For example B1=1/(1-t)-1/(1-t)^2 and B2=3/[2(1-t)^2]-4/(1-t)^3+5/[2(1-t)^4]. The split-integral argument proving (2) gives this at every finite L.

2. Solve K'_m(t_m)=1/rho recursively around t0=1-rho. The derivative of K'_0 is rho^-2, uniformly nonzero. A finite-order implicit-function argument with residual control proves each finite saddle expansion with its stated O(epsilon^(L+1)) remainder. In particular

   t_m=1-rho+(2/rho-1)/m+O(m^-2).

3. For fixed actual m and its exact saddle t_m, let sigma^2=K''_m(t_m), and lambda_r=K_m^(r)(t_m)/sigma^r. Set eta=k^(-1/2). Define a Gaussian functional G on a formal variable u by

   G[u^(2a)]=(-1)^a(2a-1)!!,  G[u^(2a+1)]=0.

   For j>=0 define

   Q_j = G [eta^(2j)] { (1+eta u/(t_m sigma))^(-1)
             * exp(sum_{r=3}^{2j+2}lambda_r u^r eta^(r-2)/r!) }.

   Then Q0=1 and the exact-saddle expansion is

   T_m(k)=exp(kK_m(t_m)-t_m m)
          /[abs(t_m)sqrt(2pi kK''_m(t_m))]
          * [sum_{j=0}^J Q_j k^(-j)+O_J(k^(-J-1))].          (5)

4. Substitute the finite expansions from steps1–2 in (5), with k=rho*m, and collect powers of epsilon. This is the algorithm for c_j(rho).

### Why (5) has a uniform remainder and only integer powers

Fourier inversion of the tilted density and integration over the required half-line give exactly

T_m(k)=exp(kK_m(t_m)-t_m m)/(2pi)
  * integral_{R} [M_m(t_m+iv)/M_m(t_m) * exp(-iv/rho)]^k
                * sign(t_m)/(t_m+iv) dv.

This global formula uses the tilted characteristic function directly; no global
logarithm of M_m is assumed. The analytic branch K_m is used only in a fixed
nonvanishing neighborhood of the real saddle for the low-frequency expansion.

The interchange is justified by the integrable kth power of the tilted characteristic function and the absolutely integrable half-line weight. Uniform exponential moments, nonlattice separation, and 1/|v| characteristic decay for the tilted laws give the same low/middle/high frequency control as PROOF.md; all constants are uniform because rho stays in a fixed compact set away from1 and0. For the tilted density, the logarithmic derivative is t_m-(m-1)/(m-y), so it is eventually decreasing on its support: t_m<=1-a while (m-1)/m→1. Its endpoint and total variation are uniformly bounded, giving the high-frequency estimate directly.

On scaling v=w/(sigma sqrt(k)), Taylor-expand the exponent and (1+iw/(t_m sigma sqrt(k)))^(-1) to any fixed order. Both have uniform remainder bounds on a small-power frequency cutoff. The denominator has no real-axis singularity because |t_m| is bounded away from0. Gaussian domination makes every polynomial error integrable. Integrating terms gives G, and odd powers of eta vanish: their monomials have odd degree in u and the Gaussian integral is symmetric. Expanding one extra odd order before bounding the remainder gives O(k^(-J-1)) after retaining through k^-J. The middle and high-frequency integrals are smaller than every algebraic order. This establishes (5), then (3).

### Independent derivation of (4)

The order1/m contribution from the exponent is

(2rho^2-4rho+1)/(2rho^3),

from the exact-saddle prefactor it is

-(rho^2-3rho+1)/[rho^2(rho-1)],

and from Q1/k it is

[ -1/12-rho/(1-rho)^2 ]/rho.

Their sum is (4). The Q1 formula before taking the m→infinity limit is

Q1=lambda4/8-5lambda3^2/24
    -lambda3/(2t_m sigma)-1/(t_m^2 sigma^2).

Exact Beta-simplex checks at m=10,20,40 and several fixed ratios are in rare-tail-exact-checks.json. As expected, convergence is substantially slower near rho=1, which is excluded from a uniform compact bound. At rho=2,m=40 the exact/leading ratio is0.98318167; including (4) improves exact/approximate to1.00143703. These checks do not replace the uniform asymptotic proof.

## Updated scope

This note now proves all fixed integer orders for the separated fixed-ratio rare tails, with a finite coefficient algorithm. It still does not prove a single transition-uniform exponentially improved formula, optimal truncation, or resurgent/Stokes-sector claims. The central and rare-tail expansions are two complementary rigorously controlled regimes.
