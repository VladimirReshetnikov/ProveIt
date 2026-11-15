# A uniform computability obstruction for arbitrary Cauchy-presented coefficients

## Precise claim

There is no uniform computable procedure which, from arbitrary fast Cauchy names of the coefficients of a monic quadratic P(X,Y), returns:

1. a positive integer e;
2. a finite Laurent lower bound k0;
3. a computable coefficient name for each coefficient y_k of a formal Puiseux root y(t)=sum_{k>=k0} y_k t^k satisfying P(t^e,y(t))=0.

Allowing arbitrary e, representation-dependent choices of root, and arbitrarily small radii of convergence does not remove the obstruction. Convergence need not be requested: the exact formal coefficient statement alone is already impossible uniformly.

The obstruction holds even when the coefficient-name evaluator is one fixed primitive-recursive program with an ordinary natural parameter m. It does not rely on coding arbitrary primitive-recursive programs or on a putative universal PR evaluator.

## The elementary discontinuity

For a nonnegative represented real a, consider

    P_a(X,Y)=Y^2−X^2−a.

Any returned root after X=t^e satisfies

    y(t)^2=t^(2e)+a.

Because the Laurent lower bound is finite and the right side has no negative exponents, every negative coefficient of y is zero. This can be proved by finite induction from its lower bound: at exponent 2j, after all earlier coefficients have vanished, the coefficient of the square is y_j^2; a complex number with square zero is zero.

If a=0, the same finite induction shows y_j=0 for 0<=j<e. At degree 2e, the identity then gives

    y_e^2=1, hence |y_e|=1.

If a>0, the constant coefficient satisfies y_0^2=a, so y_0 is apart from zero. For 1<=j<2e, coefficient comparison gives

    2 y_0 y_j + sum_{i=1}^{j-1} y_i y_{j-i}=0.

Finite induction yields y_j=0 throughout this range, and in particular

    y_e=0.

Thus the coefficient at the algorithm's own returned index e has norm exactly 1 when a=0 and exactly 0 when a>0. Obtain a Gaussian-rational approximation q to y_e within 1/8. In the first case |q|>=7/8; in the second |q|<=1/8. The rational decision |q|^2>1/4 therefore decides whether a=0.

## A single primitive-recursive halting family

Let H(m,k) be the primitive-recursive Boolean asserting that machine m halts within k steps. Define

    a_m = sum_{k>=0} 2^(−k−1) H(m,k),
    A(m,s) = sum_{k<s} 2^(−k−1) H(m,k).

The finite evaluator A is one fixed primitive-recursive function of (m,s). The omitted tail is at most 2^(−s), so A gives valid fast Cauchy names uniformly. If machine m never halts, then a_m=0. If its first halting stage is h, then

    a_m = sum_{k>=h}2^(−k−1)=2^(−h)>0.

Applying the hypothetical Puiseux constructor to P_{a_m}, and then performing the separated coefficient test, would decide the halting problem. Hence no such uniform computable constructor exists.

Every individual a_m happens to be a dyadic rational. This is why the theorem's input restriction must say FINITE EXACT ALGEBRAIC PRESENTATIONS, rather than merely saying that the represented values are algebraic. Cauchy names of algebraic-valued coefficients do not supply decidable exact zero tests or their finite exact algebraic codes.

## Interpretation for the iPRA result

This rules out the unrestricted uniform witness construction above, including a fixed-program schema uniform in m. It justifies giving the constructive theorem with exact algebraic coefficient codes (or a more general coefficient interface explicitly supplying exact equality, inverses of witnessed nonzero coefficients, and certified finite splitting).

Do not overstate the conclusion as syntactic unprovability of every conceivable first-order sentence called Puiseux's theorem. The obstruction specifically concerns outputting individually accessible exact Puiseux coefficients with computable names and a finite ramification integer from arbitrary Cauchy input. Weaker approximate-root data, conditional nondegeneracy formulations, multivalued aggregate representations, or classical nonconstructive metatheorems are different statements.

This limitation is compatible with the reused constructive FTA proof. A single complex root of a polynomial can be supplied by a coherent Cauchy name without producing the discontinuous derivative/Puiseux coefficient data demanded here.
