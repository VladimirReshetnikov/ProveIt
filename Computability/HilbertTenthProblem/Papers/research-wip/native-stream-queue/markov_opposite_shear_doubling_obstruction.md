# Positive doubling masks cannot carry both full counter directions

No two continuous strictly positive normalized doubling masks can realize a full increment and a full decrement on a common real two-dimensional finite-trigonometric coordinate space, even at independently chosen positive scales. Thus replacing the full identity instruction by a restricted zero branch does not by itself permit both full counter directions at dilation two. Among integer dilations at least two, dilation three is sharp for the full increment/decrement pair.

This is a representation theorem. It gives neither a complete guarded universal program nor an arithmetic gate saving. It does not exclude a decrement with identity required only on the zero-counter line, nor a larger construction that changes coordinate spaces between instructions.

## 1. Opposite shears and a convexity proof

Let a,b be continuous strictly positive real masks of period one with

    a(x)+a(x+1/2)=b(x)+b(x+1/2)=2,

and use the normalized doubling transfer operator

    (T_a h)(y)=[a(y/2)h(y/2)+a((y+1)/2)h((y+1)/2)]/2.

Let f,g be independent real finite trigonometric polynomials. For positive lambda,mu and real s<0<t, suppose the full actions are

    T_a f=lambda f,    T_a g=lambda(g+s f),
    T_b f=mu f,        T_b g=mu(g+t f).                 (1)

For s=−1,t=1 these are decrement and increment in homogeneous counter coordinates. Arbitrary nonzero opposite step sizes are included.

Set

    theta=mu*t/(mu*t-lambda*s),
    c=theta*a+(1-theta)*b,
    nu=theta*lambda+(1-theta)*mu.

The denominator is positive and larger than the numerator, so 0<theta<1 and nu>0. Convex combination preserves continuity, strict positivity and normalization. The operator is linear in its mask. Moreover

    theta*lambda*s+(1-theta)*mu*t=0.

Therefore T_c acts as nu times the identity on the entire span of f,g. In the new basis F=−s*f, G=g, the first operator acts as

    T_a F=lambda F,    T_a G=lambda(G−F).

We have obtained a full scaled identity/decrement pair under positive normalized doubling masks. This contradicts the proved all-positive-scale theorem in `markov_distinct_scale_fixed_point_obstruction.md`, using its equal-scale corollary if nu=lambda. This proves impossibility of (1), including lambda=mu. No mask or function evaluation is used as a free arithmetic primitive. ∎

**Family consequence.** A family of such full scaled unipotent actions on a fixed finite-trigonometric two-coordinate space cannot have shear coefficients of both signs. Nor can it contain a zero shear and a nonzero shear: that is the identity/shear theorem after a basis rescaling. This statement concerns these full unipotent actions only; a rank-one zero-branch action is outside it.

## 2. Independent fixed-point check for distinct scales

The following calculation was derived independently before the shorter convexity proof. It verifies the sign mechanism directly and states all local assumptions.

Assume lambda!=mu, put delta=mu−lambda and kappa=(lambda*s−mu*t)/delta. Write F(z),G(z) for the Laurent polynomials, F2=F(z²), G2=G(z²), and F_o=(F(z)−F(−z))/2. Subtracting the two f equations and the two g equations gives

    (b−a)F_o=delta F2,
    (b−a)G_o=delta G2+(mu*t−lambda*s)F2.

Cross-multiplication and the a-equations imply the exact Laurent identity

    F G2−G F2=kappa F F2−lambda(kappa+s)F2².          (2)

Consequently R=G/F satisfies, as a rational identity,

    R(z²)−R(z)=kappa−lambda(kappa+s)F(z²)/F(z).       (3)

At z=1, let r>=0 be the finite vanishing order of F. The quotient F(z²)/F(z) is regular with value 2^r. A pole of R of order ell>0 would leave the nonzero leading multiplier 2^(−ell)−1 in (3), so R is regular there. Since kappa+s=mu(s−t)/delta, evaluation gives

    lambda*mu*(s−t)*2^r=lambda*s−mu*t,

or

    2^r=[t/(t−s)]/lambda+[−s/(t−s)]/mu.              (4)

Both weights are strictly positive and sum to one. With lambda!=mu, (4) puts lambda and mu strictly on opposite sides of 2^(−r).

This contradicts positivity of the common eigenfunction equations. In real coordinates write f(x)=A*x^r+O(x^(r+1)), A!=0. Normalization gives

    a(x+1/2)[f(x+1/2)−f(x)]=2[lambda f(2x)−f(x)].

The coefficient a(x+1/2) is bounded away from zero near zero, hence f(x+1/2)=O(x^r). Since f is finite trigonometric, its Taylor expansion there is B*x^r+O(x^(r+1)), allowing B=0. Dividing the equations for both masks by x^r and taking limits yields

    (lambda*2^r−1)/a(1/2)
       =(mu*2^r−1)/b(1/2)=(B/A−1)/2.                (5)

The positive denominators make the two numerators have the same sign, or both zero. Equation (4) instead makes their signs strictly opposite. This independently checks the distinct-scale obstruction. Only continuity of the masks is used: the Taylor expansion after division is justified by f itself, not by differentiating a mask.

The convexity proof covers equal scales without further local cases. Independently, at a common eigenvalue different from one the finite-eigenfunction uniqueness lemma forces a=b. At eigenvalue one, normalization and positivity make T_a a contraction in the uniform norm, whereas (1) would give T_a^n g=g+n*s*f, whose norm is unbounded. These also close the equal-scale case.

## 3. Sharp dilation-three realization

Let theta=2*pi*x and use coordinates (sin(theta),sin(2theta)). At dilation three define

    a_−=1+[4cos(2theta)−2cos(theta)+2cos(4theta)]/5,
    a_+=1+[4cos(2theta)+2cos(theta)+2cos(4theta)]/5.

All nonconstant Fourier frequencies are 1,2,4, none divisible by three, so the masks are normalized. The sine-block coefficient formula is a_(3k−m)−a_(3k+m). Directly it gives

    T_(a_−)=(1/5)*[[1,−1],[0,1]],
    T_(a_+)=(1/5)*[[1, 1],[0,1]]

on the full two-sine span. The coefficient bound |m+j|<=6 excludes output frequencies above two; oddness of sine times an even mask removes the constant mode. Thus no output leaves that span. For u=cos(theta), the respective mask numerators are

    (4u²−1)²+2(1−u),
    (4u²−1)²+2(1+u).

The first is at least 1/2: use the second summand for u<=3/4 and the square for u>=3/4. The second follows by u↦−u. Thus both masks are strictly positive. They are phase translates of one another, so their positivity bounds coincide.

The lower and upper results prove minimum allowed integer dilation **three** for the full increment/decrement pair, allowing independent positive scales. The upper example uses a common scale 1/5, which is allowed in that class. No denominator minimum over arbitrary encodings is asserted.

## 4. Provenance and remaining scope

The root author read the complete frozen all-scale proof, its equal-scale dependency, and the full 192-line sine lift as mathematical text. Pins are:

| WIP dependency | SHA-256 |
|---|---|
| `markov_distinct_scale_fixed_point_obstruction.md` | `4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb` |
| `markov_doubling_mixed_subspace_boundary.md` | `baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063` |
| `markov_sine_lift.md` | `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2` |

Root derived the distinct-scale threshold argument; both peers independently checked it. Pascal supplied the shorter convex-combination proof. Root and Pascal independently observed the phase-translated dilation-three increment mask. Final complete-note reviews are separate records.

No claim about arbitrary continuous coordinates or smooth flat functions follows from this finite-Fourier theorem. Nonnegative masks with zeros, unnormalized operators, state-dependent coordinates, branch guards and restricted-line actions remain separately scoped. In particular, excluding both full counter directions does not establish nonuniversality of every doubling-based computational substrate.

No supplied, archived, frozen or predecessor helper, builder or source array was executed or imported. This is a proof-only result with metadata binding, not a numerical search. No earlier theorem is refuted or silently altered. The universal Diophantine arithmetic frontier remains 84 operations.
