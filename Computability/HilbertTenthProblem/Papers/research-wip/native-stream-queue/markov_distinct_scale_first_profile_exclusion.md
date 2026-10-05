# The first distinct-scale doubling identity/decrement profile is impossible

There is no full-action pair of strictly positive normalized continuous doubling masks at distinct positive scales on the first Fourier profile left by the preceding boundary theorem: common eigenvector frequency two and generalized eigenvector frequency three. The proof includes all shared-factor and removable-pole cases. It forces an exact zero of the identity mask.

Together with the preceding all-size necessary condition, this excludes every two-dimensional real finite-trigonometric coordinate space of maximum frequency at most five. It is not a theorem excluding all distinct-scale pairs and gives no new integer compiler or arithmetic saving.

## 1. Exact full-action hypothesis

For a continuous real mask a of period one, use

    (T_a h)(y)=[a(y/2)h(y/2)+a((y+1)/2)h((y+1)/2)]/2.

Suppose a,b are strictly positive and normalized:

    a(x)+a(x+1/2)=b(x)+b(x+1/2)=2.

Let f,g be real, linearly independent, finite trigonometric polynomials, and suppose

    T_a f=lambda*f,       T_a g=lambda*g,
    T_b f=mu*f,           T_b g=mu*(g-f),             (1)

on their whole span, where lambda and mu are distinct positive numbers. Thus the matrices in the ordered basis (f,g) are lambda*I and mu*[[1,-1],[0,1]].

Write z=exp(2*pi*i*x). The predecessor theorem proves that some integer m>=1 satisfies

    M_f=2m,  M_g=3m,  O_g=O_f+2m,  1<=O_f<=m,       (2)

where M_h is the largest positive Fourier exponent and O_h is the largest positive odd Fourier exponent. Reality supplies the corresponding nonzero negative coefficients. The present theorem excludes m=1, so its exact profile is

    M_f=2,  O_f=1,  M_g=3,  O_g=3.                  (3)

No assumption is made that the masks initially have finite Fourier expansions, that f and g are relatively prime, that their common factor has any prescribed roots, or that the Laurent quotients below can be evaluated at a zero denominator.

## 2. Continuity forces the masks to be cubic Laurent polynomials

Put h_e(z)=(h(z)+h(-z))/2 and h_o(z)=(h(z)-h(-z))/2. Normalization gives

    (T_a h)(2x)=h_e(z)+(a(x)-1)*h_o(z).              (4)

Write

    f(z)=C*z^2+B*z+c+conj(B)*z^(-1)+conj(C)*z^(-2),

where B,C are nonzero and c is real. Then

    f_o(z)=B*z+conj(B)*z^(-1).

Its only nonzero roots are the two simple roots of

    z^2=-conj(B)/B.                                 (5)

Both roots lie on the circle.

Subtracting the two equations for f in (1) gives

    (b-a)*f_o=(mu-lambda)*f(z^2).                    (6)

At each root in (5), continuity and mu-lambda!=0 imply f(z^2)=0. Equation (4) for a then implies f_e(z)=0 there as well. Thus f_o divides both f(z^2) and f_e in C[z,z^(-1)]. This is ordinary Laurent-polynomial divisibility: multiply by powers of z and use the two distinct nonzero roots. It does not discard a pole or divide by zero on the circle.

Consequently the rational expression

    a-1=[lambda*f(z^2)-f_e]/f_o                    (7)

is an exact Laurent polynomial. It agrees with the actual mask away from the two roots, and continuity extends the equality to them. Its greatest exponent is exactly three and its least is exactly minus three, because lambda,B,C are nonzero. The quotient is odd under z -> -z; it is real on the circle because a is real. Therefore

    a(z)=1+alpha*z+conj(alpha)*z^(-1)
            +beta*z^3+conj(beta)*z^(-3).             (8)

The same argument also makes b a Laurent polynomial of this form, although no coefficient of b will be needed.

This reduction covers every allowed gcd of f and g: neither a factor cancellation between f and g nor a special location of their common roots changes (5)–(8).

## 3. The eigenvalue equations force a zero of a

For finite Laurent polynomials a,h, the coefficient of z^j in T_a h is

    sum_(k+l=2j) a_k*h_l.                           (9)

This follows directly from averaging the two preimages; odd total exponents cancel.

Write g_3 for the nonzero coefficient of z^3 in g. In (8), both a and g have maximum exponent three. The only contribution to frequency three in T_a g comes from a_3*g_3. Thus

    lambda*g_3=beta*g_3,

and hence beta=lambda. Now compare frequency two in T_a f. The only contributing term is a_3*f_1, so

    lambda*C=lambda*B.

Since lambda!=0, C=B. Rename this common coefficient A, which is nonzero.

At a root in (5), now with B=A, the even part is

    f_e(z)=A*z^2+c+conj(A)*z^(-2)=c-A-conj(A).

Its vanishing, already proved in Section 2, gives c=A+conj(A). We have therefore proved

    f(z)=A*z^2+A*z+A+conj(A)
                   +conj(A)*z^(-1)+conj(A)*z^(-2).  (10)

Comparing frequency one in T_a f=lambda*f gives

    lambda*A=A+alpha*A+lambda*conj(A).

Define t=conj(A)/A, so |t|=1. Then

    alpha=lambda-1-lambda*t.                        (11)

The constant coefficient equation is

    lambda*(A+conj(A))
        = A+conj(A)+alpha*conj(A)+conj(alpha)*A.

Substituting (11), using real lambda and lambda!=0, reduces this to

    t*conj(A)+conj(t)*A=0.

Multiplication by A*conj(A), which is nonzero, gives

    A^3+conj(A)^3=0,

or equivalently

    t^3=-1.                                        (12)

All algebraic cases are therefore exactly

    t=-1,  t=omega,  or t=conj(omega),
    omega=exp(i*pi/3).                              (13)

By (8), beta=lambda, and (11), the mask on the circle is

    a(z)=1+2*Re[(lambda-1-lambda*t)*z+lambda*z^3].
                                                        (14)

If t=-1, take z=omega. Since Re(omega)=1/2 and omega^3=-1,

    a(omega)=1+(2*lambda-1)-2*lambda=0.

If t=omega, again take z=omega. The identity
(1-omega)*omega=1 gives

    Re[(lambda-1-lambda*omega)*omega]=lambda-1/2,

so a(omega)=1+2*(lambda-1/2)-2*lambda=0.

If t=conj(omega), use z=conj(omega) and the conjugate calculation. Again a(z)=0.

Each exhaustive case contradicts strict positivity. This proves the exclusion. No condition on a merely formal generic coefficient, no numerical root approximation, and no omitted repeated-root case is involved: f_o has two simple roots because A!=0. ∎

## 4. Consequences and remaining scope

**Corollary.** Under the exact full-action hypothesis (1), every surviving finite-trigonometric pair has maximum frequency at least six.

Indeed, the predecessor theorem makes the largest frequency in span(f,g) equal to 3m. The present theorem rules out m=1. Thus m>=2 and 3m>=6. The first still-unresolved profile is m=2, necessarily

    M_f=4, O_f=1, M_g=6, O_g=5,

because O_f is odd and at most two. No claim of existence for this profile is made.

The contradiction already forces a zero of a before using positivity of b. It covers initially nontrigonometric continuous masks and every Laurent common-factor case permitted by (3). It does not cover nontrigonometric coordinate functions, unnormalized operators, or action equalities required only on a selected counter ray or zero-test line.

A nonnegative mask with the forced zero is not a counterexample to this theorem: strict positivity is the stipulated interface. Conversely, no nonnegative-mask full pair is being asserted to exist. The theorem does not settle the independent-scale problem at all frequencies, and even a future distinct-scale representation would leave its word-dependent normalization, program control, ordinary input, and unbounded history to be accounted separately.

## 5. Inert provenance and method

The following predecessor note was read in full as text:

| Note under Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue | SHA-256 |
|---|---|
| markov_distinct_scale_fourier_boundary.md | 23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee |

Its Theorem 1 supplies only (2) and the nonconstant shear-basis interface. Theorem 2's common-factor lower bound motivates the task, but is not needed as a premise for the present exclusion. Equations (4)–(14) constitute a separate direct proof including the exceptional factors.

No helper, saved array, supplied program, archived program, frozen predecessor, copied program, or builder was executed or imported. No numerical search was used. Only this new proof text was authored under /tmp; no repository or Git mutation was performed.
