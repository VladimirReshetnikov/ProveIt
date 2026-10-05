# A Fourier boundary for independently scaled doubling identity and decrement actions

A normalized positive doubling identity/decrement pair with distinct positive scales, if it exists on a common two-dimensional real finite-trigonometric space, has a very restricted Fourier shape. In a shear basis its common eigenvector has maximum frequency 2m, its generalized eigenvector has maximum frequency 3m, and the two Laurent polynomials have a common factor of width at least 3m. In particular, maximum frequency at most two, coprime Laurent coordinates, and a rank-two top-frequency projection are each impossible.

This is a necessary-condition theorem, not a general nonexistence theorem or a construction. It narrows the distinct-scale question left open by the committed common-scale note. It supplies no integer compiler, counter history, arithmetic saving, or universality claim. No program, saved source array, supplied helper, or predecessor helper was executed or imported.

## 1. Exact interface and conventions

Let a,b be continuous, strictly positive real functions of period one satisfying

    a(x)+a(x+1/2)=b(x)+b(x+1/2)=2.

For either mask define

    (T_a h)(y)=[a(y/2)h(y/2)+a((y+1)/2)h((y+1)/2)]/2.

Let f,g be linearly independent real finite trigonometric polynomials, and put V=span_R(f,g). Assume, on this entire real span,

    T_a f = lambda*f,       T_a g = lambda*g,
    T_b f = mu*f,           T_b g = mu*(g-f),          (1)

where lambda and mu are distinct positive real numbers. Thus the two matrices in this fixed ordered basis are lambda*I and mu*D, with D=[[1,-1],[0,1]]. The full-space action is part of the hypothesis; a relation imposed only on an admissible counter ray or a zero-test line is different.

Write z=exp(2*pi*i*x), and identify each finite trigonometric polynomial with its Laurent polynomial in C[z,z^(-1)]. For a Laurent polynomial h let

    h_e(z)=[h(z)+h(-z)]/2,
    h_o(z)=[h(z)-h(-z)]/2.

Normalization gives the pointwise identity

    (T_a h)(2x)=h_e(z)+(a(x)-1)*h_o(z).                (2)

Although the masks need not be trigonometric polynomials, eliminating them below produces identities between Laurent polynomials. Equality on the circle therefore gives exact Laurent identities.

For a nonconstant real h let M_h be its greatest positive Fourier exponent. Reality gives nonzero coefficients at both M_h and -M_h. If h_o is nonzero, let O_h be its greatest positive odd exponent; its extreme odd exponents are O_h and -O_h.

The hypotheses imply that lambda is not one: strict positive normalized averaging fixes only constants. Indeed, a real fixed function attaining its maximum forces both preimages to attain the same maximum, and iteration gives a dense set of maximizers. Thus a two-dimensional fixed space is impossible. Consequently neither f nor g is constant. Neither odd part can vanish: otherwise (2) would halve a nonconstant function's largest frequency while its nonzero eigenvalue preserves that frequency. The same fixed-function argument for b, together with the sup-norm contraction, in fact gives 0<lambda,mu<1, though that sharper range is not needed below.

## 2. The exact 2m/3m frequency constraint

**Theorem 1.** Under (1), there is an integer m>=1 such that

    M_f=2m,        M_g=3m,
    O_g=O_f+2m,    1<=O_f<=m.                         (3)

Here O_f and O_g are odd. If m is odd, O_f=m and O_g=3m; if m is even, O_f<m.

**Proof.** Put delta=mu-lambda, which is nonzero. Subtract the two mask equations for f and g:

    (b-a)*f_o = delta*f(z^2),
    (b-a)*g_o = delta*g(z^2)-mu*f(z^2).

Eliminating b-a gives

    delta*[f(z^2)*g_o-g(z^2)*f_o]
        = -mu*f(z^2)*f_o.                            (4)

The two a-equations also give

    lambda*[f(z^2)*g_o-g(z^2)*f_o]
        = f_e*g_o-g_e*f_o.

Therefore

    delta*(f_e*g_o-g_e*f_o)
        = -mu*lambda*f(z^2)*f_o.                     (5)

The right side of (5) has greatest positive exponent exactly 2M_f+O_f. If M_g<=M_f, the left side has greatest exponent at most M_f+M_g<=2M_f. This is impossible because O_f>=1. Hence M_g>M_f.

For either h=f or h=g the a-equation gives the same rational Laurent function

    a-1 = [lambda*h(z^2)-h_e]/h_o

on the circle away from the finite zero set of h_o. These two rational functions agree identically. Their orders of growth at infinity are respectively 2M_f-O_f and 2M_g-O_g: the numerator's leading exponent is exactly 2M_h because lambda is nonzero. Thus

    k := 2M_f-O_f = 2M_g-O_g.                        (6)

Since O_g<=M_g, k>=M_g. If M_f were odd, then O_f=M_f and k=M_f, contradicting M_g>M_f. Thus M_f is even, and f_e has greatest exponent exactly M_f.

In (5), f_e*g_o has greatest exponent M_f+O_g. The other product has greatest exponent at most M_g+O_f. Their difference is strictly ordered, because (6) gives

    (M_f+O_g)-(M_g+O_f)=M_g-M_f>0.

Consequently the leading term of f_e*g_o cannot cancel. Comparing the two sides of (5) now yields O_g-O_f=M_f. Combining this with O_g-O_f=2(M_g-M_f) gives 2M_g=3M_f. Write M_f=2m and M_g=3m. Then O_g=O_f+2m and O_g<=3m imply O_f<=m.

If m is odd, M_g=3m is odd, so O_g=M_g and O_f=m. If m is even, O_f is odd and cannot equal m. This proves (3). ∎

**Corollary 1.** No such pair exists on a space whose maximum Fourier frequency is at most two. More generally, let M be the maximum frequency occurring in V. If the real-linear projection of V onto the two coefficients of cos(2*pi*M*x) and sin(2*pi*M*x) has rank two, then no such pair exists.

For the latter statement, the rank-two projection on a two-dimensional V is injective, so every nonzero vector of V has frequency M. Theorem 1 requires a nonzero common eigenvector of strictly lower frequency. Thus any remaining candidate must have a rank-one top-frequency projection, and its common eigenvector lies in that projection's kernel. This condition is independent of a chosen presentation of V.

## 3. A large common Laurent factor is necessary

Define odd decimation by

    O(h)(w)=sum_j h_(2j+1)*w^j,

so h_o(z)=z*O(h)(z^2). Both O(f) and O(g) are nonzero. Odd decimation does not generally preserve real-valuedness on the circle: the endpoint exponents of O(f) are centered at -1/2. Reality is used for f and g, not asserted for their decimations.

**Theorem 2.** Let d be a greatest common divisor of f and g in C[z,z^(-1)], defined up to a nonzero scalar times a power of z. For any nonzero Laurent polynomial h define its width by

    width(h)=largest exponent-smallest exponent.

Then, with the notation of Theorem 1,

    width(d) >= 2M_f-O_f = 4m-O_f >= 3m.             (7)

In particular, f and g cannot be relatively prime in the Laurent ring.

**Proof.** Dividing (4) in the rational-function field, and then writing w=z^2, gives

    g(w)/f(w) - O(g)(w)/O(f)(w)
        = mu/(mu-lambda) =: c.                      (8)

This is a rational identity; it makes no pointwise division assertion at a zero of f or f_o. Clearing denominators,

    g*O(f)=f*[O(g)+c*O(f)].                          (9)

Write f=d*p and g=d*q with p,q relatively prime in the Laurent ring. Equation (9) implies p divides O(f). Hence width(p)<=width(O(f)). The extreme exponents of O(f) are (-O_f-1)/2 and (O_f-1)/2, so width(O(f))=O_f. Width is additive under multiplication of nonzero Laurent polynomials, while reality gives width(f)=2M_f. Therefore

    2M_f-width(d)=width(p)<=O_f,

which proves (7). ∎

The common factor in (7) is an algebraic Laurent factor. The theorem does not say that it has a root on the real circle, that division by it preserves a trigonometric coordinate space, or that dividing it out preserves either normalized transfer action. Those would be additional assertions requiring separate proof.

## 4. What this changes, and what remains open

The standard mixed identity-only example in the predecessor note has maximum frequency one, so Corollary 1 rules out a second decrement action at a distinct positive scale on that same space; the identity block itself remains valid. The new result covers every real mixed-frequency space through frequency two and excludes top-frequency-rank-two or coprime encodings at every frequency. A first possible Fourier profile has m=1: f has frequency two with odd part at frequency one; g has frequency three with odd part at frequency three; the common Laurent divisor has width at least three.

No example with that profile is supplied, and the necessary conditions alone do not establish existence. Conversely, they do not exclude all high-common-factor spaces. The exact remaining task is to solve the rational identities (4), (5), and (8) with the required real coefficients and two continuous strictly positive normalized masks, or prove that these positivity and divisibility conditions are incompatible. No generic or numerical surrogate is being asserted to solve this task.

Even an explicit distinct-scale pair would have a word-dependent product of action scales. A uniform integer representation of that product, the ordinary-input interface, zero tests, program selection, and unbounded history would still require separate paid constructions. A finite Fourier representation is not permission to evaluate sine or cosine as a free integer primitive.

## 5. Inert provenance and exact review scope

The committed note below was read in full. Its normalized two-preimage identity and fixed-function argument are restated above; its Remark 2 explicitly leaves different action scales open.

| Path relative to Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue | SHA-256 |
|---|---|
| markov_doubling_mixed_subspace_boundary.md | baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063 |

That note was added in commit 39dd25194. The earlier harmonic-boundary note was also read as text in this investigation; its SHA-256 is 6f370b742f1fb5126a17677fb8ef7eb05a61f8cd0ebbcbb8b42f53bb2915c731. No new claim here depends on its external citations or any supplied computation.

The proofs in Sections 2–3 are symbolic, all-size arguments. There is no numerical search, source-array evaluation, helper execution, manuscript build, or repository mutation in this packet. The result is a boundary for the exact full-action interface (1), not for arbitrary continuous encodings, unnormalized masks, or actions required only on selected admissible inputs.

