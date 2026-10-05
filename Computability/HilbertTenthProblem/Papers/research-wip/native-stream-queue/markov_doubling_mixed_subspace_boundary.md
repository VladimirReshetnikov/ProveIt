# Mixed trigonometric coordinates do not realize the common-scale identity/decrement pair at dilation two

**A common finite trigonometric coordinate space cannot carry both I/q and D/q under strictly positive normalized doubling masks**, where q is any nonzero common real scale and D is the nonidentity decrement shear. This extends the earlier pure-sine obstruction to arbitrary mixtures of finitely many Fourier frequencies, including constant terms and non-even masks.

There is an important distinction: a two-dimensional scaled identity block by itself is possible. Remark 1 below gives an explicit rational q=3 example. The obstruction concerns the common-scale pair of actions, not a general bound on eigenspace dimension.

This is a self-contained proof-only representation result. It constructs no universal program, integer history or arithmetic gate saving. All predecessor material was read inertly; no supplied, archived, committed or frozen program or source array was executed or imported.

## 1. Normalization and the odd half-period component

Let a be a continuous real function of period one, and define

    (T_a f)(y) = [a(y/2)f(y/2)
                   +a((y+1)/2)f((y+1)/2)]/2.

Normalization T_a 1=1 is exactly

    a(x)+a(x+1/2)=2.                                    (1)

For any periodic function f set

    f_e(x)=[f(x)+f(x+1/2)]/2,
    f_o(x)=[f(x)-f(x+1/2)]/2.

The literal two-preimage formula and (1) give

    (T_a f)(2x)=f_e(x)+(a(x)-1)f_o(x).                   (2)

Consequently, for any two continuous normalized masks a,b,

    ((T_a-T_b)f)(2x)=(a(x)-b(x))f_o(x).                 (3)

A finite trigonometric polynomial means a finite linear combination of the integer characters exp(2*pi*i*m*x). Real polynomials may equivalently be written with real sine, cosine and constant coefficients. No restriction to consecutive frequencies, zero mean, even masks or rational coefficients is imposed.

## 2. A nonconstant finite eigenfunction determines its mask at its eigenvalue

**Lemma.** Suppose f is a nonconstant finite trigonometric polynomial, lambda is nonzero, and T_a f=lambda f for a continuous normalized mask. Then f_o is not identically zero. Moreover, if another continuous normalized mask b satisfies T_b f=lambda f with the same eigenvalue, then a=b everywhere.

**Proof.** If f_o=0, every nonzero Fourier frequency of f is even. Equation (2) reduces to T_a f(y)=f(y/2). Let M>0 be the greatest absolute frequency of f. The left side, under this formula, has greatest absolute frequency M/2, whereas lambda f has greatest absolute frequency M because lambda is nonzero. This is impossible. Thus f_o is a nonzero finite trigonometric polynomial.

Such a polynomial has only finitely many zeros on the circle: multiplication by a suitable power of z=exp(2*pi*i*x) turns it into a nonzero ordinary polynomial, whose roots are finite. Subtract the two eigenvalue equations and use (3). The masks agree off those finitely many zeros of f_o. Their continuity extends equality to those zeros as well. This proves the lemma. No division at a zero of f_o is used. ∎

The lemma requires neither positivity nor a finite Fourier expansion of the masks. Their continuity and normalization suffice. The finite Fourier assumption is on the shared eigenfunction.

## 3. Strict positivity handles the constant eigenvector boundary

**Lemma.** If a is strictly positive and normalized, every continuous function fixed by T_a is constant.

**Proof.** First let f be real and choose y0 at which it attains its maximum M. Normalization makes T_a f(y0) a convex combination of the two preimage values, with both coefficients strictly positive. Since T_a f(y0)=f(y0)=M and both values are at most M, both equal M. Repeat this argument at those preimages. Every point

    (y0+j)/2^n modulo 1,       0<=j<2^n,

therefore has value M. These inverse-orbit grids are dense, so continuity makes f identically M. For complex f apply the real argument to its real and imaginary parts. ∎

In particular the eigenvalue-one space of continuous functions has dimension one. This proof uses only positive averaging and dense inverse orbits, with no external irreducibility or spectral theorem.

## 4. The common-scale family obstruction

Let V be any real vector space of finite trigonometric polynomials, of finite dimension d>=2. Let a and b be continuous, strictly positive normalized doubling masks. Suppose

    T_a|V = lambda*I,
    T_b|V = lambda*M,                                   (4)

in one fixed basis of V, with lambda a nonzero real number, M a real nonidentity matrix, and M having eigenvalue one. Then (4) is impossible.

If lambda=1, the first equation fixes every member of V. Section 3 restricts V to the one-dimensional constants, contradicting d>=2.

If lambda is not one, choose a nonzero real eigenvector v of M with eigenvalue one and let f be its nonzero encoded function in V. Then both T_a f and T_b f equal lambda f. This f cannot be constant: every normalized operator fixes constants, while lambda differs from one. Section 2 therefore forces a=b. The two operators are identical, so their restrictions give lambda*M=lambda*I. Since lambda is nonzero and the encoding is injective, M=I, again a contradiction.

For the requested two-coordinate family take

    I = [[1,0],[0,1]],
    D = [[1,-1],[0,1]],
    lambda = 1/q.

The shared eigenvector is (1,0). Thus no arbitrary mixed-frequency two-dimensional trigonometric basis can realize both I/q and D/q at dilation two with the stated normalized positive masks. Rescaling, reordering or mixing the coordinate basis does not change the conclusion. The result even allows the masks themselves to be nontrigonometric continuous functions.

Combined with the already proved dilation-three, q=5 construction on the standard sine coordinates, this establishes minimum integer dilation three for **this full-action, common-scale identity/decrement family among finite trigonometric coordinate encodings**. The allowed dilation class begins at two, as in the preceding notes. This does not extend the earlier q=5 denominator minimum to arbitrary encodings.

## 5. Numbered boundary examples and remaining scope

**Remark 1 (a stronger identity-only exclusion would be false).** Consider the proposed stronger statement “doubling cannot have a nonzero two-dimensional finite-trigonometric identity block.” It is false. Put theta=2*pi*x and

    a(x)=1+(2/3)cos(theta),
    f(x)=sin(theta),
    g(x)=cos(theta)-1/2.

The mask has rational trigonometric coefficients, is normalized because its cosine changes sign after a half-period, and satisfies a>=1/3. Directly from (2) and the double-angle identities,

    T_a sin(theta)=(1/3)sin(theta),
    T_a cos(theta)=(1/3)(1+cos(theta)),
    T_a g=(1/3)g.

Thus V=span(f,g) is a two-dimensional I/3 block. The constant term mixed into g matters; the functions remain linearly independent and V does not contain the constant function. More generally, for any nonzero real c with |c|<1/2, the same construction uses a=1+2c*cos(theta) and g=cos(theta)-c/(1-c), with eigenvalue c. For rational c all displayed real trigonometric coefficients are rational.

This is counterevidence to that proposed overgeneralization, not a defect in the frozen earlier note, which expressly restricted its theorem to spans of individual sine harmonics and left arbitrary mixed subspaces open. The example realizes identity only; it does not supply the missing decrement action.

**Remark 2 (the same-eigenvalue premise is essential to this argument).** The two normalized positive masks 1+(2/3)cos(theta) and 1+(1/2)cos(theta) both have sin(theta) as an eigenfunction, with distinct eigenvalues 1/3 and1/4. Thus Section 2 cannot be used to identify masks from a shared eigenfunction alone. This note does not settle identity/decrement realizations with independently chosen action scales, nor does it silently convert their word-dependent scale to the common denominator used in the current substrate.

Other exclusions from the theorem are arbitrary nontrigonometric coordinate functions; state-dependent encodings; unnormalized operators; and action requirements imposed only on selected admissible inputs instead of the whole invariant vector space. In particular, a zero-test instruction may require identity only on its zero-counter line. Replacing the full identity matrix contract by such a restricted action is a different problem and is not refuted here.

The rational q=3 identity mask is only a finite Fourier-list construction; it does not license cosine evaluation as a free integer primitive. Since the pair is impossible at doubling under (4), this result provides no new mask/counter arithmetic schedule. The previously accounted positive-guard counters and the established84-operation universal construction remain unchanged. Lower dilation or a single identity block would not by itself pay a variable word, integer normalization, ordinary-input binding, guard selection or an unbounded history.

## 6. Inert provenance

The following notes were read completely as mathematical text; none of their helpers or saved arrays was run:

| Note | SHA-256 |
|---|---|
| `markov_doubling_harmonic_boundary.md` | `6f370b742f1fb5126a17677fb8ef7eb05a61f8cd0ebbcbb8b42f53bb2915c731` |
| `markov_sine_lift.md` | `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2` |
| `markov_mask_matrix_lift.md` | `5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6` |

The literal normalized transfer identity is restated and proved in Section 1; the two new lemmas and family obstruction are proved in Sections 2–4. The inherited sine-lift note supplies only the explicit dilation-three realization used for the minimum-dilation corollary. No external infinite-dimensional spectral claim, universality theorem, numerical experiment, predecessor execution or repository mutation is part of this proof-only result.
