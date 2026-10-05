# A fixed-point obstruction to every finite-Fourier unequal-scale doubling pair

There is no common two-dimensional real finite-trigonometric coordinate
space on which two strictly positive normalized doubling masks act as
`lambda I` and `mu D`, where `D=[[1,-1],[0,1]]` and lambda,mu are distinct
positive scales. This closes the unequal-scale finite-Fourier question
left by the earlier degree and first-profile boundaries. Together with
the accepted common-scale theorem, it excludes this exact full-action
doubling interface at every pair of positive scales.

The obstruction is local at the fixed point of doubling. It does not
divide out a common coordinate factor, assume that an algebraic gcd has
unit-circle roots, or infer an all-degree assertion from finite tests.
It supplies no cheaper integer compiler and no universal arithmetic bound.

## 1. Exact statement and operator convention

Let a,b be continuous, strictly positive real functions of period one,
normalized by

    a(x)+a(x+1/2)=b(x)+b(x+1/2)=2.

For either mask define

    (T_a h)(y)=[a(y/2)h(y/2)+a((y+1)/2)h((y+1)/2)]/2.

Suppose f,g are independent real finite trigonometric polynomials and
lambda,mu are distinct positive real numbers. The prohibited full actions
are

    T_a f=lambda f,       T_a g=lambda g,
    T_b f=mu f,           T_b g=mu(g-f).                 (1)

These equations are on the entire common span. They are not conditions
only along an admissible counter ray or a zero-test line. No hypothesis
that a or b has a finite Fourier expansion is imposed.

Write z=exp(2 pi i x), identify f,g with nonzero Laurent polynomials
F(z),G(z), and put F2=F(z^2), G2=G(z^2). For either Laurent polynomial H,
let H_o(z)=(H(z)-H(-z))/2 and H_e(z)=(H(z)+H(-z))/2. Normalization gives

    (T_a h)(2x)=H_e(z)+(a(x)-1)H_o(z).                 (2)

## 2. An exact rational coboundary identity

Set delta=mu-lambda and kappa=mu/delta; both are nonzero. Subtracting the
two mask equations for f and g gives, pointwise on the circle,

    (b-a)F_o=delta F2,
    (b-a)G_o=delta G2-mu F2.

Eliminate b-a by cross-multiplication:

    F_o G2-G_o F2=kappa F2 F_o.                      (3)

The a-equations and H=H_e+H_o also give

    F-lambda F2=(2-a)F_o,
    G-lambda G2=(2-a)G_o.

Consequently, without dividing by F_o, by a mask difference, or by a
common coordinate factor,

    F G2-G F2
      =(2-a)(F_o G2-G_o F2)
      =kappa F2(F-lambda F2).                        (4)

Both sides of (4) are Laurent polynomials. Equality on the circle makes
it a Laurent identity. In the rational-function field C(z) put R=G/F;
F and F2 are nonzero polynomials, so dividing (4) there is legitimate:

    R(z^2)-R(z)=kappa[1-lambda F(z^2)/F(z)].           (5)

This is a rational identity, not a pointwise division assertion at a zero.

## 3. The fixed point determines the scale

Since a nonzero Laurent polynomial is analytic near z=1, there is a finite
integer r>=0 and an analytic function U with U(1)!=0 such that

    F(z)=(z-1)^r U(z).

This includes the case F(1)!=0, for which r=0. Repeated zeros and every
possible common factor of F,G are included. The quotient

    F(z^2)/F(z)=(z+1)^r U(z^2)/U(z)

is analytic near 1 and takes the nonzero value 2^r there. Thus the right
side of (5) is analytic near 1.

The meromorphic function R cannot have a pole there. If it had pole
order s>=1 and leading term C(z-1)^(-s), C!=0, the leading term of
R(z^2)-R(z) would be

    C(2^(-s)-1)(z-1)^(-s),

which is nonzero and contradicts analyticity of the right side. Hence
R is regular at 1. Taking the value at this fixed point in (5) gives

    0=kappa(1-lambda 2^r),  hence lambda 2^r=1.       (6)

In particular, the argument proves that G vanishes to at least order r
at 1; this is a conclusion, not a permissible cancellation assumed in
advance. No unit-circle property of the earlier Laurent gcd was used.

## 4. Strict positivity contradicts that scale

In the real coordinate near x=0, analyticity and the nonzero derivative
of exp(2 pi i x) give a nonzero real coefficient A with

    f(x)=A x^r+O(x^(r+1)),
    f(2x)=2^r A x^r+O(x^(r+1)).

Equation (6) therefore implies

    lambda f(2x)-f(x)=O(x^(r+1)).                   (7)

Rewrite the first normalized eigenfunction equation in (1) directly:

    a(x+1/2)[f(x+1/2)-f(x)]
       =2[lambda f(2x)-f(x)].                       (8)

Strict positivity and continuity give a(1/2)>0, so a(x+1/2) is bounded
away from zero near x=0. Equations (7)–(8) force

    f_o(x)=[f(x)-f(x+1/2)]/2=O(x^(r+1)).

But the common-eigenvector mask difference from Section 2 is

    (b(x)-a(x)) f_o(x)=(mu-lambda) f(2x).            (9)

Its left side is O(x^(r+1)), because b-a is bounded near zero. Its right
side has nonzero leading coefficient (mu-lambda)2^r A at order r. This
is impossible. Dividing by x^r for nonzero real x and taking the limit
makes the contradiction explicit. The same proof covers r=0: the left
side tends to zero while the right side tends to a nonzero constant.

This proves the unequal-scale theorem in all finite Fourier degrees. ∎

## 5. Consequences and precise remaining interfaces

**Corollary.** No pair of continuous strictly positive normalized doubling
masks realizes a full scaled identity and a full scaled decrement on a
common two-dimensional real finite-trigonometric space, at any positive
scales, equal or unequal.

For unequal scales the proof is above. For equal scales the accepted
common-scale theorem applies: a shared nonconstant finite-trigonometric
eigenvector at the same nonzero eigenvalue determines the normalized
mask uniquely. The eigenvalue-one case is separately excluded by the
strict-positive averaging maximum principle. Thus the two masks cannot
have the different full actions I and D.

The earlier necessary conditions M_f=2m, M_g=3m and the large common
Laurent factor were correct. Their surviving profiles, including
(M_f,O_f,M_g,O_g)=(4,1,6,5), are now excluded by the new argument; the
earlier notes retain their original explicitly bounded scope. The
first-profile proof remains a separate valid exclusion, not a false
claim requiring correction.

**Remark 1 (identity alone remains possible).** The mask
`a(x)=1+(2/3)cos(2 pi x)` acts as I/3 on the span of
`sin(2 pi x)` and `cos(2 pi x)-1/2`. This valid example is retained to
prevent reading the corollary as an exclusion of finite identity blocks.
The impossible interface asks for an additional full decrement action
on that same coordinate space, possibly at a different positive scale.

**Local smooth corollary.** Under (1) and the same mask hypotheses, even
if f,g are merely smooth real periodic functions, the common eigenvector
f must be flat at x=0: every derivative there is zero. This is a necessary
condition for a smooth escape, not an existence claim.

Indeed, (4) holds pointwise without Fourier assumptions. Suppose f instead
has finite vanishing order r>=0, with leading term A x^r. If g has finite
order s<r and leading term B x^s, the left side of (4) has nonzero leading
term AB(2^s-2^r)x^(r+s), while the right side is O(x^(2r)), a contradiction.
If g has finite order s>=r, the left side is O(x^(2r+1)); for s=r its
leading terms cancel. The same bound holds when g is flat, by its Taylor
estimates to every finite order. The coefficient of x^(2r) on the right
then forces lambda 2^r=1. Equations (7)–(9) apply unchanged and contradict
finite order r. This separate division-free argument also corroborates
all repeated-zero cases of the finite-Fourier proof.

The main proof uses finite-order analyticity and meromorphicity near the
fixed point; the local corollary uses finite-order Taylor estimates. No
obstruction to all smooth flat encodings or arbitrary continuous coordinate
functions is proved. The result also does not address nonnegative masks
that vanish, unnormalized operators, state-dependent coordinate charts,
or actions imposed only on a selected line rather than the full span.

In particular, strict positivity at x=1/2 is substantive in (8): allowing
that value to vanish invalidates the division by a locally nonzero
coefficient. The theorem does not assert existence of a nonnegative-mask
counterexample. It preserves all separate obligations for a paid ordinary
integer loader, zero tests, program selection and unbounded history.
No gate count or universal construction is improved by this obstruction.

## 6. Provenance, independent challenge and method

The following frozen notes were read as inert text. The first supplies
the equal-scale half of the corollary; neither the degree classification
nor the first-profile theorem is a premise of Sections 2–4.

| WIP note | SHA-256 |
|---|---|
| `markov_doubling_mixed_subspace_boundary.md` | `baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063` |
| `markov_distinct_scale_fourier_boundary.md` | `23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee` |
| `markov_distinct_scale_first_profile_exclusion.md` | `33231c7f6306a5ad2c6b64a1bf809a2ccee08f7e87274e285ff93ca62d3b8850` |

The new fixed-point argument was derived independently of finite searches.
Root and Pascal independently challenged its algebraic identity, pole-order
calculation and local positivity contradiction before this full note was
written. Pascal supplied the independent division-free Taylor comparison;
root observed its smooth finite-order consequence, recorded above. Final
full-note reviews are separate records. No supplied,
archived, frozen or predecessor helper or source array was executed,
imported or replayed. Only proof text and fresh byte metadata are produced
under `/tmp`; no repository or Git mutation occurred.
