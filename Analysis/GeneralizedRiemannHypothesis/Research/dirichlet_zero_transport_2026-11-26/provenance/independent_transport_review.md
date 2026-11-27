# Independent audit of the determinant spectral-shift candidate

This checks the mathematical candidate sent by the parent. It is an independent derivation, not a Lean verification or a literature-priority certification.

## Hypotheses and normalization

For each primitive Dirichlet character chi_i, take the completed entire L-function, with the usual s(s-1)/2 correction for the conductor-one principal character. Set s=1/2+iz and multiply by a constant phase c_i satisfying c_i epsilon_i=conjugate(c_i). The functional equation plus conjugation gives F_i(conjugate z)=conjugate(F_i(z)). This works for complex as well as real characters; no conjugate pairing is necessary.

Under Dirichlet GRH, F_i is real entire of order one with only real zeros. Multiplicities and a zero at zero are allowed. Its logarithmic derivative satisfies
Im(F_i'/F_i)(x+iy)=-y sum_gamma m_gamma/((x-gamma)^2+y^2)<0
for y>0. The real linear exponential term in a canonical genus-one product contributes no imaginary part.

With g_i=F_i'/F_i and M_A=A+diag(g_i), every constant Hermitian A gives strictly negative-definite Im M_A in the upper half-plane, so M_A is invertible there.

## Entire extension and reality

Use the exact principal-minor expansion
P_A(z)=sum_(S subset [n]) det A[S] product_(i in S)F_i(z) product_(i not in S)F_i'(z).
It agrees with product F_i det M_A away from the F_i zeros, and shows immediately that P_A is entire and real on the real axis even if A has complex off-diagonal entries. Hermitian principal minors are real.

The upper-half-plane invertibility and reflection imply that P_A has only real zeros. It is not the zero function, as its determinant factor has the large-imaginary asymptotic (-i log(y)/2)^n.

## Log branch and boundary inertia

Let B=C C* be positive semidefinite of rank r, with C an n by r injective matrix. Set
H(z)=I_r+C* M_A(z)^(-1) C.
Then Im H>0 in the upper half-plane. Define
f(z)=Tr Log H(z),
using the principal matrix logarithm. This is analytic, exp f=det(M_A+B)/det M_A, and 0<Im f<r pi for nonzero B. Moreover f(iy)->0, fixing the branch.

At any real x away from the discrete set of poles and determinant zeros, H(x) is Hermitian and every negative eigenvalue is approached from the upper half-plane. Thus
xi(x)=pi^(-1) Im f(x+i0)=n_-(H(x)).
A block Schur-complement inertia identity gives
n_-(H)=n_+(M_A+B)-n_+(M_A).
Consequently xi is an integer in {0,...,r} almost everywhere.

Multiple/shared zeros of the F_i do not invalidate this assertion: they lie in the excluded discrete set and do not affect any Lebesgue integral. Do not define the formula at those points by an unjustified cancellation convention; define xi almost everywhere or by its boundary value.

## Poisson formula

The bounded harmonic function Im f is the Poisson integral of its essentially bounded boundary values:
Im f(iy)=integral_R xi(x)y/(x^2+y^2) dx.
Hence
I(y):=integral_R xi(x)y^2/(x^2+y^2)dx=y Im f(iy).
There is no linear y term or singular boundary measure because Im f is bounded.

## Large-y coefficient

At z=iy, functional equation transfers the calculation to s=y+1/2 for the conjugate character. Stirling and the absolutely convergent Euler product give
g_i(iy)=-i( (1/2)log y+(1/2)log(q_i/(2pi)) )+O(1/y).
For zeta, logarithmic derivatives of s(s-1)/2 contribute only O(1/y). Complex characters cause only an exponentially small non-real logarithmic derivative on the right-hand real axis, also absorbed in O(1/y).

Writing ell=(1/2)log y,
M_A(iy)^(-1)=i ell^(-1)I+O(ell^(-2)).
Therefore
f(iy)=i tr(B)/ell+O(ell^(-2)),
I(y)~2 tr(B) y/log y.

The sign is positive and the factor 2 is correct.

## Tauberian constant

Let U(T)=integral_[-T,T] xi(x)dx. Then
I(y)=integral_[0,infinity) y^2/(t^2+y^2) dU(t).
For a regularly varying U(T)~c T/log T, the transform is asymptotic to
(pi/2)c y/log y.
The nonnegative-measure Tauberian converse therefore yields
U(T)~(4 tr(B)/pi) T/log T.
For B=h(e_a-e_b)(e_a-e_b)*, tr B=2h and the coefficient is 8h/pi.

A self-contained way to prove the needed converse, avoiding an unverified named Tauberian theorem, is below.

### Elementary scaling proof of the converse

Suppose I(y)~a y/log y, a>0, for a nonnegative locally finite measure dU and finite I(y). Define measures
mu_y(E)=(log y/y) integral 1_E(t/y)dU(t)
on [0,infinity). For every fixed b>0,
integral b^2/(t^2+b^2) dmu_y(t)
=(log y/y) I(by)->a b.

The b=1 bound makes mu_y uniformly bounded on each compact interval, hence every sequence y->infinity has a vaguely convergent subsequence. For R>=b and t>R,
[b^2/(t^2+b^2)]/[R^2/(t^2+R^2)] <=2b^2/R^2.
Thus the limsup of the tail transform is at most 2ab^2/R. The same bound holds for the vague limit, so transforms pass to the limit.

The resulting measure mu has transforms ab. The measure (2a/pi)dt has exactly those transforms and is unique. To see uniqueness, weight a candidate measure by 1/(1+t^2), push it forward by u=1/(1+t^2) into [0,1], and note that all transforms determine
integral 1/[1+(b^2-1)u]dnu(u).
For b near 1 its uniformly convergent power series determines every moment of nu. Polynomial approximation then determines the finite measure uniquely.

Therefore every vague subsequential limit is (2a/pi)dt. Since this limit has no atom at 0 or 1,
(log y/y)U(y)=mu_y([0,1])->2a/pi.
Taking a=2tr(B) gives 4tr(B)/pi as above.

## Rank-one extra statement

For rank one, H is a scalar nonconstant meromorphic Herglotz function. After cancelling common zeros between P_A and P_A+B, its poles and zeros are simple and strictly interlace. Each updated zero is to the right of its preceding old zero. This is stronger and cleaner than saying all original zeros are simple, which would be false in the presence of common factors.

For rank one xi is the indicator (almost everywhere) of the intervals swept between such paired poles and zeros. Thus U(T) is the total clipped length of these intervals in [-T,T], an exact geometric interpretation of the asymptotic. No unproved simplicity of the original L zeros is required.

## Limits and wording

- These conclusions concern Dirichlet completed L-functions; do not extrapolate to all automorphic L-functions.
- The upstream proof uses a theta-lift/arithmetic-covolume sandwich, not this matrix Weyl function. Its determinant method and the real-zero conclusion inspire this construction.
- The determinant stability step is closely related to established real-stable-polynomial and Herglotz function theory. The candidate contribution is the exact arithmetic-family spectral-displacement law (and graph-edge coefficient), rather than claiming a new general Herglotz theorem.
- Novelty still needs literature and existing-ProveIt comparison. No mathematical error was found in the candidate as carefully stated above.

