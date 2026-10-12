# Lambert inverse late coefficients: intake proof audit

12 October 2026. Conventional mathematical review and a complete isolated
replay; no Lean formalization or global-priority claim.

## Reconciliation with the current manuscript

The delivered article was written against the source pin in
INTAKE-PLACEMENT.md. Its predecessor's hyperbolic-amplitude questions are
already resolved by the summation-singularities continuation. Section 1.9,
Theorem 1.26 of the collective Polylogarithms manuscript now proves every
fixed inverse-index order, with a finite Faulhaber/Poisson formula. Thus
the all-order question in this delivery's section 05 is resolved too.
The delivered article and proposed predecessor patch remain unchanged.

The current manuscript uses a signed parity function (cosh for even n,
minus sinh for odd n), whereas this report normalizes by (-1)^(n+1) and
uses positive cosh/sinh. With z=A*u/4 and b=A^2*u/288 its first correction
is exactly the manuscript's P1*E+D1*z*E'. The finite coefficient formula,
r1=-1/4, r2=1/288 and A=4*pi^2 agree. No competing first-correction formula
is needed in the collective text.

The report's new accepted contribution is its checked use of nonlinear
closure to prove continuation and sectorial summability, plus explicit
uniformity down to zero coupling and the finite-phase transport law.
The finite-phase theorem and exact-completion Stokes transport are accepted
here but remain outside this canonical synthesis milestone.

## Coefficient and endpoint arguments

The factorial convolution inequality retains its endpoints for every factor
count, and the ratio estimate grows only exponentially times the factor
count. The outer 1/k! therefore permits summation of the endpoint estimates.
The first correction separates the configuration with one small forward
index 2 from the configurations with only linear small indices; the bounded
remainder treats all remaining configurations, not just a fixed k.

For complex u on a fixed disk, absolute majorants yield uniform estimates.
For odd n>1, the normalized error vanishes at u=0. Applying Schwarz's lemma
on a larger u-disk supplies an extra factor |u|. Since sinh(A*u/4) is at
least A*u/4 for positive u, the relative first-correction estimate is uniform
for every 0<u<=U. The same reasoning applies to each fixed order of the
current canonical theorem. Neither argument is uniform in unbounded u or
through zeros of the complex leading parity amplitude.

For a forward coefficient with finitely many phases, a retained linear
coefficient rho multiplies each leading phase amplitude by
exp(A*rho*u/omega). The absolute factorial majorants justify the summation;
there is no positivity assumption on the individual phase amplitudes.
Changing only finitely many nonlinear forward coefficients leaves the
leading phase amplitudes unchanged, while altering inverse-index corrections.

## Analytic continuation: hypotheses checked against the primary source

The external input was checked in David Sauzin, *Nonlinear analysis with
resurgent functions*, [arXiv:1212.4477](https://arxiv.org/pdf/1212.4477),
Theorems 3 and 5 and summable counterparts 3' and 5', pages 7, 10, 13--14.
The additive closed discrete set is Omega=A*Z, including zero. The relevant
functions have zero constant term for analytic substitution. The inverse
map is tangent to the identity at infinity. These conditions match the
closure theorems. They are established analytic input, not new results.

The model-specific proof supplies the missing hypotheses as follows.

1. The shifted Borel kernel is -1/4 minus (2/xi) times the divisor-weighted
   sum of log(1-xi^2/(A^2*m^2)). Its Taylor coefficients follow from the
   divisor Dirichlet series. On any bounded path only finitely many terms
   need nontrivial continuation; the rest are dominated by d(m)/m^2.
2. The principal origin is removable. After a loop, logarithmic monodromy
   can introduce a pole there. Including zero in Omega, and excluding it
   after departure, is essential; no all-sheet regularity at zero is claimed.
3. Let h(t)=(sqrt(1-2*u^2*R(t))-1)/u, with the root of constant term one,
   and G(x)=x*exp(-h(1/x)). Analytic substitution is legitimate for fixed
   nonzero u. G=x-u/4+O(1/x). Multiplication by x is separately justified
   by B(x*f-f1)=d(Bf)/d(xi), which preserves allowed continuation.
4. Invert G in the closure group, writing T=G^(-1). Composing h(1/x) with T
   gives V(q)=h(1/T(1/q)). The equation G(T(1/q))=1/q gives q=t*exp(h(t)),
   hence t=q*exp(-V) and the original formal inverse equation. At u=0,
   V=0 handles the removable special case directly.
5. Away from real directions, the divisor summatory estimate and a split
   at m=2*|xi|/A bound the Borel kernel by O(1+log^2(2+|xi|)). Cauchy's
   estimate on a smaller arc preserves exponential growth under Borel
   differentiation. Summable closure now gives the exact sectorial inverse
   equation. Its small O(q) solution is unique by contraction.

This proves continuation along the allowed paths and 1-summability off the
real directions. The initial-disk log/dilog models alone would not prove
either conclusion. The nearest two singularities are genuine for every
u!=0. The theorem does not prove that every other lattice point is active,
classify all singular germs, or establish the full alien calculus.

## Exact-completion Stokes transport

The report explicitly imports the established forward exact completion and
jump J=4*pi*i*sum d(m)*E1(A*m/t). Differentiated finite Mellin expansions
control the forward derivatives uniformly near the positive ray. A disk
of radius proportional to q in the inverse variable controls the jump and
its derivative; the inverse displacement is O(u*q*exp(-A/q)). Taylor
expansion retains the u^2*q*exp(-2*A/q) error in the transported jump.
Since V0=u*q/4+O(u*q^2), evaluating the exponential at t0=q*exp(-V0)
produces exp(-A/q-A*u/4). All displayed powers of u survive uniformly
down to u=0. This argument does not identify the arithmetic mean of
nonlinear lateral inverses with a median sum.

## Fresh verification and limits

The full unmodified verifier passed on an isolated Linux copy with the
delivered dependency versions, 64 significand bits in long double and
maximum binary exponent 16384. See intake-verification/REPLAY.md and the
fresh results and run log there. All 5890 exact checks passed; all seventy
main coefficients include every finite k<=n through n=1025. Thirty-five
80-digit comparisons passed, including fifteen exact-polynomial checks.
The secondary k<=256 precision comparison retains its explicit omitted-tail
bound, which is not a roundoff enclosure. No infinite theorem follows just
from these finite observations.

Canonical continuation and all-order endpoint uniformity are integrated
into Section 1.9 in a separate commit (continuation is Theorem 1.28). Final collective PDF acceptance is
recorded in that manuscript's VALIDATION.md after compilation and visual
review, not implied by the preserved delivered PDF or by this intake audit.
