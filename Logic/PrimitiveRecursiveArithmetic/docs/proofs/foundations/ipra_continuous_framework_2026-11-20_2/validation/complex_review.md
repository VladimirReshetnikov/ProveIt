# Independent audit: complex power-series and analytic descent section

Final resolution: the delivered section explicitly includes the derivative
Lipschitz bound `2T` and extends both value and derivative names to represented
inputs. It also requires a nonempty chart family `N >= 1`. The remaining
items below are optional implementation refinements, not open proof gaps.
The original review is retained as a record of the reasoning behind the edits.

Reviewed file: `output/ipra_continuous_framework_2026-11-20/paper/sections/05_complex_descent.tex`.
Review covers the mathematical argument and PR/representation boundaries;
it does not claim Lean compilation or a deep iPRA proof.

## Verdict

The principal estimates are correct. In particular, neither the derivative
tail nor the Taylor remainder needs a missing factor of sigma, R, or two.
The exact analytic descent argument is sound once the represented-input
evaluation step is made explicit. I recommend the following small but useful
additions before finalization; none requires changing the central constants.

## Concrete additions

### 1. Make derivative continuity and evaluation on represented points explicit

The section starts by evaluating P_N at rational points, but subsequently
states the Taylor theorem at represented complex points. A direct way to
close that interface is to add the finite derivative Lipschitz estimate

    |P_N'(z)-P_N'(w)|_1
      <= (2M / [R^2 (1-theta)^3]) |z-w|_1 = 2T |z-w|_1

for rational z,w in the closed inner diamond. Factor each difference of
powers and sum n(n-1) times the coefficient majorant. The same triple
geometric-sum calculation used for the Taylor bound gives the factor 2T.
The derivative tails pass this estimate to g. The already proved Lipschitz
estimate for f and this estimate for g let the completion theorem extend
both to represented inputs. Then pass the finite Taylor inequality to those
extensions, keeping all rational approximants inside the certified domain.

Suggested text, immediately after the existing Lipschitz proof:

  "The same difference-of-powers argument applied to P_N' gives the bound
  |P_N'(z)-P_N'(w)|_1 <= 2T |z-w|_1, because the relevant majorant is
  sum n(n-1) theta^(n-2) <= 2/(1-theta)^3. Thus the derivative limit g is
  also uniformly continuous with explicit Lipschitz bound 2T. Apply the
  completion theorem to both rational-input limits f and g. This defines
  their values on represented points in the closed inner diamond and
  transports the displayed Taylor estimate. For points with an interior
  margin, rational approximants are shifted until they lie in the same
  certified domain."

At closed-boundary points one may instead work with names whose samples
are already in the rational closed diamond, i.e. its represented completion.
For the holomorphic theorem only interior points are needed, so the positive
margin argument is sufficient. This makes the representation route explicit
rather than relying on an unstated continuity property of g.

### 2. State N >= 1 in the finite-chart subsection

The descent proof divides by N. Nonemptiness follows at any point where
S >= delta > 0, so this is not a substantive counterexample. Still, begin
with a nonempty finite family of N >= 1 charts. If the family is empty, the
analytic domain is empty and the assertion is vacuous.

### 3. Optional explicit PR bounds for selecting H and b

The cutoffs are correct. To make the phrase "bounded searches on rational
codes" completely mechanical, give a search bound or a direct coarse choice.
If 1-theta = a/d with positive integers a,d, H=d works. If
M/(1-theta) = A/B with positive integer A and B >= 1, b=A works because
2^A >= A >= A/B. The analogous choices work for sigma and B1. Much sharper
bounded doubling can then be used as an optimization. All expressions are
rational-code PR operations, not unbounded convergence searches.

### 4. Optional clarification of the derivative norm convention

The linearization estimate with the taxicab norm is a valid complex-linear
Fréchet derivative condition. If the displayed requested tolerance is later
read as a bound for the usual complex difference quotient, include a factor
two in its finite tolerance schedule:

    |(f(z+h)-f(z))/h - g(z)|_2 <= 2T |h|_1,  h != 0.

This follows from |h|_1 <= 2|h|_2. No change is needed if the text explicitly
keeps the taxicab linearization-error definition; equivalent norms give the
usual holomorphicity claim.

## Estimates checked in detail

1. **Value tail.** For |z-c|_1 <= rho, the coefficient term is at most
   M theta^n. The finite tail beginning at N+1 is at most
   M theta^(N+1)/(1-theta). With H(1-theta) >= 1 and N=H(k+b+1),
   theta^(N+1) <= theta^N <= 2^(-k-b-1), hence the stated error.

2. **Derivative tail.** theta=usigma implies

       n theta^(n-1) = n u^(n-1) sigma^(n-1)
         <= (1-u)^(-2) sigma^(n-1).

   Summing for n>N gives sigma^N/(1-sigma), exactly the claimed B1 sigma^N.
   There is no missing sigma factor. The bound for n u^(n-1) is obtained
   as one coefficient-group in a finite square of a geometric sum.

3. **Binomial remainder.** The coefficient inequality

       C(n,j) <= C(n,2) C(n-2,j-2), j>=2,

   is correct because the ratio is 2/[j(j-1)] <= 1. Therefore the degree-n
   remainder is at most C(n,2) rho^(n-2)|h|_1^2. Multiplication by
   M/R^n leaves (M/R^2)C(n,2)theta^(n-2)|h|_1^2.

4. **Taylor constant.** The triple geometric-sum coefficient is
   C(r+2,2). Thus the finite sum of C(n,2)theta^(n-2) is bounded by
   (1-theta)^(-3). The stated T=M/[R^2(1-theta)^3] is correct. The
   derivative Lipschitz constant is 2T, which explains why no factor two
   belongs in the original Taylor remainder.

5. **Value Lipschitz constant.** Difference of powers yields
   n rho^(n-1)|z-w|_1; the square-geometric majorant gives
   M/[R(1-theta)^2], as stated.

6. **Represented overlap equality.** The all-precision inequality
   |f_i(p,z)-f_j(q,z)|_1 <= eps(p)+eps(q) is sufficient for equality
   of the represented values on rational overlaps. Positive overlap
   clearance plus continuity extends it to represented overlaps.
   No finite sample identity alone is being used as an identity theorem.

7. **Chart selection.** At z with S(z)>=delta+gamma, a true weight is
   at least delta/N. Approximating each weight with error delta/(8N),
   then subtracting that error to form a rational lower endpoint, gives
   a lower endpoint at least 3delta/(4N) for one chart. Hence scanning
   for a lower endpoint >=delta/(2N) succeeds.

8. **Neighborhood clearance.** Increment bound gamma/(2N) keeps
   S>=delta+gamma/2>delta. Increment bound delta/(4N) stays strictly
   inside the chosen chart whose weight is >=delta/(2N). Their minimum
   with the derivative-error radius is positive and PR from the supplied
   rational margins. This also ensures |z-c_i|_1+|h|_1 <= r_i for the
   Taylor theorem.

9. **Holomorphic descent.** The global function equals one chart function
   on an actual neighborhood, so it inherits that chart's complex
   derivative. The proof never differentiates the nonholomorphic weights.
   Approximate overlap agreement is correctly denied this conclusion.

## Remaining status boundary

The argument is a complete human derivation of a useful effective analytic
schema after the represented-input clarification above. Its iPRA realization
still depends on proofs of finite convolution identities, the finite
arithmetic contracts, and the coefficient majorant. Ordinary semantic Lean
definitions or proofs do not establish those deep arithmetic endpoints.
