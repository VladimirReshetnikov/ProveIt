# Independent check of the analytic contribution

Reviewed the analytic section now included as `article/sections/05_gamma.tex` and the interval program now included as `code/moments/certify_cubic.py`.

## Main mathematical results

- The coefficient probability formula is exact:
  `c_k = tau rho^(-k) Pr(S_k=k-1)/k`.
- Positivity follows from the Taylor coefficients of `log Gamma(1-u)`;
  the tilted distribution has span one and exponential moments.
- The variance `v = 1 + tau^2 psi_1(1-tau)`, leading coefficient
  `C = tau/sqrt(2*pi*v)`, and stated first correction are correct.
- The Fourier argument controls the only peak of the coefficient-extraction
  contour. It does not need an unproved global assertion about inverse-Gamma
  critical points.
- The coefficient asymptotic gives radius `rho` and absolute convergence
  on the entire boundary. The real inverse argument gives `h(rho)=tau`.
- The moment inverse integral, both terms of the finite-truncation remainder,
  the choice `K=floor(n/alpha-sqrt(n))`, and every factor in its resulting
  uniform bound are correct.
- The all-poles residue formula, cubic Fourier/Tornheim reduction, positive
  triangular Tornheim tail, and Taylor-cube error expression also check out.

## Corrections requested and resolved

1. The original explanation of the zeta Euler--Maclaurin error used the bare
   periodic-Bernoulli bound after truncating *before* the indicated Bernoulli
   correction. That bound alone did not give the asserted first-omitted-term
   estimate. The actual estimate is true. The corrected proof now derives it
   from the positive partial-fraction expansion of the Laplace kernel and its
   signed geometric remainder, with the precise truncation index specified.
2. The nonnegative interval convolution now asserts its positivity precondition;
   this prevents invalid interval operations with a user-selected precision too
   coarse to preserve positive lower bounds. The default certificate is unchanged.
3. Recommended specifying integer `N` in the triangular cutoff tail bound.
4. Suggested a rigorous integer cutoff `n>=7`: `rho>=1/(2*sqrt(pi))` yields
   `alpha<13/10`, hence `4*alpha^2<7`. This was added.
5. The proof now explicitly splits the Fourier integral into central,
   shrinking intermediate, and fixed outer bands to support the full expansion.

## Reproduction

Re-ran `certify_cubic.py` with its default `order=360`, `digits=130`, writing
to a separate temporary output. Every JSON field
matches the reference certificate exactly; its interval has 112 common
decimal digits. This is a replay of the same finite calculation, not a second
independent analytic proof. The interval operations were also checked directly
against their floor/ceiling definitions.

No unresolved mathematical objection was found to the main analytic theorems.
