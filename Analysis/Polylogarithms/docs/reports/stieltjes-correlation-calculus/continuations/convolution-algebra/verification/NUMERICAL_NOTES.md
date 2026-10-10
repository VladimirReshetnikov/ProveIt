# Numerical methods and limitations

## Representations compared

The finite-part digamma and trigamma checks use explicit Taylor-subtracted ordinary integrals, evaluated by mpmath quadrature. Their other sides use generalized Stieltjes constants or Hurwitz-zeta spectral derivatives. The higher Stieltjes convolution checks use a Taylor evaluator for gamma_1 centered at 3/2 after applying the unit shift. It is independently checked against mpmath's generalized-Stieltjes routine at seven arguments. The comparison formulas use gamma_2 and gamma_3 from that independent routine.

The ordinary centered log-Gamma convolution is compared with jets at -1. The complex-order semigroup is checked by ordinary quadrature. The shifted correlation is compared with polylogarithmic order jets, including a non-half shift. Cyclotomic order jets are compared with a finite Hurwitz grid. A Fourier-mode integral of the canonical finite-part trigamma independently checks the derivative contact correction.

## Cancellation controls

Removable endpoint quotients such as `(f(x-t)-f(x)+t*f'(x))/t^2` are evaluated by 16-term Taylor expressions when `t < x*1e-5`. Direct subtraction is used away from the endpoint. This is a numerical strategy, not interval arithmetic.

The higher-Stieltjes evaluator uses the exact parameter-derivative formula with Taylor center 3/2. After shifting arguments below 1, the ratio of displacement to distance from the nearest singularity is at most 1/3 in the tested region. Its truncation degree grows with requested precision. Its output is cross-checked rather than treated as a certified enclosure.

For polylogarithmic order jets at order 2, the initial use of automatic tiny-step differentiation of a rounded complex root of unity produced a discrepancy around 1e-13 in the shifted-correlation diagnostic. A finite five-point stencil, with 40 guard decimal digits and a precision-dependent fixed step, removed that discrepancy. Exact roots such as -1 are supplied exactly. This observation records sensitivity of a numerical differentiation path, not a claim of an analytically false polylogarithm formula or a general defect in mpmath.

## Recorded outcomes

At 40 decimal digits, all 31 checks passed; the largest scaled residual was approximately 8.4329188e-37. At 50 digits, all 31 checks passed; the largest scaled residual was approximately 7.0380144e-47. A scaled residual is `abs(lhs-rhs)/(1+abs(rhs))`. The test threshold is 1e-28. A printed zero is floating-point cancellation, not a mathematical equality certificate.

No rigorous interval enclosures are claimed. The proof obligations—analytic continuation, convergence, normalization, and equality—are discharged by the article's analytic arguments. The finite symbolic certificates check algebra and signs but do not formalize the analytic proofs.
