# Mellin/polylogarithm verification notes

The distributable verifier checks 2,002 exact rational/algebraic cases and
11 direct integer-order or scaled quadratures at 40 decimal digits.  The
analytic proofs, not those decimals, establish the complex-order formulas.

A separate exploratory quadrature took the third order derivative of
`mpmath.polylog` numerically at polylogarithm order 3 inside the integral
with weight x/(1+x)^4. At 23-digit
working precision and Gauss-Legendre quadrature in log x over [-22,22], it
returned

    -0.03809812559380664836424059 - 2.2586427195695017119e-11 i

where the proved expression gives

    -0.038098125414464619688643844.

The discrepancy 1.81e-10 did not meet the attempted 1e-12 tolerance. The
nonzero imaginary part for a real integrand also signals numerical failure.
This exploratory method is not included as a verification claim or in the
distributable verifier. No independent numerical verification of the
integer-order derivative corollary is asserted. Its proof differentiates
the already established jointly holomorphic transform. No optional repeat
was performed.
