# Explicit unrestricted-integer conversion

The 241-variable principal equation uses nonnegative integers. This directory
supplies a fully explicit conversion to a single quartic over all integers:

    P_hat(z,a,b,c) = P_241(z) + sum_i (8*z_i+1-a_i^2-b_i^2-c_i^2)^2.

There are 964 integer variables and 430 quadratic residuals. The exact collected
polynomial has degree four, 33,083 monomials, and coefficient height 85,187,969.
`equation.json` supplies every residual; `expanded_polynomial.json` supplies
every collected coefficient. The first 241 coordinates are the original
coordinates; the remaining three coordinates per original coordinate are its
sum-of-three-squares witnesses.

All summands are nonnegative over the integers. If the polynomial vanishes,
then each guard gives `8*z_i+1>=0`, hence `z_i>=0`. Conversely, for `z_i>=0`,
the number `8*z_i+1` is not of the form `4^a(8b+7)`, so Legendre's three-squares
theorem supplies integers `a_i,b_i,c_i` with the required sum. Thus integer
zeros correspond exactly, by existence of the guard witnesses, to natural
zeros of the principal equation. This argument is formalizable in ZFC.

This is a transparent domain conversion, **not a new integer-variable record**.
The repository already has much smaller specialized integer equations.
The top-level verifier expands every residual independently, checks the full
coefficient list and metrics, and authenticates the report binding.
