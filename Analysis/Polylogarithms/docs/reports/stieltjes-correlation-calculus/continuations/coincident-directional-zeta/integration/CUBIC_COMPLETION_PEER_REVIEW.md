# Independent multivariate check of the cubic completion

Reviewed the undifferentiated completion in `research_package/sections/02_cubic.tex`.

## Formula and convergence

Write `h_i(x)=zeta(1-lambda_i,1+x)+1/lambda_i`. The direct remainder

`R = h_1 h_2 h_3 + sum_i x^(lambda_i-1) (h_j h_k-h_j(0)h_k(0)) + sum_{i<j} x^(lambda_i+lambda_j-2) (h_k-h_k(0)-x h'_k(0))`

is absolutely integrable near zero whenever each `Re lambda_i > -1` and each `Re(lambda_i+lambda_j)>-1`. In a sufficiently small neighborhood of the spectral origin all explicit remaining denominators are nonzero. The completion is exactly

`integral_0^1 R + 1/(lambda_1+lambda_2+lambda_3-2) + sum_{i<j} h_k(0)/(lambda_i+lambda_j-1)`.

This follows by expanding the product into singular subsets. Singleton constant Taylor terms give the subtracted `h_j(0)h_k(0)/lambda_i`. Pair linear Taylor terms give the subtracted `h'_k(0)/(lambda_i+lambda_j)`, with `h'_k(0)=-(1-lambda_k)zeta(2-lambda_k)`. This confirms the positive sign of the last line in the global formula. The full triple singular term and pair constant terms are the two explicit finite terms retained above.

No correction to the parent's formula is needed.

## Independent numerical comparison

The direct side uses only Hurwitz-zeta quadrature with stable Taylor differences below x=0.125. The global side uses the spectral agent's Jonquiere plus incomplete-Gamma Mellin evaluator for each of the three Tornheim permutations, then assembles K3, K2, and the prescribed singleton/pair subtractions. The standalone script contains that evaluator so packaging does not require a sibling agent directory.

At 65 decimal working digits:

- `(lambda_1,lambda_2,lambda_3)=(0.03,0.07,0.11)`: cross-error below 2.93e-50.
- `(0.04+0.03i,-0.02+0.01i,0.06-0.02i)`: cross-error below 5.83e-50.

Repeating the complex case with 73 Jonquiere terms, incomplete-Gamma tail index 180, 93 direct Taylor coefficients, and split x=0.1 gives cross-error below 5.22e-58. The direct value changes by less than 1.51e-63. The change in the initial global value is 5.83e-50, consistent with its independent series truncation error.

These are arbitrary-precision diagnostics, not interval certificates. They specifically test multivariate phases, permutations, and subtraction signs beyond the diagonal.

Files: `code/verify_cubic_completion.py` and `results/cubic_completion_verification.json`.
