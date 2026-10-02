# Independent verification

These scripts do not import or call the main coefficient generator.

- derive_low_orders.py reconstructs p0 through p3, b0 through b3, tau1 and tau2, and the small-state source through degree three. It uses direct high-precision cumulant derivatives and enumerates Gaussian monomials by integer partitions. Its convergent Fuss moment sum uses r = 1,...,1199, rather than the generator's exact moment recurrence. For the tested k = 2,3,4 the omitted tail is below the 70-digit comparison scale. The replay requires each reported coefficient discrepancy to be below 1e-68.
- check_small_models.py exhaustively enumerates actual k-tuples of maps and tests forward and reverse reachability. It also verifies the exact renewal identity through n = 25 for k = 2,...,6.
- verify_exact_counts.py evaluates exact integer auxiliary and labeled-strong recurrences through n = 600. Its Stirling denominator is obtained by exact surjection inclusion-exclusion. Ratios are converted to 100-digit numerical values only after all integer computations finish.

Run these from the package root, or use the isolated full replay:

    python independent_checks/derive_low_orders.py
    python independent_checks/check_small_models.py
    python independent_checks/verify_exact_counts.py --k 2 --N 600 --coefficients coefficients_k2.json --output independent_checks/exact_k2.json

Repeat the last command for k = 3 and k = 4. The data files record independent formulas, exact small counts, ratio samples at n = 100,150,200,300,400,500,600, and successively scaled residuals. The `seconds` field in the exact-count outputs is machine dependent and ignored by replay comparison.

The independent reconstruction of the renewal kernel uses the exact finite difference

    R_(n-r)(r) = (1/r!) sum_(j=0)^r (-1)^(r-j) binom(r,j) (n-r+j)^(kr).

Applying the fundamental theorem of calculus r times gives the uniform-sum expectation used in the article. This reconstruction does not assume the generator's implementation of that kernel.

At n = 600 the relative degree-five errors in B_n/T_n are approximately 2.99e-12, 4.23e-14, and 2.61e-15 for k = 2,3,4. Finite checks establish agreement of implementations at the tested orders and indices. They do not prove the asymptotic remainder, establish historical priority, or certify decimal values by interval arithmetic.
