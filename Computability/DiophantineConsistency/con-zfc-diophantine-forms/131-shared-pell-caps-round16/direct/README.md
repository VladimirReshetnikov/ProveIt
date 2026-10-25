# Signed direct quartics with one Pell bound

This directory contains two fully materialized fixed quartics over unrestricted integers. Each is the sum of squares of the exact quadratic residuals in its equation.json. Its variable order is that file's variable order.

- integer324: 324 variables, 208 residuals, 5,808 collected monomials, degree 4, coefficient height 128,446.
- integer338: 338 variables, 222 residuals, 4,493 collected monomials, degree 4, coefficient height 128,446.

The previous round15 primary had 442 variables, 290 residuals, 4,652 monomials, degree 4 and the same height. The 324-variable equation lowers the variable count by 118 (26.7%), trading density for the smaller coordinate count. The 338-variable sparse companion lowers variables by 104 (23.5%), rows by 68 (23.4%) and monomials by 159 (3.4%), without raising degree or coefficient height.

Read PROOF.md for the complete new ordinary arithmetic argument, its exact inherited calibration boundary and its attributions. It proves that these equations have integer zeros exactly when ZFC has a finite refutation, using the identified prior direct-calculus calibration. It is not a proof of consistency, an end-to-end new proof-assistant development, or a global-minimum claim.

## Portable reproduction

Only Python's standard library is required. From this directory:

    python build_cap.py portable_input rebuilt --strong-cap --odd-frame --odd-comparison --ys-only --cofinal --self-radix
    python center_integer.py rebuilt rebuilt_integer324

For the sparse companion, use a second output directory and add --sparse to the first command. Its centered endpoint has 338 variables.

portable_input holds the original round15 literal raw input, not executable upstream code. The source hashes, front modifications, new single-anchor rows, guard predicates, exact Horn factorization, integral projections and translations are supplied in cap_cofinal_self and cap_sparse. The independent audit in the parent packet checks the full chain, rather than relying only on these generators or hashes.

The five JSON files per final endpoint suffice to state the exact polynomial and its final translation. For a complete reproducible derivation, retain the two certificate-bearing source directories, portable_input, the six implementation helpers named in DELIVERY_WHITELIST.json, this proof, and the inherited arithmetic/calibration dependencies identified by the parent packet. Intermediate experimental variants are deliberately excluded from that whitelist.
