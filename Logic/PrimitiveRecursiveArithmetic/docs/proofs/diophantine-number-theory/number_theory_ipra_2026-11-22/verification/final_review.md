# Final mathematical and artifact review

Report date: 22 November 2026.

## Mathematical review disposition

- **Bounded Boolean reflection and search:** the initial draft used these results in a circular order. The final chapter directly verifies the Boolean scan with guarded quantifier-free invariants, obtains bounded existential reflection, and only then derives bounded search and leastness. The follow-up independent review confirms that this resolves the dependency cycle.
- **Four-square descent:** even multipliers are reduced by equal-parity pair sums and differences; odd multipliers use balanced residues with a strict norm decrease. The separate branches avoid the equality case in an undifferentiated balanced-residue argument.
- **Pell construction:** the bound is obtained by a finite norm-and-residue collision. The sign arguments and quotient integrality cover both positive and negative common norms. This does not assume continued-fraction periodicity or a pre-existing Pell unit.
- **Finite analytic estimates:** the dyadic constants, block-product bound, explicit prime-reciprocal threshold, and Euler-product truncation/error-removal argument were independently reviewed. Positive prime-divisor sums explicitly exclude zero. Finite CRT independence is restricted to complete periods.
- **Algebraic and p-adic arguments:** norm factorization, capped valuations, the exact Hensel quotient and unique digit, and the partition bijections were independently reviewed. Capped valuation notation and the largest part of the empty partition were clarified.
- **Transcendence:** the finite root-avoidance step, rational denominator lower bound, coefficient-based Lipschitz bound, and explicit factorial domination were reviewed and checked on the stated finite samples. The internal conclusion is separation of a fixed rational name from each nonzero integer polynomial; the usual transcendence statement is its external interpretation.

The original reviews are retained as historical records. `review_root.md` describes an intermediate draft; its actionable issues were resolved. `review_additional.md` confirms the foundational repair. `verification/diophantine_review.md` records the independent Diophantine review.

## Distinct evidence layers

The report supplies human mathematical arguments for the numbered statements and explains their reduction to primitive-recursive algorithms and quantifier-free induction. The Python suites supplement this with exact finite checks. Neither the review nor those tests is a Lean proof certificate.

The supplied Lean files are uncompiled definitions and blueprint interfaces. The pinned external source interfaces were inspected selectively; their complete transitive build was not replayed. The final package therefore makes no new claim of kernel-checked object-theory derivations.

A final static review of all seven Lean files corrected an integer coercion and added the intended leading-coefficient hypothesis to the rational-root goal; see `verification/lean_static_review.md`. The six standalone Lake roots and toolchain pins were also checked, without compilation.

The generated theorem inventory, final PDF build record, and SHA-256 manifest provide artifact-level traceability. The finite suite results state their ranges and limitations. Very large worst-case search spaces were not enumerated.
