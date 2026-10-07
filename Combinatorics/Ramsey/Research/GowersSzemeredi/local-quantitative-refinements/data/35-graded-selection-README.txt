EXACT VERIFICATION
==================

Run all suites from the package root:

    python verification/verify_all.py

The runner also works from any other current directory when invoked through
its full path. It uses the current Python interpreter and only standard-library
modules. It runs each verifier with an explicit temporary --output path, loads
the resulting JSON, and compares it with the included evidence. Object-key
ordering and whitespace are ignored; values, value types, and array ordering
are checked. It reports a nonzero exit status on any verifier error, missing
output, invalid JSON, or evidence mismatch. The recorded evidence is not
rewritten.

Each individual verifier accepts --output PATH for a complete JSON record and
--help for usage. Default runs print a summary without changing the evidence.
Prefer a new output path when requesting an individual suite's JSON.

SUITES AND EXACT COUNTS
----------------------

verify_graded_selection.py / graded_selection_checks.json

* All 6,561 coefficient arrays in the F_3, k=1, m=4, bandwidth-2 model;
  degree-sensitive success probabilities and weighted exceptional mass.
* All 6,561 ordered arrangements in F_3^2 and all 243 field seeds for the
  specified target map, retaining physical vertex repetitions in the exact
  subset-survival computation.
* Three balance-subspace dimension checks, an exponent table with 16 rows,
  and 54 exact threshold schedules. The dimension-only checks at m=2 test
  an algebraic identity; the main arrangement theorem still assumes m>=4.

verify_norm_gap.py / norm_gap_checks.json

* All 17 auxiliary rational comparisons used in the scalar estimate.
* All 32,768 sign assignments for the fourth-order cosine dual identity.
* All 65,536 sign assignments for the order-three full four-cube identity.

verify_polynomial_obstruction.py / polynomial_obstruction_results.json

* All 47,089 start/step pairs for the quadratic period-217 example.
* All 90,601 pairs for the quadratic period-301 example.
* All 148,225 pairs for the cubic period-385 example.
  Total periodic pairs: 285,915. In each case, the good step residues are
  exactly zero modulo the asserted period.
* All 422,500 length-three integer progressions in the 1,301-point interval
  for a coefficient approximation modulo the prime 54,121,601. Its only good
  steps on that interval are 217 and 434.
* Independent semigroup calculations by dynamic programming and enumeration
  of the two nonnegative integer coefficients in the permitted-length sum.

ARITHMETIC AND LIMITS
--------------------

The finite decisions use integer arithmetic, exact fractions, and exact
finite-field calculations. The supplied records include the parameters,
counts, and rational comparison values. No numerical tolerance is used to
decide a finite certificate.

These programs certify the listed finite examples and auxiliary arithmetic.
They do not establish the general theorems for arbitrary groups or interval
sizes; those are proved in the article. The programs do not establish
publication priority, optimality of the displayed sufficient constants,
Lean certification, or a new global bound in Szemeredi's theorem.

The polynomial prime-modulus example is local to its specified integer
interval. The observed divisibility of good steps does not assert a global
period for a nonconstant polynomial over that prime field.
