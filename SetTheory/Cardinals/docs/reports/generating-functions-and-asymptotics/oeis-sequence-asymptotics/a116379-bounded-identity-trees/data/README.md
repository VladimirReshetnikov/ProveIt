# Reference numerical data

All entries are clean numerical results, with no third-party paper copies or
external database snapshots. Integer arrays come from the finite rooted-set
enumerator. High-precision real values are decimal strings, not certified
interval enclosures. Exact integer enumeration is independently replayed by
the two algorithms in `../code/check_identity.py`.

- `identity-checks.json`: exact counts a[0],...,a[400] for d=2,3,4 and initial
  60-digit characteristic calculations
- `identity-allorders-checks.json`: d=3,4 Puiseux/Gamma reference calculations,
  using (N,precision,route)=(200,70,sum),(400,110,sum),(250,80,differentiate)
- `identity-inverse-checks.json`: original d=3,4 order-four specified-model
  inverse calculations, separating model inverse error from series error
- `identity-inverse-replay-checks.json`: regenerated R=K=4 calculations,
  additionally recording pure-log polynomials, signed errors, and numerical
  model equation/derivative checks
- `identity-inverse-extended-checks.json`: finite-model checks with R=2,K=6
  and R=0,K=4, with D_j=0 for j>R
- `replay-validation-summary.json`: interpreter and dependency versions and
  successful offline replay status for the included generator version

Count residuals mean exact_count / truncated_asymptotic - 1. Inverse error
fields explicitly distinguish approximation-minus-model from
approximation-minus-exact-integer-n. A negative value means the approximation
is on the smaller side under the stated convention. The fact that a smooth
inverse is close to an integer does not certify an exact ceiling at a jump.

Run `bash code/reproduce.sh` from the bundle root to regenerate fresh results
without modifying these reference files. The working directory does not need
to be the bundle root when invoking the script by a path.
