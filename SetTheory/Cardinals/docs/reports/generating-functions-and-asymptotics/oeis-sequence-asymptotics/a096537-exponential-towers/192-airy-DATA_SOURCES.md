# Data sources and provenance

Reviewed 2026-10-04. This is a bounded provenance statement, not a novelty or
priority claim and not a comprehensive literature review.

## Official integer fixtures

1. OEIS A096537, https://oeis.org/A096537, Paul D. Hanna, June 24, 2004.
   The displayed sequence supplies exactly 15 integer terms, indices 0..14.
   The defining EGF is the continued exponential with linear depth factors.
   The linked table credited to Vaclav Kotesovec advertises indices 0..200:
   https://oeis.org/A096537/b096537.txt . That table could not be retrieved
   during this package's source pass and is not an input. The package makes
   no claim of agreement against all 201 official b-file terms.

2. OEIS A096542, https://oeis.org/A096542, Paul D. Hanna, June 25, 2004.
   Its explicit example supplies nine complete polynomial rows, n=0..8,
   totaling 45 nonnegative integer coefficients. These are evaluated at
   y=1/2,1,2,3 and compared with the exact shifted-tower recurrence. Its
   displayed formula T(n,1)=n*A096537(n) has an index mismatch with the
   defining series. The package checks T(n,1)=n*A096537(n-1), which agrees
   with the cross-reference on A096537, for n=1..8. The fixture stores
   the coefficients and source attribution, not the incorrect formula.

These bounded data are transcribed in data/oeis_fixtures.json. They are
separate from generated regression data and mathematical proof. Consult
OEIS's current usage terms at https://oeis.org/wiki/The_OEIS_End-User_License_Agreement .

## Author-generated data

The 49 values in data/generated_coefficients_48.json (n=0..48) were computed
by the exact integer continued-exponential recurrence and retained as a fixed
regression vector. They are explicitly labeled author-generated, not official
OEIS b-file data. Checksums of both fixture files are pinned in check_exact.py.
Every mandatory replay computes these coefficients anew by a finite-height
recurrence and a triangular truncation of the same defining recurrence.
Those two algorithms are not represented as independent mathematical models.

Independent combinatorial checks come from (i) exhaustive Pruefer strings on
n+1 labels rooted at label zero, through n=7, and (ii) positive compositions of
n describing level populations, through n=12. These methods do not read the
regression vector or use the exponential coefficient recurrence. Their
outputs are generated during replay, not inherited as certificates.

## Numerical diagnostics and special-function inputs

The optional code/diagnose_mpmath.py evaluates finite towers and the stated
Airy expressions at arbitrary working precision. It is not interval arithmetic,
uses no fitted constant, and certifies no numerical digits or asymptotic claim.
Standard Airy facts used by the manuscript are available from NIST DLMF:
https://dlmf.nist.gov/9.2 , https://dlmf.nist.gov/9.7 , and
https://dlmf.nist.gov/9.9 . The manuscript gives the full source discussion.

## Exclusions

No full OEIS export, downloaded web page, raw paper, source-audit report,
private workspace path, or unrelated research file is included in the
allowlisted public package. No network call is made during replay or build.
