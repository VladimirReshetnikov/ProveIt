# Proof audit

## Category and definitions

V_d is the solution set of three displayed min-plus equations. For d=p/q>0,
all exponent vectors in the defining equations have nonnegative integer
coordinates. Thus the construction stays inside the source's stated category.
The Hilbert function uses a single coefficient vector with strict witnesses,
and the principal cutoff is i+j <= k.

## Upper bound

1. Strict certificates form an open subset of coefficient space. Avoiding
   finitely many proper endpoint-tie hyperplanes preserves every original
   witness and makes endpoint winners unique.
2. On either horizontal segment, slopes of successive unique minima strictly
   decrease. Parallel restrictions cannot both be unique winners.
3. Every support term is active on at least one component; the support is the
   union of the two active sets, not the sum of their sizes.
4. If each segment uses k+1 slopes, both contain the unique total-degree
   exponent (k,0). Hence the union has size at most 2k+1.
5. If the facing endpoint winner is shared, its slope matches on both segments
   and subtracting the overlap gives at most k+1 terms.
6. Otherwise, adding strict endpoint inequalities gives

       d(P-r) < s-Q <= k-r <= k.

   Thus P-r <= ceil(k/d)-1, including exact divisibility cases. The resulting
   count is at most k+ceil(k/d)+1.

## Lower bound

With m=min(k,ceil(k/d))-1, omega=min(1,d), sigma=omega*k-d*m:
0<=m<k and sigma>0 for k>=1. The A-row exponents (i,k-i) and B-row exponents
(j,0), j<=m, are disjoint and all lie in the triangular degree region.
The rational epsilon, eta, delta formulas put all witnesses strictly inside
the prescribed components. Within-row gaps are positive multiples of epsilon
or eta. At an A witness every B term has value at least 11*sigma/16>0, while
the selected A value is nonpositive. At a B witness every A term has value at
least omega*k, while the selected B value is <=omega*k-delta.

The degree-zero case is treated separately, avoiding division by k.

## Box result

For d>=1 the same lower certificate is allowed. The upper comparison needs
only s<=k, not s<=k-r, to derive d(P-r)<k. Therefore the same sharp result
holds for the box. The total-degree-specific bound 2k+1 is NOT reused as a
box argument.

## Consequences

All limits follow directly from the exact formula. At rational d=p/q>1,
the error ceil(qk/p)-qk/p is bounded, periodic, and zero precisely at multiples
of p. This proves the exact least eventual quasipolynomial period. Polynomial
failure is not inferred from a finite list of values.

## Checks versus proof

The verifier directly checks all ordered competing term/witness inequalities.
It separately enumerates a relaxation of the necessary integer endpoint
conditions. No false claim of exhaustive enumeration of arbitrary tropical
polynomials is made. The reported finite results do not certify formal logic
and have no status equivalent to a proof-assistant kernel check.
