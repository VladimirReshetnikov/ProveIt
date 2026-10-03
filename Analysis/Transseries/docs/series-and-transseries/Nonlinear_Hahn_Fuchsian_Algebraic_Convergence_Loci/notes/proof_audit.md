# Proof audit

## Precise domain

The exponent monoid Gamma is a nontrivial, well-ordered additive submonoid of
the nonnegative real numbers, contains zero, and has a least positive element delta. The paper uses
ordinary real order. Solutions have positive valuation and contain no
logarithmic powers. The matrix A is fixed, finite-dimensional, and complex;
Jordan blocks and nonreal eigenvalues are allowed.

The expression F is a formal power series in finitely many unknown components,
with Hahn coefficients. Its x-exponent-zero constant and linear coefficients
vanish. Analytic results additionally assume the joint absolute majorant
specified in equation (2.8).

## Dependencies checked in the mathematical argument

1. Exact coefficient antidiagonals are finite, even when a bounded interval
   contains infinitely many exponents. The finite ancestor set uses exact
   divisibility in Gamma, not a bounded enumeration.
2. Nonlinear substitution gains at least delta in differences. This gives a
   unique formal candidate for every resonant parameter value, including
   incompatible ones. The actual equation has precisely the recorded
   finite resonant residual.
3. Kernel and cokernel projections are distinct objects. Right inverses at
   singular matrices use separate domain and codomain complements.
4. Every resonant parameter has positive exponent weight. Below a fixed real
   cutoff only finitely many parameter monomials are possible. This remains
   true with infinitely many coefficient exponents in that window.
5. The spectral cutoff includes ALL positive real eigenvalues, including
   those that are not members of Gamma. The set of exponents above it has
   a right-hand gap; the inverse is uniformly bounded there. No left gap is
   assumed for the bounded-window or algebraic-locus theorems.
6. On a bounded exponent window, absolute convergence is equivalent to
   unweighted coefficient summability. Above it, an explicit Banach
   contraction applies after shrinking the x-radius and solution ball.
7. The quotient of all window families by the summable subspace is purely
   algebraic. Only a finite-dimensional span of coefficient-family classes
   is used. No quotient topology, continuity of its coordinates, or effective
   summability-decision algorithm is assumed.
8. Parameter monomials whose weight equals the cutoff contribute at only
   one possible exponent and are summable. This is why the analytic degree
   bound uses a STRICT inequality, and top-weight resonant parameters do
   not enter the additional convergence equations.
9. Uniform convergence on compact parameter loci uses summable representatives
   of finitely many coefficient families and a uniform tail contraction.
   The off-locus holomorphic extension is not asserted to solve the full
   original equation.
10. The universal converse constructs a formal solution in an invariant
    eigenvector line. An arbitrary functional with ell(v)=1 is used; it is
    not required to be a left eigenvector. This avoids a Jordan-block flaw.
11. The arbitrary-variety construction has an auxiliary affine factor from
    free top resonant coefficients. It realizes exactly the prescribed
    variety after those coefficients are normalized to zero.
12. The scalar threshold example cancels its exact resonance but retains
    the generated near-resonance coefficients. The formulas and compatibility
    are checked independently in exact arithmetic on finite restrictions.

## Verification performed

The exact Python/SymPy run checks 21 finite systems and 670 scalar equalities.
The infinite-support theorems rely on the written proofs, not those finite
computations. No Lean code for the new results was supplied or executed.
The existing repository Lean support module was inspected but not rebuilt.

The proof audit did not identify an unresolved logical step in the stated
arguments. This is an internal audit, not an independent correctness
certification. Historical novelty has not been independently established.

## Boundaries not crossed

- No claim about all levels of the full transseries field.
- No claim that every formal solution containing arbitrary logarithms is
  classified.
- No claim that finite input data decide absolute convergence in general.
- No claim that divergent Hahn coefficients prohibit all analytic or
  renormalized asymptotic realizations.
- No extension of the finite-degree argument to arbitrary non-Archimedean
  exponent groups.
- No proof-assistant verification or independent peer review claimed.
