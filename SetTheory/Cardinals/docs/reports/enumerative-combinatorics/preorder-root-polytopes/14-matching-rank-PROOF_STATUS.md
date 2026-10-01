# Proof status and independent-review boundaries

## Proved in the article

1. The first actual-rank Newton inequality for any directed disjoint-support
   enumerator, with nonnegative tail/head activities. The proof reduces to
   the classical Motzkin-Straus inequality, whose compression proof is given.
2. Its complete unweighted equality classification: equally sized arc
   families in underlying star/triangle components; only stars in bipartite
   graphs. The resulting polynomial is (1+q*t)^d.
3. Actual-rank ultra-log-concavity for every bipartite graph of matching
   number <= 3. The mixed-cover case has a full elementary counting argument
   and sum-of-squares certificate. The one-shore case invokes a published
   theorem (Roehrle-Ulirsch), not a speculative repository claim.
4. A rank-three representable-bimatroid counterexample and the exact
   rectangular criterion for the dense Vandermonde-product family.
5. Exact bipartite and directed population-kernel formulas, fixed-parameter
   counting complexity, exact support sampling, and the weighted extension.
6. Polynomial clone dependence and one-parameter exact decidability.
7. The displayed connected rank-four family and strict inequalities at all
   three internal indices.

The disjoint-union corollary additionally invokes Liggett's classical finite-
order convolution theorem. Standard finite graph, real arithmetic, and
linear algebra arguments are used throughout.

## Imported repository boundary

The identification of the directed coefficients with the gamma coefficients
of the original preorder support-counting polynomial uses the repository's
support bridge (Parts IV-V). Its overlap-cancellation argument is reproduced,
but the geometric bridge itself is not independently re-proved here.

The full-lattice-point exact-sampling composition additionally uses the
Part IX two-flow bijection. That imported bijection is neither re-proved nor
reimplemented. The executable sampler in this package samples supports only.

## Executed vs specified

Executed: unweighted exact counters, integer-population bipartite formulas,
exact uniform support sampling, rational polynomial certificates, exhaustive
small finite comparisons, direct small preorder polytope checks, matrix minors,
and export of 24 rank-four formulas.

Specified and proved but not implemented as general user-facing solvers:
nonuniform rational-activity sampling, generic one-variable root/sign analysis,
and the composition producing full-coordinate lattice points.

## Unresolved here

- The matching-rank normalization conjecture at arbitrary rank.
- All connected rank-four graphs (the supplied 24 templates reduce this to
  specific positivity questions but are not proofs of those inequalities).
- Weighted rank-three ULC beyond the first inequality.
- General higher-height preorder gamma log-concavity or rank-ULC.
- General real-rootedness, flag-polytopal realization, or higher equality cases.
- Optimal parameter dependence or counting-complexity lower bounds.
- Exhaustive priority certification and independent referee acceptance.
- Lean formalization or any claimed successful proof-assistant compilation.

## Review priorities

Check the rank-three common-neighbor correction: C = alpha*(y+z) +
beta*(x+z) - alpha*beta*z. Omitting the last term counts some supports twice.
Check that exterior tails and heads are disjoint, producing
binom(N,p)*binom(N-p,q), not binom(N,p)*binom(N,q).
Check that the matrix's linear rank three is not the matching number of its
nonzero graph. Finally, keep imported geometric statements separate from the
independent graph and polynomial results.
