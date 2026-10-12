# Additive integration contract

This package should be preserved as a research delivery until normal ProveIt
intake assigns a report location. It makes no native patch and changes no default.

## Required source boundary

The caller supplies a validated rational `Source(n, equations, conflicts)`, an
objective with the same coordinate labels, coordinate-zero restrictions, and an
exact source partition. `compile_two_block` accepts unsigned sign-separated
cross rows; `compile_variable_separator` duplicates supplied master coordinates
and rejects nonlocal private constraints. Neither function checks 3-manifold
links, peripheral markings, or ancestry from a knot diagram.

The original source must be obtained from maintained authenticated producers.
A caller-supplied descriptive source label is not authentication. Positive
coordinates are checked directly against that original source; the geometric
consumer must bind it to its source certificate in the repository's usual way.

## Output semantics

`POSITIVE` means that an exact positive source matching ray passed the independent
algebraic verifier. On genuine standard normal coordinates it represents a
connected surface, not automatically an essential disc. Forward it to the existing
topology, essential-boundary and provenance checks.

`NO_POSITIVE` is complete only for the exact algebraic query and restrictions
that were exhausted. It is not a knottedness verdict. No short negative-result
certificate is provided here. `ResourceLimit` or failed source compilation must
lead to a fallback, an explicit error, or `INCONCLUSIVE`, never a negative verdict.

## Example adapter

`integration/source_query.py` constructs the compilation, prepares the kernel,
solves the query, reconstructs original coordinates, performs support descent,
and independently checks a primitive source ray. It returns no `UNKNOT` or
`KNOTTED` status. It is illustrative glue, not a native integration claimed to
have been exercised in a full checkout.

For repeated objectives, retain `Compilation` and `Prepared` objects. Cache keys
must bind exact equations, labels, conflicts and port maps. Slopes alone are not
safe keys: distinct rays can have identical ports but different admissibility and
witness maps. The current tables store every feasible compatible mixture at each
atlas vertex; streaming is a future option for lower memory.

## Promotion gate

Compare with the maintained native sector and branching producers on identical
source-authenticated inputs. Include failed compilation attempts, preparation,
all checking, cancellation, integer sizes and peak memory. Exercise complete
negative queries and corrupted packets. Use independent producer-disabled source
replay and preserve small-input regressions. The delivered 20.39x ratio is against
a standalone unsplit support enumerator, not the best native backend.

The main implementation only accepts entrywise nonnegative port maps. The signed
orthant-lift theorem is proved in the article but is not a separate exposed
backend. Its new local rays cannot be assumed to equal the old cone's rays.
