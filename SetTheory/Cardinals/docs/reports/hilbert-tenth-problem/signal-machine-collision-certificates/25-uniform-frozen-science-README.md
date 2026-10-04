# Uniform four-particle timing extension

4 October 2026. Research proof package; no article or upstream modification.

## Result: conditional proof, independent review PASS

For a fixed one-dimensional conservative CA with positive integer state weights, unique vacuum and at most one weight-one label, total mass at most four admits one finite timed chart family uniform in all initial coordinates:

* finite Presburger input-residue cells;
* at most two free natural evolution parameters per chart;
* affine stationary-frame spatial outputs and total-degree-at-most-two time;
* fiberwise canonical ownership of every complete timed configuration.

A strict affine-domain lift uses at most three additional, uniquely determined initial-gap quotients, hence at most five natural chart variables. This is not a claim of two total variables for literal affine domains over unrestricted raw coordinates.

The key missing step beyond the inherited fixed-input result is symbolic contraction up to the first bounded-core reset. Its cycle count is piecewise affine in initial gaps, its anchor affine, and its arrival time quadratic. Thereafter only fixed templates for finitely many core states are required. Zero-net-gap cycles retain input-dependent periods and the n*D clock term. No quadratic expressions appear in domain guards.

The construction implies uniform stationary-frame untimed Presburger reachability. A selector-safe private copy of external inputs also gives a fixed-rule finite-arity uniform timed quartic via the inherited compiler. The proof depends explicitly on the source-17 section mechanism and source-18 fixed-input charts. No published-priority claim, implemented all-rules compiler, or formal verification is asserted.

## Files

* PROOF-NOTE.md: full conditional proof and exact chart syntax
* REVIEW.md: independent scoped PASS review
* check_arithmetic.py: fresh standard-library arithmetic checks, with no upstream imports or saved schedules
* arithmetic-check-results.json: passing receipt

Arithmetic checks passed 26,733 first-contact interval cases, 69,800 direct contracting-cycle comparisons over 1,396 words, 105 huge-integer contractions, 1,538 nonnegative-cycle guard cases and 225 degree-substitution checks. These fixtures do not prove the general CA theorem.
