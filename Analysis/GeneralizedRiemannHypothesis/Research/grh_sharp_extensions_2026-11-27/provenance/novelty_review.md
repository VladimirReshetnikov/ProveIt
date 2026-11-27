# Novelty and source review

Date: 27 November 2026. This records a scoped comparison, not an exhaustive
worldwide priority search.

## Pinned sources

The upstream Lean repository was cloned and inspected at commit
72fead102f663d5c7a407964a13dc0cf9d977207. The ProveIt article was fetched at
22e5c8b7dda558fd9a50b61465483cb4c0433694. All 21 section files were available
for targeted full-text comparison. The newest incoming archives concerning
exact symplectic compressions, p-adic symplectic corners, and another
symplectic-compression treatment were also examined to avoid repeating
their general compression laws.

## Algebraic result

Already in the Article:

- `sel:thm:smith`: relation-module Smith decomposition and exact lengths.
- `sel:thm:tracedepth`: exact trace depth under full integral matrix span.
- `sel:thm:bad`: a nonmaximal-order example with torsion invisible to traces.
- `sel:sec:open`: asks for a measured-defect extension at bad coefficient primes.

New proposed statement: the sharp universal finite-level correction
`min(n,a)+(d^2-1)min(n,e)`, with the conductor defined by containment of a
scaled full matrix ring in the image order. The proof combines a singular
pencil obstruction with compensation between the longest and shortest
relation exponents. Distinct examples show sharpness of the total bound
and of the longest-exponent loss.

Classical antecedents inspected: Carayol (1994); Serre/Rouquier's primary
1993 exposition of trace rigidity; trace-comparison context in Brumer et
al. (2019). Searches also surfaced Maranda-type lattice rigidity as related
background, but no matching exact inequality was identified in this search.

Representative search strings:

- `"congruence modules" "Burnside" trace`
- `"trace" "d^2-1" "congruence" representations`
- `"approximate Schur" lemma representations p-adic`
- `"intertwiners" "Smith" "congruence" representations`
- `"congruence" "trace" "conductor" "absolutely irreducible" representations matrices`

## Analytic result

Already in the Article:

- `ana:thm:binomial`: the two-step irrational binomial filter, with
  error O(log r/sqrt r), using (r+1)^2 statistic observations.
- `ana:q:family`: asks about better shift schedules and real prime
  statistics for individual nonreal central orders.
- `zer:thm:balancing` and related proofs: continuous convolution projection.
- `rec:thm:quaddecode` and nearby recovery arguments: interval/sinc powers.
- `rec:thm:fwidth`, `rec:thm:hblock`: filters using prescribed frequencies.

New proposed statement: finite positive-grid projection with the explicit
repeated-alias bound O(log k/k^2), giving O(log^3 N/N^2) error in the actual
number N of distinct ramp samples, logarithmic support, normalized noise
control and preservation of the one-sided detector. The alias lower bound
concerns the abstract spectral-count class only.

The uniform-average cascade is classical: Hogenauer (1981), equation (3),
contains its polynomial. This is acknowledged in the report. Unser and
Aldroubi (1992) provide related spline-filter background; the construction
of a convolution filter is not claimed as new. Bennett et al. (2021)
supplies primary zero-counting context.

Representative additional search strings:

- `"finite grid" "central zeros" Dirichlet`
- finite positive filters central zeros Dirichlet L functions
- cascaded uniform average filter Hogenauer
- polynomial spline signal processing algorithms Unser

## Review status

The algebraic proof received an independent internal review of all cases,
the finite valued-field extension, the pencil argument, the compensation
inequality, and the examples. The analytic proof received an independent
review of constants, aliases, sample counts and noise scaling. A second
pass checked the expanded Mellin and Landau arguments. No mathematical
gap was identified in these reviews.

This does not establish global priority, external peer review, or a Lean
formalization. No claim of resolving an unrelated famous conjecture is
made. The concrete advances are the two proved extensions of the supplied
research program.
