# Verification record

## Mathematical review

The complete proof underwent a separate review within this analysis against its exact counting
identities. The review specifically checked:

- the prescribed-Gram embedding count, including infeasible types and characteristic two;
- the exact likelihood and sign of its deviation from the uniform matrix law;
- the normalizing powers in the rank, defect, and mixed Gaussian moments;
- the conditional reduction to an independent smaller rectangular matrix;
- the zero-index cancellations that preserve uniformity in the dimension gap;
- both geometric interpolation grids and the infinite signed correction tails;
- the tensor-product correction, sharp total variation constant, covariance,
  and exclusive-or corollary;
- the relationship to the inherited square and increasingly tall results.

Two notation/wording ambiguities were corrected during that review. No
mathematical gap remained in the final reviewed proof.

## Exact computation

The supplied JSON summaries record successful runs of:

| Method | Cases / equalities | Outcome |
|---|---:|---|
| Exact marginal distributions | 116 parameter triples | PASS |
| Exact joint distributions | 46 parameter triples | PASS |
| Direct enumeration versus marginal formulas | 98 equalities, six cases | PASS |
| Direct enumeration versus joint formulas | 76 equalities, six cases | PASS |

Every probability in these comparisons is represented by an exact fraction.
The direct enumerator constructs actual matrices over the prime fields of
orders 2 and 3 and does not call the orbit-count or moment-inversion routines.

The formula implementation checks that the prescribed-form subspace types
sum to the appropriate Gaussian binomial coefficient. It checks distribution
normalization, nonnegative mass, alternating parity, normalized likelihood,
the likelihood sign, the optimal-event total variation identity, and agreement
with the classical positive-sum complement formula. The joint implementation
also checks each of its two complete marginals.

## Numerical constants

Rational upper and lower bounds for the infinite products follow from

    1 - sum(t_i) <= product(1 - t_i) <= 1.

The constant certificates use 64 factors of the even and odd products and
128 factors of the ordinary product. Rounded decimal displays of finite
distances come from exact rational values. The asymptotic leading values
use longer finite products than needed for the displayed precision.

## Limits of verification

No new Lean theorem or proof object is supplied. The upstream repository was
inspected as source material, and its formal verification does not transfer
automatically to this research note.

Finite exact computations verify the formulas in the tested cases; they do
not prove an infinite asymptotic statement. The complete symbolic argument in
the paper supplies that proof. Independent review and reproducible checks
support the result, while journal review and a formalization remain separate
possible next stages.

## Document checks

The 17-page PDF was compiled from the supplied source, and every page was
rendered and visually checked. The final build has no unresolved references
or overfull boxes. The archive includes all files needed to rebuild the
paper and all five Python programs.
