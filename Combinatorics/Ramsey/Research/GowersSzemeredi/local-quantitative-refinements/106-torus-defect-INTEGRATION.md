# Integration plan

## Suggested destination

```text
Combinatorics/Ramsey/Research/QuadraticAffineLocalization/torus-defect-laws/
```

The directory is a suggestion, not a claim that this path already exists.
Copy the package into a suitable research directory after review. No repository
files were modified or uploaded by this delivery.

## Suggested index entry

> **Torus Defects and Sharp Affine Partition Laws** (2026-10-07).
> Proves the sharp leading affine-partition cost of every fixed product of
> `s`-arm finite-field crosses, an exact torus/dimension defect identity,
> quantitative point-mass rigidity, and the large-field regularized rate
> `rho_s(q) ~ s*q^(1-1/s)`. Includes full ordinary proofs and exact finite
> corroboration. Not Lean-verified; no new integer Szemerédi bound claimed.

Link `article.pdf`, `article.tex`, and `theorem_status.json` from the index.
Do not mark these results as formalized solely because `verify.py` passes.

## Dependency relationship to earlier work

The preceding project article *Sharp Affine Localization for Quadratic Phases*
proved the exact two-cross cost and the singular-fiber/binomial reduction. Its
Questions 13.1–13.2 asked for higher-product growth and improved regularized
bounds. This package resolves the leading fixed-product exponent **and
coefficient**, and the large-field regularized scale. It does not resolve the
exact three-cross question or the exact rate at a fixed field.

The source snapshot of that preceding article was inspected from the user's
Library. Its current public repository path was not established; update its
bibliographic entry with the actual path after locating it during integration.
The manuscript is mathematically self-contained, so the absence of that path
does not leave a theorem dependency unsupported.

## Formalization sequence

1. Define partitions of actual affine subsets with nonemptiness, coverage, and
   pairwise disjointness. Prove product submultiplicativity.
2. Prove coordinate projection capacity and orthant containment for `q > 2`.
3. Prove the nonnegative dimension weights and the exact defect identity over
   rational numbers. Add congruence rounding and the finite lower bound.
4. Construct support-level matchings and their disjoint line partitions.
5. Prove the torus equality classification, Stirling enumeration, and the
   finite stability bounds.
6. Add the fixed-parameter asymptotic theorem and point-mass proportions.
7. Add the analytic convexity/regularization layer and the independently
   reproved binomial reduction for quadratic products.

Keep this project separate from the integer progression-length interface until
an explicit length-preserving transfer theorem has been established. In
particular, do not replace `quadraticFamilyBudget` by the affine cell count.

## Checks before merging

Run `python3 verify.py` with assertions enabled, rebuild the PDF, inspect the
source manifest, and arrange independent proof review. After editing any file,
regenerate checksums; the supplied `SHA256SUMS` describes the delivered snapshot,
not future rebuilds. TeX-generated timestamps may change the PDF hash even when
the mathematical source is unchanged.
