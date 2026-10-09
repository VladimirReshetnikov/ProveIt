# Proof status and reviewer checklist

## Central assertion

For each fixed density in (0,1), the indicator-set cut discrepancy at a small four-cycle excess has an exact universal normalized envelope. The negative branch is locally globally optimal, has the expansion through degree six stated in the article, and all equality cases are the stated two-block kernel up to relabeling.

## Proof, rather than ansatz

The key review point is the distinction between a critical point and a global maximizer. Section 5 first localizes *every* maximizer of a compact five-variable relaxation. The multiplier equations improve degree coefficients from O(t^2) to O(t^3) and mass shifts to O(t^2). The six-variable rescaled Jacobian has determinant -1. The analytic implicit-function theorem then gives uniqueness, and transposition gives symmetry. This order of argument excludes a hidden nonsymmetric competing maximizer in the local regime.

The pointwise probability constraints are omitted only for the upper-bound relaxation. Section 7 explicitly realizes its optimizer inside [0,1]. Strict monotonicity of the envelope and equality in compression classify equality cases for arbitrary kernels, not merely step kernels.

## Auxiliary results

- The degree identity and sharp 3/2 inequality hold independently of the local endpoint theorem.
- The explicit global cut bound is universal, but its correction coefficient 2/3 is not asserted sharp.
- The near-extremizer result controls distance to a two-way compression, not all optimal parameters and not L1 distance. For symmetric input that compression need not be symmetric away from equality.
- The O(n^-2) realization uses weighted symmetric matrices with diagonal weights. Its mean and homomorphism four-cycle excess are exactly preserved.
- Simple-graph approximation is a fixed-D limiting statement. It is not exact finite attainment or a quantified joint n,D theorem.

## Independent review still needed

Written proofs and symbolic checks are supplied, but no independent mathematician or proof assistant has certified the package. Priority is not established. A positive explicit global-optimality radius is not certified. No numerical optimizer is used as a mathematical lemma.

## Useful review targets

Check the normalization of the cut norm and homomorphism density; the signed mixed term in the scalar constraint; the global-to-local compactness argument; the powers of t in the rescaled stationary system; the degree penalty when one degree variance is zero; the omitted probability constraints; and the weighted-versus-unweighted distinction.

The PDF and code agree on all six displayed Taylor coefficients. Symbolic identities include the mass-curvature calculation and inverse-envelope expansion, to guard against derivative and series-transcription errors.
