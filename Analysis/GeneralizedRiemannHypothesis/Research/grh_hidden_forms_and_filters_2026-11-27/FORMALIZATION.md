# Formalization plan: learning a hidden alternating form

## Status

The mathematical proof is complete in `papers/hidden_symplectic_forms.tex`. The supplied
Python programs perform exact finite-field checks and reproducible recovery
examples. No Lean or Rocq proof of the new theorem has been compiled, and the
programs are not presented as a formal proof of its asymptotic assertions.

The theorem is unconditional. Its formalization need not import the upstream
RH/GRH development. The connection with the repository's compression model
can be formalized through the self-contained fibre-count argument in the paper.

## Mathematical interface

Fix a finite field `K`, an even integer `n >= 4`, and `V := Fin n → K`.
Represent an alternating form by its coefficients above the diagonal, retaining
the zero-diagonal condition in characteristic two. Its coefficient space has
dimension `D = n * (n - 1) / 2`. Represent a plane by a two-dimensional submodule
of `V`, or by the equivalence class of an independent ordered pair under `GL₂(K)`.

The hidden parameter is a nondegenerate alternating form modulo nonzero scalar.
Its distribution is uniform on a finite set. The null distribution is a product
of uniform plane distributions. The planted distribution is a finite mixture of
products of uniform distributions on the planes isotropic for the chosen form.
Finite sums suffice until the last asymptotic section; measure-theoretic
conditioning is unnecessary.

## Suggested modules and dependency order

1. **AlternatingForms.** Alternation, nondegeneracy, even rank, quotient by scalar,
   dimension of the form space, and kernel dimension by rank-nullity. In
   characteristic two, use alternation itself rather than merely skew symmetry.
2. **PlaneIncidence.** Count ordered independent vector pairs; divide by the
   common number of bases per plane. Prove the single-form proportion `p_n`, then
   the exact two-form incidence formula by partitioning nonzero first vectors
   according to dependence of the two associated linear functionals.
3. **FormCounts.** Count nondegenerate forms using transitivity of `GL(V)` and
   symplectic stabilizers. Prove the upper bound on the number of forms of rank at
   most `R` by choosing a kernel subspace and an alternating quotient form. The
   coarse Gaussian-binomial estimate is sufficient; no exact rank distribution
   is needed.
4. **HiddenFormLikelihood.** Define finite probability mass functions `P` and
   `Q`, the number `Z` of compatible projective forms, and prove
   `P(x) = Z(x) * Q(x) / (M * p^t)`. Derive the second-moment identity, union
   bound, uniform posterior, and exact optimal Bayes recovery formula by finite
   sums. A deterministic tie-breaking rule on a finite ordering realizes the
   optimal decision.
5. **FiniteBounds.** Isolate proportional pairs, pairs close in rank to a scalar
   multiple, and the remainder. Prove the constants `rho_q`, `K_q`, `A_q` and the
   finite chi-square estimate. Index recovery failures by projective points of
   `Alt(V)/span(H)`; establish that each such point has `q(q-1)` representatives.
6. **Threshold.** Establish convergence and positivity of the two infinite
   products and the elementary bounds at `R = floor(n/5)`. Prove the bounded
   critical-window chi-square limit, transfer to total variation by
   Cauchy--Schwarz, then obtain arbitrary diverging additive gaps by monotonicity.
   This avoids uniform limit arguments for arbitrary sample sizes.
7. **CompressionBridge.** Count solutions of `AᵀB-BᵀA=H` for full-row-rank
   `(n-2) × n` matrices `A`, show the count is constant precisely on isotropic
   kernels, and prove the same conditional ancillary law given the kernel in
   both models. Derive exact equality of statistical distances in the
   conditioned block and plane experiments.

## Proof boundaries to preserve

- Separate the exact finite formulas from asymptotic estimates.
- The source form is chosen once and is shared by all observations.
- Only its projective class can be recovered.
- State the full-row-rank conditioning explicitly in the matrix corollary.
- Define total variation as half the sum of absolute mass differences, and
  chi-square with the planted distribution in the numerator and the null in the
  denominator.
- The exact critical-window second moment does not establish a Poisson law or
  any other limiting law for the number of compatible forms.
- Use the finite point count to justify the uniform prior and posterior; do not
  replace either by a continuous parameter-space argument.

## Computational certificates

The independent exhaustive checks enumerate the actual two-planes and actual
nondegenerate alternating forms in dimension four over `F₂` and `F₃`. They check
the complete common-isotropy histogram against the rank formula. In the binary
case, a dynamic program over actual linear spans of plane coefficient vectors
computes exact total variation and recovery probabilities for up to 24 samples.

`code/recovery_demo.py` is a separate, elementary demonstration over prime
fields. It samples an invertible change of basis, constructs a nondegenerate
alternating form, samples independent isotropic planes, solves the associated
homogeneous linear equations, and checks the recovered line by exact modular
arithmetic. Its output is a reproducible example, not an asymptotic experiment.
