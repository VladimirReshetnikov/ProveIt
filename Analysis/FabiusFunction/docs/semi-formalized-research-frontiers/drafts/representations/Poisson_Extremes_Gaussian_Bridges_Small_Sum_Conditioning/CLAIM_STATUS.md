# Claim and verification status

## Manuscript proofs supplied

- Theorem 1.1: Conditional maximum logarithmic CDF equals
  -N Gamma(1-1/p,b+z) + O(N^(-1/2)), for each fixed p>1 and bounded z.
  Here N=t^(1/p), t is the EXACT mean-matching tilt, and
  b+(1/p) log b=log N. The theorem gives all FIXED inverse-logarithmic orders.
- Theorem 1.2: Polynomial marked extremes, their submacroscopic locations,
  and mutual limiting independence from the Gaussian bridge and Exp(1) slack.
- Theorem 1.3: Full marked-Poisson/bridge/slack convergence for every
  uniformly lacunary positive weight sequence, including the Fabius case.
- Lemma 3.2: A quantitative density local limit theorem, including the
  capped polynomial arrays required for the maximum calculation.
- Exact independent maximum intensity integral, monotone lattice-error bound,
  capped-product likelihood, and the necessary cap-mean/variance estimates.
- Upper order statistics and the vanishing largest mass fraction.

## What is resolved relative to the inspected repository

The qualitative point-process and bridge-independence portions of Question 7
in Sharp_Conditioning_Laws_Fabius_Lacunary_Series are addressed for its full
uniformly lacunary class. Its request for explicit rates on the full joint
process is NOT completed.

The newer Sharp_Conditioning_Laws_Uniform_Random_Series already establishes
general variance-fraction conditioning and polynomial variance clocks.
Those are acknowledged background, not originality claims here.

## Executed checks

- Six symbolic checks: v=m-a*m' and expansion coefficients of orders 0,...,4.
- Twelve floating-point conditional and independent maximum-CDF diagnostics.
- One stability rerun changing all of head length, tail order, Fourier cutoff.
- Independent high-precision integral check of the p=2 mean constant.
- PDF compilation with resolved references and visual page review.

The symbolic tests validate formulas, not the complete probabilistic proofs.
The numerical tests are not rigorous error certificates.

## Not claimed

- Lean or Rocq verification, a repository build, or a commit to ProveIt.
- External peer review or exhaustive global historical novelty verification.
- A solution of a named published conjecture outside the repository.
- Total-variation convergence of lattice-located points to continuous locations.
- Uniformity as p approaches 1 or infinity, as the expansion order grows,
  or as the centered maximum height leaves bounded windows.
- The same logarithmic correction coefficients for arbitrary slowly varying
  perturbations of the weights.
- Exact-shell, null-event, nonuniform, random-weight, or multiconstraint extensions.
- Interval-certified CDF values or bit-complexity bounds.
