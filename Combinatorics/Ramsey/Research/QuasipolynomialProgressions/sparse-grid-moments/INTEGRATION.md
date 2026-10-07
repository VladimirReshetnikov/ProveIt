# Integration notes

## Proposed placement

```text
Combinatorics/Ramsey/Research/GowersSzemeredi/sparse-grid-moments-quadratic-closure/
```

This package is standalone. It does not select a source number in the existing merged refinement report. No GitHub write, commit, pull request, or formalization-status change has been made.

## Connections

The immediate OpenAI source interface is `ap:path:grid` in the relative-detection section of the arithmetic-progression manuscript. That lemma assumes q ≤ j. The present article provides an exact finite-field relation matrix and a sharp model obstruction outside that sufficient range, not an audit of the entire analytic proof.

The ProveIt connection is local quantitative analysis of configuration moments and careful separation between exploratory computation and trusted proof. The main integration objects are:

- `M_d(S)`, a finite matrix of coordinate margins;
- its kernel `K_d(S)` and orthogonal complement `H_d(S)`;
- the one-hot quadratic site matrix `v_alpha v_alpha^T`;
- the quadratic closure and rank enumerator of the site span;
- weighted-Laplacian rank counts and the exact graph-girth convergence exponent;
- exact finite-field moment and correction formulas.

All LaTeX theorem/equation labels use `gm:` to reduce collision risk.

## Possible Lean development order

1. Define finite patterns and margin matrices over a field.
2. Establish zero-extension compatibility and the support bound by slicing.
3. Prove the one-hot matrix representation of `K_2(S)`.
4. Prove rank-one rigidity and the closure count `(Q-1)|cl_2(S)|`.
5. Formalize finite additive-character orthogonality and the bilinear identity `E psi(x^T A y) = Q^(-rank A)`.
6. Combine these with exact marginal normalization to obtain Theorem 7.4.
7. Prove the weighted-Laplacian forest/cycle ranks and the shortest-cycle nullity bound; derive the girth law.
8. Add the plane Gram counts and kernel double-count for the all-field cube enumerator.

The proof of the general p-reduced polynomial relation theorem can be developed in parallel, using multivariate polynomial coefficients. General mixing and total variation need additional finite Fourier/probability infrastructure.

## Certificate design

A prospective checker could accept a finite pattern, a margin matrix, a verified row reduction, and expressions representing hidden site matrices in the original span. The checker would validate the algebra and invoke general proved theorems. Merely trusting the output of `verify.py` would not create formal status.

## Integration caution

Do not promote the global arithmetic-progression claim, the finite-field/torus comparison, or the new manuscript's novelty status solely on the basis of this package. Theorem hypotheses and the precise computational scope are recorded in `THEOREM_STATUS.md`.
