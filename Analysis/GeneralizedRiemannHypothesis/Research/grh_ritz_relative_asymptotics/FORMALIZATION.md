# Lean formalization dependency map (not implemented)

The mathematical note separates the analytic input from the abstract Hilbert space theorem. No Lean executable was present in the working container; the new results have not been kernel-checked. This map uses mathematical requirements, not guessed Mathlib declaration names.

## Phase A: finite rational / real algebra

1. Given a positive measure on distinct positive nodes with moments, define inner products of real polynomials, monic least-norm polynomials and the Hankel matrices.
2. Establish orthogonality and three-term recurrence by degree; show multiplication compressions are symmetric positive matrices. Show the Ritz eigenvalues are simple by `(t-r) P` being a multiple of the monic orthogonal polynomial.
3. For a fixed Ritz value, define `S = Q/(X-r)`, squared residual `v`, and normalized measure `ν`. Prove the identity `δ*A = v*I` using orthogonality, including the atom exclusion from the sum. Derive the finite inequalities by positive weights and the exact geometric remainder identity. This part can first be done with finite support; `exact_checks.py` is a rational example, not a proof assistant.

## Phase B: infinite spectrum

4. Model the Hilbert space as the real weighted `ℓ²` space or `L²(μ)` of an atomic probability-finite measure. Define multiplication by the atom coordinate. Compactness follows from finite-rank diagonal truncations and `x_i → 0`; trace and Hilbert–Schmidt identities follow from the positive summable atoms.
5. Prove polynomial density on a compact interval, compression min–max convergence, and weak concentration of the squared normalized orthogonal polynomials at 0 (Bessel's inequality and finite sets of atoms). Establish `h_(N+1)/h_N ≤ τ_2` by the monic minimizer.
6. Use fixed-atom isolation to prove relative residual sharpness, then summability from trace and Hilbert–Schmidt estimates.
7. Prove product convergence by dominated convergence for tail logarithms. Substitute into the exact identity for the common determinant scale. Establish the local tridiagonal compression inequality for residual moments, and the logarithmic norm law implication for the next correction.

## Phase C: analytic specialization

8. In the vendored Lake package, `import Main`; the actual exported input names are `riemannHypothesis : RiemannHypothesis` and `LFunction_eq_zero_re : DirichletLZerosOnLine`. Do not treat general automorphic GRH or simplicity as an available input. Use completed-function products and zero-count bounds to build the positive discrete spectra. The previously established Li moment rate from the article is an additional analytic theorem needed for the exact next-correction hierarchy; it must itself be formalized to close that dependency.
9. Apply the abstract theorem, then transform the atom estimates back to ordinates, handling a zero at distance zero separately. Verify the final `#print axioms` outputs after actual compilation with the pinned vendor toolchain. The root ProveIt `lake build` does not build the vendored package.

This is an implementation plan only, with no claim of formalization or successful compilation.
