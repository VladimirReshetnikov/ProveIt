# Independent final integrated LaTeX audit

Audited file: `release/compacted-binary-trees.tex`.

**Approved mathematical content, SHA-256:**

    3977a7a05b8244e19cc09a6f44f8e7b69cb591f58eba492a5a5ae76a9ff58ecb

I read the complete integrated LaTeX article, including the self-contained Jacobi appendix, and checked it against the approved amplitude proof, exact positive-model report, inverse supplement, comparison supplement, independently computed coefficients, and shared Jacobi lemmas.

The integrated article preserves:

- The exact signed recurrence, factorial normalization, gauge, shifted support and parity
- The global delay norm bound and cancellation of the nonsummable scalar drift
- Both finite-memory lemmas, the initial domination argument, scalar-amplitude convergence, arbitrary-order residual construction and zero-limit bootstrap
- The even-time endpoint extraction, use of the published lower bound for strict positivity, and common amplitude normalization
- The independent logarithmic and relative coefficients, normalized initial-value interpretation in the coefficient-field argument, and all-orders quantifiers
- The three-/four-state and positive renewal models, their exact transitions and limited symmetry obstructions
- The Lambert anchor, inverse corrections, Newton exponents, discrete two-candidate bracket and certification qualifications
- The relaxed/compacted ratio cancellations, smooth inverse gap, and separate coarse discrete threshold consequence
- The shared Jacobi appendix's form identity, coercive compactness argument, parity singular gap, finite quantitative quasimode, adjoint projection estimates and positive spectral product

Two transcription/domain clarifications were requested and are verified in the approved revision:

1. The local coefficient expansion for ell_(N,j) is explicitly restricted to `1<=j<=2sqrt(N)` on physical support, because ell_(N,0)=0.
2. The leading endpoint of order N^(-1/2) is explicitly stated for even N; the parity-restricted vector vanishes at height zero for odd N.

Neither clarification changes the argument. No mathematical correction remains outstanding. The article correctly separates mathematical convergence from uncertified numerical amplitude estimates and distinguishes an independently checked research proof from publication or peer review.

Any subsequent source change requires a hash update; a layout-only revision can be approved by comparing it against this audited baseline. This signoff concerns mathematical content and transcription, not visual PDF layout or bibliographic novelty claims.

## Final release hash approval

**Final approved LaTeX SHA-256:**

    2edaccb599540a52c8ebf58cca4f16e675b1501e542bdd23943df5b5a76f0476

The only differences from the previously approved source are bibliography-local formatting: a group using small font, zero paragraph/parse separation, and 2pt item separation. Removing exactly those six formatting lines reproduces the previously approved SHA-256 `3977a7a05b8244e19cc09a6f44f8e7b69cb591f58eba492a5a5ae76a9ff58ecb`. Thus the final mathematical text, formulas, proof and references are byte-for-byte unchanged. This final source is approved for release.
