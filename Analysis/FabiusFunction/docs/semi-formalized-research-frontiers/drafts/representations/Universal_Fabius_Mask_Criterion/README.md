# Universal Comparison of Fabius Observation Masks

A self-contained seven-page research companion.

The report proves:

1. For arbitrary independent bounded coordinates with summable caps, one observation mask universally simulates another under every total-sum reweighting exactly when its observed-sum law has the target observed-sum law as a probability convolution factor. Masks may overlap, have unequal cardinalities, or be countably infinite. Arbitrary independent additive noise and all-threshold formulations are included.
2. For common-tilt uniform coordinates with reciprocal-integer geometric caps, universal dominance is equivalent to prefix-count dominance. The result allows randomized kernels pooling every source observation; the deterministic residue map already realizes the full possible order.
3. For finite equal-cardinality masks with commensurate caps, universal dominance is equivalent to the explicit q-integer quotient being a polynomial with nonnegative coefficients. A posterior kernel works independently of the common tilt.
4. Classical Gaussian polynomials yield positive comparisons beyond pairwise cap divisibility, while the polynomial 1-u+u^2 gives a genuine positivity obstruction.

## Files and reproduction

- universal_fabius_mask_criterion.pdf: complete report
- universal_fabius_mask_criterion.tex: editable LaTeX source
- build.sh: standard TeX Live build command
- SOURCES.md: checked references and repository identifiers
- validation.json: final QA and regression results
- checks/verify_mask_criteria.py: standard-library exact arithmetic checker
- checks/mask_criteria_results.json and checks/verification.log: recorded results
- SHA256SUMS: integrity manifest

Run `bash build.sh` with standard TeX Live, or `python3 checks/verify_mask_criteria.py` to reproduce the exact checks. The checker covers 4,092 finite geometric-mask pairs by polynomial divisibility, directly solves the full kernel equations for 256 overlapping-mask pairs in an independent Bernoulli model, and verifies 66 Gaussian-polynomial identities plus both displayed examples. These finite checks support transcription and algebra; the infinite-mask and arbitrary-noise results rest on the analytic proofs.

## Scope

Universal means one kernel for the entire weight or threshold family. The result does not decide every isolated two-hypothesis comparison. The polynomial coefficient criterion specifically requires equal cardinalities; the general convolution theorem has no such restriction. Vector kernels need not be unique; only their conditionally averaged scalar-sum kernels are unique. These are ordinary mathematical proofs, not formalized or externally refereed results. Classical comparison and q-polynomial identities are attributed without a general novelty claim.
