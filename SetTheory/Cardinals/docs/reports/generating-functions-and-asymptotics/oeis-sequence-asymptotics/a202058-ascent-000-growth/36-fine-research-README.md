# Fine-scale research for A202058

2 October 2026. This extends the frozen 1 October root-limit report without modifying it. No external publication was made.

## New proved result

For the number a_n of ascent sequences in which each value occurs at most twice, set μ=8/(3π²). The new positive-kernel argument proves

    log(a_n/(n! μ^n)) <= O((log n)²).

This rules out every positive stretched-exponential correction exp(c n^σ), with c,σ>0, even in the presence of fixed power/logarithmic factors. It is a genuine analytic improvement, not a fit to coefficients.

A weighted residual estimate also improves the uniform state-function barriers. The existing broad-window lower method then gives the asymmetric enclosure

    −O(n^(2/3)(log n)^(5/3))
       <= log(a_n/(n! μ^n))
       <= O((log n)²).

For the inverse N(y)=min{n:log a_n>=y} and x=y/W(y/(eT)), T=3π²/8,

    x−O(log x) <= N(y) <= x+O(x^(2/3)(log x)^(2/3)).

The upper theorem, lower supplement and inverse have been independently mathematically audited. These remain bounds: no full equivalent, matching fine lower estimate, limiting prefactor, ratio limit or all-orders expansion is claimed.

## Files to read first

- `padded-barrier-proof.md`: main theorem and the new weighted/padded positive supersolution
- `improved-coarse-lower.md`: improved quantitative lower bound and controlled asymmetric inverse
- `kernel/audit-padded-barrier.md`: independent analytic audit, including comparison at the infinite-state boundary
- `coefficient-obstruction.md`: exact variance formulation of the missing regularity and proof-method obstructions
- `lognormal-route.md`: explicitly formal route toward a conjectural 2/3 logarithmic-square coefficient
- `literature.md` and `literature-regularity-supplement.md`: current primary-source and scoped ProveIt checks
- `numerics/README.md`: exact coefficients, numerical continuation, conditional fits and reproduction instructions

## Numerical evidence, separately labeled

An optimized exact recurrence independently reproduces all 177 published coefficients and extends them to n=400. A positive-sum long-double version reaches n=1000, agreeing with the exact values through 400 within approximately 3.22e−17 relative error.

The computations strongly motivate, but do not prove,

    log(a_n/(n! μ^n)) ~ (2/3)(log n)².

A formal continuous frozen-kernel/transport calculation selects the same coefficient. Its remaining finite-state weighted-boundary and coefficient-transfer issues are explicitly identified. In particular, the original-profile transformed chain is nearly trapped at the root for large q, so replacing it by an already-mixed large-state chain is not valid without a rare-path/weighted argument.

Global log-concavity of a_n/n! would be helpful and passes every exact tested center through 399, plus 3,060 finite all-state suffix tests. It is not proved here. Stronger shortcut hypotheses fail: the normalized sequence is not PF3, and the doubled-letter polynomial at length seven is not real-rooted.

## Verification and provenance

The independent residual checker tests 86,814 state/parameter cases and 616,005 padding-transition mappings; all assertions pass. Its script and JSON output are in `kernel/`.

`source-provenance.json` records the frozen archive hash and verifies that its TeX agrees byte-for-byte with the source directory. The frozen files have not been rewritten.

Exact computation and numerical fits are reproducible from the C++ and Python scripts in `numerics/`; the two main counting runs took approximately 62 seconds and 278 seconds in this environment. High-order fitted constants remain conditional and potentially ill-conditioned.

The literature search found no later directly applicable primary theorem or direct ProveIt keyword overlap. This is scoped negative evidence, not an exhaustive novelty certificate. The 2022 paper's detailed Section 5 leaves the subexponential form unresolved; its shorter introductory expression must not be treated as an established equivalent.
