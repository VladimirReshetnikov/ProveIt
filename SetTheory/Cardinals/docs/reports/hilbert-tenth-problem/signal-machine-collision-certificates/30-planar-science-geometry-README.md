# Planar strict-kernel classification

This independent research note supplies a corrected exact classification of

    K=intersection_{n>=0} A^(-n)P

for rational 2-by-2 A and a bounded open convex rational guard polygon P containing0.

- PROOF.md: conventional proof, all spectral cases, exact elliptic boundary formula, complexity scope, and exponential-facet family
- PRIOR_WORK.md: primary-source comparison and limits on any novelty claim
- verify_exact.py: freshly authored standard-library rational identity checks
- verification.json: output of the inspected exact-check script

Main correction: outside infinite-order elliptic dynamics, the kernel is finite linear-semialgebraic over algebraic coefficients, with strict and weak guards. The bounded-orbit subspace can be irrational. Infinite-order elliptic dynamics are exactly the nonsemialgebraic cases and admit polynomial-time rational membership by an elementary companion-denominator test.

No previous report, compiler, simulator, or collision schedule was run or edited. This note has no report-number assignment and contains no physical realization claim.
