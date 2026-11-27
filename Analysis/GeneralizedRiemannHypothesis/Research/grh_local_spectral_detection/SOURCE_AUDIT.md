# Source audit

Accessed 2026-11-26. GitHub source was fetched through the GitHub connector; public reference pages were searched/read separately.

Repository: https://github.com/lsernau/grh-lean

Confirmed `main` commit: `72fead102f663d5c7a407964a13dc0cf9d977207`, commit date 2026-11-25T20:38:07Z, message `Lean proof of GRH`.

Mathlib pin reported by the readable edition README: `56a005855ea17e0b0958f73ec801ae140b0a1679`; Lean v4.35.0.

Inspected source files (selected first 75–160 lines for Lean files, not entire proof):

- [README.md](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/README.md) — editions, dependencies, claimed standard axioms, machine-check-only status.
- [grh/GUIDE.md](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md) — roadmap of short forms, enough forms, long forms and main inequality.
- [grh/README.md](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md) — five theorem statements, build instructions.
- [Statements.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean) and [Main.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean) — actual formal statements and exported declarations.
- [PrimeError.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/PrimeError.lean) — ramp and transform definitions, residue formula.
- [Criterion.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean) — one-sided criterion and proof.
- [PrimeSums.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/PrimeSums.lean) — exact comparisons across scales.
- [OneSidedBound.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean) — main inequality to one-sided remainder estimate.
- [PrintAxioms.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/scripts/PrintAxioms.lean) — audit script (read, not executed).

Other sources:
- https://en.wikipedia.org/wiki/Riemann_hypothesis — formal proof and prime-distribution sections.
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ — independent machine-check reports and working explanatory draft.
- https://link.springer.com/article/10.1007/s11139-025-01238-9 and https://arxiv.org/html/2411.07436v3 — Suzuki's sign criteria.
- https://www.academia.edu/181655129/In_Pursuit_of_a_Proof_of_the_Riemann_Hypothesis_From_Schur_minors_and_heat_collisions_to_Gaussian_detectors_and_signed_primes — publicly indexed excerpt describing Dumas's four-scale window. Full work not audited.

No new theorem has been formally verified with Lean in this environment. The report uses the GRH statements as mathematical inputs for the GRH-specific corollaries, not a new machine-checking assertion.
