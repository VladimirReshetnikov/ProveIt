# Source provenance (accessed 2026-11-26)

Read using the GitHub connector, not a local clone. The recursive tree endpoint for `main` reported SHA `72fead102f663d5c7a407964a13dc0cf9d977207` (tree SHA; not asserted to be a commit SHA). File blob SHAs below were returned by GitHub; they identify the inspected versions of those files. The repository was not rebuilt. The compact README reports Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

- [Top README](https://github.com/lsernau/grh-lean/blob/main/README.md): research artifact, two editions, stated toolchain and proof status.
- [Compact README](https://github.com/lsernau/grh-lean/blob/main/grh-compact/README.md), blob `85d43d83a7fa3b496968ce9216f4a7d75e44e84a`: target statements and reported checks.
- [Compact guide](https://github.com/lsernau/grh-lean/blob/main/grh-compact/GUIDE.md), blob `ca70306f0ee22fca325f7f515667e51625e8eabd`: theta-lift bounds A–C and their relationship to the main inequality.
- [Compact statements](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/Statements.lean), blob `1cd1bce93344065936b2b392b23306254e0785ef`: exact propositions for Dirichlet nonvanishing and the critical strip.
- [Compact endpoints](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/Main.lean), blob `a5d8389131c985a0b54ce5b0e778ee5c8126a997`: five public theorems.
- [Compact proof spine](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/New/Main.lean), blob `198ed5bf26aa294898931e0649bc2b88f1389f65`: `star_inequality`, `eventually_primeError_le_rpow`, `New.grh`.
- [Compact Landau lemma](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/Lib/Analytic/Landau/PolarLandau.lean), blob `6b80c9062a74ecadcd9c51f9459cb3c71ac2ded9`: inspected declaration and comment excerpts for `IsPolar.landau`.
- [Readable criterion](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Reduction/Zeros/Criterion.lean), blob `5c06362a50e044d491423fb3d830bae6a50c0075`: twisted prime-power sum, poles, and one-sided criterion; direct inspiration for this note's kernel and converse.
- [Readable final step](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Main.lean), blob `fc0ae69627d2e66c3d1d57815d42f0aac5823432`: reflection by functional equations.
- [Challenge](https://github.com/lsernau/grh-lean/blob/main/grh-compact/Challenge.lean), blob `4230ff8fe8b0265a44db348c22cd5f03a7c3f3fe`: intentionally uses `sorry` in target statements, not imported by the proof according to project documentation. Not a proof artifact.

Public web references consulted:

- [Riemann hypothesis — Wikipedia](https://en.wikipedia.org/wiki/Riemann_hypothesis): formulation, proof status, explicit formulas and prime-distribution consequences.
- [Suzuki, On variants of Chebyshev's conjecture](https://doi.org/10.1007/s11139-025-01238-9): related one-sided sign criteria. [Preprint](https://arxiv.org/abs/2411.07436).
- [Rubinstein and Sarnak, Chebyshev's Bias](https://doi.org/10.1080/10586458.1994.10504289): classical prime races, distinct setting and assumptions.
- [Reading project atlas](https://nasqret.github.io/riemann-rev/atlas/): reports related original proof checks and window arguments. Treated as contextual, not as independent certification here.
- [Exposition of the original proof](https://ishaan2006.github.io/rh-lean-reproduction/): related ramp sums and windowed Landau argument.

Targeted web searches covered one-sided weighted prime sums, smoothed prime races and simultaneous almost-periodic maxima. They were not an exhaustive bibliographic priority search. The proposed contribution is the joint peak-deficit and uniform-translate theorem, not the classical kernel, zero mass formula, or Landau method.
