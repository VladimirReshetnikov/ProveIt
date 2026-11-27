# Source inspection record

Access date: 26 November 2026. Retrieved via GitHub connector (read-only). Blob identifiers below identify the content retrieved; the links point at the readable edition on the default branch. The project was not rebuilt locally.

| File | Git blob SHA | Relevance |
|---|---|---|
| [README.md](https://github.com/lsernau/grh-lean/blob/main/README.md) | `fdca72cbfa3557506543b662317267897e0058a0` | Overall claim, versions, build instructions and status |
| [grh/README.md](https://github.com/lsernau/grh-lean/blob/main/grh/README.md) | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Theorems, Mathlib pin and reported checks |
| [grh-compact/README.md](https://github.com/lsernau/grh-lean/blob/main/grh-compact/README.md) | `85d43d83a7fa3b496968ce9216f4a7d75e44e84a` | Compact edition |
| [grh/GUIDE.md](https://github.com/lsernau/grh-lean/blob/main/grh/GUIDE.md) | `c2acf9584b58efcb39ac1d668d25c107c3e76a0b` | Proof architecture and reductions |
| [grh/src/Statements.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/Statements.lean) | `1cd1bce93344065936b2b392b23306254e0785ef` | Definitions of all five theorem interfaces |
| [grh/src/Main.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/Main.lean) | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Derivation of headline theorems |
| [grh/scripts/PrintAxioms.lean](https://github.com/lsernau/grh-lean/blob/main/grh/scripts/PrintAxioms.lean) | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | Commands for axiom audit, not local execution |
| [grh/src/New/Reduction/MainInequality.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Reduction/MainInequality.lean) | `97f83ab52b2feb420e952a2722b4cef454b9e579` | Introductory comment and initial theorem proof (lines 1–130 requested) |
| [grh/src/New/Reduction/OneSidedBound.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Reduction/OneSidedBound.lean) | `99e5240de112527b739068b692e5007720d310c1` | Prime remainder and bound (lines 1–130 requested) |
| [grh/src/New/Reduction/Zeros/Criterion.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Reduction/Zeros/Criterion.lean) | `5c06362a50e044d491423fb3d830bae6a50c0075` | Landau criterion, residues and twist choice (lines 1–100 requested) |
| [grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean](https://github.com/lsernau/grh-lean/blob/main/grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean) | `6618aced1c8dea8422627ee688fc323a005ba96c` | Integral form of remainder (lines 1–100 requested) |

Upstream Lean version: v4.35.0; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` as reported in README. The five theorems are reported to depend on `propext`, `Classical.choice`, and `Quot.sound`. See the independent [Waterloo verification record](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/) and the [Lean FRO/Mathlib statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/).

Other web sources inspected: [Wikipedia RH](https://en.wikipedia.org/wiki/Riemann_hypothesis), especially consequences and related questions; [Banks, Comparing zeros of distinct Dirichlet L-functions](https://arxiv.org/abs/2302.07073), Theorem 1.2 and its proof; [Martin–Ng](https://arxiv.org/abs/1710.00088); [Devin](https://doi.org/10.4153/S0008439520000089); [Banks–Loftus](https://arxiv.org/abs/2607.22930). The research note cites these for background and explains the difference in claims. The novelty search was targeted, not exhaustive.

## Dependency boundary

* Upstream output used: GRH for primitive Dirichlet characters of every conductor, including RH for conductor one. Nothing concerning general automorphic L-functions is assumed.
* Established analytic tools: functional equation, log derivative, unit-interval zero count, orthogonality, Dirichlet's theorem, fixed-argument Landau formula (Banks Theorem 1.2 or the zeta version).
* Derived here: absolute ramp expansion; arithmetic probe separation for arbitrary distinct real shifts; uniform recovery and two-sided energy bounds; deletion-robust covariance and density/convex hull corollaries.
* The new theorem is a mathematical proof on paper; no Lean compilation or machine-checked proof is claimed. The Python checks certify only the finite rational examples exactly and illustrate the spectral formula numerically.
