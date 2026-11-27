# Source audit

Access date: 2026-11-26. Read through GitHub connector, not a local clone.

Repository: https://github.com/lsernau/grh-lean

- Branch `main` commit reported by branches/main: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- Reported commit tree: `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f`.
- Lean toolchain per compact README: v4.35.0. Mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Files actually retrieved:

| File | Blob SHA |
|---|---|
| README.md | fdca72cbfa3557506543b662317267897e0058a0 |
| grh/GUIDE.md | c2acf9584b58efcb39ac1d668d25c107c3e76a0b |
| grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef |
| grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 |
| grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 |
| grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 |
| grh-compact/README.md | 85d43d83a7fa3b496968ce9216f4a7d75e44e84a |

The public README lists five final theorems and machine checks, but no complete human reading. The source-level analysis in Section 1 of the paper is confined to the relevant declarations and excerpts from the above files; there was no attempt to audit all transitive dependencies or reproduce the Lean build.

Other accessed references:
- https://en.wikipedia.org/wiki/Riemann_hypothesis (current version: describes the theorem and the formal proof; also gives classical consequences and zero counting).
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ (independent reported verification, original and shortened developments).
- https://dlmf.nist.gov/25.15 (Dirichlet L-functions).
- https://dlmf.nist.gov/25.10 (classical zero counting).
- https://doi.org/10.1007/s00209-021-02820-9 (log derivative and primes).
- https://doi.org/10.1002/nla.2048 (polynomial and rational eigenvalue counting filters; relevant prior art, not an asserted exact match).

Search concepts for possible prior art: Riemann xi zero bounds from logarithmic derivatives; Euler–Rayleigh inequalities; Stieltjes-transform divided differences and support; real-axis sample zero counting; polynomial and rational spectral filters. This is a preliminary, nonexhaustive search. No absence-of-prior-art claim is made.
